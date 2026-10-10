use super::storage_locations::StorageLocation;
use super::*;
use rustc_abi::FieldIdx;
use rustc_index::IndexVec;
use rustc_middle::mir::visit::{MutVisitor, PlaceContext};
use rustc_middle::mir::{Local, LocalDecl, Location};

#[derive(Clone)]
pub(super) struct OriginalPlace<'tcx> {
    original: Place<'tcx>,
    lowered: Place<'tcx>,
    owner: Place<'tcx>,
    coroutine: Ty<'tcx>,
    field: usize,
    variant: Option<usize>,
    field_ty: Ty<'tcx>,
}

pub(super) fn coroutine_name(id: DefId, args: ty::GenericArgsRef<'_>) -> String {
    format!("coroutine {id:?} {args:?}")
}

pub(super) fn matches_body<'tcx>(owner: &std::rc::Weak<Body<'tcx>>, body: &Body<'tcx>) -> bool {
    owner
        .upgrade()
        .is_some_and(|owner| std::ptr::eq(owner.as_ref(), body))
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn construct_coroutine(
        &mut self,
        id: DefId,
        args: ty::GenericArgsRef<'tcx>,
        captures: Vec<Value>,
    ) -> Result<Value, String> {
        if captures.len() != args.as_coroutine().upvar_tys().len() {
            return Err("coroutine captures do not match its compiler type".into());
        }
        let layout = self
            .tcx
            .coroutine_layout(id, args)
            .map_err(|error| format!("coroutine layout is unavailable: {error:?}"))?;
        if layout.variant_fields.len() > 64
            || captures.len() + layout.field_tys.len() > MAX_INPUT_VALUES
        {
            return Err("coroutine layout exceeds the state model budget".into());
        }
        let mut fields: Vec<_> = captures
            .into_iter()
            .enumerate()
            .map(|(index, value)| (index.to_string(), value))
            .collect();
        fields.extend(
            (0..layout.field_tys.len())
                .map(|index| (format!("saved_{index}"), Value::Uninitialized)),
        );
        self.record_model(
            id,
            "coroutine construction; execution is checked only when polled",
        );
        Ok(Value::Adt {
            name: coroutine_name(id, args),
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields: fields.into(),
        })
    }

    pub(super) fn flatten_coroutine_places(
        &self,
        body: &mut Body<'tcx>,
    ) -> Result<Vec<OriginalPlace<'tcx>>, String> {
        if !body.local_decls.iter().any(|local| {
            local
                .ty
                .walk()
                .any(|arg| arg.as_type().is_some_and(|ty| ty.is_coroutine()))
        }) {
            return Ok(Vec::new());
        }
        let mut visitor = CoroutinePlaces {
            tcx: self.tcx,
            locals: body.local_decls.clone(),
            places: Vec::new(),
            error: None,
        };
        visitor.visit_body(body);
        visitor.error.map_or(Ok(visitor.places), Err)
    }

    pub(super) fn coroutine_move_storage(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<(usize, Vec<initialized_places::Step>)>, String> {
        let places = self.coroutine_places.borrow();
        let mut matches = places
            .iter()
            .filter(|(owner, cert)| matches_body(owner, body) && cert.lowered == place);
        let Some((_, certificate)) = matches.next() else {
            return Ok(None);
        };
        if matches.any(|(_, other)| other.original != certificate.original) {
            return Err("coroutine lowered place has ambiguous original provenance".into());
        }
        let (allocation, mut path, _) = self.memory_path(state, certificate.owner)?;
        path.push(symbolic::MemoryProjection::Field(certificate.field));
        let fields = initialized_places::field_footprint(&path)
            .ok_or("coroutine consumed place lacks exact fixed storage footprint")?;
        Ok(Some((
            allocation.ok_or("coroutine consumption requires tracked receiver")?,
            fields,
        )))
    }

    pub(super) fn consume_coroutine_operand(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let places = self.coroutine_places.borrow();
        let mut matches = places
            .iter()
            .filter(|(candidate, cert)| matches_body(candidate, body) && cert.lowered == place);
        let Some((_, certificate)) = matches.next() else {
            return Ok(None);
        };
        if matches.any(|(_, other)| other.original != certificate.original) {
            return Err("coroutine lowered place has ambiguous original provenance".into());
        }
        let ty::Coroutine(id, args) = certificate.coroutine.kind() else {
            return Err("coroutine place certificate has a non-coroutine original type".into());
        };
        if certificate.owner.ty(&body.local_decls, self.tcx).ty != certificate.coroutine
            || certificate.original.ty(&body.local_decls, self.tcx).ty != certificate.field_ty
        {
            return Err("coroutine original place type no longer matches its body".into());
        }
        let (allocation, mut path, writable) = self.memory_path(state, certificate.owner)?;
        let allocation = allocation.ok_or("coroutine consumption requires tracked receiver")?;
        StorageLocation::tracked(allocation, writable).require_write(&state.memory)?;
        let mut owner = state.memory[allocation]
            .clone()
            .ok_or("coroutine receiver storage is dead")?;
        for projection in &path {
            owner = self.memory_projection(owner, projection, &state.conditions)?;
        }
        let Value::Adt {
            name,
            variant,
            is_option,
            discriminant,
            fields,
        } = owner
        else {
            return Err("coroutine receiver lacks exact nominal storage".into());
        };
        let layout = self
            .tcx
            .coroutine_layout(*id, args)
            .map_err(|error| format!("coroutine layout is unavailable: {error:?}"))?;
        if name != coroutine_name(*id, args)
            || is_option
            || discriminant != variant as u128
            || variant >= layout.variant_fields.len()
            || fields.len() != args.as_coroutine().upvar_tys().len() + layout.field_tys.len()
            || certificate
                .variant
                .is_some_and(|expected| expected != variant)
        {
            return Err("coroutine consuming place differs from active compiler state".into());
        }
        path.push(symbolic::MemoryProjection::Field(certificate.field));
        let value = self.reference_value(
            &Value::Reference {
                allocation,
                projection: path.clone(),
                mutable: writable,
            },
            &state.memory,
            &state.conditions,
        )?;
        let value = self.finish_place(state, value)?;
        let fields = initialized_places::field_footprint(&path)
            .ok_or("coroutine consumed place lacks exact fixed storage footprint")?;
        state
            .memory
            .missing_places
            .consume(allocation, fields)
            .map_err(|reason| self.categorized_error(UnknownCategory::ResourceLimit, reason))?;
        Ok(Some(value))
    }

    pub(super) fn set_coroutine_state(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        index: usize,
    ) -> Result<(), String> {
        let ty::Coroutine(id, args) = place.ty(&body.local_decls, self.tcx).ty.kind() else {
            return Err("setting a non-coroutine discriminant remains unsupported".into());
        };
        let layout = self
            .tcx
            .coroutine_layout(*id, args)
            .map_err(|error| format!("coroutine layout is unavailable: {error:?}"))?;
        if index >= layout.variant_fields.len() {
            return Err("coroutine state index exceeds its compiler layout".into());
        }
        let (allocation, path, writable) = self.memory_path(state, place)?;
        let allocation = allocation.ok_or("coroutine state needs retained tracked storage")?;
        let location = StorageLocation::tracked(allocation, writable);
        location.require_write(&state.memory)?;
        location.validate(&state.memory)?;
        let captures = args.as_coroutine().upvar_tys().len();
        for saved in &layout.variant_fields[rustc_abi::VariantIdx::from_usize(index)] {
            let mut field_path = path.clone();
            field_path.push(symbolic::MemoryProjection::Field(
                captures + saved.as_usize(),
            ));
            state
                .memory
                .check_projection_initialization(allocation, &field_path)
                .map_err(|reason| self.categorized_error(UnknownCategory::Semantics, reason))?;
        }
        let mut value = location.read_storage(&state.memory)?.clone();
        self.update_coroutine_tag(&mut value, &path, *id, args, index, state)?;
        // SetDiscriminant changes the compiler state tag only, never initializes payload storage.
        state.memory[allocation] = Some(value);
        Ok(())
    }

    fn update_coroutine_tag(
        &self,
        storage: &mut Value,
        path: &[symbolic::MemoryProjection],
        id: DefId,
        args: ty::GenericArgsRef<'tcx>,
        index: usize,
        state: &State,
    ) -> Result<(), String> {
        if let Some((symbolic::MemoryProjection::Field(field), rest)) = path.split_first() {
            let Value::Adt { fields, .. } = storage else {
                return Err("coroutine tag path requires retained nominal field storage".into());
            };
            let mut updated = fields.to_vec();
            let (_, child) = updated
                .get_mut(*field)
                .ok_or("coroutine tag field exceeds its owner storage")?;
            self.update_coroutine_tag(child, rest, id, args, index, state)?;
            *fields = updated.into();
            return Ok(());
        }
        if !path.is_empty() {
            return Err("coroutine tag update needs an exact fixed owned field path".into());
        }
        let Value::Adt {
            name,
            variant,
            is_option,
            discriminant,
            fields,
        } = storage
        else {
            return Err("coroutine state needs a constructed tracked future".into());
        };
        let layout = self
            .tcx
            .coroutine_layout(id, args)
            .map_err(|error| format!("coroutine layout is unavailable: {error:?}"))?;
        let captures = args.as_coroutine().upvar_tys().len();
        if *name != coroutine_name(id, args)
            || *is_option
            || fields.len() != captures + layout.field_tys.len()
            || *variant >= layout.variant_fields.len()
            || *discriminant != *variant as u128
        {
            return Err("coroutine state storage identity does not match its type".into());
        }
        for saved in &layout.variant_fields[rustc_abi::VariantIdx::from_usize(index)] {
            let slot = captures + saved.as_usize();
            let value = &fields[slot].1;
            if matches!(value, Value::Uninitialized) {
                return Err("coroutine state requires initialized active saved storage".into());
            }
            self.validate_tracked_value(value, state)?;
        }
        *variant = index;
        *discriminant = index as u128;
        Ok(())
    }

    pub(super) fn is_task_context(&self, ty: Ty<'tcx>) -> bool {
        matches!(ty.kind(), ty::Adt(def, _) if
            self.tcx.lang_items().get(LangItem::Context) == Some(def.did()))
    }

    pub(super) fn pin_mutable_deref(
        &self,
        instance: ty::Instance<'tcx>,
        signature: ty::FnSig<'tcx>,
        values: &[Value],
        state: &State,
    ) -> Result<Option<Value>, String> {
        let callee = instance.def_id();
        let parent = self.tcx.parent(callee);
        if self.tcx.item_name(callee) != rustc_span::Symbol::intern("deref_mut")
            || !matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: true })
            || self.tcx.lang_items().get(LangItem::DerefMut)
                != Some(
                    self.tcx
                        .impl_trait_ref(parent)
                        .instantiate(self.tcx, instance.args)
                        .skip_norm_wip()
                        .def_id,
                )
        {
            return Ok(None);
        }
        let [receiver] = signature.inputs() else {
            return Ok(None);
        };
        let ty::Ref(_, pin, mutable) = receiver.kind() else {
            return Ok(None);
        };
        let ty::Adt(def, args) = pin.kind() else {
            return Ok(None);
        };
        if !mutable.is_mut()
            || self.tcx.lang_items().get(LangItem::Pin) != Some(def.did())
            || callee.krate != def.did().krate
        {
            return Ok(None);
        }
        let ty::Ref(_, pointee, mutable) = args.type_at(0).kind() else {
            return Ok(None);
        };
        if !mutable.is_mut()
            || !matches!(signature.output().kind(), ty::Ref(_, target, mutable)
                if mutable.is_mut() && target == pointee)
        {
            return Ok(None);
        }
        let [reference] = values else {
            return Err("Pin mutable dereference arity mismatch".into());
        };
        let pin = self.reference_value(reference, &state.memory, &state.conditions)?;
        let pointer = pin.field("pointer")?;
        if !matches!(pointer, Value::Reference { mutable: true, .. }) {
            return Err("Pin mutable dereference needs a tracked mutable pointer".into());
        }
        Ok(Some(pointer))
    }

    pub(super) fn task_context_constructor(
        &mut self,
        instance: ty::Instance<'tcx>,
        signature: ty::FnSig<'tcx>,
        values: &[Value],
    ) -> Result<Option<Value>, String> {
        let callee = instance.def_id();
        let parent = self.tcx.parent(callee);
        if !matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: false }) {
            return Ok(None);
        }
        let waker = self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("Waker"));
        let is_waker =
            |ty: Ty<'tcx>| matches!(ty.kind(), ty::Adt(def, _) if Some(def.did()) == waker);
        let owner = self
            .tcx
            .type_of(parent)
            .instantiate(self.tcx, instance.args)
            .skip_norm_wip();
        if is_waker(owner)
            && Some(callee.krate) == waker.map(|id| id.krate)
            && self.tcx.item_name(callee) == rustc_span::Symbol::intern("noop")
            && signature.inputs().is_empty()
            && matches!(signature.output().kind(), ty::Ref(_, inner, mutable)
                if !mutable.is_mut() && is_waker(*inner))
        {
            if !values.is_empty() {
                return Err("noop waker arity mismatch".into());
            }
            self.record_model(callee, "core noop waker; opaque shared static waker");
            return Ok(Some(Value::Adt {
                name: "opaque noop waker".into(),
                variant: 0,
                is_option: false,
                discriminant: 0,
                fields: Vec::new().into(),
            }));
        }
        if self.is_task_context(owner)
            && Some(callee.krate)
                == self
                    .tcx
                    .lang_items()
                    .get(LangItem::Context)
                    .map(|id| id.krate)
            && self.tcx.item_name(callee) == rustc_span::Symbol::intern("from_waker")
            && self.is_task_context(signature.output())
            && matches!(signature.inputs(), [input] if matches!(input.kind(),
                ty::Ref(_, inner, mutable) if !mutable.is_mut() && is_waker(*inner)))
        {
            if !matches!(values, [Value::Adt { name, .. }] if name == "opaque noop waker") {
                return Err("task context construction needs a modeled noop waker".into());
            }
            self.record_model(
                callee,
                "core task context from noop waker; opaque valid context",
            );
            return Ok(Some(Value::Adt {
                name: "opaque task context".into(),
                variant: 0,
                is_option: false,
                discriminant: 0,
                fields: Vec::new().into(),
            }));
        }
        Ok(None)
    }

    pub(super) fn context_transmute(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: &Value,
    ) -> Result<Option<Value>, String> {
        let context_ref = |ty: Ty<'tcx>| {
            matches!(ty.kind(), ty::Ref(_, inner, mutable)
            if mutable.is_mut() && self.is_task_context(*inner))
        };
        let context_pointer = |ty: Ty<'tcx>| {
            matches!(ty.kind(), ty::Adt(def, args)
            if self.tcx.lang_items().get(LangItem::NonNull) == Some(def.did())
                && self.is_task_context(args.type_at(0)))
        };
        if context_ref(source) && context_pointer(target) {
            if !matches!(value, Value::Reference { mutable: true, .. }) {
                return Err("coroutine context adapter needs a tracked mutable reference".into());
            }
            return self.constructed(target, 0, vec![value.clone()]).map(Some);
        }
        if context_pointer(source) && context_ref(target) {
            let reference = value.field("pointer")?;
            if !matches!(reference, Value::Reference { mutable: true, .. }) {
                return Err("coroutine context adapter lost its tracked reference".into());
            }
            return Ok(Some(reference));
        }
        Ok(None)
    }
}

struct CoroutinePlaces<'tcx> {
    tcx: TyCtxt<'tcx>,
    locals: IndexVec<Local, LocalDecl<'tcx>>,
    places: Vec<OriginalPlace<'tcx>>,
    error: Option<String>,
}

impl<'tcx> MutVisitor<'tcx> for CoroutinePlaces<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_place(&mut self, place: &mut Place<'tcx>, _: PlaceContext, _: Location) {
        if self.error.is_some() {
            return;
        }
        let original = *place;
        let mut certificate = None;
        for position in 0..original.projection.len() {
            let owner = Place {
                local: original.local,
                projection: self.tcx.mk_place_elems(&original.projection[..position]),
            };
            let coroutine = owner.ty(&self.locals, self.tcx).ty;
            let ty::Coroutine(id, args) = coroutine.kind() else {
                continue;
            };
            let Ok(layout) = self.tcx.coroutine_layout(*id, args) else {
                self.error = Some("coroutine original place has no compiler layout".into());
                return;
            };
            let (field, field_ty, variant, consumed) = match original.projection[position] {
                ProjectionElem::Field(field, ty) => {
                    if owner.ty(&self.locals, self.tcx).variant_index.is_some() {
                        continue;
                    }
                    let Some(expected) = args.as_coroutine().upvar_tys().get(field.as_usize())
                    else {
                        self.error = Some("coroutine capture exceeds original upvars".into());
                        return;
                    };
                    if *expected != ty {
                        self.error = Some("coroutine capture type differs".into());
                        return;
                    }
                    (field.as_usize(), ty, None, 1)
                }
                ProjectionElem::Downcast(_, variant) => {
                    let Some(ProjectionElem::Field(field, ty)) =
                        original.projection.get(position + 1)
                    else {
                        continue;
                    };
                    let Some(saved) = layout
                        .variant_fields
                        .get(variant)
                        .and_then(|fields| fields.get(*field))
                    else {
                        self.error = Some("coroutine saved place exceeds original state".into());
                        return;
                    };
                    if layout.field_tys[*saved].ty != *ty {
                        self.error = Some("coroutine saved field type differs".into());
                        return;
                    }
                    (
                        args.as_coroutine().upvar_tys().len() + saved.as_usize(),
                        *ty,
                        Some(variant.as_usize()),
                        2,
                    )
                }
                _ => continue,
            };
            if position + consumed == original.projection.len() {
                certificate = Some(OriginalPlace {
                    original,
                    lowered: original,
                    owner,
                    coroutine,
                    field,
                    variant,
                    field_ty,
                });
            }
        }
        let mut projection = Vec::new();
        let mut position = 0;
        while position < original.projection.len() {
            let element = original.projection[position];
            let prefix = Place {
                local: original.local,
                projection: self.tcx.mk_place_elems(&original.projection[..position]),
            };
            if let ProjectionElem::Downcast(_, variant) = element
                && let ty::Coroutine(id, args) = prefix.ty(&self.locals, self.tcx).ty.kind()
            {
                let Some(ProjectionElem::Field(field, field_ty)) =
                    original.projection.get(position + 1)
                else {
                    self.error = Some("whole coroutine variant projection is unsupported".into());
                    return;
                };
                let Ok(layout) = self.tcx.coroutine_layout(*id, args) else {
                    self.error = Some("coroutine has no lowered state layout".into());
                    return;
                };
                let Some(saved) = layout
                    .variant_fields
                    .get(variant)
                    .and_then(|fields| fields.get(*field))
                else {
                    self.error = Some("coroutine projection exceeds its compiler layout".into());
                    return;
                };
                // Variants can share a saved local; all accesses use its one logical slot.
                let index = args.as_coroutine().upvar_tys().len() + saved.as_usize();
                projection.push(ProjectionElem::Field(
                    FieldIdx::from_usize(index),
                    *field_ty,
                ));
                position += 2;
            } else {
                projection.push(element);
                position += 1;
            }
        }
        place.projection = self.tcx.mk_place_elems(&projection);
        if let Some(mut certificate) = certificate {
            certificate.lowered = *place;
            if !self
                .places
                .iter()
                .any(|existing| existing.original == certificate.original)
            {
                if self.places.len() >= MAX_INPUT_VALUES {
                    self.error = Some("coroutine original place inventory exceeds 512".into());
                    return;
                }
                self.places.push(certificate);
            }
        }
    }
}
