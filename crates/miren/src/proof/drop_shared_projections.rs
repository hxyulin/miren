//! Storage views for shared fixed-array projections; no owning non-Copy value is selected.
use super::*;
use initialized_places::Step;
use std::rc::{Rc, Weak};
use symbolic::MemoryProjection;
use symbolic::input::{InputKind, InputShape, InputValue};

#[derive(Clone, Debug)]
pub(super) struct Witness<'tcx> {
    instance: ty::Instance<'tcx>,
    body: Weak<Body<'tcx>>,
    allocation: usize,
    original: Ty<'tcx>,
}

struct Candidate<'a, 'tcx> {
    value: Storage<'a>,
    original: Ty<'tcx>,
    mask: Term,
    fields: Vec<Step>,
}

enum Storage<'a> {
    Physical(&'a Value),
    Lazy(LazyStorage<'a>),
    Scalar(Value),
}

#[derive(Clone, Copy)]
struct LazyStorage<'a> {
    shape: &'a Rc<InputShape>,
    start: u32,
    seed: &'a Term,
}

enum ArrayStorage<'a> {
    Physical(&'a symbolic::Elements),
    Lazy(LazyStorage<'a>),
}

// This bounds semantic nodes visited or constructed by one service, not CPU instructions.
// Type/descriptor nodes and traversed fields cost one. An index branch costs three for
// equality, guard conjunction and candidate construction. Scalar decoding costs one.
pub(super) struct Work(usize);
impl Work {
    pub(super) fn charge(&mut self, count: usize) -> Result<(), String> {
        self.0 = self
            .0
            .checked_add(count)
            .ok_or("shared Drop projection work overflow")?;
        if self.0 > 512 {
            return Err("shared Drop projection exceeds its 512-node work bound".into());
        }
        Ok(())
    }
}

fn scalar(original: Ty<'_>) -> bool {
    matches!(
        original.kind(),
        ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64)
    )
}

pub(super) fn readonly_drop_struct<'tcx>(tcx: TyCtxt<'tcx>, original: Ty<'tcx>) -> bool {
    matches!(original.kind(), ty::Adt(def, _) if def.did().is_local()
        && def.is_struct() && !def.repr().packed() && def.destructor(tcx).is_some()
        && original.is_freeze(tcx, ty::TypingEnv::fully_monomorphized()))
}

fn domain<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
    depth: usize,
    work: &mut Work,
) -> Result<(), String> {
    work.charge(1)?;
    if depth >= 16 {
        return Err("shared Drop projection exceeds depth16".into());
    }
    match original.kind() {
        ty::Array(child, count) => {
            let count = count
                .try_to_target_usize(tcx)
                .ok_or("shared Drop projection needs a concrete original array count")?;
            if count > 128 {
                return Err("shared Drop projection exceeds array count128".into());
            }
            // Every fixed-array occurrence has the same original element type.
            // Validate that complete type once, including the zero-length case.
            domain(tcx, *child, depth + 1, work)
        }
        ty::Adt(def, args)
            if def.did().is_local()
                && def.is_struct()
                && !def.repr().packed()
                && def.destructor(tcx).is_some() =>
        {
            let env = ty::TypingEnv::fully_monomorphized();
            if !original.is_freeze(tcx, env) {
                return Err("shared Drop projection requires original Freeze storage".into());
            }
            tcx.layout_of(env.as_query_input(original))
                .map_err(|error| format!("shared Drop projection layout unavailable: {error:?}"))?;
            for field in &def.non_enum_variant().fields {
                work.charge(1)?;
                if !scalar(field.ty(tcx, args).skip_norm_wip()) {
                    return Err(
                        "shared Drop projection needs original primitive struct fields".into(),
                    );
                }
            }
            Ok(())
        }
        _ => Err("shared Drop projection needs local Drop structs in original fixed arrays".into()),
    }
}

fn field_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
    index: usize,
) -> Result<Ty<'tcx>, String> {
    let ty::Adt(def, args) = original.kind() else {
        return Err("shared Drop projection field lacks its original struct".into());
    };
    if !def.did().is_local() || !def.is_struct() || def.repr().packed() {
        return Err("shared Drop projection field lacks its original local struct".into());
    }
    def.non_enum_variant()
        .fields
        .get(rustc_abi::FieldIdx::from_usize(index))
        .map(|field| field.ty(tcx, args).skip_norm_wip())
        .ok_or_else(|| "shared Drop projection field is outside original inventory".into())
}

impl<'tcx> Engine<'tcx> {
    fn drop_projection_body(
        &self,
        body: &Body<'tcx>,
    ) -> Result<(ty::Instance<'tcx>, Rc<Body<'tcx>>), String> {
        let bodies = self.bodies.borrow();
        if bodies.len() > 512 {
            return Err("shared Drop projection body lookup exceeds 512 entries".into());
        }
        let mut matches = bodies
            .iter()
            .filter(|(_, actual)| std::ptr::eq(actual.as_ref(), body));
        let (instance, actual) = matches
            .next()
            .ok_or("shared Drop projection requires actual current caller Body")?;
        if matches.next().is_some()
            || body.source.instance != instance.def
            || body.source.promoted.is_some()
        {
            return Err("shared Drop projection caller Instance association differs".into());
        }
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !self.tcx.is_mir_available(instance.def_id())
        {
            return Err(self.missing_body_reason(instance.def_id()));
        }
        Ok((*instance, actual.clone()))
    }

    pub(super) fn drop_shared_place_candidate(
        &self,
        body: &Body<'tcx>,
        place: Place<'tcx>,
    ) -> bool {
        matches!(place.projection.first(), Some(ProjectionElem::Index(_)))
            && matches!(body.local_decls[place.local].ty.kind(), ty::Array(..))
            && body.local_decls[place.local]
                .ty
                .needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
    }

    pub(super) fn drop_shared_error(&self, reason: String) -> String {
        if self.unknown_causes.borrow().contains_key(&reason) {
            return reason;
        }
        let category = if reason.contains("exceeds") || reason.contains("overflow") {
            UnknownCategory::ResourceLimit
        } else {
            UnknownCategory::Semantics
        };
        self.categorized_error(category, reason)
    }

    fn drop_projection_original(&self, original: Ty<'tcx>) -> Result<bool, String> {
        if !matches!(original.kind(), ty::Array(..))
            || !original.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Ok(false);
        }
        self.drop_input_domain(original, &mut Work(0))?;
        Ok(true)
    }

    pub(super) fn drop_input_domain(
        &self,
        original: Ty<'tcx>,
        work: &mut Work,
    ) -> Result<(), String> {
        if !matches!(original.kind(), ty::Array(..))
            || !original.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Err("shared Drop lazy storage lacks an original Drop array".into());
        }
        domain(self.tcx, original, 0, work)
    }

    pub(super) fn validate_drop_input_descriptor(
        &self,
        original: Ty<'tcx>,
        shape: &InputShape,
        work: &mut Work,
    ) -> Result<(), String> {
        self.drop_input_descriptor(original, shape, 0, work)
    }

    fn drop_input_descriptor(
        &self,
        original: Ty<'tcx>,
        shape: &InputShape,
        depth: usize,
        work: &mut Work,
    ) -> Result<(), String> {
        work.charge(1)?;
        if depth >= 16 {
            return Err("shared Drop lazy descriptor exceeds depth16".into());
        }
        let (slots, height) = match (original.kind(), &shape.kind) {
            (ty::Bool, InputKind::Bool) => (1, 1),
            (ty::Int(_) | ty::Uint(_), InputKind::Integer { bits, signed })
                if self.integer_type(original) == Some((*bits, *signed)) =>
            {
                (1, 1)
            }
            (ty::Float(_), InputKind::Float { bits })
                if self.float_type(original) == Some(*bits) =>
            {
                (1, 1)
            }
            (ty::Array(child, expected), InputKind::Array { element, count })
                if expected.try_to_target_usize(self.tcx) == Some(*count as u64)
                    && *count <= 128 =>
            {
                self.drop_input_descriptor(*child, element, depth + 1, work)?;
                let slots = element
                    .slots
                    .checked_mul(*count as u32)
                    .and_then(|slots| slots.checked_add(1))
                    .ok_or("shared Drop lazy descriptor slots overflow")?;
                (slots, element.height + 1)
            }
            (ty::Adt(def, args), InputKind::Struct { name, fields })
                if def.did().is_local()
                    && def.is_struct()
                    && !def.repr().packed()
                    && def.destructor(self.tcx).is_some()
                    && original.is_freeze(self.tcx, ty::TypingEnv::fully_monomorphized())
                    && *name == self.tcx.def_path_str(def.did())
                    && name.len() <= 128
                    && fields.len() == def.non_enum_variant().fields.len() =>
            {
                let mut slots = 1_u32;
                let mut height = 1;
                for ((name, shape), field) in fields.iter().zip(&def.non_enum_variant().fields) {
                    work.charge(1)?;
                    let original = field.ty(self.tcx, args).skip_norm_wip();
                    if name.len() > 128 || *name != field.name.as_str() || !scalar(original) {
                        return Err("shared Drop lazy descriptor original field differs".into());
                    }
                    self.drop_input_descriptor(original, shape, depth + 1, work)?;
                    slots = slots
                        .checked_add(shape.slots)
                        .ok_or("shared Drop lazy descriptor slots overflow")?;
                    height = height.max(shape.height + 1);
                }
                (slots, height)
            }
            _ => return Err("shared Drop lazy descriptor original type differs".into()),
        };
        if shape.slots != slots || shape.height != height {
            return Err("shared Drop lazy descriptor slots or height differs".into());
        }
        Ok(())
    }

    fn drop_projection_path(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Vec<MemoryProjection>, String> {
        self.drop_projection_parts(
            body,
            state,
            body.local_decls[place.local].ty,
            place.projection,
        )
    }

    fn drop_projection_parts(
        &self,
        body: &Body<'tcx>,
        state: &State,
        mut original: Ty<'tcx>,
        parts: &[rustc_middle::mir::PlaceElem<'tcx>],
    ) -> Result<Vec<MemoryProjection>, String> {
        if parts.len() > 16 {
            return Err("shared Drop projection exceeds depth16".into());
        }
        let mut path = Vec::new();
        let mut captured: BTreeMap<rustc_middle::mir::Local, Value> = BTreeMap::new();
        for &part in parts {
            match part {
                ProjectionElem::Index(local) => {
                    if body.local_decls[local].ty != self.tcx.types.usize {
                        return Err("shared Drop projection index lacks original usize".into());
                    }
                    let value = if let Some(value) = captured.get(&local) {
                        value.clone()
                    } else {
                        let value = self.local(state, local.as_usize())?;
                        captured.insert(local, value.clone());
                        value
                    };
                    let ty::Array(child, _) = original.kind() else {
                        return Err(
                            "shared Drop projection index lacks original fixed array".into()
                        );
                    };
                    original = *child;
                    path.push(MemoryProjection::Index(Box::new(value)));
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => {
                    let ty::Array(child, count) = original.kind() else {
                        return Err(
                            "shared Drop projection index lacks original fixed array".into()
                        );
                    };
                    let count = count
                        .try_to_target_usize(self.tcx)
                        .ok_or("shared Drop projection count is not concrete")?;
                    let index = if from_end {
                        count.checked_sub(offset)
                    } else {
                        Some(offset)
                    };
                    if min_length > count
                        || (from_end && offset > min_length)
                        || (!from_end && offset >= min_length)
                        || index.is_none_or(|index| index >= count)
                    {
                        return Err("shared Drop projection constant index metadata differs".into());
                    }
                    original = *child;
                    path.push(MemoryProjection::Index(Box::new(
                        self.iterator_index(u128::from(index.unwrap())),
                    )));
                }
                ProjectionElem::Field(index, recorded) => {
                    let child = field_type(self.tcx, original, index.as_usize())?;
                    if child != recorded {
                        return Err("shared Drop projection recorded FieldTy differs".into());
                    }
                    original = child;
                    path.push(MemoryProjection::Field(index.as_usize()));
                }
                _ => return Err("shared Drop projection supports fixed owned paths only".into()),
            }
        }
        Ok(path)
    }

    fn validate_drop_storage(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
        work: &mut Work,
    ) -> Result<(), String> {
        work.charge(1)?;
        if let Value::Input(input) = value
            && input.shape.slots != 0
        {
            work.charge(3)?;
            self.validate_issued_drop_storage(original, input, work)?;
            if scalar(original) {
                let value = input.materialize()?;
                return self.validate_drop_storage(original, &value, conditions, work);
            }
            return Ok(());
        }
        match original.kind() {
            ty::Array(child, count) => {
                let count = count
                    .try_to_target_usize(self.tcx)
                    .ok_or("shared Drop projection original count is unavailable")?;
                let Value::Elements(elements) = value else {
                    return Err("shared Drop projection requires retained physical elements".into());
                };
                if elements.len() as u64 != count {
                    return Err("shared Drop projection backing count differs".into());
                }
                for value in elements.iter() {
                    self.validate_drop_storage(*child, value, conditions, work)?;
                }
                Ok(())
            }
            ty::Adt(def, args) => {
                if let Value::Input(input) = value {
                    work.charge(3)?;
                    if !def.did().is_local()
                        || !def.is_struct()
                        || def.repr().packed()
                        || def.destructor(self.tcx).is_none()
                        || !def.non_enum_variant().fields.is_empty()
                        || !original.is_freeze(self.tcx, ty::TypingEnv::fully_monomorphized())
                    {
                        return Err(
                            "shared Drop lazy storage requires original fieldless type".into()
                        );
                    }
                    let layout = self
                        .tcx
                        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(original))
                        .map_err(|error| {
                            format!("shared Drop lazy storage layout unavailable: {error:?}")
                        })?;
                    if layout.size.bytes() != 0
                        || layout.is_uninhabited()
                        || input.shape.slots != 0
                        || input.shape.height != 1
                        || !input.seed.belongs_to(&self.terms)
                        || !self
                            .zero_sized_inputs
                            .get(&original)
                            .is_some_and(|shape| Rc::ptr_eq(shape, &input.shape))
                    {
                        return Err("shared Drop lazy storage original descriptor differs".into());
                    }
                    let symbolic::input::InputKind::Struct { name, fields } = &input.shape.kind
                    else {
                        return Err("shared Drop lazy storage needs original empty Struct".into());
                    };
                    if name.len() > 128
                        || *name != self.tcx.def_path_str(def.did())
                        || !fields.is_empty()
                    {
                        return Err(
                            "shared Drop lazy storage empty Struct inventory differs".into()
                        );
                    }
                    return Ok(());
                }
                let Value::Adt {
                    name,
                    variant: 0,
                    is_option: false,
                    discriminant: 0,
                    fields,
                } = value
                else {
                    return Err("shared Drop projection stored original struct differs".into());
                };
                let declarations = &def.non_enum_variant().fields;
                work.charge(fields.len().saturating_mul(2))?;
                if name.len() > 128
                    || *name != self.tcx.def_path_str(def.did())
                    || fields.len() != declarations.len()
                {
                    return Err("shared Drop projection physical field inventory differs".into());
                }
                for ((name, value), declaration) in fields.iter().zip(declarations) {
                    if name.len() > 128 || *name != declaration.name.to_string() {
                        return Err(
                            "shared Drop projection physical field inventory differs".into()
                        );
                    }
                    self.validate_drop_storage(
                        declaration.ty(self.tcx, args).skip_norm_wip(),
                        value,
                        conditions,
                        work,
                    )?;
                }
                Ok(())
            }
            _ if scalar(original) => {
                let shape = self
                    .owned_product_shape(original)?
                    .ok_or("shared Drop projection scalar codec is unsupported")?;
                let prepared = self.prepare_typed_product(original, &shape, value, 0)?;
                self.validate_owned_product(original, &prepared, conditions)
            }
            _ => Err("shared Drop projection stored original type is unsupported".into()),
        }
    }

    fn drop_projection_candidates<'a>(
        &self,
        original: Ty<'tcx>,
        value: &'a Value,
        path: &[MemoryProjection],
        memory: Option<(&Memory, usize)>,
        local_masks: Option<(&State, usize)>,
        conditions: &[Term],
    ) -> Result<Vec<Candidate<'a, 'tcx>>, String> {
        if path.len() > 16 {
            return Err("shared Drop projection exceeds depth16".into());
        }
        let mut work = Work(0);
        if !matches!(value, Value::Input(input) if input.shape.slots != 0) {
            domain(self.tcx, original, 0, &mut work)?;
        }
        let storage = self.drop_storage_candidate(original, value, &mut work)?;
        let mut candidates = vec![Candidate {
            value: storage,
            original,
            mask: self.terms.boolean(true),
            fields: Vec::new(),
        }];
        for part in path {
            let mut next = Vec::new();
            for candidate in candidates {
                work.charge(1)?;
                match part {
                    MemoryProjection::Index(index) => {
                        let ty::Array(child, count) = candidate.original.kind() else {
                            return Err("shared Drop projection lacks original array child".into());
                        };
                        let count = count
                            .try_to_target_usize(self.tcx)
                            .ok_or("shared Drop projection count is not concrete")?;
                        let elements =
                            match candidate.value {
                                Storage::Physical(Value::Elements(elements)) => {
                                    if elements.len() as u64 != count {
                                        return Err(
                                            "shared Drop projection backing count differs".into()
                                        );
                                    }
                                    ArrayStorage::Physical(elements)
                                }
                                Storage::Lazy(input) => ArrayStorage::Lazy(input),
                                Storage::Physical(_) | Storage::Scalar(_) => return Err(
                                    "shared Drop projection requires retained physical elements"
                                        .into(),
                                ),
                            };
                        let (term, bits, signed) = index.integer()?;
                        if signed
                            || bits != u32::from(self.tcx.sess.target.pointer_width)
                            || term.sort() != &Sort::BitVec(bits)
                            || !term.belongs_to(&self.terms)
                        {
                            return Err(
                                "shared Drop projection index Context or usize differs".into()
                            );
                        }
                        let mut active = conditions.to_vec();
                        active.push(candidate.mask.clone());
                        if !self.feasible(&active)? {
                            continue;
                        }
                        self.memory_bounds(
                            index,
                            &self.iterator_index(u128::from(count)),
                            &active,
                        )?;
                        for position in 0..count as usize {
                            work.charge(3)?;
                            let equal = self.terms.apply(
                                Op::Equal,
                                &[term.clone(), self.terms.bit_vector(position as u128, bits)?],
                            )?;
                            let mask = self
                                .terms
                                .apply(Op::And, &[candidate.mask.clone(), equal])?;
                            let mut active = conditions.to_vec();
                            active.push(mask.clone());
                            if !self.feasible(&active)? {
                                continue;
                            }
                            let value = match &elements {
                                ArrayStorage::Physical(elements) => self.drop_storage_candidate(
                                    *child,
                                    &elements[position],
                                    &mut work,
                                )?,
                                ArrayStorage::Lazy(input) => {
                                    let InputKind::Array { element, .. } = &input.shape.kind else {
                                        return Err(
                                            "shared Drop lazy projection lacks array".into()
                                        );
                                    };
                                    let start = element
                                        .slots
                                        .checked_mul(position as u32)
                                        .and_then(|offset| {
                                            input
                                                .start
                                                .checked_add(1)
                                                .and_then(|first| first.checked_add(offset))
                                        })
                                        .ok_or("shared Drop lazy projection offset overflow")?;
                                    Storage::Lazy(LazyStorage {
                                        shape: element,
                                        start,
                                        seed: input.seed,
                                    })
                                }
                            };
                            let mut fields = candidate.fields.clone();
                            fields.push(Step::Element(position));
                            next.push(Candidate {
                                value,
                                original: *child,
                                mask,
                                fields,
                            });
                        }
                    }
                    MemoryProjection::Field(index) => {
                        // A shared receiver must be complete before projecting any scalar field.
                        if let Some((memory, allocation)) = memory {
                            memory.missing_places.check(allocation, &candidate.fields)?;
                        } else if let Some((state, local)) = local_masks {
                            state.missing_places.check(local, &candidate.fields)?;
                        }
                        let child = field_type(self.tcx, candidate.original, *index)?;
                        let ty::Adt(def, _) = candidate.original.kind() else {
                            unreachable!()
                        };
                        let value = match candidate.value {
                            Storage::Physical(value) => {
                                let Value::Adt {
                                    name,
                                    variant: 0,
                                    is_option: false,
                                    discriminant: 0,
                                    fields,
                                } = value
                                else {
                                    return Err(
                                        "shared Drop projection stored original struct differs"
                                            .into(),
                                    );
                                };
                                work.charge(1 + fields.len().saturating_mul(2))?;
                                if name.len() > 128
                                    || fields.iter().any(|(name, _)| name.len() > 128)
                                {
                                    return Err(
                                        "shared Drop projection name exceeds128 bytes".into()
                                    );
                                }
                                if *name != self.tcx.def_path_str(def.did())
                                    || fields.len() != def.non_enum_variant().fields.len()
                                    || fields
                                        .iter()
                                        .zip(&def.non_enum_variant().fields)
                                        .any(|((name, _), field)| *name != field.name.to_string())
                                {
                                    return Err(
                                        "shared Drop projection physical field inventory differs"
                                            .into(),
                                    );
                                }
                                self.drop_storage_candidate(child, &fields[*index].1, &mut work)?
                            }
                            Storage::Lazy(input) => {
                                // Field inventory and original types were checked at root issuance.
                                let InputKind::Struct { fields, .. } = &input.shape.kind else {
                                    return Err("shared Drop lazy projection lacks struct".into());
                                };
                                let mut start = input
                                    .start
                                    .checked_add(1)
                                    .ok_or("shared Drop lazy projection offset overflow")?;
                                for (_, shape) in &fields[..*index] {
                                    work.charge(1)?;
                                    start = start
                                        .checked_add(shape.slots)
                                        .ok_or("shared Drop lazy projection offset overflow")?;
                                }
                                Storage::Lazy(LazyStorage {
                                    shape: &fields[*index].1,
                                    start,
                                    seed: input.seed,
                                })
                            }
                            Storage::Scalar(_) => {
                                return Err(
                                    "shared Drop scalar cannot carry a struct projection".into()
                                );
                            }
                        };
                        let mut keys = candidate.fields;
                        keys.push(Step::Field(*index));
                        next.push(Candidate {
                            value,
                            original: child,
                            mask: candidate.mask,
                            fields: keys,
                        });
                    }
                    _ => return Err("shared Drop projection path has unsupported transport".into()),
                }
            }
            candidates = next;
        }
        if candidates.is_empty() {
            return Err("shared Drop projection has no feasible initialized target".into());
        }
        for candidate in &mut candidates {
            work.charge(1)?;
            let mut active = conditions.to_vec();
            active.push(candidate.mask.clone());
            let decoded = match &candidate.value {
                Storage::Physical(value) => {
                    self.validate_drop_storage(candidate.original, value, &active, &mut work)?;
                    None
                }
                Storage::Lazy(input) if scalar(candidate.original) => {
                    work.charge(1)?;
                    let value = InputValue {
                        shape: input.shape.clone(),
                        start: input.start,
                        seed: input.seed.clone(),
                    }
                    .materialize()?;
                    self.validate_drop_storage(candidate.original, &value, &active, &mut work)?;
                    Some(value)
                }
                // Complete root descriptor/type validation covers composite descendants.
                Storage::Lazy(_) => None,
                Storage::Scalar(_) => return Err("shared Drop scalar was decoded twice".into()),
            };
            if let Some((memory, allocation)) = memory {
                memory.missing_places.check(allocation, &candidate.fields)?;
            } else if let Some((state, local)) = local_masks {
                state.missing_places.check(local, &candidate.fields)?;
            }
            if let Some(value) = decoded {
                // Retain a scalar only after original type, active guard and masks all pass.
                candidate.value = Storage::Scalar(value);
            }
        }
        #[cfg(test)]
        if matches!(value, Value::Input(_)) {
            println!(
                "shared lazy Drop projection: candidates={} nodes={}",
                candidates.len(),
                work.0
            );
        }
        Ok(candidates)
    }

    fn drop_storage_candidate<'a>(
        &self,
        original: Ty<'tcx>,
        value: &'a Value,
        work: &mut Work,
    ) -> Result<Storage<'a>, String> {
        match value {
            Value::Input(input) if input.shape.slots != 0 => {
                self.validate_issued_drop_storage(original, input, work)?;
                Ok(Storage::Lazy(LazyStorage {
                    shape: &input.shape,
                    start: input.start,
                    seed: &input.seed,
                }))
            }
            _ => Ok(Storage::Physical(value)),
        }
    }

    fn drop_storage_scalar(
        &self,
        original: Ty<'tcx>,
        storage: &Storage<'_>,
    ) -> Result<Value, String> {
        if !scalar(original) {
            return Err("shared Drop lazy scalar cannot materialize an owner".into());
        }
        match storage {
            Storage::Physical(value) => Ok((*value).clone()),
            Storage::Scalar(value) => Ok(value.clone()),
            Storage::Lazy(_) => Err("shared Drop scalar lacks a validated decode".into()),
        }
    }

    fn drop_projection_scalar(
        &self,
        candidates: &[Candidate<'_, 'tcx>],
        conditions: &[Term],
    ) -> Result<Value, String> {
        let first = &candidates[0];
        if !scalar(first.original) {
            return Err(
                "shared Drop projection cannot materialize or copy a non-Copy owner".into(),
            );
        }
        let shape = self
            .owned_product_shape(first.original)?
            .ok_or("shared Drop projection scalar codec is unsupported")?;
        let first_value = self.drop_storage_scalar(first.original, &first.value)?;
        let mut result = self.prepare_typed_product(first.original, &shape, &first_value, 0)?;
        self.validate_owned_product(first.original, &result, conditions)?;
        for candidate in candidates.iter().skip(1) {
            if candidate.original != first.original {
                return Err("shared Drop projection candidate scalar types differ".into());
            }
            let physical = self.drop_storage_scalar(candidate.original, &candidate.value)?;
            let value = self.prepare_typed_product(first.original, &shape, &physical, 0)?;
            self.validate_owned_product(first.original, &value, conditions)?;
            result = match (value, result) {
                (
                    Value::Int {
                        expression: left,
                        bits,
                        signed,
                    },
                    Value::Int {
                        expression: right,
                        bits: other_bits,
                        signed: other_signed,
                    },
                ) if bits == other_bits && signed == other_signed => Value::Int {
                    expression: self
                        .terms
                        .apply(Op::Ite, &[candidate.mask.clone(), left, right])?,
                    bits,
                    signed,
                },
                (Value::Bool(left), Value::Bool(right)) => Value::Bool(
                    self.terms
                        .apply(Op::Ite, &[candidate.mask.clone(), left, right])?,
                ),
                (
                    Value::Float {
                        expression: left,
                        bits,
                        raw_bits: left_raw,
                    },
                    Value::Float {
                        expression: right,
                        bits: other_bits,
                        raw_bits: right_raw,
                    },
                ) if bits == other_bits => Value::Float {
                    expression: self
                        .terms
                        .apply(Op::Ite, &[candidate.mask.clone(), left, right])?,
                    bits,
                    raw_bits: left_raw
                        .zip(right_raw)
                        .map(|(left, right)| {
                            self.terms
                                .apply(Op::Ite, &[candidate.mask.clone(), left, right])
                        })
                        .transpose()?,
                },
                _ => return Err("shared Drop projection scalar representations differ".into()),
            };
        }
        Ok(result)
    }

    fn drop_shared_deref_view(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let Some((ProjectionElem::Deref, suffix)) = place.projection.split_first() else {
            return Ok(None);
        };
        let local = place.local.as_usize();
        let carrier = if let Some(allocation) = state.addresses[local] {
            state.memory.get(allocation).and_then(Option::as_ref)
        } else {
            state.locals[local].as_ref()
        };
        let Some(Value::Reference {
            allocation,
            projection,
            mutable,
        }) = carrier
        else {
            return Ok(None);
        };
        let Some((witness, original_path)) = self.drop_reference_path(*allocation, projection)?
        else {
            return Ok(None);
        };
        self.check_local_initialization(state, local, &[])?;
        if *mutable {
            return Err("shared Drop projection grants no mutable reference authority".into());
        }
        state.flow.require_unarmed()?;
        self.drop_projection_body(body)?;
        self.check_drop_shared_reference(
            *allocation,
            projection,
            &state.memory,
            &state.conditions,
        )?;
        let storage = state
            .memory
            .get(*allocation)
            .and_then(Option::as_ref)
            .ok_or("shared Drop projection owner is not live")?;
        let candidates = self.drop_projection_candidates(
            witness.original,
            storage,
            &original_path,
            Some((&state.memory, *allocation)),
            None,
            &state.conditions,
        )?;
        let original = candidates[0].original;
        if !matches!(body.local_decls[place.local].ty.kind(), ty::Ref(_, target,
            rustc_hir::Mutability::Not) if *target == original)
        {
            return Err("shared Drop projection current receiver type differs".into());
        }
        let extension = self.drop_projection_parts(body, state, original, suffix)?;
        let mut path = projection.clone();
        path.extend(extension);
        Ok(Some(Value::Reference {
            allocation: *allocation,
            projection: path,
            mutable: false,
        }))
    }

    pub(super) fn read_drop_shared_deref(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let Some(view) = self.drop_shared_deref_view(body, state, place)? else {
            return Ok(None);
        };
        self.read_drop_shared_reference(&view, &state.memory, &state.conditions)
    }

    pub(super) fn reborrow_drop_shared_view(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let Some(view) = self.drop_shared_deref_view(body, state, place)? else {
            return Ok(None);
        };
        let original = place.ty(&body.local_decls, self.tcx).ty;
        if !scalar(original) && !readonly_drop_struct(self.tcx, original) {
            return Err(
                "shared Drop projection cannot materialize or copy a non-Copy owner".into(),
            );
        }
        let Value::Reference {
            allocation,
            projection,
            mutable: false,
        } = &view
        else {
            return Err("shared Drop readonly reborrow lacks its storage view".into());
        };
        self.check_drop_shared_reference(
            *allocation,
            projection,
            &state.memory,
            &state.conditions,
        )?;
        Ok(Some(view))
    }

    pub(super) fn read_drop_shared_place(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let original = body.local_decls[place.local].ty;
        if !self.drop_shared_place_candidate(body, place) {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        self.drop_projection_original(original)?;
        self.drop_projection_body(body)?;
        let path = self.drop_projection_path(body, state, place)?;
        if !scalar(place.ty(&body.local_decls, self.tcx).ty) {
            return Ok(None);
        }
        let local = place.local.as_usize();
        let allocation = state.addresses[local];
        let value = if let Some(allocation) = allocation {
            self.check_initialized_owner_type(&state.memory, allocation, original)?;
            state.memory.get(allocation).and_then(Option::as_ref)
        } else {
            state.locals[local].as_ref()
        }
        .ok_or("shared Drop projection owner is not live")?;
        let candidates = self.drop_projection_candidates(
            original,
            value,
            &path,
            allocation.map(|allocation| (&state.memory, allocation)),
            allocation.is_none().then_some((state, local)),
            &state.conditions,
        )?;
        self.drop_projection_scalar(&candidates, &state.conditions)
            .map(Some)
    }

    pub(super) fn borrow_drop_shared_place(
        &mut self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let original = body.local_decls[place.local].ty;
        if !self.drop_shared_place_candidate(body, place) {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        self.drop_projection_original(original)?;
        let (instance, actual) = self.drop_projection_body(body)?;
        let path = self.drop_projection_path(body, state, place)?;
        let local = place.local.as_usize();
        let value = if let Some(allocation) = state.addresses[local] {
            self.check_initialized_owner_type(&state.memory, allocation, original)?;
            state.memory.get(allocation).and_then(Option::as_ref)
        } else {
            state.locals[local].as_ref()
        }
        .ok_or("shared Drop projection owner is not live")?;
        self.drop_projection_candidates(
            original,
            value,
            &path,
            state.addresses[local].map(|allocation| (&state.memory, allocation)),
            state.addresses[local].is_none().then_some((&*state, local)),
            &state.conditions,
        )?;
        if self.owned_projection_certificates.len() >= 512 {
            return Err("shared Drop projection certificate exceeds its 512-node bound".into());
        }
        let root = Place::from(place.local);
        self.preflight_initialized_owner(body, state, root)?;
        let allocation = if let Some(allocation) = state.addresses[local] {
            allocation
        } else {
            let allocation = state.memory.len();
            let mut masks = state.memory.missing_places.clone();
            let mut locals = state.missing_places.clone();
            locals.transfer(local, allocation, &mut masks)?;
            let storage = state.locals[local]
                .take()
                .ok_or("shared Drop owner is unavailable")?;
            state.memory.push(Some(storage));
            state.memory.missing_places = masks;
            state.missing_places = locals;
            state.addresses[local] = Some(allocation);
            allocation
        };
        self.bind_initialized_owner(body, state, root)?;
        let witness = Witness {
            instance,
            body: Rc::downgrade(&actual),
            allocation,
            original,
        };
        let certificate = self.owned_projection_certificates.len();
        self.owned_projection_certificates.push(
            owned_shared_projections::OwnedProjectionCertificate {
                original,
                fields: Vec::new(),
                drop_shared: Some(witness),
            },
        );
        let Some((MemoryProjection::Index(index), rest)) = path.split_first() else {
            unreachable!()
        };
        let mut projection = vec![MemoryProjection::TypedIndex {
            index: index.clone(),
            certificate,
        }];
        projection.extend_from_slice(rest);
        self.record_model(
            instance.def_id(),
            "shared Drop storage projection; scalar observations only",
        );
        Ok(Some(Value::Reference {
            allocation,
            projection,
            mutable: false,
        }))
    }

    fn drop_reference_path<'a>(
        &self,
        allocation: usize,
        path: &'a [MemoryProjection],
    ) -> Result<Option<(&Witness<'tcx>, Vec<MemoryProjection>)>, String> {
        let Some((MemoryProjection::TypedIndex { index, certificate }, rest)) = path.split_first()
        else {
            return Ok(None);
        };
        let entry = self
            .owned_projection_certificates
            .get(*certificate)
            .ok_or("shared typed projection certificate is unavailable")?;
        let Some(witness) = &entry.drop_shared else {
            return Ok(None);
        };
        if witness.allocation != allocation {
            return Err("shared Drop projection belongs to a different allocation".into());
        }
        if !matches!(witness.instance.def, ty::InstanceKind::Item(_))
            || !self.tcx.is_mir_available(witness.instance.def_id())
        {
            return Err(self.missing_body_reason(witness.instance.def_id()));
        }
        let body = witness
            .body
            .upgrade()
            .ok_or("shared Drop projection caller Body expired")?;
        if !Rc::ptr_eq(&body, &self.instantiated_body(witness.instance)?)
            || body.source.instance != witness.instance.def
            || body.source.promoted.is_some()
        {
            return Err("shared Drop projection current caller Body differs".into());
        }
        let mut path = vec![MemoryProjection::Index(index.clone())];
        path.extend_from_slice(rest);
        Ok(Some((witness, path)))
    }

    pub(super) fn check_drop_shared_reference(
        &self,
        allocation: usize,
        path: &[MemoryProjection],
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<bool, String> {
        let Some((witness, path)) = self.drop_reference_path(allocation, path)? else {
            return Ok(false);
        };
        let (_, original) = self
            .typed_memory_evidence(memory, allocation, &[])?
            .ok_or("shared Drop projection original owner evidence is unavailable")?;
        if original != witness.original {
            return Err("shared Drop projection original owner type differs".into());
        }
        let value = memory
            .get(allocation)
            .and_then(Option::as_ref)
            .ok_or("shared Drop projection owner is not live")?;
        self.drop_projection_candidates(
            original,
            value,
            &path,
            Some((memory, allocation)),
            None,
            conditions,
        )?;
        Ok(true)
    }

    pub(super) fn shared_drop_reference_target(
        &self,
        reference: &Value,
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<Option<Ty<'tcx>>, String> {
        let Value::Reference {
            allocation,
            projection,
            mutable,
        } = reference
        else {
            return Ok(None);
        };
        let Some((witness, path)) = self.drop_reference_path(*allocation, projection)? else {
            return Ok(None);
        };
        if *mutable {
            return Err("shared Drop projection grants no mutable reference authority".into());
        }
        self.check_drop_shared_reference(*allocation, projection, memory, conditions)?;
        let value = memory
            .get(*allocation)
            .and_then(Option::as_ref)
            .ok_or("shared Drop receiver owner is not live")?;
        let candidates = self.drop_projection_candidates(
            witness.original,
            value,
            &path,
            Some((memory, *allocation)),
            None,
            conditions,
        )?;
        // Candidate construction rejects an entirely infeasible domain before returning.
        let original = candidates
            .first()
            .ok_or("shared Drop receiver has no feasible candidate")?
            .original;
        if candidates
            .iter()
            .any(|candidate| candidate.original != original)
        {
            return Err("shared Drop receiver candidate original types differ".into());
        }
        if readonly_drop_struct(self.tcx, original) {
            Ok(Some(original))
        } else {
            Ok(None)
        }
    }

    pub(super) fn read_drop_shared_reference(
        &self,
        reference: &Value,
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        let Value::Reference {
            allocation,
            projection,
            mutable,
        } = reference
        else {
            return Ok(None);
        };
        let Some((witness, path)) = self.drop_reference_path(*allocation, projection)? else {
            return Ok(None);
        };
        if *mutable {
            return Err("shared Drop projection grants no mutable reference authority".into());
        }
        self.check_drop_shared_reference(*allocation, projection, memory, conditions)?;
        let value = memory
            .get(*allocation)
            .and_then(Option::as_ref)
            .ok_or("shared Drop projection owner is not live")?;
        let candidates = self.drop_projection_candidates(
            witness.original,
            value,
            &path,
            Some((memory, *allocation)),
            None,
            conditions,
        )?;
        self.drop_projection_scalar(&candidates, conditions)
            .map(Some)
    }
}

#[cfg(test)]
#[path = "drop_shared_projections_probe.rs"]
mod probe;
