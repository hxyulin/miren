use super::*;
use rustc_middle::mir::PlaceElem;
use rustc_middle::ty::TypeVisitableExt;
use rustc_middle::ty::adjustment::PointerCoercion;

// Engineering work policy, independent of registry, array, Repeat and execution limits.
const MAX_SHARED_TRAIT_CHOICE_WORK: usize = 2048;

/// Compiler types retained at a concrete reference unsizing site. This is not a vtable address
/// and is never constructed for an arbitrary trait-object input.
#[derive(Clone, Copy, PartialEq)]
pub(super) struct TraitObject<'tcx> {
    concrete: Ty<'tcx>,
    object: Ty<'tcx>,
}

/// A choice keeps its entire executable backing graph in Value::TraitObject::source.
/// Receipts authenticate that graph; they never supply hidden receiver storage.
#[derive(Clone)]
pub(super) enum Witness<'tcx> {
    Concrete(TraitObject<'tcx>),
    SharedChoice(SharedChoice<'tcx>),
}

#[derive(Clone)]
pub(super) struct SharedChoice<'tcx> {
    object: Ty<'tcx>,
    leaves: Vec<SharedLeaf>,
}

#[derive(Clone)]
struct SharedLeaf {
    witness: usize,
    allocation: usize,
    fields: Vec<(bool, usize)>,
    mask: Term,
}

impl SharedChoice<'_> {
    fn cost(&self) -> Result<usize, String> {
        if self.leaves.is_empty() || self.leaves.len() > aggregates::MAX_ARRAY_ELEMENTS {
            return Err("shared trait choice has an invalid leaf extent".into());
        }
        self.leaves.iter().try_fold(1_usize, |cost, leaf| {
            if leaf.fields.len() > 16 {
                return Err("shared trait choice projection exceeds depth16".into());
            }
            cost.checked_add(4 + leaf.fields.len())
                .ok_or_else(|| "shared trait choice cost overflows".into())
        })
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn trait_object_coercion(
        &mut self,
        kind: PointerCoercion,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: Value,
        state: &State,
    ) -> Result<Option<Value>, String> {
        let ty::Ref(_, object, target_mutability) = target.kind() else {
            return Ok(None);
        };
        let ty::Dynamic(predicates, _) = object.kind() else {
            return Ok(None);
        };
        let ty::Ref(_, concrete, source_mutability) = source.kind() else {
            return Err("trait-object unsizing needs a concrete reference".into());
        };
        if kind == PointerCoercion::Unsize
            && self.tcx.erase_and_anonymize_regions(*concrete)
                == self.tcx.erase_and_anonymize_regions(*object)
        {
            let Value::TraitObject {
                source,
                id,
                place: false,
            } = value
            else {
                return Err("trait-object identity unsizing needs its concrete witness".into());
            };
            if self.trait_object_original(id)? != self.tcx.erase_and_anonymize_regions(*object) {
                return Err("trait-object identity unsizing changes the witnessed type".into());
            }
            return self
                .borrow_trait_object(&source, id, target_mutability.is_mut(), state)
                .map(Some);
        }
        if kind == PointerCoercion::Unsize && matches!(concrete.kind(), ty::Dynamic(..)) {
            return self
                .trait_object_upcast(
                    *concrete,
                    *object,
                    (source_mutability.is_mut(), target_mutability.is_mut()),
                    value,
                    state,
                )
                .map(Some);
        }
        if kind != PointerCoercion::Unsize
            || !concrete.is_sized(self.tcx, ty::TypingEnv::fully_monomorphized())
            || (target_mutability.is_mut() && !source_mutability.is_mut())
        {
            return Err(format!(
                "only concrete reference trait-object unsizing is modeled: \
                 {kind:?}, {source:?} to {target:?}"
            ));
        }
        let unsize = self
            .tcx
            .lang_items()
            .get(LangItem::Unsize)
            .ok_or("trait-object coercion has no compiler Unsize trait")?;
        let obligation = ty::TraitRef::new(self.tcx, unsize, [*concrete, *object]);
        self.tcx
            .codegen_select_candidate(
                ty::TypingEnv::fully_monomorphized().as_query_input(obligation),
            )
            .map_err(|error| {
                format!("compiler trait-object unsizing is not established: {error:?}")
            })?;
        let principal = predicates
            .principal()
            .ok_or("trait-object coercion needs a principal trait")?;
        let entry = TraitObject {
            concrete: self.tcx.erase_and_anonymize_regions(*concrete),
            object: self.tcx.erase_and_anonymize_regions(*object),
        };
        // Force the compiler's concrete vtable query here, rather than inferring dispatch by
        // enumerating implementations or guessing the meaning of a numeric metadata pointer.
        let trait_ref = principal
            .skip_binder()
            .with_self_ty(self.tcx, entry.concrete);
        let entries = self
            .tcx
            .vtable_entries(self.tcx.erase_and_anonymize_regions(trait_ref));
        if entries.len() < TyCtxt::COMMON_VTABLE_ENTRIES.len() {
            return Err("concrete trait-object vtable has no compiler metadata header".into());
        }
        self.validate_tracked_value(&value, state)?;
        self.static_store_value(source, &value, state, 0, &mut 0)?;
        let value = self.trait_object_source(value, target_mutability.is_mut())?;
        let id = self.insert_concrete_trait_object(entry)?;
        Ok(Some(Value::TraitObject {
            source: Box::new(value),
            id,
            place: false,
        }))
    }

    fn trait_object_upcast(
        &mut self,
        source_object: Ty<'tcx>,
        target_object: Ty<'tcx>,
        mutability: (bool, bool),
        value: Value,
        state: &State,
    ) -> Result<Value, String> {
        let (source_mutable, target_mutable) = mutability;
        if target_mutable && !source_mutable {
            return Err("trait-object upcast cannot grant mutable receiver rights".into());
        }
        let Value::TraitObject {
            source,
            id,
            place: false,
        } = value
        else {
            return Err("trait-object upcast needs a retained concrete witness".into());
        };
        if let Some(choice) = self.shared_trait_descriptor(id)? {
            return self.upcast_shared_trait_choice(
                source_object,
                target_object,
                mutability,
                *source,
                choice,
                state,
            );
        }
        let witness = self.concrete_trait_object(id)?;
        let source_object = self.tcx.erase_and_anonymize_regions(source_object);
        let target_object = self.tcx.erase_and_anonymize_regions(target_object);
        if source_object.has_non_region_param()
            || source_object.has_non_region_infer()
            || target_object.has_non_region_param()
            || target_object.has_non_region_infer()
        {
            return Err("trait-object upcast needs fully monomorphized compiler types".into());
        }
        if witness.object != source_object {
            return Err("trait-object upcast source differs from its concrete witness".into());
        }
        let ty::Dynamic(source_predicates, _) = source_object.kind() else {
            return Err("trait-object upcast source has no dynamic principal".into());
        };
        let ty::Dynamic(target_predicates, _) = target_object.kind() else {
            return Err("trait-object upcast target has no dynamic principal".into());
        };
        let source_principal = source_predicates
            .principal()
            .ok_or("trait-object upcast source needs a principal trait")?;
        let target_principal = target_predicates
            .principal()
            .ok_or("trait-object upcast target needs a principal trait")?;
        let unsize = self
            .tcx
            .lang_items()
            .get(LangItem::Unsize)
            .ok_or("trait-object upcast has no compiler Unsize trait")?;
        for from in [source_object, witness.concrete] {
            let obligation = ty::TraitRef::new(self.tcx, unsize, [from, target_object]);
            self.tcx
                .codegen_select_candidate(
                    ty::TypingEnv::fully_monomorphized().as_query_input(obligation),
                )
                .map_err(|error| {
                    format!("compiler trait-object upcast is not established: {error:?}")
                })?;
        }
        let source_trait = source_principal
            .no_bound_vars()
            .ok_or("trait-object upcast source principal has bound variables")?
            .with_self_ty(self.tcx, witness.concrete);
        let target_trait = target_principal
            .no_bound_vars()
            .ok_or("trait-object upcast target principal has bound variables")?
            .with_self_ty(self.tcx, witness.concrete);
        let source_entries = self.tcx.vtable_entries(source_trait);
        let target_entries = self.tcx.vtable_entries(target_trait);
        let header = TyCtxt::COMMON_VTABLE_ENTRIES;
        if !source_entries.starts_with(header) || !target_entries.starts_with(header) {
            return Err("trait-object upcast needs exact compiler metadata headers".into());
        }
        match self
            .tcx
            .supertrait_vtable_slot((source_object, target_object))
        {
            Some(slot) => {
                let Some(ty::VtblEntry::TraitVPtr(actual)) = source_entries.get(slot) else {
                    return Err(
                        "trait-object upcast slot is not a compiler supertrait pointer".into(),
                    );
                };
                if self.tcx.erase_and_anonymize_regions(*actual) != target_trait {
                    return Err("trait-object upcast supertrait pointer changes its target".into());
                }
            }
            None => {
                if !source_entries.starts_with(target_entries) {
                    return Err(
                        "trait-object upcast reused vtable lacks exact target prefix".into(),
                    );
                }
            }
        }
        self.validate_tracked_value(&source, state)?;
        let source = self.trait_object_source(*source, target_mutable)?;
        let entry = TraitObject {
            concrete: witness.concrete,
            object: target_object,
        };
        let id = self.insert_concrete_trait_object(entry)?;
        Ok(Value::TraitObject {
            source: Box::new(source),
            id,
            place: false,
        })
    }

    fn trait_object_source(&self, value: Value, mutable: bool) -> Result<Value, String> {
        if let Value::Reference {
            allocation,
            projection,
            mutable: writable,
        } = value
        {
            if mutable && !writable {
                return Err("mutable trait-object receiver needs writable backing".into());
            }
            return Ok(Value::Reference {
                allocation,
                projection,
                mutable,
            });
        }
        if mutable {
            return Err("mutable trait-object receiver needs retained reference storage".into());
        }
        if matches!(value, Value::TraitObject { .. }) {
            return Err("trait-object upcasting needs an authenticated supertrait vtable".into());
        }
        Ok(value)
    }

    pub(super) fn borrow_trait_object(
        &self,
        source: &Value,
        id: usize,
        mutable: bool,
        state: &State,
    ) -> Result<Value, String> {
        self.trait_object_original(id)?;
        self.validate_shared_trait_bundle(source, id)?;
        if mutable && self.shared_trait_descriptor(id)?.is_some() {
            return Err("shared trait choice cannot grant mutable receiver rights".into());
        }
        self.validate_tracked_value(source, state)?;
        Ok(Value::TraitObject {
            source: Box::new(self.trait_object_source(source.clone(), mutable)?),
            id,
            place: false,
        })
    }

    pub(super) fn resolve_trait_object_call(
        &self,
        instance: ty::Instance<'tcx>,
        values: &mut [Value],
        state: &State,
    ) -> Result<ty::Instance<'tcx>, String> {
        let ty::InstanceKind::Virtual(method, slot) = instance.def else {
            return Ok(instance);
        };
        let receiver = values.first_mut().ok_or("virtual call has no receiver")?;
        let Value::TraitObject {
            source,
            id,
            place: false,
        } = receiver
        else {
            return Err("virtual call needs a concrete trait-object coercion witness".into());
        };
        self.validate_tracked_value(source, state)?;
        let witness = self.concrete_trait_object(*id)?;
        let dynamic = self
            .tcx
            .erase_and_anonymize_regions(instance.args.type_at(0));
        if dynamic != witness.object {
            return Err("virtual-call Self type differs from its coercion witness".into());
        }
        let ty::Dynamic(predicates, _) = witness.object.kind() else {
            return Err("virtual-call witness is not a trait object".into());
        };
        let principal = predicates
            .principal()
            .ok_or("virtual-call witness has no principal trait")?;
        let trait_ref = principal
            .skip_binder()
            .with_self_ty(self.tcx, witness.concrete);
        let entries = self
            .tcx
            .vtable_entries(self.tcx.erase_and_anonymize_regions(trait_ref));
        let Some(ty::VtblEntry::Method(target)) = entries.get(slot) else {
            return Err("virtual-call slot is not a compiler vtable method".into());
        };
        let args = self
            .tcx
            .mk_args_from_iter(instance.args.iter().enumerate().map(|(index, argument)| {
                if index == 0 {
                    witness.concrete.into()
                } else {
                    argument
                }
            }));
        let resolved = self.resolve_function_item(method, args)?;
        if self.tcx.erase_and_anonymize_regions(resolved)
            != self.tcx.erase_and_anonymize_regions(*target)
            || !matches!(resolved.def, ty::InstanceKind::Item(_))
        {
            return Err("concrete method resolution differs from its compiler vtable slot".into());
        }
        let signature = self.call_poly_signature(resolved)?.skip_binder();
        let Some(receiver_ty) = signature.inputs().first() else {
            return Err("concrete vtable method has no receiver".into());
        };
        let ty::Ref(_, pointee, mutability) = receiver_ty.kind() else {
            return Err("only reference trait-object receivers are modeled".into());
        };
        if self.tcx.erase_and_anonymize_regions(*pointee) != witness.concrete {
            return Err("concrete vtable receiver differs from its coercion type".into());
        }
        *receiver = self.trait_object_source((**source).clone(), mutability.is_mut())?;
        Ok(resolved)
    }
}

impl<'tcx> Engine<'tcx> {
    #[cfg_attr(test, track_caller)]
    fn shared_trait_fee(&self, amount: usize) -> Result<(), String> {
        let current = self.trait_object_choice_work.get();
        let next = current.checked_add(amount);
        let Some(next) = next.filter(|next| *next <= MAX_SHARED_TRAIT_CHOICE_WORK) else {
            #[cfg(test)]
            eprintln!(
                "Shared trait fee refusal: current={current}; amount={amount}; \
                 attempt={next:?}; limit={MAX_SHARED_TRAIT_CHOICE_WORK}; site={}",
                std::panic::Location::caller(),
            );
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                format!(
                    "shared trait choice exceeds cumulative{MAX_SHARED_TRAIT_CHOICE_WORK} work"
                ),
            ));
        };
        self.trait_object_choice_work.set(next);
        Ok(())
    }

    fn insert_concrete_trait_object(&self, entry: TraitObject<'tcx>) -> Result<usize, String> {
        let mut registry = self.trait_objects.borrow_mut();
        if self.trait_object_choices_issued.get() {
            self.shared_trait_fee(registry.len().saturating_add(1))?;
        }
        if let Some(id) = registry
            .iter()
            .position(|item| matches!(item, Witness::Concrete(actual) if *actual == entry))
        {
            return Ok(id);
        }
        if registry.len() >= 512 {
            return Err("concrete trait-object registry exceeds 512 witnesses".into());
        }
        let id = registry.len();
        registry.push(Witness::Concrete(entry));
        Ok(id)
    }

    fn concrete_trait_object(&self, id: usize) -> Result<TraitObject<'tcx>, String> {
        match self.trait_objects.borrow().get(id) {
            Some(Witness::Concrete(entry)) => Ok(*entry),
            Some(Witness::SharedChoice(_)) => {
                Err("shared trait choice requires evaluated branch dispatch".into())
            }
            None => Err("trait-object coercion witness is missing".into()),
        }
    }

    fn trait_object_original(&self, id: usize) -> Result<Ty<'tcx>, String> {
        match self.trait_objects.borrow().get(id) {
            Some(Witness::Concrete(entry)) => Ok(entry.object),
            Some(Witness::SharedChoice(entry)) => Ok(entry.object),
            None => Err("trait-object coercion witness is missing".into()),
        }
    }

    fn shared_trait_descriptor(&self, id: usize) -> Result<Option<SharedChoice<'tcx>>, String> {
        let registry = self.trait_objects.borrow();
        match registry.get(id) {
            Some(Witness::Concrete(_)) => Ok(None),
            Some(Witness::SharedChoice(entry)) => {
                self.shared_trait_fee(entry.cost()?)?;
                Ok(Some(entry.clone()))
            }
            None => Err("trait-object coercion witness is missing".into()),
        }
    }

    fn shared_trait_reference(&self, value: &Value, mask: Term) -> Result<SharedLeaf, String> {
        let Value::TraitObject {
            source,
            id,
            place: false,
        } = value
        else {
            return Err("shared trait choice needs a concrete reference witness".into());
        };
        self.concrete_trait_object(*id)?;
        let Value::Reference {
            allocation,
            projection,
            mutable: false,
        } = source.as_ref()
        else {
            return Err("shared trait choice needs retained shared Reference backing".into());
        };
        if projection.len() > 16 || mask.sort() != &Sort::Bool || !mask.belongs_to(&self.terms) {
            return Err("shared trait choice source or mask has a different context".into());
        }
        self.shared_trait_fee(4 + projection.len())?;
        let mut fields = Vec::with_capacity(projection.len());
        for part in projection {
            match part {
                symbolic::MemoryProjection::Field(field) => fields.push((false, *field)),
                symbolic::MemoryProjection::Variant(variant) => fields.push((true, *variant)),
                symbolic::MemoryProjection::Index(_)
                | symbolic::MemoryProjection::TypedIndex { .. }
                | symbolic::MemoryProjection::Slice { .. }
                | symbolic::MemoryProjection::Chunks { .. } => {
                    return Err("shared trait choice needs an exact fixed receiver path".into());
                }
            }
        }
        Ok(SharedLeaf {
            witness: *id,
            allocation: *allocation,
            fields,
            mask,
        })
    }

    pub(super) fn validate_shared_trait_bundle(
        &self,
        source: &Value,
        id: usize,
    ) -> Result<(), String> {
        let registry = self.trait_objects.borrow();
        let choice = match registry.get(id) {
            Some(Witness::Concrete(_)) => return Ok(()),
            Some(Witness::SharedChoice(choice)) => choice,
            None => return Err("trait-object coercion witness is missing".into()),
        };
        let Value::Elements(values) = source else {
            return Err("shared trait choice lacks its complete executable backing bundle".into());
        };
        if values.len() != choice.leaves.len()
            || values.is_empty()
            || values.len() > aggregates::MAX_ARRAY_ELEMENTS
        {
            return Err("shared trait choice backing extent differs from its receipt".into());
        }
        self.shared_trait_fee(1 + values.len())?;
        for (value, leaf) in values.iter().zip(&choice.leaves) {
            let Value::TraitObject {
                source,
                id: actual_id,
                place: false,
            } = value
            else {
                return Err("shared trait choice contains a non-concrete backing value".into());
            };
            let Value::Reference {
                allocation,
                projection,
                mutable: false,
            } = source.as_ref()
            else {
                return Err("shared trait choice needs retained shared Reference backing".into());
            };
            if projection.len() > 16
                || projection.len() != leaf.fields.len()
                || leaf.mask.sort() != &Sort::Bool
                || !leaf.mask.belongs_to(&self.terms)
            {
                return Err("shared trait choice source or mask has a different context".into());
            }
            self.shared_trait_fee(3 + projection.len())?;
            let same_path = projection
                .iter()
                .zip(&leaf.fields)
                .all(|(part, (variant, field))| match part {
                    symbolic::MemoryProjection::Field(actual) => !variant && actual == field,
                    symbolic::MemoryProjection::Variant(actual) => *variant && actual == field,
                    symbolic::MemoryProjection::Index(_)
                    | symbolic::MemoryProjection::TypedIndex { .. }
                    | symbolic::MemoryProjection::Slice { .. }
                    | symbolic::MemoryProjection::Chunks { .. } => false,
                });
            let same_type = matches!(registry.get(*actual_id),
                Some(Witness::Concrete(entry)) if entry.object == choice.object);
            if *actual_id != leaf.witness
                || *allocation != leaf.allocation
                || !same_path
                || !same_type
            {
                return Err(
                    "shared trait choice executable source differs from its receipt".into(),
                );
            }
        }
        Ok(())
    }

    fn publish_shared_trait_choice(
        &self,
        object: Ty<'tcx>,
        values: Vec<Value>,
        masks: Vec<Term>,
        state: &State,
    ) -> Result<Value, String> {
        state.flow.require_unarmed()?;
        if values.is_empty()
            || values.len() != masks.len()
            || values.len() > aggregates::MAX_ARRAY_ELEMENTS
        {
            return Err("shared trait choice exceeds its existing fixed-array extent".into());
        }
        self.shared_trait_fee(1 + values.len())?;
        let mut leaves = Vec::with_capacity(values.len());
        for (value, mask) in values.iter().zip(masks) {
            self.validate_tracked_value(value, state)?;
            let leaf = self.shared_trait_reference(value, mask)?;
            if self.concrete_trait_object(leaf.witness)?.object != object {
                return Err("shared trait choice changes an original object type".into());
            }
            leaves.push(leaf);
        }
        self.shared_trait_fee(1 + leaves.len())?;
        let mut registry = self.trait_objects.borrow_mut();
        if registry.len() >= 512 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "shared trait choice registry exceeds512 witnesses".into(),
            ));
        }
        let id = registry.len();
        registry.push(Witness::SharedChoice(SharedChoice { object, leaves }));
        self.trait_object_choices_issued.set(true);
        Ok(Value::TraitObject {
            source: Box::new(Value::Elements(values.into())),
            id,
            place: false,
        })
    }

    pub(super) fn shared_trait_object_choice(
        &self,
        original: Ty<'tcx>,
        elements: &[Value],
        index: &Value,
        conditions: &[Term],
        state: &State,
    ) -> Result<Option<Value>, String> {
        let element = match original.kind() {
            ty::Array(element, _) | ty::Slice(element) => *element,
            _ => return Ok(None),
        };
        let ty::Ref(_, object, mutability) = element.kind() else {
            return Ok(None);
        };
        if mutability.is_mut() || !matches!(object.kind(), ty::Dynamic(..)) {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        if let ty::Array(_, count) = original.kind()
            && count.try_to_target_usize(self.tcx) != Some(elements.len() as u64)
        {
            return Err("shared trait choice differs from its compiler array extent".into());
        }
        if elements.is_empty() || elements.len() > aggregates::MAX_ARRAY_ELEMENTS {
            return Err("shared trait choice exceeds its existing fixed-array extent".into());
        }
        let object = self.tcx.erase_and_anonymize_regions(*object);
        if object.has_non_region_param() || object.has_non_region_infer() {
            return Err(
                "shared trait choice needs fully instantiated original object types".into(),
            );
        }
        let (index, bits, signed) = index.integer()?;
        if signed
            || bits != u32::from(self.tcx.sess.target.pointer_width)
            || index.sort() != &Sort::BitVec(bits)
            || !index.belongs_to(&self.terms)
        {
            return Err("shared trait choice needs original target usize in its context".into());
        }
        self.shared_trait_type_work(object, 0)?;
        self.shared_trait_fee(1 + elements.len() + conditions.len())?;
        let mut values = Vec::new();
        let mut masks = Vec::new();
        for (position, value) in elements.iter().enumerate() {
            self.validate_tracked_value(value, state)?;
            let mask = self.terms.apply(
                Op::Equal,
                &[
                    index.clone(),
                    self.terms.bit_vector(position as u128, bits)?,
                ],
            )?;
            if let Value::TraitObject {
                source,
                id,
                place: false,
            } = value
                && let Some(choice) = self.shared_trait_descriptor(*id)?
            {
                self.validate_shared_trait_bundle(source, *id)?;
                if choice.object != object {
                    return Err("nested shared trait choice changes original object type".into());
                }
                let Value::Elements(children) = source.as_ref() else {
                    return Err("nested shared trait choice has no backing bundle".into());
                };
                self.shared_trait_fee(children.len())?;
                for (child, leaf) in children.iter().zip(choice.leaves) {
                    if values.len() >= aggregates::MAX_ARRAY_ELEMENTS {
                        return Err(
                            "nested shared trait choice exceeds its fixed-array extent".into()
                        );
                    }
                    values.push(child.clone());
                    masks.push(self.terms.apply(Op::And, &[mask.clone(), leaf.mask])?);
                }
            } else {
                self.shared_trait_reference(value, mask.clone())?;
                self.shared_trait_fee(1)?;
                values.push(value.clone());
                masks.push(mask);
            }
        }
        self.shared_trait_fee(masks.len() + conditions.len())?;
        let covered = self.terms.apply(Op::Or, &masks)?;
        let mut uncovered = conditions.to_vec();
        uncovered.push(symbolic::not(&covered));
        if self.feasible(&uncovered)? {
            return Err("shared trait choice lacks proven current mask coverage".into());
        }
        self.publish_shared_trait_choice(object, values, masks, state)
            .map(Some)
    }

    fn upcast_shared_trait_choice(
        &mut self,
        source_object: Ty<'tcx>,
        target_object: Ty<'tcx>,
        mutability: (bool, bool),
        source: Value,
        choice: SharedChoice<'tcx>,
        state: &State,
    ) -> Result<Value, String> {
        if mutability.1 || self.tcx.erase_and_anonymize_regions(source_object) != choice.object {
            return Err("shared trait choice upcast changes type or grants mutable rights".into());
        }
        let Value::Elements(values) = source else {
            return Err("shared trait choice upcast lacks its complete backing".into());
        };
        if values.len() != choice.leaves.len() {
            return Err("shared trait choice upcast has a different receipt extent".into());
        }
        self.shared_trait_fee(choice.cost()?)?;
        let mut mapped = Vec::with_capacity(values.len());
        let mut masks = Vec::with_capacity(values.len());
        for (value, leaf) in values.iter().zip(choice.leaves) {
            let receipt = self.shared_trait_reference(value, leaf.mask.clone())?;
            if receipt.witness != leaf.witness
                || receipt.allocation != leaf.allocation
                || receipt.fields != leaf.fields
            {
                return Err("shared trait choice upcast source differs from its receipt".into());
            }
            mapped.push(self.trait_object_upcast(
                source_object,
                target_object,
                (false, false),
                value.clone(),
                state,
            )?);
            masks.push(leaf.mask);
        }
        self.publish_shared_trait_choice(
            self.tcx.erase_and_anonymize_regions(target_object),
            mapped,
            masks,
            state,
        )
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn validate_shared_trait_graph(
        &self,
        value: &Value,
        state: &State,
    ) -> Result<(), String> {
        if !self.trait_object_choices_issued.get() {
            return Ok(());
        }
        self.shared_trait_graph_node(value, state, 0, &mut Vec::new())
    }

    fn shared_trait_graph_node(
        &self,
        value: &Value,
        state: &State,
        depth: usize,
        visited: &mut Vec<usize>,
    ) -> Result<(), String> {
        if depth > 16 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "shared trait choice backing graph exceeds depth16".into(),
            ));
        }
        self.shared_trait_fee(1)?;
        let mut child = |value| self.shared_trait_graph_node(value, state, depth + 1, visited);
        match value {
            Value::TraitObject { source, id, .. } => {
                self.validate_shared_trait_bundle(source, *id)?;
                child(source)
            }
            Value::Reference { allocation, .. } => {
                self.shared_trait_fee(visited.len())?;
                if !visited.contains(allocation) {
                    visited.push(*allocation);
                    if let Some(Some(value)) = state.memory.get(*allocation) {
                        self.shared_trait_graph_node(value, state, depth + 1, visited)?;
                    }
                }
                Ok(())
            }
            Value::Tuple(values)
            | Value::Enum {
                variants: values, ..
            } => {
                for value in values {
                    child(value)?;
                }
                Ok(())
            }
            Value::Elements(values) => {
                for value in values.iter() {
                    child(value)?;
                }
                Ok(())
            }
            Value::Adt { fields, .. } => {
                for (_, value) in fields {
                    child(value)?;
                }
                Ok(())
            }
            Value::MaybeUninit { payload, .. } => {
                if let Some(value) = payload {
                    child(value)?;
                }
                Ok(())
            }
            Value::TrackedPointer { reference, .. } => child(reference),
            Value::RawSlice { source, .. }
            | Value::SliceIterator { source, .. }
            | Value::MetadataPointer(source)
            | Value::DebugReference { source, .. } => child(source),
            Value::StaticSlice {
                source, elements, ..
            } => {
                child(source)?;
                for value in elements {
                    child(value)?;
                }
                Ok(())
            }
            Value::Input(_)
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::CompositeSlice { .. }
            | Value::ScalarSlice { .. }
            | Value::Bytes { .. }
            | Value::Cell { .. }
            | Value::Atomic { .. }
            | Value::LocalAtomic { .. }
            | Value::MutableU16 { .. }
            | Value::OwnedRegion { .. }
            | Value::OwnedSnapshot(_)
            | Value::RawPointer { .. }
            | Value::StaticView { .. }
            | Value::StaticText
            | Value::FormatArguments
            | Value::FunctionPointer { .. }
            | Value::Function
            | Value::Uninitialized
            | Value::Unit => Ok(()),
        }
    }

    fn shared_trait_type_work(&self, original: Ty<'tcx>, depth: usize) -> Result<(), String> {
        if depth > 16 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "shared trait choice original type exceeds depth16".into(),
            ));
        }
        self.shared_trait_fee(1)?;
        if original.has_non_region_param() || original.has_non_region_infer() {
            return Err("shared trait choice needs fully instantiated original types".into());
        }
        match original.kind() {
            ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) | ty::Slice(pointee) => {
                self.shared_trait_type_work(*pointee, depth + 1)
            }
            ty::Array(element, count) => {
                self.shared_trait_fee(1)?;
                if count.try_to_target_usize(self.tcx).is_none() {
                    return Err("shared trait choice original array count is unavailable".into());
                }
                self.shared_trait_type_work(*element, depth + 1)
            }
            ty::Tuple(fields) => {
                self.shared_trait_fee(fields.len())?;
                for field in fields.iter() {
                    self.shared_trait_type_work(field, depth + 1)?;
                }
                Ok(())
            }
            ty::Adt(_, args) => {
                self.shared_trait_fee(args.len())?;
                for arg in args.iter() {
                    match arg.kind() {
                        ty::GenericArgKind::Type(ty) => {
                            self.shared_trait_type_work(ty, depth + 1)?
                        }
                        ty::GenericArgKind::Lifetime(_) => {}
                        ty::GenericArgKind::Const(_) => {
                            return Err(
                                "shared trait const substitution remains unsupported".into()
                            );
                        }
                    }
                }
                Ok(())
            }
            ty::FnDef(_, original_args) => {
                let args = original_args.skip_binder();
                self.shared_trait_fee(args.len())?;
                for arg in args.iter() {
                    match arg.kind() {
                        ty::GenericArgKind::Type(ty) => {
                            self.shared_trait_type_work(ty, depth + 1)?
                        }
                        ty::GenericArgKind::Lifetime(_) => {}
                        ty::GenericArgKind::Const(_) => {
                            return Err(
                                "shared trait const substitution remains unsupported".into()
                            );
                        }
                    }
                }
                Ok(())
            }
            ty::Dynamic(predicates, _) => {
                self.shared_trait_fee(predicates.len())?;
                for predicate in predicates.iter() {
                    match predicate.skip_binder() {
                        ty::ExistentialPredicate::Trait(trait_ref) => {
                            self.shared_trait_fee(trait_ref.args.len())?;
                            for arg in trait_ref.args.iter() {
                                if let ty::GenericArgKind::Type(ty) = arg.kind() {
                                    self.shared_trait_type_work(ty, depth + 1)?;
                                }
                            }
                        }
                        ty::ExistentialPredicate::Projection(projection) => {
                            self.shared_trait_fee(projection.args.len() + 1)?;
                            for arg in projection.args.iter() {
                                if let ty::GenericArgKind::Type(ty) = arg.kind() {
                                    self.shared_trait_type_work(ty, depth + 1)?;
                                }
                            }
                            if let Some(ty) = projection.term.as_type() {
                                self.shared_trait_type_work(ty, depth + 1)?;
                            }
                        }
                        ty::ExistentialPredicate::AutoTrait(_) => {}
                    }
                }
                Ok(())
            }
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never => Ok(()),
            _ => Err("shared trait choice original type grammar is unsupported".into()),
        }
    }

    fn shared_trait_target_work(&self, instance: ty::Instance<'tcx>) -> Result<(), String> {
        let ty::InstanceKind::Item(id) = instance.def else {
            return Err("shared trait choice target is not an original Item".into());
        };
        self.shared_trait_fee(instance.args.len())?;
        for arg in instance.args.iter() {
            if let ty::GenericArgKind::Type(ty) = arg.kind() {
                self.shared_trait_type_work(ty, 0)?;
            }
        }
        self.shared_trait_raw_signature(id, instance.args)?;
        // Instantiate the raw signature without normalization after charging original arguments.
        let raw = self
            .tcx
            .fn_sig(id)
            .instantiate(self.tcx, instance.args)
            .skip_norm_wip();
        let raw = raw.skip_binder();
        if raw.safety() != rustc_hir::Safety::Safe
            || raw.abi() != rustc_abi::ExternAbi::Rust
            || raw.c_variadic()
        {
            return Err("shared trait choice target needs an original safe Rust signature".into());
        }
        self.shared_trait_fee(raw.inputs().len() + 1)?;
        for ty in raw.inputs() {
            self.shared_trait_type_work(*ty, 0)?;
        }
        self.shared_trait_type_work(raw.output(), 0)
    }

    pub(super) fn shared_trait_object_call(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &State,
        stack: &[DefId],
        site: (DefId, Span),
    ) -> Result<Option<Vec<Return>>, String> {
        let ty::InstanceKind::Virtual(_, _) = instance.def else {
            return Ok(None);
        };
        let Some(Value::TraitObject {
            source,
            id,
            place: false,
        }) = values.first()
        else {
            return Ok(None);
        };
        if !matches!(
            self.trait_objects.borrow().get(*id),
            Some(Witness::SharedChoice(_))
        ) {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        let Some(choice) = self.shared_trait_descriptor(*id)? else {
            return Ok(None);
        };
        self.validate_shared_trait_bundle(source, *id)?;
        self.validate_tracked_value(&values[0], state)?;
        self.shared_trait_type_work(choice.object, 0)?;
        let Value::Elements(candidates) = source.as_ref() else {
            return Err("shared trait choice call lacks its complete source bundle".into());
        };
        self.shared_trait_fee(
            values
                .len()
                .saturating_mul(choice.leaves.len())
                .saturating_add(state.conditions.len()),
        )?;
        let mut prepared = Vec::with_capacity(choice.leaves.len());
        for (candidate, leaf) in candidates.iter().zip(&choice.leaves) {
            let declared = self.preflight_shared_trait_method(instance, candidate)?;
            self.shared_trait_target_work(declared)?;
            for value in values {
                self.validate_tracked_value(value, state)?;
            }
            let mut arguments = values.to_vec();
            arguments[0] = candidate.clone();
            let selected = self.resolve_trait_object_call(instance, &mut arguments, state)?;
            if selected != declared {
                return Err(
                    "shared trait choice resolution changes its full compiler target".into(),
                );
            }
            let signature = self
                .tcx
                .instantiate_bound_regions_with_erased(self.call_poly_signature(selected)?);
            let Some(receiver) = signature.inputs().first() else {
                return Err("shared trait choice target has no original receiver".into());
            };
            if !matches!(receiver.kind(), ty::Ref(_, _, mutability) if !mutability.is_mut()) {
                return Err("shared trait choice target cannot borrow a mutable receiver".into());
            }
            if self.specification(selected)?.is_some() {
                return Err("shared trait choice configured targets remain unsupported".into());
            }
            self.preflight_shared_trait_body(selected)?;
            let body = self.instantiated_body(selected)?;
            if body.source.instance != selected.def
                || body.arg_count != signature.inputs().len()
                || body.return_ty() != signature.output()
                || body
                    .args_iter()
                    .zip(signature.inputs())
                    .any(|(local, ty)| body.local_decls[local].ty != *ty)
            {
                #[cfg(test)]
                {
                    eprintln!(
                        "Shared trait selected Body mismatch: selected={selected:?}; \
                         source={:?}; arg_count={}; signature_args={}; Return={:?}; \
                         signature_Return={:?}",
                        body.source.instance,
                        body.arg_count,
                        signature.inputs().len(),
                        body.return_ty(),
                        signature.output(),
                    );
                    for (local, original) in body.args_iter().zip(signature.inputs()) {
                        eprintln!(
                            "Shared trait selected Body argument: local={local:?}; \
                             actual={:?}; signature={original:?}",
                            body.local_decls[local].ty,
                        );
                    }
                }
                return Err(
                    "shared trait selected body changes original Instance or signature".into(),
                );
            }
            self.shared_trait_fee(
                body.local_decls
                    .len()
                    .saturating_add(body.basic_blocks.len()),
            )?;
            for local in body.local_decls.iter() {
                self.shared_trait_type_work(local.ty, 0)?;
            }
            for block in body.basic_blocks.iter() {
                self.shared_trait_fee(
                    block
                        .statements
                        .len()
                        .saturating_add(block.terminator().successors().count()),
                )?;
            }
            prepared.push((selected, arguments, leaf.mask.clone()));
        }
        let mut returns = Vec::new();
        for (selected, arguments, mask) in prepared {
            self.shared_trait_fee(
                state
                    .conditions
                    .len()
                    .saturating_add(state.memory.storage_slots())
                    .saturating_add(1),
            )?;
            let mut conditions = state.conditions.clone();
            conditions.push(mask);
            if !self.feasible(&conditions)? {
                continue;
            }
            self.shared_trait_fee(state.locals.len().saturating_add(state.addresses.len()))?;
            let mut branch = state.clone();
            self.byte_copy_call_eligibility(selected, true, &mut branch);
            for result in self.call_instance_flow(
                &mut branch.flow,
                selected,
                arguments,
                conditions,
                branch.memory.clone(),
                (stack, site),
            )? {
                self.shared_trait_fee(
                    state
                        .locals
                        .len()
                        .saturating_add(state.addresses.len())
                        .saturating_add(result.conditions.len()),
                )?;
                let returned = self.adopt_flow_return(
                    state,
                    result.conditions.clone(),
                    result.memory.clone(),
                    result.flow.clone(),
                )?;
                self.validate_tracked_value(&result.value, &returned)?;
                self.shared_trait_fee(1)?;
                returns.push(result);
            }
        }
        Ok(Some(returns))
    }
}

impl<'tcx> Engine<'tcx> {
    fn shared_trait_raw_type(
        &self,
        original: Ty<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
        depth: usize,
    ) -> Result<(), String> {
        if depth > 16 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "shared trait raw substitution exceeds depth16".into(),
            ));
        }
        self.shared_trait_fee(1)?;
        match original.kind() {
            ty::Param(parameter) => {
                let Some(argument) = args.get(parameter.index as usize) else {
                    return Err("shared trait raw signature has no original substitution".into());
                };
                let ty::GenericArgKind::Type(ty) = argument.kind() else {
                    return Err("shared trait raw type substitution has a different kind".into());
                };
                self.shared_trait_type_work(ty, depth + 1)
            }
            ty::Ref(_, ty, _) | ty::RawPtr(ty, _) | ty::Slice(ty) => {
                self.shared_trait_raw_type(*ty, args, depth + 1)
            }
            ty::Array(ty, _) => self.shared_trait_raw_type(*ty, args, depth + 1),
            ty::Tuple(types) => {
                self.shared_trait_fee(types.len())?;
                for ty in types.iter() {
                    self.shared_trait_raw_type(ty, args, depth + 1)?;
                }
                Ok(())
            }
            ty::Adt(_, types) => {
                self.shared_trait_fee(types.len())?;
                for ty in types.iter() {
                    if let ty::GenericArgKind::Type(ty) = ty.kind() {
                        self.shared_trait_raw_type(ty, args, depth + 1)?;
                    }
                }
                Ok(())
            }
            ty::FnDef(_, original_types) => {
                let types = original_types.skip_binder();
                self.shared_trait_fee(types.len())?;
                for ty in types.iter() {
                    if let ty::GenericArgKind::Type(ty) = ty.kind() {
                        self.shared_trait_raw_type(ty, args, depth + 1)?;
                    }
                }
                Ok(())
            }
            ty::Alias(_, alias) => {
                self.shared_trait_fee(alias.args.len())?;
                for arg in alias.args.iter() {
                    if let ty::GenericArgKind::Type(ty) = arg.kind() {
                        self.shared_trait_raw_type(ty, args, depth + 1)?;
                    }
                }
                Ok(())
            }
            _ => self.shared_trait_type_work(original, depth + 1),
        }
    }

    fn shared_trait_raw_signature(
        &self,
        id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<(), String> {
        if !matches!(self.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn) {
            return Err("shared trait signature is not an original Fn or AssocFn".into());
        }
        let raw = self.tcx.fn_sig(id).instantiate_identity().skip_norm_wip();
        if raw
            .bound_vars()
            .iter()
            .any(|variable| !matches!(variable, ty::BoundVariableKind::Region(_)))
        {
            return Err("shared trait signature bound types or consts remain unsupported".into());
        }
        let signature = raw.skip_binder();
        self.shared_trait_fee(signature.inputs().len() + 1)?;
        for ty in signature.inputs() {
            self.shared_trait_raw_type(*ty, args, 0)?;
        }
        self.shared_trait_raw_type(signature.output(), args, 0)
    }

    fn preflight_shared_trait_method(
        &self,
        instance: ty::Instance<'tcx>,
        candidate: &Value,
    ) -> Result<ty::Instance<'tcx>, String> {
        let ty::InstanceKind::Virtual(method, slot) = instance.def else {
            return Err("shared trait choice requires the original virtual Method".into());
        };
        self.shared_trait_fee(instance.args.len())?;
        for arg in instance.args.iter() {
            if let ty::GenericArgKind::Type(ty) = arg.kind() {
                self.shared_trait_type_work(ty, 0)?;
            }
        }
        self.shared_trait_raw_signature(method, instance.args)?;
        let Value::TraitObject {
            id, place: false, ..
        } = candidate
        else {
            return Err("shared trait Method requires its exact concrete witness".into());
        };
        let witness = self.concrete_trait_object(*id)?;
        self.shared_trait_type_work(witness.concrete, 0)?;
        let ty::Dynamic(predicates, _) = witness.object.kind() else {
            return Err("shared trait Method witness has no original principal".into());
        };
        let principal = predicates
            .principal()
            .ok_or("shared trait Method has no principal")?;
        let trait_ref = principal
            .no_bound_vars()
            .ok_or("shared trait principal bound variables remain unsupported")?
            .with_self_ty(self.tcx, witness.concrete);
        let entries = self.tcx.vtable_entries(trait_ref);
        self.shared_trait_fee(entries.len())?;
        match entries.get(slot) {
            Some(ty::VtblEntry::Method(target)) => Ok(*target),
            _ => Err("shared trait selected slot is not an actual compiler Method".into()),
        }
    }
}

#[cfg(test)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum SharedReturnFault {
    None,
    MissingBundle,
    SwappedBacking,
}

#[cfg(test)]
thread_local! {
    static SHARED_RETURN_FAULT: std::cell::Cell<SharedReturnFault> = const {
        std::cell::Cell::new(SharedReturnFault::None)
    };
    static SHARED_RETURN_OBSERVATIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
pub(super) fn observed_shared_return(value: &Value) -> Value {
    let fault = SHARED_RETURN_FAULT.with(std::cell::Cell::get);
    let mut observed = value.clone();
    if fault == SharedReturnFault::None {
        return observed;
    }
    let Value::TraitObject { source, .. } = &mut observed else {
        return observed;
    };
    let Value::Elements(children) = source.as_ref() else {
        return observed;
    };
    SHARED_RETURN_OBSERVATIONS.with(|count| count.set(count.get() + 1));
    match fault {
        SharedReturnFault::None => {}
        SharedReturnFault::MissingBundle => **source = Value::Unit,
        SharedReturnFault::SwappedBacking => {
            let mut leaves = children.to_vec();
            if let Some(Value::TraitObject { source, .. }) = leaves.first_mut()
                && let Value::Reference { allocation, .. } = source.as_mut()
            {
                *allocation = allocation.saturating_add(1);
            }
            **source = Value::Elements(leaves.into());
        }
    }
    observed
}

struct SharedBodyWork<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    arguments: ty::GenericArgsRef<'tcx>,
    locals: usize,
    error: Option<String>,
}

impl<'tcx> rustc_middle::mir::visit::Visitor<'tcx> for SharedBodyWork<'_, 'tcx> {
    fn visit_ty(&mut self, original: Ty<'tcx>, _: rustc_middle::mir::visit::TyContext) {
        if self.error.is_none() {
            self.error = self
                .engine
                .shared_trait_raw_type(original, self.arguments, 0)
                .err();
        }
    }

    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        _: rustc_middle::mir::visit::PlaceContext,
        _: rustc_middle::mir::Location,
    ) {
        if self.error.is_some() {
            return;
        }
        if place.local.as_usize() >= self.locals || place.projection.len() > 16 {
            self.error = Some("shared trait body place has a different local or depth".into());
            return;
        }
        self.error = self
            .engine
            .shared_trait_fee(1 + place.projection.len())
            .err();
        for projection in place.projection {
            if self.error.is_some() {
                break;
            }
            match projection {
                PlaceElem::Field(_, original) | PlaceElem::OpaqueCast(original) => {
                    self.error = self
                        .engine
                        .shared_trait_raw_type(original, self.arguments, 0)
                        .err();
                }
                PlaceElem::UnwrapUnsafeBinder(_) => {
                    self.error = Some("shared trait body unsafe binder remains unsupported".into());
                }
                PlaceElem::Deref
                | PlaceElem::Index(_)
                | PlaceElem::ConstantIndex { .. }
                | PlaceElem::Subslice { .. }
                | PlaceElem::Downcast(_, _)
                | PlaceElem::PhantomDeref => {}
            }
        }
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: rustc_middle::mir::Location) {
        if self.error.is_none() {
            self.error = self.engine.shared_trait_fee(1).err();
        }
        if self.error.is_none() {
            self.super_operand(operand, location);
        }
    }

    fn visit_const_operand(
        &mut self,
        constant: &rustc_middle::mir::ConstOperand<'tcx>,
        _: rustc_middle::mir::Location,
    ) {
        if self.error.is_some() {
            return;
        }
        match constant.const_ {
            rustc_middle::mir::Const::Val(
                rustc_middle::mir::ConstValue::Scalar(_) | rustc_middle::mir::ConstValue::ZeroSized,
                original,
            ) => {
                self.error = self
                    .engine
                    .shared_trait_raw_type(original, self.arguments, 0)
                    .err();
            }
            _ => self.error = Some("shared trait body constant grammar remains unsupported".into()),
        }
    }

    fn visit_ty_const(&mut self, _: ty::Const<'tcx>, _: rustc_middle::mir::Location) {
        if self.error.is_none() {
            self.error = Some("shared trait body type constants remain unsupported".into());
        }
    }

    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: rustc_middle::mir::Location) {
        if self.error.is_none() {
            self.error = self.engine.shared_trait_fee(1).err();
        }
        if self.error.is_none() {
            self.super_rvalue(value, location);
        }
    }

    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        if self.error.is_none() {
            self.error = self
                .engine
                .shared_trait_fee(1_usize.saturating_add(terminator.successors().count()))
                .err();
        }
        if self.error.is_none() {
            self.super_terminator(terminator, location);
        }
    }
}

impl<'tcx> Engine<'tcx> {
    fn preflight_shared_trait_body(&self, selected: ty::Instance<'tcx>) -> Result<(), String> {
        if !matches!(selected.def, ty::InstanceKind::Item(_)) {
            return Err("shared trait selected body is not an original Item".into());
        }
        if !self.tcx.is_mir_available(selected.def_id()) {
            return Err(self.missing_body_reason(selected.def_id()));
        }
        let raw = self.tcx.instance_mir(selected.def);
        self.shared_trait_fee(raw.local_decls.len().saturating_add(raw.basic_blocks.len()))?;
        let mut work = SharedBodyWork {
            engine: self,
            arguments: selected.args,
            locals: raw.local_decls.len(),
            error: None,
        };
        rustc_middle::mir::visit::Visitor::visit_body(&mut work, raw);
        if let Some(error) = work.error {
            return Err(error);
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "trait_object_choice_probe.rs"]
mod tests;
