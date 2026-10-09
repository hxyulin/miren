use super::*;
use rustc_middle::ty::adjustment::PointerCoercion;

/// Compiler types retained at a concrete reference unsizing site. This is not a vtable address
/// and is never constructed for an arbitrary trait-object input.
#[derive(Clone, Copy, PartialEq)]
pub(super) struct TraitObject<'tcx> {
    concrete: Ty<'tcx>,
    object: Ty<'tcx>,
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
            let witness = self
                .trait_objects
                .get(id)
                .ok_or("trait-object identity unsizing witness is missing")?;
            if witness.object != self.tcx.erase_and_anonymize_regions(*object) {
                return Err("trait-object identity unsizing changes the witnessed type".into());
            }
            return self
                .borrow_trait_object(&source, id, target_mutability.is_mut(), state)
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
        let id = if let Some(id) = self.trait_objects.iter().position(|item| *item == entry) {
            id
        } else {
            if self.trait_objects.len() >= 512 {
                return Err("concrete trait-object registry exceeds 512 witnesses".into());
            }
            let id = self.trait_objects.len();
            self.trait_objects.push(entry);
            id
        };
        Ok(Some(Value::TraitObject {
            source: Box::new(value),
            id,
            place: false,
        }))
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
        self.trait_objects
            .get(id)
            .ok_or("trait-object reborrow witness is missing")?;
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
        let witness = self
            .trait_objects
            .get(*id)
            .ok_or("virtual-call coercion witness is missing")?;
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
