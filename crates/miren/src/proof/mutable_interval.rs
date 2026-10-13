//! Checked u16 interval issuer. Existing whole-slice behavior has descriptorNone.
use super::mutable_u16_children::{ChildCall, Phase};
use super::*;
use symbolic::MutableU16Role;
#[cfg(test)]
#[path = "mutable_interval_probe.rs"]
mod probe;
#[path = "mutable_interval_templates.rs"]
mod templates;

const ISSUANCE_ENABLED: bool = true;
// Original i32/usize require their complete selected compiler interval certificate.
const INTEGER_ISSUANCE_ENABLED: bool = true;

#[derive(Clone, Debug)]
struct Issue {
    backing: usize,
    certificate: usize,
    allocation: usize,
    generation: u64,
    call_tip: usize,
    start: Value,
    end: Value,
    capacity: Value,
}

#[derive(Clone, Debug)]
pub(super) struct Descriptor {
    issue: std::rc::Rc<Issue>,
    offset: Value,
    length: Value,
}

impl Descriptor {
    pub(super) fn length(&self) -> &Value {
        &self.length
    }
    pub(super) fn storage_slots(&self) -> usize {
        7
    }
}

fn same_integer(a: &Value, b: &Value) -> bool {
    matches!((a.integer(), b.integer()), (Ok((a, ab, asigned)), Ok((b, bb, bsigned)))
        if a == b && ab == bb && asigned == bsigned)
}

impl<'tcx> Engine<'tcx> {
    fn interval_error(&self, detail: &str) -> String {
        self.categorized_error(UnknownCategory::Semantics, detail.into())
    }

    fn interval_element_eligible(&self, certificate: usize) -> Result<bool, String> {
        let original = self.mutable_interval_element(certificate)?;
        Ok(original == self.tcx.types.u16
            || (INTEGER_ISSUANCE_ENABLED
                && templates::integer_element(self.tcx, original).is_some()))
    }

    pub(super) fn validate_mutable_interval(
        &self,
        id: usize,
        backing: &super::mutable_u16::Backing,
    ) -> Result<(), String> {
        let Some(view) = &backing.interval else {
            return Ok(());
        };
        if backing.phase == Phase::Idle
            || id != view.issue.backing
            || backing.certificate != view.issue.certificate
            || backing.allocation != view.issue.allocation
            || backing.generation != view.issue.generation
            || !same_integer(&backing.length, &view.issue.capacity)
            || !self.interval_element_eligible(backing.certificate)?
        {
            return Err(self.interval_error("mutable interval issued identity/phase differs"));
        }
        self.mutable_u16_call_tip_identity(view.issue.call_tip)?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for bound in [
            &view.offset,
            &view.length,
            &view.issue.start,
            &view.issue.end,
        ] {
            let (term, width, signed) = bound.integer()?;
            if width != bits
                || signed
                || term.sort() != &Sort::BitVec(bits)
                || !term.belongs_to(&self.terms)
            {
                return Err(self.interval_error("mutable interval bounds have wrong context/type"));
            }
        }
        let length = symbolic::binary(
            &self.terms,
            "sub",
            view.issue.end.clone(),
            view.issue.start.clone(),
        )?;
        if !same_integer(&view.offset, &view.issue.start) || !same_integer(&view.length, &length) {
            return Err(self.interval_error("mutable interval differs from issued endpoints"));
        }
        Ok(())
    }

    pub(super) fn mutable_interval_index(
        &self,
        id: usize,
        backing: &super::mutable_u16::Backing,
        index: Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        if matches!(backing.phase, Phase::Retained { .. }) {
            return self.mutable_retained_index(id, backing, index, conditions);
        }
        let Some(view) = &backing.interval else {
            self.mutable_u16_index(&index, &backing.length, conditions)?;
            return Ok(index);
        };
        self.validate_mutable_interval(id, backing)?;
        if !matches!(backing.phase, Phase::Active { .. }) {
            return Err(self.interval_error("mutable interval data requires active owner frame"));
        }
        let inside = symbolic::binary(
            &self.terms,
            "le",
            view.offset.clone(),
            backing.length.clone(),
        )?
        .boolean()?;
        let available = symbolic::binary(
            &self.terms,
            "sub",
            backing.length.clone(),
            view.offset.clone(),
        )?;
        let fits =
            symbolic::binary(&self.terms, "le", view.length.clone(), available)?.boolean()?;
        let safe = self.terms.apply(Op::And, &[inside, fits])?;
        let mut denied = conditions.to_vec();
        denied.push(symbolic::not(&safe));
        if self.feasible(&denied)? {
            return Err(
                self.interval_error("mutable interval current root extent is not established")
            );
        }
        self.mutable_u16_index(&index, &view.length, conditions)?;
        let absolute = symbolic::binary(&self.terms, "add", view.offset.clone(), index)?;
        self.mutable_u16_index(&absolute, &backing.length, conditions)?;
        Ok(absolute)
    }

    pub(super) fn mutable_interval_call(
        &mut self,
        state: &State,
        call: ChildCall<'_, 'tcx>,
    ) -> Result<Option<(rustc_middle::mir::BasicBlock, State)>, String> {
        if !ISSUANCE_ENABLED {
            return Ok(None);
        }
        self.mutable_interval_issuer(state, call)
    }

    fn mutable_interval_issuer(
        &mut self,
        state: &State,
        call: ChildCall<'_, 'tcx>,
    ) -> Result<Option<(rustc_middle::mir::BasicBlock, State)>, String> {
        let ChildCall {
            body,
            block,
            instance,
            args,
            destination,
            target,
            site,
            ..
        } = call;
        let integer = INTEGER_ISSUANCE_ENABLED
            .then(|| templates::integer_wrapper_element(self.tcx, instance))
            .flatten();
        if state.memory.mutable_u16.is_empty()
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || self.tcx.def_kind(instance.def_id()) != DefKind::AssocFn
            || pure_comparison_templates::definition_key(instance.def_id())
                != "DefId(core::slice::index::{impl#1}::index_mut)"
            || (!templates::u16_wrapper_signature(self.tcx, instance) && integer.is_none())
        {
            return Ok(None);
        }
        let terminator = body
            .basic_blocks
            .get(block)
            .ok_or("mutable interval Call block differs")?
            .terminator();
        let TerminatorKind::Call {
            func,
            args: actual_args,
            destination: actual_destination,
            target: actual_target,
            ..
        } = &terminator.kind
        else {
            return Err(self.interval_error("mutable interval needs actual Call"));
        };
        let ty::FnDef(definition, generic) = func.ty(&body.local_decls, self.tcx).kind() else {
            return Err(self.interval_error("mutable interval Call is indirect"));
        };
        let selected = ty::Instance::try_resolve(
            self.tcx,
            ty::TypingEnv::fully_monomorphized(),
            *definition,
            generic.skip_binder(),
        )
        .map_err(|_| "mutable interval Call resolution failed")?
        .ok_or("mutable interval Call instance missing")?;
        if selected != instance
            || !matches!(func, Operand::Constant(_))
            || !std::ptr::eq(actual_args.as_ref(), args)
            || *actual_destination != destination
            || *actual_target != target
        {
            return Err(
                self.interval_error("mutable interval supplied Call/source occurrence differs")
            );
        }
        if args.len() != 2
            || target.is_none()
            || !destination.projection.is_empty()
            || destination.local.as_usize() <= body.arg_count
            || state.addresses[destination.local.as_usize()].is_some()
        {
            return Err(self.interval_error("mutable interval needs private normal CallResult"));
        }
        let (Operand::Copy(source) | Operand::Move(source)) = args[0].node else {
            return Err(self.interval_error("mutable interval source lacks current private tip"));
        };
        if !source.projection.is_empty() || source.local == destination.local {
            return Err(
                self.interval_error("mutable interval source overlaps result or has projection")
            );
        }
        let Value::MutableU16 {
            id,
            role: MutableU16Role::Child { generation },
        } = self.raw_local(state, source.local.as_usize())?
        else {
            return Err(self.interval_error("mutable interval needs staged parent"));
        };
        self.mutable_u16_staging_tip(body, state, source.local.as_usize(), id, generation)?;
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        if backing.interval.is_some()
            || !self.interval_element_eligible(backing.certificate)?
            || !self.mutable_u16_matches(
                body.local_decls[source.local].ty,
                id,
                &state.memory,
                true,
            )?
            || !self.mutable_u16_matches(
                body.local_decls[destination.local].ty,
                id,
                &state.memory,
                true,
            )?
        {
            return Err(self.interval_error("mutable interval original root/type is unsupported"));
        }
        if let Some(element) = integer {
            if self.mutable_interval_element(backing.certificate)? != element.original {
                return Err(self.interval_error("mutable interval original integer differs"));
            }
            templates::certify_integer_guarded_family(self.tcx, instance, element)
                .map_err(|error| self.categorized_error(error.category, error.reason))?;
            if let Operand::Copy(place) | Operand::Move(place) = args[1].node {
                self.owned_field_footprint(body, place)?;
            }
        } else {
            templates::certify_u16_guarded_family(self.tcx, instance)?;
        }
        let certificate = backing.certificate;
        let allocation = backing.allocation;
        let capacity = backing.length.clone();
        if state.memory.storage_slots().saturating_add(7) > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable interval exceeds existing512 storage".into(),
            ));
        }
        let mut next = state.clone();
        if matches!(args[0].node, Operand::Move(_)) {
            next.missing_places
                .consume(source.local.as_usize(), Vec::new())?;
        }
        let range = self
            .evaluate_operand(site.0, body, &mut next, &args[1].node)?
            .materialize()?;
        let range_ty = args[1].node.ty(&body.local_decls, self.tcx);
        let ty::Adt(def, generic) = range_ty.kind() else {
            return Err(self.interval_error("mutable interval lacks original Range type"));
        };
        if self.tcx.lang_items().get(LangItem::Range) != Some(def.did())
            || generic.type_at(0) != self.tcx.types.usize
            || !matches!(&range, Value::Adt { name, variant: 0, fields, .. }
                if *name == self.tcx.def_path_str(def.did()) && fields.len() == 2)
        {
            return Err(self.interval_error("mutable interval Range identity/schema differs"));
        }
        let start = range.field("start")?;
        let end = range.field("end")?;
        for bound in [&start, &end] {
            let (term, width, signed) = bound.integer()?;
            if width != u32::from(self.tcx.sess.target.pointer_width)
                || signed
                || !term.belongs_to(&self.terms)
            {
                return Err(
                    self.interval_error("mutable interval endpoints are not original usize")
                );
            }
        }
        let ordered = symbolic::binary(&self.terms, "le", start.clone(), end.clone())?.boolean()?;
        let inside =
            symbolic::binary(&self.terms, "le", end.clone(), capacity.clone())?.boolean()?;
        let safe = self.terms.apply(Op::And, &[ordered, inside])?;
        self.require(
            site.0,
            site.1,
            &next.conditions,
            &safe,
            ObligationKind::PanicSafety,
            "mutable interval requires start <= end <= original length".into(),
        )?;
        next.conditions.push(safe);
        let call_tip = self.mutable_u16_register_call_tip(body, block, destination, &next)?;
        let length = symbolic::binary(&self.terms, "sub", end.clone(), start.clone())?;
        let view = Descriptor {
            issue: std::rc::Rc::new(Issue {
                backing: id,
                certificate,
                allocation,
                generation,
                call_tip,
                start: start.clone(),
                end,
                capacity,
            }),
            offset: start,
            length,
        };
        let current = &mut std::rc::Rc::make_mut(&mut next.memory.mutable_u16)[id];
        current.interval = Some(view);
        current.phase = Phase::Pending {
            certificate: call_tip,
        };
        self.write(
            &mut next,
            destination,
            Value::MutableU16 {
                id,
                role: MutableU16Role::Child { generation },
            },
        )?;
        self.validate_mutable_interval(id, &next.memory.mutable_u16[id])?;
        self.record_model(
            instance.def_id(),
            if integer.is_some() {
                "certified checked integer interval; one pending grant, \
                same current backing, no raw pointer or ordinary returned-reference permission"
            } else {
                "certified checked u16 interval; one pending grant, \
                same current backing, no raw pointer or ordinary returned-reference permission"
            },
        );
        Ok(Some((target.unwrap(), next)))
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn certify_retained_range_family(
        &self,
        instance: ty::Instance<'tcx>,
        original: Ty<'tcx>,
    ) -> Result<bool, String> {
        if original == self.tcx.types.u16 {
            templates::certify_u16_guarded_family(self.tcx, instance)?;
        } else if original == Ty::new_array(self.tcx, self.tcx.types.f32, 2) {
            templates::certify_f32_pair_guarded_family(self.tcx, instance)
                .map_err(|e| self.categorized_error(e.category, e.reason))?;
        } else {
            return Ok(false);
        }
        Ok(true)
    }
}
