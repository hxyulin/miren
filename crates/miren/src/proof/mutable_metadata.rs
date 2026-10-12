//! Exact metadata-to-Boolean relation for issued original scalar slice roles.
use super::*;
use crate::symbolic::MutableU16Role;

const IS_EMPTY_ENABLED: bool = true;

fn enabled() -> bool {
    #[cfg(test)]
    if TEST_ENABLED.with(std::cell::Cell::get) {
        return true;
    }
    IS_EMPTY_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_ENABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestEnabled(bool);

#[cfg(test)]
impl TestEnabled {
    fn enable() -> Self {
        Self(TEST_ENABLED.with(|value| value.replace(true)))
    }
}

#[cfg(test)]
impl Drop for TestEnabled {
    fn drop(&mut self) {
        TEST_ENABLED.with(|value| value.set(self.0));
    }
}

// Metadata-only is_empty accepts additional existing scalar domains.
const SCALAR_IS_EMPTY_ENABLED: bool = true;

fn scalar_enabled() -> bool {
    #[cfg(test)]
    if TEST_SCALAR_ENABLED.with(std::cell::Cell::get) {
        return true;
    }
    SCALAR_IS_EMPTY_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_SCALAR_ENABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestScalarEnabled(bool);

#[cfg(test)]
impl TestScalarEnabled {
    fn enable() -> Self {
        Self(TEST_SCALAR_ENABLED.with(|value| value.replace(true)))
    }
}

#[cfg(test)]
impl Drop for TestScalarEnabled {
    fn drop(&mut self) {
        TEST_SCALAR_ENABLED.with(|value| value.set(self.0));
    }
}

impl<'tcx> Engine<'tcx> {
    fn issued_metadata_element(&self, original: Ty<'tcx>) -> bool {
        self.mutable_product_kind(original)
            || original == self.tcx.types.u16
            || (scalar_enabled()
                && original != self.tcx.types.u8
                && matches!(
                    original.kind(),
                    ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_)
                ))
            || (scalar_enabled()
                && super::float_pairs::ENABLE_MUTABLE_FLOAT
                && matches!(
                    original.kind(),
                    ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64)
                ))
    }

    fn issued_is_empty_candidate(&self, instance: ty::Instance<'tcx>) -> bool {
        if !enabled()
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || self.tcx.def_kind(instance.def_id()) != DefKind::AssocFn
        {
            return false;
        }
        let Some(len) = self.tcx.lang_items().get(LangItem::SliceLen) else {
            return false;
        };
        if instance.def_id().krate != len.krate
            || self.tcx.parent(instance.def_id()) != self.tcx.parent(len)
            || self.tcx.item_name(instance.def_id()).as_str() != "is_empty"
        {
            return false;
        }
        let signature = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate(self.tcx, instance.args)
            .skip_binder();
        signature.safety() == rustc_hir::Safety::Safe
            && signature.abi() == rustc_abi::ExternAbi::Rust
            && !signature.c_variadic()
            && signature.output() == self.tcx.types.bool
            && matches!(signature.inputs(), [original]
                if matches!(original.kind(), ty::Ref(_, inner, rustc_hir::Mutability::Not)
                    if matches!(inner.kind(), ty::Slice(element)
                        if self.issued_metadata_element(*element))))
    }

    pub(super) fn issued_float_is_empty_candidate(&self, instance: ty::Instance<'tcx>) -> bool {
        if !self.issued_is_empty_candidate(instance) {
            return false;
        }
        let signature = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate(self.tcx, instance.args)
            .skip_binder();
        matches!(signature.inputs(), [receiver]
            if matches!(receiver.kind(), ty::Ref(_, inner, rustc_hir::Mutability::Not)
                if matches!(inner.kind(), ty::Slice(element)
                    if matches!(element.kind(), ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64)))))
    }

    // This routes metadata only. The complete body/type certificate still precedes the result.
    pub(super) fn mutable_metadata_operation(&self, instance: ty::Instance<'tcx>) -> bool {
        self.tcx.lang_items().get(LangItem::SliceLen) == Some(instance.def_id())
            || self.issued_is_empty_candidate(instance)
    }

    fn certify_issued_is_empty(&mut self, instance: ty::Instance<'tcx>) -> Result<(), String> {
        if !self.issued_is_empty_candidate(instance) {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty needs its actual core slice definition".into(),
            ));
        }
        if !self.tcx.is_mir_available(instance.def_id()) {
            return Err(self.missing_body_reason(instance.def_id()));
        }
        let signature = self.call_signature(instance)?;
        let [selected_receiver] = signature.inputs() else {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty original receiver or Boolean signature differs".into(),
            ));
        };
        let selected_element = match selected_receiver.kind() {
            ty::Ref(_, inner, rustc_hir::Mutability::Not) => match inner.kind() {
                ty::Slice(element) => *element,
                _ => return Err("issued is_empty original receiver is not a slice".into()),
            },
            _ => return Err("issued is_empty original receiver is not shared".into()),
        };
        let receiver = |original: Ty<'tcx>| {
            matches!(original.kind(), ty::Ref(_, inner, rustc_hir::Mutability::Not)
                if matches!(inner.kind(), ty::Slice(element)
                    if *element == selected_element && self.issued_metadata_element(*element)))
        };
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.output() != self.tcx.types.bool
            || signature.inputs().len() != 1
            || !receiver(signature.inputs()[0])
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty original receiver or Boolean signature differs".into(),
            ));
        }
        // Fixed schema bounds precede cache instantiation/cloning and all constant evaluation.
        let generic = self.tcx.instance_mir(instance.def);
        if generic.local_decls.len() != 3
            || generic.basic_blocks.len() != 1
            || generic.basic_blocks[START_BLOCK].statements.len() != 4
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty body is outside the exact bounded schema".into(),
            ));
        }
        let body = self.instantiated_body(instance)?;
        if body.source.instance != instance.def
            || body.source.promoted.is_some()
            || body.coroutine.is_some()
            || body.spread_arg.is_some()
            || body.tainted_by_errors.is_some()
            || body.arg_count != 1
            || body.local_decls.len() != 3
            || body.basic_blocks.len() != 1
            || body.local_decls[rustc_middle::mir::RETURN_PLACE].ty != self.tcx.types.bool
            || !receiver(body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty)
            || body.local_decls[rustc_middle::mir::Local::from_usize(2)].ty != self.tcx.types.usize
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty body provenance or original schema differs".into(),
            ));
        }
        let block = &body.basic_blocks[START_BLOCK];
        if block.is_cleanup || !matches!(block.terminator().kind, TerminatorKind::Return) {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty has unsupported control flow".into(),
            ));
        }
        let [live, metadata, equality, dead] = block.statements.as_slice() else {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty has extra or missing effects".into(),
            ));
        };
        let temporary = rustc_middle::mir::Local::from_usize(2);
        if !matches!(live.kind, StatementKind::StorageLive(local) if local == temporary)
            || !matches!(dead.kind, StatementKind::StorageDead(local) if local == temporary)
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty temporary lifetime differs".into(),
            ));
        }
        let StatementKind::Assign(assignment) = &metadata.kind else {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty lacks its metadata assignment".into(),
            ));
        };
        if assignment.0 != Place::from(temporary)
            || !matches!(&assignment.1, Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(source))
                if *source == Place::from(rustc_middle::mir::Local::from_usize(1)))
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty metadata source differs".into(),
            ));
        }
        let StatementKind::Assign(assignment) = &equality.kind else {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty lacks its equality assignment".into(),
            ));
        };
        let Rvalue::BinaryOp(BinOp::Eq, operands) = &assignment.1 else {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty does not compare exact metadata to zero".into(),
            ));
        };
        let (Operand::Move(source), Operand::Constant(constant)) = operands.as_ref() else {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty equality operands differ".into(),
            ));
        };
        if assignment.0 != Place::from(rustc_middle::mir::RETURN_PLACE)
            || *source != Place::from(temporary)
            || constant.const_.ty() != self.tcx.types.usize
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty equality original types differ".into(),
            ));
        }
        let value = self.constant(body.source.def_id(), constant.const_, constant.span)?;
        let (term, bits, signed) = value.integer()?;
        if signed
            || bits != u32::from(self.tcx.sess.target.pointer_width)
            || symbolic::constant(&term) != Some(symbolic::Constant::BitVec { value: 0, bits })
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty zero constant differs".into(),
            ));
        }
        Ok(())
    }

    pub(super) fn mutable_slice_is_empty(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &State,
    ) -> Result<Option<Value>, String> {
        if !self.issued_is_empty_candidate(instance) {
            return Ok(None);
        }
        // Float metadata adds no armed transport or payload authority. Refuse before
        // body/cache certification and before constructing any Boolean term.
        if self.issued_float_is_empty_candidate(instance) {
            state.flow.require_unarmed()?;
        }
        let [receiver @ Value::MutableU16 { id, role }] = values else {
            return Ok(None);
        };
        let product_element = self.mutable_product_owner(*id, &state.memory)?;
        if product_element {
            state.flow.require_unarmed()?;
        }
        if !matches!(
            role,
            MutableU16Role::Metadata { .. }
                | MutableU16Role::ChildMetadata { .. }
                | MutableU16Role::HierarchyMetadata { .. }
        ) {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty requires a current metadata-only role".into(),
            ));
        }
        self.certify_issued_is_empty(instance)?;
        let signature = self.call_signature(instance)?;
        if !self.mutable_u16_matches(signature.inputs()[0], *id, &state.memory, false)? {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty original element differs from backing".into(),
            ));
        }
        let length = self.mutable_owner_length(receiver, state)?;
        let (_, bits, signed) = length.integer()?;
        if signed || bits != u32::from(self.tcx.sess.target.pointer_width) {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued is_empty current length has a different target type".into(),
            ));
        }
        let zero = symbolic::integer(&self.terms, 0, bits, false);
        let result = symbolic::binary(&self.terms, "eq", length, zero)?;
        self.record_model(
            instance.def_id(),
            if product_element {
                "issued product metadata-only is_empty; actual body certified"
            } else if matches!(signature.inputs()[0].kind(), ty::Ref(_, inner, _)
                if matches!(inner.kind(), ty::Slice(element) if *element == self.tcx.types.u16))
            {
                "issued u16 metadata-only is_empty; actual body certified"
            } else {
                "issued scalar metadata-only is_empty; actual body certified"
            },
        );
        Ok(Some(result))
    }
}

#[cfg(test)]
#[path = "mutable_metadata_probe.rs"]
mod tests;
