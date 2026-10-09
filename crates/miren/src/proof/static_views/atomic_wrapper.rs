//! An exact, body-checked portable AtomicBool shared view of its core-backed byte atomic.
use super::*;
use rustc_abi::{BackendRepr, FieldIdx, Primitive, Scalar};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Address {
    SharedSource,
    RawSource,
    RawTarget,
    SharedTarget,
}

impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn static_atomic_wrapper_call(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &State,
    ) -> Result<Option<Value>, String> {
        let id = instance.def_id();
        if self.tcx.def_kind(id) != DefKind::AssocFn
            || self.tcx.item_name(id).as_str() != "as_atomic_u8"
            || id.is_local()
            || self.tcx.crate_name(id.krate).as_str() != "portable_atomic"
        {
            return Ok(None);
        }
        let [value @ Value::StaticView { .. }] = values else {
            return Ok(None);
        };
        let signature = self.call_signature(instance)?;
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.c_variadic()
            || signature.abi() != rustc_abi::ExternAbi::Rust
        {
            return Err("atomic byte wrapper requires its safe Rust method signature".into());
        }
        let ([input], ty::Ref(_, target, target_mutability)) =
            (signature.inputs(), signature.output().kind())
        else {
            return Err("atomic byte wrapper signature mismatch".into());
        };
        let ty::Ref(_, source, source_mutability) = input.kind() else {
            return Err("atomic byte wrapper needs a shared receiver".into());
        };
        if source_mutability.is_mut() || target_mutability.is_mut() {
            return Err("atomic byte wrapper cannot grant mutable reference rights".into());
        }
        self.certify_atomic_byte_wrapper(instance, *source, *target)?;
        let body = self.instantiated_body(instance)?;
        certify_body(&body, *source, *target)?;
        let mut view = self.static_view(value, state)?;
        self.require_static_initialization(view, state)?;
        if view.kind != (ViewKind::Reference { mutable: false })
            || view.ty != *source
            || view.certified != *source
            || self.uninit_static_address(view)?
        {
            return Err(
                "atomic byte wrapper needs its live initialized original typed view".into(),
            );
        }
        // The certified method returns this same address; it neither reads nor writes the byte.
        // Keep the original allocation, offset, epoch and all pre-existing access capability.
        view.ty = *target;
        view.certified = *target;
        let result = self.intern_static_view(view)?;
        self.record_model(
            id,
            concat!(
                "body-certified portable AtomicBool shared byte-atomic view; ",
                "no value or initialization"
            ),
        );
        Ok(Some(result))
    }

    fn certify_atomic_byte_wrapper(
        &self,
        instance: ty::Instance<'tcx>,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
    ) -> Result<(), String> {
        let (ty::Adt(source_def, source_args), ty::Adt(target_def, target_args)) =
            (source.kind(), target.kind())
        else {
            return Err("atomic byte wrapper needs concrete compiler struct types".into());
        };
        let Some(implementation) = self.tcx.impl_of_assoc(instance.def_id()) else {
            return Err("atomic byte wrapper method has no compiler implementation".into());
        };
        if !matches!(
            self.tcx.def_kind(implementation),
            DefKind::Impl { of_trait: false }
        ) || !source_args.is_empty()
            || !target_args.is_empty()
            || !source_def.is_struct()
            || !target_def.is_struct()
            || source_def.did().krate != instance.def_id().krate
            || target_def.did().krate != instance.def_id().krate
            || self.tcx.def_path_str(source_def.did()) != "portable_atomic::AtomicBool"
            || self.tcx.def_path_str(target_def.did())
                != "portable_atomic::imp::core_atomic::AtomicU8"
            || self
                .tcx
                .type_of(implementation)
                .instantiate_identity()
                .skip_norm_wip()
                != source
            || !source_def.repr().c()
            || !target_def.repr().transparent()
            || source_def.non_enum_variant().fields.len() != 1
            || target_def.non_enum_variant().fields.len() != 2
        {
            return Err("atomic byte wrapper compiler identity mismatch".into());
        }
        let source_field = source_def.non_enum_variant().fields[FieldIdx::from_usize(0)]
            .ty(self.tcx, source_args)
            .skip_norm_wip();
        let ty::Adt(cell, cell_args) = source_field.kind() else {
            return Err("atomic byte wrapper source is not core UnsafeCell<u8>".into());
        };
        if self.tcx.lang_items().get(LangItem::UnsafeCell) != Some(cell.did())
            || cell_args.type_at(0) != self.tcx.types.u8
        {
            return Err("atomic byte wrapper source is not core UnsafeCell<u8>".into());
        }
        let target_fields = &target_def.non_enum_variant().fields;
        let atomic = target_fields[FieldIdx::from_usize(0)]
            .ty(self.tcx, target_args)
            .skip_norm_wip();
        let marker = target_fields[FieldIdx::from_usize(1)]
            .ty(self.tcx, target_args)
            .skip_norm_wip();
        let (ty::Adt(atomic_def, atomic_args), ty::Adt(marker_def, _)) =
            (atomic.kind(), marker.kind())
        else {
            return Err("atomic byte wrapper target field identity mismatch".into());
        };
        if self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("Atomic"))
            != Some(atomic_def.did())
            || atomic_args.type_at(0) != self.tcx.types.u8
            || self.tcx.lang_items().get(LangItem::PhantomData) != Some(marker_def.did())
            || self.static_layout(marker)?.size.bytes() != 0
        {
            return Err("atomic byte wrapper target is not core Atomic<u8> and PhantomData".into());
        }
        for ty in [source, source_field, target, atomic, self.tcx.types.u8] {
            let layout = self.static_layout(ty)?;
            if layout.size.bytes() != 1
                || layout.align.abi.bytes() != 1
                || ty.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
                || !(matches!(layout.backend_repr, BackendRepr::Memory { sized: true })
                    || matches!(layout.backend_repr, BackendRepr::Scalar(Scalar::Initialized {
                        value: Primitive::Int(rustc_abi::Integer::I8, false), valid_range,
                    }) if valid_range.start == 0 && valid_range.end == 255))
            {
                return Err("atomic byte wrapper needs exact non-Drop one-byte storage".into());
            }
        }
        if !matches!(self.static_layout(self.tcx.types.u8)?.backend_repr,
            BackendRepr::Scalar(Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I8, false), valid_range,
            }) if valid_range.start == 0 && valid_range.end == 255)
        {
            return Err("atomic byte wrapper requires its complete initialized u8 leaf".into());
        }
        if !atomic_def.is_struct() || atomic_def.non_enum_variant().fields.len() != 1 {
            return Err("atomic byte wrapper core atomic field shape mismatch".into());
        }
        let core_cell = self
            .tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                atomic_def.non_enum_variant().fields[FieldIdx::from_usize(0)]
                    .ty(self.tcx, atomic_args),
            )
            .map_err(|error| format!("atomic byte storage normalization failed: {error:?}"))?;
        let ty::Adt(core_cell_def, core_cell_args) = core_cell.kind() else {
            return Err("atomic byte wrapper core storage must be UnsafeCell".into());
        };
        let aligned = core_cell_args.type_at(0);
        let ty::Adt(aligned_def, aligned_args) = aligned.kind() else {
            return Err("atomic byte wrapper core storage must have its alignment wrapper".into());
        };
        if self.tcx.lang_items().get(LangItem::UnsafeCell) != Some(core_cell_def.did())
            || !aligned_def.is_struct()
            || aligned_def.did().krate != atomic_def.did().krate
            || aligned_def.non_enum_variant().fields.len() != 1
            || aligned_def.non_enum_variant().fields[FieldIdx::from_usize(0)]
                .ty(self.tcx, aligned_args)
                .skip_norm_wip()
                != self.tcx.types.u8
        {
            return Err("atomic byte wrapper core storage does not end in exact u8".into());
        }
        for ty in [core_cell, aligned] {
            let layout = self.static_layout(ty)?;
            if layout.size.bytes() != 1
                || layout.align.abi.bytes() != 1
                || layout.fields.offset(0).bytes() != 0
                || ty.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
                || !(matches!(layout.backend_repr, BackendRepr::Memory { sized: true })
                    || matches!(layout.backend_repr, BackendRepr::Scalar(Scalar::Initialized {
                        value: Primitive::Int(rustc_abi::Integer::I8, false), valid_range,
                    }) if valid_range.start == 0 && valid_range.end == 255))
            {
                return Err("atomic byte wrapper core storage has incompatible layout".into());
            }
        }
        for ty in [source, source_field, target, atomic] {
            if self.static_layout(ty)?.fields.offset(0).bytes() != 0 {
                return Err("atomic byte wrapper fields must start at the retained address".into());
            }
        }
        Ok(())
    }
}

fn certify_body<'tcx>(body: &Body<'tcx>, source: Ty<'tcx>, target: Ty<'tcx>) -> Result<(), String> {
    if body.arg_count != 1 || body.basic_blocks.len() != 1 || body.local_decls.len() > 16 {
        return Err(
            "atomic byte wrapper requires a bounded single-block actual method body".into(),
        );
    }
    if !matches!(body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty.kind(),
        ty::Ref(_, inner, mutable) if *inner == source && !mutable.is_mut())
        || !matches!(body.return_ty().kind(),
            ty::Ref(_, inner, mutable) if *inner == target && !mutable.is_mut())
    {
        return Err("atomic byte wrapper actual body signature mismatch".into());
    }
    let block = &body.basic_blocks[START_BLOCK];
    if block.statements.len() > 32 || !matches!(block.terminator().kind, TerminatorKind::Return) {
        return Err("atomic byte wrapper actual method has unsupported control flow".into());
    }
    let mut addresses = vec![None; body.local_decls.len()];
    addresses[1] = Some(Address::SharedSource);
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                addresses[local.as_usize()] = None;
            }
            StatementKind::Assign(assignment) => {
                let (destination, value) = assignment.as_ref();
                if !destination.projection.is_empty() || destination.local.as_usize() == 1 {
                    return Err("atomic byte wrapper body writes storage or receiver".into());
                }
                let address = match value {
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
                        if place.projection.is_empty() =>
                    {
                        addresses[place.local.as_usize()]
                    }
                    Rvalue::RawPtr(rustc_middle::mir::RawPtrKind::Const, place)
                        if place.projection.as_ref() == [ProjectionElem::Deref]
                            && addresses[place.local.as_usize()] == Some(Address::SharedSource) =>
                    {
                        Some(Address::RawSource)
                    }
                    Rvalue::Cast(CastKind::PtrToPtr, operand, ty)
                        if matches!(ty.kind(), ty::RawPtr(inner, mutable)
                            if *inner == target && !mutable.is_mut()) =>
                    {
                        match operand {
                            Operand::Copy(place) | Operand::Move(place)
                                if place.projection.is_empty()
                                    && addresses[place.local.as_usize()]
                                        == Some(Address::RawSource) =>
                            {
                                Some(Address::RawTarget)
                            }
                            _ => None,
                        }
                    }
                    Rvalue::Ref(_, BorrowKind::Shared, place)
                        if place.projection.as_ref() == [ProjectionElem::Deref]
                            && matches!(
                                addresses[place.local.as_usize()],
                                Some(Address::RawTarget | Address::SharedTarget)
                            ) =>
                    {
                        Some(Address::SharedTarget)
                    }
                    _ => None,
                };
                let Some(address) = address else {
                    return Err(
                        "atomic byte wrapper actual body is not a pure shared address cast".into(),
                    );
                };
                let ty = body.local_decls[destination.local].ty;
                let matching = match (address, ty.kind()) {
                    (Address::SharedSource, ty::Ref(_, inner, mutable)) => {
                        *inner == source && !mutable.is_mut()
                    }
                    (Address::RawSource, ty::RawPtr(inner, mutable)) => {
                        *inner == source && !mutable.is_mut()
                    }
                    (Address::RawTarget, ty::RawPtr(inner, mutable)) => {
                        *inner == target && !mutable.is_mut()
                    }
                    (Address::SharedTarget, ty::Ref(_, inner, mutable)) => {
                        *inner == target && !mutable.is_mut()
                    }
                    _ => false,
                };
                if !matching {
                    return Err(
                        "atomic byte wrapper body local type differs from its address".into(),
                    );
                }
                addresses[destination.local.as_usize()] = Some(address);
            }
            StatementKind::Nop => {}
            _ => return Err("atomic byte wrapper actual body has unsupported statements".into()),
        }
    }
    if addresses[0] != Some(Address::SharedTarget) {
        return Err("atomic byte wrapper body does not return its unchanged shared target".into());
    }
    Ok(())
}
