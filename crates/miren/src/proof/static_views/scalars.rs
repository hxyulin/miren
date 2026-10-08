//! Whole compiler-backed mutable boolean statics, without startup or shared-state history.
use super::*;

impl<'tcx> Engine<'tcx> {
    pub(super) fn mutable_bool_static_constant(
        &self,
        constant: rustc_middle::mir::Const<'tcx>,
        span: Span,
    ) -> Result<Option<Value>, String> {
        let ty::RawPtr(pointee, mutability) = constant.ty().kind() else {
            return Ok(None);
        };
        if *pointee != self.tcx.types.bool {
            return Ok(None);
        }
        let env = ty::TypingEnv::fully_monomorphized();
        let value = constant.eval(self.tcx, env, span).map_err(|error| {
            format!("mutable boolean static constant evaluation failed: {error:?}")
        })?;
        let (ecx, operand) = mk_eval_cx_for_const_val(self.tcx.at(span), env, value, constant.ty())
            .ok_or("mutable boolean static constant layout unavailable")?;
        let pointer = ecx
            .read_scalar(&operand)
            .discard_err()
            .ok_or("mutable boolean static requires a thin compiler pointer")?
            .to_pointer(&ecx);
        let Some(provenance) = pointer.provenance else {
            return Ok(None);
        };
        let GlobalAlloc::Static(static_id) = self.tcx.global_alloc(provenance.alloc_id()) else {
            return Ok(None);
        };
        if self.tcx.is_foreign_item(static_id)
            || !matches!(
                self.tcx.def_kind(static_id),
                DefKind::Static {
                    mutability: rustc_hir::Mutability::Mut,
                    ..
                }
            )
            || self.static_declared_type(static_id)? != self.tcx.types.bool
            || pointer.into_raw_parts().1.bytes() != 0
        {
            return Err(
                "boolean static requires whole mutable Rust bool allocation provenance".into(),
            );
        }
        let original = self.static_original_type(static_id, *pointee)?;
        if original != self.tcx.types.bool {
            return Err("boolean static requires an exactly typed declared storage origin".into());
        }
        self.intern_static_view(StaticView {
            static_id,
            original,
            ty: *pointee,
            certified: *pointee,
            offset: 0,
            kind: ViewKind::Raw,
            writable: mutability.is_mut(),
        })
        .map(Some)
    }

    pub(super) fn mutable_bool_static_read(
        &self,
        view: StaticView<'tcx>,
    ) -> Result<Option<Value>, String> {
        if view.kind != ViewKind::Place || view.ty != self.tcx.types.bool {
            return Ok(None);
        }
        if view.offset != 0
            || view.original != self.tcx.types.bool
            || view.certified != self.tcx.types.bool
            || self.static_declared_type(view.static_id)? != self.tcx.types.bool
            || !matches!(
                self.tcx.def_kind(view.static_id),
                DefKind::Static {
                    mutability: rustc_hir::Mutability::Mut,
                    ..
                }
            )
        {
            return Ok(None);
        }
        // The declared initializer is construction evidence, not runtime state. Each read admits
        // either valid boolean value, including after a write or a critical-section call.
        Ok(Some(Value::Bool(self.fresh_abstraction(
            Sort::Bool,
            "mutable boolean static reads admit arbitrary valid values; startup and exclusion \
             are unverified",
        ))))
    }
}
