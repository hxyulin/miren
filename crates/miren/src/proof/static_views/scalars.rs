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
        if *pointee != self.tcx.types.bool && !self.boolean_cell_payload(*pointee, 0, false, 0)? {
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
            || self.static_declared_type(static_id)? != *pointee
            || pointer.into_raw_parts().1.bytes() != 0
        {
            return Err(
                "boolean static requires whole mutable Rust bool allocation provenance".into(),
            );
        }
        let original = self.static_original_type(static_id, *pointee)?;
        if original != *pointee {
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
        if view.certified != self.tcx.types.bool {
            return Ok(None);
        }
        let declared = self.static_declared_type(view.static_id)?;
        let whole_mutable = view.offset == 0
            && view.original == self.tcx.types.bool
            && declared == self.tcx.types.bool
            && matches!(
                self.tcx.def_kind(view.static_id),
                DefKind::Static {
                    mutability: rustc_hir::Mutability::Mut,
                    ..
                }
            );
        let cell_payload = view.original == declared
            && self.boolean_cell_payload(declared, view.offset, false, 0)?;
        if !whole_mutable && !cell_payload {
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

    fn boolean_cell_payload(
        &self,
        ty: Ty<'tcx>,
        offset: u64,
        inside_cell: bool,
        depth: usize,
    ) -> Result<bool, String> {
        if depth >= 8 {
            return Ok(false);
        }
        if ty == self.tcx.types.bool {
            return Ok(inside_cell && offset == 0);
        }
        let fields = match ty.kind() {
            ty::Adt(def, args) if def.is_struct() => def
                .non_enum_variant()
                .fields
                .iter()
                .map(|field| field.ty(self.tcx, args))
                .collect::<Vec<_>>(),
            ty::Tuple(fields) => fields.iter().map(ty::Unnormalized::new_wip).collect(),
            _ => return Ok(false),
        };
        if fields.len() > 128 {
            return Ok(false);
        }
        let layout = self.static_layout(ty)?;
        let inside_cell = inside_cell || self.is_static_unsafe_cell(ty);
        for (index, field) in fields.into_iter().enumerate() {
            let field = self
                .tcx
                .try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), field)
                .map_err(|error| format!("boolean static field normalization failed: {error:?}"))?;
            let start = layout.fields.offset(index).bytes();
            let size = self.static_layout(field)?.size.bytes();
            if offset >= start
                && offset - start < size
                && self.boolean_cell_payload(field, offset - start, inside_cell, depth + 1)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
}
