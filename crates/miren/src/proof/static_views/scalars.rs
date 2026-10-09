//! Certified static scalar history is conditional on the explicit startup domain.
use super::*;
use startup_memory::StaticLocation;

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
        state: &State,
    ) -> Result<Option<Value>, String> {
        let Some(location) = self.mutable_bool_static_location(view)? else {
            return Ok(None);
        };
        if self.startup && !state.memory.startup_invalidated {
            if let Some(Value::Bool(value)) = state.memory.startup_values.get(&location) {
                return Ok(Some(Value::Bool(value.clone())));
            }
            if state.memory.startup_initializer_available(location) {
                let value = match self.startup_scalar_initializer(location)? {
                    0 => false,
                    1 => true,
                    _ => return Err("startup boolean initializer has an invalid encoding".into()),
                };
                return Ok(Some(Value::Bool(self.terms.boolean(value))));
            }
        }
        // Ordinary or invalidated reads admit either valid value, including after a write.
        Ok(Some(Value::Bool(self.fresh_abstraction(
            Sort::Bool,
            if self.startup {
                "mutable boolean static reads admit arbitrary valid values; startup and exclusion \
                 are invalidated or overlap"
            } else {
                "mutable boolean static reads admit arbitrary valid values; startup and exclusion \
                 are unverified"
            },
        ))))
    }

    pub(super) fn store_startup_bool(
        &self,
        view: StaticView<'tcx>,
        value: &Value,
        state: &mut State,
    ) -> Result<bool, String> {
        if !self.startup {
            return Ok(false);
        }
        let Some(location) = self.mutable_bool_static_location(view)? else {
            return Ok(false);
        };
        let Value::Bool(_) = value else {
            return Err("startup boolean store needs a valid boolean value".into());
        };
        if state.memory.startup_invalidated {
            return Ok(true);
        }
        if state.memory.startup_values.iter().any(|(other, stored)| {
            location.overlaps(*other) && (*other != location || !matches!(stored, Value::Bool(_)))
        }) {
            state.memory.invalidate_startup();
            return Ok(true);
        }
        if !state.memory.startup_values.contains_key(&location)
            && state.memory.startup_values.len() >= startup::MAX_STARTUP_LOCATIONS
        {
            return Err("startup boolean history exceeds the 128-location budget".into());
        }
        state.memory.startup_values.insert(location, value.clone());
        Ok(true)
    }

    pub(super) fn store_startup_enum(
        &self,
        view: StaticView<'tcx>,
        value: &Value,
        state: &mut State,
    ) -> Result<bool, String> {
        if !self.startup || view.kind != ViewKind::Place || view.ty != view.certified {
            return Ok(false);
        }
        let ty::Adt(def, args) = view.ty.kind() else {
            return Ok(false);
        };
        let env = ty::TypingEnv::fully_monomorphized();
        if !def.is_enum()
            || def.variants().is_empty()
            || def.variants().len() > 64
            || !view.ty.is_freeze(self.tcx, env)
            || !self.tcx.type_is_copy_modulo_regions(env, view.ty)
        {
            return Ok(false);
        }
        // Scalar-only fields cannot publish addresses, callbacks or retained mutable storage.
        // Validate every variant, so symbolic selections retain the same bounded domain.
        for variant in def.variants() {
            for field in &variant.fields {
                let field_ty = self
                    .tcx
                    .try_normalize_erasing_regions(env, field.ty(self.tcx, args))
                    .map_err(|error| {
                        format!("startup enum field normalization failed: {error:?}")
                    })?;
                if !matches!(
                    field_ty.kind(),
                    ty::Bool | ty::Int(_) | ty::Uint(_) | ty::Float(_)
                ) {
                    return Ok(false);
                }
            }
        }
        if state.memory.startup_invalidated {
            return Ok(true);
        }
        let location = StaticLocation {
            definition: view.static_id,
            offset: view.offset,
            bytes: self.static_layout(view.ty)?.size.bytes(),
        };
        if location.bytes == 0 {
            return Ok(false);
        }
        if state.memory.startup_values.iter().any(|(other, stored)| {
            location.overlaps(*other)
                && (*other != location || !matches!(stored, Value::Adt { .. } | Value::Enum { .. }))
        }) {
            state.memory.invalidate_startup();
            return Ok(true);
        }
        if !state.memory.startup_values.contains_key(&location)
            && state.memory.startup_values.len() >= startup::MAX_STARTUP_LOCATIONS
        {
            return Err("startup enum history exceeds the 128-location budget".into());
        }
        state.memory.startup_values.insert(location, value.clone());
        Ok(true)
    }

    fn mutable_bool_static_location(
        &self,
        view: StaticView<'tcx>,
    ) -> Result<Option<StaticLocation>, String> {
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
        Ok(Some(StaticLocation {
            definition: view.static_id,
            offset: view.offset,
            bytes: self.static_layout(view.ty)?.size.bytes(),
        }))
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
