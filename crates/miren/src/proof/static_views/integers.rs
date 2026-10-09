//! Certified primitive integer payloads; runtime reads do not assume initializer history.
use super::*;
use startup_memory::StaticLocation;

impl<'tcx> Engine<'tcx> {
    pub(super) fn mutable_integer_static_constant(
        &self,
        constant: rustc_middle::mir::Const<'tcx>,
        span: Span,
    ) -> Result<Option<Value>, String> {
        let ty::RawPtr(pointee, mutability) = constant.ty().kind() else {
            return Ok(None);
        };
        if self.integer_type(*pointee).is_none()
            && !self.integer_cell_payload(*pointee, 0, None, false, 0)?
        {
            return Ok(None);
        }
        let env = ty::TypingEnv::fully_monomorphized();
        let value = constant.eval(self.tcx, env, span).map_err(|error| {
            format!("mutable integer static constant evaluation failed: {error:?}")
        })?;
        let (ecx, operand) = mk_eval_cx_for_const_val(self.tcx.at(span), env, value, constant.ty())
            .ok_or("mutable integer static constant layout unavailable")?;
        let pointer = ecx
            .read_scalar(&operand)
            .discard_err()
            .ok_or("mutable integer static requires a thin compiler pointer")?
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
                "integer static requires whole mutable Rust integer allocation provenance".into(),
            );
        }
        let original = self.static_original_type(static_id, *pointee)?;
        if original != *pointee {
            return Err("integer static requires an exactly typed declared storage origin".into());
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

    pub(super) fn mutable_integer_static_read(
        &self,
        view: StaticView<'tcx>,
        state: &State,
    ) -> Result<Option<Value>, String> {
        let Some(location) = self.mutable_integer_static_location(view)? else {
            return Ok(None);
        };
        let (bits, signed) = self
            .integer_type(view.ty)
            .ok_or("integer payload type unavailable")?;
        if self.startup && !state.memory.startup_invalidated {
            if let Some(value) = state.memory.startup_values.get(&location) {
                let Value::Int {
                    expression,
                    bits: width,
                    signed: sign,
                } = value
                else {
                    return Err(
                        "startup integer payload overlaps incompatible cached storage".into(),
                    );
                };
                if *width != bits || *sign != signed || *expression.sort() != Sort::BitVec(bits) {
                    return Err("startup integer payload cache has an inconsistent type".into());
                }
                return Ok(Some(value.clone()));
            }
            if !state.memory.startup_initializer_available(location) {
                return Err(
                    "startup integer payload overlaps cached or overwritten storage".into(),
                );
            }
            if state.memory.startup_values.len() >= startup::MAX_STARTUP_LOCATIONS {
                return Err("startup integer history exceeds the 128-location budget".into());
            }
            return Ok(Some(symbolic::integer(
                &self.terms,
                self.startup_scalar_initializer(location)?,
                bits,
                signed,
            )));
        }
        Ok(Some(Value::Int {
            expression: self.fresh_abstraction(
                Sort::BitVec(bits),
                if self.startup {
                    "mutable integer static reads admit arbitrary valid values; startup and \
                     exclusion are invalidated"
                } else {
                    "mutable integer static reads admit arbitrary valid values; startup and \
                     exclusion are unverified"
                },
            ),
            bits,
            signed,
        }))
    }

    pub(super) fn store_startup_integer(
        &self,
        view: StaticView<'tcx>,
        value: &Value,
        state: &mut State,
    ) -> Result<bool, String> {
        if !self.startup {
            return Ok(false);
        }
        let Some(location) = self.mutable_integer_static_location(view)? else {
            return Ok(false);
        };
        let (bits, signed) = self
            .integer_type(view.ty)
            .ok_or("integer payload type unavailable")?;
        let Value::Int {
            expression,
            bits: width,
            signed: sign,
        } = value
        else {
            return Err("startup integer store needs an integer value".into());
        };
        if *width != bits || *sign != signed || *expression.sort() != Sort::BitVec(bits) {
            return Err("startup integer store has an inconsistent type".into());
        }
        if state.memory.startup_invalidated {
            return Ok(true);
        }
        if state.memory.startup_values.iter().any(|(other, stored)| {
            if !location.overlaps(*other) {
                return false;
            }
            let compatible = matches!(stored,
                Value::Int { expression, bits: width, signed: sign }
                    if *width == bits && *sign == signed
                        && *expression.sort() == Sort::BitVec(bits));
            *other != location || !compatible
        }) {
            state.memory.invalidate_startup();
            return Ok(true);
        }
        if !state.memory.startup_values.contains_key(&location)
            && state.memory.startup_values.len() >= startup::MAX_STARTUP_LOCATIONS
        {
            return Err("startup integer history exceeds the 128-location budget".into());
        }
        state.memory.startup_values.insert(location, value.clone());
        Ok(true)
    }

    fn mutable_integer_static_location(
        &self,
        view: StaticView<'tcx>,
    ) -> Result<Option<StaticLocation>, String> {
        if view.kind != ViewKind::Place
            || self.integer_type(view.ty).is_none()
            || view.ty != view.certified
        {
            return Ok(None);
        }
        let declared = self.static_declared_type(view.static_id)?;
        let whole_mutable = view.offset == 0
            && view.original == view.ty
            && declared == view.ty
            && matches!(
                self.tcx.def_kind(view.static_id),
                DefKind::Static {
                    mutability: rustc_hir::Mutability::Mut,
                    ..
                }
            );
        let cell_payload = view.original == declared
            && self.integer_cell_payload(declared, view.offset, Some(view.ty), false, 0)?;
        let byte_array = view.original == declared
            && view.ty == self.tcx.types.u8
            && matches!(
                self.tcx.def_kind(view.static_id),
                DefKind::Static {
                    mutability: rustc_hir::Mutability::Mut,
                    ..
                }
            )
            && match declared.kind() {
                ty::Array(element, _) if *element == self.tcx.types.u8 => {
                    let layout = self.static_layout(declared)?;
                    matches!(layout.fields, rustc_abi::FieldsShape::Array { stride, count }
                        if stride.bytes() == 1 && count <= 128
                        && layout.size.bytes() == count && view.offset < count)
                }
                _ => false,
            };
        if !whole_mutable && !cell_payload && !byte_array {
            return Ok(None);
        }
        Ok(Some(StaticLocation {
            definition: view.static_id,
            offset: view.offset,
            bytes: self.static_layout(view.ty)?.size.bytes(),
        }))
    }

    fn integer_cell_payload(
        &self,
        ty: Ty<'tcx>,
        offset: u64,
        expected: Option<Ty<'tcx>>,
        inside_cell: bool,
        depth: usize,
    ) -> Result<bool, String> {
        if depth >= 8 {
            return Ok(false);
        }
        if self.integer_type(ty).is_some() {
            return Ok(inside_cell && offset == 0 && expected.is_none_or(|value| value == ty));
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
                .map_err(|error| format!("integer static field normalization failed: {error:?}"))?;
            let start = layout.fields.offset(index).bytes();
            let size = self.static_layout(field)?.size.bytes();
            if offset >= start
                && offset - start < size
                && self.integer_cell_payload(
                    field,
                    offset - start,
                    expected,
                    inside_cell,
                    depth + 1,
                )?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
}
