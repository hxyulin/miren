//! Explicit device effects. Numeric transports never acquire Rust allocation provenance.
use super::*;
use miren::{HardwareDevice, HardwareModel};
use rustc_abi::{BackendRepr, Primitive, Scalar};
use rustc_span::Symbol;

impl<'tcx> Engine<'tcx> {
    fn selected_hardware_model(&self) -> Result<Option<HardwareModel>, String> {
        let Some(model) = &self.config.hardware else {
            return Ok(None);
        };
        model.validate()?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        if bits != model.pointer_bits {
            return Err("hardware model pointer width does not match the compiler target".into());
        }
        let mut found = Vec::new();
        for device in [HardwareDevice::Stm32h723vg, HardwareDevice::Stm32f407ig] {
            let marker = (
                Symbol::intern("feature"),
                Some(Symbol::intern(device.chip())),
            );
            let cfg = self.tcx.sess.config.contains(&marker);
            let path = self.tcx.sess.opts.search_paths.iter().any(|path| {
                if !path
                    .kind
                    .matches(rustc_session::search_paths::PathKind::Native)
                {
                    return false;
                }
                let components: Vec<_> = path.dir.components().collect();
                let Some(suffix) = components.len().checked_sub(4) else {
                    return false;
                };
                let components = &components[suffix..];
                components[0]
                    .as_os_str()
                    .to_str()
                    .is_some_and(|name| name.starts_with("stm32-metapac-"))
                    && components[1].as_os_str() == "src"
                    && components[2].as_os_str() == "chips"
                    && components[3].as_os_str() == device.chip()
            });
            if cfg || path {
                found.push(device);
            }
        }
        if found.as_slice() != [model.device] {
            return Err(
                "hardware model needs exact noncontradictory compiler device selection evidence"
                    .into(),
            );
        }
        Ok(Some(model.clone()))
    }

    fn record_hardware_use(&mut self, model: &HardwareModel, id: DefId, effect: String) {
        let assumption = model.assumption();
        if !self.proof.entry_assumptions.contains(&assumption) {
            self.proof.entry_assumptions.push(assumption);
        }
        self.record_model(id, &effect);
    }

    fn hardware_address(&self, value: &Value, bits: u32) -> Result<Term, String> {
        let Value::RawPointer {
            address,
            bits: actual,
        } = value
        else {
            return Err(
                "hardware effects require numeric pointers without Rust allocation rights".into(),
            );
        };
        if *actual != bits
            || address.sort() != &Sort::BitVec(bits)
            || !address.belongs_to(&self.terms)
        {
            return Err("hardware pointer metadata must match its target width and context".into());
        }
        Ok(address.clone())
    }

    pub(super) fn hardware_pointer_call_guard(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &State,
    ) -> Result<(), String> {
        if self.config.hardware.is_none()
            || !matches!(values.first(), Some(Value::RawPointer { .. }))
        {
            return Ok(());
        }
        let callee = instance.def_id();
        let parent = self.tcx.parent(callee);
        if !matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: false }) {
            return Ok(());
        }
        let owner = self
            .tcx
            .type_of(parent)
            .instantiate(self.tcx, instance.args)
            .skip_norm_wip();
        if !matches!(owner.kind(), ty::RawPtr(_, _)) {
            return Ok(());
        }
        let name = self.tcx.item_name(callee);
        if name.as_str().starts_with("wrapping_") || matches!(name.as_str(), "sub" | "byte_sub") {
            return Err(
                "hardware model does not admit subtraction or wrapping pointer methods".into(),
            );
        }
        if name != Symbol::intern("add") && name != Symbol::intern("byte_add") {
            return Ok(());
        }
        let signature = self.call_signature(instance)?;
        let [pointer_ty, count_ty] = signature.inputs() else {
            return Err("hardware add requires an exact pointer/count signature".into());
        };
        if *pointer_ty != owner || *count_ty != self.tcx.types.usize || signature.output() != owner
        {
            return Err("hardware add signature does not match its primitive owner".into());
        }
        let Some(model) = self.selected_hardware_model()? else {
            return Ok(());
        };
        let [_, count] = values else {
            return Err("hardware add arity mismatch".into());
        };
        let (count, bits, signed) = count.integer()?;
        if bits != model.pointer_bits
            || signed
            || !count.belongs_to(&self.terms)
            || count.sort() != &Sort::BitVec(bits)
        {
            return Err("hardware add count must be exact target usize".into());
        }
        let maximum = self.terms.bit_vector((1_u128 << (bits - 1)) - 1, bits)?;
        let bounded = self.terms.apply(Op::BvUnsignedLe, &[count, maximum])?;
        if self.feasible(&[state.conditions.clone(), vec![symbolic::not(&bounded)]].concat())? {
            return Err("hardware add original unsigned count is not bounded by isize::MAX".into());
        }
        Ok(())
    }

    pub(super) fn hardware_pointer_offset(
        &mut self,
        id: DefId,
        source: Ty<'tcx>,
        pointer: &Value,
        count: &Value,
        state: &State,
    ) -> Result<Option<Value>, String> {
        if !matches!(pointer, Value::RawPointer { .. }) {
            return Ok(None);
        }
        let Some(model) = self.selected_hardware_model()? else {
            return Ok(None);
        };
        let ty::RawPtr(pointee, _) = source.kind() else {
            return Err("hardware transport needs a thin byte pointer".into());
        };
        if *pointee != self.tcx.types.u8 {
            return Err("hardware pointer transport supports only byte pointees".into());
        }
        let bits = model.pointer_bits;
        let address = self.hardware_address(pointer, bits)?;
        let (count, width, signed) = count.integer()?;
        if width != bits || count.sort() != &Sort::BitVec(bits) || !count.belongs_to(&self.terms) {
            return Err(
                "hardware byte displacement must have exact target integer metadata".into(),
            );
        }
        let nonnegative = if signed {
            let zero = self.terms.bit_vector(0, bits)?;
            self.terms.apply(Op::BvSignedLe, &[zero, count.clone()])?
        } else {
            let maximum = self.terms.bit_vector((1_u128 << (bits - 1)) - 1, bits)?;
            self.terms
                .apply(Op::BvUnsignedLe, &[count.clone(), maximum])?
        };
        if self.feasible(&[state.conditions.clone(), vec![symbolic::not(&nonnegative)]].concat())? {
            return Err(
                "hardware transport currently requires a nonnegative byte displacement".into(),
            );
        }
        let wide_bits = bits * 2;
        let old = self.terms.apply(Op::ZeroExtend(bits), &[address])?;
        let displacement = self.terms.apply(
            if signed {
                Op::SignExtend(bits)
            } else {
                Op::ZeroExtend(bits)
            },
            &[count],
        )?;
        let new = self.terms.apply(Op::BvAdd, &[old.clone(), displacement])?;
        let maximum = self.terms.bit_vector((1_u128 << bits) - 1, wide_bits)?;
        let nonwrapping = self
            .terms
            .apply(Op::BvUnsignedLe, &[new.clone(), maximum])?;
        for region in &model.regions {
            let start = self.terms.bit_vector(u128::from(region.start), wide_bits)?;
            let end = self.terms.bit_vector(
                u128::from(region.start) + u128::from(region.length),
                wide_bits,
            )?;
            let bounds = [
                nonwrapping.clone(),
                self.terms
                    .apply(Op::BvUnsignedLe, &[start.clone(), old.clone()])?,
                self.terms
                    .apply(Op::BvUnsignedLt, &[old.clone(), end.clone()])?,
                self.terms.apply(Op::BvUnsignedLe, &[start, new.clone()])?,
                self.terms.apply(Op::BvUnsignedLt, &[new.clone(), end])?,
            ];
            let safe = self.terms.apply(Op::And, &bounds)?;
            if !self.feasible(&[state.conditions.clone(), vec![symbolic::not(&safe)]].concat())? {
                let address = self.terms.apply(
                    Op::Extract {
                        high: bits - 1,
                        low: 0,
                    },
                    &[new],
                )?;
                self.record_hardware_use(
                    &model,
                    id,
                    format!(
                        "external MMIO byte transport in {}; no Rust allocation rights",
                        region.name,
                    ),
                );
                return Ok(Some(Value::RawPointer { address, bits }));
            }
        }
        Err(
            "hardware byte transport lacks proven nonwrapping bounds in one configured region"
                .into(),
        )
    }

    fn hardware_u32_type(&self, ty: Ty<'tcx>) -> Result<Option<(String, String)>, String> {
        if ty == self.tcx.types.u32 {
            return Ok(None);
        }
        let ty::Adt(def, args) = ty.kind() else {
            return Err("MMIO access requires exact u32 or a transparent scalar wrapper".into());
        };
        if !def.is_struct()
            || !def.repr().transparent()
            || def.non_enum_variant().fields.len() != 1
            || ty.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Err(
                "MMIO scalar wrapper requires a non-Drop one-field transparent struct".into(),
            );
        }
        let field = &def.non_enum_variant().fields[rustc_abi::FieldIdx::from_usize(0)];
        let field_ty = self
            .tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                field.ty(self.tcx, args),
            )
            .map_err(|error| format!("MMIO scalar field normalization failed: {error:?}"))?;
        let layout = self.static_layout(ty)?;
        let integer = self.static_layout(self.tcx.types.u32)?;
        if field_ty != self.tcx.types.u32
            || layout.size != integer.size
            || layout.align != integer.align
            || layout.fields.offset(0).bytes() != 0
            || !matches!(layout.backend_repr,
                BackendRepr::Scalar(Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I32, false), valid_range,
                }) if valid_range.start == 0 && valid_range.end == u128::from(u32::MAX))
        {
            return Err("MMIO scalar wrapper lacks exact initialized full-range u32 layout".into());
        }
        Ok(Some((
            self.tcx.def_path_str(def.did()),
            field.name.as_str().to_owned(),
        )))
    }

    fn hardware_u32_value(&self, ty: Ty<'tcx>, value: &Value) -> Result<Term, String> {
        let scalar = if let Some((expected_name, expected_field)) = self.hardware_u32_type(ty)? {
            let Value::Adt {
                name,
                variant: 0,
                is_option: false,
                discriminant: 0,
                fields,
            } = value
            else {
                return Err("MMIO scalar wrapper needs exact modeled compiler storage".into());
            };
            let [(field_name, scalar)] = fields.as_slice() else {
                return Err("MMIO scalar wrapper needs one exact modeled field".into());
            };
            if *name != expected_name || *field_name != expected_field {
                return Err(
                    "MMIO scalar wrapper modeled identity disagrees with compiler metadata".into(),
                );
            }
            scalar.clone()
        } else {
            value.clone()
        };
        let (expression, bits, signed) = scalar.integer()?;
        if bits != 32
            || signed
            || expression.sort() != &Sort::BitVec(32)
            || !expression.belongs_to(&self.terms)
        {
            return Err("MMIO value needs exact unsigned u32 width and context".into());
        }
        Ok(expression)
    }

    pub(super) fn hardware_volatile_load(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &State,
    ) -> Result<Option<Vec<Return>>, String> {
        if !self
            .tcx
            .is_intrinsic(instance.def_id(), Symbol::intern("volatile_load"))
            || !matches!(values.first(), Some(Value::RawPointer { .. }))
        {
            return Ok(None);
        }
        let Some(model) = self.selected_hardware_model()? else {
            return Ok(None);
        };
        let signature = self.call_signature(instance)?;
        let [pointer_ty] = signature.inputs() else {
            return Err("MMIO volatile load requires one compiler input".into());
        };
        if !matches!(pointer_ty.kind(), ty::RawPtr(pointee, _) if *pointee == signature.output()) {
            return Err("MMIO volatile load compiler pointer/output types disagree".into());
        }
        let [pointer] = values else {
            return Err("MMIO load input arity mismatch".into());
        };
        let address = self.hardware_address(pointer, model.pointer_bits)?;
        let wrapper = self.hardware_u32_type(signature.output())?;
        for register in &model.read_registers {
            let expected = self
                .terms
                .bit_vector(u128::from(register.address), model.pointer_bits)?;
            let equal = self.terms.apply(Op::Equal, &[address.clone(), expected])?;
            if !self.feasible(&[state.conditions.clone(), vec![symbolic::not(&equal)]].concat())? {
                let scalar = Value::Int {
                    expression: self.fresh_abstraction(Sort::BitVec(32),
                        "external hardware reads admit independent arbitrary u32 values; device correlations are unverified"),
                    bits: 32, signed: false,
                };
                let value = if wrapper.is_some() {
                    self.constructed(signature.output(), 0, vec![scalar])?
                } else {
                    scalar
                };
                self.record_hardware_use(
                    &model,
                    instance.def_id(),
                    format!(
                        "external independent arbitrary u32 MMIO read {}; no readback correlation",
                        register.name,
                    ),
                );
                let mut memory = state.memory.clone();
                Self::invalidate_published_atomics(state, &mut memory)?;
                return Ok(Some(vec![Return {
                    flow: activation_flow::Flow::Unarmed,
                    value,
                    conditions: state.conditions.clone(),
                    memory,
                }]));
            }
        }
        Err("MMIO load does not equal one exact configured readable u32 register".into())
    }

    pub(super) fn hardware_volatile_store(
        &mut self,
        instance: ty::Instance<'tcx>,
        values: &[Value],
        state: &State,
    ) -> Result<Option<Vec<Return>>, String> {
        if !self
            .tcx
            .is_intrinsic(instance.def_id(), Symbol::intern("volatile_store"))
        {
            return Ok(None);
        }
        let Some(model) = self.selected_hardware_model()? else {
            return Ok(None);
        };
        let signature = self.call_signature(instance)?;
        let [pointer_ty, stored_ty] = signature.inputs() else {
            return Err("MMIO volatile store requires two compiler inputs".into());
        };
        if !matches!(pointer_ty.kind(), ty::RawPtr(ty, mutability)
            if *ty == *stored_ty && mutability.is_mut())
            || !signature.output().is_unit()
        {
            return Err("MMIO volatile store compiler pointer/value types disagree".into());
        }
        let [pointer, value] = values else {
            return Err("MMIO store input arity mismatch".into());
        };
        let address = self.hardware_address(pointer, model.pointer_bits)?;
        self.hardware_u32_value(*stored_ty, value)?;
        for register in &model.write_registers {
            let expected = self
                .terms
                .bit_vector(u128::from(register.address), model.pointer_bits)?;
            let equal = self.terms.apply(Op::Equal, &[address.clone(), expected])?;
            if !self.feasible(&[state.conditions.clone(), vec![symbolic::not(&equal)]].concat())? {
                self.record_hardware_use(&model, instance.def_id(), format!(
                    "external write-only u32 MMIO effect {}; no readback or Rust storage effect", register.name,
                ));
                let mut memory = state.memory.clone();
                Self::invalidate_published_atomics(state, &mut memory)?;
                return Ok(Some(vec![Return {
                    flow: activation_flow::Flow::Unarmed,
                    value: Value::Unit,
                    conditions: state.conditions.clone(),
                    memory,
                }]));
            }
        }
        Err("MMIO store does not equal one exact configured write-only u32 register".into())
    }
}
