use super::*;
use rustc_abi::Size;
use startup_memory::StaticLocation;

pub(super) const MAX_STARTUP_LOCATIONS: usize = 128;

#[derive(Clone, Copy)]
pub(super) enum AtomicStorage {
    Tracked(usize),
    Startup(StaticLocation),
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn startup_atomic_access(
        &mut self,
        receiver: &Value,
        state: &mut State,
        bits: u32,
        signed: bool,
    ) -> Result<(Value, Option<AtomicStorage>), String> {
        let location = self.static_atomic_location(receiver, state, bits, signed)?;
        if state.memory.startup_invalidated {
            return Ok((self.opaque_atomic_value(bits, signed), None));
        }
        if let Some(Value::Int {
            expression,
            bits: width,
            ..
        }) = state.memory.startup_values.get(&location)
        {
            if bits != *width {
                return Err("startup atomic history has an inconsistent width".into());
            }
            return Ok((
                Value::Int {
                    expression: expression.clone(),
                    bits,
                    signed,
                },
                Some(AtomicStorage::Startup(location)),
            ));
        }
        if !self.startup_location_available(location, state)? {
            return Ok((self.opaque_atomic_value(bits, signed), None));
        }
        let value = self.startup_atomic_initializer(location, bits, signed)?;
        state.memory.startup_values.insert(location, value.clone());
        self.record_model(
            location.definition,
            "fresh-startup static integer atomic; initializer and path-local updates",
        );
        Ok((value, Some(AtomicStorage::Startup(location))))
    }

    pub(super) fn startup_pointer_atomic_load(
        &mut self,
        receiver: &Value,
        receiver_ty: Ty<'tcx>,
        pointer_ty: Ty<'tcx>,
        state: &mut State,
    ) -> Result<Option<Value>, String> {
        if !self.startup || !matches!(receiver, Value::StaticView { .. }) {
            return Ok(None);
        }
        let location = self.static_atomic_storage(receiver, receiver_ty, pointer_ty, state)?;
        if state.memory.startup_invalidated {
            return Ok(None);
        }
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        if let Some(Value::RawPointer {
            address,
            bits: width,
        }) = state.memory.startup_values.get(&location)
        {
            if *width != bits || *address.sort() != Sort::BitVec(bits) {
                return Err("startup pointer atomic history has an inconsistent width".into());
            }
            return Ok(Some(Value::RawPointer {
                address: address.clone(),
                bits,
            }));
        }
        if !self.startup_location_available(location, state)? {
            return Ok(None);
        }
        if location.bytes != u64::from(bits / 8) {
            return Err("startup pointer atomic initializer has an inconsistent width".into());
        }
        let initializer = self.startup_scalar_initializer(location)?;
        let value = Value::RawPointer {
            address: self.terms.bit_vector(initializer, bits)?,
            bits,
        };
        state.memory.startup_values.insert(location, value.clone());
        self.record_model(
            location.definition,
            "fresh-startup pointer atomic; initialized address bits without pointee provenance",
        );
        Ok(Some(value))
    }

    // Called after a typed cache lookup misses. Any cached overlapping footprint is then
    // incompatible, even when its allocation/offset/size matches exactly.
    fn startup_location_available(
        &mut self,
        location: StaticLocation,
        state: &mut State,
    ) -> Result<bool, String> {
        if state
            .memory
            .startup_values
            .keys()
            .any(|other| location.overlaps(*other))
        {
            state.memory.invalidate_startup();
            self.record_model(
                location.definition,
                "overlapping startup atomic views invalidate exact static history",
            );
            return Ok(false);
        }
        if state.memory.startup_values.len() >= MAX_STARTUP_LOCATIONS {
            return Err("startup atomic history exceeds the 128-location budget".into());
        }
        Ok(true)
    }

    pub(super) fn opaque_atomic_value(&mut self, bits: u32, signed: bool) -> Value {
        Value::Int {
            expression: self.fresh_abstraction(
                Sort::BitVec(bits),
                "shared atomic reads allow arbitrary old values; exclusivity is unverified",
            ),
            bits,
            signed,
        }
    }

    pub(super) fn store_atomic(&self, state: &mut State, storage: AtomicStorage, value: Value) {
        match storage {
            AtomicStorage::Tracked(allocation) => state.memory[allocation] = Some(value),
            AtomicStorage::Startup(location) => {
                state.memory.startup_values.insert(location, value);
            }
        }
    }

    fn startup_atomic_initializer(
        &self,
        location: StaticLocation,
        bits: u32,
        signed: bool,
    ) -> Result<Value, String> {
        if location.bytes != u64::from(bits / 8) {
            return Err("startup scalar initializer has an inconsistent width".into());
        }
        let value = self.startup_scalar_initializer(location)?;
        Ok(symbolic::integer(&self.terms, value, bits, signed))
    }

    pub(super) fn startup_scalar_initializer(
        &self,
        location: StaticLocation,
    ) -> Result<u128, String> {
        let initializer = self
            .tcx
            .eval_static_initializer(location.definition)
            .map_err(|error| format!("startup static initializer evaluation failed: {error:?}"))?;
        if location
            .offset
            .checked_add(location.bytes)
            .is_none_or(|end| end > initializer.inner().size().bytes())
        {
            return Err("startup scalar initializer access exceeds its allocation".into());
        }
        let range = rustc_middle::mir::interpret::AllocRange {
            start: Size::from_bytes(location.offset),
            size: Size::from_bytes(location.bytes),
        };
        let scalar = initializer
            .inner()
            .read_scalar(&self.tcx, range, false)
            .map_err(|error| format!("startup scalar initializer scalar read failed: {error:?}"))?;
        let value = scalar
            .to_bits(range.size)
            .discard_err()
            .ok_or("startup scalar initializer cannot contain pointer provenance")?;
        Ok(value)
    }
}
