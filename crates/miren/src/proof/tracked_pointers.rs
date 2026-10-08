use super::*;
use symbolic::MemoryProjection;

const MAX_TRACKED_ADDRESSES: usize = 512;

#[derive(Clone, PartialEq, Eq)]
pub(super) struct AddressLocation {
    allocation: usize,
    projection: Vec<AddressProjection>,
    extent: u64,
    cursor: Option<(Term, Term)>,
}

#[derive(Clone, PartialEq, Eq)]
enum AddressProjection {
    Field(usize),
    Variant(usize),
    Index(Term),
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn raw_tracked_pointer(
        &mut self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        mutable: bool,
    ) -> Result<Value, String> {
        let ty = place.ty(&body.local_decls, self.tcx).ty;
        if !ty.is_sized(self.tcx, ty::TypingEnv::fully_monomorphized()) {
            return Err("tracked raw addresses require a sized pointee".into());
        }
        let reference = if place.projection.is_empty() {
            let local = place.local.as_usize();
            let allocation = if let Some(allocation) = state.addresses[local] {
                self.local(state, local)?;
                allocation
            } else {
                if state.memory.len() >= MAX_TRACKED_ADDRESSES {
                    return Err("memory allocation budget reached".into());
                }
                let value = self.local(state, local)?;
                let allocation = state.memory.len();
                state.memory.push(Some(value));
                state.addresses[local] = Some(allocation);
                allocation
            };
            Value::Reference {
                allocation,
                projection: Vec::new(),
                mutable,
            }
        } else {
            let (last, prefix) = place.projection.split_last().expect("nonempty projection");
            if *last != ProjectionElem::Deref {
                return Err("raw subobject addresses need tracked typed layout offsets".into());
            }
            let base = Place {
                local: place.local,
                projection: self.tcx.mk_place_elems(prefix),
            };
            if !matches!(self.place(state, base)?, Value::Reference { .. }) {
                return Err("raw reborrowing needs a tracked allocation reference".into());
            }
            self.borrow(state, place, mutable)?
        };
        self.tracked_reference_address(reference, ty, state)
    }

    pub(super) fn reference_raw_pointer(
        &mut self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: Value,
        state: &mut State,
    ) -> Result<Value, String> {
        let ty::Ref(_, pointee, _) = source.kind() else {
            return Err("reference address cast requires a reference source".into());
        };
        if !self.thin_raw_pointer(target)
            || !pointee.is_sized(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Err("reference address casts require sized thin pointers".into());
        }
        self.tracked_reference_address(value, *pointee, state)
    }

    fn tracked_reference_address(
        &mut self,
        reference: Value,
        pointee: Ty<'tcx>,
        state: &mut State,
    ) -> Result<Value, String> {
        self.validate_tracked_value(&reference, state)?;
        let Value::Reference {
            allocation,
            projection,
            ..
        } = &reference
        else {
            return Err("raw address requires allocation provenance, not a value snapshot".into());
        };
        let projection = projection
            .iter()
            .map(|projection| match projection {
                MemoryProjection::Field(index) => Ok(AddressProjection::Field(*index)),
                MemoryProjection::Variant(index) => Ok(AddressProjection::Variant(*index)),
                MemoryProjection::Index(index) => Ok(AddressProjection::Index(index.integer()?.0)),
                MemoryProjection::Slice { .. } | MemoryProjection::Chunks { .. } => {
                    Err("raw slice projection addresses need a typed offset model".to_owned())
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let layout = self.static_layout(pointee)?;
        let extent = layout.size.bytes();
        let location = AddressLocation {
            allocation: *allocation,
            projection,
            extent,
            cursor: None,
        };
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let address = if let Some((_, address)) = self
            .tracked_addresses
            .iter()
            .find(|(existing, _)| *existing == location)
        {
            address.clone()
        } else {
            if self.tracked_addresses.len() >= MAX_TRACKED_ADDRESSES {
                return Err("tracked raw address identity budget reached".into());
            }
            let address = self.fresh_abstraction(
                Sort::BitVec(bits),
                "tracked allocation base addresses are symbolic",
            );
            self.tracked_addresses.push((location, address.clone()));
            address
        };
        if u128::from(extent) > (1u128 << (bits - 1)) - 1 {
            return Err("tracked raw address extent exceeds target isize::MAX".into());
        }
        let limit = self
            .terms
            .bit_vector((1u128 << bits) - 1 - u128::from(extent), bits)?;
        state.conditions.push(
            self.terms
                .apply(Op::BvUnsignedLe, &[address.clone(), limit])?,
        );
        let zero = self.terms.bit_vector(0, bits)?;
        state.conditions.push(symbolic::not(
            &self
                .terms
                .apply(Op::Equal, &[address.clone(), zero.clone()])?,
        ));
        let mask = self
            .terms
            .bit_vector(u128::from(layout.align.abi.bytes() - 1), bits)?;
        let low = self.terms.apply(Op::BvAnd, &[address.clone(), mask])?;
        state
            .conditions
            .push(self.terms.apply(Op::Equal, &[low, zero])?);
        Ok(Value::TrackedPointer {
            reference: Box::new(reference),
            address,
            bits,
        })
    }

    pub(super) fn tracked_pointer_offset(
        &mut self,
        id: DefId,
        source: Ty<'tcx>,
        pointer: Value,
        count: Value,
        state: &mut State,
    ) -> Result<Value, String> {
        self.validate_tracked_value(&pointer, state)?;
        let Value::TrackedPointer {
            reference,
            address,
            bits,
        } = pointer
        else {
            return Err("pointer Offset requires tracked allocation provenance".into());
        };
        let ty::RawPtr(pointee, _) = source.kind() else {
            return Err("pointer Offset requires a thin raw pointer".into());
        };
        let stride = self.static_layout(*pointee)?.size.bytes();
        if stride == 0 {
            return Err("zero-sized pointer Offset is not modeled".into());
        }
        let (count, count_bits, signed) = count.integer()?;
        if count_bits != bits || !signed {
            return Err("pointer Offset requires target-width isize displacement".into());
        }
        let location = self
            .tracked_addresses
            .iter()
            .find(|(_, existing)| *existing == address)
            .map(|(location, _)| location.clone())
            .ok_or("pointer Offset lacks a compiler-certified tracked extent")?;
        if self.tracked_addresses.len() >= MAX_TRACKED_ADDRESSES {
            return Err("tracked raw address identity budget reached".into());
        }
        // Double-width arithmetic retains the full signed product and cursor sum.
        // Every admitted extent and stride fits the target's signed object bound.
        if u128::from(stride) > (1u128 << (bits - 1)) - 1 {
            return Err("pointer Offset stride exceeds target isize::MAX".into());
        }
        let wide_bits = bits * 2;
        let extended_count = self.terms.apply(Op::SignExtend(bits), &[count])?;
        let scale = self.terms.bit_vector(u128::from(stride), wide_bits)?;
        let displacement = self.terms.apply(Op::BvMul, &[extended_count, scale])?;
        let (base, old_offset) = location
            .cursor
            .clone()
            .unwrap_or((address.clone(), self.terms.bit_vector(0, wide_bits)?));
        let offset = self
            .terms
            .apply(Op::BvAdd, &[old_offset, displacement.clone()])?;
        let zero = self.terms.bit_vector(0, wide_bits)?;
        let extent = self
            .terms
            .bit_vector(u128::from(location.extent), wide_bits)?;
        let max = self
            .terms
            .bit_vector((1u128 << (bits - 1)) - 1, wide_bits)?;
        let min = self.terms.apply(
            Op::SignExtend(bits),
            &[self.terms.bit_vector(1u128 << (bits - 1), bits)?],
        )?;
        let conditions = [
            self.terms
                .apply(Op::BvSignedGe, &[displacement.clone(), min])?,
            self.terms.apply(Op::BvSignedLe, &[displacement, max])?,
            self.terms.apply(Op::BvSignedGe, &[offset.clone(), zero])?,
            self.terms
                .apply(Op::BvSignedLe, &[offset.clone(), extent])?,
        ];
        let valid = self.terms.apply(Op::And, &conditions)?;
        self.require(
            id,
            self.tcx.def_span(id),
            &state.conditions,
            &valid,
            ObligationKind::Validity,
            "pointer Offset must fit signed target displacement and its tracked allocation".into(),
        )?;
        state.conditions.push(valid);
        let low = self.terms.apply(
            Op::Extract {
                high: bits - 1,
                low: 0,
            },
            std::slice::from_ref(&offset),
        )?;
        let address = self.terms.apply(Op::BvAdd, &[base.clone(), low])?;
        if !self
            .tracked_addresses
            .iter()
            .any(|(_, existing)| *existing == address)
        {
            self.tracked_addresses.push((
                AddressLocation {
                    cursor: Some((base, offset)),
                    ..location
                },
                address.clone(),
            ));
        }
        self.record_model(
            id,
            "tracked in-allocation or one-past raw address; no raw memory access",
        );
        Ok(Value::TrackedPointer {
            reference,
            address,
            bits,
        })
    }
}
