use super::tracked_pointers::{AddressLocation, AddressProjection, MAX_TRACKED_ADDRESSES};
use super::*;
use rustc_middle::mir::PlaceElem;
use symbolic::MemoryProjection;

const MAX_RAW_SUBOBJECT_DEPTH: usize = 16;
const MAX_REFERENCE_ARRAY: usize = 256;

impl<'tcx> Engine<'tcx> {
    pub(super) fn raw_subobject_pointer(
        &mut self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        mutable: bool,
    ) -> Result<Value, String> {
        if place.projection.len() > MAX_RAW_SUBOBJECT_DEPTH {
            return Err("raw subobject projection depth budget reached".into());
        }
        // The last dereference identifies the containing allocation. A tracked reference is
        // required; integer-derived handles and shared value snapshots cannot supply provenance.
        let start = place
            .projection
            .iter()
            .rposition(|projection| projection == ProjectionElem::Deref)
            .map_or(0, |index| index + 1);
        let base_place = Place {
            local: place.local,
            projection: self.tcx.mk_place_elems(&place.projection[..start]),
        };
        if start != 0 {
            let before_deref = Place {
                local: place.local,
                projection: self.tcx.mk_place_elems(&place.projection[..start - 1]),
            };
            if !matches!(self.place(state, before_deref)?, Value::Reference { .. }) {
                return Err("raw reborrowing needs a tracked allocation reference".into());
            }
        }
        let base_ty = base_place.ty(&body.local_decls, self.tcx).ty;
        let base_reference = self.borrow(state, base_place, mutable)?;
        let base_pointer = self.tracked_reference_address(base_reference, base_ty, state)?;
        if start == place.projection.len() {
            return Ok(base_pointer);
        }
        let reference = self.borrow(state, place, mutable)?;
        let Value::TrackedPointer {
            address: base,
            bits,
            ..
        } = base_pointer
        else {
            return Err("raw subobject lost its tracked containing address".into());
        };
        let (offset, pointee) =
            self.raw_layout_offset(base_ty, &place.projection[start..], state)?;
        let extent = self.static_layout(pointee)?.size.bytes();
        let base_extent = self.static_layout(base_ty)?.size.bytes();
        let bound = self
            .terms
            .bit_vector(u128::from(base_extent.saturating_sub(extent)), bits)?;
        let inside = self
            .terms
            .apply(Op::BvUnsignedLe, &[offset.clone(), bound])?;
        if extent > base_extent
            || self.feasible(&[state.conditions.clone(), vec![symbolic::not(&inside)]].concat())?
        {
            return Err("raw subobject lacks proven compiler-layout extent bounds".into());
        }
        let address = self.terms.apply(Op::BvAdd, &[base, offset])?;
        let Value::Reference {
            allocation,
            projection,
            ..
        } = &reference
        else {
            return Err("raw subobject borrow lacks tracked storage".into());
        };
        let projection = address_projection(projection)?;
        let location = AddressLocation {
            allocation: *allocation,
            pointee,
            projection,
            extent,
            cursor: None,
        };
        if let Some((_, old_address)) = self
            .tracked_addresses
            .iter()
            .find(|(existing, _)| *existing == location)
        {
            // A preexisting anchor must agree with the newly known containing layout.
            let equal = self
                .terms
                .apply(Op::Equal, &[old_address.clone(), address.clone()])?;
            if self.feasible(&[state.conditions.clone(), vec![symbolic::not(&equal)]].concat())? {
                return Err("raw subobject has an incompatible previously tracked anchor".into());
            }
        } else {
            if self.tracked_addresses.len() >= MAX_TRACKED_ADDRESSES {
                return Err("tracked raw address identity budget reached".into());
            }
            self.tracked_addresses.push((location, address.clone()));
        }
        Ok(Value::TrackedPointer {
            reference: Box::new(reference),
            address,
            bits,
        })
    }

    fn raw_layout_offset(
        &self,
        mut ty: Ty<'tcx>,
        projections: &[PlaceElem<'tcx>],
        state: &State,
    ) -> Result<(Term, Ty<'tcx>), String> {
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let mut offset = self.terms.bit_vector(0, bits)?;
        for projection in projections {
            let layout = self.static_layout(ty)?;
            let delta = match projection {
                ProjectionElem::Field(field, field_ty) => {
                    let index = field.as_usize();
                    let declared = match ty.kind() {
                        ty::Tuple(fields) => ty::Unnormalized::new_wip(
                            fields
                                .get(index)
                                .copied()
                                .ok_or("raw tuple field index is out of bounds")?,
                        ),
                        ty::Adt(def, args) if def.is_struct() => def
                            .non_enum_variant()
                            .fields
                            .get(*field)
                            .ok_or("raw struct field index is out of bounds")?
                            .ty(self.tcx, args),
                        _ => {
                            return Err(
                                "raw field address requires a struct or tuple layout".into()
                            );
                        }
                    };
                    let env = ty::TypingEnv::fully_monomorphized();
                    let declared = self
                        .tcx
                        .try_normalize_erasing_regions(env, declared)
                        .map_err(|error| {
                            format!("raw declared field normalization failed: {error:?}")
                        })?;
                    let supplied = self
                        .tcx
                        .try_normalize_erasing_regions(env, ty::Unnormalized::new_wip(*field_ty))
                        .map_err(|error| {
                            format!("raw MIR field normalization failed: {error:?}")
                        })?;
                    if declared != supplied {
                        return Err("raw field type differs from its compiler declaration".into());
                    }
                    let delta = layout.fields.offset(field.as_usize()).bytes();
                    let field_layout = self.static_layout(declared)?;
                    if layout.align.abi < field_layout.align.abi
                        || delta % field_layout.align.abi.bytes() != 0
                    {
                        return Err("raw field address is not compiler-aligned for its type".into());
                    }
                    ty = declared;
                    self.terms.bit_vector(u128::from(delta), bits)?
                }
                ProjectionElem::Index(local) => {
                    let index = self.local(state, local.as_usize())?;
                    self.raw_array_offset(&mut ty, index, state)?
                }
                ProjectionElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let ty::Array(_, count) = ty.kind() else {
                        return Err("raw constant index requires a sized array".into());
                    };
                    let count = count
                        .try_to_target_usize(self.tcx)
                        .ok_or("raw array length is not concrete")?;
                    let index = if *from_end {
                        count
                            .checked_sub(*offset)
                            .ok_or("raw array index underflow")?
                    } else {
                        *offset
                    };
                    self.raw_array_offset(
                        &mut ty,
                        symbolic::integer(&self.terms, u128::from(index), bits, false),
                        state,
                    )?
                }
                _ => return Err("raw subobject needs typed struct fields or array elements".into()),
            };
            offset = self.terms.apply(Op::BvAdd, &[offset, delta])?;
        }
        Ok((offset, ty))
    }

    fn raw_array_offset(
        &self,
        ty: &mut Ty<'tcx>,
        index: Value,
        state: &State,
    ) -> Result<Term, String> {
        let ty::Array(element, count) = ty.kind() else {
            return Err("raw index address requires a sized array".into());
        };
        let count = count
            .try_to_target_usize(self.tcx)
            .ok_or("raw array length is not concrete")?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        self.memory_bounds(
            &index,
            &symbolic::integer(&self.terms, u128::from(count), bits, false),
            &state.conditions,
        )?;
        let stride = self.static_layout(*element)?.size.bytes();
        *ty = *element;
        self.terms.apply(
            Op::BvMul,
            &[
                index.integer()?.0,
                self.terms.bit_vector(u128::from(stride), bits)?,
            ],
        )
    }

    pub(super) fn tracked_reference_array_transmute(
        &self,
        source: Ty<'tcx>,
        target: Ty<'tcx>,
        value: &Value,
        state: &State,
    ) -> Result<Option<Value>, String> {
        let (ty::Array(raw, source_count), ty::Array(reference, target_count)) =
            (source.kind(), target.kind())
        else {
            return Ok(None);
        };
        let (ty::RawPtr(pointee, raw_mutability), ty::Ref(_, referent, mutability)) =
            (raw.kind(), reference.kind())
        else {
            return Ok(None);
        };
        if pointee != referent || raw_mutability != mutability || source_count != target_count {
            return Err("raw reference array transmute requires identical element types".into());
        }
        let count = source_count
            .try_to_target_usize(self.tcx)
            .ok_or("raw reference array length is not concrete")? as usize;
        if count > MAX_REFERENCE_ARRAY {
            return Err("raw reference array transmute exceeds the model budget".into());
        }
        if self.static_layout(source)?.size != self.static_layout(target)?.size {
            return Err("raw reference array transmute layout mismatch".into());
        }
        let Value::Elements(elements) = value.materialize()? else {
            return Err("raw reference array transmute needs initialized pointer elements".into());
        };
        if elements.len() != count {
            return Err("raw reference array transmute length mismatch".into());
        }
        let mutable = *mutability == rustc_hir::Mutability::Mut;
        let mut references = Vec::with_capacity(count);
        for element in elements {
            self.validate_tracked_value(&element, state)?;
            let Value::TrackedPointer {
                reference, address, ..
            } = element
            else {
                return Err("raw reference array cannot fabricate allocation provenance".into());
            };
            let Value::Reference {
                allocation,
                projection,
                mutable: writable,
            } = *reference
            else {
                return Err("raw reference array requires a tracked storage reference".into());
            };
            if mutable && !writable {
                return Err("raw reference array cannot upgrade shared storage permission".into());
            }
            let typed_projection = address_projection(&projection)?;
            let location = self
                .tracked_addresses
                .iter()
                .find(|(location, candidate)| {
                    *candidate == address
                        && location.pointee == *pointee
                        && location.allocation == allocation
                        && location.projection == typed_projection
                })
                .map(|(location, _)| location)
                .ok_or("raw reference array lacks a compiler-typed storage address")?;
            if location.cursor.is_some() {
                return Err("offset raw pointers need checked typed reference projection".into());
            }
            if mutable {
                for previous in &references {
                    self.disjoint_raw_references(previous, allocation, &projection, state)?;
                }
            }
            // Materializing the retained typed projection checks liveness and initialization.
            let reference = Value::Reference {
                allocation,
                projection,
                mutable,
            };
            let stored = self.reference_value(&reference, &state.memory, &state.conditions)?;
            self.static_store_value(*pointee, &stored, state, 0, &mut 0)?;
            references.push(reference);
        }
        if !references.is_empty() {
            // Disjoint subobjects establish spatial separation only. Even a fresh pointer
            // array needs temporal permission before it can grant Rust reference rights.
            return Err(self
                .categorized_error(UnknownCategory::Semantics, RAW_ACCESS_PERMISSION_GAP.into()));
        }
        Ok(Some(Value::Elements(references.into())))
    }

    fn disjoint_raw_references(
        &self,
        previous: &Value,
        allocation: usize,
        projection: &[MemoryProjection],
        state: &State,
    ) -> Result<(), String> {
        let Value::Reference {
            allocation: old_allocation,
            projection: old,
            ..
        } = previous
        else {
            return Err("raw reference array lost its retained projection".into());
        };
        if *old_allocation != allocation {
            return Ok(());
        }
        for (left, right) in old.iter().zip(projection) {
            match (left, right) {
                (MemoryProjection::Field(left), MemoryProjection::Field(right))
                    if left != right =>
                {
                    return Ok(());
                }
                (MemoryProjection::Index(left), MemoryProjection::Index(right)) => {
                    let equal =
                        symbolic::binary(&self.terms, "eq", (**left).clone(), (**right).clone())?
                            .boolean()?;
                    if !self.feasible(&[state.conditions.clone(), vec![equal]].concat())? {
                        return Ok(());
                    }
                }
                _ => {}
            }
        }
        Err("mutable raw reference array has overlapping or unproved-disjoint subobjects".into())
    }
}

fn address_projection(projections: &[MemoryProjection]) -> Result<Vec<AddressProjection>, String> {
    projections
        .iter()
        .map(|projection| match projection {
            MemoryProjection::Field(index) => Ok(AddressProjection::Field(*index)),
            MemoryProjection::Variant(index) => Ok(AddressProjection::Variant(*index)),
            MemoryProjection::Index(index) => Ok(AddressProjection::Index(index.integer()?.0)),
            MemoryProjection::Slice { .. } | MemoryProjection::Chunks { .. } => {
                Err("raw subobject slices need a typed region layout".into())
            }
        })
        .collect()
}
