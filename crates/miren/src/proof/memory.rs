use super::storage_locations::{StorageLocation, validate_static_epoch};
use super::*;
use symbolic::MemoryProjection;

const MAX_ALLOCATIONS: usize = 512;
const MAX_BYTE_VIEW_WRITES: u128 = 128;

impl<'tcx> Engine<'tcx> {
    pub(super) fn byte_subslice(
        &self,
        value: Value,
        from: u64,
        to: u64,
        from_end: bool,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let Value::Bytes { length, .. } = &value else {
            return Err("byte subslice requires modeled byte storage".to_owned());
        };
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let offset = symbolic::integer(&self.terms, u128::from(from), bits, false);
        let to = symbolic::integer(&self.terms, u128::from(to), bits, false);
        let end = if from_end {
            symbolic::binary(&self.terms, "sub", (**length).clone(), to)?
        } else {
            to
        };
        let length = symbolic::binary(&self.terms, "sub", end, offset.clone())?;
        self.memory_projection(
            value,
            &symbolic::MemoryProjection::Slice {
                offset: Box::new(offset),
                length: Box::new(length),
            },
            conditions,
        )
    }

    pub(super) fn local(&self, state: &State, local: usize) -> Result<Value, String> {
        let value = if let Some(allocation) = state.addresses[local] {
            state.memory.get(allocation).and_then(Option::as_ref)
        } else {
            state.locals[local].as_ref()
        };
        value
            .cloned()
            .ok_or_else(|| format!("uninitialized or unavailable local _{local}"))
    }

    pub(super) fn snapshots(
        &self,
        values: &[Value],
        memory: &[Option<Value>],
        conditions: &[Term],
    ) -> Result<Vec<Value>, String> {
        values
            .iter()
            .map(|value| self.snapshot(value, memory, conditions, 0))
            .collect()
    }

    pub(super) fn snapshot(
        &self,
        value: &Value,
        memory: &[Option<Value>],
        conditions: &[Term],
        depth: usize,
    ) -> Result<Value, String> {
        if depth >= 16 {
            return Err("memory snapshot nesting limit reached".to_owned());
        }
        match value {
            Value::StaticSlice { epoch, .. } | Value::StaticView { epoch, .. } => {
                validate_static_epoch(memory, *epoch)?;
                Ok(value.clone())
            }
            Value::LocalAtomic {
                allocation,
                bits,
                signed,
            } => match memory.get(*allocation).and_then(Option::as_ref) {
                Some(
                    Value::Int {
                        bits: width,
                        signed: sign,
                        ..
                    }
                    | Value::Atomic {
                        bits: width,
                        signed: sign,
                    },
                ) if (*width, *sign) == (*bits, *signed) => Ok(value.clone()),
                _ => Err("local atomic snapshot points to unavailable backing".into()),
            },
            Value::TraitObject { source, .. } | Value::DebugReference { source, .. } => {
                self.snapshot(source, memory, conditions, depth + 1)?;
                Ok(value.clone())
            }
            Value::RawSlice { source, .. } => {
                self.snapshot(source, memory, conditions, depth + 1)?;
                self.raw_slice_snapshot(value, memory, conditions)
            }
            Value::TrackedPointer { reference, .. } => {
                self.snapshot(reference, memory, conditions, depth + 1)?;
                Ok(value.clone())
            }
            Value::Reference { .. } => {
                let value = self.reference_value(value, memory, conditions)?;
                self.snapshot(&value, memory, conditions, depth + 1)
            }
            Value::Adt {
                name,
                variant,
                is_option,
                discriminant,
                fields,
            } => Ok(Value::Adt {
                name: name.clone(),
                variant: *variant,
                is_option: *is_option,
                discriminant: *discriminant,
                fields: fields
                    .iter()
                    .map(|(name, value)| {
                        Ok((
                            name.clone(),
                            self.snapshot(value, memory, conditions, depth + 1)?,
                        ))
                    })
                    .collect::<Result<_, String>>()?,
            }),
            Value::Enum {
                discriminant,
                variants,
                is_option,
            } => Ok(Value::Enum {
                discriminant: discriminant.clone(),
                is_option: *is_option,
                variants: variants
                    .iter()
                    .map(|value| self.snapshot(value, memory, conditions, depth + 1))
                    .collect::<Result<_, _>>()?,
            }),
            Value::Tuple(fields) => Ok(Value::Tuple(
                fields
                    .iter()
                    .map(|value| self.snapshot(value, memory, conditions, depth + 1))
                    .collect::<Result<_, _>>()?,
            )),
            Value::Elements(fields) => Ok(Value::Elements(
                fields
                    .iter()
                    .map(|value| self.snapshot(value, memory, conditions, depth + 1))
                    .collect::<Result<_, _>>()?,
            )),
            other => Ok(other.clone()),
        }
    }

    pub(super) fn reference_value(
        &self,
        reference: &Value,
        memory: &[Option<Value>],
        conditions: &[Term],
    ) -> Result<Value, String> {
        let Value::Reference {
            allocation,
            projection,
            mutable,
        } = reference
        else {
            return Err("expected an allocation reference".to_owned());
        };
        let location = StorageLocation::tracked(*allocation, *mutable);
        let mut value = location.read(memory)?.clone();
        let mut projections = projection.iter().peekable();
        while let Some(element) = projections.next() {
            if let MemoryProjection::Chunks { width, count } = element
                && let Some(MemoryProjection::Index(index)) = projections.peek()
            {
                let bits = u32::from(self.tcx.sess.target.pointer_width);
                self.memory_bounds(
                    index,
                    &symbolic::integer(&self.terms, *count as u128, bits, false),
                    conditions,
                )?;
                let offset = symbolic::binary(
                    &self.terms,
                    "mul",
                    (**index).clone(),
                    symbolic::integer(&self.terms, *width as u128, bits, false),
                )?;
                value = self.memory_projection(
                    value,
                    &MemoryProjection::Slice {
                        offset: Box::new(offset),
                        length: Box::new(symbolic::integer(
                            &self.terms,
                            *width as u128,
                            bits,
                            false,
                        )),
                    },
                    conditions,
                )?;
                projections.next();
            } else if let MemoryProjection::Slice { offset, length } = element
                && let Some(MemoryProjection::Index(index)) = projections.peek()
                && self.finite_element_region(&value, offset, length, conditions)?
            {
                self.memory_bounds(index, length, conditions)?;
                let absolute =
                    symbolic::binary(&self.terms, "add", (**offset).clone(), (**index).clone())?;
                value = self.memory_projection(
                    value,
                    &MemoryProjection::Index(Box::new(absolute)),
                    conditions,
                )?;
                projections.next();
            } else {
                value = self.memory_projection(value, element, conditions)?;
            }
        }
        Ok(value)
    }

    pub(super) fn memory_projection(
        &self,
        value: Value,
        projection: &MemoryProjection,
        conditions: &[Term],
    ) -> Result<Value, String> {
        match (projection, value.materialize()?) {
            (MemoryProjection::Field(index), Value::Adt { fields, .. }) => fields
                .get(*index)
                .map(|(_, value)| value.clone())
                .ok_or_else(|| "memory field missing".to_owned()),
            (MemoryProjection::Field(index), Value::Tuple(fields)) => fields
                .get(*index)
                .cloned()
                .ok_or_else(|| "memory tuple field missing".to_owned()),
            (MemoryProjection::Variant(expected), value @ Value::Adt { .. }) => {
                let Value::Adt { variant, .. } = value else {
                    unreachable!()
                };
                if variant != *expected {
                    return Err("memory downcast has wrong variant".to_owned());
                }
                Ok(value)
            }
            (
                MemoryProjection::Variant(expected),
                Value::Enum {
                    discriminant,
                    variants,
                    ..
                },
            ) => {
                let value = variants
                    .get(*expected)
                    .ok_or("memory enum variant missing")?;
                let Value::Adt {
                    discriminant: tag, ..
                } = value
                else {
                    return Err("memory enum payload missing".to_owned());
                };
                let (_, bits, signed) = discriminant.integer()?;
                let equal = symbolic::binary(
                    &self.terms,
                    "eq",
                    *discriminant,
                    symbolic::integer(&self.terms, *tag, bits, signed),
                )?
                .boolean()?;
                if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&equal)]].concat())? {
                    return Err("memory downcast lacks a proven variant check".to_owned());
                }
                Ok(value.clone())
            }
            (MemoryProjection::Index(index), Value::Elements(elements)) => {
                self.fixed_element(&elements, index, conditions)
            }
            (MemoryProjection::Index(index), Value::Bytes { data, length }) => {
                self.memory_bounds(index, &length, conditions)?;
                Ok(Value::Int {
                    expression: self
                        .terms
                        .apply(Op::Select, &[data.clone(), index.integer()?.0])?,
                    bits: 8,
                    signed: false,
                })
            }
            (
                MemoryProjection::Slice { offset, length },
                Value::Bytes {
                    data,
                    length: capacity,
                },
            ) => {
                let valid_offset =
                    symbolic::binary(&self.terms, "le", (**offset).clone(), (*capacity).clone())?
                        .boolean()?;
                let available =
                    symbolic::binary(&self.terms, "sub", (*capacity).clone(), (**offset).clone())?;
                let valid_length =
                    symbolic::binary(&self.terms, "le", (**length).clone(), available)?
                        .boolean()?;
                let safe = self.terms.apply(Op::And, &[valid_offset, valid_length])?;
                if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&safe)]].concat())? {
                    return Err("byte view lacks proven region bounds".to_owned());
                }
                let (offset, _bits, signed) = offset.integer()?;
                if signed {
                    return Err("signed byte view offset".to_owned());
                }
                Ok(Value::Bytes {
                    length: length.clone(),
                    data: self.terms.apply(Op::ArrayOffset, &[data, offset])?,
                })
            }
            (MemoryProjection::Chunks { width, count }, bytes @ Value::Bytes { .. }) => {
                let bits = u32::from(self.tcx.sess.target.pointer_width);
                let mut chunks = Vec::with_capacity(*count);
                for index in 0..*count {
                    chunks.push(self.memory_projection(
                        bytes.clone(),
                        &MemoryProjection::Slice {
                            offset: Box::new(symbolic::integer(
                                &self.terms,
                                (index * width) as u128,
                                bits,
                                false,
                            )),
                            length: Box::new(symbolic::integer(
                                &self.terms,
                                *width as u128,
                                bits,
                                false,
                            )),
                        },
                        conditions,
                    )?);
                }
                Ok(Value::Elements(chunks.into()))
            }
            _ => Err("unsupported memory projection".to_owned()),
        }
    }

    pub(super) fn memory_bounds(
        &self,
        index: &Value,
        length: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let (_, width, signed) = index.integer()?;
        if signed || width != u32::from(self.tcx.sess.target.pointer_width) {
            return Err("memory index type mismatch".to_owned());
        }
        let inside =
            symbolic::binary(&self.terms, "lt", index.clone(), length.clone())?.boolean()?;
        if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&inside)]].concat())? {
            return Err("memory index lacks a proven bounds check".to_owned());
        }
        Ok(())
    }

    pub(super) fn memory_path(
        &self,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<(Option<usize>, Vec<MemoryProjection>, bool), String> {
        let local = place.local.as_usize();
        let mut allocation = state.addresses[local];
        let mut path = Vec::new();
        let mut value = self.local(state, local)?;
        let mut writable = true;
        for projection in place.projection {
            value = value.materialize()?;
            match projection {
                ProjectionElem::Deref => {
                    if let Value::Reference {
                        allocation: target,
                        projection,
                        mutable,
                    } = value
                    {
                        allocation = Some(target);
                        path = projection;
                        // Every enclosing borrow must grant ordinary mutation rights.
                        writable &= mutable;
                        value = self.reference_value(
                            &Value::Reference {
                                allocation: target,
                                projection: path.clone(),
                                mutable,
                            },
                            &state.memory,
                            &state.conditions,
                        )?;
                    } else {
                        writable = false;
                    }
                }
                ProjectionElem::Field(field, _) => {
                    let element = MemoryProjection::Field(field.as_usize());
                    value = self.memory_projection(value, &element, &state.conditions)?;
                    path.push(element);
                }
                ProjectionElem::Downcast(_, variant) => {
                    let element = MemoryProjection::Variant(variant.as_usize());
                    value = self.memory_projection(value, &element, &state.conditions)?;
                    path.push(element);
                }
                ProjectionElem::Index(index) => {
                    let element =
                        MemoryProjection::Index(Box::new(self.local(state, index.as_usize())?));
                    value = self.memory_projection(value, &element, &state.conditions)?;
                    path.push(element);
                }
                ProjectionElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let width = u32::from(self.tcx.sess.target.pointer_width);
                    let offset = symbolic::integer(&self.terms, u128::from(offset), width, false);
                    let index = if from_end {
                        let length = match &value {
                            Value::Bytes { length, .. } => (**length).clone(),
                            Value::Elements(elements) => {
                                symbolic::integer(&self.terms, elements.len() as u128, width, false)
                            }
                            _ => return Err("constant memory index needs array storage".to_owned()),
                        };
                        symbolic::binary(&self.terms, "sub", length, offset)?
                    } else {
                        offset
                    };
                    let element = MemoryProjection::Index(Box::new(index));
                    value = self.memory_projection(value, &element, &state.conditions)?;
                    path.push(element);
                }
                _ => return Err("unsupported memory address projection".to_owned()),
            }
        }
        Ok((allocation, path, writable))
    }

    pub(super) fn borrow_shared_snapshot(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let ty::Ref(_, pointee, mutability) = body.local_decls[place.local].ty.kind() else {
            return Ok(None);
        };
        if mutability.is_mut()
            || !pointee.is_freeze(self.tcx, ty::TypingEnv::fully_monomorphized())
            || !matches!(place.projection.first(), Some(ProjectionElem::Deref))
            || place
                .projection
                .iter()
                .skip(1)
                .any(|element| matches!(element, ProjectionElem::Deref))
        {
            return Ok(None);
        }
        let source = self.local(state, place.local.as_usize())?.materialize()?;
        if !matches!(
            source,
            Value::Adt { .. }
                | Value::Enum { .. }
                | Value::Tuple(_)
                | Value::Elements(_)
                | Value::Bytes { .. }
                | Value::Int { .. }
                | Value::Float { .. }
                | Value::Bool(_)
                | Value::Unit
        ) {
            return Ok(None);
        }
        // Shared freeze references can be represented by pointee snapshots. Reborrowing a
        // snapshot must not invent an allocation owned by the temporary reference local.
        // Actual retained references keep their allocation and liveness checks in `borrow`.
        self.validate_tracked_value(&source, state)?;
        let value = self.place(state, place)?;
        self.validate_tracked_value(&value, state)?;
        Ok(Some(value))
    }

    pub(super) fn validate_mutable_handle_rights(
        &self,
        expected: Ty<'tcx>,
        value: &Value,
    ) -> Result<(), String> {
        if matches!(expected.kind(), ty::Ref(_, _, mutability) if mutability.is_mut())
            && matches!(value, Value::Reference { mutable: false, .. })
        {
            return Err("readonly reference cannot be exposed as a declared mutable handle".into());
        }
        if let ty::Tuple(types) = expected.kind()
            && let Value::Tuple(fields) = value
        {
            for (ty, value) in types.iter().zip(fields) {
                self.validate_mutable_handle_rights(ty, value)?;
            }
        }
        if let ty::Array(element, _) = expected.kind()
            && let Value::Elements(elements) = value
        {
            for value in elements {
                self.validate_mutable_handle_rights(*element, value)?;
            }
        }
        if let ty::Adt(def, args) = expected.kind() {
            if let Value::Enum { variants, .. } = value {
                for variant in variants {
                    self.validate_mutable_handle_rights(expected, variant)?;
                }
            }
            if let Value::Adt {
                name,
                variant,
                fields,
                ..
            } = value
            {
                if *name != self.tcx.def_path_str(def.did()) {
                    return Err("mutable return aggregate has mismatched compiler identity".into());
                }
                let layout = def
                    .variants()
                    .get(rustc_abi::VariantIdx::from_usize(*variant))
                    .ok_or("mutable return aggregate has an invalid variant")?;
                if fields.len() != layout.fields.len() {
                    return Err("mutable return aggregate has mismatched fields".into());
                }
                for (field, (_, value)) in layout.fields.iter().zip(fields.iter()) {
                    let ty = self
                        .tcx
                        .try_normalize_erasing_regions(
                            ty::TypingEnv::fully_monomorphized(),
                            field.ty(self.tcx, args),
                        )
                        .map_err(|error| {
                            format!("mutable handle field normalization failed: {error:?}")
                        })?;
                    self.validate_mutable_handle_rights(ty, value)?;
                }
            }
        }
        Ok(())
    }

    pub(super) fn shared_dereference_copy(
        &self,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let value = self.place(state, place)?;
        if matches!(value, Value::Reference { mutable: false, .. }) {
            // Further compiler dereference-only copies preserve the already narrowed rights.
            return Ok(Some(value));
        }
        if !value.contains_mutable() {
            return Ok(None);
        }
        let (_, _, writable) = self.memory_path(state, place)?;
        if writable {
            return Ok(None);
        }
        if let Value::Reference {
            allocation,
            projection,
            ..
        } = value
        {
            // Compiler no-retag copies traverse an enclosing shared borrow for reads. Their
            // allocation and projection stay exact; they cannot restore mutation permission.
            return Ok(Some(Value::Reference {
                allocation,
                projection,
                mutable: false,
            }));
        }
        Err("shared dereference copies require a direct reference handle".into())
    }

    pub(super) fn borrow(
        &self,
        state: &mut State,
        place: Place<'tcx>,
        mutable: bool,
    ) -> Result<Value, String> {
        if matches!(place.projection.as_ref(), [ProjectionElem::Deref]) {
            let source = self.local(state, place.local.as_usize())?;
            if self
                .finite_element_slice_length(&source, &state.memory, &state.conditions)?
                .is_some()
                && let Value::Reference {
                    allocation,
                    projection,
                    mutable: true,
                } = source
            {
                self.validate_tracked_value(
                    &Value::Reference {
                        allocation,
                        projection: projection.clone(),
                        mutable: true,
                    },
                    state,
                )?;
                return Ok(Value::Reference {
                    allocation,
                    projection,
                    mutable,
                });
            }
        }
        let value = self.place(state, place)?;
        if let Value::TraitObject {
            source,
            id,
            place: true,
        } = &value
        {
            return self.borrow_trait_object(source, *id, mutable, state);
        }
        if let Value::DebugReference {
            source,
            place: true,
        } = value
        {
            if mutable {
                return Err("mutable opaque Debug borrowing remains unsupported".into());
            }
            self.validate_tracked_value(&source, state)?;
            return Ok(Value::DebugReference {
                source,
                place: false,
            });
        }
        if matches!(value, Value::StaticView { .. }) && self.static_place_view(&value, state)? {
            return self.borrow_static_view(&value, mutable, state);
        }
        if !mutable
            && matches!(
                value,
                Value::Bytes { .. }
                    | Value::StaticText
                    | Value::StaticSlice { .. }
                    | Value::Atomic { .. }
            )
        {
            self.validate_tracked_value(&value, state)?;
            if matches!(value, Value::Bytes { .. }) {
                let (allocation, projection, _) = self.memory_path(state, place)?;
                if let Some(allocation) = allocation {
                    return Ok(Value::Reference {
                        allocation,
                        projection,
                        mutable: false,
                    });
                }
            }
            return Ok(value);
        }
        if mutable && matches!(value, Value::StaticText) {
            return Err("mutable static string reference storage is not modeled".to_owned());
        }
        let (allocation, projection, writable) = self.memory_path(state, place)?;
        if mutable && !writable {
            return Err("mutable borrow needs writable allocation storage".to_owned());
        }
        let allocation = if let Some(allocation) = allocation {
            allocation
        } else {
            if state.memory.len() >= MAX_ALLOCATIONS {
                return Err("memory allocation budget reached".to_owned());
            }
            let allocation = state.memory.len();
            let value = self.local(state, place.local.as_usize())?;
            state.memory.push(Some(value));
            state.addresses[place.local.as_usize()] = Some(allocation);
            allocation
        };
        Ok(Value::Reference {
            allocation,
            projection,
            mutable,
        })
    }

    pub(super) fn write(
        &self,
        state: &mut State,
        place: Place<'tcx>,
        value: Value,
    ) -> Result<(), String> {
        let local = place.local.as_usize();
        if place.projection.is_empty() {
            if let Some(allocation) = state.addresses[local] {
                state.memory[allocation] = Some(value);
            } else {
                state.locals[local] = Some(value);
            }
            return Ok(());
        }
        if self.write_static_place(state, place, &value)? {
            return Ok(());
        }
        let (allocation, path, writable) = self.memory_path(state, place)?;
        if allocation.is_none() && !writable {
            return Err("write through a shared snapshot is unsupported".to_owned());
        }
        let mut storage = if let Some(allocation) = allocation {
            let location = StorageLocation::tracked(allocation, writable);
            location.require_write(&state.memory)?;
            location.read(&state.memory)?.clone()
        } else {
            state.locals[local]
                .clone()
                .ok_or("write into uninitialized aggregate storage")?
        };
        self.write_projection(&mut storage, &path, value, &state.conditions)?;
        if let Some(allocation) = allocation {
            state.memory[allocation] = Some(storage);
        } else {
            state.locals[local] = Some(storage);
        }
        Ok(())
    }

    pub(super) fn write_projection(
        &self,
        storage: &mut Value,
        path: &[MemoryProjection],
        value: Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let Some((projection, rest)) = path.split_first() else {
            *storage = value;
            return Ok(());
        };
        if let MemoryProjection::Slice { offset, length } = projection {
            if let Some((
                MemoryProjection::Slice {
                    offset: inner_offset,
                    length: inner_length,
                },
                tail,
            )) = rest.split_first()
            {
                self.memory_projection(storage.clone(), projection, conditions)?;
                let valid_offset = symbolic::binary(
                    &self.terms,
                    "le",
                    (**inner_offset).clone(),
                    (**length).clone(),
                )?
                .boolean()?;
                let available = symbolic::binary(
                    &self.terms,
                    "sub",
                    (**length).clone(),
                    (**inner_offset).clone(),
                )?;
                let valid_length =
                    symbolic::binary(&self.terms, "le", (**inner_length).clone(), available)?
                        .boolean()?;
                let safe = self.terms.apply(Op::And, &[valid_offset, valid_length])?;
                if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&safe)]].concat())? {
                    return Err("nested byte view lacks proven region bounds".to_owned());
                }
                let absolute = symbolic::binary(
                    &self.terms,
                    "add",
                    (**offset).clone(),
                    (**inner_offset).clone(),
                )?;
                let mut translated = vec![MemoryProjection::Slice {
                    offset: Box::new(absolute),
                    length: inner_length.clone(),
                }];
                translated.extend_from_slice(tail);
                return self.write_projection(storage, &translated, value, conditions);
            }
            if let Some((MemoryProjection::Index(index), tail)) = rest.split_first() {
                // Prove the parent region before translating its element address.
                if !self.finite_element_region(storage, offset, length, conditions)? {
                    self.memory_projection(storage.clone(), projection, conditions)?;
                }
                self.memory_bounds(index, length, conditions)?;
                let absolute =
                    symbolic::binary(&self.terms, "add", (**offset).clone(), (**index).clone())?;
                let mut translated = vec![MemoryProjection::Index(Box::new(absolute))];
                translated.extend_from_slice(tail);
                return self.write_projection(storage, &translated, value, conditions);
            }
            let mut view = self.memory_projection(storage.clone(), projection, conditions)?;
            self.write_projection(&mut view, rest, value, conditions)?;
            return self.merge_byte_view(storage, offset, length, view, conditions);
        }
        if let MemoryProjection::Chunks { width, count } = projection {
            let Some((MemoryProjection::Index(index), rest)) = rest.split_first() else {
                return Err("whole chunk view assignment is not modeled".to_owned());
            };
            let bits = u32::from(self.tcx.sess.target.pointer_width);
            self.memory_bounds(
                index,
                &symbolic::integer(&self.terms, *count as u128, bits, false),
                conditions,
            )?;
            let offset = symbolic::binary(
                &self.terms,
                "mul",
                (**index).clone(),
                symbolic::integer(&self.terms, *width as u128, bits, false),
            )?;
            let mut translated = vec![MemoryProjection::Slice {
                offset: Box::new(offset),
                length: Box::new(symbolic::integer(&self.terms, *width as u128, bits, false)),
            }];
            translated.extend_from_slice(rest);
            return self.write_projection(storage, &translated, value, conditions);
        }
        *storage = storage.materialize()?;
        // Establish downcast/bounds conditions before mutating the selected field.
        self.memory_projection(storage.clone(), projection, conditions)?;
        match (projection, storage) {
            (MemoryProjection::Field(index), Value::Adt { fields, .. }) => {
                self.write_projection(&mut fields[*index].1, rest, value, conditions)
            }
            (MemoryProjection::Field(index), Value::Tuple(fields)) => {
                self.write_projection(&mut fields[*index], rest, value, conditions)
            }
            (MemoryProjection::Variant(_), storage @ Value::Adt { .. }) => {
                self.write_projection(storage, rest, value, conditions)
            }
            (MemoryProjection::Variant(index), Value::Enum { variants, .. }) => {
                self.write_projection(&mut variants[*index], rest, value, conditions)
            }
            (MemoryProjection::Index(index), Value::Elements(elements)) => {
                for (position, element) in elements.iter_mut().enumerate() {
                    let equal = symbolic::binary(
                        &self.terms,
                        "eq",
                        (**index).clone(),
                        symbolic::integer(
                            &self.terms,
                            position as u128,
                            u32::from(self.tcx.sess.target.pointer_width),
                            false,
                        ),
                    )?
                    .boolean()?;
                    if !self
                        .feasible(&[conditions.to_vec(), vec![symbolic::not(&equal)]].concat())?
                    {
                        return self.write_projection(element, rest, value, conditions);
                    }
                }
                Err("array write index is not uniquely determined".to_owned())
            }
            (MemoryProjection::Index(index), Value::Bytes { data, .. }) if rest.is_empty() => {
                let (expression, width, signed) = value.integer()?;
                if width != 8 || signed {
                    return Err("byte write has non-byte value".to_owned());
                }
                *data = self.terms.apply(
                    Op::Store,
                    &[data.clone(), index.integer()?.0, expression.clone()],
                )?;
                Ok(())
            }
            _ => Err("unsupported projected memory write".to_owned()),
        }
    }

    fn merge_byte_view(
        &self,
        storage: &mut Value,
        offset: &Value,
        length: &Value,
        view: Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let Value::Bytes {
            length: capacity,
            data,
        } = storage
        else {
            return Err("byte view requires byte allocation storage".to_owned());
        };
        let Value::Bytes {
            length: source_length,
            data: source,
        } = view
        else {
            return Err("byte view assignment requires a byte array".to_owned());
        };
        let equal = symbolic::binary(&self.terms, "eq", (*source_length).clone(), length.clone())?
            .boolean()?;
        if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&equal)]].concat())? {
            return Err("byte view assignment changed its length".to_owned());
        }
        let Some(symbolic::Constant::BitVec { value: count, .. }) =
            symbolic::constant(&capacity.integer()?.0)
        else {
            return Err("byte view updates need a fixed allocation capacity".to_owned());
        };
        let (offset, bits, signed) = offset.integer()?;
        let (length, length_bits, length_signed) = length.integer()?;
        if signed || length_signed || bits != length_bits {
            return Err("byte view index type mismatch".to_owned());
        }
        let fixed_length = match symbolic::constant(&length) {
            Some(symbolic::Constant::BitVec { value, .. }) if value <= count => Some(value),
            _ => None,
        };
        let writes = fixed_length.unwrap_or(count);
        if writes > MAX_BYTE_VIEW_WRITES {
            return Err("byte view update exceeds the 128-write budget".to_owned());
        }
        let original = data.clone();
        let mut copied = original.clone();
        for index in 0..writes {
            let cell = self.terms.bit_vector(index, bits)?;
            let target = self
                .terms
                .apply(Op::BvAdd, &[offset.clone(), cell.clone()])?;
            let source_byte = self
                .terms
                .apply(Op::Select, &[source.clone(), cell.clone()])?;
            let byte = if fixed_length.is_some() {
                source_byte
            } else {
                let inside = self
                    .terms
                    .apply(Op::BvUnsignedLt, &[cell, length.clone()])?;
                let previous = self
                    .terms
                    .apply(Op::Select, &[original.clone(), target.clone()])?;
                self.terms
                    .apply(Op::Ite, &[inside, source_byte, previous])?
            };
            copied = self.terms.apply(Op::Store, &[copied, target, byte])?;
        }
        *data = copied;
        Ok(())
    }

    pub(super) fn callback_environment(
        &self,
        callback: &Value,
        state: &State,
    ) -> Result<(Value, Memory), String> {
        self.validate_tracked_value(callback, state)?;
        if state.memory.len() >= MAX_ALLOCATIONS {
            return Err("memory allocation budget reached".to_owned());
        }
        let mut memory = state.memory.clone();
        let allocation = memory.len();
        memory.push(Some(callback.clone()));
        Ok((
            Value::Reference {
                allocation,
                projection: Vec::new(),
                mutable: true,
            },
            memory,
        ))
    }

    pub(super) fn retire_callback_environment(&self, callback: &Value, results: &mut [Return]) {
        if let Value::Reference { allocation, .. } = callback {
            for result in results {
                result.memory[*allocation] = None;
            }
        }
    }

    pub(super) fn return_value(
        &self,
        value: Value,
        state: &State,
        incoming: usize,
    ) -> Result<Value, String> {
        if matches!(
            value,
            Value::Reference { .. }
                | Value::RawSlice { .. }
                | Value::TrackedPointer { .. }
                | Value::TraitObject { .. }
                | Value::DebugReference { .. }
        ) {
            self.validate_static_initialization_graph(&value, state, &mut Vec::new())?;
        }
        match value {
            Value::StaticSlice { .. } => {
                self.validate_tracked_value(&value, state)?;
                Ok(value)
            }
            Value::StaticView { .. } => self.static_view_operand(value, state),
            Value::TraitObject { place: true, .. } => {
                Err("trait-object payload cannot escape as an owned value".into())
            }
            Value::DebugReference { place: true, .. } => {
                Err("opaque Debug data cannot escape as an owned value".into())
            }
            Value::RawSlice { .. }
            | Value::TraitObject { place: false, .. }
            | Value::DebugReference { place: false, .. }
            | Value::TrackedPointer { .. } => {
                Self::validate_reference_graph(&value, state, Some(incoming), &mut Vec::new())?;
                Ok(value)
            }
            Value::SliceIterator {
                source,
                front,
                back,
                mutable,
                unchecked,
            } => Ok(Value::SliceIterator {
                source: Box::new(self.return_value(*source, state, incoming)?),
                front,
                back,
                mutable,
                unchecked,
            }),
            Value::Reference {
                allocation,
                mutable,
                ..
            } if allocation >= incoming => {
                if mutable {
                    return Err("mutable local borrows cannot escape their frame".to_owned());
                }
                let referent = self.reference_value(&value, &state.memory, &state.conditions)?;
                if referent.contains_local_atomic() {
                    return Err(
                        "borrowed frame-owned atomics cannot escape as owned snapshots".into(),
                    );
                }
                self.return_value(referent, state, incoming)
            }
            value @ (Value::Reference { .. } | Value::Cell { .. } | Value::LocalAtomic { .. }) => {
                Self::validate_reference_graph(&value, state, Some(incoming), &mut Vec::new())?;
                Ok(value)
            }
            Value::Adt {
                name,
                variant,
                is_option,
                discriminant,
                fields,
            } => Ok(Value::Adt {
                name,
                variant,
                is_option,
                discriminant,
                fields: fields
                    .into_iter()
                    .map(|(name, value)| Ok((name, self.return_value(value, state, incoming)?)))
                    .collect::<Result<_, String>>()?,
            }),
            Value::Enum {
                discriminant,
                variants,
                is_option,
            } => Ok(Value::Enum {
                discriminant,
                variants: variants
                    .into_iter()
                    .map(|value| self.return_value(value, state, incoming))
                    .collect::<Result<_, _>>()?,
                is_option,
            }),
            Value::MetadataPointer(value) => Ok(Value::MetadataPointer(Box::new(
                self.return_value(*value, state, incoming)?,
            ))),
            Value::Tuple(fields) => Ok(Value::Tuple(
                fields
                    .into_iter()
                    .map(|value| self.return_value(value, state, incoming))
                    .collect::<Result<_, _>>()?,
            )),
            Value::Elements(fields) => Ok(Value::Elements(
                fields
                    .into_iter()
                    .map(|value| self.return_value(value, state, incoming))
                    .collect::<Result<_, _>>()?,
            )),
            other => Ok(other),
        }
    }
}
