use super::*;

const MAX_ENCODED_BYTES: usize = 128;

impl<'tcx> Engine<'tcx> {
    pub(super) fn raw_slice_aggregate(
        &mut self,
        id: DefId,
        pointee: Ty<'tcx>,
        mutable: bool,
        values: Vec<Value>,
        state: &mut State,
    ) -> Result<Value, String> {
        if pointee != Ty::new_slice(self.tcx, self.tcx.types.u8) || mutable {
            return Err(
                "raw slice construction requires a shared compiler-typed byte slice".into(),
            );
        }
        let [source, length]: [Value; 2] = values
            .try_into()
            .map_err(|_| "raw slice construction requires pointer and length")?;
        let (metadata, bits, signed) = length.integer()?;
        if signed
            || bits != u32::from(self.tcx.sess.target.pointer_width)
            || metadata.sort() != &Sort::BitVec(bits)
            || !metadata.belongs_to(&self.terms)
        {
            return Err("raw slice metadata requires target-width usize".into());
        }
        let (Value::RawPointer {
            address,
            bits: width,
        }
        | Value::TrackedPointer {
            address,
            bits: width,
            ..
        }) = &source
        else {
            return Err("raw slice metadata requires a modeled thin pointer".into());
        };
        if *width != bits
            || address.sort() != &Sort::BitVec(bits)
            || !address.belongs_to(&self.terms)
        {
            return Err(
                "raw slice source pointer target width or symbolic context mismatch".into(),
            );
        }
        self.validate_tracked_value(&source, state)?;
        let slice = Value::RawSlice {
            source: Box::new(source),
            length: Box::new(length),
        };
        // Raw fat-pointer formation records metadata only. It neither reads the source nor
        // grants reference rights, and the length need not fit a live allocation.
        self.record_model(
            id,
            "compiler-typed raw byte-slice pointer metadata; no Rust access rights",
        );
        Ok(slice)
    }

    pub(super) fn retained_raw_slice(
        &self,
        value: &Value,
        state: &State,
    ) -> Result<Option<Value>, String> {
        self.validate_tracked_value(value, state)?;
        let mut value = value.clone();
        for _ in 0..16 {
            match value {
                value @ Value::RawSlice { .. } => return Ok(Some(value)),
                Value::Reference { .. } => {
                    value = self.reference_value(&value, &state.memory, &state.conditions)?;
                }
                Value::Input(_)
                | Value::Bool(_)
                | Value::Int { .. }
                | Value::Float { .. }
                | Value::Bytes { .. }
                | Value::Adt { .. }
                | Value::Enum { .. }
                | Value::Cell { .. }
                | Value::Atomic { .. }
                | Value::LocalAtomic { .. }
                | Value::SliceIterator { .. }
                | Value::MetadataPointer(_)
                | Value::StaticText
                | Value::FormatArguments
                | Value::RawPointer { .. }
                | Value::TrackedPointer { .. }
                | Value::StaticSlice { .. }
                | Value::StaticView { .. }
                | Value::Tuple(_)
                | Value::Elements(_)
                | Value::Uninitialized
                | Value::TraitObject { .. }
                | Value::DebugReference { .. }
                | Value::FunctionPointer { .. }
                | Value::Function
                | Value::Unit => return Ok(None),
            }
        }
        Err("retained byte slice reference nesting exceeds the model budget".into())
    }

    pub(super) fn raw_slice_bytes(&self, slice: &Value, state: &State) -> Result<Value, String> {
        self.validate_tracked_value(slice, state)?;
        self.raw_slice_snapshot(slice, &state.memory, &state.conditions)
    }

    pub(super) fn raw_slice_snapshot(
        &self,
        slice: &Value,
        memory: &[Option<Value>],
        conditions: &[Term],
    ) -> Result<Value, String> {
        let Value::RawSlice { source, length } = slice else {
            return Err("expected retained raw byte slice".into());
        };
        let Value::TrackedPointer {
            reference,
            address,
            bits,
        } = source.as_ref()
        else {
            return Err("raw byte slice requires tracked allocation provenance".into());
        };
        let location = self
            .tracked_addresses
            .iter()
            .find(|(_, existing)| existing == address)
            .map(|(location, _)| location)
            .ok_or("raw byte slice lacks compiler-certified storage")?;
        if !location
            .pointee
            .is_freeze(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Err("raw byte slices of interior mutable storage remain unsupported".into());
        }
        let value = self.reference_value(reference, memory, conditions)?;
        let bytes = self.encode_storage_bytes(location.pointee, &value, 0)?;
        let mut data = self.terms.apply(
            Op::ConstArray { index_bits: *bits },
            &[self.terms.bit_vector(0, 8)?],
        )?;
        for (index, byte) in bytes.iter().enumerate() {
            data = self.terms.apply(
                Op::Store,
                &[
                    data,
                    self.terms.bit_vector(index as u128, *bits)?,
                    byte.clone(),
                ],
            )?;
        }
        let offset = if let Some((_, cursor)) = &location.cursor {
            Value::Int {
                expression: self.terms.apply(
                    Op::Extract {
                        high: *bits - 1,
                        low: 0,
                    },
                    std::slice::from_ref(cursor),
                )?,
                bits: *bits,
                signed: false,
            }
        } else {
            symbolic::integer(&self.terms, 0, *bits, false)
        };
        self.memory_projection(
            Value::Bytes {
                data,
                length: Box::new(symbolic::integer(
                    &self.terms,
                    bytes.len() as u128,
                    *bits,
                    false,
                )),
            },
            &symbolic::MemoryProjection::Slice {
                offset: Box::new(offset),
                length: length.clone(),
            },
            conditions,
        )?;
        // A byte encoding certifies initialized spatial storage, not permission to create
        // or keep using a Rust reference through a raw pointer.
        Err(self.categorized_error(UnknownCategory::Semantics, RAW_ACCESS_PERMISSION_GAP.into()))
    }

    fn encode_storage_bytes(
        &self,
        ty: Ty<'tcx>,
        value: &Value,
        depth: usize,
    ) -> Result<Vec<Term>, String> {
        let layout = self.static_layout(ty)?;
        let size = layout.size.bytes() as usize;
        if depth >= 16 || size > MAX_ENCODED_BYTES {
            return Err("typed byte storage encoding exceeds the model budget".into());
        }
        let value = value.materialize()?;
        if let Some((bits, signed)) = self.integer_type(ty) {
            let (expression, width, sign) = value.integer()?;
            if (width, sign) != (bits, signed) || size * 8 != bits as usize {
                return Err("typed byte storage integer representation mismatch".into());
            }
            return (0..size)
                .map(|index| {
                    let byte = if self.tcx.data_layout.endian == rustc_abi::Endian::Little {
                        index
                    } else {
                        size - 1 - index
                    } as u32;
                    self.terms.apply(
                        Op::Extract {
                            high: byte * 8 + 7,
                            low: byte * 8,
                        },
                        std::slice::from_ref(&expression),
                    )
                })
                .collect();
        }
        if let ty::Array(element, count) = ty.kind() {
            let count = count
                .try_to_target_usize(self.tcx)
                .ok_or("unknown byte storage length")?;
            if *element == self.tcx.types.u8 {
                let Value::Bytes { data, .. } = value else {
                    return Err("typed byte array lacks initialized storage".into());
                };
                return (0..count)
                    .map(|index| {
                        self.terms.apply(
                            Op::Select,
                            &[
                                data.clone(),
                                self.terms.bit_vector(
                                    u128::from(index),
                                    u32::from(self.tcx.sess.target.pointer_width),
                                )?,
                            ],
                        )
                    })
                    .collect();
            }
            let Value::Elements(elements) = value else {
                return Err("typed array lacks modeled elements".into());
            };
            if elements.len() as u64 != count {
                return Err("typed array length mismatch".into());
            }
            let mut bytes = Vec::new();
            for element_value in elements {
                bytes.extend(self.encode_storage_bytes(*element, &element_value, depth + 1)?);
            }
            return Ok(bytes);
        }
        let ty::Adt(def, args) = ty.kind() else {
            return Err(
                "typed byte storage requires integers, arrays or padding-free structs".into(),
            );
        };
        if !def.is_struct() {
            return Err("typed byte storage unions and enums remain unsupported".into());
        }
        let Value::Adt { fields, .. } = value else {
            return Err("typed byte struct lacks initialized field storage".into());
        };
        if fields.len() != def.non_enum_variant().fields.len() {
            return Err("typed byte struct field count mismatch".into());
        }
        let mut bytes = vec![None; size];
        for (index, field) in def.non_enum_variant().fields.iter().enumerate() {
            let field_ty = self
                .tcx
                .try_normalize_erasing_regions(
                    ty::TypingEnv::fully_monomorphized(),
                    field.ty(self.tcx, args),
                )
                .map_err(|error| format!("byte storage field normalization failed: {error:?}"))?;
            let field_value = &fields
                .get(index)
                .ok_or("typed byte struct field missing")?
                .1;
            let encoded = self.encode_storage_bytes(field_ty, field_value, depth + 1)?;
            let offset = layout.fields.offset(index).bytes() as usize;
            for (position, byte) in encoded.into_iter().enumerate() {
                let slot = bytes
                    .get_mut(offset + position)
                    .ok_or("typed field exceeds layout")?;
                if slot.replace(byte).is_some() {
                    return Err("overlapping byte storage fields remain unsupported".into());
                }
            }
        }
        bytes
            .into_iter()
            .map(|byte| {
                byte.ok_or_else(|| "typed byte storage contains uninitialized padding".into())
            })
            .collect()
    }
}
