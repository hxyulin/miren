use super::*;
use rustc_middle::mir::Local;

impl<'tcx> Engine<'tcx> {
    pub(super) fn immutable_root_input(&self, body: &Body<'tcx>) -> Result<Option<Local>, String> {
        let mut candidate = None;
        let mut nodes = 0;
        for local in body.args_iter() {
            let ty = body.local_decls[local].ty;
            if let ty::Ref(_, pointee, mutability) = ty.kind()
                && !mutability.is_mut()
                && pointee.is_freeze(self.tcx, ty::TypingEnv::fully_monomorphized())
                && self.plain_root_storage(*pointee, 0, &mut nodes)?
            {
                if candidate.replace(local).is_some() {
                    return Ok(None);
                }
            } else if !self.plain_root_storage(ty, 0, &mut nodes)? {
                // Existing snapshot domains remain available, but competing or nested
                // references and raw pointers cannot acquire new allocation identity.
                return Ok(None);
            }
        }
        Ok(candidate)
    }

    fn plain_root_storage(
        &self,
        ty: Ty<'tcx>,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<bool, String> {
        if depth >= 16
            || *nodes >= MAX_INPUT_VALUES
            || !ty.is_freeze(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            return Ok(false);
        }
        *nodes += 1;
        match ty.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => Ok(true),
            ty::Slice(element) => {
                Ok(*element != self.tcx.types.u8 && self.scalar_slice_element(*element)?.is_some())
            }
            ty::Pat(base, _) => self.plain_root_storage(*base, depth + 1, nodes),
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    if !self.plain_root_storage(field, depth + 1, nodes)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            ty::Array(element, count) => {
                if count
                    .try_to_target_usize(self.tcx)
                    .is_none_or(|count| count > 256)
                {
                    return Ok(false);
                }
                self.plain_root_storage(*element, depth + 1, nodes)
            }
            ty::Adt(def, args) if !def.is_union() => {
                for variant in def.variants() {
                    for field in &variant.fields {
                        let field = self
                            .tcx
                            .try_normalize_erasing_regions(
                                ty::TypingEnv::fully_monomorphized(),
                                field.ty(self.tcx, args),
                            )
                            .map_err(|error| {
                                format!("immutable input field normalization failed: {error:?}")
                            })?;
                        if !self.plain_root_storage(field, depth + 1, nodes)? {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn input_has_shared_storage(&self, ty: Ty<'tcx>, depth: usize) -> Result<bool, String> {
        if depth >= 16 {
            return Err("shared input type nesting exceeds the depth budget".into());
        }
        let env = ty::TypingEnv::fully_monomorphized();
        match ty.kind() {
            ty::Ref(_, pointee, mutability) if !mutability.is_mut() => {
                if !pointee.is_freeze(self.tcx, env) {
                    Ok(true)
                } else {
                    self.input_has_shared_storage(*pointee, depth + 1)
                }
            }
            ty::Pat(base, _) | ty::Array(base, _) => {
                self.input_has_shared_storage(*base, depth + 1)
            }
            ty::Tuple(types) => {
                for ty in types.iter() {
                    if self.input_has_shared_storage(ty, depth + 1)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            ty::Adt(def, args) => {
                for variant in def.variants() {
                    for field in &variant.fields {
                        let ty = self
                            .tcx
                            .try_normalize_erasing_regions(env, field.ty(self.tcx, args))
                            .map_err(|error| {
                                format!("shared input field normalization failed: {error:?}")
                            })?;
                        if self.input_has_shared_storage(ty, depth + 1)? {
                            return Ok(true);
                        }
                    }
                }
                Ok(false)
            }
            _ => Ok(false),
        }
    }

    pub(super) fn retain_shared_input_storage(
        &self,
        ty: Ty<'tcx>,
        value: Value,
        memory: &mut Memory,
        depth: usize,
    ) -> Result<Value, String> {
        if !self.input_has_shared_storage(ty, depth)? {
            return Ok(value);
        }
        if depth >= 16 {
            return Err("shared input reference nesting exceeds the depth budget".into());
        }
        let env = ty::TypingEnv::fully_monomorphized();
        if let ty::Ref(_, pointee, mutability) = ty.kind()
            && !mutability.is_mut()
        {
            if !pointee.is_freeze(self.tcx, env) {
                if !memory.is_empty() {
                    return Err(
                        "multiple interior/mutable root locations need alias constraints".into(),
                    );
                }
                // The incoming lifetime belongs to the root's environment, not its frame.
                // Retain identity without authorizing ordinary writes to shared storage.
                memory.push(Some(value));
                return Ok(Value::Reference {
                    allocation: 0,
                    projection: Vec::new(),
                    mutable: false,
                });
            }
            return self.retain_shared_input_storage(*pointee, value, memory, depth + 1);
        }
        let value = value.materialize()?;
        match (ty.kind(), value) {
            (ty::Pat(base, _), value) => {
                self.retain_shared_input_storage(*base, value, memory, depth + 1)
            }
            (ty::Tuple(types), Value::Tuple(fields)) => {
                if types.len() != fields.len() {
                    return Err("shared input tuple field shape mismatch".into());
                }
                let fields = types
                    .iter()
                    .zip(fields)
                    .map(|(ty, value)| {
                        self.retain_shared_input_storage(ty, value, memory, depth + 1)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::Tuple(fields))
            }
            (ty::Array(element, _), Value::Elements(fields)) => {
                let fields = fields
                    .into_iter()
                    .map(|value| {
                        self.retain_shared_input_storage(*element, value, memory, depth + 1)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::Elements(fields.into()))
            }
            (
                ty::Adt(def, args),
                Value::Adt {
                    name,
                    variant,
                    is_option,
                    discriminant,
                    fields,
                },
            ) => {
                let compiler_fields = &def
                    .variants()
                    .get(rustc_abi::VariantIdx::from_usize(variant))
                    .ok_or("shared input aggregate variant mismatch")?
                    .fields;
                if name != self.tcx.def_path_str(def.did()) || compiler_fields.len() != fields.len()
                {
                    return Err("shared input aggregate field shape mismatch".into());
                }
                let fields = compiler_fields
                    .iter()
                    .zip(fields.iter())
                    .map(|(field, (name, value))| {
                        if field.name.as_str() != name {
                            return Err("shared input aggregate field identity mismatch".into());
                        }
                        let ty = self
                            .tcx
                            .try_normalize_erasing_regions(env, field.ty(self.tcx, args))
                            .map_err(|error| {
                                format!("shared input field normalization failed: {error:?}")
                            })?;
                        let value =
                            self.retain_shared_input_storage(ty, value.clone(), memory, depth + 1)?;
                        Ok((name.clone(), value))
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                Ok(Value::Adt {
                    name,
                    variant,
                    is_option,
                    discriminant,
                    fields: fields.into(),
                })
            }
            (
                ty::Adt(def, _),
                Value::Enum {
                    discriminant,
                    variants,
                    is_option,
                },
            ) if def.is_enum() => {
                let variants = variants
                    .into_iter()
                    .map(|value| self.retain_shared_input_storage(ty, value, memory, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Value::Enum {
                    discriminant,
                    variants,
                    is_option,
                })
            }
            (_, _) => Err("shared input reference has an unsupported typed value shape".into()),
        }
    }
}
