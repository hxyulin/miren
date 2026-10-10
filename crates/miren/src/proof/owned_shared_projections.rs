//! Compiler evidence for retained shared projections; allocation access remains separate.
use super::*;
use memory::MAX_ALLOCATIONS;
use storage_locations::StorageLocation;
use symbolic::MemoryProjection;
use typed_array_choices::MAX_CHOICE_NODES;

impl<'tcx> Engine<'tcx> {
    pub(super) fn owned_array_projection_type(
        &self,
        certificate: usize,
    ) -> Result<Ty<'tcx>, String> {
        self.owned_array_projection_types
            .get(certificate)
            .copied()
            .ok_or_else(|| "typed owned projection has no compiler certificate".into())
    }

    fn owned_array_projection_certificate(&mut self, original: Ty<'tcx>) -> Result<usize, String> {
        if let Some(id) = self
            .owned_array_projection_types
            .iter()
            .position(|ty| *ty == original)
        {
            return Ok(id);
        }
        if self.owned_array_projection_types.len() >= MAX_CHOICE_NODES {
            return Err("typed owned projection certificate budget exceeded".into());
        }
        let id = self.owned_array_projection_types.len();
        self.owned_array_projection_types.push(original);
        Ok(id)
    }

    pub(super) fn read_typed_owned_index(
        &self,
        original: Ty<'tcx>,
        value: Value,
        index: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let ty::Array(_, count) = original.kind() else {
            return Err("typed owned projection requires original compiler array".into());
        };
        validate_projection_index(
            &self.terms,
            u32::from(self.tcx.sess.target.pointer_width),
            index,
        )?;
        let shape = self
            .owned_product_shape(original)?
            .ok_or("typed owned projection requires a pure original compiler array")?;
        let prepared = self.prepare_typed_product(original, &shape, &value, 0)?;
        self.validate_owned_product(original, &prepared, conditions)?;
        match prepared {
            Value::Elements(elements) => {
                if count.try_to_target_usize(self.tcx) != Some(elements.len() as u64) {
                    return Err(
                        "typed owned projection inventory differs from compiler length".into(),
                    );
                }
                self.fixed_element_with_type(&elements, index, conditions, Some(original))
            }
            value @ Value::Bytes { .. } => self.memory_projection(
                value,
                &MemoryProjection::Index(Box::new(index.clone())),
                conditions,
            ),
            _ => Err("typed owned projection source has no complete array storage".into()),
        }
    }

    pub(super) fn borrow_typed_owned_array(
        &mut self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let local = place.local.as_usize();
        let original = body.local_decls[place.local].ty;
        if !matches!(original.kind(), ty::Array(..))
            || !matches!(place.projection.first(), Some(ProjectionElem::Index(_)))
            || place.projection.iter().any(|part| {
                !matches!(
                    part,
                    ProjectionElem::Index(_)
                        | ProjectionElem::Field(..)
                        | ProjectionElem::ConstantIndex {
                            from_end: false,
                            ..
                        }
                )
            })
        {
            return Ok(None);
        }
        if self.owned_product_shape(original)?.is_none() {
            return Ok(None);
        }
        let source = self.local(state, local)?;
        self.validate_tracked_value(&source, state)?;
        self.validate_owned_product(original, &source, &state.conditions)?;
        let mut value = source.clone();
        let mut ty = original;
        let mut path = Vec::new();
        for part in place.projection {
            match part {
                ProjectionElem::Index(index) => {
                    if body.local_decls[index].ty != self.tcx.types.usize {
                        return Err("typed owned borrow index lacks compiler usize type".into());
                    }
                    let index = self.local(state, index.as_usize())?;
                    value = self.read_typed_owned_index(ty, value, &index, &state.conditions)?;
                    let certificate = self.owned_array_projection_certificate(ty)?;
                    let ty::Array(inner, _) = ty.kind() else {
                        unreachable!();
                    };
                    ty = *inner;
                    path.push(MemoryProjection::TypedIndex {
                        index: Box::new(index),
                        certificate,
                    });
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end: false,
                } => {
                    let ty::Array(inner, count) = ty.kind() else {
                        return Err("typed owned constant projection lacks original array".into());
                    };
                    let count = count
                        .try_to_target_usize(self.tcx)
                        .ok_or("typed owned constant projection lacks compiler count")?;
                    if min_length > count || offset >= count {
                        return Err(
                            "typed owned constant projection is outside compiler extent".into()
                        );
                    }
                    let index = symbolic::integer(
                        &self.terms,
                        u128::from(offset),
                        u32::from(self.tcx.sess.target.pointer_width),
                        false,
                    );
                    value = self.read_typed_owned_index(ty, value, &index, &state.conditions)?;
                    let certificate = self.owned_array_projection_certificate(ty)?;
                    ty = *inner;
                    path.push(MemoryProjection::TypedIndex {
                        index: Box::new(index),
                        certificate,
                    });
                }
                ProjectionElem::Field(index, recorded) => {
                    let child = match ty.kind() {
                        ty::Tuple(fields) => fields.get(index.as_usize()).copied(),
                        ty::Adt(def, args) if self.plain_composite_struct(*def) => def
                            .non_enum_variant()
                            .fields
                            .get(index)
                            .map(|field| field.ty(self.tcx, args).skip_norm_wip()),
                        _ => None,
                    }
                    .ok_or("typed owned projection field has no original compiler identity")?;
                    if child != recorded {
                        return Err("typed owned field differs from compiler type".into());
                    }
                    let projection = MemoryProjection::Field(index.as_usize());
                    value = self.memory_projection(value, &projection, &state.conditions)?;
                    ty = child;
                    path.push(projection);
                }
                _ => return Ok(None),
            }
        }
        self.validate_owned_product(ty, &value, &state.conditions)?;
        let allocation = if let Some(allocation) = state.addresses[local] {
            StorageLocation::tracked(allocation, false).read(&state.memory)?;
            allocation
        } else {
            if state.memory.len() >= MAX_ALLOCATIONS {
                return Err("memory allocation budget reached".into());
            }
            let allocation = state.memory.len();
            state.memory.push(Some(source));
            state.addresses[local] = Some(allocation);
            allocation
        };
        let model = "compiler-certified retained owned array shared projection".to_owned();
        if !self.proof.models.contains(&model) {
            self.proof.models.push(model);
        }
        Ok(Some(Value::Reference {
            allocation,
            projection: path,
            mutable: false,
        }))
    }
}

fn validate_projection_index(
    context: &Context,
    pointer_bits: u32,
    index: &Value,
) -> Result<(), String> {
    let (term, bits, signed) = index.integer()?;
    if signed
        || bits != pointer_bits
        || term.sort() != &Sort::BitVec(bits)
        || !term.belongs_to(context)
    {
        return Err("typed owned projection index requires exact target usize".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_index_requires_target_width_unsigned_current_context() {
        let context = Context::default();
        let foreign = Context::default();
        let index = symbolic::integer(&context, 1, 32, false);
        validate_projection_index(&context, 32, &index).unwrap();
        assert!(validate_projection_index(&context, 64, &index).is_err());
        assert!(validate_projection_index(&foreign, 32, &index).is_err());
        let signed = symbolic::integer(&context, 1, 32, true);
        assert!(validate_projection_index(&context, 32, &signed).is_err());
        let forged = Value::Int {
            expression: context.boolean(true),
            bits: 32,
            signed: false,
        };
        assert!(validate_projection_index(&context, 32, &forged).is_err());
        assert!(validate_projection_index(&context, 32, &Value::Unit).is_err());
    }
}
