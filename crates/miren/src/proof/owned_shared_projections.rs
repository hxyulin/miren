//! Compiler evidence for retained shared projections; allocation access remains separate.
use super::*;
use memory::MAX_ALLOCATIONS;
use storage_locations::StorageLocation;
use symbolic::MemoryProjection;
use typed_array_choices::{MAX_CHOICE_DEPTH, MAX_CHOICE_NODES};

#[derive(Clone, Debug)]
pub(super) struct OwnedProjectionCertificate<'tcx> {
    pub(super) original: Ty<'tcx>,
    pub(super) fields: Vec<usize>,
    pub(super) drop_shared: Option<drop_shared_projections::Witness<'tcx>>,
}

impl<'tcx> Engine<'tcx> {
    fn owned_projection_certificate(
        &mut self,
        original: Ty<'tcx>,
        fields: Vec<usize>,
    ) -> Result<usize, String> {
        validate_projection_prefix(&fields)?;
        let certificate = OwnedProjectionCertificate {
            original,
            fields,
            drop_shared: None,
        };
        if let Some(id) = self
            .owned_projection_certificates
            .iter()
            .position(|issued| {
                issued.drop_shared.is_none()
                    && issued.original == certificate.original
                    && issued.fields == certificate.fields
            })
        {
            return Ok(id);
        }
        if self.owned_projection_certificates.len() >= MAX_CHOICE_NODES {
            return Err("typed owned projection certificate budget exceeded".into());
        }
        let id = self.owned_projection_certificates.len();
        self.owned_projection_certificates.push(certificate);
        Ok(id)
    }

    pub(super) fn read_typed_owned_projection(
        &self,
        certificate: usize,
        value: Value,
        index: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let certificate = self
            .owned_projection_certificates
            .get(certificate)
            .ok_or("typed owned projection has no compiler certificate")?;
        if certificate.drop_shared.is_some() {
            return Err("shared Drop projection cannot materialize a non-Copy owner".into());
        }
        // Keep prior direct-array reads, including their query construction, unchanged.
        if certificate.fields.is_empty() {
            return self.read_typed_owned_index(certificate.original, value, index, conditions);
        }
        validate_projection_prefix(&certificate.fields)?;
        if !matches!(certificate.original.kind(), ty::Tuple(_) | ty::Adt(..)) {
            return Err("typed field projection lacks original compiler product".into());
        }
        let shape = self
            .owned_product_shape(certificate.original)?
            .ok_or("typed field projection requires a pure original compiler root")?;
        let mut value = self.prepare_typed_product(certificate.original, &shape, &value, 0)?;
        self.validate_owned_product(certificate.original, &value, conditions)?;
        let mut original = certificate.original;
        for field in &certificate.fields {
            let child = self.owned_projection_field_type(original, *field)?;
            value = self.memory_projection(value, &MemoryProjection::Field(*field), conditions)?;
            original = child;
        }
        self.read_typed_owned_index(original, value, index, conditions)
    }

    fn owned_projection_field_type(
        &self,
        original: Ty<'tcx>,
        field: usize,
    ) -> Result<Ty<'tcx>, String> {
        match original.kind() {
            ty::Tuple(fields) => {
                validate_projection_field(field, fields.len())?;
                fields.get(field).copied()
            }
            ty::Adt(def, args) if self.plain_composite_struct(*def) => {
                let fields = &def.non_enum_variant().fields;
                validate_projection_field(field, fields.len())?;
                fields
                    .get(rustc_abi::FieldIdx::from_usize(field))
                    .map(|field| field.ty(self.tcx, args).skip_norm_wip())
            }
            _ => None,
        }
        .ok_or_else(|| "typed owned projection field has no original compiler identity".into())
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

    pub(super) fn borrow_typed_owned_projection(
        &mut self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let local = place.local.as_usize();
        let original = body.local_decls[place.local].ty;
        let field_root = matches!(original.kind(), ty::Tuple(_) | ty::Adt(..))
            && matches!(place.projection.first(), Some(ProjectionElem::Field(..)))
            && place
                .projection
                .iter()
                .any(|part| matches!(part, ProjectionElem::Index(_)));
        let array_root = matches!(original.kind(), ty::Array(..))
            && matches!(place.projection.first(), Some(ProjectionElem::Index(_)));
        if (!array_root && !field_root)
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
        let mut value = if field_root {
            let shape = self
                .owned_product_shape(original)?
                .ok_or("typed field borrow requires an original pure product")?;
            self.prepare_typed_product(original, &shape, &source, 0)?
        } else {
            source.clone()
        };
        let mut ty = original;
        let mut path = Vec::new();
        let mut leading_fields = Vec::new();
        let mut before_index = field_root;
        for part in place.projection {
            match part {
                ProjectionElem::Index(index) => {
                    if body.local_decls[index].ty != self.tcx.types.usize {
                        return Err("typed owned borrow index lacks compiler usize type".into());
                    }
                    let index = self.local(state, index.as_usize())?;
                    value = self.read_typed_owned_index(ty, value, &index, &state.conditions)?;
                    let certificate = if before_index {
                        self.owned_projection_certificate(original, leading_fields.clone())?
                    } else {
                        self.owned_projection_certificate(ty, Vec::new())?
                    };
                    before_index = false;
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
                    let certificate = if before_index {
                        self.owned_projection_certificate(original, leading_fields.clone())?
                    } else {
                        self.owned_projection_certificate(ty, Vec::new())?
                    };
                    before_index = false;
                    ty = *inner;
                    path.push(MemoryProjection::TypedIndex {
                        index: Box::new(index),
                        certificate,
                    });
                }
                ProjectionElem::Field(index, recorded) => {
                    let child = self.owned_projection_field_type(ty, index.as_usize())?;
                    if child != recorded {
                        return Err("typed owned field differs from compiler type".into());
                    }
                    let projection = MemoryProjection::Field(index.as_usize());
                    value = self.memory_projection(value, &projection, &state.conditions)?;
                    ty = child;
                    if before_index {
                        leading_fields.push(index.as_usize());
                        validate_projection_prefix(&leading_fields)?;
                    } else {
                        path.push(projection);
                    }
                }
                _ => return Ok(None),
            }
        }
        self.validate_owned_product(ty, &value, &state.conditions)?;
        let allocation = if let Some(allocation) = state.addresses[local] {
            StorageLocation::tracked(allocation, false).read(&state.memory)?;
            allocation
        } else {
            if state.memory.storage_slots() >= MAX_ALLOCATIONS {
                return Err("memory allocation budget reached".into());
            }
            let allocation = state.memory.len();
            state.memory.push(Some(source));
            state.addresses[local] = Some(allocation);
            allocation
        };
        let model = if field_root {
            "compiler-certified retained owned field-array shared projection"
        } else {
            "compiler-certified retained owned array shared projection"
        }
        .to_owned();
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

fn validate_projection_prefix(fields: &[usize]) -> Result<(), String> {
    if fields.len() > MAX_CHOICE_DEPTH {
        return Err("typed owned field prefix exceeds its depth budget".into());
    }
    Ok(())
}

fn validate_projection_field(field: usize, count: usize) -> Result<(), String> {
    if count > MAX_CHOICE_NODES || field >= count {
        return Err("typed owned projection field exceeds its compiler inventory".into());
    }
    Ok(())
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

    #[test]
    fn retained_field_metadata_checks_full_inventory_and_prefix_budget() {
        validate_projection_field(0, 1).unwrap();
        validate_projection_field(3, 4).unwrap();
        for (field, count) in [(0, 0), (4, 4), (usize::MAX, 4), (0, MAX_CHOICE_NODES + 1)] {
            assert!(validate_projection_field(field, count).is_err());
        }
        validate_projection_prefix(&[]).unwrap();
        validate_projection_prefix(&[0; MAX_CHOICE_DEPTH]).unwrap();
        assert!(validate_projection_prefix(&[0; MAX_CHOICE_DEPTH + 1]).is_err());
    }
}
