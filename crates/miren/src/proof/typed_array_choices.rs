//! Owned finite choices and whole-element writes certified by actual MIR array types.
use super::*;
use call_destinations::CapturedDestinationIndices;
use composite_slices::CompositeShape;
use storage_locations::StorageLocation;
use symbolic::ScalarSliceElement;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum OwnedChoiceShape {
    Primitive(ScalarSliceElement),
    Tuple(Vec<OwnedChoiceShape>),
    Array(Vec<OwnedChoiceShape>),
    Struct {
        name: String,
        fields: Vec<(String, OwnedChoiceShape)>,
    },
    ByteArray(usize),
}

struct ProductPathTarget<'tcx> {
    original: Ty<'tcx>,
    shape: OwnedChoiceShape,
    span: std::ops::Range<usize>,
}

enum ProductWritePlan<'tcx> {
    Single(ProductPathTarget<'tcx>),
    Indexed {
        index: Term,
        targets: Vec<ProductPathTarget<'tcx>>,
    },
}

#[derive(Clone, Copy)]
enum OwnedWriteMode {
    Nonunique,
    Known,
}

struct ProductUpdate<'a> {
    span: std::ops::Range<usize>,
    leaves: &'a [Value],
}

pub(super) const MAX_CHOICE_NODES: usize = 512;
pub(super) const MAX_CHOICE_DEPTH: usize = 16;

pub(super) fn known_owned_write_frontier(error: &str) -> bool {
    matches!(
        error,
        "non-scalar array index is not uniquely determined on this path"
            | "array write index is not uniquely determined"
    )
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn typed_owned_array_choice(
        &self,
        original: Ty<'tcx>,
        elements: &[Value],
        index: &Value,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        let ty::Array(element, count) = original.kind() else {
            return Ok(None);
        };
        if count.try_to_target_usize(self.tcx) != Some(elements.len() as u64) {
            return Err("typed struct array choice inventory differs from compiler length".into());
        }
        let Some(shape) = self.owned_product_shape(*element)? else {
            return Ok(None);
        };
        if !contains_owned_choice(&shape)
            && !(matches!(element.kind(), ty::Tuple(_) | ty::Array(..))
                && contains_deferred_product(elements)?)
        {
            return Ok(None);
        }
        let (term, bits, signed) = index.integer()?;
        if signed
            || bits != u32::from(self.tcx.sess.target.pointer_width)
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
        {
            return Err("typed struct array choice requires exact target usize".into());
        }
        let mut columns: Vec<Vec<Value>> = Vec::new();
        let mut nodes = 0;
        for value in elements {
            let mut leaves = Vec::new();
            let value = self.prepare_typed_product(*element, &shape, value, nodes)?;
            flatten(
                &self.terms,
                bits,
                &shape,
                &value,
                0,
                &mut nodes,
                &mut leaves,
            )?;
            for (position, (kind, leaf)) in leaves.into_iter().enumerate() {
                if kind == ScalarSliceElement::Char {
                    self.prove_char_value(&leaf, conditions)?;
                }
                if columns.len() <= position {
                    columns.push(Vec::new());
                }
                columns[position].push(leaf);
            }
        }
        let selected = columns
            .iter()
            .map(|values| symbolic::select_element(&self.terms, values, index))
            .collect::<Result<Vec<_>, _>>()?;
        let mut cursor = 0;
        let result = rebuild(&self.terms, bits, &shape, &selected, &mut cursor)?;
        if cursor != selected.len() {
            return Err("typed struct array choice omitted leaf values".into());
        }
        Ok(Some(result))
    }
    pub(super) fn validate_owned_product(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let shape = self.owned_product_shape(original)?.ok_or_else(|| {
            self.categorized_error(
                UnknownCategory::Semantics,
                "sized alignment requires an exact primitive or pure owned product".into(),
            )
        })?;
        let mut nodes = 0;
        self.product_leaves(
            original,
            u32::from(self.tcx.sess.target.pointer_width),
            &shape,
            value,
            conditions,
            &mut nodes,
        )?;
        Ok(())
    }

    pub(super) fn validate_owned_product_update(
        &self,
        original: Ty<'tcx>,
        storage: &Value,
        target: Ty<'tcx>,
        replacement: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let original_shape = self
            .owned_product_shape(original)?
            .ok_or("captured store requires a complete pure owned root type")?;
        let target_shape = self
            .owned_product_shape(target)?
            .ok_or("captured store requires a pure original replacement type")?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let mut nodes = 0;
        self.product_leaves(
            original,
            bits,
            &original_shape,
            storage,
            conditions,
            &mut nodes,
        )?;
        self.product_leaves(
            target,
            bits,
            &target_shape,
            replacement,
            conditions,
            &mut nodes,
        )?;
        Ok(())
    }

    pub(super) fn owned_product_shape(
        &self,
        original: Ty<'tcx>,
    ) -> Result<Option<OwnedChoiceShape>, String> {
        if let Some(kind) = self.scalar_slice_element(original)? {
            return Ok(Some(OwnedChoiceShape::Primitive(kind)));
        }
        self.owned_struct_choice_shape(original)?
            .map(|shape| self.annotate_owned_shape(original, &shape))
            .transpose()
    }

    pub(super) fn write_owned_array_element(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        replacement: &Value,
        indices: Option<&CapturedDestinationIndices>,
    ) -> Result<bool, String> {
        self.write_owned_array_element_mode(
            body,
            state,
            place,
            replacement,
            indices,
            OwnedWriteMode::Nonunique,
        )
    }

    pub(super) fn known_owned_array_write_candidate(
        &self,
        body: &Body<'tcx>,
        place: Place<'tcx>,
    ) -> bool {
        matches!(body.local_decls[place.local].ty.kind(), ty::Array(..))
            && matches!(
                place.projection.first(),
                Some(
                    ProjectionElem::Index(_)
                        | ProjectionElem::ConstantIndex {
                            from_end: false,
                            ..
                        }
                )
            )
            && place.projection.iter().skip(1).all(|part| {
                matches!(
                    part,
                    ProjectionElem::Field(..)
                        | ProjectionElem::Index(_)
                        | ProjectionElem::ConstantIndex {
                            from_end: false,
                            ..
                        }
                )
            })
            && place
                .projection
                .iter()
                .skip(1)
                .any(|part| matches!(part, ProjectionElem::Index(_)))
    }

    pub(super) fn write_known_owned_array_element(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        replacement: &Value,
        indices: Option<&CapturedDestinationIndices>,
    ) -> Result<bool, String> {
        self.write_owned_array_element_mode(
            body,
            state,
            place,
            replacement,
            indices,
            OwnedWriteMode::Known,
        )
    }

    pub(super) fn owned_field_array_write_candidate(
        &self,
        body: &Body<'tcx>,
        place: Place<'tcx>,
    ) -> bool {
        matches!(
            body.local_decls[place.local].ty.kind(),
            ty::Tuple(_) | ty::Adt(..)
        ) && matches!(place.projection.first(), Some(ProjectionElem::Field(..)))
            && place.projection.iter().all(|part| {
                matches!(
                    part,
                    ProjectionElem::Field(..)
                        | ProjectionElem::Index(_)
                        | ProjectionElem::ConstantIndex {
                            from_end: false,
                            ..
                        }
                )
            })
            && place
                .projection
                .iter()
                .any(|part| matches!(part, ProjectionElem::Index(_)))
    }

    pub(super) fn write_owned_field_array(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        replacement: &Value,
        indices: Option<&CapturedDestinationIndices>,
    ) -> Result<bool, String> {
        if !self.owned_field_array_write_candidate(body, place) {
            return Ok(false);
        }
        let original = body.local_decls[place.local].ty;
        let Some(shape) = self.owned_product_shape(original)? else {
            return Ok(false);
        };
        let Some(ProductWritePlan::Indexed { index, targets }) = self.owned_product_write_plan(
            body,
            state,
            original,
            &shape,
            place.projection,
            indices,
        )?
        else {
            return Ok(false);
        };
        let target = targets
            .first()
            .ok_or("owned indexed write has no feasible target")?;
        let local = place.local.as_usize();
        let allocation = state.addresses[local];
        let storage = if let Some(allocation) = allocation {
            let location = StorageLocation::tracked(allocation, true);
            location.require_write(&state.memory)?;
            location.read(&state.memory)?.clone()
        } else {
            self.local(state, local)?
        };
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let mut nodes = 0;
        let replacement = self
            .product_leaves(
                target.original,
                bits,
                &target.shape,
                replacement,
                &state.conditions,
                &mut nodes,
            )
            .map_err(|error| format!("owned product write replacement: {error}"))?;
        let old = self
            .product_leaves(
                original,
                bits,
                &shape,
                &storage,
                &state.conditions,
                &mut nodes,
            )
            .map_err(|error| format!("owned product write parent: {error}"))?;
        let spans = targets
            .iter()
            .map(|target| target.span.clone())
            .collect::<Vec<_>>();
        let masks = indexed_product_masks(&self.terms, bits, &index, &spans)?;
        let updated =
            conditional_indexed_product(&self.terms, bits, &shape, &masks, &replacement, &old)?;
        if let Some(allocation) = allocation {
            state.memory[allocation] = Some(updated);
        } else {
            state.locals[local] = Some(updated);
        }
        Ok(true)
    }

    fn write_owned_array_element_mode(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        replacement: &Value,
        indices: Option<&CapturedDestinationIndices>,
        mode: OwnedWriteMode,
    ) -> Result<bool, String> {
        let Some((outer, fields)) = place.projection.split_first() else {
            return Ok(false);
        };
        if !matches!(outer, ProjectionElem::Index(_))
            && !matches!(
                (mode, outer),
                (
                    OwnedWriteMode::Known,
                    ProjectionElem::ConstantIndex {
                        from_end: false,
                        ..
                    }
                )
            )
        {
            return Ok(false);
        }
        if fields.iter().any(|field| {
            !matches!(
                field,
                ProjectionElem::Field(..)
                    | ProjectionElem::Index(..)
                    | ProjectionElem::ConstantIndex { .. }
            )
        }) {
            return Ok(false);
        }
        let original = body.local_decls[place.local].ty;
        let ty::Array(element, count) = original.kind() else {
            return Ok(false);
        };
        let local = place.local.as_usize();
        let allocation = state.addresses[local];
        let storage = if let Some(allocation) = allocation {
            let location = StorageLocation::tracked(allocation, true);
            location.require_write(&state.memory)?;
            location.read(&state.memory)?.clone()
        } else {
            self.local(state, local)?
        };
        let storage = match mode {
            OwnedWriteMode::Nonunique => storage,
            OwnedWriteMode::Known => {
                let Some(parent_shape) = self.owned_product_shape(original)? else {
                    return Ok(false);
                };
                self.prepare_typed_product(original, &parent_shape, &storage, 0)?
            }
        };
        let Value::Elements(elements) = storage.materialize()? else {
            return Ok(false);
        };
        if count.try_to_target_usize(self.tcx) != Some(elements.len() as u64) {
            return Err("owned array write inventory differs from compiler length".into());
        }
        let index = match outer {
            ProjectionElem::Index(index_local) => {
                if matches!(mode, OwnedWriteMode::Known)
                    && body.local_decls[*index_local].ty != self.tcx.types.usize
                {
                    return Err("known owned outer index requires compiler usize".into());
                }
                self.destination_index(state, *index_local, indices)?
            }
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end: false,
            } => {
                let position = usize::try_from(*offset)
                    .map_err(|_| "known owned constant index exceeds host capacity")?;
                checked_fixed_index(elements.len() as u64, position, Some(*min_length))?;
                symbolic::integer(
                    &self.terms,
                    u128::from(*offset),
                    u32::from(self.tcx.sess.target.pointer_width),
                    false,
                )
            }
            _ => return Ok(false),
        };
        let (term, bits, signed) = index.integer()?;
        if signed
            || bits != u32::from(self.tcx.sess.target.pointer_width)
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
        {
            return Err("owned array write requires exact target usize".into());
        }
        // The existing nonunique writer still leaves known stores to the old writer.
        let constant = symbolic::constant(&term);
        let mut known = constant.is_some();
        let mut known_position = match constant {
            Some(symbolic::Constant::BitVec { value, .. }) => usize::try_from(value)
                .ok()
                .filter(|position| *position < elements.len()),
            _ => None,
        };
        if known && matches!(mode, OwnedWriteMode::Nonunique) {
            return Ok(false);
        }
        if !known {
            for position in 0..elements.len() {
                let equal = self.terms.apply(
                    Op::Equal,
                    &[term.clone(), self.terms.bit_vector(position as u128, bits)?],
                )?;
                if !self
                    .feasible(&[state.conditions.clone(), vec![symbolic::not(&equal)]].concat())?
                {
                    known = true;
                    known_position = Some(position);
                    break;
                }
            }
        }
        match (mode, known) {
            (OwnedWriteMode::Nonunique, true) | (OwnedWriteMode::Known, false) => return Ok(false),
            (OwnedWriteMode::Nonunique, false) | (OwnedWriteMode::Known, true) => {}
        }
        let Some(shape) = self.owned_product_shape(*element)? else {
            return Ok(false);
        };
        let Some(plan) =
            self.owned_product_write_plan(body, state, *element, &shape, fields, indices)?
        else {
            return Ok(false);
        };
        if matches!(mode, OwnedWriteMode::Known)
            && !matches!(plan, ProductWritePlan::Indexed { .. })
        {
            return Ok(false);
        }
        self.memory_bounds(
            &index,
            &symbolic::integer(&self.terms, elements.len() as u128, bits, false),
            &state.conditions,
        )?;
        let target = match &plan {
            ProductWritePlan::Single(target) => target,
            ProductWritePlan::Indexed { targets, .. } => {
                if elements
                    .len()
                    .checked_mul(targets.len())
                    .is_none_or(|work| work > MAX_CHOICE_NODES)
                {
                    return Err("owned indexed write exceeds its expanded node budget".into());
                }
                targets
                    .first()
                    .ok_or("owned indexed write has no feasible target")?
            }
        };
        let mut nodes = 0;
        let replacement = self
            .product_leaves(
                target.original,
                bits,
                &target.shape,
                replacement,
                &state.conditions,
                &mut nodes,
            )
            .map_err(|error| format!("owned array write replacement: {error}"))?;
        let mut updated = Vec::new();
        for (position, value) in elements.iter().enumerate() {
            let old = self
                .product_leaves(*element, bits, &shape, value, &state.conditions, &mut nodes)
                .map_err(|error| format!("owned array write candidate {position}: {error}"))?;
            let Some(condition) =
                owned_row_condition(&self.terms, &term, bits, position, known_position, mode)?
            else {
                updated.push(value.clone());
                continue;
            };
            updated.push(match &plan {
                ProductWritePlan::Indexed { index, targets } => {
                    let masks = targets
                        .iter()
                        .enumerate()
                        .map(|(position, target)| {
                            let equal = self.terms.apply(
                                Op::Equal,
                                &[
                                    index.clone(),
                                    self.terms.bit_vector(position as u128, bits)?,
                                ],
                            )?;
                            let mask = self.terms.apply(Op::And, &[condition.clone(), equal])?;
                            Ok((target.span.clone(), mask))
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    conditional_indexed_product(
                        &self.terms,
                        bits,
                        &shape,
                        &masks,
                        &replacement,
                        &old,
                    )?
                }
                ProductWritePlan::Single(_) if fields.is_empty() => {
                    conditional_product(&self.terms, bits, &shape, &condition, &replacement, &old)?
                }
                ProductWritePlan::Single(target) => conditional_product_field(
                    &self.terms,
                    bits,
                    &shape,
                    &condition,
                    ProductUpdate {
                        span: target.span.clone(),
                        leaves: &replacement,
                    },
                    &old,
                )?,
            });
        }
        let updated = Value::Elements(updated.into());
        if let Some(allocation) = allocation {
            state.memory[allocation] = Some(updated);
        } else {
            state.locals[local] = Some(updated);
        }
        Ok(true)
    }

    fn owned_product_write_plan(
        &self,
        body: &Body<'tcx>,
        state: &State,
        original: Ty<'tcx>,
        shape: &OwnedChoiceShape,
        projections: &[rustc_middle::mir::PlaceElem<'tcx>],
        indices: Option<&CapturedDestinationIndices>,
    ) -> Result<Option<ProductWritePlan<'tcx>>, String> {
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for (position, projection) in projections.iter().enumerate() {
            let ProjectionElem::Index(local) = projection else {
                continue;
            };
            if body.local_decls[*local].ty != self.tcx.types.usize {
                return Err("owned nested array index requires compiler usize".into());
            }
            let value = self.destination_index(state, *local, indices)?;
            if fixed_index_value(&self.terms, &value, bits)?.is_some() {
                continue;
            }
            let Some(prefix) = self.owned_product_path_target(
                body,
                state,
                original,
                shape,
                &projections[..position],
                indices,
            )?
            else {
                return Ok(None);
            };
            let ty::Array(_, count) = prefix.original.kind() else {
                return Err("owned symbolic nested index requires original fixed array".into());
            };
            let count = count
                .try_to_target_usize(self.tcx)
                .ok_or("owned symbolic nested array requires compiler length")?;
            let count = usize::try_from(count)
                .map_err(|_| "owned symbolic nested length exceeds host capacity")?;
            if count > MAX_CHOICE_NODES {
                return Err("owned indexed targets exceed their node budget".into());
            }
            self.memory_bounds(
                &value,
                &symbolic::integer(&self.terms, count as u128, bits, false),
                &state.conditions,
            )?;
            let mut targets: Vec<ProductPathTarget<'tcx>> = Vec::new();
            for index in 0..count {
                let (child_ty, child_shape, offset) =
                    self.owned_product_array_target(prefix.original, &prefix.shape, index, None)?;
                let Some(mut target) = self.owned_product_path_target(
                    body,
                    state,
                    child_ty,
                    &child_shape,
                    &projections[position + 1..],
                    indices,
                )?
                else {
                    return Ok(None);
                };
                if targets.first().is_some_and(|first| {
                    first.original != target.original || first.shape != target.shape
                }) {
                    return Err("owned indexed targets differ in original type or shape".into());
                }
                let offset = prefix
                    .span
                    .start
                    .checked_add(offset)
                    .ok_or("owned indexed target offset overflow")?;
                target.span.start = target
                    .span
                    .start
                    .checked_add(offset)
                    .ok_or("owned indexed target offset overflow")?;
                target.span.end = target
                    .span
                    .end
                    .checked_add(offset)
                    .ok_or("owned indexed target extent overflow")?;
                targets.push(target);
            }
            let leaves = targets
                .first()
                .map(|target| product_leaf_count(&target.shape))
                .transpose()?
                .unwrap_or(0);
            validate_indexed_spans(
                &targets
                    .iter()
                    .map(|target| target.span.clone())
                    .collect::<Vec<_>>(),
                product_leaf_count(shape)?,
                leaves,
            )?;
            return Ok(Some(ProductWritePlan::Indexed {
                index: value.integer()?.0,
                targets,
            }));
        }
        Ok(self
            .owned_product_path_target(body, state, original, shape, projections, indices)?
            .map(ProductWritePlan::Single))
    }

    fn owned_product_path_target(
        &self,
        body: &Body<'tcx>,
        state: &State,
        mut original: Ty<'tcx>,
        shape: &OwnedChoiceShape,
        projections: &[rustc_middle::mir::PlaceElem<'tcx>],
        indices: Option<&CapturedDestinationIndices>,
    ) -> Result<Option<ProductPathTarget<'tcx>>, String> {
        let mut shape = shape.clone();
        let mut start = 0_usize;
        for projection in projections {
            let (child_ty, child, offset) = match projection {
                ProjectionElem::Field(index, recorded) => {
                    let index = index.as_usize();
                    let child_ty = match (original.kind(), &shape) {
                        (ty::Tuple(types), OwnedChoiceShape::Tuple(children))
                            if types.len() == children.len() =>
                        {
                            let ty = types
                                .get(index)
                                .ok_or("owned tuple field index is invalid")?;
                            *ty
                        }
                        (ty::Adt(def, args), OwnedChoiceShape::Struct { name, fields })
                            if self.plain_composite_struct(*def)
                                && self.tcx.def_path_str(def.did()) == *name
                                && def.non_enum_variant().fields.len() == fields.len() =>
                        {
                            let declared = &def.non_enum_variant().fields;
                            let field = declared
                                .get(rustc_abi::FieldIdx::from_usize(index))
                                .ok_or("owned struct field index is invalid")?;
                            for (field, (name, _)) in declared.iter().zip(fields) {
                                if field.name.as_str() != name {
                                    return Err("owned struct field identity mismatch".into());
                                }
                            }
                            field.ty(self.tcx, args).skip_norm_wip()
                        }
                        _ => {
                            return Err(
                                "owned field target differs from exact compiler product shape"
                                    .into(),
                            );
                        }
                    };
                    if child_ty != *recorded {
                        return Err(
                            "owned field target differs from original compiler field type".into(),
                        );
                    }

                    let (child, offset) = product_field(&shape, index)?;
                    (child_ty, child.clone(), offset)
                }
                ProjectionElem::Index(local) => {
                    if body.local_decls[*local].ty != self.tcx.types.usize {
                        return Err("owned nested array index requires compiler usize".into());
                    }
                    let value = self.destination_index(state, *local, indices)?;
                    let Some(index) = fixed_index_value(
                        &self.terms,
                        &value,
                        u32::from(self.tcx.sess.target.pointer_width),
                    )?
                    else {
                        return Ok(None);
                    };
                    self.owned_product_array_target(original, &shape, index, None)?
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => {
                    if *from_end {
                        return Ok(None);
                    }
                    let index = usize::try_from(*offset)
                        .map_err(|_| "owned nested array index exceeds host capacity")?;
                    self.owned_product_array_target(original, &shape, index, Some(*min_length))?
                }
                _ => return Ok(None),
            };
            start = start
                .checked_add(offset)
                .ok_or("owned product leaf offset overflow")?;
            shape = child;
            original = child_ty;
        }
        let end = start
            .checked_add(product_leaf_count(&shape)?)
            .ok_or("owned product leaf extent overflow")?;
        Ok(Some(ProductPathTarget {
            original,
            shape,
            span: start..end,
        }))
    }

    fn owned_product_array_target(
        &self,
        original: Ty<'tcx>,
        shape: &OwnedChoiceShape,
        index: usize,
        min_length: Option<u64>,
    ) -> Result<(Ty<'tcx>, OwnedChoiceShape, usize), String> {
        let ty::Array(inner, count) = original.kind() else {
            return Err("owned nested index requires original fixed array type".into());
        };
        let count = count
            .try_to_target_usize(self.tcx)
            .ok_or("owned nested array requires exact compiler length")?;
        checked_fixed_index(count, index, min_length)?;
        match shape {
            OwnedChoiceShape::Array(children) if children.len() as u64 == count => {
                let (child, offset) = product_array_child(children, index)?;
                Ok((*inner, child.clone(), offset))
            }
            OwnedChoiceShape::ByteArray(length)
                if *inner == self.tcx.types.u8 && *length as u64 == count =>
            {
                Ok((
                    *inner,
                    OwnedChoiceShape::Primitive(ScalarSliceElement::Integer {
                        bits: 8,
                        signed: false,
                    }),
                    index,
                ))
            }
            _ => Err("owned nested array differs from exact compiler product shape".into()),
        }
    }

    fn product_leaves(
        &self,
        original: Ty<'tcx>,
        bits: u32,
        shape: &OwnedChoiceShape,
        value: &Value,
        conditions: &[Term],
        nodes: &mut usize,
    ) -> Result<Vec<Value>, String> {
        let mut leaves = Vec::new();
        let value = self.prepare_typed_product(original, shape, value, *nodes)?;
        flatten(&self.terms, bits, shape, &value, 0, nodes, &mut leaves)?;
        leaves
            .into_iter()
            .map(|(kind, value)| {
                if kind == ScalarSliceElement::Char {
                    self.prove_char_value(&value, conditions)?;
                }
                Ok(value)
            })
            .collect()
    }

    fn annotate_owned_shape(
        &self,
        original: Ty<'tcx>,
        certified: &CompositeShape,
    ) -> Result<OwnedChoiceShape, String> {
        match (original.kind(), certified) {
            (ty::Array(element, count), CompositeShape::Array(fields)) => {
                let count = count
                    .try_to_target_usize(self.tcx)
                    .ok_or("owned array annotation requires concrete compiler count")?;
                if count != fields.len() as u64 {
                    return Err("owned array annotation differs from certified count".into());
                }
                if *element == self.tcx.types.u8 {
                    return certified_byte_array_annotation(count, fields);
                }
                Ok(OwnedChoiceShape::Array(
                    fields
                        .iter()
                        .map(|field| self.annotate_owned_shape(*element, field))
                        .collect::<Result<_, _>>()?,
                ))
            }
            (ty::Tuple(types), CompositeShape::Tuple(fields)) if types.len() == fields.len() => {
                Ok(OwnedChoiceShape::Tuple(
                    types
                        .iter()
                        .zip(fields)
                        .map(|(ty, field)| self.annotate_owned_shape(ty, field))
                        .collect::<Result<_, _>>()?,
                ))
            }
            (ty::Adt(def, args), CompositeShape::Struct { name, fields })
                if self.plain_composite_struct(*def)
                    && self.tcx.def_path_str(def.did()) == *name
                    && def.non_enum_variant().fields.len() == fields.len() =>
            {
                let fields = def
                    .non_enum_variant()
                    .fields
                    .iter()
                    .zip(fields)
                    .map(|(field, (name, shape))| {
                        if field.name.as_str() != name {
                            return Err("owned struct annotation field identity mismatch".into());
                        }
                        Ok((
                            name.clone(),
                            self.annotate_owned_shape(
                                field.ty(self.tcx, args).skip_norm_wip(),
                                shape,
                            )?,
                        ))
                    })
                    .collect::<Result<_, String>>()?;
                Ok(OwnedChoiceShape::Struct {
                    name: name.clone(),
                    fields,
                })
            }
            (_, CompositeShape::Primitive(kind))
                if self.scalar_slice_element(original)? == Some(*kind) =>
            {
                Ok(OwnedChoiceShape::Primitive(*kind))
            }
            _ => Err("owned choice annotation differs from original compiler type".into()),
        }
    }
}

// The caller first checks the ORIGINAL compiler array element is exactly core u8. In
// particular, an empty certified shape alone never supplies that element-type evidence.
fn certified_byte_array_annotation(
    count: u64,
    fields: &[CompositeShape],
) -> Result<OwnedChoiceShape, String> {
    if count != fields.len() as u64
        || fields.iter().any(|field| {
            !matches!(
                field,
                CompositeShape::Primitive(ScalarSliceElement::Integer {
                    bits: 8,
                    signed: false
                })
            )
        })
    {
        return Err("owned byte array annotation differs from certified primitive shape".into());
    }
    Ok(OwnedChoiceShape::ByteArray(fields.len()))
}

// This is only an eligibility hint. Preparation still certifies every complete candidate.
fn contains_deferred_product(values: &[Value]) -> Result<bool, String> {
    if values.len() > MAX_CHOICE_NODES {
        return Err("deferred candidate search exceeds its node budget".into());
    }
    let mut pending = values.iter().map(|value| (value, 0)).collect::<Vec<_>>();
    let mut nodes = 0_usize;
    while let Some((value, depth)) = pending.pop() {
        if depth >= MAX_CHOICE_DEPTH || nodes >= MAX_CHOICE_NODES {
            return Err("deferred candidate search exceeds its depth or node budget".into());
        }
        nodes += 1;
        let children: &[Value] = match value {
            Value::MutableU16 { .. } | Value::OwnedRegion { .. } | Value::OwnedSnapshot(_) => {
                return Ok(false);
            }
            Value::Input(_) => return Ok(true),
            Value::Tuple(children) => children,
            Value::Elements(children) => children,
            Value::Uninitialized
            | Value::MaybeUninit { .. }
            | Value::StaticSlice { .. }
            | Value::StaticView { .. }
            | Value::RawPointer { .. }
            | Value::TrackedPointer { .. }
            | Value::RawSlice { .. }
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::Bytes { .. }
            | Value::CompositeSlice { .. }
            | Value::ScalarSlice { .. }
            | Value::Adt { .. }
            | Value::Enum { .. }
            | Value::Cell { .. }
            | Value::Atomic { .. }
            | Value::LocalAtomic { .. }
            | Value::Reference { .. }
            | Value::SliceIterator { .. }
            | Value::MetadataPointer(_)
            | Value::TraitObject { .. }
            | Value::DebugReference { .. }
            | Value::StaticText
            | Value::FormatArguments
            | Value::FunctionPointer { .. }
            | Value::Function
            | Value::Unit => continue,
        };
        if children.len() > MAX_CHOICE_NODES.saturating_sub(nodes + pending.len()) {
            return Err("deferred candidate search exceeds its node budget".into());
        }
        pending.extend(children.iter().map(|child| (child, depth + 1)));
    }
    Ok(false)
}

fn contains_owned_choice(shape: &OwnedChoiceShape) -> bool {
    match shape {
        OwnedChoiceShape::Struct { .. } | OwnedChoiceShape::ByteArray(_) => true,
        OwnedChoiceShape::Tuple(fields) | OwnedChoiceShape::Array(fields) => {
            fields.iter().any(contains_owned_choice)
        }
        OwnedChoiceShape::Primitive(_) => false,
    }
}

fn validate_owned_bytes(
    context: &Context,
    pointer_bits: u32,
    count: usize,
    length: &Value,
    data: &Term,
) -> Result<(), String> {
    if !aggregate_validity::byte_array_payload_matches(
        context,
        pointer_bits,
        count as u64,
        length,
        data,
    )? {
        return Err("owned byte array choice has invalid length, sort or context".into());
    }
    Ok(())
}

fn flatten(
    context: &Context,
    pointer_bits: u32,
    shape: &OwnedChoiceShape,
    value: &Value,
    depth: usize,
    nodes: &mut usize,
    leaves: &mut Vec<(ScalarSliceElement, Value)>,
) -> Result<(), String> {
    if depth >= MAX_CHOICE_DEPTH || *nodes >= MAX_CHOICE_NODES {
        return Err("typed struct array choice exceeds its depth or candidate node budget".into());
    }
    *nodes += 1;
    let valid = |term: &Term, sort: Sort| term.sort() == &sort && term.belongs_to(context);
    match (shape, value) {
        (OwnedChoiceShape::ByteArray(count), value) => {
            let bytes = match value {
                Value::Elements(values) if values.len() == *count => values.to_vec(),
                Value::Bytes { data, length } => {
                    validate_owned_bytes(context, pointer_bits, *count, length, data)?;
                    (0..*count)
                        .map(|position| {
                            Ok(Value::Int {
                                expression: context.apply(
                                    Op::Select,
                                    &[
                                        data.clone(),
                                        context.bit_vector(position as u128, pointer_bits)?,
                                    ],
                                )?,
                                bits: 8,
                                signed: false,
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?
                }
                _ => return Err("owned byte array choice has incorrect carrier or count".into()),
            };
            for byte in &bytes {
                flatten(
                    context,
                    pointer_bits,
                    &OwnedChoiceShape::Primitive(ScalarSliceElement::Integer {
                        bits: 8,
                        signed: false,
                    }),
                    byte,
                    depth + 1,
                    nodes,
                    leaves,
                )?;
            }
        }
        (OwnedChoiceShape::Primitive(kind), value) => {
            let correct = match (kind, value) {
                (ScalarSliceElement::Bool, Value::Bool(term)) => valid(term, Sort::Bool),
                (
                    ScalarSliceElement::Integer { bits, signed },
                    Value::Int {
                        expression,
                        bits: actual,
                        signed: actual_signed,
                    },
                ) => {
                    bits == actual
                        && signed == actual_signed
                        && valid(expression, Sort::BitVec(*bits))
                }
                (
                    ScalarSliceElement::Char,
                    Value::Int {
                        expression,
                        bits: 32,
                        signed: false,
                    },
                ) => valid(expression, Sort::BitVec(32)),
                (
                    ScalarSliceElement::Float { bits },
                    Value::Float {
                        expression,
                        bits: actual,
                        raw_bits,
                    },
                ) => {
                    let (exponent, significand) = match bits {
                        32 => (8, 24),
                        64 => (11, 53),
                        _ => return Err("typed struct choice float width is invalid".into()),
                    };
                    bits == actual
                        && valid(
                            expression,
                            Sort::Float {
                                exponent,
                                significand,
                            },
                        )
                        && raw_bits
                            .as_ref()
                            .is_none_or(|raw| valid(raw, Sort::BitVec(*bits)))
                }
                _ => false,
            };
            if !correct {
                return Err("typed struct choice primitive differs from compiler shape".into());
            }
            leaves.push((*kind, value.clone()));
        }
        (OwnedChoiceShape::Tuple(fields), Value::Unit) if fields.is_empty() => {}
        (OwnedChoiceShape::Tuple(fields), Value::Tuple(values)) if fields.len() == values.len() => {
            for (field, value) in fields.iter().zip(values) {
                flatten(
                    context,
                    pointer_bits,
                    field,
                    value,
                    depth + 1,
                    nodes,
                    leaves,
                )?;
            }
        }
        (OwnedChoiceShape::Array(fields), Value::Elements(values))
            if fields.len() == values.len() =>
        {
            for (field, value) in fields.iter().zip(values.iter()) {
                flatten(
                    context,
                    pointer_bits,
                    field,
                    value,
                    depth + 1,
                    nodes,
                    leaves,
                )?;
            }
        }
        (
            OwnedChoiceShape::Struct { name, fields },
            Value::Adt {
                name: actual,
                variant: 0,
                discriminant: 0,
                is_option: false,
                fields: values,
            },
        ) if name == actual && fields.len() == values.len() => {
            for ((name, field), (actual, value)) in fields.iter().zip(values.iter()) {
                if name != actual {
                    return Err(
                        "typed struct choice field identity differs from compiler shape".into(),
                    );
                }
                flatten(
                    context,
                    pointer_bits,
                    field,
                    value,
                    depth + 1,
                    nodes,
                    leaves,
                )?;
            }
        }
        _ => return Err("typed struct choice value differs from exact compiler shape".into()),
    }
    Ok(())
}

fn conditional_product(
    context: &Context,
    pointer_bits: u32,
    shape: &OwnedChoiceShape,
    condition: &Term,
    replacement: &[Value],
    old: &[Value],
) -> Result<Value, String> {
    conditional_product_field(
        context,
        pointer_bits,
        shape,
        condition,
        ProductUpdate {
            span: 0..old.len(),
            leaves: replacement,
        },
        old,
    )
}

fn conditional_product_field(
    context: &Context,
    pointer_bits: u32,
    shape: &OwnedChoiceShape,
    condition: &Term,
    update: ProductUpdate<'_>,
    old: &[Value],
) -> Result<Value, String> {
    if condition.sort() != &Sort::Bool || !condition.belongs_to(context) {
        return Err("owned array write condition has invalid sort or context".into());
    }
    if update.span.start > update.span.end
        || update.span.end > old.len()
        || update.span.len() != update.leaves.len()
        || old.len() != product_leaf_count(shape)?
    {
        return Err("owned array write differs in certified leaf count or field span".into());
    }
    let selected = old
        .iter()
        .enumerate()
        .map(|(position, old)| {
            if update.span.contains(&position) {
                symbolic::conditional_scalar(
                    context,
                    condition,
                    &update.leaves[position - update.span.start],
                    old,
                )
            } else {
                Ok(old.clone())
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut cursor = 0;
    let result = rebuild(context, pointer_bits, shape, &selected, &mut cursor)?;
    if cursor != selected.len() {
        return Err("owned array write omitted certified leaves".into());
    }
    Ok(result)
}

fn validate_indexed_spans(
    spans: &[std::ops::Range<usize>],
    count: usize,
    width: usize,
) -> Result<(), String> {
    if spans.len() > MAX_CHOICE_NODES {
        return Err("owned indexed span budget exceeded".into());
    }
    let mut end = 0;
    for span in spans {
        if span.start > span.end
            || span.end > count
            || span.len() != width
            || (!span.is_empty() && span.start < end)
        {
            return Err("owned indexed spans are invalid or overlap".into());
        }
        if !span.is_empty() {
            end = span.end;
        }
    }
    Ok(())
}

fn conditional_indexed_product(
    context: &Context,
    pointer_bits: u32,
    shape: &OwnedChoiceShape,
    masks: &[(std::ops::Range<usize>, Term)],
    replacement: &[Value],
    old: &[Value],
) -> Result<Value, String> {
    if masks.len() > MAX_CHOICE_NODES {
        return Err("owned indexed span budget exceeded".into());
    }
    if old.len() != product_leaf_count(shape)? {
        return Err("owned indexed write differs in complete leaf inventory".into());
    }
    validate_indexed_spans(
        &masks
            .iter()
            .map(|(span, _)| span.clone())
            .collect::<Vec<_>>(),
        old.len(),
        replacement.len(),
    )?;
    for (_, mask) in masks {
        if mask.sort() != &Sort::Bool || !mask.belongs_to(context) {
            return Err("owned indexed write mask has invalid sort or context".into());
        }
    }
    let selected = old
        .iter()
        .enumerate()
        .map(|(position, old)| {
            if let Some((span, mask)) = masks.iter().find(|(span, _)| span.contains(&position)) {
                symbolic::conditional_scalar(
                    context,
                    mask,
                    &replacement[position - span.start],
                    old,
                )
            } else {
                Ok(old.clone())
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut cursor = 0;
    let result = rebuild(context, pointer_bits, shape, &selected, &mut cursor)?;
    if cursor != selected.len() {
        return Err("owned indexed write omitted leaves".into());
    }
    Ok(result)
}

fn indexed_product_masks(
    context: &Context,
    bits: u32,
    index: &Term,
    spans: &[std::ops::Range<usize>],
) -> Result<Vec<(std::ops::Range<usize>, Term)>, String> {
    if index.sort() != &Sort::BitVec(bits) || !index.belongs_to(context) {
        return Err("owned product write index has invalid width or context".into());
    }
    if spans.len() > MAX_CHOICE_NODES {
        return Err("owned indexed span budget exceeded".into());
    }
    spans
        .iter()
        .enumerate()
        .map(|(position, span)| {
            let mask = context.apply(
                Op::Equal,
                &[index.clone(), context.bit_vector(position as u128, bits)?],
            )?;
            Ok((span.clone(), mask))
        })
        .collect()
}

fn owned_row_condition(
    context: &Context,
    index: &Term,
    bits: u32,
    position: usize,
    known: Option<usize>,
    mode: OwnedWriteMode,
) -> Result<Option<Term>, String> {
    if index.sort() != &Sort::BitVec(bits) || !index.belongs_to(context) {
        return Err("owned row mask requires exact index width and context".into());
    }
    match mode {
        OwnedWriteMode::Nonunique => context
            .apply(
                Op::Equal,
                &[index.clone(), context.bit_vector(position as u128, bits)?],
            )
            .map(Some),
        OwnedWriteMode::Known => {
            let selected = known.ok_or("known owned array index has no bounded target")?;
            Ok((position == selected).then(|| context.boolean(true)))
        }
    }
}

fn fixed_index_value(
    context: &Context,
    value: &Value,
    pointer_bits: u32,
) -> Result<Option<usize>, String> {
    let (term, bits, signed) = value.integer()?;
    if signed
        || bits != pointer_bits
        || term.sort() != &Sort::BitVec(bits)
        || !term.belongs_to(context)
    {
        return Err("owned nested array index requires exact target usize".into());
    }
    let Some(symbolic::Constant::BitVec { value, .. }) = symbolic::constant(&term) else {
        return Ok(None);
    };
    usize::try_from(value)
        .map(Some)
        .map_err(|_| "owned nested array index exceeds host capacity".into())
}

fn product_array_child(
    children: &[OwnedChoiceShape],
    index: usize,
) -> Result<(&OwnedChoiceShape, usize), String> {
    let child = children
        .get(index)
        .ok_or("owned nested array index is invalid")?;
    let offset = children[..index].iter().try_fold(0_usize, |sum, child| {
        sum.checked_add(product_leaf_count(child)?)
            .ok_or_else(|| "owned product leaf offset overflow".to_owned())
    })?;
    Ok((child, offset))
}

fn checked_fixed_index(count: u64, index: usize, min_length: Option<u64>) -> Result<(), String> {
    if min_length.is_some_and(|minimum| minimum > count)
        || u64::try_from(index).map_or(true, |index| index >= count)
    {
        return Err("owned nested array index or minimum length is invalid".into());
    }
    Ok(())
}

fn product_field(
    shape: &OwnedChoiceShape,
    index: usize,
) -> Result<(&OwnedChoiceShape, usize), String> {
    let mut offset = 0_usize;
    match shape {
        OwnedChoiceShape::Tuple(fields) => {
            let field = fields
                .get(index)
                .ok_or("owned tuple field index is invalid")?;
            for field in &fields[..index] {
                offset = offset
                    .checked_add(product_leaf_count(field)?)
                    .ok_or("owned field leaf offset overflow")?;
            }
            Ok((field, offset))
        }
        OwnedChoiceShape::Struct { fields, .. } => {
            let (_, field) = fields
                .get(index)
                .ok_or("owned struct field index is invalid")?;
            for (_, field) in &fields[..index] {
                offset = offset
                    .checked_add(product_leaf_count(field)?)
                    .ok_or("owned field leaf offset overflow")?;
            }
            Ok((field, offset))
        }
        _ => Err("owned field projection requires a tuple or ordinary struct".into()),
    }
}

fn product_leaf_count(shape: &OwnedChoiceShape) -> Result<usize, String> {
    fn count(shape: &OwnedChoiceShape, depth: usize, nodes: &mut usize) -> Result<usize, String> {
        if depth >= MAX_CHOICE_DEPTH || *nodes >= MAX_CHOICE_NODES {
            return Err("owned field shape exceeds its depth or node budget".into());
        }
        *nodes += 1;
        match shape {
            OwnedChoiceShape::Primitive(_) => Ok(1),
            OwnedChoiceShape::ByteArray(count) => {
                if *count > MAX_CHOICE_NODES.saturating_sub(*nodes) {
                    return Err("owned field shape exceeds its byte budget".into());
                }
                *nodes += count;
                Ok(*count)
            }
            OwnedChoiceShape::Tuple(fields) | OwnedChoiceShape::Array(fields) => {
                fields.iter().try_fold(0_usize, |sum, field| {
                    sum.checked_add(count(field, depth + 1, nodes)?)
                        .ok_or_else(|| "owned field leaf count overflow".into())
                })
            }
            OwnedChoiceShape::Struct { fields, .. } => {
                fields.iter().try_fold(0_usize, |sum, (_, field)| {
                    sum.checked_add(count(field, depth + 1, nodes)?)
                        .ok_or_else(|| "owned field leaf count overflow".into())
                })
            }
        }
    }
    count(shape, 0, &mut 0)
}

pub(super) fn rebuild(
    context: &Context,
    pointer_bits: u32,
    shape: &OwnedChoiceShape,
    leaves: &[Value],
    cursor: &mut usize,
) -> Result<Value, String> {
    Ok(match shape {
        OwnedChoiceShape::ByteArray(count) => {
            let mut data = context.apply(
                Op::ConstArray {
                    index_bits: pointer_bits,
                },
                &[context.bit_vector(0, 8)?],
            )?;
            for position in 0..*count {
                let byte = leaves
                    .get(*cursor)
                    .ok_or("owned byte array choice leaf missing")?;
                *cursor += 1;
                let (byte, bits, signed) = byte.integer()?;
                if bits != 8 || signed {
                    return Err("owned byte array choice selected leaf is not u8".into());
                }
                data = context.apply(
                    Op::Store,
                    &[
                        data,
                        context.bit_vector(position as u128, pointer_bits)?,
                        byte,
                    ],
                )?;
            }
            Value::Bytes {
                data,
                length: Box::new(symbolic::integer(
                    context,
                    *count as u128,
                    pointer_bits,
                    false,
                )),
            }
        }
        OwnedChoiceShape::Primitive(_) => {
            let value = leaves
                .get(*cursor)
                .ok_or("typed struct choice leaf missing")?
                .clone();
            *cursor += 1;
            value
        }
        OwnedChoiceShape::Tuple(fields) if fields.is_empty() => Value::Unit,
        OwnedChoiceShape::Tuple(fields) => Value::Tuple(
            fields
                .iter()
                .map(|field| rebuild(context, pointer_bits, field, leaves, cursor))
                .collect::<Result<_, _>>()?,
        ),
        OwnedChoiceShape::Array(fields) => Value::Elements(
            fields
                .iter()
                .map(|field| rebuild(context, pointer_bits, field, leaves, cursor))
                .collect::<Result<Vec<_>, _>>()?
                .into(),
        ),
        OwnedChoiceShape::Struct { name, fields } => Value::Adt {
            name: name.clone(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: fields
                .iter()
                .map(|(name, field)| {
                    Ok((
                        name.clone(),
                        rebuild(context, pointer_bits, field, leaves, cursor)?,
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?
                .into(),
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn indexed_product_updates_preserve_disjoint_correlation_bits_and_empty_validation() {
        let context = Context::default();
        let outer = context.symbol(90, Sort::Bool).unwrap();
        let inner = context.symbol(91, Sort::Bool).unwrap();
        let first = context
            .apply(Op::And, &[outer.clone(), inner.clone()])
            .unwrap();
        let second = context
            .apply(Op::And, &[outer, symbolic::not(&inner)])
            .unwrap();
        let row = OwnedChoiceShape::Tuple(vec![
            OwnedChoiceShape::Primitive(ScalarSliceElement::Float { bits: 32 }),
            OwnedChoiceShape::Primitive(ScalarSliceElement::Integer {
                bits: 16,
                signed: false,
            }),
        ]);
        let shape = OwnedChoiceShape::Array(vec![row.clone(), row]);
        let old = vec![
            symbolic::float_from_bits(&context, context.bit_vector(0x7fc0_1234, 32).unwrap(), 32),
            symbolic::integer(&context, 7, 16, false),
            symbolic::float_from_bits(&context, context.bit_vector(0, 32).unwrap(), 32),
            symbolic::integer(&context, 11, 16, false),
        ];
        let replacement = vec![symbolic::float_from_bits(
            &context,
            context.bit_vector(0x8000_0000, 32).unwrap(),
            32,
        )];
        let masks = vec![(0..1, first.clone()), (2..3, second.clone())];
        let result =
            conditional_indexed_product(&context, 64, &shape, &masks, &replacement, &old).unwrap();
        let Value::Elements(rows) = result else {
            panic!("expected array");
        };
        for (position, mask) in [first, second].iter().enumerate() {
            let Value::Tuple(fields) = &rows[position] else {
                panic!("expected tuple");
            };
            assert_eq!(
                fields[1].integer().unwrap().0,
                old[position * 2 + 1].integer().unwrap().0
            );
            let Value::Float {
                raw_bits: Some(bits),
                ..
            } = &fields[0]
            else {
                panic!("expected certified bits");
            };
            let Value::Float {
                raw_bits: Some(new),
                ..
            } = &replacement[0]
            else {
                unreachable!();
            };
            let Value::Float {
                raw_bits: Some(old),
                ..
            } = &old[position * 2]
            else {
                unreachable!();
            };
            assert_eq!(
                *bits,
                context
                    .apply(Op::Ite, &[mask.clone(), new.clone(), old.clone()])
                    .unwrap()
            );
        }
        assert!(validate_indexed_spans(&[0..2, 1..3], 4, 2).is_err());
        assert!(validate_indexed_spans(&[std::ops::Range { start: 2, end: 1 }], 4, 1).is_err());
        assert!(validate_indexed_spans(std::slice::from_ref(&(3..5)), 4, 2).is_err());
        assert!(validate_indexed_spans(std::slice::from_ref(&(0..1)), 4, 2).is_err());
        assert!(validate_indexed_spans(&vec![0..0; MAX_CHOICE_NODES + 1], 0, 0).is_err());
        let zero = OwnedChoiceShape::Struct {
            name: "Zero".into(),
            fields: vec![],
        };
        let empty = conditional_indexed_product(
            &context,
            64,
            &zero,
            &[
                (0..0, context.boolean(true)),
                (0..0, context.boolean(false)),
            ],
            &[],
            &[],
        )
        .unwrap();
        assert!(
            matches!(empty, Value::Adt { name, fields, .. } if name=="Zero" && fields.is_empty())
        );
        let foreign = Context::default();
        assert!(
            conditional_indexed_product(
                &context,
                64,
                &zero,
                &[(0..0, foreign.boolean(true))],
                &[],
                &[]
            )
            .is_err()
        );
        assert!(
            conditional_indexed_product(
                &context,
                64,
                &zero,
                &[(0..0, context.bit_vector(0, 32).unwrap())],
                &[],
                &[]
            )
            .is_err()
        );
    }

    #[test]
    fn deferred_candidate_hint_is_bounded_and_does_not_observe_identity_carriers() {
        use std::rc::Rc;
        use symbolic::input::{InputKind, InputShape, InputValue};
        let context = Context::default();
        let deferred = Value::Input(InputValue {
            shape: Rc::new(InputShape {
                kind: InputKind::Unit,
                slots: 0,
                height: 1,
            }),
            start: 0,
            seed: context.boolean(false),
        });
        assert!(contains_deferred_product(std::slice::from_ref(&deferred)).unwrap());
        let mixed = Value::Tuple(vec![
            Value::Unit,
            Value::Elements(vec![Value::Unit, deferred.clone()].into()),
        ]);
        assert!(contains_deferred_product(&[mixed]).unwrap());
        assert!(!contains_deferred_product(&[Value::Tuple(vec![Value::Unit])]).unwrap());
        let hidden = Value::Adt {
            name: "Opaque".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: vec![("field".into(), deferred.clone())].into(),
        };
        assert!(!contains_deferred_product(&[hidden]).unwrap());
        let raw = Value::RawSlice {
            source: Box::new(deferred),
            length: Box::new(Value::Unit),
        };
        assert!(!contains_deferred_product(&[raw]).unwrap());
        assert!(contains_deferred_product(&vec![Value::Unit; MAX_CHOICE_NODES + 1]).is_err());
        assert!(
            contains_deferred_product(&[Value::Elements(
                vec![Value::Unit; MAX_CHOICE_NODES].into()
            )])
            .is_err()
        );
        let mut nested = Value::Unit;
        for _ in 0..MAX_CHOICE_DEPTH {
            nested = Value::Tuple(vec![nested]);
        }
        assert!(contains_deferred_product(&[nested]).is_err());
    }

    #[test]
    fn fixed_array_paths_validate_literal_metadata_bounds_and_logical_spans() {
        let context = Context::default();
        assert_eq!(
            fixed_index_value(&context, &symbolic::integer(&context, 1, 64, false), 64).unwrap(),
            Some(1)
        );
        let symbolic_index = Value::Int {
            expression: context.symbol(42, Sort::BitVec(64)).unwrap(),
            bits: 64,
            signed: false,
        };
        assert!(
            fixed_index_value(&context, &symbolic_index, 64)
                .unwrap()
                .is_none()
        );
        assert!(
            fixed_index_value(&context, &symbolic::integer(&context, 0, 64, true), 64).is_err()
        );
        assert!(
            fixed_index_value(&context, &symbolic::integer(&context, 0, 32, false), 64).is_err()
        );
        let foreign = Context::default();
        assert!(
            fixed_index_value(&context, &symbolic::integer(&foreign, 0, 64, false), 64).is_err()
        );
        let forged = Value::Int {
            expression: context.boolean(false),
            bits: 64,
            signed: false,
        };
        assert!(fixed_index_value(&context, &forged, 64).is_err());
        // Actual optimized MIR uses [0 of 1] for the original [u16; 2].
        assert!(checked_fixed_index(2, 0, Some(1)).is_ok());
        assert!(checked_fixed_index(2, 1, Some(2)).is_ok());
        assert!(checked_fixed_index(2, 0, Some(3)).is_err());
        assert!(checked_fixed_index(2, 2, Some(1)).is_err());
        assert!(checked_fixed_index(0, 0, Some(0)).is_err());
        let integer = OwnedChoiceShape::Primitive(ScalarSliceElement::Integer {
            bits: 16,
            signed: false,
        });
        let empty = OwnedChoiceShape::Struct {
            name: "Zero".into(),
            fields: vec![],
        };
        let row = OwnedChoiceShape::Tuple(vec![integer.clone(), empty, integer.clone()]);
        let rows = vec![row.clone(), row];
        let (child, offset) = product_array_child(&rows, 1).unwrap();
        assert_eq!(offset, 2);
        let (zero, inner) = product_field(child, 1).unwrap();
        assert_eq!(inner, 1);
        assert_eq!(product_leaf_count(zero).unwrap(), 0);
        assert!(product_array_child(&rows, 2).is_err());
        assert!(product_array_child(&[], 0).is_err());
        assert!(product_array_child(&[OwnedChoiceShape::ByteArray(513), integer], 1).is_err());
    }

    #[test]
    fn field_updates_preserve_untouched_terms_float_bits_zero_identity_and_checked_spans() {
        let context = Context::default();
        let integer = OwnedChoiceShape::Primitive(ScalarSliceElement::Integer {
            bits: 16,
            signed: false,
        });
        let zero = OwnedChoiceShape::Struct {
            name: "Zero".into(),
            fields: Vec::new(),
        };
        let nested = OwnedChoiceShape::Tuple(vec![
            OwnedChoiceShape::Primitive(ScalarSliceElement::Float { bits: 32 }),
            zero.clone(),
        ]);
        let shape = OwnedChoiceShape::Struct {
            name: "Record".into(),
            fields: vec![
                ("first".into(), integer.clone()),
                ("nested".into(), nested.clone()),
            ],
        };
        let (child, offset) = product_field(&shape, 1).unwrap();
        assert_eq!(offset, 1);
        let (empty, relative) = product_field(child, 1).unwrap();
        assert_eq!(relative, 1);
        assert_eq!(product_leaf_count(empty).unwrap(), 0);
        assert!(product_field(&shape, 2).is_err());
        assert!(product_field(&OwnedChoiceShape::Array(vec![integer.clone()]), 0).is_err());
        assert!(product_leaf_count(&OwnedChoiceShape::Array(vec![integer; 513])).is_err());
        assert!(product_leaf_count(&OwnedChoiceShape::ByteArray(513)).is_err());
        let condition = context.symbol(0, Sort::Bool).unwrap();
        let old = vec![
            symbolic::integer(&context, 7, 16, false),
            symbolic::float_from_bits(&context, context.bit_vector(0x8000_0000, 32).unwrap(), 32),
        ];
        let replacement = vec![symbolic::float_from_bits(
            &context,
            context.bit_vector(0x7fc0_0005, 32).unwrap(),
            32,
        )];
        let result = conditional_product_field(
            &context,
            64,
            &shape,
            &condition,
            ProductUpdate {
                span: 1..2,
                leaves: &replacement,
            },
            &old,
        )
        .unwrap();
        let mut leaves = Vec::new();
        flatten(&context, 64, &shape, &result, 0, &mut 0, &mut leaves).unwrap();
        assert_eq!(
            leaves[0].1.integer().unwrap().0,
            old[0].integer().unwrap().0
        );
        let Value::Float {
            raw_bits: Some(actual),
            ..
        } = &leaves[1].1
        else {
            panic!("lost Float bits");
        };
        let Value::Float {
            raw_bits: Some(new),
            ..
        } = &replacement[0]
        else {
            unreachable!();
        };
        let Value::Float {
            raw_bits: Some(previous),
            ..
        } = &old[1]
        else {
            unreachable!();
        };
        assert_eq!(
            *actual,
            context
                .apply(Op::Ite, &[condition.clone(), new.clone(), previous.clone()])
                .unwrap()
        );
        assert!(
            conditional_product_field(
                &context,
                64,
                &shape,
                &condition,
                ProductUpdate {
                    span: std::ops::Range { start: 2, end: 1 },
                    leaves: &[]
                },
                &old
            )
            .is_err()
        );
        assert!(
            conditional_product_field(
                &context,
                64,
                &shape,
                &condition,
                ProductUpdate {
                    span: 1..3,
                    leaves: &replacement
                },
                &old
            )
            .is_err()
        );
        assert!(
            conditional_product_field(
                &context,
                64,
                &shape,
                &condition,
                ProductUpdate {
                    span: 0..1,
                    leaves: &[]
                },
                &old
            )
            .is_err()
        );
        let unchanged = conditional_product_field(
            &context,
            64,
            &shape,
            &condition,
            ProductUpdate {
                span: 2..2,
                leaves: &[],
            },
            &old,
        )
        .unwrap();
        let Value::Adt { fields, .. } = unchanged else {
            panic!("lost parent identity");
        };
        let Value::Tuple(fields) = &fields[1].1 else {
            panic!("lost nested shape");
        };
        assert!(matches!(&fields[1], Value::Adt { name, .. } if name == "Zero"));
        assert!(
            conditional_product_field(
                &context,
                64,
                &zero,
                &Context::default().boolean(true),
                ProductUpdate {
                    span: 0..0,
                    leaves: &[]
                },
                &[]
            )
            .is_err()
        );
    }

    #[test]
    fn conditional_owned_products_preserve_nominal_bytes_and_complete_leaf_inventory() {
        let context = Context::default();
        let shape = OwnedChoiceShape::Struct {
            name: "Record".into(),
            fields: vec![
                ("bytes".into(), OwnedChoiceShape::ByteArray(2)),
                ("empty".into(), OwnedChoiceShape::Tuple(Vec::new())),
            ],
        };
        let bytes = |a, b| {
            vec![
                symbolic::integer(&context, a, 8, false),
                symbolic::integer(&context, b, 8, false),
            ]
        };
        let old = bytes(3, 7);
        let replacement = bytes(9, 19);
        for (condition, expected) in [(false, &old), (true, &replacement)] {
            let result = conditional_product(
                &context,
                32,
                &shape,
                &context.boolean(condition),
                &replacement,
                &old,
            )
            .unwrap();
            let mut nodes = 0;
            let mut leaves = Vec::new();
            flatten(&context, 32, &shape, &result, 0, &mut nodes, &mut leaves).unwrap();
            assert_eq!(leaves.len(), 2);
            for ((_, actual), expected) in leaves.iter().zip(expected) {
                assert_eq!(actual.integer().unwrap().0, expected.integer().unwrap().0);
            }
            assert!(matches!(
                result,
                Value::Adt {
                    variant: 0,
                    discriminant: 0,
                    is_option: false,
                    ..
                }
            ));
        }
        assert!(
            conditional_product(
                &context,
                32,
                &shape,
                &context.boolean(true),
                &replacement[..1],
                &old,
            )
            .is_err()
        );
        assert!(
            conditional_product(
                &context,
                32,
                &shape,
                &context.boolean(true),
                &bytes(9, 19),
                &bytes(3, 7)[..1],
            )
            .is_err()
        );
        let empty = OwnedChoiceShape::Struct {
            name: "Empty".into(),
            fields: Vec::new(),
        };
        assert!(
            conditional_product(
                &context,
                32,
                &empty,
                &Context::default().boolean(true),
                &[],
                &[]
            )
            .is_err()
        );
        assert!(
            conditional_product(
                &context,
                32,
                &empty,
                &context.bit_vector(1, 8).unwrap(),
                &[],
                &[]
            )
            .is_err()
        );
        assert!(
            conditional_product(
                &context,
                32,
                &OwnedChoiceShape::ByteArray(1),
                &context.boolean(true),
                &replacement,
                &old,
            )
            .is_err()
        );
    }

    #[test]
    fn byte_candidates_require_typed_annotations_exact_carriers_and_expanded_budgets() {
        let context = Context::default();
        let foreign = Context::default();
        let u8_shape = CompositeShape::Primitive(ScalarSliceElement::Integer {
            bits: 8,
            signed: false,
        });
        assert!(certified_byte_array_annotation(1, &[]).is_err());
        assert!(
            certified_byte_array_annotation(
                1,
                &[CompositeShape::Primitive(ScalarSliceElement::Integer {
                    bits: 16,
                    signed: false
                })]
            )
            .is_err()
        );
        let shape = certified_byte_array_annotation(3, &vec![u8_shape; 3]).unwrap();
        let empty = certified_byte_array_annotation(0, &[]).unwrap();
        for bits in [32, 64] {
            let data = context
                .apply(
                    Op::ConstArray { index_bits: bits },
                    &[context.bit_vector(7, 8).unwrap()],
                )
                .unwrap();
            let length = symbolic::integer(&context, 3, bits, false);
            let bytes = Value::Bytes {
                data: data.clone(),
                length: Box::new(length.clone()),
            };
            let elements =
                Value::Elements(vec![symbolic::integer(&context, 7, 8, false); 3].into());
            let mut byte_leaves = Vec::new();
            let mut element_leaves = Vec::new();
            let mut byte_nodes = 0;
            let mut element_nodes = 0;
            flatten(
                &context,
                bits,
                &shape,
                &bytes,
                0,
                &mut byte_nodes,
                &mut byte_leaves,
            )
            .unwrap();
            flatten(
                &context,
                bits,
                &shape,
                &elements,
                0,
                &mut element_nodes,
                &mut element_leaves,
            )
            .unwrap();
            assert_eq!(byte_nodes, 4);
            assert_eq!(element_nodes, byte_nodes);
            assert_eq!(format!("{byte_leaves:?}"), format!("{element_leaves:?}"));
            let selected = byte_leaves
                .into_iter()
                .map(|(_, value)| value)
                .collect::<Vec<_>>();
            let result = rebuild(&context, bits, &shape, &selected, &mut 0).unwrap();
            let Value::Bytes {
                data: result_data,
                length: result_len,
            } = result
            else {
                panic!("selected owned byte array must retain the byte carrier");
            };
            validate_owned_bytes(&context, bits, 3, &result_len, &result_data).unwrap();
            for position in 0..3 {
                assert_eq!(
                    symbolic::constant(
                        &context
                            .apply(
                                Op::Select,
                                &[
                                    result_data.clone(),
                                    context.bit_vector(position, bits).unwrap(),
                                ]
                            )
                            .unwrap()
                    ),
                    Some(symbolic::Constant::BitVec { value: 7, bits: 8 })
                );
            }
            let empty_bytes = Value::Bytes {
                data: data.clone(),
                length: Box::new(symbolic::integer(&context, 0, bits, false)),
            };
            flatten(
                &context,
                bits,
                &empty,
                &empty_bytes,
                0,
                &mut 0,
                &mut Vec::new(),
            )
            .unwrap();
            assert!(
                flatten(
                    &context,
                    bits,
                    &OwnedChoiceShape::Array(vec![]),
                    &empty_bytes,
                    0,
                    &mut 0,
                    &mut Vec::new()
                )
                .is_err()
            );
            assert!(
                flatten(
                    &context,
                    bits,
                    &empty,
                    &Value::Unit,
                    0,
                    &mut 0,
                    &mut Vec::new()
                )
                .is_err()
            );
            for invalid_length in [
                symbolic::integer(&context, 2, bits, false),
                symbolic::integer(&context, 3, bits, true),
                symbolic::integer(&foreign, 3, bits, false),
                Value::Int {
                    expression: context.symbol(100 + bits, Sort::BitVec(bits)).unwrap(),
                    bits,
                    signed: false,
                },
            ] {
                assert!(validate_owned_bytes(&context, bits, 3, &invalid_length, &data).is_err());
            }
            for invalid_data in [
                foreign
                    .apply(
                        Op::ConstArray { index_bits: bits },
                        &[foreign.bit_vector(7, 8).unwrap()],
                    )
                    .unwrap(),
                context
                    .apply(
                        Op::ConstArray {
                            index_bits: bits / 2,
                        },
                        &[context.bit_vector(7, 8).unwrap()],
                    )
                    .unwrap(),
                context
                    .apply(
                        Op::ConstArray { index_bits: bits },
                        &[context.bit_vector(7, 16).unwrap()],
                    )
                    .unwrap(),
            ] {
                assert!(validate_owned_bytes(&context, bits, 3, &length, &invalid_data).is_err());
            }
            for candidate in [&bytes, &elements] {
                let mut exhausted = MAX_CHOICE_NODES - 3;
                assert!(
                    flatten(
                        &context,
                        bits,
                        &shape,
                        candidate,
                        0,
                        &mut exhausted,
                        &mut Vec::new()
                    )
                    .is_err()
                );
            }
            let signed = Value::Elements(vec![symbolic::integer(&context, 7, 8, true); 3].into());
            assert!(flatten(&context, bits, &shape, &signed, 0, &mut 0, &mut Vec::new()).is_err());
        }
    }

    #[test]
    fn typed_candidate_schema_rejects_corruption_and_preserves_nominal_zero_values() {
        let context = Context::default();
        let foreign = Context::default();
        let shape = OwnedChoiceShape::Struct {
            name: "fixture::Pair".into(),
            fields: vec![
                (
                    "value".into(),
                    OwnedChoiceShape::Primitive(ScalarSliceElement::Integer {
                        bits: 16,
                        signed: false,
                    }),
                ),
                (
                    "marker".into(),
                    OwnedChoiceShape::Struct {
                        name: "fixture::Zero".into(),
                        fields: vec![],
                    },
                ),
            ],
        };
        let zero = Value::Adt {
            name: "fixture::Zero".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: vec![].into(),
        };
        let value = |term| Value::Adt {
            name: "fixture::Pair".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: vec![
                (
                    "value".into(),
                    Value::Int {
                        expression: term,
                        bits: 16,
                        signed: false,
                    },
                ),
                ("marker".into(), zero.clone()),
            ]
            .into(),
        };
        let correct = value(context.bit_vector(7, 16).unwrap());
        let mut leaves = Vec::new();
        flatten(&context, 64, &shape, &correct, 0, &mut 0, &mut leaves).unwrap();
        assert_eq!(leaves.len(), 1);
        let rebuilt = rebuild(&context, 64, &shape, &[leaves[0].1.clone()], &mut 0).unwrap();
        assert_eq!(format!("{correct:?}"), format!("{rebuilt:?}"));
        assert!(
            flatten(
                &context,
                64,
                &shape,
                &value(foreign.bit_vector(7, 16).unwrap()),
                0,
                &mut 0,
                &mut Vec::new()
            )
            .is_err()
        );
        let Value::Adt { fields, .. } = correct.clone() else {
            unreachable!()
        };
        for invalid in [
            Value::Adt {
                name: "fixture::Other".into(),
                variant: 0,
                discriminant: 0,
                is_option: false,
                fields: fields.clone(),
            },
            Value::Adt {
                name: "fixture::Pair".into(),
                variant: 1,
                discriminant: 0,
                is_option: false,
                fields: fields.clone(),
            },
            Value::Adt {
                name: "fixture::Pair".into(),
                variant: 0,
                discriminant: 1,
                is_option: false,
                fields: fields.clone(),
            },
            Value::Adt {
                name: "fixture::Pair".into(),
                variant: 0,
                discriminant: 0,
                is_option: true,
                fields: fields.clone(),
            },
            Value::Adt {
                name: "fixture::Pair".into(),
                variant: 0,
                discriminant: 0,
                is_option: false,
                fields: vec![].into(),
            },
        ] {
            assert!(flatten(&context, 64, &shape, &invalid, 0, &mut 0, &mut Vec::new()).is_err());
        }
        let Value::Adt { mut fields, .. } = correct.clone() else {
            unreachable!()
        };
        fields = fields.iter().cloned().rev().collect::<Vec<_>>().into();
        let reordered = Value::Adt {
            name: "fixture::Pair".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields,
        };
        assert!(flatten(&context, 64, &shape, &reordered, 0, &mut 0, &mut Vec::new()).is_err());
        let Value::Adt { fields, .. } = correct.clone() else {
            unreachable!()
        };
        let mut renamed = fields.iter().cloned().collect::<Vec<_>>();
        renamed[0].0 = "wrong".into();
        let renamed = Value::Adt {
            name: "fixture::Pair".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: renamed.into(),
        };
        assert!(flatten(&context, 64, &shape, &renamed, 0, &mut 0, &mut Vec::new()).is_err());
        let mut signed = fields.iter().cloned().collect::<Vec<_>>();
        let Value::Int { signed: sign, .. } = &mut signed[0].1 else {
            unreachable!()
        };
        *sign = true;
        let signed = Value::Adt {
            name: "fixture::Pair".into(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: signed.into(),
        };
        assert!(flatten(&context, 64, &shape, &signed, 0, &mut 0, &mut Vec::new()).is_err());
        let mut exhausted = MAX_CHOICE_NODES;
        assert!(
            flatten(
                &context,
                64,
                &shape,
                &correct,
                0,
                &mut exhausted,
                &mut Vec::new()
            )
            .is_err()
        );
    }

    #[test]
    fn known_write_fallback_matches_only_the_exact_unsupported_boundaries() {
        assert!(known_owned_write_frontier(
            "array write index is not uniquely determined"
        ));
        assert!(known_owned_write_frontier(
            "non-scalar array index is not uniquely determined on this path"
        ));
        for error in [
            "array write index is not uniquely determined on this path",
            "write through shared storage is unsupported",
            "solver could not discharge an obligation",
            "missing compiler-exported body",
            "reference points to dead or uninitialized storage",
            "wrapped: array write index is not uniquely determined",
        ] {
            assert!(!known_owned_write_frontier(error));
        }
    }

    #[test]
    fn known_row_masks_preserve_unrelated_rows_and_prior_nonunique_terms() {
        let context = Context::default();
        let index = context.symbol(0, Sort::BitVec(64)).unwrap();
        let old = context
            .apply(
                Op::Equal,
                &[index.clone(), context.bit_vector(1, 64).unwrap()],
            )
            .unwrap();
        assert_eq!(
            owned_row_condition(&context, &index, 64, 1, None, OwnedWriteMode::Nonunique)
                .unwrap()
                .unwrap(),
            old
        );
        assert_eq!(
            owned_row_condition(&context, &index, 64, 1, Some(1), OwnedWriteMode::Known)
                .unwrap()
                .unwrap(),
            context.boolean(true)
        );
        assert!(
            owned_row_condition(&context, &index, 64, 0, Some(1), OwnedWriteMode::Known)
                .unwrap()
                .is_none()
        );
        assert!(owned_row_condition(&context, &index, 64, 1, None, OwnedWriteMode::Known).is_err());
        assert!(
            owned_row_condition(&context, &index, 32, 1, Some(1), OwnedWriteMode::Known).is_err()
        );
        assert!(
            owned_row_condition(
                &Context::default(),
                &index,
                64,
                1,
                Some(1),
                OwnedWriteMode::Known
            )
            .is_err()
        );
        assert!(
            owned_row_condition(
                &Context::default(),
                &index,
                64,
                1,
                None,
                OwnedWriteMode::Nonunique
            )
            .is_err()
        );
    }

    #[test]
    fn product_root_masks_preserve_absolute_spans_and_index_context() {
        let context = Context::default();
        let index = context.symbol(0, Sort::BitVec(64)).unwrap();
        let spans = [1..3, 3..5];
        let masks = indexed_product_masks(&context, 64, &index, &spans).unwrap();
        for (position, (span, mask)) in masks.iter().enumerate() {
            assert_eq!(span, &spans[position]);
            assert_eq!(
                mask,
                &context
                    .apply(
                        Op::Equal,
                        &[
                            index.clone(),
                            context.bit_vector(position as u128, 64).unwrap()
                        ]
                    )
                    .unwrap()
            );
        }
        assert!(indexed_product_masks(&Context::default(), 64, &index, &spans).is_err());
        assert!(indexed_product_masks(&context, 32, &index, &spans).is_err());
        assert!(
            indexed_product_masks(&context, 64, &index, &vec![0..0; MAX_CHOICE_NODES + 1]).is_err()
        );
        assert!(validate_indexed_spans(&[1..3, 2..4], 5, 2).is_err());
        assert!(validate_indexed_spans(&[1..3, 3..6], 5, 2).is_err());
        assert!(validate_indexed_spans(&[1..1, 2..2], 3, 0).is_ok());
    }
}
