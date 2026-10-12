//! Exact incoming mutable product owners. Columns are logical typed storage, never raw bytes.
use super::composite_slices::{CompositeShape, CompositeType};
use super::mutable_u16::{Backing, ElementCodec, IntegerCertificate, Storage};
use super::mutable_u16_children::Phase;
use super::*;
use symbolic::{MutableU16Role, ScalarSliceElement};

#[path = "mutable_product_projection.rs"]
mod projection;

fn same_product_shape(left: &CompositeShape, right: &CompositeShape) -> bool {
    match (left, right) {
        (CompositeShape::Primitive(left), CompositeShape::Primitive(right)) => left == right,
        (CompositeShape::Tuple(left), CompositeShape::Tuple(right))
        | (CompositeShape::Array(left), CompositeShape::Array(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| same_product_shape(left, right))
        }
        (
            CompositeShape::Struct {
                name: left_name,
                fields: left,
            },
            CompositeShape::Struct {
                name: right_name,
                fields: right,
            },
        ) => {
            left_name == right_name
                && left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|((ln, ls), (rn, rs))| ln == rn && same_product_shape(ls, rs))
        }
        (
            CompositeShape::Primitive(_)
            | CompositeShape::Tuple(_)
            | CompositeShape::Array(_)
            | CompositeShape::Struct { .. }
            | CompositeShape::NonZeroNiche(_)
            | CompositeShape::Sum { .. },
            _,
        ) => false,
    }
}

fn leaf_count(shape: &CompositeShape) -> Result<usize, String> {
    match shape {
        CompositeShape::Primitive(_) => Ok(1),
        CompositeShape::Tuple(fields) | CompositeShape::Array(fields) => {
            fields.iter().try_fold(0_usize, |total, field| {
                total
                    .checked_add(leaf_count(field)?)
                    .ok_or_else(|| "mutable product leaf count overflow".into())
            })
        }
        CompositeShape::Struct { fields, .. } => {
            fields.iter().try_fold(0_usize, |total, (_, field)| {
                total
                    .checked_add(leaf_count(field)?)
                    .ok_or_else(|| "mutable product leaf count overflow".into())
            })
        }
        CompositeShape::NonZeroNiche(_) | CompositeShape::Sum { .. } => {
            Err("mutable product sums and niches are unsupported".into())
        }
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn mutable_product_kind(&self, ty: Ty<'tcx>) -> bool {
        matches!(ty.kind(), ty::Tuple(_) | ty::Array(..))
            || matches!(ty.kind(), ty::Adt(def, _) if def.is_struct() && def.did().is_local())
    }

    pub(super) fn mutable_product_shape(
        &self,
        original: Ty<'tcx>,
    ) -> Result<Option<CompositeType<'tcx>>, String> {
        if !self.mutable_product_kind(original) {
            return Ok(None);
        }
        let Some(descriptor) = self.composite_shape_with_sums(original, false)? else {
            return Ok(None);
        };
        self.mutable_product_originals(original, 0)?;
        if descriptor.leaves.len() != leaf_count(&descriptor.shape)? {
            return Err("mutable product descriptor omitted typed leaves".into());
        }
        Ok(Some(descriptor))
    }

    fn mutable_product_originals(&self, original: Ty<'tcx>, depth: usize) -> Result<(), String> {
        if depth >= 16 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable product original type exceeds existing depth budget".into(),
            ));
        }
        match original.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64) => Ok(()),
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    self.mutable_product_originals(field, depth + 1)?;
                }
                Ok(())
            }
            ty::Array(element, _) => self.mutable_product_originals(*element, depth + 1),
            ty::Adt(def, args) if def.is_struct() && def.did().is_local() => {
                for field in &def.non_enum_variant().fields {
                    self.mutable_product_originals(
                        field.ty(self.tcx, args).skip_norm_wip(),
                        depth + 1,
                    )?;
                }
                Ok(())
            }
            _ => Err(
                "mutable product requires exact primitive leaves and local pure products".into(),
            ),
        }
    }

    pub(super) fn mutable_product_certificate(
        &self,
        id: usize,
    ) -> Result<&IntegerCertificate<'tcx>, String> {
        let certificate = self
            .mutable_integer_types
            .get(id)
            .ok_or("mutable product certificate was not issued")?;
        let ElementCodec::Product(issued) = &certificate.codec else {
            return Err("mutable product needs an exact product certificate".into());
        };
        let current = self
            .mutable_product_shape(certificate.original)?
            .ok_or("mutable product original type is unsupported")?;
        let layout = self.static_layout(certificate.original)?;
        if issued.ty != certificate.original
            || issued.bytes != current.bytes
            || issued.leaves != current.leaves
            || !same_product_shape(&issued.shape, &current.shape)
            || certificate.bytes != current.bytes
            || certificate.alignment != layout.align.abi.bytes()
        {
            return Err(
                "mutable product certificate differs from exact original compiler type".into(),
            );
        }
        Ok(certificate)
    }

    pub(super) fn mutable_product_input(
        &mut self,
        original: Ty<'tcx>,
        memory: &mut Memory,
        conditions: &mut Vec<Term>,
    ) -> Result<Value, String> {
        let descriptor = self.mutable_product_shape(original)?.ok_or_else(|| {
            self.categorized_error(
                UnknownCategory::Semantics,
                "mutable product input requires exact pure tuple/array/local struct".into(),
            )
        })?;
        let count = descriptor.leaves.len().saturating_add(1);
        let storage = 1 + descriptor.leaves.len().max(1);
        if self.input_values.saturating_add(count) > MAX_INPUT_VALUES
            || memory.storage_slots().saturating_add(storage) > MAX_INPUT_VALUES
            || self.mutable_integer_types.len() >= MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable product input exceeds existing input/storage budget".into(),
            ));
        }
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let length = self.fresh(Sort::BitVec(bits));
        let maximum = self.mutable_product_extent(descriptor.bytes);
        conditions.push(self.terms.apply(
            Op::BvUnsignedLe,
            &[length.clone(), self.terms.bit_vector(maximum, bits)?],
        )?);
        let mut columns = Vec::with_capacity(descriptor.leaves.len());
        for leaf in &descriptor.leaves {
            columns.push(self.fresh(Sort::Array(
                Box::new(Sort::BitVec(bits)),
                Box::new(super::scalar_slices::scalar_slice_sort(*leaf)?),
            )));
            if matches!(leaf, ScalarSliceElement::Float { .. }) {
                self.float_pairs.activate();
            }
        }
        let layout = self.static_layout(original)?;
        let certificate = self.mutable_integer_types.len();
        self.mutable_integer_types.push(IntegerCertificate {
            original,
            codec: ElementCodec::from(descriptor),
            bytes: layout.size.bytes(),
            alignment: layout.align.abi.bytes(),
        });
        self.input_values += count;
        let allocation = memory.len();
        // One actual logical owner marker; columns stay inside the same Backing payload.
        // Memory derives additional column slots in its existing backing accounting pass.
        memory.push(Some(Value::Unit));
        let id = memory.mutable_u16.len();
        std::rc::Rc::make_mut(&mut memory.mutable_u16).push(Backing {
            certificate,
            allocation,
            length: Value::Int {
                expression: length,
                bits,
                signed: false,
            },
            data: Storage::from(columns),
            generation: 0,
            phase: Phase::Idle,
            interval: None,
            hierarchy: None,
        });
        Ok(Value::MutableU16 {
            id,
            role: MutableU16Role::Root,
        })
    }

    fn mutable_product_extent(&self, bytes: u64) -> u128 {
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let maximum = u128::MAX >> (128 - bits);
        if bytes == 0 {
            maximum
        } else {
            (maximum >> 1) / u128::from(bytes)
        }
    }

    pub(super) fn mutable_product_owner(&self, id: usize, memory: &Memory) -> Result<bool, String> {
        let backing = memory
            .mutable_u16
            .get(id)
            .ok_or("mutable owner identity was not issued")?;
        Ok(matches!(backing.data, Storage::Product(_)))
    }

    pub(super) fn mutable_product_backing<'a>(
        &self,
        id: usize,
        memory: &'a Memory,
    ) -> Result<&'a Backing, String> {
        let backing = memory
            .mutable_u16
            .get(id)
            .ok_or("mutable product owner identity was not issued")?;
        let certificate = self.mutable_product_certificate(backing.certificate)?;
        let ElementCodec::Product(descriptor) = &certificate.codec else {
            return Err("mutable product descriptor is absent".into());
        };
        let Storage::Product(columns) = &backing.data else {
            return Err("mutable product owner has a scalar storage payload".into());
        };
        // This gate validates representation, not lifecycle permission. Pending observations
        // remain refused by role validation; only original staging/call transactions use it.
        if backing.interval.is_some()
            || backing.hierarchy.is_some()
            || memory.mutable_hierarchy.is_some()
            || columns.len() != descriptor.leaves.len()
        {
            return Err("mutable product root identity/phase/column inventory differs".into());
        }
        memory.check_projection_initialization(backing.allocation, &[])?;
        if !matches!(memory.get(backing.allocation), Some(Some(Value::Unit))) {
            return Err("mutable product backing allocation is unavailable".into());
        }
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let (length, width, signed) = backing.length.integer()?;
        if width != bits
            || signed
            || length.sort() != &Sort::BitVec(bits)
            || !length.belongs_to(&self.terms)
        {
            return Err("mutable product length differs from target usize/current Context".into());
        }
        for (column, leaf) in columns.iter().zip(&descriptor.leaves) {
            if !column.belongs_to(&self.terms)
                || column.sort()
                    != &Sort::Array(
                        Box::new(Sort::BitVec(bits)),
                        Box::new(super::scalar_slices::scalar_slice_sort(*leaf)?),
                    )
            {
                return Err(
                    "mutable product columns differ from original codec/current Context".into(),
                );
            }
        }
        Ok(backing)
    }

    pub(super) fn mutable_product_length(
        &self,
        value: &Value,
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let Value::MutableU16 { id, role } = value else {
            return Err("mutable product length needs an issued owner role".into());
        };
        let backing = self.mutable_product_backing(*id, memory)?;
        self.mutable_u16_role_live(*id, role, memory)?;
        if !matches!(
            role,
            MutableU16Role::Root
                | MutableU16Role::Metadata { .. }
                | MutableU16Role::Child { .. }
                | MutableU16Role::ChildMetadata { .. }
        ) {
            return Err("mutable product hierarchy/Ghost length is unsupported".into());
        }
        if let Phase::Active { frames } = &backing.phase {
            self.mutable_product_issued_frames(frames)?;
        }
        let certificate = self.mutable_product_certificate(backing.certificate)?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let bounded = self.terms.apply(
            Op::BvUnsignedLe,
            &[
                backing.length.integer()?.0,
                self.terms
                    .bit_vector(self.mutable_product_extent(certificate.bytes), bits)?,
            ],
        )?;
        let mut invalid = conditions.to_vec();
        invalid.push(symbolic::not(&bounded));
        if self.feasible(&invalid)? {
            return Err("mutable product lacks current valid target allocation extent".into());
        }
        Ok(backing.length.clone())
    }

    pub(super) fn mutable_owner_length(
        &self,
        value: &Value,
        state: &State,
    ) -> Result<Value, String> {
        if let Value::MutableU16 { id, role } = value
            && !matches!(role, MutableU16Role::Ghost { .. })
            && self.mutable_product_owner(*id, &state.memory)?
        {
            state.flow.require_unarmed()?;
            self.mutable_product_length(value, &state.memory, &state.conditions)
        } else {
            self.mutable_u16_length(value, &state.memory)
        }
    }

    pub(super) fn mutable_product_issued_frames(&self, frames: &[usize]) -> Result<(), String> {
        if frames.is_empty() {
            return Err("mutable product active frame inventory is unsupported".into());
        }
        if frames.len() > MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable u16 active frame stack exceeds existing depth budget".into(),
            ));
        }
        let issued = self.mutable_u16_frames.borrow();
        let bodies = self.bodies.borrow();
        for frame in frames {
            let body = issued
                .get(*frame)
                .and_then(std::rc::Weak::upgrade)
                .ok_or("mutable product current frame Body expired or was not issued")?;
            if !bodies
                .values()
                .any(|current| std::rc::Rc::ptr_eq(current, &body))
            {
                return Err("mutable product current frame Body was replaced".into());
            }
        }
        Ok(())
    }

    pub(super) fn mutable_product_frame(
        &self,
        body: &Body<'tcx>,
        id: usize,
        role: &MutableU16Role,
        memory: &Memory,
    ) -> Result<(), String> {
        let backing = self.mutable_product_backing(id, memory)?;
        self.mutable_u16_role_live(id, role, memory)?;
        match &backing.phase {
            Phase::Idle => {
                if !matches!(role, MutableU16Role::Root | MutableU16Role::Metadata { .. }) {
                    return Err("mutable product idle owner has no current root role".into());
                }
            }
            Phase::Pending { .. } => {
                return Err("mutable product pending child has no observation permission".into());
            }
            Phase::Active { frames } => {
                if !matches!(
                    role,
                    MutableU16Role::Child { .. } | MutableU16Role::ChildMetadata { .. }
                ) {
                    return Err(
                        "mutable product active owner requires its current child role".into(),
                    );
                }
                self.mutable_product_issued_frames(frames)?;
                self.mutable_u16_frame_top(body, frames)?;
            }
        }
        Ok(())
    }

    fn product_local(
        &self,
        body: &Body<'tcx>,
        state: &State,
        local: usize,
    ) -> Result<Option<(usize, MutableU16Role)>, String> {
        let value = if let Some(allocation) = state.addresses[local] {
            state.memory.get(allocation).and_then(Option::as_ref)
        } else {
            state.locals[local].as_ref()
        };
        let Some(Value::MutableU16 { id, role }) = value else {
            return Ok(None);
        };
        if matches!(role, MutableU16Role::Ghost { .. })
            || !self.mutable_product_owner(*id, &state.memory)?
        {
            return Ok(None);
        }
        let (id, role) = (*id, role.clone());
        state.flow.require_unarmed()?;
        self.check_local_initialization(state, local, &[])?;
        self.mutable_product_frame(body, id, &role, &state.memory)?;
        Ok(Some((id, role)))
    }

    pub(super) fn mutable_product_metadata(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let Some((id, role)) = self.product_local(body, state, place.local.as_usize())? else {
            return Ok(None);
        };
        if !matches!(role, MutableU16Role::Root | MutableU16Role::Child { .. })
            || place.projection.as_ref() != [ProjectionElem::Deref]
            || !self.mutable_u16_matches(
                body.local_decls[place.local].ty,
                id,
                &state.memory,
                true,
            )?
        {
            return Err("mutable product metadata needs the original direct root".into());
        }
        let generation = self.mutable_product_backing(id, &state.memory)?.generation;
        let metadata = match role {
            MutableU16Role::Root => MutableU16Role::Metadata { generation },
            MutableU16Role::Child { .. } => MutableU16Role::ChildMetadata { generation },
            MutableU16Role::Metadata { .. }
            | MutableU16Role::ChildMetadata { .. }
            | MutableU16Role::Ghost { .. }
            | MutableU16Role::HierarchyChild { .. }
            | MutableU16Role::HierarchyMetadata { .. } => {
                return Err("mutable product metadata source lacks payload authority".into());
            }
        };
        let root = Value::MutableU16 { id, role };
        self.mutable_product_length(&root, &state.memory, &state.conditions)?;
        Ok(Some(Value::MutableU16 { id, role: metadata }))
    }

    pub(super) fn mutable_product_store_role(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        value: &Value,
    ) -> Result<bool, String> {
        let Value::MutableU16 { id, role } = value else {
            return Ok(false);
        };
        if !self.mutable_product_owner(*id, &state.memory)? {
            return Ok(false);
        }
        state.flow.require_unarmed()?;
        self.mutable_product_frame(body, *id, role, &state.memory)?;
        if !matches!(
            role,
            MutableU16Role::Metadata { .. } | MutableU16Role::ChildMetadata { .. }
        ) || !place.projection.is_empty()
            || place.local.as_usize() <= body.arg_count
            || state.addresses[place.local.as_usize()].is_some()
        {
            return Err(
                "mutable product roles require private original metadata temporaries".into(),
            );
        }
        let inner = match body.local_decls[place.local].ty.kind() {
            ty::Ref(_, inner, mutability) | ty::RawPtr(inner, mutability)
                if !mutability.is_mut() =>
            {
                *inner
            }
            _ => return Err("mutable product metadata destination has a different type".into()),
        };
        let backing = self.mutable_product_backing(*id, &state.memory)?;
        let certificate = self.mutable_product_certificate(backing.certificate)?;
        if !matches!(inner.kind(), ty::Slice(element) if *element == certificate.original) {
            return Err("mutable product metadata destination needs original product slice".into());
        }
        self.mutable_product_length(value, &state.memory, &state.conditions)?;
        Ok(true)
    }

    fn product_projection<'a>(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        descriptor: &'a CompositeType<'tcx>,
        length: &Value,
    ) -> Result<projection::Projection<'a, 'tcx>, String> {
        let [ProjectionElem::Deref, outer, suffix @ ..] = place.projection.as_ref() else {
            return Err("mutable product observation needs one direct outer index".into());
        };
        let index = match outer {
            ProjectionElem::Index(local) if body.local_decls[*local].ty == self.tcx.types.usize => {
                self.local(state, local.as_usize())?
            }
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => self.product_constant_index(
                *offset,
                *min_length,
                *from_end,
                length,
                &state.conditions,
            )?,
            _ => {
                return Err(
                    "mutable product outer index differs from original target usize".into(),
                );
            }
        };
        let (term, width, signed) = index.integer()?;
        if width != u32::from(self.tcx.sess.target.pointer_width)
            || signed
            || term.sort() != &Sort::BitVec(width)
            || !term.belongs_to(&self.terms)
        {
            return Err("mutable product outer index differs from current target usize".into());
        }
        self.memory_bounds(&index, length, &state.conditions)?;
        let mut original = descriptor.ty;
        let mut shape = &descriptor.shape;
        let mut start = 0;
        for projection in suffix {
            let (position, fields, next_ty) = match (projection, original.kind(), shape) {
                (
                    ProjectionElem::Field(field, field_ty),
                    ty::Tuple(types),
                    CompositeShape::Tuple(fields),
                ) => {
                    let position = field.as_usize();
                    let ty = *types
                        .get(position)
                        .ok_or("mutable product tuple field differs")?;
                    if ty != *field_ty {
                        return Err("mutable product original FieldTy differs".into());
                    }
                    (position, fields.as_slice(), ty)
                }
                (
                    ProjectionElem::Field(field, field_ty),
                    ty::Adt(def, args),
                    CompositeShape::Struct { fields, .. },
                ) if def.is_struct() => {
                    let position = field.as_usize();
                    let field = def
                        .non_enum_variant()
                        .fields
                        .get(*field)
                        .ok_or("mutable product struct field differs")?;
                    let ty = field.ty(self.tcx, args).skip_norm_wip();
                    if ty != *field_ty {
                        return Err("mutable product original FieldTy differs".into());
                    }
                    for (_, preceding) in fields.iter().take(position) {
                        start += leaf_count(preceding)?;
                    }
                    shape = &fields
                        .get(position)
                        .ok_or("mutable product field inventory differs")?
                        .1;
                    original = ty;
                    continue;
                }
                (
                    ProjectionElem::Index(local),
                    ty::Array(element, count),
                    CompositeShape::Array(fields),
                ) if body.local_decls[*local].ty == self.tcx.types.usize => {
                    let count = count
                        .try_to_target_usize(self.tcx)
                        .ok_or("mutable product inner array count is unavailable")?;
                    let value = self.local(state, local.as_usize())?;
                    let (term, width, signed) = value.integer()?;
                    let Some(symbolic::Constant::BitVec {
                        value: position,
                        bits,
                    }) = symbolic::constant(&term)
                    else {
                        let position = suffix
                            .iter()
                            .position(|current| std::ptr::eq(current, projection))
                            .unwrap();
                        return projection::prepare(
                            self,
                            projection::Source { body, state, place },
                            projection::Seed {
                                outer: index,
                                original,
                                shape,
                                start,
                                first: value,
                                suffix: &suffix[position..],
                                columns: descriptor.leaves.len(),
                                prefix_scan: position + 1,
                            },
                        )
                        .map(projection::Projection::Symbolic);
                    };
                    if width != u32::from(self.tcx.sess.target.pointer_width)
                        || signed
                        || bits != width
                        || !term.belongs_to(&self.terms)
                        || count != fields.len() as u64
                        || position >= u128::from(count)
                    {
                        return Err(
                            "mutable product constant suffix differs from original array".into(),
                        );
                    }
                    (position as usize, fields.as_slice(), *element)
                }
                (
                    ProjectionElem::ConstantIndex {
                        offset,
                        min_length,
                        from_end,
                    },
                    ty::Array(element, count),
                    CompositeShape::Array(fields),
                ) => {
                    let count = count
                        .try_to_target_usize(self.tcx)
                        .ok_or("mutable product inner array count is unavailable")?;
                    if count != fields.len() as u64
                        || *min_length > count
                        || (!*from_end && *offset >= *min_length)
                        || (*from_end && *offset > *min_length)
                        || (*from_end && (*offset == 0 || *offset > count))
                        || (!*from_end && *offset >= count)
                    {
                        return Err(
                            "mutable product inner constant index exceeds original array".into(),
                        );
                    }
                    let position = if *from_end { count - *offset } else { *offset } as usize;
                    (position, fields.as_slice(), *element)
                }
                _ => {
                    return Err(
                        "mutable product suffix needs original fields/constant indices".into(),
                    );
                }
            };
            for preceding in fields.iter().take(position) {
                start += leaf_count(preceding)?;
            }
            shape = fields
                .get(position)
                .ok_or("mutable product suffix inventory differs")?;
            original = next_ty;
        }
        if place.ty(&body.local_decls, self.tcx).ty != original {
            return Err("mutable product projected original type differs".into());
        }
        Ok(projection::Projection::Direct(
            index, original, shape, start,
        ))
    }

    fn product_constant_index(
        &self,
        offset: u64,
        minimum: u64,
        from_end: bool,
        length: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let maximum = u128::MAX >> (128 - bits);
        if u128::from(offset) > maximum
            || u128::from(minimum) > maximum
            || (!from_end && offset >= minimum)
            || (from_end && (offset == 0 || offset > minimum))
        {
            return Err("mutable product constant index metadata is invalid".into());
        }
        let minimum = symbolic::integer(&self.terms, u128::from(minimum), bits, false);
        let safe = symbolic::binary(&self.terms, "le", minimum, length.clone())?.boolean()?;
        let mut invalid = conditions.to_vec();
        invalid.push(symbolic::not(&safe));
        if self.feasible(&invalid)? {
            return Err("mutable product constant index minimum is not established".into());
        }
        let offset = symbolic::integer(&self.terms, u128::from(offset), bits, false);
        if from_end {
            symbolic::binary(&self.terms, "sub", length.clone(), offset)
        } else {
            Ok(offset)
        }
    }

    pub(super) fn mutable_product_read(
        &self,
        body: Option<&Body<'tcx>>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        let Some(body) = body else {
            let local = place.local.as_usize();
            let current = if let Some(allocation) = state.addresses[local] {
                state.memory.get(allocation).and_then(Option::as_ref)
            } else {
                state.locals[local].as_ref()
            };
            if let Some(Value::MutableU16 { id, role }) = current
                && !matches!(role, MutableU16Role::Ghost { .. })
                && self.mutable_product_owner(*id, &state.memory)?
            {
                return Err("mutable product observation needs original compiler Body".into());
            }
            return Ok(None);
        };
        let Some((id, role)) = self.product_local(body, state, place.local.as_usize())? else {
            return Ok(None);
        };
        if place.projection.is_empty() {
            return Ok(Some(Value::MutableU16 { id, role }));
        }
        if !matches!(role, MutableU16Role::Root | MutableU16Role::Child { .. }) {
            return Err("mutable product metadata cannot observe payload".into());
        }
        if !self.mutable_u16_matches(body.local_decls[place.local].ty, id, &state.memory, true)? {
            return Err("mutable product root differs from original compiler type".into());
        }
        let length = self.mutable_product_length(
            &Value::MutableU16 { id, role },
            &state.memory,
            &state.conditions,
        )?;
        let backing = self.mutable_product_backing(id, &state.memory)?;
        let certificate = self.mutable_product_certificate(backing.certificate)?;
        let ElementCodec::Product(descriptor) = &certificate.codec else {
            unreachable!()
        };
        let Storage::Product(columns) = &backing.data else {
            unreachable!()
        };
        let selected = self.product_projection(body, state, place, descriptor, &length)?;
        let (index, shape, start) = match selected {
            projection::Projection::Direct(index, _, shape, start) => (index, shape, start),
            projection::Projection::Symbolic(mut selection) => {
                return selection.read(self, columns, &state.conditions).map(Some);
            }
        };
        let mut cursor = start;
        let value = shape.observe(&self.terms, columns, &index.integer()?.0, &mut cursor)?;
        if cursor != start + leaf_count(shape)? {
            return Err("mutable product read omitted typed columns".into());
        }
        Ok(Some(value))
    }

    pub(super) fn mutable_product_store(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        value: &Value,
    ) -> Result<bool, String> {
        let Some((id, role)) = self.product_local(body, state, place.local.as_usize())? else {
            return Ok(false);
        };
        if place.projection.is_empty()
            && matches!(
                role,
                MutableU16Role::Metadata { .. } | MutableU16Role::ChildMetadata { .. }
            )
        {
            return Ok(false);
        }
        if !matches!(role, MutableU16Role::Root | MutableU16Role::Child { .. }) {
            return Err("mutable product metadata cannot write payload".into());
        }
        if !self.mutable_u16_matches(body.local_decls[place.local].ty, id, &state.memory, true)? {
            return Err("mutable product store differs from original compiler root".into());
        }
        let length = self.mutable_product_length(
            &Value::MutableU16 { id, role },
            &state.memory,
            &state.conditions,
        )?;
        let backing = self.mutable_product_backing(id, &state.memory)?;
        let certificate = self.mutable_product_certificate(backing.certificate)?;
        let ElementCodec::Product(descriptor) = &certificate.codec else {
            unreachable!()
        };
        let Storage::Product(columns) = &backing.data else {
            unreachable!()
        };
        let selected = self.product_projection(body, state, place, descriptor, &length)?;
        let (index, original, shape, start) = match selected {
            projection::Projection::Direct(index, original, shape, start) => {
                (index, original, shape, start)
            }
            projection::Projection::Symbolic(mut selection) => {
                let next = selection.store(self, columns, value, &state.conditions)?;
                std::rc::Rc::make_mut(&mut state.memory.mutable_u16)[id].data =
                    Storage::Product(next);
                return Ok(true);
            }
        };
        let mut replacements = Vec::new();
        self.product_replacements(original, shape, value, &state.conditions, &mut replacements)?;
        if replacements.len() != leaf_count(shape)? {
            return Err("mutable product store omitted typed leaves".into());
        }
        let mut next = columns.clone();
        for (offset, replacement) in replacements.into_iter().enumerate() {
            next[start + offset] = self.terms.apply(
                Op::Store,
                &[
                    columns[start + offset].clone(),
                    index.integer()?.0.clone(),
                    replacement,
                ],
            )?;
        }
        // No current Memory write occurs until every original type/Char/Float check and every
        // column update succeeds. Other branches, columns and outer indices retain storage.
        std::rc::Rc::make_mut(&mut state.memory.mutable_u16)[id].data = Storage::Product(next);
        Ok(true)
    }

    fn product_replacements(
        &self,
        original: Ty<'tcx>,
        shape: &CompositeShape,
        value: &Value,
        conditions: &[Term],
        output: &mut Vec<Term>,
    ) -> Result<(), String> {
        match (original.kind(), shape, value) {
            (_, CompositeShape::Primitive(element), _) => {
                if self.scalar_slice_element(original)? != Some(*element) {
                    return Err("mutable product leaf differs from original primitive".into());
                }
                let layout = self.static_layout(original)?;
                let codec = IntegerCertificate {
                    original,
                    codec: ElementCodec::Scalar(*element),
                    bytes: layout.size.bytes(),
                    alignment: layout.align.abi.bytes(),
                };
                let term = self.mutable_scalar_replacement(&codec, value)?;
                match element {
                    ScalarSliceElement::Char => self.prove_char_value(value, conditions)?,
                    ScalarSliceElement::Float { bits } => {
                        self.prove_float_pair(value, *bits, conditions)?
                    }
                    ScalarSliceElement::Bool | ScalarSliceElement::Integer { .. } => {}
                }
                output.push(term);
            }
            (ty::Tuple(types), CompositeShape::Tuple(fields), Value::Tuple(values))
                if types.len() == fields.len() && values.len() == fields.len() =>
            {
                for ((ty, shape), value) in types.iter().zip(fields).zip(values) {
                    self.product_replacements(ty, shape, value, conditions, output)?;
                }
            }
            (ty::Tuple(types), CompositeShape::Tuple(fields), Value::Unit)
                if types.is_empty() && fields.is_empty() => {}
            (ty::Array(element, count), CompositeShape::Array(fields), Value::Elements(values))
                if count.try_to_target_usize(self.tcx) == Some(fields.len() as u64)
                    && values.len() == fields.len() =>
            {
                for (shape, value) in fields.iter().zip(values.iter()) {
                    self.product_replacements(*element, shape, value, conditions, output)?;
                }
            }
            (
                ty::Adt(def, args),
                CompositeShape::Struct { name, fields },
                Value::Adt {
                    name: actual,
                    variant: 0,
                    discriminant: 0,
                    is_option: false,
                    fields: values,
                },
            ) if def.is_struct()
                && def.did().is_local()
                && name == actual
                && fields.len() == values.len()
                && def.non_enum_variant().fields.len() == fields.len() =>
            {
                for ((field, (name, shape)), (actual, value)) in def
                    .non_enum_variant()
                    .fields
                    .iter()
                    .zip(fields)
                    .zip(values.iter())
                {
                    if field.name.as_str() != name || actual != name {
                        return Err("mutable product replacement field identity differs".into());
                    }
                    self.product_replacements(
                        field.ty(self.tcx, args).skip_norm_wip(),
                        shape,
                        value,
                        conditions,
                        output,
                    )?;
                }
            }
            _ => {
                return Err(
                    "mutable product replacement differs from exact compiler product".into(),
                );
            }
        }
        Ok(())
    }

    pub(super) fn mutable_product_arguments(
        &self,
        values: &[Value],
        memory: &Memory,
    ) -> Result<bool, String> {
        for value in values {
            if let Value::MutableU16 { id, role } = value
                && !matches!(role, MutableU16Role::Ghost { .. })
                && self.mutable_product_owner(*id, memory)?
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn mutable_product_unbound_contracts(
        &mut self,
        instance: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        if self
            .configured_contracts(instance)?
            .iter()
            .any(|contract| !matches!(contract.kind, ContractKind::NoPanic))
            || self
                .specification(instance)?
                .is_some_and(|spec| !spec.arguments.is_empty())
        {
            return Err("mutable product contracts/specification snapshots are unsupported".into());
        }
        Ok(())
    }

    pub(super) fn mutable_product_entry_observations(
        &mut self,
        instance: ty::Instance<'tcx>,
        arguments: &[Value],
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<Vec<Value>, String> {
        if !self.mutable_product_arguments(arguments, memory)? {
            return self.snapshots(arguments, memory, conditions);
        }
        self.mutable_product_unbound_contracts(instance)?;
        arguments
            .iter()
            .map(|value| {
                if let Value::MutableU16 {
                    id,
                    role: MutableU16Role::Root,
                } = value
                    && self.mutable_product_owner(*id, memory)?
                {
                    self.mutable_product_length(value, memory, conditions)?;
                    // Diagnostics retain the live owner id only. It is not original payload or a
                    // contract snapshot; replay of these arbitrary product inputs is unsupported.
                    Ok(value.clone())
                } else {
                    self.snapshot(value, memory, conditions, 0)
                }
            })
            .collect()
    }
}

#[cfg(test)]
#[path = "mutable_products_probe.rs"]
mod probe;

#[cfg(test)]
#[path = "mutable_product_children_probe.rs"]
mod children_probe;
