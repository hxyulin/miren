//! Direct incoming mutable primitive roots; Float requires exact producer-pair authority.
//! Metadata and ghosts have no data-write authority.
use super::*;
use symbolic::MutableU16Role;

#[cfg(test)]
#[path = "typed_constant_index_probe.rs"]
mod constant_index_probe;

const CONSTANT_INDEX_ENABLED: bool = true;

fn constant_index_enabled() -> bool {
    #[cfg(test)]
    if CONSTANT_INDEX_TEST_ENABLED.with(std::cell::Cell::get) {
        return true;
    }
    CONSTANT_INDEX_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static CONSTANT_INDEX_TEST_ENABLED: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct ConstantIndexTestEnabled(bool);

#[cfg(test)]
impl ConstantIndexTestEnabled {
    fn enable() -> Self {
        Self(CONSTANT_INDEX_TEST_ENABLED.with(|value| value.replace(true)))
    }
}

#[cfg(test)]
impl Drop for ConstantIndexTestEnabled {
    fn drop(&mut self) {
        CONSTANT_INDEX_TEST_ENABLED.with(|value| value.set(self.0));
    }
}

#[derive(Clone, Copy, Debug)]
enum TypedElementProjection {
    Local(rustc_middle::mir::Local),
    Constant {
        offset: u64,
        minimum: u64,
        from_end: bool,
    },
}

fn typed_element_projection(place: Place<'_>) -> Option<TypedElementProjection> {
    match place.projection.as_ref() {
        [ProjectionElem::Deref, ProjectionElem::Index(index)] => {
            Some(TypedElementProjection::Local(*index))
        }
        [
            ProjectionElem::Deref,
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            },
        ] if constant_index_enabled() => Some(TypedElementProjection::Constant {
            offset: *offset,
            minimum: *min_length,
            from_end: *from_end,
        }),
        _ => None,
    }
}

#[derive(Clone, Debug)]
pub(super) enum ElementCodec<'tcx> {
    Scalar(symbolic::ScalarSliceElement),
    Product(super::composite_slices::CompositeType<'tcx>),
}

// Representation conversion only; this issues no certificate, owner or lease.
impl<'tcx> From<super::composite_slices::CompositeType<'tcx>> for ElementCodec<'tcx> {
    fn from(product: super::composite_slices::CompositeType<'tcx>) -> Self {
        Self::Product(product)
    }
}

impl ElementCodec<'_> {
    fn scalar(&self) -> Result<symbolic::ScalarSliceElement, String> {
        match self {
            Self::Scalar(element) => Ok(*element),
            Self::Product(product) => Err(format!(
                "mutable product codec cannot enter scalar authority: {:?}",
                product.ty
            )),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(super) enum Storage {
    Scalar(Term),
    Product(Vec<Term>),
}

// Representation conversion only; these columns grant no tracked Memory authority.
impl From<Vec<Term>> for Storage {
    fn from(columns: Vec<Term>) -> Self {
        Self::Product(columns)
    }
}

impl Storage {
    pub(super) fn scalar(&self) -> Result<&Term, &'static str> {
        match self {
            Self::Scalar(data) => Ok(data),
            Self::Product(_) => Err("mutable product columns cannot enter scalar authority"),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct IntegerCertificate<'tcx> {
    pub(super) original: Ty<'tcx>,
    pub(super) codec: ElementCodec<'tcx>,
    pub(super) bytes: u64,
    pub(super) alignment: u64,
}

#[derive(Clone, Debug)]
pub(super) struct Backing {
    pub(super) certificate: usize,
    pub(super) allocation: usize,
    pub(super) length: Value,
    pub(super) data: Storage,
    pub(super) generation: u64,
    pub(super) phase: super::mutable_u16_children::Phase,
    pub(super) interval: Option<super::mutable_interval::Descriptor>,
    pub(super) hierarchy: Option<super::mutable_hierarchy::Hierarchy>,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn mutable_u16_type(&self, original: Ty<'tcx>) -> bool {
        matches!(original.kind(), ty::Ref(_, inner, mutability)
            if mutability.is_mut() && matches!(inner.kind(), ty::Slice(element)
                if self.mutable_integer_element(*element) || self.mutable_product_kind(*element)))
    }

    fn mutable_integer_element(&self, original: Ty<'tcx>) -> bool {
        matches!(
            original.kind(),
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_)
        ) && original != self.tcx.types.u8
            || (super::float_pairs::ENABLE_MUTABLE_FLOAT
                && matches!(
                    original.kind(),
                    ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64)
                ))
    }

    fn mutable_integer_certificate(&self, id: usize) -> Result<&IntegerCertificate<'tcx>, String> {
        let certificate = self
            .mutable_integer_types
            .get(id)
            .ok_or("mutable integer element certificate was not issued")?;
        if !self.mutable_integer_element(certificate.original) {
            return Err("mutable integer certificate has an unsupported original type".into());
        }
        let layout = self.static_layout(certificate.original)?;
        if (certificate.original == self.tcx.types.bool
            && (layout.size.bytes() != 1 || layout.align.abi.bytes() != 1))
            || (certificate.original == self.tcx.types.char
                && (layout.size.bytes() != 4 || layout.align.abi.bytes() != 4))
            || self.scalar_slice_element(certificate.original)? != Some(certificate.codec.scalar()?)
            || layout.size.bytes() != certificate.bytes
            || layout.align.abi.bytes() != certificate.alignment
        {
            return Err("mutable integer certificate differs from original compiler layout".into());
        }
        Ok(certificate)
    }

    pub(super) fn mutable_owner_certificate(
        &self,
        id: usize,
    ) -> Result<&IntegerCertificate<'tcx>, String> {
        match &self
            .mutable_integer_types
            .get(id)
            .ok_or("mutable owner certificate was not issued")?
            .codec
        {
            ElementCodec::Scalar(_) => self.mutable_integer_certificate(id),
            ElementCodec::Product(_) => self.mutable_product_certificate(id),
        }
    }

    pub(super) fn mutable_owner_type(&self, original: Ty<'tcx>, element: Ty<'tcx>) -> bool {
        matches!(original.kind(), ty::Ref(_, inner, mutability)
            if mutability.is_mut()
                && matches!(inner.kind(), ty::Slice(actual) if *actual == element))
    }

    pub(super) fn mutable_integer_pending_message(
        &self,
        certificate: usize,
    ) -> Result<&'static str, String> {
        Ok(
            if self.mutable_integer_certificate(certificate)?.original == self.tcx.types.u16 {
                "mutable u16 staging needs a pending child"
            } else if self.mutable_integer_certificate(certificate)?.original == self.tcx.types.bool
            {
                "mutable bool staging needs a pending child"
            } else if self.mutable_integer_certificate(certificate)?.original == self.tcx.types.char
            {
                "mutable char staging needs a pending child"
            } else if self
                .float_type(self.mutable_integer_certificate(certificate)?.original)
                .is_some()
            {
                "mutable float staging needs a pending child"
            } else {
                "mutable integer staging needs a pending child"
            },
        )
    }

    pub(super) fn mutable_u16_matches(
        &self,
        original: Ty<'tcx>,
        id: usize,
        memory: &Memory,
        mutable: bool,
    ) -> Result<bool, String> {
        let backing = self.mutable_u16_backing(id, memory)?;
        let expected = match &backing.data {
            Storage::Scalar(_) => {
                self.mutable_integer_certificate(backing.certificate)?
                    .original
            }
            Storage::Product(_) => {
                self.mutable_product_certificate(backing.certificate)?
                    .original
            }
        };
        Ok(matches!(original.kind(), ty::Ref(_, inner, mutability)
            if mutability.is_mut() == mutable && matches!(inner.kind(), ty::Slice(element)
                if *element == expected)))
    }

    pub(super) fn mutable_u16_float_domain(
        &self,
        id: usize,
        memory: &Memory,
    ) -> Result<bool, String> {
        let backing = self.mutable_u16_backing(id, memory)?;
        match &backing.data {
            Storage::Scalar(_) => Ok(matches!(
                self.mutable_integer_certificate(backing.certificate)?
                    .codec
                    .scalar()?,
                symbolic::ScalarSliceElement::Float { .. }
            )),
            Storage::Product(_) => {
                let certificate = self.mutable_owner_certificate(backing.certificate)?;
                let ElementCodec::Product(product) = &certificate.codec else {
                    return Err("mutable product float inventory differs from its storage".into());
                };
                Ok(product
                    .leaves
                    .iter()
                    .any(|leaf| matches!(leaf, symbolic::ScalarSliceElement::Float { .. })))
            }
        }
    }

    fn mutable_u16_error(&self, detail: &str) -> String {
        self.categorized_error(UnknownCategory::Semantics, detail.into())
    }

    pub(super) fn mutable_u16_input(
        &mut self,
        original: Ty<'tcx>,
        memory: &mut Memory,
        conditions: &mut Vec<Term>,
    ) -> Result<Value, String> {
        if self.mutable_product_kind(original) {
            return self.mutable_product_input(original, memory, conditions);
        }
        if memory.storage_slots().saturating_add(2) > MAX_INPUT_VALUES
            || self.input_values.saturating_add(2) > MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable u16 root exceeds existing storage budget".into(),
            ));
        }
        if !self.mutable_integer_element(original) {
            return Err("mutable integer input needs exact admitted primitive".into());
        }
        let element = self
            .scalar_slice_element(original)?
            .ok_or("mutable integer codec is unavailable")?;
        let layout = self.static_layout(original)?;
        let certificate = if let Some(id) = self
            .mutable_integer_types
            .iter()
            .position(|certificate| certificate.original == original)
        {
            id
        } else {
            if self.mutable_integer_types.len() >= MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "mutable integer certificates exceed existing budget".into(),
                ));
            }
            let id = self.mutable_integer_types.len();
            self.mutable_integer_types.push(IntegerCertificate {
                original,
                codec: ElementCodec::Scalar(element),
                bytes: layout.size.bytes(),
                alignment: layout.align.abi.bytes(),
            });
            id
        };
        if matches!(element, symbolic::ScalarSliceElement::Float { .. }) {
            self.float_pairs.activate();
        }
        self.input_values += 2;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let length = self.fresh(Sort::BitVec(bits));
        let max = ((1_u128 << (bits - 1)) - 1) / u128::from(layout.size.bytes());
        conditions.push(self.terms.apply(
            Op::BvUnsignedLe,
            &[length.clone(), self.terms.bit_vector(max, bits)?],
        )?);
        let data = self.fresh(Sort::Array(
            Box::new(Sort::BitVec(bits)),
            Box::new(super::scalar_slices::scalar_slice_sort(element)?),
        ));
        let allocation = memory.len();
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
            data: Storage::Scalar(data),
            generation: 0,
            phase: super::mutable_u16_children::Phase::Idle,
            interval: None,
            hierarchy: None,
        });
        Ok(Value::MutableU16 {
            id,
            role: MutableU16Role::Root,
        })
    }

    pub(super) fn mutable_u16_backing<'a>(
        &self,
        id: usize,
        memory: &'a Memory,
    ) -> Result<&'a Backing, String> {
        let backing = memory
            .mutable_u16
            .get(id)
            .ok_or("mutable u16 root identity was not issued")?;
        if matches!(self.mutable_integer_types.get(backing.certificate),
            Some(certificate) if self.mutable_product_kind(certificate.original))
        {
            return self.mutable_product_backing(id, memory);
        }
        if backing.hierarchy.is_some() && memory.mutable_hierarchy != Some(id) {
            return Err("hierarchy backing has no authenticated Memory namespace".into());
        }
        self.mutable_hierarchy_scope_backing(backing)?;
        memory.check_projection_initialization(backing.allocation, &[])?;
        if !matches!(memory.get(backing.allocation), Some(Some(Value::Unit))) {
            return Err(self.mutable_u16_error("mutable u16 root backing is unavailable"));
        }
        self.mutable_u16_terms(backing.certificate, &backing.length, backing.data.scalar()?)?;
        self.validate_mutable_interval(id, backing)?;
        Ok(backing)
    }

    pub(super) fn mutable_interval_element(&self, certificate: usize) -> Result<Ty<'tcx>, String> {
        Ok(self.mutable_integer_certificate(certificate)?.original)
    }

    fn mutable_u16_terms(
        &self,
        certificate: usize,
        length: &Value,
        data: &Term,
    ) -> Result<(), String> {
        let element = self
            .mutable_integer_certificate(certificate)?
            .codec
            .scalar()?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let (term, width, signed) = length.integer()?;
        if width != bits
            || signed
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
            || data.sort()
                != &Sort::Array(
                    Box::new(Sort::BitVec(bits)),
                    Box::new(super::scalar_slices::scalar_slice_sort(element)?),
                )
            || !data.belongs_to(&self.terms)
        {
            return Err("mutable u16 backing has a different width, sort or context".into());
        }
        Ok(())
    }

    pub(super) fn mutable_u16_length(
        &self,
        value: &Value,
        memory: &Memory,
    ) -> Result<Value, String> {
        let Value::MutableU16 { id, role } = value else {
            return Err("expected a private mutable u16 role".into());
        };
        match role {
            MutableU16Role::Root
            | MutableU16Role::Metadata { .. }
            | MutableU16Role::Child { .. }
            | MutableU16Role::ChildMetadata { .. }
            | MutableU16Role::HierarchyChild { .. }
            | MutableU16Role::HierarchyMetadata { .. } => {
                self.mutable_u16_role_live(*id, role, memory)?;
                let backing = self.mutable_u16_backing(*id, memory)?;
                if matches!(backing.data, Storage::Product(_)) {
                    return Err("mutable product length requires current path conditions".into());
                }
                Ok(backing
                    .interval
                    .as_ref()
                    .map_or_else(|| backing.length.clone(), |view| view.length().clone()))
            }
            MutableU16Role::Ghost {
                certificate,
                element,
                length,
                data,
            } => {
                self.mutable_u16_terms(*certificate, length, data)?;
                if self
                    .mutable_integer_certificate(*certificate)?
                    .codec
                    .scalar()?
                    != *element
                {
                    return Err("mutable integer ghost codec differs from its certificate".into());
                }
                Ok((**length).clone())
            }
        }
    }

    pub(super) fn mutable_u16_snapshot(
        &self,
        value: &Value,
        memory: &Memory,
    ) -> Result<Value, String> {
        let Value::MutableU16 { id, role } = value else {
            return Err("expected mutable u16 snapshot source".into());
        };
        match role {
            MutableU16Role::Root
            | MutableU16Role::Child { .. }
            | MutableU16Role::HierarchyChild { .. } => {
                self.mutable_u16_role_live(*id, role, memory)?;
                let backing = self.mutable_u16_backing(*id, memory)?;
                Ok(Value::MutableU16 {
                    id: *id,
                    role: MutableU16Role::Ghost {
                        certificate: backing.certificate,
                        element: self
                            .mutable_integer_certificate(backing.certificate)?
                            .codec
                            .scalar()?,
                        length: Box::new(
                            backing.interval.as_ref().map_or_else(
                                || backing.length.clone(),
                                |view| view.length().clone(),
                            ),
                        ),
                        data: backing.data.scalar()?.clone(),
                    },
                })
            }
            MutableU16Role::HierarchyMetadata { .. } => {
                self.mutable_u16_role_live(*id, role, memory)?;
                let backing = self.mutable_u16_backing(*id, memory)?;
                Ok(Value::MutableU16 {
                    id: *id,
                    role: MutableU16Role::Ghost {
                        certificate: backing.certificate,
                        element: self
                            .mutable_integer_certificate(backing.certificate)?
                            .codec
                            .scalar()?,
                        length: Box::new(backing.length.clone()),
                        data: backing.data.scalar()?.clone(),
                    },
                })
            }
            MutableU16Role::Metadata { .. } | MutableU16Role::ChildMetadata { .. } => {
                self.mutable_u16_role_live(*id, role, memory)?;
                self.mutable_u16_backing(*id, memory)?;
                Ok(value.clone())
            }
            MutableU16Role::Ghost {
                certificate,
                element,
                length,
                data,
            } => {
                self.mutable_u16_terms(*certificate, length, data)?;
                if self
                    .mutable_integer_certificate(*certificate)?
                    .codec
                    .scalar()?
                    != *element
                {
                    return Err("mutable integer ghost codec differs from its certificate".into());
                }
                Ok(value.clone())
            }
        }
    }

    pub(super) fn mutable_u16_read(
        &self,
        body: Option<&Body<'tcx>>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(None);
        }
        if let Some(value) = self.mutable_product_read(body, state, place)? {
            return Ok(Some(value));
        }
        let value = self.raw_local(state, place.local.as_usize())?;
        let Value::MutableU16 { id, role } = value else {
            return Ok(None);
        };
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        self.mutable_u16_role_live(id, &role, &state.memory)?;
        if place.projection.is_empty() {
            return Ok(Some(Value::MutableU16 { id, role }));
        }
        if !matches!(
            role,
            MutableU16Role::Root
                | MutableU16Role::Child { .. }
                | MutableU16Role::HierarchyChild { .. }
        ) {
            return Err(self.mutable_u16_error("mutable u16 metadata cannot observe data"));
        }
        let Some(projection) = typed_element_projection(place) else {
            return Err(self.mutable_u16_error("mutable u16 root needs direct element observation"));
        };
        let body = body.ok_or("mutable u16 data observation needs original compiler Body")?;
        if !self.mutable_u16_matches(body.local_decls[place.local].ty, id, &state.memory, true)?
            || matches!(projection, TypedElementProjection::Local(index)
                if body.local_decls[index].ty != self.tcx.types.usize)
            || place.ty(&body.local_decls, self.tcx).ty
                != self
                    .mutable_integer_certificate(backing.certificate)?
                    .original
        {
            return Err("mutable u16 element differs from original compiler type".into());
        }
        let index = match projection {
            TypedElementProjection::Local(index) => self.local(state, index.as_usize())?,
            TypedElementProjection::Constant {
                offset,
                minimum,
                from_end,
            } => self.mutable_constant_index(
                id,
                backing,
                offset,
                minimum,
                from_end,
                &state.conditions,
            )?,
        };
        let index = self.mutable_interval_index(id, backing, index, &state.conditions)?;
        Ok(Some(super::scalar_slices::decode_scalar_element(
            &self.terms,
            self.mutable_integer_certificate(backing.certificate)?
                .codec
                .scalar()?,
            self.terms.apply(
                Op::Select,
                &[backing.data.scalar()?.clone(), index.integer()?.0.clone()],
            )?,
        )?))
    }

    fn mutable_constant_index(
        &self,
        id: usize,
        backing: &Backing,
        offset: u64,
        minimum: u64,
        from_end: bool,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let maximum = match bits {
            32 => u64::from(u32::MAX),
            64 => u64::MAX,
            _ => {
                return Err(self.mutable_u16_error(
                    "typed constant index needs original 32/64-bit target usize",
                ));
            }
        };
        if offset > maximum || minimum > maximum {
            return Err(self
                .mutable_u16_error("typed constant index metadata exceeds original target usize"));
        }
        if (!from_end && offset >= minimum) || (from_end && (offset == 0 || offset > minimum)) {
            return Err(self.mutable_u16_error(
                "typed constant index metadata is outside its compiler relation",
            ));
        }
        self.validate_mutable_interval(id, backing)?;
        let length = backing
            .interval
            .as_ref()
            .map_or(&backing.length, |view| view.length());
        let (term, width, signed) = length.integer()?;
        if width != bits
            || signed
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
        {
            return Err(self.mutable_u16_error(
                "typed constant index extent needs original target usize context",
            ));
        }
        let minimum = symbolic::integer(&self.terms, u128::from(minimum), bits, false);
        let enough = symbolic::binary(&self.terms, "le", minimum, length.clone())?.boolean()?;
        let mut denied = conditions.to_vec();
        denied.push(symbolic::not(&enough));
        if self.feasible(&denied)? {
            return Err(self.mutable_u16_error(
                "typed constant index minimum is not established for current view",
            ));
        }
        let offset = symbolic::integer(&self.terms, u128::from(offset), bits, false);
        if !from_end {
            return Ok(offset);
        }
        let inside =
            symbolic::binary(&self.terms, "le", offset.clone(), length.clone())?.boolean()?;
        let mut denied = conditions.to_vec();
        denied.push(symbolic::not(&inside));
        if self.feasible(&denied)? {
            return Err(
                self.mutable_u16_error("typed constant index reverse offset exceeds current view")
            );
        }
        symbolic::binary(&self.terms, "sub", length.clone(), offset)
    }

    pub(super) fn mutable_u16_index(
        &self,
        index: &Value,
        length: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let (term, bits, signed) = index.integer()?;
        if bits != u32::from(self.tcx.sess.target.pointer_width)
            || signed
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
        {
            return Err("mutable u16 index requires original target usize context".into());
        }
        let in_bounds = symbolic::binary(&self.terms, "lt", index.clone(), length.clone())?;
        if self.feasible(
            &[
                conditions.to_vec(),
                vec![symbolic::not(&in_bounds.boolean()?)],
            ]
            .concat(),
        )? {
            return Err(self.mutable_u16_error("mutable u16 index bounds are not established"));
        }
        Ok(())
    }

    pub(super) fn mutable_u16_store(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        place: Place<'tcx>,
        replacement: &Value,
    ) -> Result<bool, String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(false);
        }
        if self.mutable_product_store(body, state, place, replacement)? {
            return Ok(true);
        }
        let Ok(root) = self.raw_local(state, place.local.as_usize()) else {
            return Ok(false);
        };
        let Value::MutableU16 { id, role } = root else {
            return Ok(false);
        };
        if place.projection.is_empty() {
            return if matches!(
                role,
                MutableU16Role::Root
                    | MutableU16Role::Child { .. }
                    | MutableU16Role::HierarchyChild { .. }
            ) {
                Err(self.mutable_u16_error("mutable u16 root assignment transport is unsupported"))
            } else {
                Ok(false)
            };
        }
        if !matches!(
            role,
            MutableU16Role::Root
                | MutableU16Role::Child { .. }
                | MutableU16Role::HierarchyChild { .. }
        ) {
            return Err(self.mutable_u16_error("mutable u16 metadata has no write authority"));
        }
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        self.mutable_u16_role_live(id, &role, &state.memory)?;
        let Some(projection) = typed_element_projection(place) else {
            return Err(self.mutable_u16_error("mutable u16 store requires direct whole element"));
        };
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        if !self.mutable_u16_matches(body.local_decls[place.local].ty, id, &state.memory, true)?
            || matches!(projection, TypedElementProjection::Local(index)
                if body.local_decls[index].ty != self.tcx.types.usize)
            || place.ty(&body.local_decls, self.tcx).ty
                != self
                    .mutable_integer_certificate(backing.certificate)?
                    .original
        {
            return Err("mutable u16 store differs from original compiler type".into());
        }
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let index = match projection {
            TypedElementProjection::Local(index) => self.local(state, index.as_usize())?,
            TypedElementProjection::Constant {
                offset,
                minimum,
                from_end,
            } => self.mutable_constant_index(
                id,
                backing,
                offset,
                minimum,
                from_end,
                &state.conditions,
            )?,
        };
        let index = self.mutable_interval_index(id, backing, index, &state.conditions)?;
        let certificate = self.mutable_integer_certificate(backing.certificate)?;
        let term = self.mutable_scalar_replacement(certificate, replacement)?;
        if certificate.original == self.tcx.types.char {
            self.prove_char_value(replacement, &state.conditions)?;
        }
        if let symbolic::ScalarSliceElement::Float { bits } = certificate.codec.scalar()? {
            self.prove_float_pair(replacement, bits, &state.conditions)?;
        }
        let data = self.terms.apply(
            Op::Store,
            &[
                backing.data.scalar()?.clone(),
                index.integer()?.0.clone(),
                term.clone(),
            ],
        )?;
        std::rc::Rc::make_mut(&mut state.memory.mutable_u16)[id].data = Storage::Scalar(data);
        Ok(true)
    }

    pub(super) fn mutable_scalar_replacement(
        &self,
        certificate: &IntegerCertificate<'tcx>,
        replacement: &Value,
    ) -> Result<Term, String> {
        if certificate.codec.scalar()? == symbolic::ScalarSliceElement::Bool {
            let Value::Bool(term) = replacement else {
                return Err(
                    "mutable Bool replacement requires logical Bool in current context".into(),
                );
            };
            if certificate.original != self.tcx.types.bool
                || term.sort() != &Sort::Bool
                || !term.belongs_to(&self.terms)
            {
                return Err(
                    "mutable Bool replacement differs from issued type, sort or context".into(),
                );
            }
            return Ok(term.clone());
        }
        if let symbolic::ScalarSliceElement::Float { bits } = certificate.codec.scalar()? {
            if self.float_type(certificate.original) != Some(bits) {
                return Err("mutable Float replacement differs from original compiler type".into());
            }
            self.validate_float_pair(replacement, bits)?;
            let Value::Float {
                raw_bits: Some(raw),
                ..
            } = replacement
            else {
                return Err("mutable Float replacement requires exact encoded producer".into());
            };
            return Ok(raw.clone());
        }
        if certificate.codec.scalar()? == symbolic::ScalarSliceElement::Char {
            let (term, bits, signed) = replacement.integer()?;
            if certificate.original != self.tcx.types.char
                || bits != 32
                || signed
                || term.sort() != &Sort::BitVec(32)
                || !term.belongs_to(&self.terms)
            {
                return Err(
                    "mutable Char replacement differs from issued type, sort or context".into(),
                );
            }
            return Ok(term.clone());
        }
        let (term, bits, signed) = replacement.integer()?;
        let symbolic::ScalarSliceElement::Integer {
            bits: expected_bits,
            signed: expected_signed,
        } = certificate.codec.scalar()?
        else {
            return Err("mutable integer replacement certificate has a different kind".into());
        };
        if bits != expected_bits
            || signed != expected_signed
            || term.sort() != &Sort::BitVec(expected_bits)
            || !term.belongs_to(&self.terms)
        {
            return Err(if certificate.original == self.tcx.types.u16 {
                "mutable u16 replacement requires unsigned BV16 in current context".into()
            } else {
                "mutable integer replacement differs from issued width, sign or context".into()
            });
        }
        Ok(term.clone())
    }

    pub(super) fn mutable_u16_metadata(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
    ) -> Result<Option<Value>, String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(None);
        }
        if let Some(value) = self.mutable_product_metadata(body, state, place)? {
            return Ok(Some(value));
        }
        let root = self.raw_local(state, place.local.as_usize())?;
        let Value::MutableU16 { id, role } = root else {
            return Ok(None);
        };
        if !matches!(
            role,
            MutableU16Role::Root
                | MutableU16Role::Child { .. }
                | MutableU16Role::HierarchyChild { .. }
        ) || place.projection.as_ref() != [ProjectionElem::Deref]
            || !self.mutable_u16_matches(
                body.local_decls[place.local].ty,
                id,
                &state.memory,
                true,
            )?
        {
            return Err(self.mutable_u16_error("mutable u16 metadata needs original direct root"));
        }
        self.check_local_initialization(state, place.local.as_usize(), &[])?;
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        self.mutable_u16_role_live(id, &role, &state.memory)?;
        Ok(Some(Value::MutableU16 {
            id,
            role: match role {
                MutableU16Role::Child { generation } => {
                    MutableU16Role::ChildMetadata { generation }
                }
                MutableU16Role::Root => match &backing.hierarchy {
                    Some(h) => MutableU16Role::HierarchyMetadata {
                        lease: 0,
                        epoch: h.metadata_epoch(0)?,
                    },
                    None => MutableU16Role::Metadata {
                        generation: backing.generation,
                    },
                },
                MutableU16Role::HierarchyChild { lease } => {
                    let epoch = backing
                        .hierarchy
                        .as_ref()
                        .ok_or("hierarchy missing")?
                        .metadata_epoch(lease)?;
                    MutableU16Role::HierarchyMetadata { lease, epoch }
                }
                MutableU16Role::Metadata { .. }
                | MutableU16Role::ChildMetadata { .. }
                | MutableU16Role::HierarchyMetadata { .. }
                | MutableU16Role::Ghost { .. } => {
                    return Err("mutable u16 metadata source has no data authority".into());
                }
            },
        }))
    }
    pub(super) fn mutable_u16_store_role(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        value: &Value,
    ) -> Result<(), String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(());
        }
        if self.mutable_product_store_role(body, state, place, value)? {
            return Ok(());
        }
        if self.mutable_u16_contains(value, &state.memory)?
            && !matches!(value, Value::MutableU16 { .. })
        {
            return Err(self.mutable_u16_error("mutable u16 roles cannot enter aggregate storage"));
        }
        if let Value::MutableU16 { id, role } = value {
            if matches!(
                role,
                MutableU16Role::Child { .. } | MutableU16Role::HierarchyChild { .. }
            ) {
                return self.mutable_u16_staging_store(body, state, place, *id, role);
            }
            if !matches!(
                role,
                MutableU16Role::Metadata { .. }
                    | MutableU16Role::ChildMetadata { .. }
                    | MutableU16Role::HierarchyMetadata { .. }
            ) || !place.projection.is_empty()
                || place.local.as_usize() <= body.arg_count
                || state.addresses[place.local.as_usize()].is_some()
            {
                return Err(
                    self.mutable_u16_error("mutable u16 roles need private metadata temporary")
                );
            }
            let original = body.local_decls[place.local].ty;
            let inner = match original.kind() {
                ty::Ref(_, inner, mutability) if !mutability.is_mut() => *inner,
                ty::RawPtr(inner, mutability) if !mutability.is_mut() => *inner,
                _ => return Err("mutable u16 metadata destination has a different type".into()),
            };
            if !matches!(inner.kind(), ty::Slice(element)
                if *element == self.mutable_integer_certificate(
                    self.mutable_u16_backing(*id, &state.memory)?.certificate)?.original)
            {
                return Err("mutable u16 metadata destination needs original u16 slice".into());
            }
            self.mutable_u16_backing(*id, &state.memory)?;
            self.mutable_u16_role_live(*id, role, &state.memory)?;
        }
        Ok(())
    }

    pub(super) fn mutable_u16_call_allowed(
        &self,
        body: &Body<'tcx>,
        state: &State,
        instance: ty::Instance<'tcx>,
        args: &[rustc_span::Spanned<Operand<'tcx>>],
    ) -> Result<(), String> {
        if state.memory.mutable_u16.is_empty() {
            return Ok(());
        }
        for arg in args {
            if let Operand::Copy(place) | Operand::Move(place) = arg.node {
                let value = self.read_place(state, place, Some(body))?;
                if self.mutable_u16_contains(&value, &state.memory)?
                    && !matches!(value, Value::MutableU16 { .. })
                {
                    return Err(self.mutable_u16_error(
                        "mutable u16 roles cannot enter ordinary aggregate calls",
                    ));
                }
                if let Value::MutableU16 { id, role } = value {
                    if self.mutable_product_owner(id, &state.memory)? {
                        state.flow.require_unarmed()?;
                        self.mutable_product_frame(body, id, &role, &state.memory)?;
                    }
                    self.check_local_initialization(state, place.local.as_usize(), &[])?;
                    self.mutable_u16_backing(id, &state.memory)?;
                    if args.len() != 1
                        || !place.projection.is_empty()
                        || !matches!(
                            role,
                            MutableU16Role::Metadata { .. }
                                | MutableU16Role::ChildMetadata { .. }
                                | MutableU16Role::HierarchyMetadata { .. }
                        )
                        || !self.mutable_metadata_operation(instance)
                        || !self.mutable_u16_matches(
                            body.local_decls[place.local].ty,
                            id,
                            &state.memory,
                            false,
                        )?
                    {
                        return Err(self.mutable_u16_error(
                            "mutable u16 roles require selected metadata-only operation",
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    pub(super) fn certify_mutable_u16_len(
        &mut self,
        instance: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        let core = self
            .tcx
            .lang_items()
            .sized_trait()
            .ok_or("core identity is unavailable")?
            .krate;
        if self.tcx.lang_items().get(LangItem::SliceLen) != Some(instance.def_id())
            || instance.def_id().krate != core
        {
            return Err("mutable u16 length requires actual core SliceLen identity".into());
        }
        let signature = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate(self.tcx, instance.args)
            .skip_binder();
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.output() != self.tcx.types.usize
            || signature.inputs().len() != 1
            || !matches!(signature.inputs()[0].kind(), ty::Ref(_, inner, mutability)
                if !mutability.is_mut() && matches!(inner.kind(), ty::Slice(element)
                    if self.mutable_integer_element(*element)
                        || self.mutable_product_shape(*element)?.is_some()))
        {
            return Err("mutable u16 SliceLen has a different original signature".into());
        }
        let ty::Ref(_, signature_slice, _) = signature.inputs()[0].kind() else {
            return Err("mutable integer SliceLen receiver differs".into());
        };
        let ty::Slice(signature_element) = signature_slice.kind() else {
            return Err("mutable integer SliceLen element differs".into());
        };
        let body = self.instantiated_body(instance)?;
        if body.arg_count != 1
            || body.local_decls.len() != 2
            || body.basic_blocks.len() != 1
            || body.local_decls[rustc_middle::mir::RETURN_PLACE].ty != self.tcx.types.usize
            || !matches!(body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty.kind(),
                ty::Ref(_, inner, mutability) if !mutability.is_mut()
                    && matches!(inner.kind(), ty::Slice(element) if element == signature_element))
        {
            return Err("mutable u16 SliceLen body has a different original schema".into());
        }
        let block = &body.basic_blocks[START_BLOCK];
        let [statement] = block.statements.as_slice() else {
            return Err("mutable u16 SliceLen body has extra effects".into());
        };
        if block.is_cleanup || !matches!(block.terminator().kind, TerminatorKind::Return) {
            return Err("mutable u16 SliceLen body does not return its metadata directly".into());
        }
        let StatementKind::Assign(assignment) = &statement.kind else {
            return Err("mutable u16 SliceLen body has a different statement".into());
        };
        let (destination, value) = assignment.as_ref();
        if destination.local != rustc_middle::mir::RETURN_PLACE
            || !destination.projection.is_empty()
            || !matches!(value, Rvalue::UnaryOp(UnOp::PtrMetadata, Operand::Copy(source))
                if source.local.as_usize() == 1 && source.projection.is_empty())
        {
            return Err("mutable u16 SliceLen does not return the exact receiver metadata".into());
        }
        Ok(())
    }
    pub(super) fn mutable_u16_contains(
        &self,
        value: &Value,
        memory: &Memory,
    ) -> Result<bool, String> {
        let mut pending = vec![(value, 0_usize)];
        let mut visited = Vec::new();
        let mut nodes = 0_usize;
        while let Some((value, depth)) = pending.pop() {
            nodes += 1;
            if nodes > 512 || depth >= 16 || nodes + pending.len() > 512 {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "mutable u16 role traversal exceeds existing node/depth budget".into(),
                ));
            }
            let children = match value {
                Value::Tuple(fields) => fields.len(),
                Value::Elements(fields) => fields.len(),
                Value::Adt { fields, .. } => fields.len(),
                Value::Enum { variants, .. } => variants.len().saturating_add(1),
                Value::StaticSlice { elements, .. } => elements.len().saturating_add(1),
                Value::SliceIterator { unchecked, .. } => unchecked.len().saturating_add(3),
                Value::RawSlice { .. } => 2,
                _ => 1,
            };
            if nodes.saturating_add(pending.len()).saturating_add(children) > 512 {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "mutable u16 role traversal exceeds existing node budget".into(),
                ));
            }
            match value {
                Value::OwnedArrayIterator { .. } => {
                    return Err("owned array iterator requires its private typed protocol".into());
                }
                Value::MutableU16 { .. } => return Ok(true),
                Value::Tuple(fields) => pending.extend(fields.iter().map(|v| (v, depth + 1))),
                Value::Elements(fields) => pending.extend(fields.iter().map(|v| (v, depth + 1))),
                Value::Adt { fields, .. } => {
                    pending.extend(fields.iter().map(|(_, v)| (v, depth + 1)))
                }
                Value::Enum {
                    discriminant,
                    variants,
                    ..
                } => {
                    pending.push((discriminant, depth + 1));
                    pending.extend(variants.iter().map(|v| (v, depth + 1)));
                }
                Value::Reference {
                    allocation,
                    projection,
                    ..
                } => {
                    memory.check_projection_initialization(*allocation, projection)?;
                    if !visited.contains(allocation) {
                        visited.push(*allocation);
                        if let Some(Some(value)) = memory.get(*allocation) {
                            pending.push((value, depth + 1));
                        } else {
                            return Err("mutable u16 role traversal found dead reference".into());
                        }
                    }
                }
                Value::Cell { allocation } | Value::LocalAtomic { allocation, .. } => {
                    memory.check_projection_initialization(*allocation, &[])?;
                    if !visited.contains(allocation) {
                        visited.push(*allocation);
                        if let Some(Some(value)) = memory.get(*allocation) {
                            pending.push((value, depth + 1));
                        } else {
                            return Err("mutable u16 role traversal found dead storage".into());
                        }
                    }
                }
                Value::StaticSlice {
                    source, elements, ..
                } => {
                    pending.push((source, depth + 1));
                    pending.extend(elements.iter().map(|v| (v, depth + 1)));
                }
                Value::SliceIterator {
                    source,
                    front,
                    back,
                    unchecked,
                    ..
                } => {
                    pending.extend([
                        (source.as_ref(), depth + 1),
                        (front.as_ref(), depth + 1),
                        (back.as_ref(), depth + 1),
                    ]);
                    pending.extend(unchecked.iter().map(|v| (v, depth + 1)));
                }
                Value::RawSlice { source, length } => {
                    pending.extend([(source.as_ref(), depth + 1), (length.as_ref(), depth + 1)]);
                }
                Value::OwnedSnapshot(source)
                | Value::MetadataPointer(source)
                | Value::TraitObject { source, .. }
                | Value::DebugReference { source, .. }
                | Value::TrackedPointer {
                    reference: source, ..
                } => pending.push((source, depth + 1)),
                Value::MaybeUninit { payload, .. } => {
                    if let Some(payload) = payload {
                        pending.push((payload, depth + 1));
                    }
                }
                Value::OwnedRegion { .. }
                | Value::Input(_)
                | Value::Bool(_)
                | Value::Int { .. }
                | Value::Float { .. }
                | Value::Bytes { .. }
                | Value::CompositeSlice { .. }
                | Value::ScalarSlice { .. }
                | Value::Uninitialized
                | Value::StaticView { .. }
                | Value::RawPointer { .. }
                | Value::Atomic { .. }
                | Value::StaticText
                | Value::FormatArguments
                | Value::FunctionPointer { .. }
                | Value::Function
                | Value::Unit => {}
            }
        }
        Ok(false)
    }
}

#[cfg(test)]
pub(super) fn compiler_bool_hierarchy_backing_probe(engine: &mut Engine<'_>, memory: &Memory) {
    let backing = engine.mutable_u16_backing(0, memory).unwrap();
    let certificate = backing.certificate;
    let issued = engine.mutable_integer_types[certificate].clone();
    assert_eq!(issued.original, engine.tcx.types.bool);
    assert_eq!(
        issued.codec.scalar().unwrap(),
        symbolic::ScalarSliceElement::Bool
    );
    assert_eq!((issued.bytes, issued.alignment), (1, 1));
    for original in [
        engine.tcx.types.u8,
        engine.tcx.types.i8,
        engine.tcx.types.char,
    ] {
        engine.mutable_integer_types[certificate].original = original;
        assert!(engine.mutable_u16_backing(0, memory).is_err());
        engine.mutable_integer_types[certificate] = issued.clone();
    }
    for (bytes, alignment) in [(0, 1), (1, 2)] {
        engine.mutable_integer_types[certificate].bytes = bytes;
        engine.mutable_integer_types[certificate].alignment = alignment;
        assert!(engine.mutable_u16_backing(0, memory).is_err());
        engine.mutable_integer_types[certificate] = issued.clone();
    }
    engine.mutable_integer_types[certificate].codec =
        ElementCodec::Scalar(symbolic::ScalarSliceElement::Integer {
            bits: 8,
            signed: false,
        });
    assert!(engine.mutable_u16_backing(0, memory).is_err());
    engine.mutable_integer_types[certificate] = issued;
    let foreign = Context::default();
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    let mut context = memory.clone();
    std::rc::Rc::make_mut(&mut context.mutable_u16)[0].data = super::mutable_u16::Storage::Scalar(
        foreign
            .symbol(
                99,
                Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::Bool)),
            )
            .unwrap(),
    );
    assert!(engine.mutable_u16_backing(0, &context).is_err());
    for wrong in [
        symbolic::integer(&engine.terms, 1, 8, false),
        Value::Bool(engine.terms.bit_vector(1, 8).unwrap()),
        Value::Bool(foreign.boolean(true)),
    ] {
        assert!(
            engine
                .mutable_hierarchy_primitive_value_probe(&wrong)
                .is_err()
        );
    }
}

#[cfg(test)]
pub(super) fn compiler_char_hierarchy_backing_probe(engine: &mut Engine<'_>, memory: &Memory) {
    let backing = engine.mutable_u16_backing(0, memory).unwrap();
    let certificate = backing.certificate;
    let issued = engine.mutable_integer_types[certificate].clone();
    assert_eq!(issued.original, engine.tcx.types.char);
    assert_eq!(
        issued.codec.scalar().unwrap(),
        symbolic::ScalarSliceElement::Char
    );
    assert_eq!((issued.bytes, issued.alignment), (4, 4));
    for original in [
        engine.tcx.types.u32,
        engine.tcx.types.i32,
        engine.tcx.types.bool,
    ] {
        engine.mutable_integer_types[certificate].original = original;
        assert!(engine.mutable_u16_backing(0, memory).is_err());
        engine.mutable_integer_types[certificate] = issued.clone();
    }
    for (bytes, alignment) in [(1, 4), (4, 1)] {
        engine.mutable_integer_types[certificate].bytes = bytes;
        engine.mutable_integer_types[certificate].alignment = alignment;
        assert!(engine.mutable_u16_backing(0, memory).is_err());
        engine.mutable_integer_types[certificate] = issued.clone();
    }
    engine.mutable_integer_types[certificate].codec =
        ElementCodec::Scalar(symbolic::ScalarSliceElement::Integer {
            bits: 32,
            signed: false,
        });
    assert!(engine.mutable_u16_backing(0, memory).is_err());
    engine.mutable_integer_types[certificate] = issued;
    let foreign = Context::default();
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    let mut wrong_context = memory.clone();
    std::rc::Rc::make_mut(&mut wrong_context.mutable_u16)[0].data =
        super::mutable_u16::Storage::Scalar(
            foreign
                .symbol(
                    99,
                    Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(32))),
                )
                .unwrap(),
        );
    assert!(engine.mutable_u16_backing(0, &wrong_context).is_err());
    let symbolic = engine.terms.symbol(987, Sort::BitVec(32)).unwrap();
    let symbolic_value = Value::Int {
        expression: symbolic.clone(),
        bits: 32,
        signed: false,
    };
    for wrong in [
        symbolic::integer(&engine.terms, 0xd800, 32, false),
        symbolic::integer(&engine.terms, 0xdfff, 32, false),
        symbolic::integer(&engine.terms, 0x110000, 32, false),
        symbolic::integer(&engine.terms, 65, 32, true),
        symbolic::integer(&engine.terms, 65, 16, false),
        symbolic::integer(&foreign, 65, 32, false),
        Value::Bool(engine.terms.boolean(true)),
        Value::Int {
            expression: engine.terms.boolean(true),
            bits: 32,
            signed: false,
        },
        symbolic_value.clone(),
    ] {
        assert!(
            engine
                .mutable_hierarchy_char_value_probe(&wrong, &[])
                .is_err()
        );
    }
    for scalar in [0, 0xd7ff, 0xe000, 0x10ffff] {
        engine
            .mutable_hierarchy_char_value_probe(
                &symbolic::integer(&engine.terms, scalar, 32, false),
                &[],
            )
            .unwrap();
    }
    let equal = engine
        .terms
        .apply(
            Op::Equal,
            &[symbolic, engine.terms.bit_vector(0xe000, 32).unwrap()],
        )
        .unwrap();
    let conditions = vec![equal];
    let original_conditions = conditions.clone();
    engine
        .mutable_hierarchy_char_value_probe(&symbolic_value, &conditions)
        .unwrap();
    assert_eq!(conditions, original_conditions);
    compiler_char_store_probe(engine);
}

#[cfg(test)]
fn compiler_char_store_probe(engine: &mut Engine<'_>) {
    let definition = engine
        .tcx
        .hir_body_owners()
        .find(|owner| engine.tcx.item_name(owner.to_def_id()).as_str() == "char_store")
        .unwrap();
    let instance = engine
        .resolve_function_item(definition.to_def_id(), engine.tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(instance).unwrap();
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let root = engine
        .mutable_u16_input(engine.tcx.types.char, &mut memory, &mut conditions)
        .unwrap();
    std::rc::Rc::make_mut(&mut memory.mutable_u16)[0].length =
        symbolic::integer(&engine.terms, 2, bits, false);
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        addresses: vec![None; body.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: Default::default(),
        memory,
        conditions,
    };
    state.locals[1] = Some(root);
    state.locals[2] = Some(symbolic::integer(&engine.terms, 0, bits, false));
    let place = Place {
        local: rustc_middle::mir::Local::from_usize(1),
        projection: engine.tcx.mk_place_elems(&[
            ProjectionElem::Deref,
            ProjectionElem::Index(rustc_middle::mir::Local::from_usize(2)),
        ]),
    };
    let unproven = Value::Int {
        expression: engine.terms.symbol(988, Sort::BitVec(32)).unwrap(),
        bits: 32,
        signed: false,
    };
    for value in [
        symbolic::integer(&engine.terms, 0xd800, 32, false),
        symbolic::integer(&engine.terms, 0xdfff, 32, false),
        symbolic::integer(&engine.terms, 0x110000, 32, false),
        unproven,
    ] {
        let before = state.clone();
        assert!(
            engine
                .mutable_u16_store(&body, &mut state, place, &value)
                .is_err()
        );
        assert_eq!(
            state.memory.mutable_u16[0].data,
            before.memory.mutable_u16[0].data
        );
        assert_eq!(
            state.memory.mutable_u16[0].generation,
            before.memory.mutable_u16[0].generation
        );
        assert_eq!(
            state.memory.mutable_u16[0].phase,
            before.memory.mutable_u16[0].phase
        );
        assert_eq!(state.conditions, before.conditions);
        assert_eq!(state.memory.storage_slots(), before.memory.storage_slots());
    }
    for scalar in [0, 0xd7ff, 0xe000, 0x10ffff] {
        let conditions = state.conditions.clone();
        let value = symbolic::integer(&engine.terms, scalar, 32, false);
        assert!(
            engine
                .mutable_u16_store(&body, &mut state, place, &value)
                .unwrap()
        );
        assert_eq!(state.conditions, conditions);
        let observed = engine
            .mutable_u16_read(Some(&body), &state, place)
            .unwrap()
            .unwrap();
        engine
            .prove_char_value(&observed, &state.conditions)
            .unwrap();
    }
}

#[cfg(test)]
fn compiler_product_payload_refusal_probe(engine: &mut Engine<'_>, root: &Value, memory: &Memory) {
    let backing = engine.mutable_u16_backing(0, memory).unwrap();
    let certificate = backing.certificate;
    let issued = engine.mutable_integer_types[certificate].clone();
    let ghost = engine.mutable_u16_snapshot(root, memory).unwrap();
    let product = engine
        .composite_slice_shape(Ty::new_array(engine.tcx, engine.tcx.types.f32, 2))
        .unwrap()
        .unwrap();
    engine.mutable_integer_types[certificate].codec = ElementCodec::from(product);
    assert!(
        engine
            .mutable_u16_backing(0, memory)
            .unwrap_err()
            .contains("mutable product codec cannot enter scalar authority")
    );
    assert!(engine.mutable_u16_length(root, memory).is_err());
    assert!(engine.mutable_u16_snapshot(root, memory).is_err());
    assert!(engine.mutable_u16_length(&ghost, memory).is_err());
    engine.mutable_integer_types[certificate] = issued;
    let mut wrong_storage = memory.clone();
    std::rc::Rc::make_mut(&mut wrong_storage.mutable_u16)[0].data =
        Storage::from(vec![backing.data.scalar().unwrap().clone()]);
    assert!(
        engine
            .mutable_u16_backing(0, &wrong_storage)
            .unwrap_err()
            .contains("mutable product columns cannot enter scalar authority")
    );
    assert!(engine.mutable_u16_length(root, &wrong_storage).is_err());
    assert!(engine.mutable_u16_snapshot(root, &wrong_storage).is_err());
    assert!(
        engine
            .mutable_u16_role_live(0, &MutableU16Role::Root, &wrong_storage)
            .is_err()
    );
    assert!(engine.mutable_u16_backing(0, memory).is_ok());
    assert_eq!(memory.mutable_u16[0].data, backing.data);
    eprintln!("product_representation_refusal_targets=8");
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn compiler_metadata_roles_and_branch_backing_preserve_source_and_ghost_identity() {
        struct Check {
            checked: bool,
        }
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                let config = miren::ContractConfig::default();
                let limits = miren::AnalysisLimits::default();
                let all_failures = false;
                let induction = false;
                let startup = false;
                let isolated_startup = false;
                let async_entry = false;
                let mut engine = Engine::new(
                    tcx,
                    &config,
                    VerificationOptions {
                        all_failures,
                        induction,
                        startup,
                        isolated_startup,
                        async_entry,
                        limits,
                    },
                );
                let len = tcx.lang_items().get(LangItem::SliceLen).unwrap();
                let args = tcx.mk_args(&[tcx.types.u16.into()]);
                let instance = engine.resolve_function_item(len, args).unwrap();
                engine.certify_mutable_u16_len(instance).unwrap();
                let original = engine.instantiated_body(instance).unwrap();
                let mut wrong = (*original).clone();
                let StatementKind::Assign(assignment) =
                    &mut wrong.basic_blocks.as_mut()[START_BLOCK].statements[0].kind
                else {
                    panic!("assignment")
                };
                assignment.1 = Rvalue::Use(
                    Operand::Copy(Place::from(rustc_middle::mir::Local::from_usize(1))),
                    rustc_middle::mir::WithRetag::No,
                );
                engine
                    .bodies
                    .borrow_mut()
                    .insert(instance, std::rc::Rc::new(wrong));
                assert!(engine.certify_mutable_u16_len(instance).is_err());
                engine.bodies.borrow_mut().insert(instance, original);
                engine.certify_mutable_u16_len(instance).unwrap();
                let mut memory = Memory::default();
                let mut conditions = Vec::new();
                let root = engine
                    .mutable_u16_input(tcx.types.u16, &mut memory, &mut conditions)
                    .unwrap();
                let ghost = engine.mutable_u16_snapshot(&root, &memory).unwrap();
                let Value::MutableU16 { id, .. } = root else {
                    panic!("root")
                };
                let old_data = memory.mutable_u16[id].data.clone();
                let probe = tcx
                    .hir_body_owners()
                    .find(|id| tcx.item_name(id.to_def_id()).as_str() == "probe")
                    .unwrap();
                let probe_instance = engine
                    .resolve_function_item(probe.to_def_id(), tcx.mk_args(&[]))
                    .unwrap();
                let body = engine.instantiated_body(probe_instance).unwrap();
                let bits = u32::from(tcx.sess.target.pointer_width);
                let index = symbolic::integer(&engine.terms, 1, bits, false);
                conditions.push(
                    symbolic::binary(
                        &engine.terms,
                        "lt",
                        index.clone(),
                        memory.mutable_u16[id].length.clone(),
                    )
                    .unwrap()
                    .boolean()
                    .unwrap(),
                );
                let mut state = State {
                    flow: activation_flow::Flow::Unarmed,
                    locals: vec![None; body.local_decls.len()],
                    addresses: vec![None; body.local_decls.len()],
                    conditions,
                    memory,
                    constant_receipts: constant_reference_receipts::Slots::default(),
                    missing_places: Default::default(),
                };
                state.locals[1] = Some(root.clone());
                state.locals[2] = Some(index);
                state.locals[3] = Some(symbolic::integer(&engine.terms, 41, 16, false));
                let place = Place {
                    local: rustc_middle::mir::Local::from_usize(1),
                    projection: tcx.mk_place_elems(&[
                        ProjectionElem::Deref,
                        ProjectionElem::Index(rustc_middle::mir::Local::from_usize(2)),
                    ]),
                };
                engine.check_mutable_u16_child_roles(&body, &state);
                let original_state = state.clone();
                let word = state.locals[3].clone().unwrap();
                assert!(
                    engine
                        .mutable_u16_store(&body, &mut state, place, &word)
                        .unwrap()
                );
                assert_eq!(original_state.memory.mutable_u16[id].data, old_data);
                assert_ne!(state.memory.mutable_u16[id].data, old_data);
                let Value::MutableU16 {
                    role: MutableU16Role::Ghost { data, .. },
                    ..
                } = ghost
                else {
                    panic!("ghost")
                };
                assert_eq!(data, *old_data.scalar().unwrap());
                let returned =
                    original_state.continuation(state.conditions.clone(), state.memory.clone());
                assert_eq!(
                    returned.memory.mutable_u16[id].data,
                    state.memory.mutable_u16[id].data
                );
                assert_ne!(
                    returned.memory.mutable_u16[id].data,
                    original_state.memory.mutable_u16[id].data
                );
                assert!(
                    engine
                        .mutable_u16_read(Some(&body), &returned, place)
                        .unwrap()
                        .is_some()
                );
                let mut dead = returned.clone();
                let allocation = dead.memory.mutable_u16[id].allocation;
                dead.memory[allocation] = None;
                assert!(engine.mutable_u16_read(Some(&body), &dead, place).is_err());
                let mut consumed = returned.clone();
                consumed.missing_places.consume(1, Vec::new()).unwrap();
                assert!(
                    engine
                        .mutable_u16_read(Some(&body), &consumed, place)
                        .is_err()
                );
                let wrong = Value::Int {
                    expression: engine.terms.bit_vector(1, 16).unwrap(),
                    bits: 16,
                    signed: true,
                };
                assert!(
                    engine
                        .mutable_u16_store(&body, &mut state, place, &wrong)
                        .is_err()
                );
                let foreign = Context::default();
                let wrong = Value::Int {
                    expression: foreign.bit_vector(1, 16).unwrap(),
                    bits: 16,
                    signed: false,
                };
                assert!(
                    engine
                        .mutable_u16_store(&body, &mut state, place, &wrong)
                        .is_err()
                );
                let metadata = Value::MutableU16 {
                    id,
                    role: MutableU16Role::Metadata { generation: 0 },
                };
                assert!(
                    engine
                        .mutable_u16_contains(&Value::Tuple(vec![metadata.clone()]), &state.memory)
                        .unwrap()
                );
                assert!(
                    engine
                        .mutable_u16_store_role(
                            &body,
                            &state,
                            Place::from(rustc_middle::mir::Local::from_usize(3)),
                            &Value::Tuple(vec![metadata])
                        )
                        .is_err()
                );
                assert!(engine.mutable_u16_backing(id + 1, &state.memory).is_err());
                let mut masked_backing = state.memory.clone();
                let allocation = masked_backing.mutable_u16[id].allocation;
                masked_backing
                    .missing_places
                    .consume(allocation, Vec::new())
                    .unwrap();
                assert!(engine.mutable_u16_backing(id, &masked_backing).is_err());
                let shared = tcx
                    .hir_body_owners()
                    .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "shared")
                    .unwrap();
                let shared_instance = engine
                    .resolve_function_item(shared.to_def_id(), tcx.mk_args(&[]))
                    .unwrap();
                let shared_body = engine.instantiated_body(shared_instance).unwrap();
                let mut metadata_state = state.clone();
                metadata_state.locals = vec![None; shared_body.local_decls.len()];
                metadata_state.addresses = vec![None; shared_body.local_decls.len()];
                metadata_state.locals[1] = Some(Value::MutableU16 {
                    id,
                    role: MutableU16Role::Metadata { generation: 0 },
                });
                let argument = rustc_span::Spanned {
                    node: Operand::Copy(Place::from(rustc_middle::mir::Local::from_usize(1))),
                    span: rustc_span::DUMMY_SP,
                };
                assert!(
                    engine
                        .mutable_u16_call_allowed(
                            &shared_body,
                            &metadata_state,
                            shared_instance,
                            std::slice::from_ref(&argument)
                        )
                        .is_err()
                );
                engine
                    .mutable_u16_call_allowed(&shared_body, &metadata_state, instance, &[argument])
                    .unwrap();
                let mut wrong_backing = state.memory.clone();
                std::rc::Rc::make_mut(&mut wrong_backing.mutable_u16)[id].data =
                    super::mutable_u16::Storage::Scalar(
                        foreign
                            .symbol(
                                0,
                                Sort::Array(
                                    Box::new(Sort::BitVec(bits)),
                                    Box::new(Sort::BitVec(16)),
                                ),
                            )
                            .unwrap(),
                    );
                assert!(engine.mutable_u16_backing(id, &wrong_backing).is_err());
                for (original_name, wrong_name) in
                    [("caller_i32", "caller_u32"), ("caller_usize", "caller_u64")]
                {
                    let find = |name: &str| {
                        tcx.hir_body_owners()
                            .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == name)
                            .unwrap()
                            .to_def_id()
                    };
                    let own_instance = engine
                        .resolve_function_item(find(original_name), tcx.mk_args(&[]))
                        .unwrap();
                    let wrong_instance = engine
                        .resolve_function_item(find(wrong_name), tcx.mk_args(&[]))
                        .unwrap();
                    let own_body = engine.instantiated_body(own_instance).unwrap();
                    let wrong_body = engine.instantiated_body(wrong_instance).unwrap();
                    let local = rustc_middle::mir::Local::from_usize(1);
                    let ty::Ref(_, slice, _) = own_body.local_decls[local].ty.kind() else {
                        panic!("reference")
                    };
                    let ty::Slice(element) = slice.kind() else {
                        panic!("slice")
                    };
                    let mut memory = Memory::default();
                    let mut conditions = Vec::new();
                    let root = engine
                        .mutable_u16_input(*element, &mut memory, &mut conditions)
                        .unwrap();
                    assert!(
                        engine
                            .mutable_u16_matches(own_body.local_decls[local].ty, 0, &memory, true)
                            .unwrap()
                    );
                    assert!(
                        !engine
                            .mutable_u16_matches(wrong_body.local_decls[local].ty, 0, &memory, true)
                            .unwrap()
                    );
                    let certificate = memory.mutable_u16[0].certificate;
                    let old_certificate = engine.mutable_integer_types[certificate].clone();
                    engine.mutable_integer_types[certificate].bytes = 0;
                    assert!(engine.mutable_u16_backing(0, &memory).is_err());
                    engine.mutable_integer_types[certificate] = old_certificate.clone();
                    engine.mutable_integer_types[certificate].alignment = 0;
                    assert!(engine.mutable_u16_backing(0, &memory).is_err());
                    engine.mutable_integer_types[certificate] = old_certificate;
                    let mut state = State {
                        flow: activation_flow::Flow::Unarmed,
                        locals: vec![None; wrong_body.local_decls.len()],
                        addresses: vec![None; wrong_body.local_decls.len()],
                        conditions,
                        memory,
                        constant_receipts: constant_reference_receipts::Slots::default(),
                        missing_places: Default::default(),
                    };
                    state.locals[1] = Some(root);
                    let bits = u32::from(tcx.sess.target.pointer_width);
                    state.locals[2] = Some(symbolic::integer(&engine.terms, 0, bits, false));
                    let ty::Ref(_, wrong_slice, _) = wrong_body.local_decls[local].ty.kind() else {
                        panic!("reference")
                    };
                    let ty::Slice(wrong_element) = wrong_slice.kind() else {
                        panic!("slice")
                    };
                    let (width, signed) = engine.integer_type(*wrong_element).unwrap();
                    state.locals[3] = Some(symbolic::integer(&engine.terms, 17, width, signed));
                    let (block, instance) = wrong_body
                        .basic_blocks
                        .iter_enumerated()
                        .find_map(|(block, data)| {
                            if let TerminatorKind::Call { func, .. } = &data.terminator().kind
                                && let ty::FnDef(id, args) =
                                    func.ty(&wrong_body.local_decls, tcx).kind()
                                && tcx.item_name(*id).as_str().starts_with("child_")
                            {
                                Some((
                                    block,
                                    engine
                                        .resolve_function_item(*id, args.skip_binder())
                                        .unwrap(),
                                ))
                            } else {
                                None
                            }
                        })
                        .unwrap();
                    let TerminatorKind::Call {
                        args,
                        destination,
                        target,
                        ..
                    } = &wrong_body.basic_blocks[block].terminator().kind
                    else {
                        panic!("call")
                    };
                    let before = state.memory.mutable_u16[0].data.clone();
                    assert!(
                        engine
                            .mutable_u16_child_call(
                                &mut state,
                                super::super::mutable_u16_children::ChildCall {
                                    body: &wrong_body,
                                    block,
                                    instance,
                                    args,
                                    destination: *destination,
                                    target: *target,
                                    stack: &[],
                                    site: (wrong_instance.def_id(), rustc_span::DUMMY_SP),
                                }
                            )
                            .is_err()
                    );
                    assert_eq!(state.memory.mutable_u16[0].data, before);
                    assert_eq!(
                        state.memory.mutable_u16[0].phase,
                        super::super::mutable_u16_children::Phase::Idle
                    );
                    let place = Place {
                        local,
                        projection: tcx.mk_place_elems(&[ProjectionElem::Deref]),
                    };
                    let destination = Place::from(rustc_middle::mir::Local::from_usize(4));
                    let value = Rvalue::Ref(
                        tcx.lifetimes.re_erased,
                        BorrowKind::Mut {
                            kind: rustc_middle::mir::MutBorrowKind::Default,
                        },
                        place,
                    );
                    let occurrence = StatementKind::Assign(Box::new((destination, value)));
                    let StatementKind::Assign(assignment) = &occurrence else {
                        panic!("assign")
                    };
                    assert!(
                        engine
                            .mutable_u16_stage(
                                &wrong_body,
                                &mut state,
                                destination,
                                &assignment.1,
                                &occurrence
                            )
                            .is_err()
                    );
                    let len = engine
                        .resolve_function_item(
                            tcx.lang_items().get(LangItem::SliceLen).unwrap(),
                            tcx.mk_args(&[(*wrong_element).into()]),
                        )
                        .unwrap();
                    let metadata = Value::MutableU16 {
                        id: 0,
                        role: MutableU16Role::Metadata { generation: 0 },
                    };
                    assert!(
                        engine
                            .builtin(
                                &wrong_body,
                                len,
                                std::slice::from_ref(&metadata),
                                std::slice::from_ref(&metadata),
                                &mut state,
                                rustc_span::DUMMY_SP
                            )
                            .is_err()
                    );
                    let mut ghost = engine
                        .mutable_u16_snapshot(state.locals[1].as_ref().unwrap(), &state.memory)
                        .unwrap();
                    let Value::MutableU16 {
                        role: MutableU16Role::Ghost { element, .. },
                        ..
                    } = &mut ghost
                    else {
                        panic!("ghost")
                    };
                    *element = symbolic::ScalarSliceElement::Integer {
                        bits: width,
                        signed,
                    };
                    // i32/u32 share width; usize/u64 share codec. Original types still differ.
                    if original_name == "caller_i32" {
                        assert!(engine.mutable_u16_snapshot(&ghost, &state.memory).is_err());
                    }
                }
                let mut bool_memory = Memory::default();
                let mut bool_conditions = Vec::new();
                let bool_root = engine
                    .mutable_u16_input(tcx.types.bool, &mut bool_memory, &mut bool_conditions)
                    .unwrap();
                compiler_product_payload_refusal_probe(&mut engine, &bool_root, &bool_memory);
                let ghost = engine
                    .mutable_u16_snapshot(&bool_root, &bool_memory)
                    .unwrap();
                let certificate = bool_memory.mutable_u16[0].certificate;
                let issued = engine.mutable_integer_types[certificate].clone();
                assert_eq!(
                    issued.codec.scalar().unwrap(),
                    symbolic::ScalarSliceElement::Bool
                );
                assert_eq!((issued.bytes, issued.alignment), (1, 1));
                let good = Value::Bool(engine.terms.boolean(true));
                assert!(engine.mutable_scalar_replacement(&issued, &good).is_ok());
                for wrong in [
                    symbolic::integer(&engine.terms, 1, 8, false),
                    Value::Bool(foreign.boolean(true)),
                    Value::Bool(engine.terms.bit_vector(1, 8).unwrap()),
                ] {
                    assert!(engine.mutable_scalar_replacement(&issued, &wrong).is_err());
                }
                for wrong_type in [tcx.types.u8, tcx.types.i8] {
                    engine.mutable_integer_types[certificate].original = wrong_type;
                    assert!(engine.mutable_u16_backing(0, &bool_memory).is_err());
                    engine.mutable_integer_types[certificate] = issued.clone();
                }
                for (bytes, alignment) in [(0, 1), (1, 2)] {
                    engine.mutable_integer_types[certificate].bytes = bytes;
                    engine.mutable_integer_types[certificate].alignment = alignment;
                    assert!(engine.mutable_u16_backing(0, &bool_memory).is_err());
                    engine.mutable_integer_types[certificate] = issued.clone();
                }
                for context in [&engine.terms, &foreign] {
                    let mut corrupt = bool_memory.clone();
                    std::rc::Rc::make_mut(&mut corrupt.mutable_u16)[0].data =
                        super::mutable_u16::Storage::Scalar(
                            context
                                .symbol(
                                    99,
                                    Sort::Array(
                                        Box::new(Sort::BitVec(bits)),
                                        Box::new(Sort::BitVec(8)),
                                    ),
                                )
                                .unwrap(),
                        );
                    assert!(engine.mutable_u16_backing(0, &corrupt).is_err());
                }
                let bool_definition = tcx
                    .hir_body_owners()
                    .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "bool_probe")
                    .unwrap();
                let bool_instance = engine
                    .resolve_function_item(bool_definition.to_def_id(), tcx.mk_args(&[]))
                    .unwrap();
                let bool_body = engine.instantiated_body(bool_instance).unwrap();
                std::rc::Rc::make_mut(&mut bool_memory.mutable_u16)[0].length =
                    symbolic::integer(&engine.terms, 2, bits, false);
                let mut bool_state = State {
                    flow: activation_flow::Flow::Unarmed,
                    locals: vec![None; bool_body.local_decls.len()],
                    addresses: vec![None; bool_body.local_decls.len()],
                    conditions: bool_conditions,
                    memory: bool_memory.clone(),
                    constant_receipts: constant_reference_receipts::Slots::default(),
                    missing_places: Default::default(),
                };
                bool_state.locals[1] = Some(bool_root.clone());
                bool_state.locals[2] = Some(symbolic::integer(&engine.terms, 0, bits, false));
                let bool_place = Place {
                    local: rustc_middle::mir::Local::from_usize(1),
                    projection: tcx.mk_place_elems(&[
                        ProjectionElem::Deref,
                        ProjectionElem::Index(rustc_middle::mir::Local::from_usize(2)),
                    ]),
                };
                assert!(
                    engine
                        .mutable_u16_store(&bool_body, &mut bool_state, bool_place, &good)
                        .unwrap()
                );
                assert!(matches!(
                    engine
                        .mutable_u16_read(Some(&bool_body), &bool_state, bool_place)
                        .unwrap(),
                    Some(Value::Bool(_))
                ));
                assert!(
                    !engine
                        .mutable_u16_matches(
                            body.local_decls[rustc_middle::mir::Local::from_usize(1)].ty,
                            0,
                            &bool_state.memory,
                            true
                        )
                        .unwrap()
                );
                bool_state.locals[1] = Some(ghost.clone());
                assert!(
                    engine
                        .mutable_u16_read(Some(&bool_body), &bool_state, bool_place)
                        .is_err()
                );
                let old_data = bool_memory.mutable_u16[0].data.clone();
                std::rc::Rc::make_mut(&mut bool_memory.mutable_u16)[0].data =
                    super::mutable_u16::Storage::Scalar(
                        engine
                            .terms
                            .apply(
                                Op::Store,
                                &[
                                    old_data.scalar().unwrap().clone(),
                                    engine.terms.bit_vector(0, bits).unwrap(),
                                    engine.terms.boolean(true),
                                ],
                            )
                            .unwrap(),
                    );
                assert!(engine.mutable_u16_length(&ghost, &bool_memory).is_ok());
                if let Value::MutableU16 {
                    role: MutableU16Role::Ghost { data, .. },
                    ..
                } = ghost
                {
                    assert_ne!(data, *bool_memory.mutable_u16[0].data.scalar().unwrap());
                } else {
                    panic!("detached ghost");
                }
                let mut char_memory = Memory::default();
                let mut char_conditions = Vec::new();
                let char_root = engine
                    .mutable_u16_input(tcx.types.char, &mut char_memory, &mut char_conditions)
                    .unwrap();
                let certificate = char_memory.mutable_u16[0].certificate;
                let issued = engine.mutable_integer_types[certificate].clone();
                assert_eq!(
                    issued.codec.scalar().unwrap(),
                    symbolic::ScalarSliceElement::Char
                );
                assert_eq!((issued.bytes, issued.alignment), (4, 4));
                for wrong_type in [tcx.types.u32, tcx.types.i32] {
                    engine.mutable_integer_types[certificate].original = wrong_type;
                    assert!(engine.mutable_u16_backing(0, &char_memory).is_err());
                    engine.mutable_integer_types[certificate] = issued.clone();
                }
                for (bytes, alignment) in [(1, 4), (4, 1)] {
                    engine.mutable_integer_types[certificate].bytes = bytes;
                    engine.mutable_integer_types[certificate].alignment = alignment;
                    assert!(engine.mutable_u16_backing(0, &char_memory).is_err());
                    engine.mutable_integer_types[certificate] = issued.clone();
                }
                for data in [
                    engine
                        .terms
                        .symbol(
                            90,
                            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::Bool)),
                        )
                        .unwrap(),
                    foreign
                        .symbol(
                            90,
                            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(32))),
                        )
                        .unwrap(),
                ] {
                    let mut wrong = char_memory.clone();
                    std::rc::Rc::make_mut(&mut wrong.mutable_u16)[0].data =
                        super::mutable_u16::Storage::Scalar(data);
                    assert!(engine.mutable_u16_backing(0, &wrong).is_err());
                }
                let definition = tcx
                    .hir_body_owners()
                    .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "char_probe")
                    .unwrap();
                let instance = engine
                    .resolve_function_item(definition.to_def_id(), tcx.mk_args(&[]))
                    .unwrap();
                let char_body = engine.instantiated_body(instance).unwrap();
                std::rc::Rc::make_mut(&mut char_memory.mutable_u16)[0].length =
                    symbolic::integer(&engine.terms, 2, bits, false);
                let mut char_state = State {
                    flow: activation_flow::Flow::Unarmed,
                    locals: vec![None; char_body.local_decls.len()],
                    addresses: vec![None; char_body.local_decls.len()],
                    conditions: char_conditions,
                    memory: char_memory,
                    constant_receipts: constant_reference_receipts::Slots::default(),
                    missing_places: Default::default(),
                };
                char_state.locals[1] = Some(char_root);
                char_state.locals[2] = Some(symbolic::integer(&engine.terms, 0, bits, false));
                let char_place = Place {
                    local: rustc_middle::mir::Local::from_usize(1),
                    projection: tcx.mk_place_elems(&[
                        ProjectionElem::Deref,
                        ProjectionElem::Index(rustc_middle::mir::Local::from_usize(2)),
                    ]),
                };
                let ghost = engine
                    .mutable_u16_snapshot(
                        char_state.locals[1].as_ref().unwrap(),
                        &char_state.memory,
                    )
                    .unwrap();
                for replacement in [
                    symbolic::integer(&engine.terms, 0xd800, 32, false),
                    symbolic::integer(&engine.terms, 0xdfff, 32, false),
                    symbolic::integer(&engine.terms, 0x110000, 32, false),
                    symbolic::integer(&engine.terms, 65, 32, true),
                    symbolic::integer(&engine.terms, 65, 8, false),
                    symbolic::integer(&foreign, 65, 32, false),
                    Value::Int {
                        expression: engine.terms.boolean(true),
                        bits: 32,
                        signed: false,
                    },
                    Value::Bool(engine.terms.boolean(true)),
                ] {
                    let before = char_state.memory.mutable_u16[0].clone();
                    assert!(
                        engine
                            .mutable_u16_store(
                                &char_body,
                                &mut char_state,
                                char_place,
                                &replacement
                            )
                            .is_err()
                    );
                    let after = &char_state.memory.mutable_u16[0];
                    assert_eq!(after.data, before.data);
                    assert_eq!(after.generation, before.generation);
                    assert_eq!(after.phase, before.phase);
                }
                for scalar in [0, 0xd7ff, 0xe000, 0xffff, 0x10000, 0x10ffff] {
                    let replacement = symbolic::integer(&engine.terms, scalar, 32, false);
                    assert!(
                        engine
                            .mutable_u16_store(
                                &char_body,
                                &mut char_state,
                                char_place,
                                &replacement
                            )
                            .unwrap()
                    );
                    let observed = engine
                        .mutable_u16_read(Some(&char_body), &char_state, char_place)
                        .unwrap()
                        .unwrap();
                    engine
                        .prove_char_value(&observed, &char_state.conditions)
                        .unwrap();
                }
                char_state.locals[1] = Some(ghost.clone());
                assert!(
                    engine
                        .mutable_u16_read(Some(&char_body), &char_state, char_place)
                        .is_err()
                );
                assert!(
                    engine
                        .mutable_u16_length(&ghost, &char_state.memory)
                        .is_ok()
                );
                for (original, name, width, nan) in [
                    (tcx.types.f32, "fp32_probe", 32, 0x7fc00017_u128),
                    (tcx.types.f64, "fp64_probe", 64, 0x7ff8000000000017_u128),
                ] {
                    let mut memory = Memory::default();
                    let mut conditions = Vec::new();
                    let root = engine
                        .mutable_u16_input(original, &mut memory, &mut conditions)
                        .unwrap();
                    let certificate = memory.mutable_u16[0].certificate;
                    let issued = engine.mutable_integer_types[certificate].clone();
                    assert_eq!(
                        issued.codec.scalar().unwrap(),
                        symbolic::ScalarSliceElement::Float { bits: width }
                    );
                    assert_eq!(issued.bytes * 8, u64::from(width));
                    let definition = tcx
                        .hir_body_owners()
                        .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == name)
                        .unwrap();
                    let instance = engine
                        .resolve_function_item(definition.to_def_id(), tcx.mk_args(&[]))
                        .unwrap();
                    let selected = engine.instantiated_body(instance).unwrap();
                    std::rc::Rc::make_mut(&mut memory.mutable_u16)[0].length =
                        symbolic::integer(&engine.terms, 2, bits, false);
                    let mut state = State {
                        flow: activation_flow::Flow::Unarmed,
                        locals: vec![None; selected.local_decls.len()],
                        addresses: vec![None; selected.local_decls.len()],
                        conditions,
                        memory,
                        constant_receipts: constant_reference_receipts::Slots::default(),
                        missing_places: Default::default(),
                    };
                    state.locals[1] = Some(root);
                    state.locals[2] = Some(symbolic::integer(&engine.terms, 0, bits, false));
                    let place = Place {
                        local: rustc_middle::mir::Local::from_usize(1),
                        projection: tcx.mk_place_elems(&[
                            ProjectionElem::Deref,
                            ProjectionElem::Index(rustc_middle::mir::Local::from_usize(2)),
                        ]),
                    };
                    let valid = symbolic::float_from_bits(
                        &engine.terms,
                        engine.terms.bit_vector(nan, width).unwrap(),
                        width,
                    );
                    let Value::Float {
                        expression,
                        raw_bits: Some(raw),
                        ..
                    } = &valid
                    else {
                        unreachable!()
                    };
                    let mut forged_nan = valid.clone();
                    if let Value::Float { raw_bits, .. } = &mut forged_nan {
                        *raw_bits = Some(engine.terms.bit_vector(nan + 1, width).unwrap());
                    }
                    let wrong_numeric = Value::Float {
                        expression: engine.terms.boolean(true),
                        bits: width,
                        raw_bits: Some(raw.clone()),
                    };
                    let wrong_raw = Value::Float {
                        expression: expression.clone(),
                        bits: width,
                        raw_bits: Some(engine.terms.boolean(true)),
                    };
                    let no_raw = Value::Float {
                        expression: expression.clone(),
                        bits: width,
                        raw_bits: None,
                    };
                    let missing_issuer = Value::Float {
                        expression: engine
                            .terms
                            .apply(Op::FpNeg, std::slice::from_ref(expression))
                            .unwrap(),
                        bits: width,
                        raw_bits: Some(raw.clone()),
                    };
                    for replacement in [
                        forged_nan,
                        wrong_numeric,
                        wrong_raw,
                        no_raw,
                        missing_issuer,
                        symbolic::float_from_bits(
                            &foreign,
                            foreign.bit_vector(nan, width).unwrap(),
                            width,
                        ),
                        symbolic::float_from_bits(
                            &engine.terms,
                            engine
                                .terms
                                .bit_vector(0, if width == 32 { 64 } else { 32 })
                                .unwrap(),
                            if width == 32 { 64 } else { 32 },
                        ),
                    ] {
                        let before = state.memory.mutable_u16[0].clone();
                        assert!(
                            engine
                                .mutable_u16_store(&selected, &mut state, place, &replacement)
                                .is_err()
                        );
                        let after = &state.memory.mutable_u16[0];
                        assert_eq!(before.data, after.data);
                        assert_eq!(before.phase, after.phase);
                        assert_eq!(before.generation, after.generation);
                    }
                    for wrong_type in [tcx.types.u32, tcx.types.char, tcx.types.bool] {
                        engine.mutable_integer_types[certificate].original = wrong_type;
                        assert!(engine.mutable_u16_backing(0, &state.memory).is_err());
                        engine.mutable_integer_types[certificate] = issued.clone();
                    }
                    engine.mutable_integer_types[certificate].bytes += 1;
                    assert!(engine.mutable_u16_backing(0, &state.memory).is_err());
                    engine.mutable_integer_types[certificate] = issued.clone();
                    engine.mutable_integer_types[certificate].alignment += 1;
                    assert!(engine.mutable_u16_backing(0, &state.memory).is_err());
                    engine.mutable_integer_types[certificate] = issued.clone();
                    engine.mutable_integer_types[certificate].codec =
                        ElementCodec::Scalar(symbolic::ScalarSliceElement::Float {
                            bits: if width == 32 { 64 } else { 32 },
                        });
                    assert!(engine.mutable_u16_backing(0, &state.memory).is_err());
                    engine.mutable_integer_types[certificate] = issued;
                    assert!(
                        engine
                            .mutable_u16_store(&selected, &mut state, place, &valid)
                            .unwrap()
                    );
                    let observed = engine
                        .mutable_u16_read(Some(&selected), &state, place)
                        .unwrap()
                        .unwrap();
                    engine
                        .prove_float_pair(&observed, width, &state.conditions)
                        .unwrap();
                    let arithmetic =
                        symbolic::binary(&engine.terms, "add", valid.clone(), valid.clone())
                            .unwrap();
                    let materialized = engine.materialize_float(arithmetic);
                    let Value::Float {
                        raw_bits: Some(raw),
                        ..
                    } = &materialized
                    else {
                        unreachable!()
                    };
                    let symbol = raw.symbol_index().unwrap();
                    let binding = engine.float_encodings.remove(&symbol).unwrap();
                    let before = state.memory.mutable_u16[0].clone();
                    assert!(
                        engine
                            .mutable_u16_store(&selected, &mut state, place, &materialized)
                            .is_err()
                    );
                    engine
                        .float_encodings
                        .insert(symbol, engine.terms.boolean(false));
                    assert!(
                        engine
                            .mutable_u16_store(&selected, &mut state, place, &materialized)
                            .is_err()
                    );
                    assert_eq!(before.data, state.memory.mutable_u16[0].data);
                    assert_eq!(before.phase, state.memory.mutable_u16[0].phase);
                    assert_eq!(before.generation, state.memory.mutable_u16[0].generation);
                    engine.float_encodings.insert(symbol, binding);
                    assert!(
                        engine
                            .mutable_u16_store(&selected, &mut state, place, &materialized)
                            .unwrap()
                    );
                }
                self.checked = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory = std::env::temp_dir().join(format!(
            "miren-mutable-u16-certificate-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("probe.rs");
        std::fs::write(
            &source,
            r#"#![no_std]
#[inline(never)]
pub fn child_i32(values: &mut [i32], index: usize, word: i32) {
    if index < values.len() {
        values[index] = word;
    }
}
#[inline(never)]
pub fn child_u32(values: &mut [u32], index: usize, word: u32) {
    if index < values.len() {
        values[index] = word;
    }
}
#[inline(never)]
pub fn child_usize(values: &mut [usize], index: usize, word: usize) {
    if index < values.len() {
        values[index] = word;
    }
}
#[inline(never)]
pub fn child_u64(values: &mut [u64], index: usize, word: u64) {
    if index < values.len() {
        values[index] = word;
    }
}
pub fn caller_i32(values: &mut [i32], index: usize, word: i32) {
    child_i32(values, index, word);
    let _ = values.len();
}
pub fn caller_u32(values: &mut [u32], index: usize, word: u32) {
    child_u32(values, index, word);
    let _ = values.len();
}
pub fn caller_usize(values: &mut [usize], index: usize, word: usize) {
    child_usize(values, index, word);
    let _ = values.len();
}
pub fn caller_u64(values: &mut [u64], index: usize, word: u64) {
    child_u64(values, index, word);
    let _ = values.len();
}
pub fn shared(values: &[u16]) -> usize {
    values.len()
}
pub fn scalar(word: u16) -> u16 {
    word ^ 0
}
pub fn fp32_probe(values: &mut [f32], index: usize, word: f32) {
    if index < values.len() { values[index] = word; }
}
pub fn fp64_probe(values: &mut [f64], index: usize, word: f64) {
    if index < values.len() { values[index] = word; }
}
pub fn char_probe(values: &mut [char], index: usize, word: char) {
    if index < values.len() { values[index] = word; }
}
pub fn bool_probe(values: &mut [bool], index: usize, word: bool) {
    if index < values.len() { values[index] = word; }
}
pub fn probe(values: &mut [u16], index: usize, word: u16) {
    if index < values.len() {
        values[index] = word;
    }
}
"#,
        )
        .unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        assert!(sysroot.status.success());
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for level in ["0", "2"] {
                let mut check = Check { checked: false };
                let mut arguments = vec![
                    "rustc".into(),
                    source.to_str().unwrap().into(),
                    "--crate-type=lib".into(),
                    "--edition=2024".into(),
                    "-Cpanic=abort".into(),
                    format!("-Copt-level={level}"),
                    "--out-dir".into(),
                    directory.to_str().unwrap().into(),
                    "--sysroot".into(),
                    String::from_utf8(sysroot.stdout.clone())
                        .unwrap()
                        .trim()
                        .into(),
                ];
                if let Some(target) = target {
                    arguments.extend(["--target".into(), target.into()]);
                }
                rustc_driver::run_compiler(&arguments, &mut check);
                assert!(check.checked);
            }
        }
        std::fs::remove_dir_all(directory).unwrap();
    }
}
