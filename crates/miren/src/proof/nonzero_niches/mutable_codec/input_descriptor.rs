//! Paid input compiler evidence. This record is not an owner, lease or Memory permission.
use super::super::super::composite_slices::{CompositeShape, CompositeType};
use super::*;
use rustc_middle::mir::Local;

pub(in crate::proof) struct Input<'tcx> {
    instance: ty::Instance<'tcx>,
    body: Rc<Body<'tcx>>,
    signature: ty::PolyFnSig<'tcx>,
    local: Local,
    parameter: Ty<'tcx>,
    descriptor: CompositeType<'tcx>,
    expected: CompositeType<'tcx>,
    alignment: u64,
    expected_alignment: u64,
    token: Term,
    session: Rc<Session>,
}

struct Plan {
    nodes: usize,
    niches: usize,
}

impl Plan {
    fn original<'tcx>(
        &mut self,
        engine: &mut Engine<'tcx>,
        original: Ty<'tcx>,
        depth: usize,
    ) -> Result<(), String> {
        pay(engine, 8)?;
        if depth >= 16 || self.nodes >= 512 {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "mutable niche input graph exceeds512/depth16".into(),
            ));
        }
        self.nodes += 1;
        match original.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64) => Ok(()),
            ty::Tuple(fields) => {
                if fields.len() > 512 {
                    return Err("mutable niche tuple fields exceed512".into());
                }
                pay(engine, fields.len() + 4)?;
                for field in fields.iter() {
                    self.original(engine, field, depth + 1)?;
                }
                Ok(())
            }
            ty::Array(element, count) => {
                pay(engine, 16)?;
                let ty::ConstKind::Value(value) = count.kind() else {
                    return Err("mutable niche input array needs original scalar count".into());
                };
                if !matches!(value.ty.kind(), ty::Uint(ty::UintTy::Usize)) {
                    return Err("mutable niche input array count is not usize".into());
                }
                let count = count
                    .try_to_target_usize(engine.tcx)
                    .ok_or("mutable niche input array count unavailable")?;
                if count > 128 {
                    return Err(engine.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "mutable niche input array exceeds128".into(),
                    ));
                }
                // Validate original elements even at zero length; pay every actual occurrence.
                for _ in 0..count.max(1) {
                    self.original(engine, *element, depth + 1)?;
                }
                pay(engine, (count as usize) * 16 + 8)
            }
            ty::Adt(def, args) if def.is_struct() && def.did().is_local() => {
                names::path(engine, def.did())?;
                let fields = &def.non_enum_variant().fields;
                if fields.len() > 512 {
                    return Err("mutable niche struct fields exceed512".into());
                }
                pay(engine, fields.len() + 129 + 16)?;
                for field in fields {
                    pay(engine, 8)?;
                    if field.name.as_str().len() > 128 {
                        return Err("mutable niche field name exceeds128".into());
                    }
                    pay(engine, 129 + 16)?;
                    self.original(
                        engine,
                        field.ty(engine.tcx, args).skip_norm_wip(),
                        depth + 1,
                    )?;
                }
                Ok(())
            }
            ty::Adt(def, _) if def.is_enum() => {
                if !selected(engine, original)? {
                    return Err("mutable niche input has an uncertified enum leaf".into());
                }
                pay(engine, 512 + 16 * 129 + 128)?;
                let raw = certify_raw(engine.tcx, original)?;
                let names = names::prepare(engine, &raw)?;
                names.check(&raw)?;
                self.niches += 1;
                Ok(())
            }
            _ => {
                Err("mutable niche input needs primitive products and certified enum leaves".into())
            }
        }
    }
}

fn columns(shape: &CompositeShape) -> Result<usize, String> {
    match shape {
        CompositeShape::Primitive(_) | CompositeShape::NonZeroNiche(_) => Ok(1),
        CompositeShape::Tuple(fields) | CompositeShape::Array(fields) => {
            fields.iter().try_fold(0usize, |total, shape| {
                total
                    .checked_add(columns(shape)?)
                    .ok_or("mutable niche columns overflow".into())
            })
        }
        CompositeShape::Struct { fields, .. } => {
            fields.iter().try_fold(0usize, |total, (_, shape)| {
                total
                    .checked_add(columns(shape)?)
                    .ok_or("mutable niche columns overflow".into())
            })
        }
        CompositeShape::Sum { .. } => Err("mutable niche input cannot admit arbitrary sums".into()),
    }
}

pub(in crate::proof) fn prepare<'tcx>(
    engine: &mut Engine<'tcx>,
    session: &Rc<Session>,
    instance: ty::Instance<'tcx>,
    local: Local,
) -> Result<Input<'tcx>, String> {
    let result = (|| {
        if session.0.get() {
            return Err("failed niche input session cannot continue".into());
        }
        let signature = super::super::super::mutable_hierarchy::products::niche_codec_signature(
            engine, instance,
        )?;
        let body = super::super::super::compiler_sources::authenticated_item(engine, instance)?;
        pay(engine, 24)?;
        if local.as_usize() == 0 || local.as_usize() > body.arg_count {
            return Err("mutable niche input is not an actual parameter".into());
        }
        let parameter = body.local_decls[local].ty;
        pay(
            engine,
            2 * signature.skip_binder().inputs_and_output.len() + 8,
        )?;
        let callable = engine.tcx.instantiate_bound_regions_with_erased(signature);
        if body.source.instance != instance.def
            || callable.inputs().len() != body.arg_count
            || callable.output() != body.return_ty()
            || body
                .args_iter()
                .zip(callable.inputs())
                .any(|(local, expected)| {
                    engine
                        .tcx
                        .erase_and_anonymize_regions(body.local_decls[local].ty)
                        != *expected
                })
        {
            return Err("mutable niche input Body/full signature parameter differs".into());
        }
        let ty::Ref(_, slice, mutability) = parameter.kind() else {
            return Err("mutable niche input parameter is not a reference".into());
        };
        if !mutability.is_mut() {
            return Err("mutable niche input is not mutable".into());
        }
        let ty::Slice(original) = slice.kind() else {
            return Err("mutable niche input parameter is not a slice".into());
        };
        if !engine.mutable_product_kind(*original) {
            return Err("mutable niche input requires a product root".into());
        }
        let mut plan = Plan {
            nodes: 0,
            niches: 0,
        };
        plan.original(engine, *original, 0)?;
        if plan.niches == 0 {
            return Err("mutable niche input has no niche leaves".into());
        }
        // Disjoint work for two actual compiler constructions and bounded schema/layout checks.
        // The expected record is never derived from a mutable owner certificate.
        pay(
            engine,
            2 * plan.nodes * (512 + 8 * 129) + 2 * plan.nodes * 32 + 64,
        )?;
        let descriptor = engine
            .composite_shape_with_niches(*original)?
            .ok_or("mutable niche input original shape is unsupported")?;
        if columns(&descriptor.shape)? != descriptor.leaves.len() {
            return Err("mutable niche input column inventory differs".into());
        }
        let alignment = engine.static_layout(*original)?.align.abi.bytes();
        let expected = engine
            .composite_shape_with_niches(*original)?
            .ok_or("mutable niche expected input shape is unsupported")?;
        let expected_alignment = engine.static_layout(*original)?.align.abi.bytes();
        let signatures = engine
            .call_signatures
            .try_borrow()
            .map_err(|_| "mutable niche input signature registry borrowed")?
            .len();
        if signatures > 256 {
            return Err("mutable niche input signature registry exceeds ordinary256 cap".into());
        }
        pay(engine, signatures + 16)?;
        let mut catalogue = engine
            .call_signatures
            .try_borrow_mut()
            .map_err(|_| "mutable niche input signature registry borrowed")?;
        if catalogue
            .get(&instance)
            .is_some_and(|current| *current != signature)
        {
            return Err("mutable niche input cached full signature differs".into());
        }
        if signatures < 256 {
            catalogue.insert(instance, signature);
        }
        drop(catalogue);
        // Linear metadata consumption pays its own current Body/signature lookup pair.
        // Root transfer below pays a separate pair; neither reuses builder/lookup work.
        pay(engine, 128 + 256 + 32)?;
        Ok(Input {
            instance,
            body,
            signature,
            local,
            parameter,
            descriptor,
            expected,
            alignment,
            expected_alignment,
            token: engine.terms.boolean(true),
            session: session.clone(),
        })
    })();
    if result.is_err() {
        session.0.set(true);
    }
    result.map_err(|reason| categorized(engine, reason))
}

pub(in crate::proof) struct Issued<'tcx> {
    descriptor: CompositeType<'tcx>,
    expected: CompositeType<'tcx>,
    alignment: u64,
    instance: ty::Instance<'tcx>,
    body: Rc<Body<'tcx>>,
    signature: ty::PolyFnSig<'tcx>,
    local: Local,
    parameter: Ty<'tcx>,
    token: Term,
}

impl<'tcx> Input<'tcx> {
    pub(in crate::proof) fn consume(self, engine: &Engine<'tcx>) -> Result<Issued<'tcx>, String> {
        let result = (|| {
            if self.session.0.get() {
                return Err("failed niche input session cannot issue".into());
            }
            if self.descriptor.ty != self.expected.ty
                || self.descriptor.bytes != self.expected.bytes
                || self.descriptor.leaves != self.expected.leaves
                || self.alignment != self.expected_alignment
                || !same(&self.descriptor.shape, &self.expected.shape)
            {
                return Err("mutable niche input full descriptor/layout differs".into());
            }
            let issued = Issued {
                descriptor: self.descriptor,
                expected: self.expected,
                alignment: self.alignment,
                instance: self.instance,
                body: self.body,
                signature: self.signature,
                local: self.local,
                parameter: self.parameter,
                token: self.token,
            };
            issued.source(engine)?;
            Ok(issued)
        })();
        if result.is_err() {
            self.session.0.set(true);
        }
        result.map_err(|reason| categorized(engine, reason))
    }
}

impl<'tcx> Issued<'tcx> {
    fn source(&self, engine: &Engine<'tcx>) -> Result<(), String> {
        if !self.token.belongs_to(&engine.terms) {
            return Err("mutable niche input Context differs".into());
        }
        let bodies = engine
            .bodies
            .try_borrow()
            .map_err(|_| "mutable niche input Body registry is mutably borrowed")?;
        let signatures = engine
            .call_signatures
            .try_borrow()
            .map_err(|_| "mutable niche input signature registry is mutably borrowed")?;
        if bodies.len() > 128 || signatures.len() > 256 {
            return Err("mutable niche input source exceeds prepaid ordinary catalogues".into());
        }
        if bodies
            .get(&self.instance)
            .is_none_or(|body| !Rc::ptr_eq(body, &self.body))
            || signatures
                .get(&self.instance)
                .is_some_and(|signature| *signature != self.signature)
            || self.body.local_decls[self.local].ty != self.parameter
        {
            return Err("mutable niche input source/full signature/parameter differs".into());
        }
        Ok(())
    }
}

fn same(left: &CompositeShape, right: &CompositeShape) -> bool {
    match (left, right) {
        (CompositeShape::Primitive(left), CompositeShape::Primitive(right)) => left == right,
        (CompositeShape::Tuple(left), CompositeShape::Tuple(right))
        | (CompositeShape::Array(left), CompositeShape::Array(right)) => {
            left.len() == right.len() && left.iter().zip(right).all(|(l, r)| same(l, r))
        }
        (
            CompositeShape::Struct {
                name: ln,
                fields: left,
            },
            CompositeShape::Struct {
                name: rn,
                fields: right,
            },
        ) => {
            ln == rn
                && left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|((ln, l), (rn, r))| ln == rn && same(l, r))
        }
        (CompositeShape::NonZeroNiche(left), CompositeShape::NonZeroNiche(right)) => {
            left.storage_matches(right)
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

impl<'tcx> Issued<'tcx> {
    // Borrowed metadata only: this accessor neither revalidates source nor issues an owner right.
    #[cfg(test)]
    pub(in crate::proof) fn descriptor(&self) -> &CompositeType<'tcx> {
        &self.descriptor
    }
    #[cfg(test)]
    pub(in crate::proof) fn alignment(&self) -> u64 {
        self.alignment
    }
}

impl Input<'_> {
    #[cfg(test)]
    pub(super) fn corrupt_for_test(&mut self, alignment: bool) {
        if alignment {
            self.alignment += 1;
        } else {
            self.descriptor.bytes += 1;
        }
    }
}

// Administrative root setup is marked only by Engine::root. Descriptor metadata alone cannot
// create this private one-shot authority. Drop closes early-error paths as well as normal setup.
#[derive(Default)]
pub(in crate::proof) struct RootRegistry {
    phase: Rc<Cell<Option<DefId>>>,
    started: bool,
    issued: bool,
}

pub(in crate::proof) struct RootSetup {
    phase: Rc<Cell<Option<DefId>>>,
}

impl RootRegistry {
    pub(in crate::proof) fn begin(&mut self, root: DefId) -> Result<RootSetup, String> {
        if self.started {
            return Err("root niche input setup cannot restart".into());
        }
        self.started = true;
        self.phase.set(Some(root));
        Ok(RootSetup {
            phase: self.phase.clone(),
        })
    }
}

impl RootSetup {
    pub(in crate::proof) fn close(&self) {
        self.phase.set(None);
    }
}
impl Drop for RootSetup {
    fn drop(&mut self) {
        self.close();
    }
}

pub(in crate::proof) struct RootInput<'tcx> {
    #[cfg(test)]
    deny_origin_plan: bool,
    root: DefId,
    local: Local,
    phase: Rc<Cell<Option<DefId>>>,
    metadata: Issued<'tcx>,
}

fn candidate<'tcx>(
    engine: &mut Engine<'tcx>,
    original: Ty<'tcx>,
    depth: usize,
    nodes: &mut usize,
) -> Result<bool, String> {
    pay(engine, 4)?;
    if depth >= 16 || *nodes >= 512 {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "root niche selector exceeds512/depth16".into(),
        ));
    }
    *nodes += 1;
    match original.kind() {
        ty::Tuple(fields) => {
            for field in fields.iter() {
                if candidate(engine, field, depth + 1, nodes)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        ty::Array(element, _) => candidate(engine, *element, depth + 1, nodes),
        ty::Adt(def, args) if def.is_struct() && def.did().is_local() => {
            for field in &def.non_enum_variant().fields {
                pay(engine, 8)?;
                let original = field.ty(engine.tcx, args).skip_norm_wip();
                if candidate(engine, original, depth + 1, nodes)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        ty::Adt(def, _) if def.is_enum() => selected(engine, original),
        _ => Ok(false),
    }
}

pub(in crate::proof) fn prepare_root<'tcx>(
    engine: &mut Engine<'tcx>,
    root: DefId,
    body: &Body<'tcx>,
    local: Local,
    memory: &Memory,
) -> Result<Option<RootInput<'tcx>>, String> {
    // Classify the actual original parameter before acquiring full signature/descriptor service.
    let ty::Ref(_, slice, mutability) = body.local_decls[local].ty.kind() else {
        return Ok(None);
    };
    let ty::Slice(original) = slice.kind() else {
        return Ok(None);
    };
    if !mutability.is_mut()
        || !engine.mutable_product_kind(*original)
        || !candidate(engine, *original, 0, &mut 0)?
    {
        return Ok(None);
    }
    if engine.niche_root_inputs.phase.get() != Some(root)
        || engine.niche_root_inputs.issued
        || !engine.call_chain.is_empty()
        || !memory.is_empty()
        || !memory.mutable_u16.is_empty()
        || !memory.owned_regions.is_empty()
    {
        return Err("niche owner input needs actual fresh root setup".into());
    }
    let session = Rc::new(Session::default());
    let instance =
        ty::Instance::new_raw(root, ty::GenericArgs::identity_for_item(engine.tcx, root));
    let metadata = prepare(engine, &session, instance, local)?.consume(engine)?;
    if metadata.descriptor.ty != *original {
        return Err("root niche parameter descriptor differs".into());
    }
    engine.niche_root_inputs.issued = true;
    Ok(Some(RootInput {
        #[cfg(test)]
        deny_origin_plan: false,
        root,
        local,
        phase: engine.niche_root_inputs.phase.clone(),
        metadata,
    }))
}

impl<'tcx> RootInput<'tcx> {
    pub(in crate::proof) fn consume(
        self,
        engine: &mut Engine<'tcx>,
        memory: &Memory,
    ) -> Result<RootParts<'tcx>, String> {
        pay(engine, 128 + 256 + 32)?;
        if self.phase.get() != Some(self.root)
            || !Rc::ptr_eq(&self.phase, &engine.niche_root_inputs.phase)
            || !engine.niche_root_inputs.issued
            || !engine.call_chain.is_empty()
            || !memory.is_empty()
            || !memory.mutable_u16.is_empty()
            || !memory.owned_regions.is_empty()
            || self.metadata.instance.def_id() != self.root
            || self.metadata.local != self.local
        {
            return Err("niche root input token is stale/outside fresh root setup".into());
        }
        self.metadata.source(engine)?;
        #[cfg(test)]
        if self.deny_origin_plan {
            engine.limits.max_steps = engine.steps.used().checked_add(15).unwrap();
        }
        let plan = origin_plan(engine, &self.metadata.expected.shape, 0, &mut 0)?;
        pay(engine, 16)?;
        let compare_work = self
            .metadata
            .expected
            .leaves
            .len()
            .checked_mul(2)
            .and_then(|work| work.checked_add(64))
            .and_then(|work| work.checked_add(plan.compare))
            .ok_or("niche immutable origin comparison plan overflow")?;
        let value_work = self
            .metadata
            .expected
            .leaves
            .len()
            .checked_mul(160)
            .and_then(|work| work.checked_add(64))
            .and_then(|work| work.checked_add(plan.value))
            .ok_or("niche immutable origin value plan overflow")?;

        Ok(RootParts {
            descriptor: self.metadata.descriptor,
            origin: Origin {
                compare_work,
                value_work,
                receipts: plan.receipts,
                expected: self.metadata.expected,
                alignment: self.metadata.alignment,
                instance: self.metadata.instance,
                body: self.metadata.body,
                signature: self.metadata.signature,
                local: self.metadata.local,
                token: self.metadata.token,
            },
        })
    }
}

pub(in crate::proof) struct RootParts<'tcx> {
    pub(in crate::proof) descriptor: CompositeType<'tcx>,
    pub(in crate::proof) origin: Origin<'tcx>,
}

struct OriginPlan {
    compare: usize,
    value: usize,
    receipts: usize,
}
fn origin_plan(
    engine: &mut Engine<'_>,
    shape: &CompositeShape,
    depth: usize,
    nodes: &mut usize,
) -> Result<OriginPlan, String> {
    pay(engine, 16)?;
    if depth >= 16 || *nodes >= 512 {
        return Err("niche immutable origin plan exceeds512/depth16".into());
    }
    *nodes += 1;
    let mut result = OriginPlan {
        compare: 4,
        value: 128 + depth,
        receipts: 0,
    };
    match shape {
        CompositeShape::Primitive(_) => {}
        CompositeShape::NonZeroNiche(schema) => {
            if schema.variant_names.len() > 2 {
                return Err("niche immutable origin variant inventory differs".into());
            }
            pay(engine, schema.variant_names.len() + 16)?;
            result.compare = schema
                .variant_names
                .iter()
                .try_fold(128usize, |sum, name| {
                    sum.checked_add(name.len())
                        .ok_or("niche immutable name plan overflow")
                })?;
            for name in [
                &schema.name,
                &schema.outer_name,
                &schema.inner_name,
                &schema.outer_field,
                &schema.inner_field,
                &schema.payload_field,
            ] {
                result.compare = result
                    .compare
                    .checked_add(name.len())
                    .ok_or("niche immutable name plan overflow")?;
            }
            result.receipts = 1;
        }
        CompositeShape::Tuple(fields) | CompositeShape::Array(fields) => {
            if fields.len() > 512 {
                return Err("niche immutable origin field inventory exceeds512".into());
            }
            pay(engine, fields.len() + 8)?;
            result.value = result
                .value
                .checked_add(fields.len() * 32)
                .ok_or("niche immutable field value plan overflow")?;
            for shape in fields {
                let child = origin_plan(engine, shape, depth + 1, nodes)?;
                result.compare = result
                    .compare
                    .checked_add(child.compare)
                    .ok_or("niche immutable comparison plan overflow")?;
                result.value = result
                    .value
                    .checked_add(child.value)
                    .ok_or("niche immutable value plan overflow")?;
                result.receipts = result
                    .receipts
                    .checked_add(child.receipts)
                    .ok_or("niche immutable receipt plan overflow")?;
            }
        }
        CompositeShape::Struct { name, fields } => {
            if fields.len() > 512 {
                return Err("niche immutable origin field inventory exceeds512".into());
            }
            pay(engine, fields.len() + 8)?;
            result.compare = result
                .compare
                .checked_add(name.len())
                .ok_or("niche immutable name plan overflow")?;
            result.value = result
                .value
                .checked_add(fields.len() * 32)
                .and_then(|work| work.checked_add(name.len()))
                .ok_or("niche immutable field value plan overflow")?;
            for (name, shape) in fields {
                let child = origin_plan(engine, shape, depth + 1, nodes)?;
                result.compare = result
                    .compare
                    .checked_add(child.compare)
                    .and_then(|work| work.checked_add(name.len()))
                    .ok_or("niche immutable comparison plan overflow")?;
                result.value = result
                    .value
                    .checked_add(child.value)
                    .and_then(|work| work.checked_add(name.len()))
                    .ok_or("niche immutable value plan overflow")?;
                result.receipts = result
                    .receipts
                    .checked_add(child.receipts)
                    .ok_or("niche immutable receipt plan overflow")?;
            }
        }
        CompositeShape::Sum { .. } => {
            return Err("niche immutable origin cannot plan arbitrary sums".into());
        }
    }
    Ok(result)
}

pub(in crate::proof) struct Origin<'tcx> {
    compare_work: usize,
    value_work: usize,
    receipts: usize,
    expected: CompositeType<'tcx>,
    alignment: u64,
    instance: ty::Instance<'tcx>,
    body: Rc<Body<'tcx>>,
    signature: ty::PolyFnSig<'tcx>,
    local: Local,
    token: Term,
}
impl<'tcx> Origin<'tcx> {
    pub(in crate::proof) fn compare_work(&self) -> usize {
        self.compare_work
    }
    pub(in crate::proof) fn value_work(&self, receipt_work: usize) -> Result<usize, String> {
        self.receipts
            .checked_mul(receipt_work)
            .and_then(|work| work.checked_add(self.value_work))
            .ok_or_else(|| "niche actual value construction plan overflow".into())
    }
    pub(in crate::proof) fn verify(
        &self,
        engine: &Engine<'tcx>,
        certificate: &super::super::super::mutable_u16::IntegerCertificate<'tcx>,
        paid: super::super::super::mutable_product_niche_ledger::PaidComparison<'tcx>,
    ) -> Result<(), String> {
        paid.consume(engine, self)?;
        engine.niche_source_inventory_guard()?;
        let bodies = engine
            .bodies
            .try_borrow()
            .map_err(|_| "niche origin Body registry borrowed")?;
        let signatures = engine
            .call_signatures
            .try_borrow()
            .map_err(|_| "niche origin signature registry borrowed")?;
        if bodies.len() > 128 || signatures.len() > 256 {
            return Err("niche originating source catalogue exceeds prepaid ordinary caps".into());
        }
        if !self.token.belongs_to(&engine.terms)
            || bodies
                .get(&self.instance)
                .is_none_or(|body| !Rc::ptr_eq(body, &self.body))
            || signatures
                .get(&self.instance)
                .is_some_and(|signature| *signature != self.signature)
            || self.local.as_usize() == 0
            || self.local.as_usize() > self.body.arg_count
        {
            return Err("niche owner originating source/Context differs".into());
        }
        let super::super::super::mutable_u16::ElementCodec::Product(current) = &certificate.codec
        else {
            return Err("niche owner current certificate is not a product".into());
        };
        if certificate.original != self.expected.ty
            || current.ty != self.expected.ty
            || current.bytes != self.expected.bytes
            || current.leaves != self.expected.leaves
            || certificate.bytes != self.expected.bytes
            || certificate.alignment != self.alignment
            || !same(&current.shape, &self.expected.shape)
        {
            return Err("niche owner full current certificate differs from compiler origin".into());
        }
        Ok(())
    }
}

pub(in crate::proof) fn price_leaf_schema<'tcx>(
    engine: &mut Engine<'tcx>,
    original: Ty<'tcx>,
) -> Result<usize, String> {
    if !selected(engine, original)? {
        return Err("product leaf is not a certified integer niche".into());
    }
    pay(engine, 512 + 16 * 129 + 128)?;
    let raw = certify_raw(engine.tcx, original)?;
    let names = names::prepare(engine, &raw)?;
    names.check(&raw)?;
    Ok(512 + 8 * 129)
}

impl<'tcx> Origin<'tcx> {
    pub(in crate::proof) fn original(&self) -> Ty<'tcx> {
        self.expected.ty
    }
}

#[cfg(test)]
#[path = "origin_plan_probe.rs"]
mod origin_plan_probe;
