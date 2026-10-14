//! Immutable compiler metadata reuse within a paid, authenticated Product instruction.
//! This catalogue never grants storage or owner rights. Mutable certificates remain untrusted.
use super::composite_slices::{CompositeShape, CompositeType};
use super::mutable_u16::{ElementCodec, IntegerCertificate};
use super::*;
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq)]
enum DescriptorPolicy {
    PureProduct,
}

pub(super) struct Binding<'tcx> {
    pub(super) frame: usize,
    pub(super) instance: ty::Instance<'tcx>,
    pub(super) body: Rc<Body<'tcx>>,
    pub(super) signature: ty::PolyFnSig<'tcx>,
}

// Bound actual retained table lookups separately from immutable certificate comparison.
// Equality/hash of the pinned compiler's interned lists use pointer identity, not type walks.
#[derive(Clone, Copy, Default)]
pub(super) struct RegistryPlan {
    counts: [usize; 3],
}

impl RegistryPlan {
    pub(super) fn current(engine: &Engine<'_>) -> Result<Self, String> {
        Ok(Self {
            counts: [
                engine
                    .mutable_product_sources
                    .try_borrow()
                    .map_err(|_| "product descriptor issuer registry is borrowed")?
                    .len(),
                engine
                    .bodies
                    .try_borrow()
                    .map_err(|_| "product descriptor Body registry is borrowed")?
                    .len(),
                engine
                    .call_signatures
                    .try_borrow()
                    .map_err(|_| "product descriptor signature registry is borrowed")?
                    .len(),
            ],
        })
    }

    pub(super) fn with_pending_sources(mut self, count: usize) -> Result<Self, String> {
        self.counts[0] = self.counts[0]
            .checked_add(count)
            .ok_or("product descriptor pending source inventory overflow")?;
        Ok(self)
    }

    pub(super) fn with_pending_bodies(mut self, count: usize) -> Result<Self, String> {
        self.counts[1] = self.counts[1]
            .checked_add(count)
            .ok_or("product descriptor pending Body inventory overflow")?;
        Ok(self)
    }

    pub(super) fn with_pending_signatures(mut self, count: usize) -> Result<Self, String> {
        self.counts[2] = self.counts[2]
            .checked_add(count)
            .ok_or("product descriptor pending signature inventory overflow")?;
        Ok(self)
    }

    pub(super) fn work(self) -> Result<usize, String> {
        self.counts.iter().try_fold(16usize, |sum, count| {
            sum.checked_add(*count)
                .ok_or_else(|| "product source lookup work overflow".into())
        })
    }

    pub(super) fn covers(self, current: Self) -> bool {
        self.counts
            .iter()
            .zip(current.counts)
            .all(|(paid, actual)| actual <= *paid)
    }

    pub(super) fn expanded(self, current: Self) -> Self {
        Self {
            counts: std::array::from_fn(|index| self.counts[index].max(current.counts[index])),
        }
    }
}

impl<'tcx> Binding<'tcx> {
    pub(super) fn validate_source(&self, engine: &Engine<'tcx>) -> Result<(), String> {
        engine.mutable_product_descriptor_source_matches(self)?;
        let bodies = engine
            .bodies
            .try_borrow()
            .map_err(|_| "product descriptor current Body registry is borrowed")?;
        let signatures = engine
            .call_signatures
            .try_borrow()
            .map_err(|_| "product descriptor current signature registry is borrowed")?;
        if bodies
            .get(&self.instance)
            .is_none_or(|current| !Rc::ptr_eq(current, &self.body))
            || signatures
                .get(&self.instance)
                .is_some_and(|current| *current != self.signature)
        {
            return Err(
                "product descriptor original/current Body or full signature differs".into(),
            );
        }
        Ok(())
    }

    pub(super) fn input_local(
        &self,
        engine: &mut Engine<'tcx>,
        original: Ty<'tcx>,
    ) -> Result<Option<rustc_middle::mir::Local>, String> {
        if self.body.arg_count > MAX_INPUT_VALUES {
            return Err("product descriptor actual input inventory exceeds existing bound".into());
        }
        mutable_hierarchy::products::pay(engine, 4 * self.body.arg_count + 8)?;
        Ok(self.body.args_iter().find(|local| {
            matches!(self.body.local_decls[*local].ty.kind(),
                ty::Ref(_, inner, mutability) if mutability.is_mut()
                    && matches!(inner.kind(), ty::Slice(element) if *element == original))
        }))
    }
}

pub(super) struct Prepared<'tcx> {
    binding: Binding<'tcx>,
    original: Ty<'tcx>,
    policy: DescriptorPolicy,
    context: Term,
    descriptor: CompositeType<'tcx>,
    alignment: u64,
    input_local: rustc_middle::mir::Local,
    compare_work: usize,
}

impl<'tcx> Prepared<'tcx> {
    pub(super) fn compare_work(&self) -> usize {
        self.compare_work
    }

    pub(super) fn matches_binding(&self, binding: &Binding<'tcx>) -> bool {
        self.binding.frame == binding.frame
            && self.binding.instance == binding.instance
            && self.binding.signature == binding.signature
            && Rc::ptr_eq(&self.binding.body, &binding.body)
    }

    pub(super) fn validate_source(&self, engine: &Engine<'tcx>) -> Result<(), String> {
        if !self.context.belongs_to(&engine.terms) {
            return Err("product descriptor Context differs".into());
        }
        if !matches!(self.binding.body.local_decls[self.input_local].ty.kind(),
            ty::Ref(_, inner, mutability) if mutability.is_mut()
                && matches!(inner.kind(), ty::Slice(element) if *element == self.original))
        {
            return Err("product descriptor actual input original type differs".into());
        }
        self.binding.validate_source(engine)?;
        Ok(())
    }

    pub(super) fn compare(&self, certificate: &IntegerCertificate<'tcx>) -> Result<(), String> {
        let ElementCodec::Product(issued) = &certificate.codec else {
            return Err("mutable product needs an exact product certificate".into());
        };
        if certificate.original != self.original
            || issued.ty != self.original
            || issued.bytes != self.descriptor.bytes
            || issued.leaves != self.descriptor.leaves
            || !mutable_products::same_product_shape(&issued.shape, &self.descriptor.shape)
            || certificate.bytes != self.descriptor.bytes
            || certificate.alignment != self.alignment
        {
            return Err(
                "mutable product certificate differs from exact original compiler type".into(),
            );
        }
        Ok(())
    }
}

// Only the independently constructed expected shape determines the prepaid comparison bound.
// A hostile actual shape cannot enlarge the traversal: lengths are compared before children.
fn shape_compare_work(shape: &CompositeShape) -> Result<usize, String> {
    let children = match shape {
        CompositeShape::Primitive(_) => 0,
        CompositeShape::Tuple(fields) | CompositeShape::Array(fields) => {
            fields.iter().try_fold(0usize, |sum, field| {
                sum.checked_add(shape_compare_work(field)? + 2)
                    .ok_or_else(|| "product descriptor comparison work overflow".to_owned())
            })?
        }
        CompositeShape::Struct { name, fields } => {
            fields
                .iter()
                .try_fold(name.len() + 4, |sum, (name, field)| {
                    sum.checked_add(name.len() + shape_compare_work(field)? + 4)
                        .ok_or_else(|| "product descriptor comparison work overflow".to_owned())
                })?
        }
        CompositeShape::NonZeroNiche(_) | CompositeShape::Sum { .. } => {
            return Err("pure product descriptor cannot admit sums or niches".into());
        }
    };
    children
        .checked_add(4)
        .ok_or_else(|| "product comparison work overflow".into())
}

pub(super) fn prepare<'tcx>(
    engine: &mut Engine<'tcx>,
    binding: Binding<'tcx>,
    certificate: usize,
    original: Ty<'tcx>,
) -> Result<(Rc<Prepared<'tcx>>, bool), String> {
    let result = prepare_inner(engine, binding, certificate, original);
    if result.is_err() {
        engine.mutable_product_failed.set(true);
    }
    result
}

fn prepare_inner<'tcx>(
    engine: &mut Engine<'tcx>,
    binding: Binding<'tcx>,
    certificate: usize,
    original: Ty<'tcx>,
) -> Result<(Rc<Prepared<'tcx>>, bool), String> {
    use mutable_hierarchy::products::{pay, work};
    let count = engine.mutable_product_descriptors.len();
    if count > MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "product descriptor catalogue exceeds existing512 bound".into(),
        ));
    }
    // Catalogue scan, Rc retention and source binding checks precede any retained lookup.
    pay(engine, 24 + 8 * count)?;
    let prior = engine
        .mutable_product_descriptors
        .iter()
        .find(|prepared| {
            prepared.binding.frame == binding.frame
                && prepared.original == original
                && prepared.policy == DescriptorPolicy::PureProduct
        })
        .cloned();
    if let Some(prior) = prior {
        if prior.binding.instance != binding.instance
            || prior.binding.signature != binding.signature
            || !Rc::ptr_eq(&prior.binding.body, &binding.body)
        {
            return Err("product descriptor retained issuer binding changed".into());
        }
        let source_work = RegistryPlan::current(engine)?.work()?;
        pay(engine, prior.compare_work + source_work)?;
        prior.validate_source(engine)?;
        prior.compare(
            engine
                .mutable_integer_types
                .get(certificate)
                .ok_or("product descriptor mutable certificate absent")?,
        )?;
        return Ok((prior, false));
    }
    if count == MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "product descriptor catalogue exceeds existing512 bound".into(),
        ));
    }
    let input_local = binding
        .input_local(engine, original)?
        .ok_or("product descriptor has no actual mutable slice input of its original type")?;
    let construction = work::descriptor_work(engine, original)?;
    // Actual construction/layout and the once-only immutable comparison-plan traversal.
    pay(
        engine,
        construction
            .checked_mul(2)
            .and_then(|work| work.checked_add(64))
            .ok_or("product descriptor preparation work overflow")?,
    )?;
    let descriptor = engine
        .mutable_product_shape(original)?
        .ok_or("product descriptor original type is unsupported")?;
    let alignment = engine.static_layout(original)?.align.abi.bytes();
    let compare_work = 24 + 2 * descriptor.leaves.len() + shape_compare_work(&descriptor.shape)?;
    let prepared = Rc::new(Prepared {
        binding,
        original,
        policy: DescriptorPolicy::PureProduct,
        context: engine.terms.boolean(true),
        descriptor,
        alignment,
        input_local,
        compare_work,
    });
    let source_work = RegistryPlan::current(engine)?.work()?;
    pay(engine, compare_work + source_work + 8)?;
    prepared.validate_source(engine)?;
    prepared.compare(
        engine
            .mutable_integer_types
            .get(certificate)
            .ok_or("product descriptor mutable certificate absent")?,
    )?;
    // No template derived from the mutable certificate is ever published, even on refusal.
    Ok((prepared, true))
}
