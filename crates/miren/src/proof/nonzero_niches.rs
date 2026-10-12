//! Exact bounded readonly for exact zero-only NonZero<u16> niche observations.
use super::*;
#[path = "nonzero_niche_comparisons.rs"]
mod comparisons;
use rustc_abi::{BackendRepr, FieldIdx, Integer, Primitive, Scalar, TagEncoding, Variants};
use rustc_middle::mir::Local;
use rustc_middle::ty::{AdtFlags, CoroutineArgsExt, TypeVisitableExt};

#[derive(Clone, Debug)]
struct NicheFacts {
    parent: BackendRepr,
    tag: Scalar,
    payload: BackendRepr,
    inner: BackendRepr,
    primitive: BackendRepr,
    size: u64,
    align: u64,
    payload_size: u64,
    payload_align: u64,
    inner_size: u64,
    inner_align: u64,
    tag_offset: u64,
    payload_offset: u64,
    inner_offset: u64,
    tag_field: usize,
    parent_fields: usize,
    untagged: usize,
    niche_first: usize,
    niche_last: usize,
    niche_start: u128,
    empty_size: u64,
    empty_repr: BackendRepr,
}

fn scalar_range(repr: BackendRepr, start: u128) -> bool {
    matches!(repr, BackendRepr::Scalar(Scalar::Initialized {
        value: Primitive::Int(Integer::I16, false), valid_range,
    }) if valid_range.start == start && valid_range.end == u16::MAX.into())
}

fn facts_match(facts: &NicheFacts) -> bool {
    facts.untagged < 2
        && facts.niche_first == 1 - facts.untagged
        && facts.niche_last == facts.niche_first
        && facts.niche_start == 0
        && facts.tag_field == 0
        && facts.parent_fields == 1
        && facts.tag_offset == 0
        && facts.payload_offset == 0
        && facts.inner_offset == 0
        && facts.size == 2
        && facts.align == 2
        && facts.payload_size == 2
        && facts.payload_align == 2
        && facts.inner_size == 2
        && facts.inner_align == 2
        && facts.empty_size == 0
        && facts.empty_repr == (BackendRepr::Memory { sized: true })
        && facts.parent == BackendRepr::Scalar(facts.tag)
        && scalar_range(facts.parent, 0)
        && scalar_range(facts.primitive, 0)
        && scalar_range(facts.payload, 1)
        && scalar_range(facts.inner, 1)
}

#[derive(Clone)]
struct Certificate<'tcx> {
    original: Ty<'tcx>,
    nonzero: Ty<'tcx>,
    inner: Ty<'tcx>,
    inner_name: String,
    outer_name: String,
    inner_field: String,
    outer_field: String,
    payload_field: String,
    payload_variant: usize,
    tags: [u128; 2],
    bits: u32,
    signed: bool,
    facts: NicheFacts,
}

fn layout<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
) -> Result<ty::layout::TyAndLayout<'tcx>, String> {
    tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(original))
        .map_err(|error| format!("NonZero layout unavailable: {error:?}"))
}

fn certify<'tcx>(tcx: TyCtxt<'tcx>, original: Ty<'tcx>) -> Result<Certificate<'tcx>, String> {
    let ty::Adt(def, args) = original.kind() else {
        return Err("NonZero niche requires original enum".into());
    };
    if original.has_escaping_bound_vars() {
        return Err("NonZero original type is not fully instantiated".into());
    }
    let env = ty::TypingEnv::fully_monomorphized();
    let option = tcx.lang_items().get(LangItem::Option) == Some(def.did());
    let ordinary = def.did().is_local()
        && (def.flags() == AdtFlags::IS_ENUM
            || def.flags() == (AdtFlags::IS_ENUM | AdtFlags::HAS_CTOR));
    if (!option && !ordinary)
        || !def.is_enum()
        || def.variants().len() != 2
        || def.repr().pack.is_some()
        || !original.is_freeze(tcx, env)
        || !tcx.type_is_copy_modulo_regions(env, original)
        || original.needs_drop(tcx, env)
    {
        return Err("NonZero niche original enum identity or purity mismatch".into());
    }
    let parent = layout(tcx, original)?;
    let Variants::Multiple {
        tag,
        tag_encoding:
            TagEncoding::Niche {
                untagged_variant,
                niche_variants,
                niche_start,
            },
        tag_field,
        variants,
    } = &parent.variants
    else {
        return Err("NonZero niche requires actual niche encoding".into());
    };
    if variants.len() != 2 || untagged_variant.as_usize() >= 2 {
        return Err("NonZero niche variant inventory mismatch".into());
    }
    let payload_variant = *untagged_variant;
    let empty_variant = rustc_abi::VariantIdx::from_usize(1 - payload_variant.as_usize());
    let payload = def.variant(payload_variant);
    let empty = def.variant(empty_variant);
    let actual_payload = &variants[payload_variant];
    let actual_empty = &variants[empty_variant];
    if payload.fields.len() != 1
        || !empty.fields.is_empty()
        || actual_payload.field_offsets.len() != 1
        || !actual_empty.field_offsets.is_empty()
        || parent.fields.count() != 1
        || tag_field.as_usize() != 0
        || parent.uninhabited
        || actual_payload.is_uninhabited()
        || actual_empty.is_uninhabited()
    {
        return Err("NonZero niche original variant schema mismatch".into());
    }
    let field = FieldIdx::from_usize(0);
    // Inspect original payload before any normalization. Only the anchored associated
    // inner field is subsequently resolved; arbitrary Pat payloads are never normalized.
    let nonzero_ty = payload.fields[field].ty(tcx, args).skip_norm_wip();
    let ty::Adt(nonzero, nz_args) = nonzero_ty.kind() else {
        return Err("NonZero niche requires actual NonZero wrapper".into());
    };
    let Some(anchor) = tcx.get_diagnostic_item(rustc_span::Symbol::intern("NonZero")) else {
        return Err("NonZero diagnostic anchor unavailable".into());
    };
    if nonzero.did() != anchor
        || tcx
            .lang_items()
            .sized_trait()
            .is_none_or(|sized| sized.krate != anchor.krate)
        || !nonzero.is_struct()
        || nz_args.len() != 1
        || nz_args.type_at(0) != tcx.types.u16
        || nonzero.non_enum_variant().fields.len() != 1
        || !nonzero_ty.is_freeze(tcx, env)
        || !tcx.type_is_copy_modulo_regions(env, nonzero_ty)
        || nonzero_ty.needs_drop(tcx, env)
    {
        return Err("NonZero wrapper original identity mismatch".into());
    }
    if option
        && (args.len() != 1
            || args.type_at(0) != nonzero_ty
            || payload_variant.as_usize() != 1
            || payload.name.as_str() != "Some"
            || empty.name.as_str() != "None")
    {
        return Err("NonZero Option original identity mismatch".into());
    }
    let original_inner = nonzero.non_enum_variant().fields[field].ty(tcx, nz_args);
    let inner_ty = tcx
        .try_normalize_erasing_regions(env, original_inner)
        .map_err(|error| format!("NonZero associated inner unavailable: {error:?}"))?;
    let ty::Adt(inner, inner_args) = inner_ty.kind() else {
        return Err("NonZero requires actual scalar inner ADT".into());
    };
    if inner.did().krate != anchor.krate
        || !inner.is_struct()
        || inner.non_enum_variant().fields.len() != 1
    {
        return Err("NonZero associated inner identity mismatch".into());
    }
    let raw = inner.non_enum_variant().fields[field]
        .ty(tcx, inner_args)
        .skip_norm_wip();
    if !matches!(raw.kind(), ty::Pat(base, _) if *base == tcx.types.u16) {
        return Err("NonZero original inner must be exact Pat<u16>".into());
    }
    let nz_layout = layout(tcx, nonzero_ty)?;
    let inner_layout = layout(tcx, inner_ty)?;
    let raw_layout = layout(tcx, raw)?;
    if nz_layout.fields.count() != 1
        || inner_layout.fields.count() != 1
        || raw_layout.backend_repr != inner_layout.backend_repr
        || raw_layout.size != inner_layout.size
        || raw_layout.align.abi != inner_layout.align.abi
        || actual_payload.size != nz_layout.size
        || actual_payload.backend_repr != nz_layout.backend_repr
    {
        return Err("NonZero original storage wrapper mismatch".into());
    }
    let facts = NicheFacts {
        parent: parent.backend_repr,
        tag: *tag,
        payload: nz_layout.backend_repr,
        inner: inner_layout.backend_repr,
        primitive: layout(tcx, tcx.types.u16)?.backend_repr,
        size: parent.size.bytes(),
        align: parent.align.abi.bytes(),
        payload_size: nz_layout.size.bytes(),
        payload_align: nz_layout.align.abi.bytes(),
        inner_size: inner_layout.size.bytes(),
        inner_align: inner_layout.align.abi.bytes(),
        tag_offset: parent.fields.offset(0).bytes(),
        payload_offset: actual_payload.field_offsets[field].bytes(),
        inner_offset: inner_layout.fields.offset(0).bytes(),
        tag_field: tag_field.as_usize(),
        parent_fields: parent.fields.count(),
        untagged: payload_variant.as_usize(),
        niche_first: niche_variants.start.as_usize(),
        niche_last: niche_variants.last.as_usize(),
        niche_start: *niche_start,
        empty_size: actual_empty.size.bytes(),
        empty_repr: actual_empty.backend_repr,
    };
    if !facts_match(&facts) || nz_layout.fields.offset(0).bytes() != 0 {
        return Err("NonZero zero-only compiler scalar partition mismatch".into());
    }
    let discriminant = original.discriminant_ty(tcx);
    let (bits, signed) = match discriminant.kind() {
        ty::Int(ty::IntTy::Isize) => (u32::from(tcx.sess.target.pointer_width), true),
        ty::Uint(ty::UintTy::Usize) => (u32::from(tcx.sess.target.pointer_width), false),
        _ => return Err("NonZero unsupported original discriminant type".into()),
    };
    let tags = [
        def.discriminant_for_variant(tcx, rustc_abi::VariantIdx::from_usize(0))
            .val,
        def.discriminant_for_variant(tcx, rustc_abi::VariantIdx::from_usize(1))
            .val,
    ];
    if tags != [0, 1] {
        return Err("NonZero original discriminant mapping mismatch".into());
    }
    Ok(Certificate {
        original,
        nonzero: nonzero_ty,
        inner: inner_ty,
        inner_name: tcx.def_path_str(inner.did()),
        outer_name: tcx.def_path_str(nonzero.did()),
        inner_field: inner.non_enum_variant().fields[field]
            .name
            .as_str()
            .to_owned(),
        outer_field: nonzero.non_enum_variant().fields[field]
            .name
            .as_str()
            .to_owned(),
        payload_field: payload.fields[field].name.as_str().to_owned(),
        payload_variant: payload_variant.as_usize(),
        tags,
        bits,
        signed,
        facts,
    })
}

#[cfg(test)]
#[derive(Clone)]
enum Shape<'tcx> {
    Sum(Box<Certificate<'tcx>>),
    Array(Vec<Shape<'tcx>>),
}

#[cfg(test)]
fn shape<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
    depth: usize,
    nodes: &mut usize,
) -> Result<Shape<'tcx>, String> {
    if depth >= 16 || *nodes >= 512 {
        return Err("NonZero original shape budget exceeded".into());
    }
    *nodes += 1;
    if let ty::Array(element, count) = original.kind() {
        let count = count
            .try_to_target_usize(tcx)
            .ok_or("inactive array count unavailable")?;
        if count > 128 {
            return Err("NonZero array count exceeds128".into());
        }
        let first = shape(tcx, *element, depth + 1, nodes)?;
        let mut fields = Vec::new();
        if count != 0 {
            fields.push(first);
            for _ in 1..count {
                fields.push(shape(tcx, *element, depth + 1, nodes)?);
            }
        }
        return Ok(Shape::Array(fields));
    }
    let certificate = certify(tcx, original)?;
    // Charge both variants, exact NonZero outer, associated inner and original Pat node.
    *nodes = nodes.checked_add(5).ok_or("NonZero node cost overflow")?;
    if *nodes > 512 || depth + 3 >= 16 {
        return Err("NonZero expanded wrapper budget exceeded".into());
    }
    Ok(Shape::Sum(Box::new(certificate)))
}

#[cfg(test)]
impl Shape<'_> {
    fn columns(&self) -> usize {
        match self {
            Self::Sum(certificate) => {
                assert!(facts_match(&certificate.facts));
                1
            }
            Self::Array(fields) => fields.iter().map(Self::columns).sum(),
        }
    }
}

// This prototype deliberately does not publish a Value::Enum containing an invalid latent
// NonZero ADT. Until runtime snapshot/graph/flatten/callee transport is independently audited,
// the inactive raw pair stays private and only guarded_payload can issue a standalone value.
#[cfg(test)]
#[derive(Clone)]
struct Observation<'tcx> {
    certificate: Certificate<'tcx>,
    raw: Term,
    discriminant: Term,
}

#[cfg(test)]
impl<'tcx> Observation<'tcx> {
    fn new(
        context: &Context,
        certificate: &Certificate<'tcx>,
        array: &Term,
        index: &Term,
        pointer_bits: u32,
    ) -> Result<Self, String> {
        if !matches!(pointer_bits, 32 | 64)
            || certificate.bits != pointer_bits
            || !certificate.signed
            || certificate.tags != [0, 1]
            || certificate.payload_variant != certificate.facts.untagged
            || index.sort() != &Sort::BitVec(pointer_bits)
            || array.sort()
                != &Sort::Array(
                    Box::new(Sort::BitVec(pointer_bits)),
                    Box::new(Sort::BitVec(16)),
                )
            || !array.belongs_to(context)
            || !index.belongs_to(context)
            || !facts_match(&certificate.facts)
        {
            return Err("NonZero observation metadata mismatch".into());
        }
        let raw = context.apply(Op::Select, &[array.clone(), index.clone()])?;
        let zero = context.apply(Op::Equal, &[raw.clone(), context.bit_vector(0, 16)?])?;
        let payload = certificate.payload_variant;
        let discriminant = context.apply(
            Op::Ite,
            &[
                zero,
                context.bit_vector(certificate.tags[1 - payload], certificate.bits)?,
                context.bit_vector(certificate.tags[payload], certificate.bits)?,
            ],
        )?;
        Ok(Self {
            certificate: certificate.clone(),
            raw,
            discriminant,
        })
    }

    fn guarded_payload(&self, context: &Context, conditions: &[Term]) -> Result<Value, String> {
        let active = context.apply(
            Op::Equal,
            &[
                self.discriminant.clone(),
                context.bit_vector(
                    self.certificate.tags[self.certificate.payload_variant],
                    self.certificate.bits,
                )?,
            ],
        )?;
        let zero = context.apply(Op::Equal, &[self.raw.clone(), context.bit_vector(0, 16)?])?;
        let mut solver = Solver::default();
        let active_failure = Query::from_terms(
            context,
            conditions,
            &symbolic::not(&active),
            &BTreeMap::new(),
        )?;
        if !matches!(solver.check_query(&active_failure), Answer::Unsat) {
            return Err("NonZero payload requires proven active variant".into());
        }
        let zero_failure = Query::from_terms(context, conditions, &zero, &BTreeMap::new())?;
        if !matches!(solver.check_query(&zero_failure), Answer::Unsat) {
            return Err("NonZero payload requires proven nonzero value".into());
        }
        let ty::Adt(_, _) = self.certificate.nonzero.kind() else {
            return Err("NonZero certificate lost original wrapper".into());
        };
        let ty::Adt(_, _) = self.certificate.inner.kind() else {
            return Err("NonZero certificate lost original inner".into());
        };
        let inner = Value::Adt {
            name: self.certificate.inner_name.clone(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: vec![(
                self.certificate.inner_field.clone(),
                Value::Int {
                    expression: self.raw.clone(),
                    bits: 16,
                    signed: false,
                },
            )]
            .into(),
        };
        Ok(Value::Adt {
            name: self.certificate.outer_name.clone(),
            variant: 0,
            discriminant: 0,
            is_option: false,
            fields: vec![(self.certificate.outer_field.clone(), inner)].into(),
        })
    }
}

#[test]
fn exact_compiler_nonzero_niche_and_private_latent_observations() {
    struct Check {
        checked: bool,
    }
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let mut originals = BTreeMap::new();
            for id in tcx.mir_keys(()).iter().copied() {
                if tcx.def_kind(id) != DefKind::Fn {
                    continue;
                }
                let input = tcx.fn_sig(id).instantiate_identity().skip_binder().inputs()[0];
                let ty::Ref(_, pointee, _) = *input.kind() else {
                    continue;
                };
                let ty::Slice(element) = *pointee.kind() else {
                    continue;
                };
                originals.insert(tcx.item_name(id.to_def_id()).as_str().to_owned(), element);
            }
            for name in ["option", "word", "reversed"] {
                let original = originals[name];
                let certificate = certify(tcx, original).unwrap();
                assert_eq!(certificate.original, original);
                assert_eq!(certificate.payload_field, "0");
                assert_eq!(certificate.outer_field, "0");
                assert_eq!(certificate.inner_field, "0");
                assert!(certificate.signed);
                assert_eq!(certificate.bits, u32::from(tcx.sess.target.pointer_width));
                assert_eq!(certificate.payload_variant, usize::from(name != "reversed"));
                assert!(facts_match(&certificate.facts));
                let mut nodes = 0;
                assert_eq!(shape(tcx, original, 0, &mut nodes).unwrap().columns(), 1);
                assert_eq!(nodes, 6);
                check_selected_getter_body(tcx, &certificate, originals["external_wrapper"]);
                check_metadata_mutations(&certificate.facts);
                check_observation(&certificate, u32::from(tcx.sess.target.pointer_width));
            }
            let mut nodes = 0;
            assert_eq!(
                shape(tcx, originals["zero"], 0, &mut nodes)
                    .unwrap()
                    .columns(),
                0
            );
            assert_eq!(nodes, 7);
            for name in [
                "zero_ref",
                "zero_pat",
                "wrong_width",
                "wrong_sign",
                "plain",
                "extra",
                "drop",
            ] {
                assert!(shape(tcx, originals[name], 0, &mut 0).is_err(), "{name}");
            }
            for name in ["wide", "expanded"] {
                assert!(shape(tcx, originals[name], 0, &mut 0).is_err(), "{name}");
            }
            assert!(shape(tcx, originals["option"], 13, &mut 0).is_err());
            assert!(shape(tcx, originals["option"], 0, &mut 507).is_err());
            assert!(contains_nonzero16(tcx, originals["many_units"], 0, &mut 0).is_err());
            super::coroutines::check_original_operand_lookup(tcx);
            self.checked = true;
            rustc_driver::Compilation::Stop
        }
    }
    let directory = std::env::temp_dir().join(format!(
        "miren-nonzero-inactive-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&directory).unwrap();
    let source = directory.join("input.rs");
    std::fs::write(
        &source,
        r#"
#![no_std]
#![feature(pattern_types, pattern_type_macro)]
use core::num::{NonZeroU16,NonZeroU32,NonZeroI16};
#[derive(Clone,Copy)] pub enum Word { Empty, Value(NonZeroU16) }
#[derive(Clone,Copy)] pub enum Reversed { Value(NonZeroU16), Empty }
#[derive(Clone,Copy)] pub enum Plain { Empty, Value(u16) }
#[derive(Clone,Copy)] pub enum Extra { Empty, Value(NonZeroU16,u16) }
pub enum Dropping { Empty, Value(NonZeroU16) }
impl Drop for Dropping { fn drop(&mut self) {} }
pub fn external_wrapper(_: &[core::cmp::Reverse<NonZeroU16>]) {}
pub fn option(_: &[Option<NonZeroU16>]) {}
pub fn word(_: &[Word]) {}
pub fn reversed(_: &[Reversed]) {}
pub fn zero(_: &[[Option<NonZeroU16>;0]]) {}
pub fn zero_ref(_: &[[Option<&u16>;0]]) {}
pub fn zero_pat(_: &[[core::pattern_type!(u16 is 1..);0]]) {}
pub fn wrong_width(_: &[Option<NonZeroU32>]) {}
pub fn wrong_sign(_: &[Option<NonZeroI16>]) {}
pub fn plain(_: &[Plain]) {}
pub fn extra(_: &[Extra]) {}
pub fn drop(_: &[Dropping]) {}
pub fn wide(_: &[[Option<NonZeroU16>;129]]) {}
pub fn expanded(_: &[[Option<NonZeroU16>;86]]) {}
pub fn coroutine_probe(input: NonZeroU16) -> impl core::future::Future<Output=u16> {
    async move {
        let saved = [input; 2];
        core::future::ready(()).await;
        saved[0].get()
    }
}
"#
        .to_owned()
            + &format!(
                "enum ManyUnits {{ {} }} pub fn many_units(_: &[ManyUnits]) {{}}",
                (0..513)
                    .map(|index| format!("V{index}"))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
    )
    .unwrap();
    let output = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .unwrap();
    assert!(output.status.success());
    let sysroot = String::from_utf8(output.stdout).unwrap();
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for opt in [0, 2] {
            let mut check = Check { checked: false };
            let mut args = vec![
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                format!("-Copt-level={opt}"),
                "-Zmir-opt-level=0".into(),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
                "--sysroot".into(),
                sysroot.trim().into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.checked);
        }
    }
    std::fs::remove_dir_all(directory).unwrap();
}

#[cfg(test)]
fn check_metadata_mutations(facts: &NicheFacts) {
    let mut wrong = facts.clone();
    wrong.niche_start = 1;
    assert!(!facts_match(&wrong));
    wrong = facts.clone();
    wrong.untagged = 2;
    assert!(!facts_match(&wrong));
    wrong = facts.clone();
    wrong.niche_first = facts.untagged;
    assert!(!facts_match(&wrong));
    wrong = facts.clone();
    wrong.niche_last = 1 - facts.niche_last;
    assert!(!facts_match(&wrong));
    for field in [0, 1, 2, 3, 4, 5, 6, 7] {
        wrong = facts.clone();
        match field {
            0 => wrong.size = 4,
            1 => wrong.align = 1,
            2 => wrong.payload_offset = 1,
            3 => wrong.inner_offset = 1,
            4 => wrong.tag_offset = 1,
            5 => wrong.tag_field = 1,
            6 => wrong.parent_fields = 2,
            7 => wrong.empty_size = 2,
            _ => unreachable!(),
        }
        assert!(!facts_match(&wrong));
    }
    for repr in [
        BackendRepr::Scalar(Scalar::Union {
            value: Primitive::Int(Integer::I16, false),
        }),
        BackendRepr::Scalar(Scalar::Initialized {
            value: Primitive::Int(Integer::I16, true),
            valid_range: rustc_abi::WrappingRange {
                start: 1,
                end: 65535,
            },
        }),
        BackendRepr::Scalar(Scalar::Initialized {
            value: Primitive::Int(Integer::I32, false),
            valid_range: rustc_abi::WrappingRange {
                start: 1,
                end: 65535,
            },
        }),
        BackendRepr::Scalar(Scalar::Initialized {
            value: Primitive::Int(Integer::I16, false),
            valid_range: rustc_abi::WrappingRange {
                start: 0,
                end: 65535,
            },
        }),
        BackendRepr::Scalar(Scalar::Initialized {
            value: Primitive::Int(Integer::I16, false),
            valid_range: rustc_abi::WrappingRange {
                start: 1,
                end: 65534,
            },
        }),
    ] {
        wrong = facts.clone();
        wrong.payload = repr;
        assert!(!facts_match(&wrong));
        wrong = facts.clone();
        wrong.inner = repr;
        assert!(!facts_match(&wrong));
    }
    wrong = facts.clone();
    wrong.tag = Scalar::Initialized {
        value: Primitive::Int(Integer::I16, false),
        valid_range: rustc_abi::WrappingRange {
            start: 1,
            end: 65535,
        },
    };
    wrong.parent = BackendRepr::Scalar(wrong.tag);
    assert!(!facts_match(&wrong));
}

#[cfg(test)]
fn check_observation(certificate: &Certificate<'_>, bits: u32) {
    let context = Context::default();
    let index = context.bit_vector(0, bits).unwrap();
    let array = context
        .symbol(
            0,
            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(16))),
        )
        .unwrap();
    for field in 0..4 {
        let mut forged = certificate.clone();
        match field {
            0 => forged.bits = 16,
            1 => forged.signed = false,
            2 => forged.tags = [1, 0],
            3 => forged.payload_variant = 1 - forged.payload_variant,
            _ => unreachable!(),
        }
        assert!(Observation::new(&context, &forged, &array, &index, bits).is_err());
    }
    let observation = Observation::new(&context, certificate, &array, &index, bits).unwrap();
    assert!(observation.guarded_payload(&context, &[]).is_err());
    let active = context
        .apply(
            Op::Equal,
            &[
                observation.discriminant.clone(),
                context
                    .bit_vector(
                        certificate.tags[certificate.payload_variant],
                        certificate.bits,
                    )
                    .unwrap(),
            ],
        )
        .unwrap();
    let value = observation
        .guarded_payload(&context, std::slice::from_ref(&active))
        .unwrap();
    assert!(matches!(value, Value::Adt { .. }));
    let zero = context
        .apply(
            Op::Equal,
            &[observation.raw.clone(), context.bit_vector(0, 16).unwrap()],
        )
        .unwrap();
    assert!(observation.guarded_payload(&context, &[zero]).is_err());
    // A copied private observation keeps the same raw/tag correlation. It has no Value,
    // allocation or reference carrier for snapshots/graphs/Horn flattening to reinterpret.
    let copied = observation.clone();
    assert_eq!(copied.raw, observation.raw);
    assert_eq!(copied.discriminant, observation.discriminant);
    assert!(copied.guarded_payload(&context, &[]).is_err());
    let wrong = Context::default();
    assert!(Observation::new(&wrong, certificate, &array, &index, bits).is_err());
    let wrong_array = context
        .symbol(
            1,
            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(32))),
        )
        .unwrap();
    assert!(Observation::new(&context, certificate, &wrong_array, &index, bits).is_err());
    let wrong_index = context.bit_vector(0, 16).unwrap();
    assert!(Observation::new(&context, certificate, &array, &wrong_index, bits).is_err());
}

// Enabling this draft requires a separate source/evidence checkpoint. Inactive calls return
// before compiler queries, SMT allocation, source validation or observer-body lookup.
pub(super) const ENABLE_RUNTIME: bool = true;

#[derive(Clone, Debug)]
pub(super) struct Schema {
    name: String,
    is_option: bool,
    variant_names: [String; 2],
    payload_field: String,
    outer_name: String,
    inner_name: String,
    outer_field: String,
    inner_field: String,
    payload_variant: usize,
    tags: [u128; 2],
    bits: u32,
    signed: bool,
    facts: NicheFacts,
}

impl Schema {
    pub(super) fn observe(
        &self,
        context: &Context,
        leaves: &[Term],
        index: &Term,
        cursor: &mut usize,
    ) -> Result<Value, String> {
        let array = leaves.get(*cursor).ok_or("NonZero niche column missing")?;
        if !facts_match(&self.facts)
            || self.payload_variant != self.facts.untagged
            || self.tags != [0, 1]
            || !self.signed
            || !matches!(self.bits, 32 | 64)
            || index.sort() != &Sort::BitVec(self.bits)
            || array.sort()
                != &Sort::Array(
                    Box::new(Sort::BitVec(self.bits)),
                    Box::new(Sort::BitVec(16)),
                )
            || !array.belongs_to(context)
            || !index.belongs_to(context)
        {
            return Err("NonZero niche observation compiler metadata mismatch".into());
        }
        let raw = context.apply(Op::Select, &[array.clone(), index.clone()])?;
        let zero = context.apply(Op::Equal, &[raw.clone(), context.bit_vector(0, 16)?])?;
        let tag = context.apply(
            Op::Ite,
            &[
                zero,
                context.bit_vector(self.tags[1 - self.payload_variant], self.bits)?,
                context.bit_vector(self.tags[self.payload_variant], self.bits)?,
            ],
        )?;
        let inner = Value::Adt {
            name: self.inner_name.clone(),
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields: vec![(
                self.inner_field.clone(),
                Value::Int {
                    expression: raw,
                    bits: 16,
                    signed: false,
                },
            )]
            .into(),
        };
        let payload = Value::Adt {
            name: self.outer_name.clone(),
            variant: 0,
            is_option: false,
            discriminant: 0,
            fields: vec![(self.outer_field.clone(), inner)].into(),
        };
        let variants = (0..2)
            .map(|variant| Value::Adt {
                name: self.name.clone(),
                variant,
                is_option: self.is_option,
                discriminant: self.tags[variant],
                fields: if variant == self.payload_variant {
                    vec![(self.payload_field.clone(), payload.clone())].into()
                } else {
                    Vec::new().into()
                },
            })
            .collect();
        if self.variant_names.iter().any(String::is_empty) {
            return Err("NonZero niche original variant name missing".into());
        }
        *cursor += 1;
        Ok(Value::Enum {
            discriminant: Box::new(Value::Int {
                expression: tag,
                bits: self.bits,
                signed: self.signed,
            }),
            variants,
            is_option: self.is_option,
        })
    }
}

fn schema<'tcx>(tcx: TyCtxt<'tcx>, certificate: Certificate<'tcx>) -> Result<Schema, String> {
    let ty::Adt(def, _) = certificate.original.kind() else {
        unreachable!()
    };
    let (ty::Adt(outer, _), ty::Adt(inner, _)) =
        (certificate.nonzero.kind(), certificate.inner.kind())
    else {
        return Err("NonZero niche original payload schema missing".into());
    };
    if certificate.outer_name != tcx.def_path_str(outer.did())
        || certificate.inner_name != tcx.def_path_str(inner.did())
    {
        return Err("NonZero niche original payload name mismatch".into());
    }
    Ok(Schema {
        name: tcx.def_path_str(def.did()),
        is_option: tcx.lang_items().get(LangItem::Option) == Some(def.did()),
        variant_names: [
            def.variants()[rustc_abi::VariantIdx::from_usize(0)]
                .name
                .to_string(),
            def.variants()[rustc_abi::VariantIdx::from_usize(1)]
                .name
                .to_string(),
        ],
        payload_field: certificate.payload_field,
        outer_name: certificate.outer_name,
        inner_name: certificate.inner_name,
        outer_field: certificate.outer_field,
        inner_field: certificate.inner_field,
        payload_variant: certificate.payload_variant,
        tags: certificate.tags,
        bits: certificate.bits,
        signed: certificate.signed,
        facts: certificate.facts,
    })
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn nonzero_niche_shape(
        &self,
        original: Ty<'tcx>,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<Option<Schema>, String> {
        if !ENABLE_RUNTIME {
            return Ok(None);
        }
        let ty::Adt(def, args) = original.kind() else {
            return Ok(None);
        };
        if !def.is_enum()
            || !def.variants().iter().any(|variant| {
                variant.fields.iter().any(|field| {
                    matches!(field.ty(self.tcx, args).skip_norm_wip().kind(), ty::Adt(payload, _)
                        if self.tcx.is_diagnostic_item(
                            rustc_span::Symbol::intern("NonZero"), payload.did()))
                })
            })
        {
            return Ok(None);
        }
        if depth + 3 >= 16 || nodes.saturating_add(5) > 512 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "NonZero niche original child exceeds composite shape budget".into(),
            ));
        }
        let certificate = certify(self.tcx, original)
            .map_err(|reason| self.categorized_error(UnknownCategory::Semantics, reason))?;
        if self.induction {
            return Err("NonZero niche Horn reconstruction is unsupported".into());
        }
        *nodes += 5;
        Ok(Some(schema(self.tcx, certificate)?))
    }

    pub(super) fn nonzero_niche_admission(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        if !ENABLE_RUNTIME {
            return Ok(());
        }
        let ty::Adt(def, args) = original.kind() else {
            return Ok(());
        };
        if !self
            .tcx
            .is_diagnostic_item(rustc_span::Symbol::intern("NonZero"), def.did())
        {
            return Ok(());
        }
        if args.len() != 1 {
            return Err("NonZero niche standalone original argument count mismatch".into());
        }
        if args.type_at(0) != self.tcx.types.u16 {
            return Ok(());
        }
        self.nonzero_niche_checked_value(original, value, conditions)?;
        Ok(())
    }
}

impl<'tcx> Engine<'tcx> {
    fn nonzero_niche_checked_value(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let option = self
            .tcx
            .lang_items()
            .get(LangItem::Option)
            .ok_or("NonZero payload original Option anchor unavailable")?;
        let parent = Ty::new_adt(
            self.tcx,
            self.tcx.adt_def(option),
            self.tcx.mk_args(&[original.into()]),
        );
        let certificate = certify(self.tcx, parent)?;
        if certificate.nonzero != original {
            return Err("NonZero payload original type mismatch".into());
        }
        self.nonzero_integer_transmute(original, self.tcx.types.u16, value, conditions)?
            .ok_or_else(|| "NonZero niche standalone original identity missing".into())
    }

    pub(super) fn nonzero_get_body_certificate(
        &self,
        instance: ty::Instance<'tcx>,
        receiver: Ty<'tcx>,
    ) -> Result<(), String> {
        let callee = instance.def_id();
        let anchor = self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("NonZero"))
            .ok_or("NonZero getter compiler anchor unavailable")?;
        if self.tcx.def_kind(callee) != DefKind::AssocFn
            || callee.krate != anchor.krate
            || self.tcx.item_name(callee) != rustc_span::Symbol::intern("get")
        {
            return Err("NonZero getter selected method identity mismatch".into());
        }
        let parent = self.tcx.parent(callee);
        if !matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: false })
            || !matches!(receiver.kind(), ty::Adt(def, args)
                if def.did() == anchor && args.len() == 1 && args.type_at(0) == self.tcx.types.u16)
            || self
                .tcx
                .type_of(parent)
                .instantiate(self.tcx, instance.args)
                .skip_norm_wip()
                != receiver
        {
            return Err("NonZero getter selected receiver identity mismatch".into());
        }
        let signature = self.call_signature(instance)?;
        if signature.inputs() != [receiver]
            || signature.output() != self.tcx.types.u16
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.safety() != rustc_hir::Safety::Safe
            || signature.c_variadic()
            || !matches!(instance.def, ty::InstanceKind::Item(_))
        {
            return Err("NonZero getter requires exact safe instantiated signature".into());
        }
        // Availability is checked by instantiated_body; preserve MissingCompilerEvidence.
        let body = self.instantiated_body(instance)?;
        if getter_work(&body) > 512 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "NonZero getter body exceeds its 512-node certificate budget".into(),
            ));
        }
        certify_get_body(&body, receiver, self.tcx.types.u16)
    }
}

fn certify_get_body<'tcx>(
    body: &Body<'tcx>,
    receiver: Ty<'tcx>,
    output: Ty<'tcx>,
) -> Result<(), String> {
    if getter_work(body) > 512 {
        return Err("NonZero getter body exceeds its 512-node certificate budget".into());
    }
    if body.arg_count != 1
        || body.local_decls.len() != 2
        || body.local_decls[Local::from_usize(0)].ty != output
        || body.local_decls[Local::from_usize(1)].ty != receiver
        || body.coroutine.is_some()
        || body.spread_arg.is_some()
        || body.tainted_by_errors.is_some()
        || body.basic_blocks.len() != 1
    {
        return Err("NonZero getter body has unsupported receiver or CFG".into());
    }
    let block = &body.basic_blocks[rustc_middle::mir::START_BLOCK];
    if block.is_cleanup || !matches!(block.terminator().kind, TerminatorKind::Return) {
        return Err("NonZero getter body has unsupported effect or cleanup".into());
    }
    let mut assigned = false;
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Assign(assignment) => {
                let (destination, rvalue) = &**assignment;
                if assigned || destination.as_local() != Some(Local::from_usize(0)) {
                    return Err("NonZero getter has a different destination".into());
                }
                let Rvalue::Cast(rustc_middle::mir::CastKind::Transmute, operand, target) = rvalue
                else {
                    return Err("NonZero getter lacks exact compiler transmute".into());
                };
                if *target != output
                    || !matches!(operand, Operand::Copy(place) | Operand::Move(place)
                        if place.as_local() == Some(Local::from_usize(1)))
                {
                    return Err("NonZero getter transmute changes receiver or type".into());
                }
                assigned = true;
            }
            StatementKind::Nop => {}
            _ => return Err("NonZero getter has unsupported statement effects".into()),
        }
    }
    if !assigned {
        return Err("NonZero getter result is not initialized".into());
    }
    Ok(())
}

#[cfg(test)]
fn check_selected_getter_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    certificate: &Certificate<'tcx>,
    external: Ty<'tcx>,
) {
    let ty::Adt(nonzero, args) = certificate.nonzero.kind() else {
        panic!("original NonZero")
    };
    let selected = tcx
        .inherent_impls(nonzero.did())
        .iter()
        .find_map(|implementation| {
            tcx.associated_items(*implementation)
                .in_definition_order()
                .find(|item| item.name() == rustc_span::Symbol::intern("get"))
                .map(|item| item.def_id)
        })
        .unwrap();
    let instance =
        ty::Instance::try_resolve(tcx, ty::TypingEnv::fully_monomorphized(), selected, args)
            .unwrap()
            .unwrap();
    let engine = test_engine(tcx);
    engine
        .nonzero_get_body_certificate(instance, certificate.nonzero)
        .unwrap();
    let context = &engine.terms;
    let raw = context.symbol(42, Sort::BitVec(16)).unwrap();
    let inner = Value::Adt {
        name: certificate.inner_name.clone(),
        variant: 0,
        is_option: false,
        discriminant: 0,
        fields: vec![(
            certificate.inner_field.clone(),
            Value::Int {
                expression: raw.clone(),
                bits: 16,
                signed: false,
            },
        )]
        .into(),
    };
    let value = Value::Adt {
        name: certificate.outer_name.clone(),
        variant: 0,
        is_option: false,
        discriminant: 0,
        fields: vec![(certificate.outer_field.clone(), inner)].into(),
    };
    assert!(
        engine
            .nonzero_niche_checked_value(certificate.nonzero, &value, &[])
            .is_err()
    );
    let zero = context
        .apply(
            Op::Equal,
            &[raw.clone(), context.bit_vector(0, 16).unwrap()],
        )
        .unwrap();
    let active = symbolic::not(&zero);
    assert!(
        engine
            .nonzero_niche_checked_value(certificate.nonzero, &value, std::slice::from_ref(&active))
            .is_ok()
    );
    assert!(
        engine
            .nonzero_niche_checked_value(certificate.nonzero, &value, &[zero])
            .is_err()
    );
    let copied = value.clone();
    assert!(
        engine
            .nonzero_niche_checked_value(
                certificate.nonzero,
                &copied,
                std::slice::from_ref(&active)
            )
            .is_ok()
    );
    assert!(
        engine
            .nonzero_niche_checked_value(tcx.types.u16, &value, std::slice::from_ref(&active))
            .is_err()
    );
    for fault in 0..4 {
        let mut wrong = value.clone();
        let Value::Adt {
            name,
            variant,
            fields,
            ..
        } = &mut wrong
        else {
            unreachable!()
        };
        match fault {
            0 => *name = "local::lookalike".into(),
            1 => *variant = 1,
            2 => fields[0].0 = "wrong".into(),
            3 => {
                let Value::Adt { fields, .. } = &mut fields[0].1 else {
                    unreachable!()
                };
                fields[0].1 = symbolic::integer(&Context::default(), 1, 16, false);
            }
            _ => unreachable!(),
        }
        assert!(
            engine
                .nonzero_niche_checked_value(
                    certificate.nonzero,
                    &wrong,
                    std::slice::from_ref(&active)
                )
                .is_err()
        );
    }
    assert!(tcx.is_mir_available(instance.def_id()));
    let body = instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(tcx, tcx.instance_mir(instance.def).clone()),
        )
        .unwrap();
    let result = certify_get_body(&body, certificate.nonzero, tcx.types.u16);
    assert!(result.is_ok(), "{result:?}: {body:?}");
    let mut malformed = body.clone();
    malformed.spread_arg = Some(Local::from_usize(1));
    assert!(certify_get_body(&malformed, certificate.nonzero, tcx.types.u16).is_err());
    malformed = body.clone();
    let mut nop = malformed.basic_blocks[rustc_middle::mir::START_BLOCK].statements[0].clone();
    nop.kind = StatementKind::Nop;
    malformed.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK]
        .statements
        .extend(std::iter::repeat_n(nop, 512));
    assert!(getter_work(&malformed) > 512);
    assert!(certify_get_body(&malformed, certificate.nonzero, tcx.types.u16).is_err());
    check_copy_path(tcx, certificate, &body);
    check_external_copy_path(tcx, certificate, &body, external);

    let mut wrong = body.clone();
    wrong.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK].is_cleanup = true;
    assert!(certify_get_body(&wrong, certificate.nonzero, tcx.types.u16).is_err());
    wrong = body.clone();
    wrong.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK]
        .statements
        .clear();
    assert!(certify_get_body(&wrong, certificate.nonzero, tcx.types.u16).is_err());
    assert!(certify_get_body(&body, tcx.types.u16, tcx.types.u16).is_err());
    assert!(certify_get_body(&body, certificate.nonzero, tcx.types.u32).is_err());
    let schema = schema(tcx, certificate.clone()).unwrap();
    let context = Context::default();
    let bits = certificate.bits;
    let array = context
        .symbol(
            0,
            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(16))),
        )
        .unwrap();
    let index = context.bit_vector(0, bits).unwrap();
    let mut cursor = 0;
    let value = schema
        .observe(&context, std::slice::from_ref(&array), &index, &mut cursor)
        .unwrap();
    assert_eq!(cursor, 1);
    let Value::Enum {
        discriminant,
        variants,
        ..
    } = value
    else {
        panic!("sum")
    };
    assert_eq!(variants.len(), 2);
    let copied = discriminant.clone();
    assert_eq!(copied.integer().unwrap(), discriminant.integer().unwrap());
    let wrong = context
        .symbol(
            1,
            Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(32))),
        )
        .unwrap();
    let mut cursor = 0;
    assert!(
        schema
            .observe(&context, &[wrong], &index, &mut cursor)
            .is_err()
    );
    assert_eq!(cursor, 0);
}

#[cfg(test)]
pub(super) fn test_engine<'tcx>(tcx: TyCtxt<'tcx>) -> Engine<'tcx> {
    let config = miren::ContractConfig::default();
    let limits = miren::AnalysisLimits::default();
    let all_failures = false;
    let induction = false;
    let startup = false;
    let isolated_startup = false;
    let async_entry = false;
    Engine {
        tcx,
        terms: Context::default(),
        next_symbol: std::cell::Cell::new(0),
        float_encodings: BTreeMap::new(),
        float_pairs: super::float_pairs::Registry::default(),
        abstraction_symbols: std::cell::RefCell::new(BTreeMap::new()),
        static_views: std::cell::RefCell::new(Vec::new()),
        static_origins: Default::default(),
        static_epoch: None,
        static_roots: None,
        function_pointers: std::cell::RefCell::new(Vec::new()),
        static_addresses: std::collections::HashMap::new(),
        tracked_addresses: Vec::new(),
        maybe_uninit_types: Vec::new(),
        scalar_slice_types: Vec::new(),
        composite_slice_types: Vec::new(),
        steps: 0,
        call_chain: Vec::new(),
        failed_call_chain: None,
        trait_objects: std::cell::RefCell::new(Vec::new()),
        trait_object_choice_work: std::cell::Cell::new(0),
        trait_object_choices_issued: std::cell::Cell::new(false),
        input_depth: 0,
        input_values: 0,
        input_reservations: Vec::new(),
        owned_projection_certificates: Vec::new(),
        input_shapes: std::collections::HashMap::new(),
        zero_sized_inputs: std::collections::HashMap::new(),
        zero_sized_input_nodes: 0,
        prefer_lazy_inputs: false,
        building_mutable_input: false,
        unknown_causes: std::cell::RefCell::new(BTreeMap::new()),
        started: std::time::Instant::now(),
        config: config.clone(),
        all_failures,
        induction,
        startup,
        isolated_startup,
        limits,
        resolved_contracts: BTreeMap::new(),
        solver: std::cell::RefCell::new(Solver::with_limits(limits)),
        mutable_u16_frames: Default::default(),
        mutable_integer_types: Vec::new(),
        mutable_u16_staging: Default::default(),
        activation: Default::default(),
        coroutine_places: Default::default(),
        owned_box_types: Vec::new(),
        next_owned_region: 0,
        owned_box_constructors: Vec::new(),
        bodies: std::cell::RefCell::new(std::collections::HashMap::new()),
        call_signatures: std::cell::RefCell::new(std::collections::HashMap::new()),
        proof: Proof {
            status: ProofStatus::Proved,
            async_entry,
            assumptions: Vec::new(),
            entry_assumptions: Vec::new(),
            inputs: BTreeMap::new(),
            models: Vec::new(),
            invariants: Vec::new(),
            analyzed_bodies: Vec::new(),
            body_entries: Vec::new(),
            body_entries_truncated: false,
            obligations: Vec::new(),
            trusted_calls: Vec::new(),
            matched_contracts: Vec::new(),
            stopped_after_counterexample: false,
            replay_inputs: None,
        },
    }
}

fn getter_work(body: &Body<'_>) -> usize {
    body.basic_blocks
        .iter()
        .fold(body.local_decls.len(), |work, block| {
            work.saturating_add(1)
                .saturating_add(block.statements.len())
                .saturating_add(1)
        })
}

#[cfg(test)]
fn contains_nonzero16<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
    depth: usize,
    nodes: &mut usize,
) -> Result<bool, String> {
    if depth >= 16 || *nodes >= 512 {
        return Err("NonZero operand type probe exceeds its 512-node/depth16 budget".into());
    }
    *nodes += 1;
    match original.kind() {
        ty::Ref(_, element, _) | ty::Slice(element) | ty::Array(element, _) => {
            contains_nonzero16(tcx, *element, depth + 1, nodes)
        }
        ty::Tuple(fields) => {
            for field in fields.iter() {
                if contains_nonzero16(tcx, field, depth + 1, nodes)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        ty::Adt(def, args) => {
            if tcx.is_diagnostic_item(rustc_span::Symbol::intern("NonZero"), def.did()) {
                return Ok(args.len() == 1 && args.type_at(0) == tcx.types.u16);
            }
            for variant in def.variants() {
                if *nodes >= 512 {
                    return Err("NonZero operand type probe exceeds its 512-node budget".into());
                }
                *nodes += 1;
                for field in &variant.fields {
                    if contains_nonzero16(
                        tcx,
                        field.ty(tcx, args).skip_norm_wip(),
                        depth + 1,
                        nodes,
                    )? {
                        return Ok(true);
                    }
                }
            }
            Ok(false)
        }
        _ => Ok(false),
    }
}

// Resolve the actual operand path without exploring unrelated aggregate descendants. A
// recorded FieldTy never determines the next compiler type, including on an external wrapper.
fn original_operand_terminal<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
) -> Result<Ty<'tcx>, String> {
    if place.projection.len() > 16 {
        return Err("NonZero operand original path exceeds depth16".into());
    }
    let mut original = body.local_decls[place.local].ty;
    let mut variant = None;
    for part in place.projection {
        original = match part {
            ProjectionElem::Deref => {
                variant = None;
                original
                    .builtin_deref(true)
                    .ok_or("NonZero operand dereference lacks original compiler pointee")?
            }
            ProjectionElem::Downcast(_, selected) => {
                let valid = match original.kind() {
                    ty::Adt(def, _) => def.is_enum() && selected.as_usize() < def.variants().len(),
                    ty::Coroutine(def, args) if selected.as_usize() < 512 => args
                        .as_coroutine()
                        .state_tys(*def, tcx)
                        .nth(selected.as_usize())
                        .is_some(),
                    _ => false,
                };
                if !valid || variant.is_some() {
                    return Err("NonZero operand downcast original metadata mismatch".into());
                }
                variant = Some(selected);
                original
            }
            ProjectionElem::Field(index, _) => {
                let field = match original.kind() {
                    ty::Tuple(fields) => fields.get(index.as_usize()).copied(),
                    ty::Closure(_, args) if variant.is_none() => {
                        args.as_closure().upvar_tys().get(index.as_usize()).copied()
                    }
                    ty::CoroutineClosure(_, args) if variant.is_none() => args
                        .as_coroutine_closure()
                        .upvar_tys()
                        .get(index.as_usize())
                        .copied(),
                    ty::Coroutine(def, args) => match variant {
                        Some(selected) if selected.as_usize() < 512 && index.as_usize() < 512 => {
                            args.as_coroutine()
                                .state_tys(*def, tcx)
                                .nth(selected.as_usize())
                                .and_then(|mut fields| fields.nth(index.as_usize()))
                        }
                        None => args
                            .as_coroutine()
                            .upvar_tys()
                            .get(index.as_usize())
                            .copied(),
                        _ => None,
                    },
                    ty::Adt(def, args) if def.is_enum() => variant
                        .and_then(|variant| def.variant(variant).fields.get(index))
                        .map(|field| field.ty(tcx, args).skip_norm_wip()),
                    ty::Adt(def, args) if def.is_struct() => def
                        .non_enum_variant()
                        .fields
                        .get(index)
                        .map(|field| field.ty(tcx, args).skip_norm_wip()),
                    _ => None,
                }
                .ok_or("NonZero operand field lacks original compiler parent")?;
                variant = None;
                field
            }
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => {
                let (ty::Array(element, _) | ty::Slice(element)) = original.kind() else {
                    return Err("NonZero operand index lacks original array or slice".into());
                };
                variant = None;
                *element
            }
            ProjectionElem::Subslice { from, to, from_end } => match original.kind() {
                ty::Slice(_) => original,
                ty::Array(element, count) => {
                    let count = count
                        .try_to_target_usize(tcx)
                        .ok_or("NonZero operand subslice lacks original fixed extent")?;
                    let end = if from_end {
                        count.checked_sub(to)
                    } else {
                        (to <= count).then_some(to)
                    }
                    .ok_or("NonZero operand subslice exceeds original fixed extent")?;
                    let count = end
                        .checked_sub(from)
                        .ok_or("NonZero operand subslice original bounds are reversed")?;
                    Ty::new_array(tcx, *element, count)
                }
                _ => return Err("NonZero operand subslice lacks original array or slice".into()),
            },
            _ => return Err("NonZero operand original projection transport is unsupported".into()),
        };
    }
    Ok(original)
}

fn nonzero16_terminal<'tcx>(tcx: TyCtxt<'tcx>, mut original: Ty<'tcx>) -> bool {
    // Reference receivers do not mint a payload; their actual FieldTy still needs authentication.
    for _ in 0..16 {
        match original.kind() {
            ty::Ref(_, inner, _) => original = *inner,
            ty::Adt(def, args) => {
                return tcx.is_diagnostic_item(rustc_span::Symbol::intern("NonZero"), def.did())
                    && args.len() == 1
                    && args.type_at(0) == tcx.types.u16;
            }
            _ => return false,
        }
    }
    false
}

fn authenticate_operand_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
) -> Result<(), String> {
    if place.projection.len() > 16 {
        return Err("NonZero operand original path exceeds depth16".into());
    }
    let mut original = body.local_decls[place.local].ty;
    let mut variant = None;
    for part in place.projection {
        match part {
            ProjectionElem::Deref => {
                let ty::Ref(_, pointee, mutability) = original.kind() else {
                    return Err(
                        "NonZero operand requires an original ordinary shared reference".into(),
                    );
                };
                if mutability.is_mut() {
                    return Err("NonZero operand mutable reference transport is unsupported".into());
                }
                original = *pointee;
                variant = None;
            }
            ProjectionElem::Downcast(_, selected) => {
                let ty::Adt(def, _) = original.kind() else {
                    return Err("NonZero operand downcast lacks original enum".into());
                };
                if !def.is_enum()
                    || selected.as_usize() >= def.variants().len()
                    || variant.is_some()
                {
                    return Err("NonZero operand downcast original metadata mismatch".into());
                }
                variant = Some(selected);
            }
            ProjectionElem::Field(index, recorded) => {
                let selected = match original.kind() {
                    ty::Tuple(fields) => fields.get(index.as_usize()).copied(),
                    ty::Adt(def, args) if def.is_enum() => variant
                        .and_then(|variant| def.variant(variant).fields.get(index))
                        .map(|field| field.ty(tcx, args).skip_norm_wip()),
                    ty::Adt(def, args) if def.is_struct() => def
                        .non_enum_variant()
                        .fields
                        .get(index)
                        .map(|field| field.ty(tcx, args).skip_norm_wip()),
                    _ => None,
                }
                .ok_or("NonZero operand field lacks original compiler parent")?;
                if selected != recorded {
                    return Err(
                        "NonZero operand recorded FieldTy differs from original compiler type"
                            .into(),
                    );
                }
                original = selected;
                variant = None;
            }
            ProjectionElem::Index(index) => {
                if body.local_decls[index].ty != tcx.types.usize || variant.is_some() {
                    return Err("NonZero operand index original metadata mismatch".into());
                }
                let (ty::Array(element, _) | ty::Slice(element)) = original.kind() else {
                    return Err("NonZero operand index lacks original array or slice".into());
                };
                original = *element;
            }
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                let (ty::Array(element, _) | ty::Slice(element)) = original.kind() else {
                    return Err("NonZero operand fixed index lacks original array or slice".into());
                };
                if from_end || offset >= min_length || variant.is_some() {
                    return Err("NonZero operand fixed index original metadata mismatch".into());
                }
                if let ty::Array(_, count) = original.kind()
                    && count
                        .try_to_target_usize(tcx)
                        .is_none_or(|count| min_length > count)
                {
                    return Err("NonZero operand fixed index exceeds original array".into());
                }
                original = *element;
            }
            _ => return Err("NonZero operand original projection transport is unsupported".into()),
        }
    }
    Ok(())
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn nonzero_niche_operand_path(
        &self,
        body: &Body<'tcx>,
        place: Place<'tcx>,
    ) -> Result<(), String> {
        if !ENABLE_RUNTIME {
            return Ok(());
        }
        if place.projection.is_empty() {
            return Ok(());
        }
        if place.projection.len() > 16 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "NonZero operand original path exceeds depth16".into(),
            ));
        }
        // Failure to resolve an executable projection is never proof that it is unrelated.
        // In particular, a forged recorded u16 must not hide an authentic NonZero leaf.
        let original_place = self
            .coroutine_original_operand_place(body, place)?
            .unwrap_or(place);
        let original = original_operand_terminal(self.tcx, body, original_place)?;
        let recorded = place.ty(&body.local_decls, self.tcx).ty;
        if !nonzero16_terminal(self.tcx, original) && !nonzero16_terminal(self.tcx, recorded) {
            return Ok(());
        }
        authenticate_operand_path(self.tcx, body, original_place)
    }
}

#[cfg(test)]
fn check_copy_path<'tcx>(tcx: TyCtxt<'tcx>, certificate: &Certificate<'tcx>, body: &Body<'tcx>) {
    let mut original = body.clone();
    original.local_decls[Local::from_usize(1)].ty = certificate.original;
    let valid = Place {
        local: Local::from_usize(1),
        projection: tcx.mk_place_elems(&[
            ProjectionElem::Downcast(
                None,
                rustc_abi::VariantIdx::from_usize(certificate.payload_variant),
            ),
            ProjectionElem::Field(FieldIdx::from_usize(0), certificate.nonzero),
        ]),
    };
    let copy = Operand::Copy(valid);
    let Operand::Copy(place) = copy else {
        unreachable!()
    };
    authenticate_operand_path(tcx, &original, place).unwrap();
    let engine = test_engine(tcx);
    engine.nonzero_niche_operand_path(&original, place).unwrap();
    assert_eq!(
        original_operand_terminal(tcx, &original, place).unwrap(),
        certificate.nonzero
    );
    assert_eq!(place.ty(&original.local_decls, tcx).ty, certificate.nonzero);
    let forged = Place {
        projection: tcx.mk_place_elems(&[
            ProjectionElem::Downcast(
                None,
                rustc_abi::VariantIdx::from_usize(certificate.payload_variant),
            ),
            ProjectionElem::Field(FieldIdx::from_usize(0), tcx.types.u16),
        ]),
        ..valid
    };
    assert_eq!(forged.ty(&original.local_decls, tcx).ty, tcx.types.u16);
    assert_eq!(
        original_operand_terminal(tcx, &original, forged).unwrap(),
        certificate.nonzero
    );
    assert!(authenticate_operand_path(tcx, &original, forged).is_err());
    assert!(
        test_engine(tcx)
            .nonzero_niche_operand_path(&original, forged)
            .is_err()
    );
    original.local_decls[Local::from_usize(1)].ty = tcx.types.u16;
    assert!(authenticate_operand_path(tcx, &original, place).is_err());
    original.local_decls[Local::from_usize(1)].ty = Ty::new_array(tcx, certificate.original, 0);
    let empty = Place {
        local: Local::from_usize(1),
        projection: tcx.mk_place_elems(&[
            ProjectionElem::ConstantIndex {
                offset: 0,
                min_length: 1,
                from_end: false,
            },
            ProjectionElem::Downcast(
                None,
                rustc_abi::VariantIdx::from_usize(certificate.payload_variant),
            ),
            ProjectionElem::Field(FieldIdx::from_usize(0), certificate.nonzero),
        ]),
    };
    assert!(authenticate_operand_path(tcx, &original, empty).is_err());
    assert!(contains_nonzero16(tcx, certificate.original, 0, &mut 0).unwrap());
    assert!(contains_nonzero16(tcx, certificate.original, 0, &mut 512).is_err());
    let whole_budget = Ty::new_tup(tcx, &[tcx.types.u16; 511]);
    let mut cumulative = 0;
    assert!(!contains_nonzero16(tcx, whole_budget, 0, &mut cumulative).unwrap());
    assert_eq!(cumulative, 512);
    assert!(contains_nonzero16(tcx, certificate.nonzero, 0, &mut cumulative).is_err());

    // Whole aggregates do not publish a standalone leaf and require no descendant scan.
    original.local_decls[Local::from_usize(1)].ty = whole_budget;
    let whole = Place::from(Local::from_usize(1));
    assert_eq!(
        original_operand_terminal(tcx, &original, whole).unwrap(),
        whole_budget
    );
    assert!(!nonzero16_terminal(tcx, whole_budget));

    // Exhausted actual extraction paths must not be skipped because the recorded leaf is u16.
    let mut root = certificate.nonzero;
    let mut fields = Vec::new();
    for _ in 0..17 {
        fields.push(ProjectionElem::Field(FieldIdx::from_usize(0), root));
        root = Ty::new_tup(tcx, &[root]);
    }
    fields.reverse();
    original.local_decls[Local::from_usize(1)].ty = root;
    let deep = Place {
        local: Local::from_usize(1),
        projection: tcx.mk_place_elems(&fields),
    };
    assert!(original_operand_terminal(tcx, &original, deep).is_err());
    *fields.last_mut().unwrap() = ProjectionElem::Field(FieldIdx::from_usize(0), tcx.types.u16);
    let hidden = Place {
        projection: tcx.mk_place_elems(&fields),
        ..deep
    };
    assert_eq!(hidden.ty(&original.local_decls, tcx).ty, tcx.types.u16);
    assert!(original_operand_terminal(tcx, &original, hidden).is_err());
    let engine = test_engine(tcx);
    let reason = engine
        .nonzero_niche_operand_path(&original, hidden)
        .unwrap_err();
    assert_eq!(
        engine.unknown_causes.borrow().get(&reason),
        Some(&UnknownCategory::ResourceLimit)
    );
    original.local_decls[Local::from_usize(1)].ty = certificate.nonzero;
    let unresolved = Place {
        local: Local::from_usize(1),
        projection: tcx.mk_place_elems(&[ProjectionElem::OpaqueCast(tcx.types.u16)]),
    };
    assert!(original_operand_terminal(tcx, &original, unresolved).is_err());
    assert!(
        test_engine(tcx)
            .nonzero_niche_operand_path(&original, unresolved)
            .is_err()
    );
}

#[cfg(test)]
fn check_external_copy_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    certificate: &Certificate<'tcx>,
    body: &Body<'tcx>,
    external: Ty<'tcx>,
) {
    let ty::Adt(def, _) = external.kind() else {
        unreachable!()
    };
    assert!(!def.did().is_local());
    assert!(contains_nonzero16(tcx, external, 0, &mut 0).unwrap());
    let mut original = body.clone();
    original.local_decls[Local::from_usize(1)].ty = external;
    let valid = Place {
        local: Local::from_usize(1),
        projection: tcx.mk_place_elems(&[ProjectionElem::Field(
            FieldIdx::from_usize(0),
            certificate.nonzero,
        )]),
    };
    authenticate_operand_path(tcx, &original, valid).unwrap();
    let forged = Place {
        projection: tcx.mk_place_elems(&[ProjectionElem::Field(
            FieldIdx::from_usize(0),
            tcx.types.u16,
        )]),
        ..valid
    };
    assert_eq!(forged.ty(&original.local_decls, tcx).ty, tcx.types.u16);
    assert_eq!(
        original_operand_terminal(tcx, &original, forged).unwrap(),
        certificate.nonzero
    );
    assert!(authenticate_operand_path(tcx, &original, forged).is_err());
    assert!(
        test_engine(tcx)
            .nonzero_niche_operand_path(&original, forged)
            .is_err()
    );
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn exact_niche_membership(
        &self,
        original: Ty<'tcx>,
        instance: ty::Instance<'tcx>,
        slice: &Value,
        needle: &Value,
        state: &State,
    ) -> Result<Term, String> {
        self.checked_niche_membership(original, instance, slice, needle, state)
    }
}

impl Schema {
    pub(super) fn membership_match_work(&self, expected: &Self) -> Result<usize, String> {
        // Sixteen length/bound/add visits48, two facts services64,
        // and the remaining tag/width/header comparisons16.
        let mut work = 128usize;
        for name in [
            self.name.as_str(),
            self.variant_names[0].as_str(),
            self.variant_names[1].as_str(),
            self.payload_field.as_str(),
            self.outer_name.as_str(),
            self.inner_name.as_str(),
            self.outer_field.as_str(),
            self.inner_field.as_str(),
            expected.name.as_str(),
            expected.variant_names[0].as_str(),
            expected.variant_names[1].as_str(),
            expected.payload_field.as_str(),
            expected.outer_name.as_str(),
            expected.inner_name.as_str(),
            expected.outer_field.as_str(),
            expected.inner_field.as_str(),
        ] {
            if name.len() > 128 {
                return Err("niche schema name exceeds128 bytes".into());
            }
            work = work
                .checked_add(name.len())
                .ok_or("niche schema match work overflow")?;
        }
        Ok(work)
    }

    pub(super) fn membership_matches(&self, expected: &Self) -> bool {
        facts_match(&self.facts)
            && facts_match(&expected.facts)
            && self.name == expected.name
            && self.is_option
            && expected.is_option
            && self.variant_names == expected.variant_names
            && self.payload_field == expected.payload_field
            && self.outer_name == expected.outer_name
            && self.inner_name == expected.inner_name
            && self.outer_field == expected.outer_field
            && self.inner_field == expected.inner_field
            && self.payload_variant == expected.payload_variant
            && self.tags == expected.tags
            && self.bits == expected.bits
            && self.signed == expected.signed
    }
}
