//! Complete selected u16 grammar certifies a guarded interval relation only.
//! The caller must still prove the guards and authenticate live root/tip/issued storage.
use super::super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Family {
    Wrapper,
    Range,
}

const REFERENCES: &[(&str, Family, &str)] = &[
    (
        "DefId(core::slice::index::{impl#1}::index_mut)",
        Family::Wrapper,
        include_str!("mutable_interval_reference/wrapper-host.mir"),
    ),
    (
        "DefId(core::slice::index::{impl#1}::index_mut)",
        Family::Wrapper,
        include_str!("mutable_interval_reference/wrapper-arm.mir"),
    ),
    (
        "DefId(core::slice::index::{impl#4}::index_mut)",
        Family::Range,
        include_str!("mutable_interval_reference/range-host.mir"),
    ),
    (
        "DefId(core::slice::index::{impl#4}::index_mut)",
        Family::Range,
        include_str!("mutable_interval_reference/range-arm.mir"),
    ),
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Element<'tcx> {
    pub(super) original: Ty<'tcx>,
    pub(super) bytes: u64,
    pub(super) alignment: u64,
    pub(super) bits: u32,
    pub(super) signed: bool,
}

/// Compiler layout facts do not issue a mutable view or authenticate storage.
pub(super) fn integer_element<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
) -> Option<Element<'tcx>> {
    let (bits, signed) = if original == tcx.types.i32 {
        (32, true)
    } else if original == tcx.types.usize {
        (u32::from(tcx.sess.target.pointer_width), false)
    } else {
        return None;
    };
    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(original))
        .ok()?;
    let bytes = u64::from(bits / 8);
    if !matches!(bits, 32 | 64)
        || layout.size.bytes() != bytes
        || layout.align.abi.bytes() != bytes
        || !matches!(layout.variants, rustc_abi::Variants::Single { .. })
    {
        return None;
    }
    Some(Element {
        original,
        bytes,
        alignment: bytes,
        bits,
        signed,
    })
}

fn integer_body_matches(key: &str, family: Family, encoded: &str, element: Element<'_>) -> bool {
    let wrappers = match element.original.kind() {
        ty::Int(ty::IntTy::I32) => [
            include_str!("mutable_interval_reference/wrapper-i32-host.mir"),
            include_str!("mutable_interval_reference/wrapper-i32-arm.mir"),
        ],
        ty::Uint(ty::UintTy::Usize) => [
            include_str!("mutable_interval_reference/wrapper-usize-host.mir"),
            include_str!("mutable_interval_reference/wrapper-usize-arm.mir"),
        ],
        _ => return false,
    };
    match family {
        Family::Wrapper => {
            key == "DefId(core::slice::index::{impl#1}::index_mut)"
                && wrappers
                    .iter()
                    .any(|body| body.strip_suffix('\n') == Some(encoded))
        }
        Family::Range => matches_body(key, family, encoded),
    }
}

fn integer_instantiated_range_matches(encoded: &str, element: Element<'_>) -> bool {
    let references = match element.original.kind() {
        ty::Int(ty::IntTy::I32) => [
            include_str!("mutable_interval_reference/range-i32-host.mir"),
            include_str!("mutable_interval_reference/range-i32-arm.mir"),
        ],
        ty::Uint(ty::UintTy::Usize) => [
            include_str!("mutable_interval_reference/range-usize-host.mir"),
            include_str!("mutable_interval_reference/range-usize-arm.mir"),
        ],
        _ => return false,
    };
    references
        .iter()
        .any(|body| body.strip_suffix('\n') == Some(encoded))
}

fn matches_body(key: &str, family: Family, encoded: &str) -> bool {
    REFERENCES.iter().any(|(expected, actual, body)| {
        *expected == key && *actual == family && body.strip_suffix('\n') == Some(encoded)
    })
}

fn signature_for<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    family: Family,
    element: Ty<'tcx>,
) -> bool {
    let Ok(signature) = tcx.try_normalize_erasing_regions(
        ty::TypingEnv::fully_monomorphized(),
        tcx.fn_sig(instance.def_id())
            .instantiate(tcx, instance.args),
    ) else {
        return false;
    };
    let signature = tcx.erase_and_anonymize_regions(signature.skip_binder());
    if signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.safety() != rustc_hir::Safety::Safe
        || signature.c_variadic()
    {
        return false;
    }
    let slice = Ty::new_slice(tcx, element);
    let reference = |original: Ty<'tcx>| {
        matches!(original.kind(),
        ty::Ref(_, inner, rustc_hir::Mutability::Mut) if *inner == slice)
    };
    let range = |original: Ty<'tcx>| {
        matches!(original.kind(), ty::Adt(def, args)
        if tcx.lang_items().get(LangItem::Range) == Some(def.did())
            && args.type_at(0) == tcx.types.usize)
    };
    if !reference(signature.output()) {
        return false;
    }
    match (family, signature.inputs()) {
        (Family::Wrapper, [receiver, index]) => reference(*receiver) && range(*index),
        (Family::Range, [index, receiver]) => range(*index) && reference(*receiver),
        _ => false,
    }
}

fn signature<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>, family: Family) -> bool {
    signature_for(tcx, instance, family, tcx.types.u16)
}

pub(super) fn integer_wrapper_element<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Option<Element<'tcx>> {
    if !matches!(instance.def, ty::InstanceKind::Item(_))
        || tcx.def_kind(instance.def_id()) != DefKind::AssocFn
    {
        return None;
    }
    [tcx.types.i32, tcx.types.usize]
        .into_iter()
        .find_map(|original| {
            let element = integer_element(tcx, original)?;
            signature_for(tcx, instance, Family::Wrapper, original).then_some(element)
        })
}

pub(super) fn available_integer_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<&'tcx Body<'tcx>, pure_comparison_templates::TemplateError> {
    if !tcx.is_mir_available(instance.def_id()) {
        return Err(pure_comparison_templates::TemplateError {
            category: UnknownCategory::MissingCompilerEvidence,
            reason: "interval integer selected compiler body is unavailable".into(),
        });
    }
    Ok(tcx.instance_mir(instance.def))
}

pub(super) fn certify_integer_guarded_family<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: ty::Instance<'tcx>,
    element: Element<'tcx>,
) -> Result<(), pure_comparison_templates::TemplateError> {
    if integer_element(tcx, element.original) != Some(element) {
        return Err("interval original integer layout/codec differs".into());
    }
    certify_guarded_family(tcx, root, Schema::Integer(element))
}

pub(super) fn u16_wrapper_signature<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>) -> bool {
    signature(tcx, instance, Family::Wrapper)
}

/// Pins the full selected u16 transport relation, not library execution.
/// Under start<=end<=current N the matched Range blocks are bb0->bb5->bb1:
/// bb0's end<start is false; bb5's end<=metadata is true; SubUnchecked cannot underflow.
/// RawPtr/Offset/fat reference in bb1 returns the SAME receiver region at (start,end-start).
/// Failure blocks bb4/bb2->bb3 and their missing panic/unwind are outside that guarded relation.
/// No caller guard, provenance, source mask, phase or write right is established here.
pub(super) fn certify_u16_guarded_family<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: ty::Instance<'tcx>,
) -> Result<(), String> {
    certify_guarded_family(tcx, root, Schema::LegacyU16).map_err(|error| error.reason)
}

#[derive(Clone, Copy)]
enum Schema<'tcx> {
    LegacyU16,
    Integer(Element<'tcx>),
    F32Pair,
}

fn certify_guarded_family<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: ty::Instance<'tcx>,
    schema: Schema<'tcx>,
) -> Result<(), pure_comparison_templates::TemplateError> {
    let (original, element, local_pair) = match schema {
        Schema::LegacyU16 => (tcx.types.u16, None, false),
        Schema::Integer(element) => (element.original, Some(element), false),
        Schema::F32Pair => (Ty::new_array(tcx, tcx.types.f32, 2), None, true),
    };
    let core = tcx
        .lang_items()
        .sized_trait()
        .ok_or("interval core identity missing")?
        .krate;
    let mut pending = vec![(root, Family::Wrapper)];
    let mut seen = std::collections::HashSet::new();
    let mut work = 0_usize;
    while let Some((instance, family)) = pending.pop() {
        if !seen.insert((instance, family)) {
            continue;
        }
        if seen.len() > 2 {
            return Err("interval selected family graph differs".into());
        }
        if element.is_some() {
            if instance.def_id().krate != core
                || !matches!(instance.def, ty::InstanceKind::Item(_))
                || tcx.def_kind(instance.def_id()) != DefKind::AssocFn
            {
                return Err("interval integer selected compiler identity differs".into());
            }
        } else {
            if instance.def_id().krate != core
                || !matches!(instance.def, ty::InstanceKind::Item(_))
                || tcx.def_kind(instance.def_id()) != DefKind::AssocFn
                || !tcx.is_mir_available(instance.def_id())
            {
                return Err("interval selected body unavailable or not actual core Item".into());
            }
        }
        if !signature_for(tcx, instance, family, original) {
            return Err("interval original selected signature differs".into());
        }
        let generic = if element.is_some() {
            available_integer_body(tcx, instance)?
        } else {
            tcx.instance_mir(instance.def)
        };
        if generic.coroutine.is_some()
            || generic.tainted_by_errors.is_some()
            || generic.spread_arg.is_some()
            || generic.basic_blocks.len() > 128
        {
            return Err("interval selected body metadata differs".into());
        }
        work = work
            .saturating_add(generic.local_decls.len())
            .saturating_add(generic.basic_blocks.len());
        if work > 512 {
            return Err(pure_comparison_templates::TemplateError {
                category: UnknownCategory::ResourceLimit,
                reason: "interval selected graph exceeds512 work".into(),
            });
        }
        for data in generic.basic_blocks.iter() {
            work = work.saturating_add(data.statements.len());
            if work > 512 {
                return Err(pure_comparison_templates::TemplateError {
                    category: UnknownCategory::ResourceLimit,
                    reason: "interval selected graph exceeds512 work".into(),
                });
            }
        }
        let mono = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(tcx, generic.clone()),
            )
            .map_err(|_| "interval exact original substitution unavailable")?;
        let template_body = match family {
            Family::Wrapper => &mono,
            Family::Range => generic,
        };
        let encoded =
            pure_comparison_templates::encode_byte_copy_template(tcx, template_body, core)?;
        let key = pure_comparison_templates::definition_key(instance.def_id());
        let matched = if local_pair && family == Family::Wrapper {
            key == "DefId(core::slice::index::{impl#1}::index_mut)"
                && [
                    include_str!("mutable_interval_reference/wrapper-f32-pair.mir"),
                    include_str!("mutable_interval_reference/wrapper-f32-pair-arm.mir"),
                ]
                .iter()
                .any(|body| body.strip_suffix('\n') == Some(encoded.as_str()))
        } else {
            element.map_or_else(
                || matches_body(&key, family, &encoded),
                |element| integer_body_matches(&key, family, &encoded, element),
            )
        };
        if !matched || !signature_for(tcx, instance, family, original) {
            return Err("interval complete selected body or signature differs".into());
        }
        if family == Family::Range
            && let Some(element) = element
        {
            let instantiated =
                pure_comparison_templates::encode_byte_copy_template(tcx, &mono, core)?;
            if !integer_instantiated_range_matches(&instantiated, element) {
                return Err("interval original integer substitution/body differs".into());
            }
            #[cfg(test)]
            reject_integer_instantiated_mutations(tcx, core, &mono, element)?;
        }
        if family == Family::Wrapper {
            let TerminatorKind::Call { func, .. } = &mono.basic_blocks
                [rustc_middle::mir::BasicBlock::from_usize(0)]
            .terminator()
            .kind
            else {
                return Err("interval wrapper delegate differs".into());
            };
            if element.is_some() && !matches!(func, Operand::Constant(_)) {
                return Err("interval integer delegate is not an exact constant FnDef".into());
            }
            let ty::FnDef(id, args) = func.ty(&mono.local_decls, tcx).kind() else {
                return Err("interval wrapper delegate is indirect".into());
            };
            let selected = ty::Instance::try_resolve(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                *id,
                args.skip_binder(),
            )
            .map_err(|_| "interval delegate resolution failed")?
            .ok_or("interval delegate is missing")?;
            pending.push((selected, Family::Range));
        }
        #[cfg(test)]
        if element.is_some() {
            reject_integer_metadata(tcx, core, &key, family, template_body, element)?;
        }
        #[cfg(test)]
        for (block, data) in template_body.basic_blocks.iter_enumerated() {
            for (position, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(assignment) = &statement.kind else {
                    continue;
                };
                let replacement = match &assignment.1 {
                    Rvalue::BinaryOp(BinOp::Lt, operands) => {
                        Some(Rvalue::BinaryOp(BinOp::Gt, operands.clone()))
                    }
                    Rvalue::BinaryOp(BinOp::Offset, operands) => Some(Rvalue::BinaryOp(
                        BinOp::Offset,
                        Box::new((operands.1.clone(), operands.0.clone())),
                    )),
                    Rvalue::Aggregate(kind, operands)
                        if matches!(kind.as_ref(), AggregateKind::RawPtr(..)) =>
                    {
                        let mut wrong = operands.clone();
                        wrong.swap(
                            rustc_abi::FieldIdx::from_usize(0),
                            rustc_abi::FieldIdx::from_usize(1),
                        );
                        Some(Rvalue::Aggregate(kind.clone(), wrong))
                    }
                    _ => None,
                };
                let Some(replacement) = replacement else {
                    continue;
                };
                let mut changed = template_body.clone();
                let StatementKind::Assign(assignment) =
                    &mut changed.basic_blocks_mut()[block].statements[position].kind
                else {
                    unreachable!()
                };
                assignment.1 = replacement;
                reject_mutation(tcx, core, &key, family, &changed, element)?;
            }
            if let TerminatorKind::Call { .. } = &data.terminator().kind {
                let mut changed = template_body.clone();
                let TerminatorKind::Call { args, .. } =
                    &mut changed.basic_blocks_mut()[block].terminator_mut().kind
                else {
                    unreachable!()
                };
                args.swap(0, 1);
                reject_mutation(tcx, core, &key, family, &changed, element)?;
            }
            if matches!(data.terminator().kind, TerminatorKind::Return) {
                let mut changed = template_body.clone();
                changed.basic_blocks_mut()[block].terminator_mut().kind =
                    TerminatorKind::Unreachable;
                reject_mutation(tcx, core, &key, family, &changed, element)?;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
fn reject_mutation<'tcx>(
    tcx: TyCtxt<'tcx>,
    core: rustc_span::def_id::CrateNum,
    key: &str,
    family: Family,
    changed: &Body<'tcx>,
    element: Option<Element<'tcx>>,
) -> Result<(), String> {
    let encoded = pure_comparison_templates::encode_byte_copy_template(tcx, changed, core)
        .map_err(|error| error.reason)?;
    if element.map_or_else(
        || matches_body(key, family, &encoded),
        |element| integer_body_matches(key, family, &encoded, element),
    ) {
        Err("interval changed endpoint/receiver/offset/fat-pointer/return was admitted".into())
    } else {
        Ok(())
    }
}

#[cfg(test)]
fn reject_integer_metadata<'tcx>(
    tcx: TyCtxt<'tcx>,
    core: rustc_span::def_id::CrateNum,
    key: &str,
    family: Family,
    body: &Body<'tcx>,
    element: Option<Element<'tcx>>,
) -> Result<(), String> {
    let mut changed = body.clone();
    changed.spread_arg = Some(rustc_middle::mir::Local::from_usize(1));
    reject_mutation(tcx, core, key, family, &changed, element)?;
    struct WrongField<'tcx> {
        tcx: TyCtxt<'tcx>,
        changed: bool,
    }
    impl<'tcx> rustc_middle::mir::visit::MutVisitor<'tcx> for WrongField<'tcx> {
        fn tcx(&self) -> TyCtxt<'tcx> {
            self.tcx
        }

        fn visit_place(
            &mut self,
            place: &mut Place<'tcx>,
            _: rustc_middle::mir::visit::PlaceContext,
            _: rustc_middle::mir::Location,
        ) {
            let mut projection = place.projection.to_vec();
            for field in &mut projection {
                if let ProjectionElem::Field(index, _) = field {
                    *field = ProjectionElem::Field(*index, self.tcx.types.u32);
                    self.changed = true;
                }
            }
            place.projection = self.tcx.mk_place_elems(&projection);
        }
    }
    let mut changed = body.clone();
    let mut visitor = WrongField {
        tcx,
        changed: false,
    };
    rustc_middle::mir::visit::MutVisitor::visit_body(&mut visitor, &mut changed);
    if visitor.changed {
        reject_mutation(tcx, core, key, family, &changed, element)?;
    }
    Ok(())
}

#[cfg(test)]
fn reject_integer_instantiated_mutations<'tcx>(
    tcx: TyCtxt<'tcx>,
    core: rustc_span::def_id::CrateNum,
    body: &Body<'tcx>,
    element: Element<'tcx>,
) -> Result<(), String> {
    let reject = |changed: &Body<'tcx>| -> Result<(), String> {
        let encoded = pure_comparison_templates::encode_byte_copy_template(tcx, changed, core)
            .map_err(|reason| reason.reason)?;
        if integer_instantiated_range_matches(&encoded, element) {
            Err("interval changed original integer substitution was admitted".into())
        } else {
            Ok(())
        }
    };
    let mut changed = body.clone();
    changed.local_decls[rustc_middle::mir::Local::from_usize(2)].ty = Ty::new_mut_ref(
        tcx,
        tcx.lifetimes.re_erased,
        Ty::new_slice(tcx, tcx.types.u32),
    );
    reject(&changed)?;
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (position, statement) in data.statements.iter().enumerate() {
            let StatementKind::Assign(assignment) = &statement.kind else {
                continue;
            };
            let replacement = match &assignment.1 {
                Rvalue::BinaryOp(BinOp::Offset, operands) => Some(Rvalue::BinaryOp(
                    BinOp::Offset,
                    Box::new((operands.1.clone(), operands.0.clone())),
                )),
                Rvalue::Aggregate(kind, operands)
                    if matches!(kind.as_ref(), AggregateKind::RawPtr(..)) =>
                {
                    let mut operands = operands.clone();
                    operands.swap(
                        rustc_abi::FieldIdx::from_usize(0),
                        rustc_abi::FieldIdx::from_usize(1),
                    );
                    Some(Rvalue::Aggregate(kind.clone(), operands))
                }
                Rvalue::Use(Operand::Copy(place), retag)
                    if place
                        .projection
                        .iter()
                        .any(|step| matches!(step, ProjectionElem::Field(..))) =>
                {
                    let mut projection = place.projection.to_vec();
                    for step in &mut projection {
                        if let ProjectionElem::Field(index, _) = step {
                            *step = ProjectionElem::Field(*index, tcx.types.u32);
                        }
                    }
                    Some(Rvalue::Use(
                        Operand::Copy(Place {
                            local: place.local,
                            projection: tcx.mk_place_elems(&projection),
                        }),
                        *retag,
                    ))
                }
                _ => None,
            };
            if let Some(replacement) = replacement {
                let mut changed = body.clone();
                let StatementKind::Assign(assignment) =
                    &mut changed.basic_blocks_mut()[block].statements[position].kind
                else {
                    unreachable!()
                };
                assignment.1 = replacement;
                reject(&changed)?;
            }
        }
    }
    Ok(())
}

pub(super) fn certify_f32_pair_guarded_family<'tcx>(
    tcx: TyCtxt<'tcx>,
    root: ty::Instance<'tcx>,
) -> Result<(), pure_comparison_templates::TemplateError> {
    certify_guarded_family(tcx, root, Schema::F32Pair)
}
