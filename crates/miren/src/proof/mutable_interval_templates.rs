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

fn matches_body(key: &str, family: Family, encoded: &str) -> bool {
    REFERENCES.iter().any(|(expected, actual, body)| {
        *expected == key && *actual == family && body.strip_suffix('\n') == Some(encoded)
    })
}

fn signature<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>, family: Family) -> bool {
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
    let slice = Ty::new_slice(tcx, tcx.types.u16);
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
        if instance.def_id().krate != core
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || tcx.def_kind(instance.def_id()) != DefKind::AssocFn
            || !tcx.is_mir_available(instance.def_id())
        {
            return Err("interval selected body unavailable or not actual core Item".into());
        }
        if !signature(tcx, instance, family) {
            return Err("interval original selected signature differs".into());
        }
        let generic = tcx.instance_mir(instance.def);
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
            return Err("interval selected graph exceeds512 work".into());
        }
        for data in generic.basic_blocks.iter() {
            work = work.saturating_add(data.statements.len());
            if work > 512 {
                return Err("interval selected graph exceeds512 work".into());
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
            pure_comparison_templates::encode_byte_copy_template(tcx, template_body, core)
                .map_err(|reason| reason.reason)?;
        let key = pure_comparison_templates::definition_key(instance.def_id());
        if !matches_body(&key, family, &encoded) || !signature(tcx, instance, family) {
            return Err("interval complete selected body or signature differs".into());
        }
        if family == Family::Wrapper {
            let TerminatorKind::Call { func, .. } = &mono.basic_blocks
                [rustc_middle::mir::BasicBlock::from_usize(0)]
            .terminator()
            .kind
            else {
                return Err("interval wrapper delegate differs".into());
            };
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
                reject_mutation(tcx, core, &key, family, &changed)?;
            }
            if let TerminatorKind::Call { .. } = &data.terminator().kind {
                let mut changed = template_body.clone();
                let TerminatorKind::Call { args, .. } =
                    &mut changed.basic_blocks_mut()[block].terminator_mut().kind
                else {
                    unreachable!()
                };
                args.swap(0, 1);
                reject_mutation(tcx, core, &key, family, &changed)?;
            }
            if matches!(data.terminator().kind, TerminatorKind::Return) {
                let mut changed = template_body.clone();
                changed.basic_blocks_mut()[block].terminator_mut().kind =
                    TerminatorKind::Unreachable;
                reject_mutation(tcx, core, &key, family, &changed)?;
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
) -> Result<(), String> {
    let encoded = pure_comparison_templates::encode_byte_copy_template(tcx, changed, core)
        .map_err(|error| error.reason)?;
    if matches_body(key, family, &encoded) {
        Err("interval changed endpoint/receiver/offset/fat-pointer/return was admitted".into())
    } else {
        Ok(())
    }
}
