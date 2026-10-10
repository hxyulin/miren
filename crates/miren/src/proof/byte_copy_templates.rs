//! Conditional selected copy relation. Runtime source and destination authority are separate.
use super::*;

#[derive(Debug)]
pub(super) struct CertificateError {
    pub(super) category: UnknownCategory,
    pub(super) reason: String,
}
impl CertificateError {
    pub(super) fn resource(reason: &str) -> Self {
        Self {
            category: UnknownCategory::ResourceLimit,
            reason: reason.into(),
        }
    }
}
impl From<super::pure_comparison_templates::TemplateError> for CertificateError {
    fn from(error: super::pure_comparison_templates::TemplateError) -> Self {
        Self {
            category: error.category,
            reason: error.reason,
        }
    }
}
impl From<String> for CertificateError {
    fn from(reason: String) -> Self {
        Self {
            category: UnknownCategory::Semantics,
            reason,
        }
    }
}
impl From<&str> for CertificateError {
    fn from(reason: &str) -> Self {
        reason.to_owned().into()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum Family {
    Copy,
    Implementation,
    Precondition,
    Alignment,
    Nonoverlap,
}

fn family(definition: &str, encoded: &str) -> Option<Family> {
    super::byte_copy_references::REFERENCES
        .iter()
        .find_map(|(key, family, body)| {
            (*key == definition && body.strip_suffix('\n') == Some(encoded)).then_some(*family)
        })
}

fn reached(family: Family) -> &'static [usize] {
    match family {
        // Equal receiver/source lengths: the exact wrapper forwards both operands unchanged.
        Family::Copy => &[0, 1],
        // Length Ne is false. Both UbChecks settings converge on the sole exact copy intrinsic.
        Family::Implementation => &[0, 2, 3, 4, 5],
        // Size1/count<=128, align1, both valid nonnull typed references and nonoverlap.
        // Count zero and nonzero are included; pointer validity is required in either case.
        Family::Precondition => &[0, 2, 3, 4, 5, 10, 11, 13, 14, 15, 16, 18, 19, 20, 21],
        // ctpop(1)==1, then addr & (1-1)==0 for every pointer. The panic edge is excluded.
        Family::Alignment => &[0, 1, 3],
        // 1*count has no overflow in either target width. Both pointer orderings are included;
        // physical distance>=count follows only from the separately authenticated disjointness.
        Family::Nonoverlap => &[0, 3, 4, 5, 6],
    }
}

fn signature<'tcx>(tcx: TyCtxt<'tcx>, instance: ty::Instance<'tcx>, family: Family) -> bool {
    let signature = tcx.erase_and_anonymize_regions(
        tcx.fn_sig(instance.def_id())
            .instantiate(tcx, instance.args)
            .skip_binder(),
    );
    if signature.c_variadic() || signature.abi() != rustc_abi::ExternAbi::Rust {
        return false;
    }
    let safety = if family == Family::Implementation {
        rustc_hir::Safety::Unsafe
    } else {
        rustc_hir::Safety::Safe
    };
    if signature.safety() != safety {
        return false;
    }
    let unit = tcx.types.unit;
    let usize = tcx.types.usize;
    let slice = Ty::new_slice(tcx, tcx.types.u8);
    let shared_slice = |input: Ty<'tcx>, mutability| {
        matches!(input.kind(), ty::Ref(_, pointee, actual)
            if *pointee == slice && *actual == mutability)
    };
    let constant = Ty::new_ptr(tcx, unit, rustc_hir::Mutability::Not);
    let writable = Ty::new_ptr(tcx, unit, rustc_hir::Mutability::Mut);
    match family {
        Family::Copy | Family::Implementation => {
            signature.inputs().len() == 2
                && shared_slice(signature.inputs()[0], rustc_hir::Mutability::Mut)
                && shared_slice(signature.inputs()[1], rustc_hir::Mutability::Not)
                && signature.output() == unit
        }
        Family::Precondition => {
            signature.inputs() == [constant, writable, usize, usize, usize]
                && signature.output() == unit
        }
        Family::Alignment => {
            signature.inputs() == [constant, usize] && signature.output() == tcx.types.bool
        }
        Family::Nonoverlap => {
            signature.inputs() == [constant, constant, usize, usize]
                && signature.output() == tcx.types.bool
        }
    }
}

fn compiler_one<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
    property: &str,
) -> Result<(), String> {
    let Operand::Constant(operand) = operand else {
        return Err("byte copy layout operand is not the original compiler constant".into());
    };
    let rustc_middle::mir::Const::Unevaluated(value, _) = operand.const_ else {
        return Err("byte copy layout lacks its original compiler property".into());
    };
    if super::pure_comparison_templates::definition_key(value.def) != property
        || value.promoted.is_some()
        || value.args.type_at(0) != tcx.types.u8
        || operand.const_.ty() != tcx.types.usize
    {
        return Err("byte copy layout has a different original type or property".into());
    }
    let evaluated = operand
        .const_
        .eval(tcx, ty::TypingEnv::fully_monomorphized(), operand.span)
        .map_err(|_| "byte copy layout constant is unavailable")?;
    let rustc_middle::mir::ConstValue::Scalar(scalar) = evaluated else {
        return Err("byte copy layout constant is not scalar".into());
    };
    if scalar.to_bits(tcx.data_layout.pointer_size()).discard_err() != Some(1) {
        return Err("byte copy compiler size/alignment differs from one".into());
    }
    Ok(())
}

/// Checks the complete selected family under equal-length, valid/disjoint typed reference
/// premises. This function alone does not authenticate those premises or issue storage rights.
pub(super) fn certify<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    count: u128,
) -> Result<(), CertificateError> {
    use super::pure_comparison_templates as templates;
    if count > 128 {
        return Err(CertificateError::resource(
            "fixed byte copy exceeds its original target/count domain",
        ));
    }
    if !matches!(tcx.sess.target.pointer_width, 32 | 64) {
        return Err("fixed byte copy exceeds its original target/count domain".into());
    }
    let core = tcx
        .lang_items()
        .sized_trait()
        .ok_or("byte copy core identity missing")?
        .krate;
    let mut pending = vec![(instance, Family::Copy)];
    let mut seen = std::collections::HashSet::new();
    while let Some((instance, expected)) = pending.pop() {
        if !seen.insert((instance, expected)) {
            continue;
        }
        if seen.len() > 512 {
            return Err(CertificateError {
                category: UnknownCategory::ResourceLimit,
                reason: "fixed byte copy selected graph exceeds its 512-node budget".into(),
            });
        }
        if !matches!(instance.def, ty::InstanceKind::Item(_)) || instance.def_id().krate != core {
            return Err("fixed byte copy selected body has an unsupported origin".into());
        }
        if !tcx.is_mir_available(instance.def_id()) {
            return Err(CertificateError {
                category: UnknownCategory::MissingCompilerEvidence,
                reason: "fixed byte copy selected body is unavailable".into(),
            });
        }
        let generic = tcx.instance_mir(instance.def);
        let encoded = templates::encode_byte_copy_template(tcx, generic, core)?;
        if family(&templates::definition_key(instance.def_id()), &encoded) != Some(expected)
            || !signature(tcx, instance, expected)
        {
            return Err("fixed byte copy selected body or original signature differs".into());
        }
        let body = instance
            .try_instantiate_mir_and_normalize_erasing_regions(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                ty::EarlyBinder::bind(tcx, generic.clone()),
            )
            .map_err(|e| format!("fixed byte copy MIR substitution failed: {e:?}"))?;
        for index in reached(expected) {
            let block = body
                .basic_blocks
                .get(rustc_middle::mir::BasicBlock::from_usize(*index))
                .ok_or("fixed byte copy template block is absent")?;
            let TerminatorKind::Call {
                func,
                args: operands,
                ..
            } = &block.terminator().kind
            else {
                continue;
            };
            let ty::FnDef(id, args) = func.ty(&body.local_decls, tcx).kind() else {
                return Err("fixed byte copy selected transport is indirect".into());
            };
            let selected = ty::Instance::try_resolve(
                tcx,
                ty::TypingEnv::fully_monomorphized(),
                *id,
                args.skip_binder(),
            )
            .map_err(|e| format!("byte copy resolution failed:{e:?}"))?
            .ok_or("fixed byte copy selected transport is missing")?;
            if expected == Family::Implementation {
                compiler_one(
                    tcx,
                    &operands[2].node,
                    "DefId(core::mem::SizedTypeProperties::SIZE)",
                )?;
                compiler_one(
                    tcx,
                    &operands[3].node,
                    "DefId(core::mem::SizedTypeProperties::ALIGN)",
                )?;
            }
            let child = match expected {
                Family::Copy => Family::Implementation,
                Family::Implementation => Family::Precondition,
                Family::Precondition => {
                    if *index == 5 {
                        Family::Nonoverlap
                    } else {
                        Family::Alignment
                    }
                }
                Family::Alignment => {
                    if id.krate != core
                        || !tcx.is_intrinsic(*id, rustc_span::Symbol::intern("ctpop"))
                        || args.skip_binder().type_at(0) != tcx.types.usize
                    {
                        return Err("byte copy alignment has an unsupported intrinsic".into());
                    }
                    let intrinsic = tcx
                        .fn_sig(*id)
                        .instantiate(tcx, args.skip_binder())
                        .skip_binder();
                    if intrinsic.inputs() != [tcx.types.usize]
                        || intrinsic.output() != tcx.types.u32
                        || intrinsic.c_variadic()
                        || intrinsic.safety() != rustc_hir::Safety::Safe
                    {
                        return Err("byte copy alignment intrinsic signature differs".into());
                    }
                    continue;
                }
                Family::Nonoverlap => {
                    return Err("byte copy nonoverlap has an unexpected reachable call".into());
                }
            };
            pending.push((selected, child));
        }
    }
    Ok(())
}

/// Actual compiler-body mutation guard, exercised by the diagnostic integration test.
#[cfg(test)]
pub(super) fn mutation_guard<'tcx>(
    tcx: TyCtxt<'tcx>,
    generic: &Body<'tcx>,
    core: rustc_span::def_id::CrateNum,
) {
    use rustc_middle::mir::NonDivergingIntrinsic;
    let key = "DefId(core::slice::copy_from_slice_impl)";
    let original =
        super::pure_comparison_templates::encode_byte_copy_template(tcx, generic, core).unwrap();
    assert_eq!(family(key, &original), Some(Family::Implementation));
    let mut changed = generic.clone();
    let mut found = false;
    for block in changed.basic_blocks_mut().iter_mut() {
        for statement in &mut block.statements {
            if let StatementKind::Intrinsic(intrinsic) = &mut statement.kind
                && let NonDivergingIntrinsic::CopyNonOverlapping(copy) = intrinsic.as_mut()
            {
                std::mem::swap(&mut copy.src, &mut copy.dst);
                found = true;
            }
        }
    }
    assert!(found);
    let encoded =
        super::pure_comparison_templates::encode_byte_copy_template(tcx, &changed, core).unwrap();
    assert_ne!(encoded, original);
    assert_eq!(family(key, &encoded), None);
    let mut returned = generic.clone();
    returned.basic_blocks_mut()[rustc_middle::mir::BasicBlock::from_usize(5)]
        .terminator_mut()
        .kind = TerminatorKind::Unreachable;
    let encoded =
        super::pure_comparison_templates::encode_byte_copy_template(tcx, &returned, core).unwrap();
    assert_eq!(family(key, &encoded), None);
}
