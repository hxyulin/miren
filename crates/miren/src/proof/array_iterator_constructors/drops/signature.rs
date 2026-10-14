//! Paid original full callable signatures, independent of the mutable dispatcher cache.
use super::super::*;
use rustc_middle::ty::{TypeSuperVisitable, TypeVisitable, TypeVisitor};
use std::ops::ControlFlow;

struct Plan<'a, 'tcx> {
    engine: &'a mut Engine<'tcx>,
    arguments: ty::GenericArgsRef<'tcx>,
    nodes: usize,
    depth: usize,
    error: Option<String>,
}
impl Plan<'_, '_> {
    fn node(&mut self) -> Result<(), String> {
        pay(self.engine, 1)?;
        self.nodes += 1;
        if self.nodes > MAX_INPUT_VALUES || self.depth >= MAX_INPUT_DEPTH {
            return Err(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "IntoIter Drop signature exceeds existing type graph limits".into(),
            ));
        }
        Ok(())
    }
    fn refuse(&mut self, message: &str) -> ControlFlow<()> {
        self.error = Some(
            self.engine
                .categorized_error(UnknownCategory::Semantics, message.into()),
        );
        ControlFlow::Break(())
    }
}
impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for Plan<'_, 'tcx> {
    type Result = ControlFlow<()>;
    fn visit_ty(&mut self, original: Ty<'tcx>) -> Self::Result {
        if let Err(error) = self.node() {
            self.error = Some(error);
            return ControlFlow::Break(());
        }
        self.depth += 1;
        let result = match original.kind() {
            ty::Param(parameter) => match self.arguments.get(parameter.index as usize) {
                Some(argument) => match argument.kind() {
                    ty::GenericArgKind::Type(value) if value != original => self.visit_ty(value),
                    _ => self.refuse("IntoIter Drop signature type substitution differs"),
                },
                None => self.refuse("IntoIter Drop signature type argument absent"),
            },
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Never
            | ty::Tuple(_)
            | ty::Array(..)
            | ty::Slice(_)
            | ty::Ref(..)
            | ty::RawPtr(..)
            | ty::Adt(..)
            | ty::FnDef(..)
            | ty::Closure(..) => original.super_visit_with(self),
            ty::FnPtr(signature, _) => {
                let variables = signature.bound_vars().len();
                if variables > MAX_INPUT_VALUES {
                    self.error = Some(self.engine.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "IntoIter Drop nested signature binder exceeds existing limit".into(),
                    ));
                    ControlFlow::Break(())
                } else {
                    let mut result = ControlFlow::Continue(());
                    for _ in 0..variables {
                        if let Err(error) = self.node() {
                            self.error = Some(error);
                            result = ControlFlow::Break(());
                            break;
                        }
                    }
                    if result.is_continue() {
                        original.super_visit_with(self)
                    } else {
                        result
                    }
                }
            }
            ty::Bound(..)
            | ty::Alias(..)
            | ty::Foreign(_)
            | ty::Pat(..)
            | ty::UnsafeBinder(_)
            | ty::Dynamic(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::CoroutineWitness(..)
            | ty::Placeholder(_)
            | ty::Infer(_)
            | ty::Error(_) => {
                self.refuse("IntoIter Drop original signature type domain remains unsupported")
            }
        };
        self.depth -= 1;
        result
    }
    fn visit_region(&mut self, _: ty::Region<'tcx>) -> Self::Result {
        match self.node() {
            Ok(()) => ControlFlow::Continue(()),
            Err(error) => {
                self.error = Some(error);
                ControlFlow::Break(())
            }
        }
    }
    fn visit_const(&mut self, original: ty::Const<'tcx>) -> Self::Result {
        if let Err(error) = self.node() {
            self.error = Some(error);
            return ControlFlow::Break(());
        }
        self.depth += 1;
        let result = match original.kind() {
            ty::ConstKind::Param(parameter) => match self.arguments.get(parameter.index as usize) {
                Some(argument) => match argument.kind() {
                    ty::GenericArgKind::Const(value) if value != original => {
                        self.visit_const(value)
                    }
                    _ => self.refuse("IntoIter Drop signature constant substitution differs"),
                },
                None => self.refuse("IntoIter Drop signature constant argument absent"),
            },
            ty::ConstKind::Value(_) => original.super_visit_with(self),
            ty::ConstKind::Bound(..)
            | ty::ConstKind::Alias(..)
            | ty::ConstKind::Expr(_)
            | ty::ConstKind::Infer(_)
            | ty::ConstKind::Placeholder(_)
            | ty::ConstKind::Error(_) => {
                self.refuse("IntoIter Drop original signature constant domain remains unsupported")
            }
        };
        self.depth -= 1;
        result
    }
}

pub(super) fn check<'tcx>(
    engine: &mut Engine<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<ty::PolyFnSig<'tcx>, String> {
    pay(engine, 8)?;
    if !matches!(instance.def, ty::InstanceKind::Item(id)
        if matches!(engine.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn))
    {
        return Err("IntoIter Drop signature requires an original ordinary callable".into());
    }
    if instance.args.len() > MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "IntoIter Drop signature Instance exceeds existing 512-value limit".into(),
        ));
    }
    if instance.args.len() != engine.tcx.generics_of(instance.def_id()).count() {
        return Err("IntoIter Drop signature full Instance arguments differ".into());
    }
    let original = engine.tcx.fn_sig(instance.def_id());
    let poly = original.skip_binder();
    let count = poly.skip_binder().inputs_and_output.len();
    if count > MAX_INPUT_VALUES || poly.bound_vars().len() > MAX_INPUT_VALUES {
        return Err(engine.categorized_error(
            UnknownCategory::ResourceLimit,
            "IntoIter Drop signature header exceeds existing 512-value limit".into(),
        ));
    }
    pay(
        engine,
        count + poly.bound_vars().len() + instance.args.len() + 4,
    )?;
    let mut plan = Plan {
        engine,
        arguments: instance.args,
        nodes: 0,
        depth: 0,
        error: None,
    };
    let _ = instance.args.visit_with(&mut plan);
    if plan.error.is_none() {
        let _ = poly.visit_with(&mut plan);
    }
    if let Some(error) = plan.error {
        return Err(error);
    }
    let work = plan.nodes + poly.bound_vars().len() + count + 4;
    // Disjoint prepayment for actual substitution and normalization of this bounded graph.
    pay(plan.engine, 2 * work)?;
    let expected = plan
        .engine
        .tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            original.instantiate(plan.engine.tcx, instance.args),
        )
        .map_err(|error| {
            format!("IntoIter Drop original full signature normalization: {error:?}")
        })?;
    // Interned signature comparison and bounded cache lookup are distinct. This gate publishes
    // nothing; a missing dispatcher entry will still be derived from the same compiler source.
    let registry = plan.engine.call_signatures.borrow().len();
    pay(plan.engine, registry + work + 4)?;
    let prior = plan.engine.call_signatures.borrow().get(&instance).copied();
    if prior.is_some_and(|cached| cached != expected) {
        return Err(plan.engine.categorized_error(
            UnknownCategory::Semantics,
            "IntoIter Drop cached/original full signature differs".into(),
        ));
    }
    Ok(expected)
}
