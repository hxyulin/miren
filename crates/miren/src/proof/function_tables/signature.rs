//! Bounded original full signatures; admission work is distinct from dispatch steps.
use super::super::aggregates::RepeatWork;
use super::*;
use rustc_middle::ty::{TypeSuperVisitable, TypeVisitable, TypeVisitor};
use std::ops::ControlFlow;

#[cfg(test)]
thread_local! {
    static CHECK_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(super) fn check_count() -> usize {
    CHECK_COUNT.with(std::cell::Cell::get)
}

struct Plan<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    work: &'a mut RepeatWork,
    arguments: ty::GenericArgsRef<'tcx>,
    nodes: usize,
    depth: usize,
    error: Option<String>,
}
impl Plan<'_, '_> {
    fn node(&mut self) -> Result<(), String> {
        self.engine.repeat_charge(self.work, 1)?;
        self.nodes += 1;
        if self.nodes > MAX_INPUT_VALUES || self.depth >= MAX_INPUT_DEPTH {
            return Err(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "nested function choice signature exceeds existing type graph limits".into(),
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
                    _ => self.refuse("nested function choice signature type substitution differs"),
                },
                None => self.refuse("nested function choice signature type argument absent"),
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
            | ty::Closure(..) => original.super_visit_with(self),
            ty::FnDef(_, arguments) => {
                let variables = arguments.bound_vars().len();
                if variables > MAX_INPUT_VALUES {
                    self.refuse("nested choice signature argument binder exceeds existing bounds")
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
            ty::FnPtr(signature, _) => {
                let variables = signature.bound_vars().len();
                if variables > MAX_INPUT_VALUES {
                    self.error = Some(
                        self.engine.categorized_error(
                            UnknownCategory::ResourceLimit,
                            "nested function choice nested signature binder exceeds existing limit"
                                .into(),
                        ),
                    );
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
            | ty::Error(_) => self.refuse(
                "nested function choice original signature type domain remains unsupported",
            ),
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
                    _ => self
                        .refuse("nested function choice signature constant substitution differs"),
                },
                None => self.refuse("nested function choice signature constant argument absent"),
            },
            ty::ConstKind::Value(_) => original.super_visit_with(self),
            ty::ConstKind::Bound(..)
            | ty::ConstKind::Alias(..)
            | ty::ConstKind::Expr(_)
            | ty::ConstKind::Infer(_)
            | ty::ConstKind::Placeholder(_)
            | ty::ConstKind::Error(_) => self.refuse(
                "nested function choice original signature constant domain remains unsupported",
            ),
        };
        self.depth -= 1;
        result
    }
}

pub(super) fn check<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    expected_pointer: Option<Ty<'tcx>>,
    work: &mut RepeatWork,
) -> Result<ty::PolyFnSig<'tcx>, String> {
    engine.repeat_charge(work, 8)?;
    if !(matches!(instance.def, ty::InstanceKind::Item(id)
        if matches!(engine.tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn))
        || matches!(instance.def, ty::InstanceKind::Intrinsic(_)))
        || instance.args.len() > MAX_INPUT_VALUES
        || instance.args.len() != engine.tcx.generics_of(instance.def_id()).count()
    {
        return Err("nested function choice full Instance differs".into());
    }
    let original = engine.tcx.fn_sig(instance.def_id());
    let poly = original.skip_binder();
    let count = poly.skip_binder().inputs_and_output.len();
    if count > MAX_INPUT_VALUES || poly.bound_vars().len() > MAX_INPUT_VALUES {
        return Err("nested function choice signature header exceeds bounds".into());
    }
    engine.repeat_charge(
        work,
        count + poly.bound_vars().len() + instance.args.len() + 4,
    )?;
    let mut plan = Plan {
        engine,
        work,
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
    let cost = plan.nodes + poly.bound_vars().len() + count + 4;
    // Actual substitution and normalization, independently prepaid before compiler services.
    engine.repeat_charge(plan.work, 2 * cost)?;
    #[cfg(test)]
    CHECK_COUNT.with(|count| count.set(count.get() + 1));
    let normalized = engine
        .tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::fully_monomorphized(),
            original.instantiate(engine.tcx, instance.args),
        )
        .map_err(|_| "nested function choice original signature normalization failed")?;
    engine.repeat_charge(plan.work, cost + 4 + engine.call_signatures.borrow().len())?;
    if engine
        .call_signatures
        .borrow()
        .get(&instance)
        .is_some_and(|cached| *cached != normalized)
    {
        return Err("nested function choice cached/original full signature differs".into());
    }
    let pointer = engine
        .tcx
        .erase_and_anonymize_regions(Ty::new_fn_ptr(engine.tcx, normalized));
    if expected_pointer
        .is_some_and(|expected| pointer != expected || !engine.table_signature(pointer))
    {
        return Err("nested function choice original safe signature differs".into());
    }
    Ok(normalized)
}
