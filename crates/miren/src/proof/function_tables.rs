//! Correlated known-target tables and actual prepared primitive calls.
use super::aggregates::MAX_ARRAY_ELEMENTS;
use super::function_pointers::Target;
use super::*;

const ENABLE_FUNCTION_TABLES: bool = true;
const ENABLE_INTEGER_FUNCTION_TABLES: bool = true;
const ENABLE_INTEGER_FUNCTION_TABLE_PAIRS: bool = true;
const ENABLE_TWO_ARGUMENT_INTEGER_FUNCTION_TABLES: bool = true;

#[cfg(test)]
thread_local! {
    static TWO_ARGUMENT_TABLE_OVERRIDE: std::cell::Cell<bool> = const {
        std::cell::Cell::new(false)
    };
}

fn two_argument_tables_enabled() -> bool {
    #[cfg(test)]
    if TWO_ARGUMENT_TABLE_OVERRIDE.with(std::cell::Cell::get) {
        return true;
    }
    ENABLE_TWO_ARGUMENT_INTEGER_FUNCTION_TABLES
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct IntegerSignature<'tcx> {
    original: Ty<'tcx>,
    bits: u32,
    signed: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct IntegerCallSignature<'tcx> {
    argument: IntegerSignature<'tcx>,
    result: IntegerSignature<'tcx>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct TwoArgumentIntegerSignature<'tcx> {
    first: IntegerSignature<'tcx>,
    second: IntegerSignature<'tcx>,
    result: IntegerSignature<'tcx>,
}

#[derive(Clone, PartialEq)]
pub(super) struct Choice<'tcx> {
    original: Ty<'tcx>,
    signature: Ty<'tcx>,
    index: Term,
    targets: Vec<usize>,
}

impl<'tcx> Choice<'tcx> {
    pub(super) fn signature(&self) -> Ty<'tcx> {
        self.signature
    }
}

pub(super) fn registry_cost(target: &Target<'_>) -> usize {
    match target {
        Target::Known { .. } | Target::Opaque { .. } => 1,
        Target::Choice(choice) => 1 + choice.targets.len(),
    }
}

pub(super) struct TableCall<'a, 'tcx> {
    pub(super) body: &'a Body<'tcx>,
    pub(super) block: rustc_middle::mir::BasicBlock,
    pub(super) func: &'a Operand<'tcx>,
    pub(super) args: &'a [rustc_span::Spanned<Operand<'tcx>>],
    pub(super) destination: Place<'tcx>,
    pub(super) target: Option<rustc_middle::mir::BasicBlock>,
    pub(super) stack: &'a [DefId],
    pub(super) site: (DefId, Span),
}

#[derive(Clone, Copy)]
pub(super) struct TableSource<'a, 'tcx> {
    pub(super) body: &'a Body<'tcx>,
    pub(super) prefix: Place<'tcx>,
    pub(super) state: &'a State,
    pub(super) index: rustc_middle::mir::Local,
}

impl<'tcx> Engine<'tcx> {
    fn original_integer_signature(&self, original: Ty<'tcx>) -> Option<IntegerSignature<'tcx>> {
        if !matches!(original.kind(), ty::Int(_) | ty::Uint(_)) {
            return None;
        }
        let (bits, signed) = self.integer_type(original)?;
        Some(IntegerSignature {
            original,
            bits,
            signed,
        })
    }

    fn integer_table_signature(&self, callable: Ty<'tcx>) -> Option<IntegerCallSignature<'tcx>> {
        let ty::FnPtr(..) = callable.kind() else {
            return None;
        };
        let signature = callable.fn_sig(self.tcx).skip_binder();
        let [argument] = signature.inputs() else {
            return None;
        };
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
        {
            return None;
        }
        Some(IntegerCallSignature {
            argument: self.original_integer_signature(*argument)?,
            result: self.original_integer_signature(signature.output())?,
        })
    }

    fn two_argument_integer_signature(
        &self,
        callable: Ty<'tcx>,
    ) -> Option<TwoArgumentIntegerSignature<'tcx>> {
        let ty::FnPtr(..) = callable.kind() else {
            return None;
        };
        let signature = callable.fn_sig(self.tcx).skip_binder();
        let [first, second] = signature.inputs() else {
            return None;
        };
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
        {
            return None;
        }
        Some(TwoArgumentIntegerSignature {
            first: self.original_integer_signature(*first)?,
            second: self.original_integer_signature(*second)?,
            result: self.original_integer_signature(signature.output())?,
        })
    }

    fn table_signature(&self, callable: Ty<'tcx>) -> bool {
        self.integer_table_signature(callable)
            .is_some_and(|signature| {
                if signature.argument.original != signature.result.original {
                    ENABLE_INTEGER_FUNCTION_TABLE_PAIRS
                } else {
                    signature.argument.original == self.tcx.types.u16
                        || ENABLE_INTEGER_FUNCTION_TABLES
                }
            })
            || (two_argument_tables_enabled()
                && self.two_argument_integer_signature(callable).is_some())
    }

    fn validate_table_result(
        &self,
        value: &Value,
        signature: IntegerSignature<'tcx>,
    ) -> Result<(), String> {
        let (term, bits, signed) = value.integer()?;
        if bits != signature.bits
            || signed != signature.signed
            || term.sort() != &Sort::BitVec(signature.bits)
            || !term.belongs_to(&self.terms)
        {
            return Err("function table result differs from original integer type".into());
        }
        Ok(())
    }

    pub(super) fn function_table_choice(
        &self,
        original: Ty<'tcx>,
        elements: &[Value],
        index: &Value,
        conditions: &[Term],
        source: Option<TableSource<'_, 'tcx>>,
    ) -> Result<Option<Value>, String> {
        if !ENABLE_FUNCTION_TABLES {
            return Ok(None);
        }
        let ty::Array(element, _) = original.kind() else {
            return Ok(None);
        };
        if !self.table_signature(*element) {
            return Ok(None);
        }
        let Some(source) = source else {
            return Ok(None);
        };
        self.owned_field_footprint(source.body, source.prefix)?;
        if source.prefix.ty(&source.body.local_decls, self.tcx).ty != original
            || source.body.local_decls[source.index].ty != self.tcx.types.usize
            || source.state.conditions != conditions
        {
            return Err("function table source differs from original compiler array".into());
        }
        let actual_index = self.local(source.state, source.index.as_usize())?;
        if actual_index.integer()? != index.integer()? {
            return Err("function table index differs from actual initialized source local".into());
        }
        let Value::Elements(current) = self
            .read_place(source.state, source.prefix, Some(source.body))?
            .materialize()?
        else {
            return Err("function table source requires a whole initialized owned array".into());
        };
        if current.len() != elements.len()
            || !current.iter().zip(elements).all(|(left, right)| {
                matches!((left,right), (Value::FunctionPointer {id:left},Value::FunctionPointer {id:right})
                    if left == right)
            })
        {
            return Err("function table elements differ from their actual current source".into());
        }
        self.capture_function_table(original, elements, index, conditions)
    }

    pub(super) fn capture_function_table(
        &self,
        original: Ty<'tcx>,
        elements: &[Value],
        index: &Value,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        let ty::Array(element, count) = original.kind() else {
            return Ok(None);
        };
        if self.integer_table_signature(*element).is_none()
            && self.two_argument_integer_signature(*element).is_none()
        {
            return Ok(None);
        }
        if elements.is_empty()
            || elements.len() > MAX_ARRAY_ELEMENTS
            || count.try_to_target_usize(self.tcx) != Some(elements.len() as u64)
        {
            return Err("function table differs from its original fixed array".into());
        }
        let (expression, bits, signed) = index.integer()?;
        if signed
            || bits != u32::from(self.tcx.sess.target.pointer_width)
            || expression.sort() != &Sort::BitVec(bits)
            || !expression.belongs_to(&self.terms)
        {
            return Err("function table index requires current target usize".into());
        }
        let signature = self.tcx.erase_and_anonymize_regions(*element);
        let mut targets = Vec::with_capacity(elements.len());
        for value in elements {
            let Value::FunctionPointer { id } = value else {
                return Err("function table requires initialized known pointer elements".into());
            };
            self.validate_table_target(*id, signature)?;
            targets.push(*id);
        }
        let bound = symbolic::binary(
            &self.terms,
            "lt",
            index.clone(),
            symbolic::integer(&self.terms, elements.len() as u128, bits, false),
        )?
        .boolean()?;
        let mut outside = conditions.to_vec();
        outside.push(symbolic::not(&bound));
        if self.feasible(&outside)? {
            return Err("function table read lacks a proven bounds check".into());
        }
        let id = self.register_function_pointer(Target::Choice(Choice {
            original,
            signature,
            index: expression,
            targets,
        }))?;
        Ok(Some(Value::FunctionPointer { id }))
    }

    fn validate_table_target(
        &self,
        id: usize,
        expected: Ty<'tcx>,
    ) -> Result<ty::Instance<'tcx>, String> {
        let entry = self
            .function_pointers
            .borrow()
            .get(id)
            .cloned()
            .ok_or("function table target is missing")?;
        let Target::Known {
            instance,
            signature,
        } = entry
        else {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "function table cannot contain opaque or nested choices".into(),
            ));
        };
        if signature != expected
            || (self.integer_table_signature(signature).is_none()
                && self.two_argument_integer_signature(signature).is_none())
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
            || self.tcx.erase_and_anonymize_regions(Ty::new_fn_ptr(
                self.tcx,
                self.call_poly_signature(instance)?,
            )) != expected
        {
            return Err("function table target differs from its original safe signature".into());
        }
        Ok(instance)
    }

    pub(super) fn function_table_call(
        &mut self,
        state: &State,
        call: TableCall<'_, 'tcx>,
    ) -> Result<Option<Vec<(State, Return)>>, String> {
        if !ENABLE_FUNCTION_TABLES {
            return Ok(None);
        }
        self.prepared_function_table_call(state, call)
    }

    pub(super) fn prepared_function_table_call(
        &mut self,
        state: &State,
        call: TableCall<'_, 'tcx>,
    ) -> Result<Option<Vec<(State, Return)>>, String> {
        // This is only a routing hint. The actual operand is read and consumed below.
        // A non-choice takes the original pipeline without a second operand evaluation.
        let (Operand::Copy(place) | Operand::Move(place)) = call.func else {
            return Ok(None);
        };
        if !place.projection.is_empty() || state.addresses[place.local.as_usize()].is_some() {
            return Ok(None);
        }
        let Some(Value::FunctionPointer { id }) = &state.locals[place.local.as_usize()] else {
            return Ok(None);
        };
        let Some(Target::Choice(choice)) = self.function_pointers.borrow().get(*id).cloned() else {
            return Ok(None);
        };
        let terminator = call.body.basic_blocks[call.block].terminator();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            ..
        } = &terminator.kind
        else {
            return Err("function table dispatch is not the actual Call terminator".into());
        };
        if !std::ptr::eq(func, call.func)
            || !std::ptr::eq(args.as_ref(), call.args)
            || *destination != call.destination
            || *target != call.target
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || call.body.source.def_id() != call.site.0
            || terminator.source_info.span != call.site.1
            || call.body.coroutine.is_some()
            || call.body.tainted_by_errors.is_some()
            || call.body.spread_arg.is_some()
            || call.body.basic_blocks[call.block].is_cleanup
        {
            return Err("function table dispatch differs from actual abort-only Call".into());
        }
        let callable = self
            .tcx
            .erase_and_anonymize_regions(call.func.ty(&call.body.local_decls, self.tcx));
        let ty::Array(element, count) = choice.original.kind() else {
            return Err("function table choice lost its original array type".into());
        };
        let Some(integer) = self.integer_table_signature(callable) else {
            if two_argument_tables_enabled()
                && let Some(integer) = self.two_argument_integer_signature(callable)
            {
                return self.prepared_two_argument_table_call(
                    state, call, &choice, *id, callable, integer,
                );
            }
            return Err("function table call requires an original integer signature".into());
        };
        if callable != choice.signature
            || self.tcx.erase_and_anonymize_regions(*element) != callable
            || count.try_to_target_usize(self.tcx) != Some(choice.targets.len() as u64)
            || choice.targets.is_empty()
            || choice.targets.len() > MAX_ARRAY_ELEMENTS
            || !choice.index.belongs_to(&self.terms)
            || choice.index.sort() != &Sort::BitVec(u32::from(self.tcx.sess.target.pointer_width))
            || call.args.len() != 1
            || call.args[0].node.ty(&call.body.local_decls, self.tcx) != integer.argument.original
            || call.destination.ty(&call.body.local_decls, self.tcx).ty != integer.result.original
            || call.target.is_none()
            || !state.memory.mutable_u16.is_empty()
            || !state.memory.owned_regions.is_empty()
        {
            return Err("function table call exceeds its primitive prepared-call domain".into());
        }
        // Copy must authenticate recorded FieldTy just as Move consumption already does.
        // The initial protocol admits direct locals and fixed original owned field paths.
        if let Operand::Copy(place) | Operand::Move(place) = &call.args[0].node {
            self.owned_field_footprint(call.body, *place)?;
        }
        self.owned_field_footprint(call.body, call.destination)?;
        let instances = choice
            .targets
            .iter()
            .map(|id| self.validate_table_target(*id, callable))
            .collect::<Result<Vec<_>, _>>()?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let outside = self.terms.apply(
            Op::Not,
            &[self.terms.apply(
                Op::BvUnsignedLt,
                &[
                    choice.index.clone(),
                    self.terms.bit_vector(choice.targets.len() as u128, bits)?,
                ],
            )?],
        )?;
        let mut uncovered = state.conditions.clone();
        uncovered.push(outside);
        if self.feasible(&uncovered)? {
            return Err("function table call lost its covered index domain".into());
        }
        let next = self
            .steps
            .checked_add(instances.len())
            .ok_or("function table step overflow")?;
        if next > self.limits.max_steps {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "function table expansion exceeds execution step budget".into(),
            ));
        }
        self.steps = next;
        let mut consumed = state.clone();
        let actual = self.evaluate_operand(call.site.0, call.body, &mut consumed, call.func)?;
        if !matches!(actual, Value::FunctionPointer { id: actual } if actual == *id) {
            return Err("function table actual callable differs from its routing hint".into());
        }
        let value =
            self.evaluate_operand(call.site.0, call.body, &mut consumed, &call.args[0].node)?;
        let (term, bits, signed) = value.integer()?;
        if bits != integer.argument.bits
            || signed != integer.argument.signed
            || term.sort() != &Sort::BitVec(integer.argument.bits)
            || !term.belongs_to(&self.terms)
        {
            return Err(if integer.argument.original == self.tcx.types.u16 {
                "function table argument differs from original u16".into()
            } else {
                "function table argument differs from original integer type".into()
            });
        }
        self.validate_owned_call_arguments(std::slice::from_ref(&value), &consumed.memory)?;
        let mut returns = Vec::new();
        for (position, instance) in instances.into_iter().enumerate() {
            let mut conditions = consumed.conditions.clone();
            conditions.push(self.terms.apply(
                Op::Equal,
                &[
                    choice.index.clone(),
                    self.terms.bit_vector(
                        position as u128,
                        u32::from(self.tcx.sess.target.pointer_width),
                    )?,
                ],
            )?);
            if !self.feasible(&conditions)? {
                continue;
            }
            if self.specification(instance)?.is_some() {
                return Err(
                    "function table configured target is outside the initial domain".into(),
                );
            }
            let mut branch = consumed.clone();
            self.byte_copy_call_eligibility(instance, true, &mut branch);
            for result in self.call_instance(
                instance,
                vec![value.clone()],
                conditions,
                branch.memory.clone(),
                call.stack,
                call.site,
            )? {
                self.validate_table_result(&result.value, integer.result)?;
                returns.push((branch.clone(), result));
            }
        }
        Ok(Some(returns))
    }

    fn prepared_two_argument_table_call(
        &mut self,
        state: &State,
        call: TableCall<'_, 'tcx>,
        choice: &Choice<'tcx>,
        id: usize,
        callable: Ty<'tcx>,
        integer: TwoArgumentIntegerSignature<'tcx>,
    ) -> Result<Option<Vec<(State, Return)>>, String> {
        let ty::Array(element, count) = choice.original.kind() else {
            return Err("two-argument table lost its original array type".into());
        };
        if callable != choice.signature
            || self.tcx.erase_and_anonymize_regions(*element) != callable
            || count.try_to_target_usize(self.tcx) != Some(choice.targets.len() as u64)
            || choice.targets.is_empty()
            || choice.targets.len() > MAX_ARRAY_ELEMENTS
            || !choice.index.belongs_to(&self.terms)
            || choice.index.sort() != &Sort::BitVec(u32::from(self.tcx.sess.target.pointer_width))
            || call.args.len() != 2
            || call.target.is_none()
            || !state.memory.mutable_u16.is_empty()
            || !state.memory.owned_regions.is_empty()
        {
            return Err("two-argument table exceeds its primitive prepared-call domain".into());
        }
        for operand in call.args {
            if let Operand::Copy(place) | Operand::Move(place) = operand.node {
                self.owned_field_footprint(call.body, place)?;
            }
        }
        self.owned_field_footprint(call.body, call.destination)?;
        if call.args[0].node.ty(&call.body.local_decls, self.tcx) != integer.first.original
            || call.args[1].node.ty(&call.body.local_decls, self.tcx) != integer.second.original
            || call.destination.ty(&call.body.local_decls, self.tcx).ty != integer.result.original
        {
            return Err("two-argument table operands differ from original A/B/R types".into());
        }
        // Preserve the old all-target validation policy before feasibility or operand reads.
        let instances = choice
            .targets
            .iter()
            .map(|id| self.validate_table_target(*id, callable))
            .collect::<Result<Vec<_>, _>>()?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let outside = self.terms.apply(
            Op::Not,
            &[self.terms.apply(
                Op::BvUnsignedLt,
                &[
                    choice.index.clone(),
                    self.terms.bit_vector(choice.targets.len() as u128, bits)?,
                ],
            )?],
        )?;
        let mut uncovered = state.conditions.clone();
        uncovered.push(outside);
        if self.feasible(&uncovered)? {
            return Err("two-argument table lost its covered index domain".into());
        }
        let next = self
            .steps
            .checked_add(instances.len())
            .ok_or("function table step overflow")?;
        if next > self.limits.max_steps {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "function table expansion exceeds execution step budget".into(),
            ));
        }
        self.steps = next;
        let mut consumed = state.clone();
        let actual = self.evaluate_operand(call.site.0, call.body, &mut consumed, call.func)?;
        if !matches!(actual, Value::FunctionPointer { id: actual } if actual == id) {
            return Err("two-argument table callable differs from its routing hint".into());
        }
        let first =
            self.evaluate_operand(call.site.0, call.body, &mut consumed, &call.args[0].node)?;
        self.validate_table_result(&first, integer.first)?;
        let second =
            self.evaluate_operand(call.site.0, call.body, &mut consumed, &call.args[1].node)?;
        self.validate_table_result(&second, integer.second)?;
        let values = vec![first, second];
        self.validate_owned_call_arguments(&values, &consumed.memory)?;
        let mut returns = Vec::new();
        for (position, instance) in instances.into_iter().enumerate() {
            let mut conditions = consumed.conditions.clone();
            conditions.push(self.terms.apply(
                Op::Equal,
                &[
                    choice.index.clone(),
                    self.terms.bit_vector(position as u128, bits)?,
                ],
            )?);
            if !self.feasible(&conditions)? {
                continue;
            }
            if self.specification(instance)?.is_some() {
                return Err(
                    "function table configured target is outside the initial domain".into(),
                );
            }
            let mut branch = consumed.clone();
            self.byte_copy_call_eligibility(instance, true, &mut branch);
            for result in self.call_instance(
                instance,
                values.clone(),
                conditions,
                branch.memory.clone(),
                call.stack,
                call.site,
            )? {
                self.validate_table_result(&result.value, integer.result)?;
                returns.push((branch.clone(), result));
            }
        }
        Ok(Some(returns))
    }
}

#[cfg(test)]
#[path = "function_tables_probe.rs"]
mod tests;

#[cfg(test)]
#[path = "integer_function_tables_probe.rs"]
mod integer_tests;

#[cfg(test)]
#[path = "integer_function_table_pairs_probe.rs"]
mod integer_pair_tests;
