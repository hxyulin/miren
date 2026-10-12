//! Correlated known-target tables and actual prepared primitive calls.
use super::aggregates::MAX_ARRAY_ELEMENTS;
use super::function_pointers::Target;
use super::*;
use rustc_middle::mir::visit::Visitor;

const ENABLE_PRIMITIVE_FUNCTION_TABLES: bool = true;

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

#[cfg(test)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum FloatTableReturnFault {
    None,
    WrongWidth,
    MissingRaw,
    ForeignContext,
    InconsistentRaw,
}

#[cfg(test)]
thread_local! {
    static FLOAT_TABLE_RETURN_FAULT: std::cell::Cell<FloatTableReturnFault> = const {
        std::cell::Cell::new(FloatTableReturnFault::None)
    };
    static FLOAT_TABLE_RETURN_OBSERVATIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
fn observed_float_table_return(engine: &Engine<'_>, value: &Value) -> Value {
    let fault = FLOAT_TABLE_RETURN_FAULT.with(std::cell::Cell::get);
    if fault == FloatTableReturnFault::None {
        return value.clone();
    }
    FLOAT_TABLE_RETURN_OBSERVATIONS.with(|count| count.set(count.get() + 1));
    let Value::Float {
        expression,
        bits,
        raw_bits,
    } = value
    else {
        return value.clone();
    };
    match fault {
        FloatTableReturnFault::None => value.clone(),
        FloatTableReturnFault::WrongWidth => Value::Float {
            expression: expression.clone(),
            bits: if *bits == 32 { 64 } else { 32 },
            raw_bits: raw_bits.clone(),
        },
        FloatTableReturnFault::MissingRaw => Value::Float {
            expression: expression.clone(),
            bits: *bits,
            raw_bits: None,
        },
        FloatTableReturnFault::ForeignContext => symbolic::float(&Context::default(), 0, *bits),
        FloatTableReturnFault::InconsistentRaw => Value::Float {
            expression: expression.clone(),
            bits: *bits,
            raw_bits: Some(engine.terms.bit_vector(1, *bits).unwrap()),
        },
    }
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

// Values are already evaluated and consumed before this private dispatch carrier is built.
enum EvaluatedTableArguments {
    One(Value),
    Two(Vec<Value>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PrimitiveSignature<'tcx> {
    Bool(Ty<'tcx>),
    Char(Ty<'tcx>),
    Float32(Ty<'tcx>),
    Float64(Ty<'tcx>),
}

impl<'tcx> PrimitiveSignature<'tcx> {
    fn original(self) -> Ty<'tcx> {
        match self {
            Self::Bool(original)
            | Self::Char(original)
            | Self::Float32(original)
            | Self::Float64(original) => original,
        }
    }
}

#[derive(Clone, Copy)]
enum TableResultSignature<'tcx> {
    Integer(IntegerSignature<'tcx>),
    Primitive(PrimitiveSignature<'tcx>),
}

#[derive(Clone, Copy)]
enum PrimitiveBodyDomain {
    BoolChar,
    Float32,
    Float64,
}

impl PrimitiveSignature<'_> {
    fn body_domain(self) -> PrimitiveBodyDomain {
        match self {
            Self::Bool(_) | Self::Char(_) => PrimitiveBodyDomain::BoolChar,
            Self::Float32(_) => PrimitiveBodyDomain::Float32,
            Self::Float64(_) => PrimitiveBodyDomain::Float64,
        }
    }
}

// New primitive admission alone scans this borrowed grammar before selected Body cloning.
struct PrimitiveBodyWork<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    domain: PrimitiveBodyDomain,
    used: usize,
    error: Option<String>,
    locals: usize,
}

impl<'tcx> PrimitiveBodyWork<'_, 'tcx> {
    fn charge(&mut self, count: usize) {
        if self.error.is_some() {
            return;
        }
        self.used = self.used.saturating_add(count);
        if self.used > MAX_INPUT_VALUES {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "primitive table borrowed admission exceeds 512 work units".into(),
            ));
        }
    }

    fn original_type(&mut self, original: Ty<'tcx>, depth: usize) {
        self.charge(1);
        if self.error.is_some() {
            return;
        }
        if depth >= MAX_INPUT_DEPTH {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "primitive table original type exceeds depth16".into(),
            ));
            return;
        }
        match original.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Never => {}
            ty::Float(ty::FloatTy::F32) if matches!(self.domain, PrimitiveBodyDomain::Float32) => {}
            ty::Float(ty::FloatTy::F64) if matches!(self.domain, PrimitiveBodyDomain::Float64) => {}
            ty::Tuple(fields) => {
                self.charge(fields.len());
                if self.error.is_some() {
                    return;
                }
                for field in fields.iter() {
                    self.original_type(field, depth + 1);
                }
            }
            ty::FnDef(_, args) if args.skip_binder().is_empty() => {}
            _ => self.error = Some("primitive table borrowed type grammar is unsupported".into()),
        }
    }
    fn operand_place(&mut self, body: &Body<'tcx>, place: Place<'tcx>) -> Result<(), String> {
        let declaration = body
            .local_decls
            .get(place.local)
            .ok_or("primitive table operand local is unavailable")?;
        self.original_type(declaration.ty, 0);
        self.visit_place(
            &place,
            rustc_middle::mir::visit::PlaceContext::NonMutatingUse(
                rustc_middle::mir::visit::NonMutatingUseContext::Inspect,
            ),
            rustc_middle::mir::Location::START,
        );
        self.error.take().map_or(Ok(()), Err)
    }
}

impl<'tcx> Visitor<'tcx> for PrimitiveBodyWork<'_, 'tcx> {
    fn visit_ty(&mut self, original: Ty<'tcx>, _: rustc_middle::mir::visit::TyContext) {
        self.original_type(original, 0);
    }

    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        _: rustc_middle::mir::visit::PlaceContext,
        _: rustc_middle::mir::Location,
    ) {
        self.charge(place.projection.len());
        if place.local.as_usize() >= self.locals || place.projection.len() >= MAX_INPUT_DEPTH {
            if self.error.is_none() {
                self.error = Some("primitive table borrowed place is unsupported".into());
            }
            return;
        }
        for projection in place.projection {
            match projection {
                ProjectionElem::Field(_, original) => self.original_type(original, 0),
                ProjectionElem::Deref
                | ProjectionElem::Index(_)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. }
                | ProjectionElem::Downcast(_, _)
                | ProjectionElem::OpaqueCast(_)
                | ProjectionElem::UnwrapUnsafeBinder(_)
                | ProjectionElem::PhantomDeref => {
                    if self.error.is_none() {
                        self.error =
                            Some("primitive table borrowed projection is unsupported".into());
                    }
                }
            }
        }
    }

    fn visit_user_type_projection(&mut self, projection: &rustc_middle::mir::UserTypeProjection) {
        self.charge(projection.projs.len());
        if self.error.is_none() {
            self.error = Some("primitive table user projection is unsupported".into());
        }
    }

    fn visit_ty_const(&mut self, _: ty::Const<'tcx>, _: rustc_middle::mir::Location) {
        if self.error.is_none() {
            self.error = Some("primitive table type constant is unsupported".into());
        }
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: rustc_middle::mir::Location) {
        self.charge(1);
        if self.error.is_none() {
            self.super_operand(operand, location);
        }
    }

    fn visit_const_operand(
        &mut self,
        constant: &rustc_middle::mir::ConstOperand<'tcx>,
        _: rustc_middle::mir::Location,
    ) {
        match constant.const_ {
            rustc_middle::mir::Const::Val(
                rustc_middle::mir::ConstValue::Scalar(_) | rustc_middle::mir::ConstValue::ZeroSized,
                original,
            ) => self.original_type(original, 0),
            _ if self.error.is_none() => {
                self.error = Some("primitive table borrowed constant is unsupported".into());
            }
            _ => {}
        }
    }

    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: rustc_middle::mir::Location) {
        if let Rvalue::Aggregate(kind, operands) = value {
            self.charge(operands.len());
            if self.error.is_none() && !matches!(**kind, rustc_middle::mir::AggregateKind::Tuple) {
                self.error = Some("primitive table borrowed aggregate is unsupported".into());
            }
        }
        if self.error.is_none() {
            self.super_rvalue(value, location);
        }
    }

    fn visit_terminator(
        &mut self,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        match &terminator.kind {
            TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                self.charge(args.len());
            }
            TerminatorKind::SwitchInt { targets, .. } => {
                self.charge(targets.all_targets().len().saturating_mul(2))
            }
            TerminatorKind::InlineAsm { .. } if self.error.is_none() => {
                self.error = Some("primitive table inline assembly is unsupported".into());
            }
            _ => {}
        }
        if self.error.is_none() {
            self.super_terminator(terminator, location);
        }
    }
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
    pub(super) fn validate_repeat_target(
        &self,
        value: &Value,
        expected: Ty<'tcx>,
        work: &mut super::aggregates::RepeatWork,
    ) -> Result<(), String> {
        self.repeat_type_work(expected, self.tcx.mk_args(&[]), 0, work)?;
        let Value::FunctionPointer { id } = value else {
            return Err("known Repeat operand lacks its evaluated function-pointer token".into());
        };
        let (instance, signature) = {
            let pointers = self.function_pointers.borrow();
            let target = pointers
                .get(*id)
                .ok_or("known Repeat target registry entry is unavailable")?;
            match target {
                Target::Known {
                    instance,
                    signature,
                } => (*instance, *signature),
                Target::Opaque { .. } | Target::Choice(_) => {
                    return Err("known Repeat refuses opaque or nested Choice targets".into());
                }
            }
        };
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
            || signature != expected
        {
            return Err("known Repeat target original Instance/signature differs".into());
        }
        self.repeat_argument_work(instance.args, 0, work)?;
        let raw = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate_identity()
            .skip_norm_wip();
        if !raw.bound_vars().is_empty() {
            return Err("known Repeat selected bound signature is unsupported".into());
        }
        self.repeat_signature_work(raw.skip_binder(), instance.args, 0, work)?;
        let instantiated = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate(self.tcx, instance.args)
            .skip_norm_wip();
        if instantiated != expected.fn_sig(self.tcx) {
            return Err(
                "known Repeat raw substituted signature differs from original FnPtr".into(),
            );
        }
        if !self.table_signature(expected) {
            return Err("known Repeat target family is not enabled".into());
        }
        self.validate_table_target(*id, expected)?;
        Ok(())
    }

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

    fn primitive_table_signature(&self, callable: Ty<'tcx>) -> Option<PrimitiveSignature<'tcx>> {
        if !ENABLE_PRIMITIVE_FUNCTION_TABLES || !matches!(callable.kind(), ty::FnPtr(..)) {
            return None;
        }
        let poly = callable.fn_sig(self.tcx);
        if !poly.bound_vars().is_empty() {
            return None;
        }
        let signature = poly.skip_binder();
        let [argument] = signature.inputs() else {
            return None;
        };
        if *argument != signature.output()
            || signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
        {
            return None;
        }
        match argument.kind() {
            ty::Bool => Some(PrimitiveSignature::Bool(*argument)),
            ty::Char => Some(PrimitiveSignature::Char(*argument)),
            ty::Float(ty::FloatTy::F32) => Some(PrimitiveSignature::Float32(*argument)),
            ty::Float(ty::FloatTy::F64) => Some(PrimitiveSignature::Float64(*argument)),
            _ => None,
        }
    }

    fn validate_primitive_table_value(
        &self,
        value: &Value,
        signature: PrimitiveSignature<'tcx>,
        conditions: &[Term],
    ) -> Result<(), String> {
        match signature {
            PrimitiveSignature::Bool(_) => {
                let term = value.boolean()?;
                if term.sort() != &Sort::Bool || !term.belongs_to(&self.terms) {
                    return Err(
                        "primitive table Bool value has inconsistent context or sort".into(),
                    );
                }
                Ok(())
            }
            PrimitiveSignature::Char(_) => self.prove_char_value(value, conditions),
            PrimitiveSignature::Float32(_) => self.prove_scalar_float(value, 32, conditions),
            PrimitiveSignature::Float64(_) => self.prove_scalar_float(value, 64, conditions),
        }
    }

    fn primitive_table_body_work(
        &self,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
        work: &mut PrimitiveBodyWork<'_, 'tcx>,
    ) -> Result<(), String> {
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
            || !instance.args.is_empty()
        {
            return Err(
                "primitive table borrowed Body needs an exact nongeneric named Item".into(),
            );
        }
        let raw = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate_identity()
            .skip_norm_wip();
        if !raw.bound_vars().is_empty() || !instance.args.is_empty() {
            return Err(
                "primitive table selected Body has unsupported signature parameters".into(),
            );
        }
        let signature = raw.skip_binder();
        if body.arg_count != signature.inputs().len()
            || body
                .local_decls
                .get(rustc_middle::mir::RETURN_PLACE)
                .is_none_or(|local| local.ty != signature.output())
            || body
                .args_iter()
                .zip(signature.inputs())
                .any(|(local, original)| body.local_decls[local].ty != *original)
        {
            return Err("primitive table selected Body argument/Return types differ".into());
        }
        work.charge(body.local_decls.len());
        work.charge(body.basic_blocks.len());
        work.charge(body.source_scopes.len());
        work.charge(body.var_debug_info.len());
        if let Some(error) = work.error.take() {
            return Err(error);
        }
        if body.source.instance != instance.def
            || body.source.promoted.is_some()
            || body.coroutine.is_some()
            || body.tainted_by_errors.is_some()
            || body.spread_arg.is_some()
            || !body.user_type_annotations.is_empty()
            || body.coverage_early_info.is_some()
            || body.coverage_mir_info.is_some()
            || body.required_consts.as_ref().is_some_and(|v| !v.is_empty())
            || body.mentioned_items.as_ref().is_some_and(|v| !v.is_empty())
            || body
                .var_debug_info
                .iter()
                .any(|info| info.composite.is_some())
            || body.local_decls.iter().any(|local| {
                local.user_ty.is_some()
                    || matches!(local.local_info, rustc_middle::mir::ClearCrossCrate::Set(_))
            })
            || body
                .source_scopes
                .iter()
                .any(|scope| scope.inlined.is_some())
        {
            return Err("primitive table selected Body has unsupported metadata".into());
        }
        work.locals = body.local_decls.len();
        for block in body.basic_blocks.iter() {
            work.charge(block.statements.len().saturating_add(1));
            if work.error.is_some() {
                break;
            }
        }
        if work.error.is_none() {
            work.visit_body(body);
        }
        work.error.take().map_or(Ok(()), Err)
    }

    fn primitive_table_target_work(
        &self,
        instance: ty::Instance<'tcx>,
        signature: Ty<'tcx>,
        work: &mut PrimitiveBodyWork<'_, 'tcx>,
    ) -> Result<(), String> {
        if self.primitive_table_signature(signature).is_none()
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
            || !instance.args.is_empty()
        {
            return Err("primitive table target needs a nongeneric named actual Item".into());
        }
        work.charge(
            signature
                .fn_sig(self.tcx)
                .skip_binder()
                .inputs()
                .len()
                .saturating_add(1),
        );
        let raw = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate_identity()
            .skip_norm_wip();
        if raw != signature.fn_sig(self.tcx) {
            return Err("primitive table raw target signature differs".into());
        }
        if !self.tcx.is_mir_available(instance.def_id()) {
            return Err(self.categorized_error(
                UnknownCategory::MissingCompilerEvidence,
                "primitive table selected actual body is unavailable".into(),
            ));
        }
        self.primitive_table_body_work(instance, self.tcx.optimized_mir(instance.def_id()), work)?;
        if let Some(body) = self.bodies.borrow().get(&instance) {
            self.primitive_table_body_work(instance, body, work)?;
        }
        Ok(())
    }

    fn table_signature(&self, callable: Ty<'tcx>) -> bool {
        self.primitive_table_signature(callable).is_some()
            || self
                .integer_table_signature(callable)
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
        if self.primitive_table_signature(*element).is_some() {
            let ty::Array(_, count) = original.kind() else {
                unreachable!();
            };
            if elements.is_empty()
                || elements.len() > MAX_ARRAY_ELEMENTS
                || count.try_to_target_usize(self.tcx) != Some(elements.len() as u64)
            {
                return Err("primitive table source exceeds its bounded original array".into());
            }
        }
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
            && self.primitive_table_signature(*element).is_none()
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
        let mut primitive_work = PrimitiveBodyWork {
            engine: self,
            domain: self.primitive_table_signature(signature).map_or(
                PrimitiveBodyDomain::BoolChar,
                PrimitiveSignature::body_domain,
            ),
            used: 0,
            error: None,
            locals: 0,
        };
        if self.primitive_table_signature(signature).is_some() {
            primitive_work.charge(elements.len());
        }
        for value in elements {
            let Value::FunctionPointer { id } = value else {
                return Err("function table requires initialized known pointer elements".into());
            };
            if self.primitive_table_signature(signature).is_some() {
                let pointers = self.function_pointers.borrow();
                if let Some(Target::Known {
                    instance,
                    signature,
                }) = pointers.get(*id)
                {
                    self.primitive_table_target_work(*instance, *signature, &mut primitive_work)?;
                }
            }
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
                && self.two_argument_integer_signature(signature).is_none()
                && self.primitive_table_signature(signature).is_none())
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
        {
            let pointers = self.function_pointers.borrow();
            if matches!(pointers.get(*id), Some(Target::Choice(_))) {
                state.flow.require_unarmed()?;
            }
            if let Some(Target::Choice(choice)) = pointers.get(*id)
                && (self.primitive_table_signature(choice.signature).is_some()
                    || call
                        .body
                        .local_decls
                        .get(place.local)
                        .is_some_and(|local| self.primitive_table_signature(local.ty).is_some()))
            {
                let original_matches = match choice.original.kind() {
                    ty::Array(element, count) => {
                        *element == choice.signature
                            && count.try_to_target_usize(self.tcx)
                                == Some(choice.targets.len() as u64)
                    }
                    _ => false,
                };
                if !original_matches
                    || choice.targets.is_empty()
                    || choice.targets.len() > MAX_ARRAY_ELEMENTS
                    || call
                        .body
                        .local_decls
                        .get(place.local)
                        .is_none_or(|local| local.ty != choice.signature)
                    || call.args.len() != 1
                {
                    return Err(
                        "primitive table routing Choice differs from bounded actual call".into(),
                    );
                }
                let mut work = PrimitiveBodyWork {
                    engine: self,
                    domain: self
                        .primitive_table_signature(choice.signature)
                        .ok_or("primitive table routing signature is unavailable")?
                        .body_domain(),
                    used: 0,
                    error: None,
                    locals: call.body.local_decls.len(),
                };
                if let Operand::Copy(argument) | Operand::Move(argument) = &call.args[0].node {
                    work.operand_place(call.body, *argument)?;
                } else if let Operand::Constant(constant) = &call.args[0].node {
                    work.visit_const_operand(constant, rustc_middle::mir::Location::START);
                    if let Some(error) = work.error.take() {
                        return Err(error);
                    }
                }
                work.operand_place(call.body, call.destination)?;
            }
        }
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
        if let Some(primitive) = self.primitive_table_signature(callable) {
            return self
                .prepared_primitive_table_call(state, call, &choice, *id, callable, primitive);
        }
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
        self.dispatch_evaluated_table(
            &consumed,
            call,
            &choice,
            instances,
            EvaluatedTableArguments::One(value),
            TableResultSignature::Integer(integer.result),
        )
        .map(Some)
    }

    fn prepared_primitive_table_call(
        &mut self,
        state: &State,
        call: TableCall<'_, 'tcx>,
        choice: &Choice<'tcx>,
        id: usize,
        callable: Ty<'tcx>,
        primitive: PrimitiveSignature<'tcx>,
    ) -> Result<Option<Vec<(State, Return)>>, String> {
        let ty::Array(element, count) = choice.original.kind() else {
            return Err("primitive table lost its original fixed array".into());
        };
        if callable != choice.signature
            || self.tcx.erase_and_anonymize_regions(*element) != callable
            || count.try_to_target_usize(self.tcx) != Some(choice.targets.len() as u64)
            || choice.targets.is_empty()
            || choice.targets.len() > MAX_ARRAY_ELEMENTS
            || !choice.index.belongs_to(&self.terms)
            || choice.index.sort() != &Sort::BitVec(u32::from(self.tcx.sess.target.pointer_width))
            || call.args.len() != 1
            || call.args[0].node.ty(&call.body.local_decls, self.tcx) != primitive.original()
            || call.destination.ty(&call.body.local_decls, self.tcx).ty != primitive.original()
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
        let mut work = PrimitiveBodyWork {
            engine: self,
            domain: primitive.body_domain(),
            used: 0,
            error: None,
            locals: 0,
        };
        work.charge(choice.targets.len());
        for target in &choice.targets {
            let pointers = self.function_pointers.borrow();
            let Some(Target::Known {
                instance,
                signature,
            }) = pointers.get(*target)
            else {
                return Err("primitive table target is not known".into());
            };
            self.primitive_table_target_work(*instance, *signature, &mut work)?;
        }
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
        if !matches!(actual, Value::FunctionPointer { id: actual } if actual == id) {
            return Err("function table actual callable differs from its routing hint".into());
        }
        let value =
            self.evaluate_operand(call.site.0, call.body, &mut consumed, &call.args[0].node)?;
        self.validate_primitive_table_value(&value, primitive, &consumed.conditions)?;
        self.validate_owned_call_arguments(std::slice::from_ref(&value), &consumed.memory)?;
        self.dispatch_evaluated_table(
            &consumed,
            call,
            choice,
            instances,
            EvaluatedTableArguments::One(value),
            TableResultSignature::Primitive(primitive),
        )
        .map(Some)
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
        self.dispatch_evaluated_table(
            &consumed,
            call,
            choice,
            instances,
            EvaluatedTableArguments::Two(values),
            TableResultSignature::Integer(integer.result),
        )
        .map(Some)
    }

    fn dispatch_evaluated_table(
        &mut self,
        consumed: &State,
        call: TableCall<'_, 'tcx>,
        choice: &Choice<'tcx>,
        instances: Vec<ty::Instance<'tcx>>,
        arguments: EvaluatedTableArguments,
        result_signature: TableResultSignature<'tcx>,
    ) -> Result<Vec<(State, Return)>, String> {
        let bits = u32::from(self.tcx.sess.target.pointer_width);
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
            let values = match &arguments {
                EvaluatedTableArguments::One(value) => vec![value.clone()],
                EvaluatedTableArguments::Two(values) => values.clone(),
            };
            for result in self.call_instance(
                instance,
                values,
                conditions,
                branch.memory.clone(),
                call.stack,
                call.site,
            )? {
                match result_signature {
                    TableResultSignature::Integer(signature) => {
                        self.validate_table_result(&result.value, signature)?
                    }
                    TableResultSignature::Primitive(signature) => {
                        // Test faults observe a clone at this actual Return boundary. They do
                        // not mutate the callee Return, its Memory, or production transport.
                        #[cfg(test)]
                        let observed = match signature {
                            PrimitiveSignature::Float32(_) | PrimitiveSignature::Float64(_) => {
                                observed_float_table_return(self, &result.value)
                            }
                            PrimitiveSignature::Bool(_) | PrimitiveSignature::Char(_) => {
                                result.value.clone()
                            }
                        };
                        #[cfg(test)]
                        let value = &observed;
                        #[cfg(not(test))]
                        let value = &result.value;
                        self.validate_primitive_table_value(value, signature, &result.conditions)?;
                    }
                }
                returns.push((branch.clone(), result));
            }
        }
        Ok(returns)
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
