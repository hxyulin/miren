//! Complete compiler array/slice destructor protocol. No general raw slice authority is issued.
use super::*;
use rustc_middle::mir::{BasicBlock, Local, UnwindAction};
use std::rc::Rc;

fn local(place: Place<'_>, index: usize) -> bool {
    place.local.as_usize() == index && place.projection.is_empty()
}
fn moved(operand: &Operand<'_>, index: usize) -> bool {
    matches!(operand, Operand::Move(place) if local(*place, index))
}
fn copied(operand: &Operand<'_>, index: usize) -> bool {
    matches!(operand, Operand::Copy(place) if local(*place, index))
}
fn mutable_reference<'tcx>(ty: Ty<'tcx>, pointee: Ty<'tcx>) -> bool {
    matches!(ty.kind(), ty::Ref(_, original, rustc_hir::Mutability::Mut) if *original == pointee)
}
fn assignment<'a, 'tcx>(
    body: &'a Body<'tcx>,
    block: usize,
    index: usize,
    to: usize,
) -> Result<&'a Rvalue<'tcx>, String> {
    let statement = &body.basic_blocks[BasicBlock::from_usize(block)].statements[index];
    if !statement.debuginfos.is_empty() {
        return Err("array DropGlue statement has additional debug effects".into());
    }
    let StatementKind::Assign(pair) = &statement.kind else {
        return Err("array DropGlue statement is not its complete assignment".into());
    };
    if !local(pair.0, to) {
        return Err("array DropGlue assignment destination differs".into());
    }
    Ok(&pair.1)
}
fn scalar<'tcx>(tcx: TyCtxt<'tcx>, operand: &Operand<'tcx>, expected: u128) -> Result<(), String> {
    let Operand::Constant(value) = operand else {
        return Err("array DropGlue loop constant is not compiler-issued".into());
    };
    if value.const_.ty() != tcx.types.usize
        || value
            .const_
            .try_eval_scalar_int(tcx, ty::TypingEnv::fully_monomorphized())
            .and_then(|v| {
                let width = rustc_abi::Size::from_bits(u64::from(tcx.sess.target.pointer_width));
                (v.size() == width).then(|| v.to_bits(width))
            })
            != Some(expected)
    {
        return Err("array DropGlue loop constant differs from original usize".into());
    }
    Ok(())
}
fn structural(body: &Body<'_>, locals: usize, statements: &[usize]) -> Result<(), String> {
    if body.arg_count != 1
        || !body.return_ty().is_unit()
        || body.local_decls.len() != locals
        || body.basic_blocks.len() != statements.len()
        || body.coroutine.is_some()
        || body.tainted_by_errors.is_some()
        || body.spread_arg.is_some()
    {
        return Err("array DropGlue complete original local/block schema differs".into());
    }
    for (block, count) in body.basic_blocks.iter().zip(statements) {
        if block.is_cleanup
            || block.statements.len() != *count
            || !block.terminator().attributes.is_empty()
        {
            return Err("array DropGlue contains extra operations or cleanup".into());
        }
    }
    Ok(())
}
fn array_schema<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    array: Ty<'tcx>,
    slice: Ty<'tcx>,
    slice_glue: ty::Instance<'tcx>,
) -> Result<(), String> {
    structural(body, 3, &[1, 0])?;
    if !mutable_reference(body.local_decls[Local::from_usize(1)].ty, array)
        || !mutable_reference(body.local_decls[Local::from_usize(2)].ty, slice)
    {
        return Err("array DropGlue argument or slice carrier type differs".into());
    }
    let Rvalue::Cast(
        CastKind::PointerCoercion(
            ty::adjustment::PointerCoercion::Unsize,
            rustc_middle::mir::CoercionSource::Implicit,
        ),
        operand,
        target,
    ) = assignment(body, 0, 0, 2)?
    else {
        return Err("array DropGlue requires its exact Unsize forwarding".into());
    };
    if !moved(operand, 1) || *target != body.local_decls[Local::from_usize(2)].ty {
        return Err("array DropGlue Unsize source or result differs".into());
    }
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        unwind,
        call_source,
        ..
    } = &body.basic_blocks[BasicBlock::from_usize(0)]
        .terminator()
        .kind
    else {
        return Err("array DropGlue requires its exact slice call".into());
    };
    let Operand::Constant(function) = func else {
        return Err("array DropGlue slice callee is not compiler-issued".into());
    };
    let ty::FnDef(id, substitutions) = function.const_.ty().kind() else {
        return Err("array DropGlue slice callee is not an exact function item".into());
    };
    if *id != slice_glue.def_id()
        || substitutions.skip_binder() != slice_glue.args
        || args.len() != 1
        || !moved(&args[0].node, 2)
        || !local(*destination, 0)
        || *target != Some(BasicBlock::from_usize(1))
        || *unwind != UnwindAction::Unreachable
        || *call_source != rustc_middle::mir::CallSource::Misc
        || !matches!(
            body.basic_blocks[BasicBlock::from_usize(1)]
                .terminator()
                .kind,
            TerminatorKind::Return
        )
    {
        return Err("array DropGlue call identity/arguments/targets/normal return differ".into());
    }
    // The queried array element's layout is retained independently of its unsized slice carrier.
    let ty::Array(element, _) = array.kind() else {
        unreachable!()
    };
    tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(*element))
        .map_err(|error| format!("array DropGlue original element layout failed: {error:?}"))?;
    Ok(())
}
fn slice_schema<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    slice: Ty<'tcx>,
    element: Ty<'tcx>,
) -> Result<(), String> {
    structural(body, 8, &[2, 0, 2, 1])?;
    let types = &body.local_decls;
    if !mutable_reference(types[Local::from_usize(1)].ty, slice)
        || types[Local::from_usize(2)].ty != tcx.types.usize
        || types[Local::from_usize(3)].ty != tcx.types.usize
        || types[Local::from_usize(5)].ty != tcx.types.bool
        || types[Local::from_usize(7)].ty != tcx.types.bool
        || ![4, 6].into_iter().all(|index| {
            matches!(types[Local::from_usize(index)].ty.kind(),
            ty::RawPtr(pointee, rustc_hir::Mutability::Mut) if *pointee == element)
        })
    {
        return Err("slice DropGlue exact loop/element local types differ".into());
    }
    if !matches!(assignment(body, 0, 0, 2)?, Rvalue::UnaryOp(UnOp::PtrMetadata, operand)
        if copied(operand, 1))
    {
        return Err("slice DropGlue metadata source differs".into());
    }
    let Rvalue::Use(zero, _) = assignment(body, 0, 1, 3)? else {
        return Err("slice DropGlue initial index differs".into());
    };
    scalar(tcx, zero, 0)?;
    if !matches!(body.basic_blocks[BasicBlock::from_usize(0)].terminator().kind,
        TerminatorKind::Goto { target } if target == BasicBlock::from_usize(3))
        || !matches!(
            body.basic_blocks[BasicBlock::from_usize(1)]
                .terminator()
                .kind,
            TerminatorKind::Return
        )
    {
        return Err("slice DropGlue entry or normal return differs".into());
    }
    let Rvalue::RawPtr(rustc_middle::mir::RawPtrKind::Mut, place) = assignment(body, 2, 0, 6)?
    else {
        return Err("slice DropGlue actual element-address producer differs".into());
    };
    if place.local.as_usize() != 1
        || !matches!(place.projection.as_ref(),
        [ProjectionElem::Deref, ProjectionElem::Index(index)] if index.as_usize() == 3)
    {
        return Err("slice DropGlue element projection differs".into());
    }
    let Rvalue::BinaryOp(BinOp::Add, operands) = assignment(body, 2, 1, 3)? else {
        return Err("slice DropGlue increment operation differs".into());
    };
    if !moved(&operands.0, 3) {
        return Err("slice DropGlue increment source differs".into());
    }
    scalar(tcx, &operands.1, 1)?;
    if !matches!(&body.basic_blocks[BasicBlock::from_usize(2)].terminator().kind,
        TerminatorKind::Drop { place, target, unwind, .. }
        if place.local.as_usize() == 6 && place.projection.as_ref() == [ProjectionElem::Deref]
            && *target == BasicBlock::from_usize(3) && *unwind == UnwindAction::Unreachable)
    {
        return Err("slice DropGlue element Drop or continuation differs".into());
    }
    let Rvalue::BinaryOp(BinOp::Eq, operands) = assignment(body, 3, 0, 7)? else {
        return Err("slice DropGlue loop comparison differs".into());
    };
    if !copied(&operands.0, 3) || !copied(&operands.1, 2) {
        return Err("slice DropGlue loop bounds source differs".into());
    }
    let TerminatorKind::SwitchInt { discr, targets } = &body.basic_blocks
        [BasicBlock::from_usize(3)]
    .terminator()
    .kind
    else {
        return Err("slice DropGlue loop switch differs".into());
    };
    if !moved(discr, 7)
        || targets.iter().collect::<Vec<_>>() != [(0, BasicBlock::from_usize(2))]
        || targets.otherwise() != BasicBlock::from_usize(1)
    {
        return Err("slice DropGlue loop order/exit targets differ".into());
    }
    Ok(())
}

fn source_identity<'tcx>(body: &Body<'tcx>, instance: ty::Instance<'tcx>) -> Result<(), String> {
    if body.source.instance != instance.def || body.source.promoted.is_some() {
        return Err("array DropGlue original/current source Instance differs".into());
    }
    Ok(())
}
fn original_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
) -> Result<Body<'tcx>, String> {
    let raw = tcx.instance_mir(instance.def);
    source_identity(raw, instance)?;
    instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            ty::TypingEnv::fully_monomorphized(),
            ty::EarlyBinder::bind(tcx, raw.clone()),
        )
        .map_err(|error| format!("array DropGlue raw compiler substitution failed: {error:?}"))
}
fn current_operations<'tcx>(original: &Body<'tcx>, current: &Body<'tcx>) -> Result<(), String> {
    if original.span != current.span
        || original.phase != current.phase
        || original.basic_blocks.len() != current.basic_blocks.len()
        || original.local_decls.len() != current.local_decls.len()
        || original
            .local_decls
            .iter()
            .zip(current.local_decls.iter())
            .any(|(a, b)| {
                a.ty != b.ty || a.mutability != b.mutability || a.source_info != b.source_info
            })
    {
        return Err("array DropGlue current compiler phase/types differ from raw".into());
    }
    for (a, b) in original
        .basic_blocks
        .iter()
        .zip(current.basic_blocks.iter())
    {
        if a.is_cleanup != b.is_cleanup
            || a.statements.len() != b.statements.len()
            || a.statements.iter().zip(&b.statements).any(|(a, b)| {
                a.kind != b.kind
                    || a.source_info != b.source_info
                    || !a.debuginfos.is_empty()
                    || !b.debuginfos.is_empty()
            })
            || a.terminator().kind != b.terminator().kind
            || a.terminator().source_info != b.terminator().source_info
        {
            return Err("array DropGlue current operations/source differ from raw".into());
        }
    }
    Ok(())
}
fn validate_protocol<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Body<'tcx>,
    array: Ty<'tcx>,
    slice_glue: ty::Instance<'tcx>,
    slice_body: &Body<'tcx>,
) -> Result<(), String> {
    source_identity(body, instance)?;
    source_identity(slice_body, slice_glue)?;
    let ty::Array(element, _) = array.kind() else {
        return Err("array DropGlue protocol requires an original fixed array".into());
    };
    let slice = Ty::new_slice(tcx, *element);
    if instance != ty::Instance::resolve_drop_glue(tcx, array)
        || slice_glue != ty::Instance::resolve_drop_glue(tcx, slice)
    {
        return Err("array DropGlue original compiler Instance selection differs".into());
    }
    let raw_array = original_body(tcx, instance)?;
    let raw_slice = original_body(tcx, slice_glue)?;
    array_schema(tcx, &raw_array, array, slice, slice_glue)?;
    slice_schema(tcx, &raw_slice, slice, *element)?;
    array_schema(tcx, body, array, slice, slice_glue)?;
    slice_schema(tcx, slice_body, slice, *element)?;
    current_operations(&raw_array, body)?;
    current_operations(&raw_slice, slice_body)?;
    Ok(())
}

pub(super) struct Frame<'tcx> {
    instance: ty::Instance<'tcx>,
    admission: Option<Admission<'tcx>>,
    constructor: Option<array_iterator_constructors::Invocation>,
    step: Option<array_iterator_constructors::steps::Invocation<'tcx>>,
    retained_helper: Option<mutable_reborrows::helpers::Invocation<'tcx>>,
}
struct Admission<'tcx> {
    array: Ty<'tcx>,
    array_instance: ty::Instance<'tcx>,
    array_body: Rc<Body<'tcx>>,
    slice_body: Rc<Body<'tcx>>,
}
impl<'tcx> Frame<'tcx> {
    pub(super) fn original(instance: ty::Instance<'tcx>) -> Self {
        Self {
            instance,
            admission: None,
            constructor: None,
            step: None,
            retained_helper: None,
        }
    }
    pub(super) fn constructor(
        instance: ty::Instance<'tcx>,
        invocation: array_iterator_constructors::Invocation,
    ) -> Self {
        Self {
            instance,
            admission: None,
            constructor: Some(invocation),
            step: None,
            retained_helper: None,
        }
    }
    pub(super) fn step(
        instance: ty::Instance<'tcx>,
        invocation: array_iterator_constructors::steps::Invocation<'tcx>,
    ) -> Self {
        Self {
            instance,
            admission: None,
            constructor: None,
            step: Some(invocation),
            retained_helper: None,
        }
    }
    pub(super) fn retained_helper(
        instance: ty::Instance<'tcx>,
        invocation: mutable_reborrows::helpers::Invocation<'tcx>,
    ) -> Self {
        Self {
            instance,
            admission: None,
            constructor: None,
            step: None,
            retained_helper: Some(invocation),
        }
    }
    pub(super) fn retained_helper_invocation(
        &self,
    ) -> Option<&mutable_reborrows::helpers::Invocation<'tcx>> {
        self.retained_helper.as_ref()
    }
    pub(super) fn step_invocation(
        &self,
    ) -> Option<&array_iterator_constructors::steps::Invocation<'tcx>> {
        self.step.as_ref()
    }
    pub(super) fn constructor_invocation(
        &self,
    ) -> Option<&array_iterator_constructors::Invocation> {
        self.constructor.as_ref()
    }
    pub(super) fn instance(&self) -> ty::Instance<'tcx> {
        self.instance
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn execute_array_drop_glue(
        &mut self,
        frame: &Frame<'tcx>,
        body: &Rc<Body<'tcx>>,
        state: &State,
        stack: &[DefId],
    ) -> Result<Option<(BasicBlock, Vec<State>)>, String> {
        let instance = frame.instance;
        if let Some(admission) = &frame.admission {
            let states =
                self.execute_certified_slice_children(frame, body, state, stack, admission)?;
            return Ok(Some((BasicBlock::from_usize(1), states)));
        }
        let ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, Some(array))) = instance.def else {
            return Ok(None);
        };
        let ty::Array(element, count) = array.kind() else {
            return Ok(None);
        };
        state.flow.require_unarmed()?;
        if instance != ty::Instance::resolve_drop_glue(self.tcx, array)
            || !Rc::ptr_eq(body, &self.instantiated_body(instance)?)
        {
            return Err("array DropGlue requires actual current resolved Instance/Body".into());
        }
        let count = count
            .try_to_target_usize(self.tcx)
            .ok_or("array DropGlue original count is not concrete")?;
        if count > symbolic::MAX_REPEAT_VALUES as u64 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "array DropGlue exceeds 256 original elements".into(),
            ));
        }
        let slice = Ty::new_slice(self.tcx, *element);
        let slice_glue = ty::Instance::resolve_drop_glue(self.tcx, slice);
        let slice_body = self.instantiated_body(slice_glue)?;
        validate_protocol(self.tcx, instance, body, array, slice_glue, &slice_body)?;
        if !self.configured_contracts(slice_glue)?.is_empty()
            || self.specification(slice_glue)?.is_some()
            || self.foreign_rust_target(slice_glue)?.is_some()
        {
            return Err(
                "certified slice DropGlue contract/specification/adapter is unsupported".into(),
            );
        }
        let argument = self.local(state, 1)?;
        self.validate_tracked_value(&argument, state)?;
        let certified = Frame {
            instance: slice_glue,
            constructor: None,
            step: None,
            retained_helper: None,
            admission: Some(Admission {
                array,
                array_instance: instance,
                array_body: body.clone(),
                slice_body,
            }),
        };
        let mut pending = Vec::new();
        for result in self.execute_certified_drop_frame(
            certified,
            vec![argument],
            state.conditions.clone(),
            state.memory.clone(),
            stack,
        )? {
            if pending.len() >= MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "array DropGlue exceeds 512 returned branches".into(),
                ));
            }
            let mut branch =
                self.adopt_flow_return(state, result.conditions, result.memory, result.flow)?;
            branch.locals[1] = None;
            branch
                .constant_receipts
                .invalidate(Place::from(Local::from_usize(1)));
            branch.missing_places.consume(1, Vec::new())?;
            pending.push(branch);
        }
        self.record_model(
            instance.def_id(),
            "complete compiler array/slice DropGlue protocol",
        );
        Ok(Some((BasicBlock::from_usize(1), pending)))
    }

    fn execute_certified_drop_frame(
        &mut self,
        frame: Frame<'tcx>,
        arguments: Vec<Value>,
        conditions: Vec<Term>,
        memory: Memory,
        stack: &[DefId],
    ) -> Result<Vec<Return>, String> {
        let chain = stack
            .iter()
            .copied()
            .chain([frame.instance.def_id()])
            .collect();
        let previous = std::mem::replace(&mut self.call_chain, chain);
        let result = self.execute_body_with_protocol(
            frame,
            arguments,
            conditions,
            memory,
            stack,
            activation_flow::Flow::Unarmed,
        );
        if result.is_err() && self.failed_call_chain.is_none() {
            self.failed_call_chain = Some(self.call_chain.clone());
        }
        self.call_chain = previous;
        result
    }

    fn execute_certified_slice_children(
        &mut self,
        frame: &Frame<'tcx>,
        body: &Rc<Body<'tcx>>,
        state: &State,
        stack: &[DefId],
        admission: &Admission<'tcx>,
    ) -> Result<Vec<State>, String> {
        state.flow.require_unarmed()?;
        let instance = admission.array_instance;
        let array = admission.array;
        let ty::Array(element, count) = array.kind() else {
            return Err("certified slice DropGlue lacks its original fixed array".into());
        };
        let count = count
            .try_to_target_usize(self.tcx)
            .ok_or("certified slice DropGlue count is not concrete")?;
        let slice = Ty::new_slice(self.tcx, *element);
        let slice_glue = ty::Instance::resolve_drop_glue(self.tcx, slice);
        let slice_body = &admission.slice_body;
        if frame.instance != slice_glue
            || !Rc::ptr_eq(body, slice_body)
            || !Rc::ptr_eq(&admission.array_body, &self.instantiated_body(instance)?)
            || !Rc::ptr_eq(slice_body, &self.instantiated_body(slice_glue)?)
        {
            return Err(
                "certified slice DropGlue current Instance/Body association differs".into(),
            );
        }
        validate_protocol(
            self.tcx,
            instance,
            &admission.array_body,
            array,
            slice_glue,
            body,
        )?;
        let argument = self.local(state, 1)?;
        self.validate_tracked_value(&argument, state)?;
        let Value::Reference {
            allocation,
            projection,
            mutable: true,
        } = argument
        else {
            return Err("array DropGlue requires current tracked mutable array argument".into());
        };
        let (root_fields, original) = self
            .typed_memory_evidence(&state.memory, allocation, &projection)?
            .ok_or("array DropGlue requires scoped original array type evidence")?;
        if original != array {
            return Err("array DropGlue original receiver type differs".into());
        }
        state
            .memory
            .missing_places
            .check(allocation, &root_fields)?;
        let value = self.reference_value(
            &Value::Reference {
                allocation,
                projection: projection.clone(),
                mutable: true,
            },
            &state.memory,
            &state.conditions,
        )?;
        let Value::Elements(elements) = value.materialize()? else {
            return Err("array DropGlue requires complete retained original array elements".into());
        };
        if elements.len() as u64 != count || projection.len() >= 16 {
            return Err("array DropGlue original backing count or depth differs".into());
        }
        let mut preflight = state.memory.missing_places.clone();
        for index in 0..count {
            let mut fields = root_fields.clone();
            fields.push(initialized_places::Step::Element(index as usize));
            preflight.consume(allocation, fields)?;
        }
        let mut pending = vec![state.clone()];
        for index in 0..count {
            let mut next = Vec::new();
            for branch in pending {
                self.steps = self.steps.checked_add(2).ok_or_else(|| {
                    self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "array DropGlue execution step count overflow".into(),
                    )
                })?;
                if self.steps > self.limits.max_steps {
                    return Err(self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "array DropGlue shared execution step limit reached".into(),
                    ));
                }
                if !Rc::ptr_eq(&admission.array_body, &self.instantiated_body(instance)?)
                    || !Rc::ptr_eq(slice_body, &self.instantiated_body(slice_glue)?)
                {
                    return Err("array DropGlue current compiler bodies changed".into());
                }
                let mut path = projection.clone();
                path.push(symbolic::MemoryProjection::Index(Box::new(
                    self.iterator_index(u128::from(index)),
                )));
                let (fields, original) = self
                    .typed_memory_evidence(&branch.memory, allocation, &path)?
                    .ok_or("array DropGlue child original evidence unavailable")?;
                if original != *element {
                    return Err("array DropGlue child original type differs".into());
                }
                branch.memory.missing_places.check(allocation, &fields)?;
                let child = Value::Reference {
                    allocation,
                    projection: path,
                    mutable: true,
                };
                self.validate_tracked_value(&child, &branch)?;
                for result in self.call_instance(
                    ty::Instance::resolve_drop_glue(self.tcx, *element),
                    vec![child],
                    branch.conditions.clone(),
                    branch.memory.clone(),
                    stack,
                    (instance.def_id(), slice_body.span),
                )? {
                    if next.len() >= MAX_INPUT_VALUES {
                        return Err(self.categorized_error(
                            UnknownCategory::ResourceLimit,
                            "array DropGlue exceeds 512 returned branches".into(),
                        ));
                    }
                    let mut continuation = self.adopt_flow_return(
                        &branch,
                        result.conditions,
                        result.memory,
                        result.flow,
                    )?;
                    let (_, current) = self
                        .typed_memory_evidence(&continuation.memory, allocation, &projection)?
                        .ok_or("array DropGlue returned original owner evidence unavailable")?;
                    if current != array {
                        return Err("array DropGlue returned original owner type differs".into());
                    }
                    continuation
                        .memory
                        .missing_places
                        .descendants(allocation, &fields)?;
                    continuation
                        .memory
                        .missing_places
                        .consume(allocation, fields.clone())?;
                    next.push(continuation);
                }
            }
            pending = next;
        }
        for _ in &pending {
            self.steps = self.steps.checked_add(1).ok_or_else(|| {
                self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "array DropGlue execution step count overflow".into(),
                )
            })?;
            if self.steps > self.limits.max_steps {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "array DropGlue shared execution step limit reached".into(),
                ));
            }
        }
        Ok(pending)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn compiler_controls<'tcx>(tcx: TyCtxt<'tcx>) {
        let id = |name: &str| {
            tcx.mir_keys(())
                .iter()
                .copied()
                .find(|id| {
                    tcx.def_kind(id.to_def_id()) == DefKind::Fn
                        && tcx.item_name(id.to_def_id()).as_str() == name
                })
                .unwrap()
                .to_def_id()
        };
        let config = miren::ContractConfig::default();
        let options = || VerificationOptions {
            all_failures: false,
            induction: false,
            startup: false,
            isolated_startup: false,
            async_entry: false,
            limits: miren::AnalysisLimits::default(),
        };
        let mut engine = Engine::new(tcx, &config, options());
        let helper = engine
            .resolve_function_item(id("covering"), ty::GenericArgs::empty())
            .unwrap();
        let helper_body = engine.instantiated_body(helper).unwrap();
        let array = helper_body
            .local_decls
            .iter()
            .find_map(|decl| matches!(decl.ty.kind(), ty::Array(..)).then_some(decl.ty))
            .unwrap();
        let ty::Array(element, _) = array.kind() else {
            panic!("actual array")
        };
        let slice = Ty::new_slice(tcx, *element);
        let array_glue = ty::Instance::resolve_drop_glue(tcx, array);
        let slice_glue = ty::Instance::resolve_drop_glue(tcx, slice);
        let body = engine.instantiated_body(array_glue).unwrap();
        let sliced = engine.instantiated_body(slice_glue).unwrap();
        validate_protocol(tcx, array_glue, &body, array, slice_glue, &sliced).unwrap();
        let mut changed = body.as_ref().clone();
        changed.source.instance = slice_glue.def;
        assert_eq!(
            validate_protocol(tcx, array_glue, &changed, array, slice_glue, &sliced).unwrap_err(),
            "array DropGlue original/current source Instance differs"
        );
        changed = body.as_ref().clone();
        changed.source.promoted = Some(rustc_middle::mir::Promoted::from_usize(0));
        assert_eq!(
            validate_protocol(tcx, array_glue, &changed, array, slice_glue, &sliced).unwrap_err(),
            "array DropGlue original/current source Instance differs"
        );
        changed = body.as_ref().clone();
        changed.arg_count = 0;
        assert_eq!(
            array_schema(tcx, &changed, array, slice, slice_glue).unwrap_err(),
            "array DropGlue complete original local/block schema differs"
        );
        changed = body.as_ref().clone();
        changed.basic_blocks.as_mut()[BasicBlock::from_usize(0)].is_cleanup = true;
        assert_eq!(
            array_schema(tcx, &changed, array, slice, slice_glue).unwrap_err(),
            "array DropGlue contains extra operations or cleanup"
        );
        changed = body.as_ref().clone();
        changed.local_decls[Local::from_usize(1)].ty = tcx.types.u32;
        assert_eq!(
            array_schema(tcx, &changed, array, slice, slice_glue).unwrap_err(),
            "array DropGlue argument or slice carrier type differs"
        );
        changed = body.as_ref().clone();
        changed.basic_blocks.as_mut()[BasicBlock::from_usize(0)].statements[0].kind =
            StatementKind::Nop;
        assert_eq!(
            array_schema(tcx, &changed, array, slice, slice_glue).unwrap_err(),
            "array DropGlue statement is not its complete assignment"
        );
        changed = body.as_ref().clone();
        changed.basic_blocks.as_mut()[BasicBlock::from_usize(1)]
            .terminator_mut()
            .kind = TerminatorKind::Unreachable;
        assert_eq!(
            array_schema(tcx, &changed, array, slice, slice_glue).unwrap_err(),
            "array DropGlue call identity/arguments/targets/normal return differ"
        );
        let mut bad_slice = sliced.as_ref().clone();
        bad_slice.local_decls[Local::from_usize(7)].ty = tcx.types.u16;
        assert_eq!(
            slice_schema(tcx, &bad_slice, slice, *element).unwrap_err(),
            "slice DropGlue exact loop/element local types differ"
        );
        bad_slice = sliced.as_ref().clone();
        bad_slice.basic_blocks.as_mut()[BasicBlock::from_usize(3)]
            .terminator_mut()
            .kind = TerminatorKind::Unreachable;
        assert_eq!(
            slice_schema(tcx, &bad_slice, slice, *element).unwrap_err(),
            "slice DropGlue loop switch differs"
        );
        bad_slice = sliced.as_ref().clone();
        bad_slice.basic_blocks.as_mut()[BasicBlock::from_usize(2)].statements[1].kind =
            StatementKind::Nop;
        assert_eq!(
            slice_schema(tcx, &bad_slice, slice, *element).unwrap_err(),
            "array DropGlue statement is not its complete assignment"
        );
        bad_slice = sliced.as_ref().clone();
        if let TerminatorKind::Drop { unwind, .. } = &mut bad_slice.basic_blocks.as_mut()
            [BasicBlock::from_usize(2)]
        .terminator_mut()
        .kind
        {
            *unwind = UnwindAction::Continue;
        } else {
            panic!("actual compiler element Drop")
        }
        assert_eq!(
            slice_schema(tcx, &bad_slice, slice, *element).unwrap_err(),
            "slice DropGlue element Drop or continuation differs"
        );
        // Same-operation wrong source in an Engine cache is rejected independently of Rc identity.
        changed = body.as_ref().clone();
        changed.source.instance = slice_glue.def;
        engine
            .bodies
            .borrow_mut()
            .insert(array_glue, Rc::new(changed.clone()));
        assert_eq!(
            validate_protocol(
                tcx,
                array_glue,
                &engine.instantiated_body(array_glue).unwrap(),
                array,
                slice_glue,
                &sliced
            )
            .unwrap_err(),
            "array DropGlue original/current source Instance differs"
        );
        engine.bodies.borrow_mut().insert(array_glue, body.clone());
        changed = body.as_ref().clone();
        if let TerminatorKind::Call { target, .. } = &mut changed.basic_blocks.as_mut()
            [BasicBlock::from_usize(0)]
        .terminator_mut()
        .kind
        {
            *target = Some(BasicBlock::from_usize(0));
        } else {
            panic!("actual array call")
        }
        assert_eq!(
            array_schema(tcx, &changed, array, slice, slice_glue).unwrap_err(),
            "array DropGlue call identity/arguments/targets/normal return differ"
        );
        let mut tagged = sliced.as_ref().clone();
        if let StatementKind::Assign(pair) =
            &mut tagged.basic_blocks.as_mut()[BasicBlock::from_usize(0)].statements[1].kind
        {
            if let Rvalue::Use(_, retag) = &mut pair.1 {
                *retag = match *retag {
                    rustc_middle::mir::WithRetag::Yes => rustc_middle::mir::WithRetag::No,
                    rustc_middle::mir::WithRetag::No => rustc_middle::mir::WithRetag::Yes,
                };
            } else {
                panic!("actual index constant")
            }
        } else {
            panic!("actual assignment")
        }
        assert_ne!(
            sliced.basic_blocks[BasicBlock::from_usize(0)].statements[1].kind,
            tagged.basic_blocks[BasicBlock::from_usize(0)].statements[1].kind
        );
        assert_eq!(
            current_operations(&sliced, &tagged).unwrap_err(),
            "array DropGlue current operations/source differ from raw"
        );
        let zero = Ty::new_array(tcx, *element, 0);
        let zero_glue = ty::Instance::resolve_drop_glue(tcx, zero);
        assert!(matches!(
            zero_glue.def,
            ty::InstanceKind::Shim(ty::ShimKind::DropGlue(_, None))
        ));
        source_identity(&engine.instantiated_body(zero_glue).unwrap(), zero_glue).unwrap();
        let large = Ty::new_array(tcx, *element, 257);
        let large_glue = ty::Instance::resolve_drop_glue(tcx, large);
        let large_body = engine.instantiated_body(large_glue).unwrap();
        let empty = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; large_body.local_decls.len()],
            constant_receipts: constant_reference_receipts::Slots::default(),
            missing_places: initialized_places::MissingPlaces::default(),
            addresses: vec![None; large_body.local_decls.len()],
            conditions: Vec::new(),
            memory: Memory::default(),
        };
        assert_eq!(
            engine
                .execute_array_drop_glue(&Frame::original(large_glue), &large_body, &empty, &[])
                .err()
                .unwrap(),
            "array DropGlue exceeds 256 original elements"
        );
        assert_eq!(
            engine
                .unknown_causes
                .borrow()
                .get("array DropGlue exceeds 256 original elements"),
            Some(&UnknownCategory::ResourceLimit)
        );
        let owner_id = id("owner_probe");
        let owner_instance = engine
            .resolve_function_item(owner_id, ty::GenericArgs::empty())
            .unwrap();
        let owner_body = engine.instantiated_body(owner_instance).unwrap();
        let root = Place::from(Local::from_usize(1));
        let original = owner_body.local_decls[root.local].ty;
        let mut conditions = Vec::new();
        let value = engine
            .argument(owner_id, original, &mut conditions)
            .unwrap();
        let mut state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; owner_body.local_decls.len()],
            constant_receipts: constant_reference_receipts::Slots::default(),
            addresses: vec![None; owner_body.local_decls.len()],
            conditions,
            memory: Memory::default(),
            missing_places: initialized_places::MissingPlaces::default(),
        };
        state.locals[1] = Some(value);
        let reference = engine
            .borrow_typed(&owner_body, &mut state, root, true)
            .unwrap();
        let Value::Reference {
            allocation,
            projection,
            ..
        } = reference
        else {
            panic!("actual typed whole-array borrower")
        };
        assert_eq!(
            engine
                .typed_memory_evidence(&state.memory, allocation, &projection)
                .unwrap()
                .unwrap()
                .1,
            original
        );
        let foreign = Engine::new(tcx, &config, options());
        assert_eq!(
            foreign
                .typed_memory_evidence(&state.memory, allocation, &projection)
                .unwrap_err(),
            "ownership initialization type belongs to a foreign engine"
        );
        let mut consumed = state.clone();
        consumed
            .memory
            .missing_places
            .consume(allocation, Vec::new())
            .unwrap();
        assert_eq!(
            engine
                .check_memory_initialization(&consumed.memory, allocation, &projection)
                .unwrap_err(),
            "place initialization is unavailable after ownership consumption"
        );
        let mut retired = state.clone();
        retired.memory.retire_initialized_owner(allocation);
        retired.memory[allocation] = None;
        assert_eq!(
            engine
                .typed_memory_evidence(&retired.memory, allocation, &projection)
                .unwrap_err(),
            "ownership initialization type belongs to retired allocation"
        );
        println!("array DropGlue raw/current schema and whole-owner controls complete");
    }

    #[test]
    fn actual_compiler_array_slice_glue_rejects_schema_source_and_owner_mutations() {
        struct Check(bool);
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                compiler_controls(tcx);
                self.0 = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory = std::env::temp_dir().join(format!(
            "miren-array-glue-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("drop.rs");
        std::fs::write(
            &source,
            include_str!("../../../../tests/fixtures/partial_array_drops.rs"),
        )
        .unwrap();
        let args = vec![
            "rustc".into(),
            source.to_str().unwrap().into(),
            "--crate-type=lib".into(),
            "--edition=2024".into(),
            "-Cpanic=abort".into(),
            "-Copt-level=0".into(),
            "--out-dir".into(),
            directory.to_str().unwrap().into(),
            "--sysroot".into(),
            env!("MIREN_SYSROOT").into(),
        ];
        let mut callback = Check(false);
        rustc_driver::run_compiler(&args, &mut callback);
        assert!(callback.0);
        std::fs::remove_dir_all(directory).unwrap();
    }
}
