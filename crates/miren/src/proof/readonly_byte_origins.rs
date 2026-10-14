//! Current safe-origin observations only, never permission for a raw read or derived reference.
use super::*;
use rustc_middle::mir::BasicBlock;
use std::rc::Rc;

pub(super) struct CallOccurrence<'a, 'tcx> {
    caller: ty::Instance<'tcx>,
    body: &'a Rc<Body<'tcx>>,
    block: BasicBlock,
    evaluated: &'a [Value],
    receipts: Option<(
        &'a constant_reference_receipts::Registry<'tcx>,
        &'a [Option<constant_reference_receipts::Key>],
    )>,
}

impl<'a, 'tcx> CallOccurrence<'a, 'tcx> {
    pub(super) fn new(
        caller: ty::Instance<'tcx>,
        body: &'a Rc<Body<'tcx>>,
        block: BasicBlock,
        evaluated: &'a [Value],
    ) -> Self {
        Self {
            caller,
            body,
            block,
            evaluated,
            receipts: None,
        }
    }

    pub(super) fn with_receipts(
        mut self,
        registry: &'a constant_reference_receipts::Registry<'tcx>,
        arguments: &'a [Option<constant_reference_receipts::Key>],
    ) -> Self {
        self.receipts = if arguments.is_empty() {
            None
        } else {
            Some((registry, arguments))
        };
        self
    }

    pub(super) fn site(&self) -> Result<(DefId, Span), String> {
        let block = self
            .body
            .basic_blocks
            .get(self.block)
            .ok_or("readonly byte origin call block is outside its current Body")?;
        Ok((self.caller.def_id(), block.terminator().source_info.span))
    }
}

pub(super) struct NeedleState<'a> {
    pub(super) needle: &'a Value,
    pub(super) state: &'a State,
}

pub(super) struct Inputs<'a, 'tcx> {
    pub(super) selected: ty::Instance<'tcx>,
    pub(super) slice_first: bool,
    pub(super) raw: &'a [Value],
    pub(super) slice: &'a Value,
    pub(super) needle: &'a Value,
}

// Immutable operation identity only. Preparing sources may publish caches, so this carries no
// live source read guard and no storage permit. Original source/storage is authenticated later.
pub(super) struct RouteScope<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    original: Ty<'tcx>,
    call: &'a CallOccurrence<'a, 'tcx>,
    inputs: &'a Inputs<'a, 'tcx>,
    state: &'a State,
    used: usize,
}

impl<'a, 'tcx> RouteScope<'a, 'tcx> {
    pub(super) fn new(
        engine: &'a Engine<'tcx>,
        original: Ty<'tcx>,
        call: &'a CallOccurrence<'a, 'tcx>,
        inputs: &'a Inputs<'a, 'tcx>,
        state: &'a State,
    ) -> Result<Self, String> {
        let mut work = nonzero_niches::ByteWork::new(0)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        work.charge(13)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        Ok(Self {
            engine,
            original,
            call,
            inputs,
            state,
            used: work.used(),
        })
    }
    pub(super) fn request(
        &self,
        engine: &Engine<'tcx>,
    ) -> Result<(Ty<'tcx>, ty::Instance<'tcx>, usize), String> {
        if !std::ptr::eq(self.engine, engine) || !std::ptr::eq(self.call.evaluated, self.inputs.raw)
        {
            return Err("byte route request has a foreign Engine or raw operand occurrence".into());
        }
        Ok((self.original, self.inputs.selected, self.used))
    }
}

// This borrow has invocation scope, not Rust raw-access authority. There is no issuance or escape
// API; current storage and original typed operands are observed without authenticating helpers.
pub(super) struct Origin<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    call: &'a CallOccurrence<'a, 'tcx>,
    state: &'a State,
    inputs: &'a Inputs<'a, 'tcx>,
    original: Ty<'tcx>,
    source_scope: rustc_middle::mir::SourceScope,
    slice_allocation: usize,
    needle_allocation: usize,
    offset: Term,
    capacity: Term,
    caller_source: nonzero_niches::CallerSource<'a, 'tcx>,
    source_work: Option<nonzero_niches::ByteWork>,
}

fn usize_term(engine: &Engine<'_>, value: &Value) -> Result<Term, String> {
    let (term, bits, signed) = value.integer()?;
    if signed
        || bits != u32::from(engine.tcx.sess.target.pointer_width)
        || term.sort() != &Sort::BitVec(bits)
        || !term.belongs_to(&engine.terms)
    {
        return Err("readonly byte origin extent has a different target width or Context".into());
    }
    Ok(term)
}

fn readonly_reference(value: &Value) -> Result<(usize, &[symbolic::MemoryProjection]), String> {
    let Value::Reference {
        allocation,
        projection,
        mutable: false,
    } = value
    else {
        return Err("readonly byte origin requires a live shared Rust reference".into());
    };
    if projection.len() > MAX_INPUT_DEPTH {
        return Err("readonly byte origin projection exceeds the existing depth16 limit".into());
    }
    Ok((*allocation, projection))
}

fn same_slice(engine: &Engine<'_>, left: &Value, right: &Value) -> Result<(), String> {
    let (
        Value::CompositeSlice {
            id: a,
            length: x,
            leaves: first,
        },
        Value::CompositeSlice {
            id: b,
            length: y,
            leaves: second,
        },
    ) = (left, right)
    else {
        return Err("readonly byte origin lacks its current initialized niche slice".into());
    };
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    let [column] = first.as_slice() else {
        return Err("readonly byte origin requires exactly one byte column".into());
    };
    if a != b
        || usize_term(engine, x)? != usize_term(engine, y)?
        || first != second
        || column.sort() != &Sort::Array(Box::new(Sort::BitVec(bits)), Box::new(Sort::BitVec(8)))
        || !column.belongs_to(&engine.terms)
    {
        return Err(
            "readonly byte origin snapshot differs from its current storage or Context".into(),
        );
    }
    Ok(())
}

// Exact current carrier comparison, not a raw encoding or proof of latent NonZero validity.
fn same_needle<'tcx>(
    engine: &Engine<'tcx>,
    original: Ty<'tcx>,
    left: &Value,
    right: &Value,
    depth: usize,
    fields: &nonzero_niches::ByteNeedleFields<'tcx>,
    work: &mut nonzero_niches::ByteWork,
) -> Result<(), String> {
    work.charge(2)
        .map_err(|error| engine.categorized_error(error.category, error.reason))?;
    if depth >= MAX_INPUT_DEPTH {
        return Err("readonly byte origin needle exceeds the existing depth16 limit".into());
    }
    if original == engine.tcx.types.u8 {
        let (a, width, sign) = left.integer()?;
        let (b, other, signed) = right.integer()?;
        if width == 8
            && other == 8
            && !sign
            && !signed
            && a == b
            && a.sort() == &Sort::BitVec(8)
            && a.belongs_to(&engine.terms)
        {
            return Ok(());
        }
        return Err("readonly byte origin needle byte differs or has a foreign Context".into());
    }
    let ty::Adt(def, args) = original.kind() else {
        return Err("readonly byte origin needle lacks its original compiler ADT".into());
    };
    let option = engine.tcx.lang_items().get(LangItem::Option) == Some(def.did());
    if let (
        Value::Enum {
            discriminant: a,
            variants: first,
            is_option: true,
        },
        Value::Enum {
            discriminant: b,
            variants: second,
            is_option: true,
        },
    ) = (left, right)
    {
        let (a, bits, signed) = a.integer()?;
        let (b, other, sign) = b.integer()?;
        if !option
            || first.len() != 2
            || second.len() != 2
            || bits != u32::from(engine.tcx.sess.target.pointer_width)
            || other != bits
            || !signed
            || !sign
            || a != b
            || a.sort() != &Sort::BitVec(bits)
            || !a.belongs_to(&engine.terms)
        {
            return Err("readonly byte origin needle tag or Context differs".into());
        }
        for (a, b) in first.iter().zip(second) {
            same_needle(engine, original, a, b, depth + 1, fields, work)?;
        }
        return Ok(());
    }
    let (
        Value::Adt {
            name: a,
            variant: x,
            is_option: p,
            discriminant: i,
            fields: first,
        },
        Value::Adt {
            name: b,
            variant: y,
            is_option: q,
            discriminant: j,
            fields: second,
        },
    ) = (left, right)
    else {
        return Err(
            "readonly byte origin needle carrier differs from its typed current storage".into(),
        );
    };
    if *x >= def.variants().len() {
        return Err("readonly byte origin needle variant is outside its original ADT".into());
    }
    let variant_index = rustc_abi::VariantIdx::from_usize(*x);
    let variant = &def.variants()[variant_index];
    let discriminant = if def.is_enum() {
        def.discriminant_for_variant(engine.tcx, variant_index).val
    } else {
        0
    };
    if a != b
        || a != &engine.tcx.def_path_str(def.did())
        || x != y
        || *p != option
        || p != q
        || i != j
        || *i != discriminant
        || first.len() != variant.fields.len()
        || second.len() != first.len()
    {
        return Err(
            "readonly byte origin needle original fields or variant metadata differ".into(),
        );
    }
    for (index, ((a, left), ((b, right), field))) in first
        .iter()
        .zip(second.iter().zip(&variant.fields))
        .enumerate()
    {
        if a != b || a != field.name.as_str() {
            return Err("readonly byte origin needle original FieldTy/name differs".into());
        }
        work.charge(4)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        let original_field = field.ty(engine.tcx, args).skip_norm_wip();
        let bound = fields.field(original, index, original_field)?;
        same_needle(engine, bound, left, right, depth + 1, fields, work)?;
    }
    Ok(())
}

fn current_call<'a, 'tcx>(
    engine: &Engine<'tcx>,
    call: &'a CallOccurrence<'_, 'tcx>,
    selected: ty::Instance<'tcx>,
) -> Result<&'a [rustc_span::Spanned<Operand<'tcx>>], String> {
    if !matches!(call.caller.def, ty::InstanceKind::Item(_))
        || !engine
            .bodies
            .borrow()
            .get(&call.caller)
            .is_some_and(|body| Rc::ptr_eq(body, call.body))
    {
        return Err(
            "readonly byte origin current caller Body/Instance was replaced or unavailable".into(),
        );
    }
    let signature = engine.call_signature(call.caller)?;
    if signature.safety() != rustc_hir::Safety::Safe
        || signature.abi() != rustc_abi::ExternAbi::Rust
        || signature.c_variadic()
    {
        return Err("readonly byte origin requires an actual safe Rust caller".into());
    }
    let block = call
        .body
        .basic_blocks
        .get(call.block)
        .ok_or("readonly byte origin call block is outside its current Body")?;
    if call
        .body
        .source_scopes
        .get(block.terminator().source_info.scope)
        .is_none()
    {
        return Err("readonly byte origin Call has no current Body source scope".into());
    }
    let TerminatorKind::Call {
        func,
        args,
        target: Some(_),
        ..
    } = &block.terminator().kind
    else {
        return Err("readonly byte origin requires its current direct Call occurrence".into());
    };
    let ty::FnDef(id, arguments) = func.ty(&call.body.local_decls, engine.tcx).kind() else {
        return Err("readonly byte origin has no original FnDef operand".into());
    };
    if !arguments.bound_vars().is_empty()
        || engine.resolve_function_item(*id, arguments.skip_binder())? != selected
    {
        return Err(
            "readonly byte origin selected Instance differs from its genuine operand".into(),
        );
    }
    Ok(args)
}

#[cfg(test)]
pub(super) fn observe<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    call: &'a CallOccurrence<'a, 'tcx>,
    inputs: &'a Inputs<'a, 'tcx>,
    state: &'a State,
) -> Result<Origin<'a, 'tcx>, String> {
    observe_with_work(engine, call, inputs, state, 0)
}

pub(super) fn observe_with_work<'a, 'tcx>(
    engine: &'a Engine<'tcx>,
    call: &'a CallOccurrence<'a, 'tcx>,
    inputs: &'a Inputs<'a, 'tcx>,
    state: &'a State,
    prior: usize,
) -> Result<Origin<'a, 'tcx>, String> {
    state.flow.require_unarmed()?;
    let mut source_work = nonzero_niches::ByteWork::new(prior)
        .map_err(|error| engine.categorized_error(error.category, error.reason))?;
    let caller_source =
        nonzero_niches::caller_source(engine, call.caller, call.body, &mut source_work)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
    let args = current_call(engine, call, inputs.selected)?;
    if !std::ptr::eq(call.evaluated, inputs.raw) {
        return Err(
            "readonly byte origin lost its evaluated raw-argument occurrence witness".into(),
        );
    }
    let [first, second] = inputs.raw else {
        return Err("readonly byte origin requires two actual reference arguments".into());
    };
    if args.len() != 2 {
        return Err("readonly byte origin original Call arity differs".into());
    }
    let (source, needle, source_arg, needle_arg) = if inputs.slice_first {
        (first, second, &args[0].node, &args[1].node)
    } else {
        (second, first, &args[1].node, &args[0].node)
    };
    let ty::Ref(_, slice_ty, rustc_hir::Mutability::Not) =
        source_arg.ty(&call.body.local_decls, engine.tcx).kind()
    else {
        return Err("readonly byte origin source operand has no original shared slice type".into());
    };
    let ty::Slice(original) = slice_ty.kind() else {
        return Err("readonly byte origin original operand is not a Rust slice".into());
    };
    if !matches!(needle_arg.ty(&call.body.local_decls, engine.tcx).kind(),
        ty::Ref(_, ty, rustc_hir::Mutability::Not) if ty == original)
        || !matches!(original.kind(), ty::Adt(def, option)
            if engine.tcx.lang_items().get(LangItem::Option) == Some(def.did())
                && option.len() == 1 && matches!(option.type_at(0).kind(), ty::Adt(nonzero, inner)
                    if engine.tcx.is_diagnostic_item(rustc_span::Symbol::intern("NonZero"),
                        nonzero.did()) && inner.len() == 1
                        && inner.type_at(0) == engine.tcx.types.u8))
    {
        return Err("readonly byte origin requires exact shared Option<NonZeroU8> operands".into());
    }
    let env = ty::TypingEnv::fully_monomorphized();
    if !original.is_freeze(engine.tcx, env)
        || !engine.tcx.type_is_copy_modulo_regions(env, *original)
        || original.needs_drop(engine.tcx, env)
    {
        return Err("readonly byte origin original Rust storage policy differs".into());
    }
    let schema = engine.niche_membership_descriptor(*original, inputs.slice)?;
    let layout = engine.static_layout(*original)?;
    if schema.payload_bits() != 8
        || schema.item_bytes() != 1
        || layout.size.bytes() != 1
        || layout.align.abi.bytes() != 1
    {
        return Err("readonly byte origin original niche layout differs".into());
    }
    for (arg, value) in [(source_arg, source), (needle_arg, needle)] {
        engine.validate_tracked_value(value, state)?;
        engine.validate_readonly_slice_value(
            arg.ty(&call.body.local_decls, engine.tcx),
            value,
            &state.memory,
            &state.conditions,
        )?;
    }
    if let Some((registry, keys)) = call.receipts {
        if keys.len() != args.len() {
            return Err("compiler constant receipt argument occurrence arity differs".into());
        }
        let needle_index = if inputs.slice_first { 1 } else { 0 };
        if let Some(key) = &keys[needle_index] {
            registry.validate_argument(
                engine,
                call.body,
                key,
                needle_arg.ty(&call.body.local_decls, engine.tcx),
            )?;
        }
        // Compiler storage observations do not replace the live-reference requirement below.
    }
    let (slice_allocation, projection) = readonly_reference(source)?;
    let (needle_allocation, needle_projection) = readonly_reference(needle)?;
    if !needle_projection.is_empty() {
        return Err("readonly byte origin needle subobject transport remains unsupported".into());
    }
    let stored =
        storage_locations::StorageLocation::tracked(slice_allocation, false).read(&state.memory)?;
    engine.niche_membership_descriptor(*original, stored)?;
    same_slice(engine, stored, stored)?;
    let Value::CompositeSlice { length, .. } = stored else {
        return Err(
            "readonly byte origin source has no current initialized slice allocation".into(),
        );
    };
    let capacity = usize_term(engine, length)?;
    for condition in &state.conditions {
        if condition.sort() != &Sort::Bool || !condition.belongs_to(&engine.terms) {
            return Err("readonly byte origin path condition has a foreign Context".into());
        }
    }
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    if !matches!(bits, 32 | 64) {
        return Err("readonly byte origin requires a supported target index width".into());
    }
    let outside = engine.terms.apply(
        Op::BvUnsignedGt,
        &[
            capacity.clone(),
            engine.terms.bit_vector((1u128 << (bits - 1)) - 1, bits)?,
        ],
    )?;
    let mut conditions = state.conditions.clone();
    conditions.push(outside);
    if engine.feasible(&conditions)? {
        return Err("readonly byte origin lacks its original isize allocation extent".into());
    }
    // Only the already checked one-column descriptor is cloned for safe projected observations.
    let mut current = stored.clone();
    let mut offset = engine
        .terms
        .bit_vector(0, u32::from(engine.tcx.sess.target.pointer_width))?;
    for step in projection {
        let symbolic::MemoryProjection::Slice {
            offset: part,
            length,
        } = step
        else {
            return Err("readonly byte origin supports only safe slice projections".into());
        };
        usize_term(engine, length)?;
        let part = usize_term(engine, part)?;
        current = engine.memory_projection(current, step, &state.conditions)?;
        offset = engine.terms.apply(Op::BvAdd, &[offset, part])?;
    }
    same_slice(engine, &current, inputs.slice)?;
    let current = storage_locations::StorageLocation::tracked(needle_allocation, false)
        .read(&state.memory)?;
    let needle_fields = engine.byte_needle_fields(*original, &mut source_work)?;
    same_needle(
        engine,
        *original,
        current,
        inputs.needle,
        0,
        &needle_fields,
        &mut source_work,
    )?;
    Ok(Origin {
        engine,
        call,
        state,
        inputs,
        original: *original,
        source_scope: call.body.basic_blocks[call.block]
            .terminator()
            .source_info
            .scope,
        slice_allocation,
        needle_allocation,
        offset,
        capacity,
        caller_source,
        source_work: Some(source_work),
    })
}

impl<'tcx> Origin<'_, 'tcx> {
    pub(super) fn validate_current(
        &self,
        engine: &Engine<'tcx>,
        call: &CallOccurrence<'_, 'tcx>,
        state: &State,
    ) -> Result<(), String> {
        if !std::ptr::eq(self.engine, engine)
            || !std::ptr::eq(self.call, call)
            || !std::ptr::eq(self.state, state)
        {
            return Err(
                "readonly byte origin belongs to another invocation/Engine/Memory scope".into(),
            );
        }
        current_call(engine, call, self.inputs.selected)?;
        if call.body.basic_blocks[call.block]
            .terminator()
            .source_info
            .scope
            != self.source_scope
        {
            return Err("readonly byte origin current Body source scope differs".into());
        }
        engine.niche_membership_descriptor(self.original, self.inputs.slice)?;
        storage_locations::StorageLocation::tracked(self.slice_allocation, false)
            .read(&state.memory)?;
        storage_locations::StorageLocation::tracked(self.needle_allocation, false)
            .read(&state.memory)?;
        if !self.offset.belongs_to(&engine.terms) || !self.capacity.belongs_to(&engine.terms) {
            return Err("readonly byte origin offset/extent Context differs".into());
        }
        // No operation here authenticates the helper's no-write path or issues raw-access rights.
        Ok(())
    }
}

// A live safe-origin/encoding relation, not a transport theorem or a raw-access permit.
// The original borrowed occurrence, input values and State cannot be replaced during this service.
pub(super) struct Relation<'a, 'tcx> {
    origin: Origin<'a, 'tcx>,
    length: Term,
    encoding: Term,
    work: nonzero_niches::ByteWork,
}

impl<'a, 'tcx> Origin<'a, 'tcx> {
    pub(super) fn relation(mut self) -> Result<Relation<'a, 'tcx>, String> {
        let engine = self.engine;
        let mut work = self
            .source_work
            .take()
            .ok_or("byte origin caller source work was already consumed")?;
        // Retain the previous relation initialization fee and pay the actual Option handoff.
        work.charge(3 + 2)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        self.caller_source
            .check(engine, self.call.caller, self.call.body, &mut work)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        // Hold the actual current caller cache guard through all live relation observations.
        work.charge(4)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        let bodies = engine
            .bodies
            .try_borrow()
            .map_err(|_| "byte relation current caller registry is mutably borrowed")?;
        if !bodies
            .get(&self.call.caller)
            .is_some_and(|body| Rc::ptr_eq(body, self.call.body))
        {
            return Err("byte relation current caller Body was replaced or unavailable".into());
        }
        // Exact current length/extent/context reads, arithmetic, predicate nodes and term copies.
        work.charge(24)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        let Value::CompositeSlice { length, .. } = self.inputs.slice else {
            return Err("byte relation lacks its original live slice".into());
        };
        let length = usize_term(engine, length)?;
        let offset_outside = engine.terms.apply(
            Op::BvUnsignedGt,
            &[self.offset.clone(), self.capacity.clone()],
        )?;
        let remaining = engine
            .terms
            .apply(Op::BvSub, &[self.capacity.clone(), self.offset.clone()])?;
        let length_outside = engine
            .terms
            .apply(Op::BvUnsignedGt, &[length.clone(), remaining])?;
        let outside = engine
            .terms
            .apply(Op::Or, &[offset_outside, length_outside])?;
        // Subtraction is guarded by offset<=capacity; this does not assume wrapping addition safe.
        work.charge(
            self.state
                .conditions
                .len()
                .checked_add(3)
                .ok_or("byte relation condition work overflow")?,
        )
        .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        let mut conditions = self.state.conditions.clone();
        conditions.push(outside);
        if engine.feasible(&conditions)? {
            return Err("byte relation projected extent exceeds its current allocation".into());
        }
        let encoding = engine.readonly_byte_encoding(
            self.original,
            self.inputs.slice,
            self.inputs.needle,
            &self.state.conditions,
            &mut work,
        )?;
        // Observe the initialized needle again and validate its own exact compiler-derived codec.
        // Origin checked carrier identity; encoding equality is an additional requirement.
        work.charge(3)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        let current = storage_locations::StorageLocation::tracked(self.needle_allocation, false)
            .read(&self.state.memory)?;
        let current_encoding = engine.readonly_byte_encoding(
            self.original,
            self.inputs.slice,
            current,
            &self.state.conditions,
            &mut work,
        )?;
        work.charge(2)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        if current_encoding != encoding {
            return Err("byte relation needle encoding differs from current storage".into());
        }
        Ok(Relation {
            origin: self,
            length,
            encoding,
            work,
        })
    }
}

impl<'a, 'tcx> Relation<'a, 'tcx> {
    pub(super) fn bind_route(&mut self, scope: &RouteScope<'_, 'tcx>) -> Result<usize, String> {
        self.work.charge(12).map_err(|error| {
            self.origin
                .engine
                .categorized_error(error.category, error.reason)
        })?;
        if !std::ptr::eq(self.origin.engine, scope.engine)
            || self.origin.original != scope.original
            || !std::ptr::eq(self.origin.call, scope.call)
            || !std::ptr::eq(self.origin.inputs, scope.inputs)
            || !std::ptr::eq(self.origin.state, scope.state)
            || self.work.used() < scope.used
        {
            return Err(
                "byte route scope has a different original caller/operand/Memory nonce".into(),
            );
        }
        self.origin
            .caller_source
            .check(
                scope.engine,
                scope.call.caller,
                scope.call.body,
                &mut self.work,
            )
            .map_err(|error| scope.engine.categorized_error(error.category, error.reason))?;
        Ok(self.work.used())
    }

    pub(super) fn check_invocation(
        &mut self,
        engine: &Engine<'tcx>,
        original: Ty<'tcx>,
        selected: ty::Instance<'tcx>,
        slice: &Value,
        needle: &Value,
        state: &State,
    ) -> Result<usize, String> {
        self.work
            .charge(10)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        if !std::ptr::eq(self.origin.engine, engine)
            || !std::ptr::eq(self.origin.state, state)
            || !std::ptr::eq(self.origin.inputs.slice, slice)
            || !std::ptr::eq(self.origin.inputs.needle, needle)
            || self.origin.original != original
            || self.origin.inputs.selected != selected
            || !self.length.belongs_to(&engine.terms)
            || !self.encoding.belongs_to(&engine.terms)
        {
            return Err("byte relation belongs to another live invocation".into());
        }
        self.work
            .charge(4)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        let bodies = engine
            .bodies
            .try_borrow()
            .map_err(|_| "byte relation current caller registry is mutably borrowed")?;
        if !bodies
            .get(&self.origin.call.caller)
            .is_some_and(|body| Rc::ptr_eq(body, self.origin.call.body))
        {
            return Err("byte relation current caller Body was replaced or unavailable".into());
        }
        // Reading spent work does not consume the borrowed caller or initialized State.
        Ok(self.work.used())
    }

    #[cfg(test)]
    pub(super) fn into_work(
        mut self,
        engine: &Engine<'tcx>,
        original: Ty<'tcx>,
        selected: ty::Instance<'tcx>,
        slice: &Value,
        needle: &Value,
        state: &State,
    ) -> Result<usize, String> {
        self.check_invocation(engine, original, selected, slice, needle, state)
    }

    pub(super) fn borrow_storage(
        mut self,
        engine: &Engine<'tcx>,
        prior: usize,
    ) -> Result<BorrowedStorage<'a, 'tcx>, String> {
        if !std::ptr::eq(engine, self.origin.engine) || prior < self.work.used() {
            return Err(
                "byte storage handoff has a different Engine or lost cumulative work".into(),
            );
        }
        self.work = nonzero_niches::ByteWork::new(prior)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        self.work
            .charge(16)
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        self.origin
            .caller_source
            .check(
                engine,
                self.origin.call.caller,
                self.origin.call.body,
                &mut self.work,
            )
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        let raw = self.origin.inputs.raw;
        let source = &raw[if self.origin.inputs.slice_first { 0 } else { 1 }];
        let needle = &raw[if self.origin.inputs.slice_first { 1 } else { 0 }];
        let (allocation, projection) = readonly_reference(source)?;
        let (needle_allocation, needle_projection) = readonly_reference(needle)?;
        if allocation != self.origin.slice_allocation
            || needle_allocation != self.origin.needle_allocation
            || !needle_projection.is_empty()
        {
            return Err("byte storage current shared reference identity differs".into());
        }
        // Origin established original safe shared types and the typed lifetime/initialization
        // graph after cold preparation. This same immutable State is retained here: no lifetime
        // or address is inferred from a CompositeSlice alone or an allocation number.
        // Whole source and needle mask scans are separate actual visits; their empty field
        // prefixes require no missing-path traversal. The original projected initialization and
        // typed lifetime checks remain live in the immutable Origin issued after preparation.
        self.work
            .charge(12 + 2 * self.origin.state.memory.missing_places.entries().len())
            .map_err(|error| engine.categorized_error(error.category, error.reason))?;
        if projection.len() > MAX_INPUT_DEPTH {
            return Err("byte storage original projection exceeds depth16".into());
        }
        storage_locations::StorageLocation::tracked(needle_allocation, false)
            .read(&self.origin.state.memory)?;
        let stored = storage_locations::StorageLocation::tracked(allocation, false)
            .read(&self.origin.state.memory)?;
        let Value::CompositeSlice { length, leaves, .. } = stored else {
            return Err("byte storage has no retained current source column".into());
        };
        let [column] = leaves.as_slice() else {
            return Err("byte storage current column inventory differs".into());
        };
        if usize_term(engine, length)? != self.origin.capacity || !column.belongs_to(&engine.terms)
        {
            return Err("byte storage current capacity or column Context differs".into());
        }
        // No second projection reconstruction is needed: Origin retained the exact original
        // initialized projected view, evaluated inputs and this same immutable Memory. The
        // preparation/revalidation services can change caches, never this borrowed storage.
        Ok(BorrowedStorage {
            relation: self,
            _column: column,
        })
    }
}

// Original Rust safe-reference contract plus retained initialized typed storage. This is not a
// pointer value or raw-access permit. The private allocation identity is never address arithmetic.
pub(super) struct BorrowedStorage<'a, 'tcx> {
    relation: Relation<'a, 'tcx>,
    _column: &'a Term,
}

impl BorrowedStorage<'_, '_> {
    pub(super) fn used(&self) -> usize {
        // The exact one-column reference is held together with the immutable live State.
        self.relation.work.used()
    }
}

#[cfg(test)]
#[path = "readonly_byte_origins_probe.rs"]
mod probe;
