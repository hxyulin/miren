use super::*;

#[path = "pure_comparison_references.rs"]
mod references;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PureTemplateFamily {
    Primitive,
    Tuple,
    Array,
    SpecArrayDefault,
    SpecArrayBytes,
    SliceEquality,
    SliceEqualityDefault,
    SliceEqualityBytes,
    Contains,
    ContainsDefault,
    ContainsBytes,
    ClosureDefault,
    ClosureBytes,
    IterAny,
    AddPrecondition,
    SubPrecondition,
}

pub(super) fn reference_family(definition: &str, encoded: &str) -> Option<PureTemplateFamily> {
    references::REFERENCES
        .iter()
        .find_map(|(expected, family, body)| {
            (*expected == definition && body.strip_suffix('\n') == Some(encoded)).then_some(*family)
        })
}

pub(super) fn definition_key(id: DefId) -> String {
    normalize_template(&format!("{id:?}"))
}

pub(super) fn owned_definition_key(id: DefId) -> String {
    normalize_owned_template(&format!("{id:?}"), true)
}

const TEMPLATE_NODES: usize = 512;
const TEMPLATE_DEPTH: usize = 16;
const TEMPLATE_OPERAND_WORK: usize = TEMPLATE_NODES * 8;
const TEMPLATE_BYTES: usize = TEMPLATE_NODES * 128;

fn template_work(body: &Body<'_>) -> Result<(), String> {
    let mut work = 0usize;
    for block in body.basic_blocks.iter() {
        work = work
            .saturating_add(block.statements.len())
            .saturating_add(1);
        if work > TEMPLATE_NODES {
            return Err("comparison template exceeds its operation budget".into());
        }
        for statement in &block.statements {
            if let StatementKind::Assign(assignment) = &statement.kind
                && let Rvalue::Aggregate(_, operands) = &assignment.1
                && operands.len() > TEMPLATE_OPERAND_WORK
            {
                return Err("comparison template exceeds its operand budget".into());
            }
        }
        if let TerminatorKind::Call { args, .. } = &block.terminator().kind
            && args.len() > TEMPLATE_OPERAND_WORK
        {
            return Err("comparison template exceeds its operand budget".into());
        }
    }
    Ok(())
}

pub(super) fn encode_template<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    core: rustc_span::def_id::CrateNum,
) -> Result<String, String> {
    encode_template_with_alloc(tcx, body, core, None)
}

// The additional crate is supplied only by an independently authenticated owned-box family.
// Existing pure comparison callers retain the exact single-core domain.
pub(super) fn encode_template_with_alloc<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    core: rustc_span::def_id::CrateNum,
    alloc: Option<rustc_span::def_id::CrateNum>,
) -> Result<String, String> {
    if body.coroutine.is_some()
        || body.tainted_by_errors.is_some()
        || body.basic_blocks.len() > 128
        || body.local_decls.len() > TEMPLATE_NODES
    {
        return Err("comparison template exceeds its supported body domain".into());
    }
    template_work(body)?;
    validate_template_core(body, core, alloc)?;
    let mut work = 0;
    let mut lines = vec![format!(
        "args={} spread={:?}",
        body.arg_count, body.spread_arg
    )];
    for (local, decl) in body.local_decls.iter_enumerated() {
        lines.push(format!(
            "local {local:?} {:?} {:?} user={:?}",
            decl.mutability,
            decl.ty.kind(),
            decl.user_ty
        ));
    }
    for (block, data) in body.basic_blocks.iter_enumerated() {
        lines.push(format!("block {block:?} cleanup={}", data.is_cleanup));
        for statement in &data.statements {
            work += 1;
            if work > TEMPLATE_NODES {
                return Err("comparison template exceeds its operation budget".into());
            }
            match &statement.kind {
                StatementKind::Assign(assignment) => {
                    let (place, value) = assignment.as_ref();
                    lines.push(format!(
                        "assign local={:?} path={:?}",
                        place.local, place.projection
                    ));
                    match value {
                        Rvalue::Ref(region, kind, place) => lines.push(format!(
                            "ref {region:?} {kind:?} local={:?} path={:?}",
                            place.local, place.projection
                        )),
                        Rvalue::RawPtr(kind, place) => lines.push(format!(
                            "raw {kind:?} local={:?} path={:?}",
                            place.local, place.projection
                        )),
                        Rvalue::Aggregate(kind, operands) => {
                            lines.push(format!("aggregate {kind:?}"));
                            for operand in operands {
                                lines.push(encode_operand(tcx, operand, alloc.is_some())?);
                            }
                        }
                        Rvalue::Use(operand, retag) => {
                            lines.push(format!("use {retag:?}"));
                            lines.push(encode_operand(tcx, operand, alloc.is_some())?);
                        }
                        Rvalue::Cast(kind, operand, target) => {
                            lines.push(format!("cast {kind:?} target={:?}", target.kind()));
                            lines.push(encode_operand(tcx, operand, alloc.is_some())?);
                        }
                        Rvalue::BinaryOp(op, operands) => {
                            lines.push(format!("binary {op:?}"));
                            lines.push(encode_operand(tcx, &operands.0, alloc.is_some())?);
                            lines.push(encode_operand(tcx, &operands.1, alloc.is_some())?);
                        }
                        Rvalue::UnaryOp(op, operand) => {
                            lines.push(format!("unary {op:?}"));
                            lines.push(encode_operand(tcx, operand, alloc.is_some())?);
                        }
                        Rvalue::Discriminant(place) | Rvalue::CopyForDeref(place) => {
                            lines.push(format!(
                                "{value:?} local={:?} path={:?}",
                                place.local, place.projection
                            ));
                        }
                        Rvalue::Repeat(..)
                        | Rvalue::ThreadLocalRef(..)
                        | Rvalue::WrapUnsafeBinder(..)
                        | Rvalue::Reborrow(..) => {
                            return Err("comparison template has an unsupported rvalue".into());
                        }
                    }
                }
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop => lines.push(format!("{:?}", statement.kind)),
                StatementKind::Intrinsic(intrinsic) if alloc.is_some() => {
                    match intrinsic.as_ref() {
                        rustc_middle::mir::NonDivergingIntrinsic::Assume(operand) => {
                            lines.push("assume".into());
                            lines.push(encode_operand(tcx, operand, alloc.is_some())?);
                        }
                        rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(_) => {
                            return Err("owned template has an unsupported copy intrinsic".into());
                        }
                    }
                }
                StatementKind::FakeRead(_)
                | StatementKind::SetDiscriminant { .. }
                | StatementKind::PlaceMention(_)
                | StatementKind::AscribeUserType(..)
                | StatementKind::Coverage(_)
                | StatementKind::Intrinsic(_)
                | StatementKind::ConstEvalCounter
                | StatementKind::BackwardIncompatibleDropHint { .. } => {
                    return Err("comparison template has an unsupported statement".into());
                }
            }
        }
        work += 1;
        if work > TEMPLATE_NODES {
            return Err("comparison template exceeds its operation budget".into());
        }
        match &data.terminator().kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
                call_source,
                ..
            } => {
                lines.push(format!(
                    concat!(
                        "call {:?} destination={:?}/{:?} target={:?} ",
                        "unwind={:?} source={:?}"
                    ),
                    func, destination.local, destination.projection, target, unwind, call_source,
                ));
                lines.push(encode_operand(tcx, func, alloc.is_some())?);
                for argument in args {
                    lines.push(encode_operand(tcx, &argument.node, alloc.is_some())?);
                }
            }
            TerminatorKind::Drop {
                place,
                target,
                unwind,
                replace,
                drop,
            } => lines.push(format!(
                "drop {:?}/{:?} target={:?} unwind={:?} replace={} async={:?}",
                place.local, place.projection, target, unwind, replace, drop
            )),
            TerminatorKind::SwitchInt { discr, targets } => {
                lines.push(format!("switch {targets:?}"));
                lines.push(encode_operand(tcx, discr, alloc.is_some())?);
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_) => {
                lines.push(format!("{:?}", data.terminator().kind))
            }
            TerminatorKind::Assert { .. }
            | TerminatorKind::TailCall { .. }
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::InlineAsm { .. } => {
                return Err("comparison template has an unsupported terminator".into());
            }
        }
    }
    let bytes = lines.iter().try_fold(0usize, |bytes, line| {
        bytes.checked_add(line.len())?.checked_add(1)
    });
    if bytes.is_none_or(|bytes| bytes > TEMPLATE_BYTES) {
        return Err("comparison template exceeds its encoded byte budget".into());
    }
    let encoded = wrap_template(&normalize_owned_template(
        &lines.join("\n"),
        alloc.is_some(),
    ))?;
    if encoded.len() > TEMPLATE_BYTES {
        return Err("comparison template exceeds its encoded byte budget".into());
    }
    Ok(encoded)
}

fn encode_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
    alloc: bool,
) -> Result<String, String> {
    Ok(match operand {
        Operand::Copy(place) => format!("copy {:?}/{:?}", place.local, place.projection),
        Operand::Move(place) => format!("move {:?}/{:?}", place.local, place.projection),
        Operand::Constant(constant) => match constant.const_ {
            rustc_middle::mir::Const::Ty(ty, value) => {
                format!("const-type {:?} {:?}", ty.kind(), value.kind())
            }
            rustc_middle::mir::Const::Unevaluated(value, ty) => {
                format!("const-unevaluated {value:?} {:?}", ty.kind())
            }
            rustc_middle::mir::Const::Val(
                rustc_middle::mir::ConstValue::Slice { alloc_id, meta },
                ty,
            ) => {
                if !matches!(ty.kind(), ty::Ref(_, element, mutability)
                    if !mutability.is_mut() && matches!(element.kind(), ty::Str))
                    || meta > TEMPLATE_NODES as u64
                {
                    return Err("comparison template has unsupported constant slice".into());
                }
                let Some(rustc_middle::mir::interpret::GlobalAlloc::Memory(allocation)) =
                    tcx.try_get_global_alloc(alloc_id)
                else {
                    return Err("comparison template string lacks compiler storage".into());
                };
                let allocation = allocation.inner();
                if allocation.mutability.is_mut() || allocation.len() as u64 != meta {
                    return Err(
                        "comparison template string storage differs from its metadata".into(),
                    );
                }
                let range = rustc_middle::mir::interpret::alloc_range(
                    rustc_abi::Size::ZERO,
                    rustc_abi::Size::from_bytes(meta),
                );
                let bytes = allocation.get_bytes_strip_provenance(&tcx, range).map_err(
                    |_| "comparison template string storage is not initialized plain bytes",
                )?;
                let text = std::str::from_utf8(bytes)
                    .map_err(|_| "comparison template string storage is not UTF-8")?;
                format!("const-string {text:?} {:?}", ty.kind())
            }
            rustc_middle::mir::Const::Val(
                rustc_middle::mir::ConstValue::Indirect { alloc_id, offset },
                original,
            ) if alloc => encode_owned_constant(tcx, alloc_id, offset, original)?,
            rustc_middle::mir::Const::Val(value, ty) => {
                if !matches!(
                    value,
                    rustc_middle::mir::ConstValue::Scalar(
                        rustc_middle::mir::interpret::Scalar::Int(_)
                    ) | rustc_middle::mir::ConstValue::ZeroSized
                ) {
                    return Err("comparison template has unsupported constant storage".into());
                }
                format!("const-value {value:?} {:?}", ty.kind())
            }
        },
        Operand::RuntimeChecks(checks) => format!("runtime-checks {checks:?}"),
    })
}

fn encode_owned_constant<'tcx>(
    tcx: TyCtxt<'tcx>,
    id: rustc_middle::mir::interpret::AllocId,
    offset: rustc_abi::Size,
    original: Ty<'tcx>,
) -> Result<String, String> {
    use rustc_abi::Size;
    use rustc_middle::mir::interpret::{GlobalAlloc, alloc_range};
    let layout = tcx
        .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(original))
        .map_err(|_| "owned template constant has unavailable original layout")?;
    if !layout.is_sized() || layout.size.bytes() > TEMPLATE_NODES as u64 {
        return Err("owned template constant exceeds the original sized byte budget".into());
    }
    let Some(GlobalAlloc::Memory(allocation)) = tcx.try_get_global_alloc(id) else {
        return Err("owned template constant lacks actual compiler memory".into());
    };
    let allocation = allocation.inner();
    let end = offset
        .bytes()
        .checked_add(layout.size.bytes())
        .ok_or("owned template constant extent overflows")?;
    if allocation.mutability.is_mut()
        || allocation.len() > TEMPLATE_NODES
        || end > allocation.len() as u64
        || allocation.align < layout.align.abi
        || !offset.bytes().is_multiple_of(layout.align.abi.bytes())
    {
        return Err("owned template constant differs from original extent/alignment".into());
    }
    let range = alloc_range(Size::ZERO, Size::from_bytes(allocation.len() as u64));
    if !allocation.provenance().range_empty(range, &tcx) {
        return Err("owned template constant contains allocation provenance".into());
    }
    let mut bytes = Vec::new();
    for index in offset.bytes()..end {
        let position = Size::from_bytes(index);
        if allocation.init_mask().get(position) {
            let byte = allocation
                .get_bytes_strip_provenance(&tcx, alloc_range(position, Size::from_bytes(1)))
                .map_err(|_| "owned template constant byte is unavailable")?[0];
            bytes.push(format!("{byte:02x}"));
        } else {
            bytes.push("uninit".into());
        }
    }
    Ok(format!(
        "const-object type={:?} size={} align={} offset={} bytes=[{}]",
        original.kind(),
        layout.size.bytes(),
        layout.align.abi.bytes(),
        offset.bytes(),
        bytes.join(",")
    ))
}

fn wrap_template(text: &str) -> Result<String, String> {
    if text
        .lines()
        .any(|line| line.starts_with("  |") || line.starts_with("  >"))
    {
        return Err("comparison template contains a reserved continuation prefix".into());
    }
    let mut wrapped = String::new();
    for (number, line) in text.lines().enumerate() {
        if number != 0 {
            wrapped.push('\n');
        }
        let mut chunk = String::new();
        for (position, character) in line.chars().enumerate() {
            if position != 0 && position % 96 == 0 {
                append_template_chunk(&mut wrapped, &chunk);
                wrapped.push_str("\n  | ");
                chunk.clear();
            }
            chunk.push(character);
        }
        append_template_chunk(&mut wrapped, &chunk);
    }
    Ok(wrapped)
}

fn append_template_chunk(output: &mut String, chunk: &str) {
    // Whitespace is data, including inside quoted constants. Encode it rather than trim it.
    // Reserved marker lines distinguish every escaped character from semantic line breaks.
    let plain = chunk.trim_end_matches(char::is_whitespace);
    if plain.is_empty() && output.ends_with("\n  | ") {
        output.pop();
    }
    output.push_str(plain);
    for character in chunk[plain.len()..].chars() {
        output.push_str(&format!("\n  > U+{:04X}", u32::from(character)));
    }
}

pub(super) fn normalize_template(text: &str) -> String {
    normalize_owned_template(text, false)
}

fn normalize_owned_template(text: &str, alloc: bool) -> String {
    // Only actual DefId debug tokens outside quoted constants have session metadata removed.
    // The visitor independently certifies every embedded compiler identity before encoding.
    let mut result = String::new();
    let mut rest = text;
    let mut quoted = false;
    let mut escaped = false;
    while !rest.is_empty() {
        if !quoted
            && rest.starts_with("DefId(")
            && let Some(end) = rest.find(')')
        {
            let id = &rest[..=end];
            if let Some(core) = id.find("~ core[")
                && let Some(path) = id[core..].find("]::")
            {
                result.push_str("DefId(core::");
                result.push_str(&id[core + path + 3..]);
            } else if alloc
                && let Some(start) = id.find("~ alloc[")
                && let Some(path) = id[start..].find("]::")
            {
                result.push_str("DefId(alloc::");
                result.push_str(&id[start + path + 3..]);
            } else {
                result.push_str(id);
            }
            rest = &rest[end + 1..];
            continue;
        }
        let character = rest.chars().next().expect("nonempty template remainder");
        result.push(character);
        rest = &rest[character.len_utf8()..];
        if quoted && escaped {
            escaped = false;
        } else if quoted && character == '\\' {
            escaped = true;
        } else if character == '"' {
            quoted = !quoted;
        }
    }
    result
}

fn validate_template_core<'tcx>(
    body: &Body<'tcx>,
    core: rustc_span::def_id::CrateNum,
    alloc: Option<rustc_span::def_id::CrateNum>,
) -> Result<(), String> {
    use rustc_middle::mir::visit::Visitor;
    let mut checker = CoreTemplateVisitor {
        types: CoreTemplateTypes {
            core,
            alloc,
            count: 0,
            depth: 0,
        },
        valid: true,
        work: 0,
    };
    checker.visit_body(body);
    if !checker.valid {
        return Err("comparison template has uncertified embedded compiler identities".into());
    }
    Ok(())
}

struct CoreTemplateTypes {
    core: rustc_span::def_id::CrateNum,
    alloc: Option<rustc_span::def_id::CrateNum>,
    count: usize,
    depth: usize,
}

impl CoreTemplateTypes {
    fn permits(&self, krate: rustc_span::def_id::CrateNum) -> bool {
        krate == self.core || self.alloc == Some(krate)
    }
}

impl<'tcx> ty::TypeVisitor<TyCtxt<'tcx>> for CoreTemplateTypes {
    type Result = std::ops::ControlFlow<()>;

    fn visit_ty(&mut self, original: Ty<'tcx>) -> Self::Result {
        use ty::TypeSuperVisitable;
        if self.count >= TEMPLATE_NODES || self.depth >= TEMPLATE_DEPTH {
            return std::ops::ControlFlow::Break(());
        }
        self.count += 1;
        let named = match original.kind() {
            ty::Adt(def, _) => Some(def.did()),
            ty::FnDef(id, _) | ty::Closure(id, _) => Some(*id),
            ty::Alias(..) => return std::ops::ControlFlow::Break(()),
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
            | ty::FnPtr(..)
            | ty::Param(_)
            | ty::Bound(..) => None,
            ty::Foreign(_)
            | ty::Pat(..)
            | ty::UnsafeBinder(_)
            | ty::Dynamic(..)
            | ty::CoroutineClosure(..)
            | ty::Coroutine(..)
            | ty::CoroutineWitness(..)
            | ty::Placeholder(_)
            | ty::Infer(_)
            | ty::Error(_) => return std::ops::ControlFlow::Break(()),
        };
        if named.is_some_and(|id| !self.permits(id.krate)) {
            return std::ops::ControlFlow::Break(());
        }
        self.depth += 1;
        let result = original.super_visit_with(self);
        self.depth -= 1;
        result
    }

    fn visit_const(&mut self, constant: ty::Const<'tcx>) -> Self::Result {
        use ty::TypeSuperVisitable;
        if self.count >= TEMPLATE_NODES || self.depth >= TEMPLATE_DEPTH {
            return std::ops::ControlFlow::Break(());
        }
        self.count += 1;
        match constant.kind() {
            ty::ConstKind::Param(_) | ty::ConstKind::Bound(..) | ty::ConstKind::Value(_) => {}
            ty::ConstKind::Infer(_)
            | ty::ConstKind::Placeholder(_)
            | ty::ConstKind::Alias(..)
            | ty::ConstKind::Error(_)
            | ty::ConstKind::Expr(_) => return std::ops::ControlFlow::Break(()),
        }
        self.depth += 1;
        let result = constant.super_visit_with(self);
        self.depth -= 1;
        result
    }
}

struct CoreTemplateVisitor {
    types: CoreTemplateTypes,
    valid: bool,
    work: usize,
}

impl<'tcx> rustc_middle::mir::visit::Visitor<'tcx> for CoreTemplateVisitor {
    fn visit_var_debug_info(&mut self, info: &rustc_middle::mir::VarDebugInfo<'tcx>) {
        // Debug-only promoted Global constants are not executable MIR operands. Existing
        // comparison validation stays unchanged; the owned encoder still visits every statement.
        if self.types.alloc.is_none() {
            self.super_var_debug_info(info);
        }
    }

    fn visit_ty(&mut self, original: Ty<'tcx>, _: rustc_middle::mir::visit::TyContext) {
        if !self.valid {
            return;
        }
        use ty::TypeVisitable;
        self.valid &= original.visit_with(&mut self.types).is_continue();
    }

    fn visit_args(&mut self, args: &ty::GenericArgsRef<'tcx>, _: rustc_middle::mir::Location) {
        if !self.valid {
            return;
        }
        use ty::TypeVisitable;
        self.valid &= args.visit_with(&mut self.types).is_continue();
    }

    fn visit_const_operand(
        &mut self,
        constant: &rustc_middle::mir::ConstOperand<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        if !self.valid {
            return;
        }
        if let rustc_middle::mir::Const::Unevaluated(value, _) = constant.const_ {
            self.valid &= self.types.permits(value.def.krate) && value.promoted.is_none();
        }
        self.super_const_operand(constant, location);
    }

    fn visit_ty_const(&mut self, constant: ty::Const<'tcx>, _: rustc_middle::mir::Location) {
        if !self.valid {
            return;
        }
        use ty::TypeVisitable;
        self.valid &= constant.visit_with(&mut self.types).is_continue();
    }

    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        context: rustc_middle::mir::visit::PlaceContext,
        location: rustc_middle::mir::Location,
    ) {
        self.work = self.work.saturating_add(1 + place.projection.len());
        self.valid &= self.work <= TEMPLATE_OPERAND_WORK;
        if self.valid {
            self.super_place(place, context, location);
        }
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: rustc_middle::mir::Location) {
        self.work = self.work.saturating_add(1);
        self.valid &= self.work <= TEMPLATE_OPERAND_WORK;
        if self.valid {
            self.super_operand(operand, location);
        }
    }

    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: rustc_middle::mir::Location) {
        if !self.valid {
            return;
        }
        if let Rvalue::Aggregate(kind, _) = value {
            let id = match kind.as_ref() {
                AggregateKind::Adt(id, ..) | AggregateKind::Closure(id, _) => Some(*id),
                AggregateKind::Array(_) | AggregateKind::Tuple | AggregateKind::RawPtr(..) => None,
                AggregateKind::Coroutine(..) | AggregateKind::CoroutineClosure(..) => {
                    self.valid = false;
                    None
                }
            };
            self.valid &= id.is_none_or(|id| self.types.permits(id.krate));
        }
        self.super_rvalue(value, location);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reference_wrapping_preserves_all_semantic_bytes() {
        let original = format!(
            "header\nconstant {:?}\n{}",
            "é\\\"DefId(9 ~ core[bad]::fake)",
            "名".repeat(220)
        );
        let wrapped = wrap_template(&original).unwrap();
        assert!(wrapped.lines().all(|line| line.chars().count() <= 100));
        assert_eq!(decode_wrapped_template(&wrapped), original);
        assert!(wrap_template("header\n  | forged").is_err());
        let literal = "constant \"DefId(9 ~ core[bad]::fake)\"";
        assert_eq!(normalize_template(literal), literal);
        assert_eq!(
            normalize_template("DefId(1:2 ~ core[abcd]::tuple::{impl#4}::eq)"),
            "DefId(core::tuple::{impl#4}::eq)"
        );
    }
    fn decode_wrapped_template(text: &str) -> String {
        let mut lines: Vec<String> = Vec::new();
        for line in text.lines() {
            if line == "  |" {
                continue;
            } else if let Some(continuation) = line.strip_prefix("  | ") {
                lines.last_mut().unwrap().push_str(continuation);
            } else if let Some(character) = line.strip_prefix("  > U+") {
                lines
                    .last_mut()
                    .unwrap()
                    .push(char::from_u32(u32::from_str_radix(character, 16).unwrap()).unwrap());
            } else {
                lines.push(line.to_owned());
            }
        }
        lines.join("\n")
    }

    #[test]
    fn wrap_boundaries_escape_whitespace_without_losing_constant_bytes() {
        for whitespace in [' ', '\t', '\u{00a0}'] {
            let original = format!(
                "{}{}quoted \"literal {}\"  ",
                "x".repeat(95),
                whitespace,
                whitespace.to_string().repeat(200)
            );
            let wrapped = wrap_template(&original).unwrap();
            assert!(wrapped.contains("\n  > U+"));
            assert!(
                wrapped
                    .lines()
                    .all(|line| !line.ends_with(char::is_whitespace))
            );
            assert!(wrapped.lines().all(|line| line.chars().count() <= 100));
            assert_eq!(decode_wrapped_template(&wrapped), original);
            assert_eq!(
                wrap_template(&decode_wrapped_template(&wrapped)).unwrap(),
                wrapped
            );
        }
        assert!(wrap_template("header\n  > U+0020").is_err());
        assert!(wrap_template("header\n  |").is_err());
        for (_, _, reference) in references::REFERENCES {
            assert!(
                reference
                    .lines()
                    .all(|line| !line.ends_with(char::is_whitespace))
            );
        }
    }

    #[test]
    fn actual_compiler_body_mutations_fail_exact_reference_matching() {
        struct MutationCheck {
            checked: bool,
        }
        impl rustc_driver::Callbacks for MutationCheck {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                let eq = tcx
                    .get_diagnostic_item(rustc_span::Symbol::intern("cmp_partialeq_eq"))
                    .unwrap();
                let core = eq.krate;
                for original in [
                    tcx.types.u16,
                    Ty::new_tup(tcx, &[tcx.types.u16, tcx.types.u16]),
                ] {
                    let args = tcx.mk_args(&[original.into(), original.into()]);
                    let instance = ty::Instance::try_resolve(
                        tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        eq,
                        args,
                    )
                    .unwrap()
                    .unwrap();
                    let original = tcx.instance_mir(instance.def);
                    let definition = definition_key(instance.def_id());
                    let encoded = encode_template(tcx, original, core).unwrap();
                    assert!(reference_family(&definition, &encoded).is_some());
                    // A same-name local crate is not the actual compiler core identity.
                    let local_probe = tcx
                        .mir_keys(())
                        .iter()
                        .copied()
                        .find(|id| {
                            tcx.item_name(id.to_def_id()) == rustc_span::Symbol::intern("probe")
                        })
                        .unwrap()
                        .to_def_id();
                    let mut foreign = original.clone();
                    let mut substituted = false;
                    for block in foreign.basic_blocks.as_mut() {
                        if let TerminatorKind::Call { func, .. } = &mut block.terminator_mut().kind
                        {
                            let Operand::Constant(constant) = func else {
                                panic!("function item");
                            };
                            constant.const_ = rustc_middle::mir::Const::Val(
                                rustc_middle::mir::ConstValue::ZeroSized,
                                Ty::new_fn_def(
                                    tcx,
                                    local_probe,
                                    ty::Binder::dummy(tcx.mk_args(&[])),
                                ),
                            );
                            substituted = true;
                            break;
                        }
                    }
                    if substituted {
                        assert!(encode_template(tcx, &foreign, core).is_err());
                    }
                    let mut mutations = Vec::new();
                    let mut changed = original.clone();
                    for block in changed.basic_blocks.as_mut() {
                        if let TerminatorKind::Return = block.terminator().kind {
                            block.terminator_mut().kind = TerminatorKind::Unreachable;
                            break;
                        }
                    }
                    mutations.push(changed);
                    let mut changed = original.clone();
                    for block in changed.basic_blocks.as_mut() {
                        if let TerminatorKind::Call { args, .. } = &mut block.terminator_mut().kind
                        {
                            let mut enlarged = args.to_vec();
                            enlarged.push(enlarged[0].clone());
                            *args = enlarged.into_boxed_slice();
                            break;
                        }
                    }
                    if matches!(original.return_ty().kind(), ty::Bool)
                        && original.basic_blocks.iter().any(|block| {
                            matches!(block.terminator().kind, TerminatorKind::Call { .. })
                        })
                    {
                        mutations.push(changed);
                    }
                    let mut changed = original.clone();
                    let mut found = false;
                    for block in changed.basic_blocks.as_mut() {
                        for statement in &mut block.statements {
                            if let StatementKind::Assign(assignment) = &mut statement.kind {
                                if let Rvalue::BinaryOp(op, operands) = &mut assignment.1 {
                                    *op = match *op {
                                        BinOp::Eq => BinOp::Ne,
                                        _ => BinOp::Eq,
                                    };
                                    operands.1 = operands.0.clone();
                                    found = true;
                                    break;
                                }
                                if let Rvalue::Ref(_, _, place) = &mut assignment.1
                                    && !place.projection.is_empty()
                                {
                                    let mut projection = place.projection.to_vec();
                                    for field in &mut projection {
                                        if let ProjectionElem::Field(index, _) = field {
                                            *index = rustc_abi::FieldIdx::from_usize(
                                                1 - index.as_usize(),
                                            );
                                            found = true;
                                            break;
                                        }
                                    }
                                    place.projection = tcx.mk_place_elems(&projection);
                                    if found {
                                        break;
                                    }
                                }
                            }
                        }
                        if found {
                            break;
                        }
                    }
                    assert!(found);
                    mutations.push(changed);
                    for changed in mutations {
                        let encoded = encode_template(tcx, &changed, core).unwrap();
                        assert!(reference_family(&definition, &encoded).is_none());
                    }
                }
                let contains = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| {
                        tcx.item_name(id.to_def_id()) == rustc_span::Symbol::intern("contains")
                    })
                    .unwrap();
                let local = tcx.optimized_mir(contains.to_def_id());
                let mut pending = Vec::new();
                for block in local.basic_blocks.iter() {
                    if let TerminatorKind::Call { func, .. } = &block.terminator().kind
                        && let ty::FnDef(id, args) = func.ty(&local.local_decls, tcx).kind()
                    {
                        pending.push(
                            ty::Instance::try_resolve(
                                tcx,
                                ty::TypingEnv::fully_monomorphized(),
                                *id,
                                args.skip_binder(),
                            )
                            .unwrap()
                            .unwrap(),
                        );
                    }
                }
                let mut checked_callback = false;
                let mut seen = std::collections::HashSet::new();
                while let Some(instance) = pending.pop() {
                    if !seen.insert(instance) {
                        continue;
                    }
                    assert!(seen.len() <= 16);
                    let generic = tcx.instance_mir(instance.def);
                    let encoded = encode_template(tcx, generic, core).unwrap();
                    let definition = definition_key(instance.def_id());
                    let family = reference_family(&definition, &encoded).unwrap();
                    if family == PureTemplateFamily::ClosureDefault {
                        // Redirect the callback comparison to the captured needle on both sides.
                        let mut changed = generic.clone();
                        let mut found = false;
                        for block in changed.basic_blocks.as_mut() {
                            if let TerminatorKind::Call { args, .. } =
                                &mut block.terminator_mut().kind
                            {
                                assert_eq!(args.len(), 2);
                                args[0].node = args[1].node.clone();
                                found = true;
                                break;
                            }
                        }
                        assert!(found);
                        let encoded = encode_template(tcx, &changed, core).unwrap();
                        assert!(reference_family(&definition, &encoded).is_none());
                        checked_callback = true;
                        break;
                    }
                    let concrete = instance
                        .try_instantiate_mir_and_normalize_erasing_regions(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            ty::EarlyBinder::bind(tcx, generic.clone()),
                        )
                        .unwrap();
                    for block in concrete.basic_blocks.iter() {
                        for statement in &block.statements {
                            if let StatementKind::Assign(assignment) = &statement.kind
                                && let Rvalue::Aggregate(kind, _) = &assignment.1
                                && let AggregateKind::Closure(id, args) = kind.as_ref()
                            {
                                pending.push(ty::Instance::new_raw(*id, args));
                            }
                        }
                        if family == PureTemplateFamily::Contains
                            && let TerminatorKind::Call { func, .. } = &block.terminator().kind
                            && let ty::FnDef(id, args) = func.ty(&concrete.local_decls, tcx).kind()
                        {
                            pending.push(
                                ty::Instance::try_resolve(
                                    tcx,
                                    ty::TypingEnv::fully_monomorphized(),
                                    *id,
                                    args.skip_binder(),
                                )
                                .unwrap()
                                .unwrap(),
                            );
                        }
                    }
                }
                assert!(checked_callback);
                self.checked = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory = std::env::temp_dir().join(format!(
            "miren-comparison-template-mutation-{}",
            std::process::id(),
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("probe.rs");
        std::fs::write(
            &source,
            "#![no_std]\npub fn probe(x:u16,y:u16)->bool{x==y}\n\
             pub fn contains(x:&[(u16,u16)],y:&(u16,u16))->bool{x.contains(y)}\n",
        )
        .unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        assert!(sysroot.status.success());
        let mut callback = MutationCheck { checked: false };
        rustc_driver::run_compiler(
            &[
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "--crate-name=core".into(),
                "-Cpanic=abort".into(),
                "-Copt-level=0".into(),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
                "--sysroot".into(),
                String::from_utf8(sysroot.stdout).unwrap().trim().into(),
            ],
            &mut callback,
        );
        assert!(callback.checked);
        std::fs::remove_dir_all(directory).unwrap();
    }
}
