use super::*;
use composite_slices::CompositeShape;
use rustc_middle::mir::{BasicBlock, Local};
use std::collections::HashMap;
use symbolic::ScalarSliceElement;

const LIMIT: usize = 512;

#[derive(Debug)]
enum Failure {
    Semantics(&'static str),
    Resource(&'static str),
    Existing(String),
}

impl From<&'static str> for Failure {
    fn from(reason: &'static str) -> Self {
        Self::Semantics(reason)
    }
}

impl From<String> for Failure {
    fn from(reason: String) -> Self {
        Self::Existing(reason)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LeafStep {
    Field(usize),
    ArrayElement(usize),
}

#[derive(Clone)]
struct Origin<'tcx> {
    right: bool,
    path: Vec<LeafStep>,
    original: Ty<'tcx>,
    shared: bool,
}

#[derive(Clone)]
enum Observation<'tcx> {
    Origin(Origin<'tcx>),
    Boolean(usize),
}

// A bounded reduced ordered Boolean DAG. Leaves represent numeric equality of one exact
// corresponding receiver field, including independent Float equality (never reflexivity).
#[derive(Default)]
struct Relations {
    nodes: Vec<(usize, usize, usize)>,
    unique: HashMap<(usize, usize, usize), usize>,
    choices: HashMap<(usize, usize, usize), usize>,
    work: usize,
}

impl Relations {
    fn tick(&mut self) -> Result<(), Failure> {
        self.work += 1;
        if self.work > LIMIT {
            return Err(Failure::Resource(
                "nominal comparison Boolean traversal exceeds its node budget",
            ));
        }
        Ok(())
    }

    fn node(&mut self, variable: usize, low: usize, high: usize) -> Result<usize, Failure> {
        if low == high {
            return Ok(low);
        }
        let key = (variable, low, high);
        if let Some(id) = self.unique.get(&key) {
            return Ok(*id);
        }
        self.tick()?;
        let id = self.nodes.len() + 2;
        self.nodes.push(key);
        self.unique.insert(key, id);
        Ok(id)
    }

    fn split(&self, id: usize, variable: usize) -> (usize, usize) {
        if id < 2 {
            return (id, id);
        }
        let (selected, low, high) = self.nodes[id - 2];
        if selected == variable {
            (low, high)
        } else {
            (id, id)
        }
    }

    fn choose(&mut self, condition: usize, yes: usize, no: usize) -> Result<usize, Failure> {
        if condition < 2 {
            return Ok(if condition == 1 { yes } else { no });
        }
        if yes == no {
            return Ok(yes);
        }
        let key = (condition, yes, no);
        if let Some(id) = self.choices.get(&key) {
            return Ok(*id);
        }
        self.tick()?;
        let variable = [condition, yes, no]
            .into_iter()
            .filter(|id| *id >= 2)
            .map(|id| self.nodes[id - 2].0)
            .min()
            .ok_or("nominal comparison has no Boolean variable")?;
        let (cl, ch) = self.split(condition, variable);
        let (yl, yh) = self.split(yes, variable);
        let (nl, nh) = self.split(no, variable);
        let low = self.choose(cl, yl, nl)?;
        let high = self.choose(ch, yh, nh)?;
        let result = self.node(variable, low, high)?;
        self.choices.insert(key, result);
        Ok(result)
    }
}

struct Certificate<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    body: &'a Body<'tcx>,
    leaves: Vec<Vec<LeafStep>>,
    relations: Relations,
    visited: Vec<BasicBlock>,
    steps: &'a mut usize,
    depth: usize,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn nominal_comparison_fields(
        &self,
        original: Ty<'tcx>,
    ) -> Result<Option<Vec<(String, Ty<'tcx>)>>, String> {
        let ty::Adt(definition, _) = original.kind() else {
            return Ok(None);
        };
        if !definition.is_struct() {
            return Ok(None);
        }
        // Preserve the original owned-product scalar probe before its full fresh shape service.
        let _primitive = self.scalar_slice_element(original)?;
        let Some(shape) = self.owned_struct_choice_shape(original)? else {
            return Ok(None);
        };
        self.nominal_product_fields_from_shape(original, shape)
            .map(Some)
    }

    fn nominal_product_fields_from_shape(
        &self,
        original: Ty<'tcx>,
        shape: CompositeShape,
    ) -> Result<Vec<(String, Ty<'tcx>)>, String> {
        // Production callers supply the fresh shape for this exact original Ty. Its existing
        // Copy/Freeze/no-Drop/layout/physical-field/zero-storage gates have already succeeded.
        let ty::Adt(definition, args) = original.kind() else {
            return Err("owned choice annotation differs from original compiler type".into());
        };
        match shape {
            CompositeShape::Struct { name, fields }
                if self.plain_composite_struct(*definition)
                    && self.tcx.def_path_str(definition.did()) == name
                    && definition.non_enum_variant().fields.len() == fields.len() =>
            {
                let mut result = Vec::with_capacity(fields.len());
                for (field, (name, shape)) in
                    definition.non_enum_variant().fields.iter().zip(fields)
                {
                    if field.name.as_str() != name {
                        return Err("owned struct annotation field identity mismatch".into());
                    }
                    let original = field.ty(self.tcx, args).skip_norm_wip();
                    self.validate_nominal_product_shape(original, &shape)?;
                    result.push((name, original));
                }
                Ok(result)
            }
            CompositeShape::Primitive(_)
            | CompositeShape::Tuple(_)
            | CompositeShape::Array(_)
            | CompositeShape::Struct { .. }
            | CompositeShape::NonZeroNiche(_)
            | CompositeShape::Sum { .. } => {
                Err("owned choice annotation differs from original compiler type".into())
            }
        }
    }

    fn validate_nominal_product_shape(
        &self,
        original: Ty<'tcx>,
        shape: &CompositeShape,
    ) -> Result<(), String> {
        match shape {
            CompositeShape::Primitive(kind) => {
                if self.scalar_slice_element(original)? == Some(*kind) {
                    Ok(())
                } else {
                    Err("owned choice annotation differs from original compiler type".into())
                }
            }
            CompositeShape::Tuple(fields) => {
                let ty::Tuple(types) = original.kind() else {
                    return Err(
                        "owned choice annotation differs from original compiler type".into(),
                    );
                };
                if types.len() != fields.len() {
                    return Err(
                        "owned choice annotation differs from original compiler type".into(),
                    );
                }
                for (original, shape) in types.iter().zip(fields) {
                    self.validate_nominal_product_shape(original, shape)?;
                }
                Ok(())
            }
            CompositeShape::Array(fields) => {
                let ty::Array(element, count) = original.kind() else {
                    return Err(
                        "owned choice annotation differs from original compiler type".into(),
                    );
                };
                let count = count
                    .try_to_target_usize(self.tcx)
                    .ok_or("owned array annotation requires concrete compiler count")?;
                if count != fields.len() as u64 {
                    return Err("owned array annotation differs from certified count".into());
                }
                if *element == self.tcx.types.u8 {
                    if fields.iter().any(|field| {
                        !matches!(
                            field,
                            CompositeShape::Primitive(ScalarSliceElement::Integer {
                                bits: 8,
                                signed: false,
                            })
                        )
                    }) {
                        return Err(
                            "owned byte array annotation differs from certified primitive shape"
                                .into(),
                        );
                    }
                    return Ok(());
                }
                for shape in fields {
                    self.validate_nominal_product_shape(*element, shape)?;
                }
                Ok(())
            }
            CompositeShape::Struct { name, fields } => {
                let ty::Adt(definition, args) = original.kind() else {
                    return Err(
                        "owned choice annotation differs from original compiler type".into(),
                    );
                };
                if !self.plain_composite_struct(*definition)
                    || self.tcx.def_path_str(definition.did()) != *name
                    || definition.non_enum_variant().fields.len() != fields.len()
                {
                    return Err(
                        "owned choice annotation differs from original compiler type".into(),
                    );
                }
                for (field, (name, shape)) in
                    definition.non_enum_variant().fields.iter().zip(fields)
                {
                    if field.name.as_str() != name {
                        return Err("owned struct annotation field identity mismatch".into());
                    }
                    self.validate_nominal_product_shape(
                        field.ty(self.tcx, args).skip_norm_wip(),
                        shape,
                    )?;
                }
                Ok(())
            }
            CompositeShape::NonZeroNiche(_) | CompositeShape::Sum { .. } => {
                Err("owned choice annotation differs from original compiler type".into())
            }
        }
    }

    // This validates a selected body, not an inventory entry or derive marker. It is separate
    // from formula admission so the implementation can be reviewed before enabling summaries.
    pub(super) fn certify_nominal_comparison(
        &self,
        original: Ty<'tcx>,
        instance: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        self.nominal_comparison_body(original, instance, 0, &mut 0)
            .map_err(|failure| match failure {
                Failure::Semantics(reason) => {
                    self.categorized_error(UnknownCategory::Semantics, reason.into())
                }
                Failure::Resource(reason) => {
                    self.categorized_error(UnknownCategory::ResourceLimit, reason.into())
                }
                Failure::Existing(reason) => reason,
            })
    }

    fn nominal_comparison_body(
        &self,
        original: Ty<'tcx>,
        instance: ty::Instance<'tcx>,
        depth: usize,
        steps: &mut usize,
    ) -> Result<(), Failure> {
        if depth >= 16 {
            return Err(Failure::Resource(
                "nominal comparison exceeds its selected-body depth budget",
            ));
        }
        if self.nominal_comparison_fields(original)?.is_none() {
            return Err("nominal comparison requires an exact ordinary pure struct".into());
        }
        let core = self
            .tcx
            .lang_items()
            .sized_trait()
            .ok_or("nominal comparison actual core identity is unavailable")?
            .krate;
        let eq = self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("cmp_partialeq_eq"))
            .filter(|id| id.krate == core)
            .ok_or("nominal comparison PartialEq identity is unavailable")?;
        let ne = self
            .tcx
            .get_diagnostic_item(rustc_span::Symbol::intern("cmp_partialeq_ne"))
            .filter(|id| id.krate == core && self.tcx.parent(*id) == self.tcx.parent(eq))
            .ok_or("nominal comparison PartialEq::ne identity is unavailable")?;
        let args = self.tcx.mk_args(&[original.into(), original.into()]);
        let selected_eq = self.resolve_function_item(eq, args)?;
        let selected_ne = self.resolve_function_item(ne, args)?;
        let negate = instance == selected_ne && instance.def_id() == ne;
        if instance != selected_eq && !negate {
            return Err("nominal comparison has a different selected comparator".into());
        }
        if !matches!(instance.def, ty::InstanceKind::Item(_)) {
            return Err("nominal comparison has an unsupported selected adapter".into());
        }
        let signature = self.call_signature(instance)?;
        if signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.safety() != rustc_hir::Safety::Safe
            || signature.output() != self.tcx.types.bool
            || signature.inputs().len() != 2
            || signature.inputs().iter().any(|input| {
                !matches!(input.kind(),
                ty::Ref(_, element, mutability) if *element == original && !mutability.is_mut())
            })
        {
            return Err(
                "nominal comparison requires its exact safe Rust receiver signature".into(),
            );
        }
        let body = self.instantiated_body(instance)?;
        if body.local_decls.len() > LIMIT || body.basic_blocks.len() > LIMIT {
            return Err(Failure::Resource(
                "nominal comparison body exceeds its storage budget",
            ));
        }
        if body.arg_count != 2 || body.local_decls[Local::from_usize(0)].ty != self.tcx.types.bool {
            return Err("nominal comparison has a different receiver or result schema".into());
        }
        for index in [1, 2] {
            if !matches!(body.local_decls[Local::from_usize(index)].ty.kind(),
                ty::Ref(_, element, mutability) if *element == original && !mutability.is_mut())
            {
                return Err("nominal comparison requires exact ordinary shared receivers".into());
            }
        }
        let mut leaves = Vec::new();
        self.nominal_comparison_leaves(original, &mut Vec::new(), &mut leaves, 0, &mut 0, true)?;
        let mut certificate = Certificate {
            engine: self,
            body: &body,
            leaves,
            relations: Relations::default(),
            visited: Vec::new(),
            steps,
            depth,
        };
        let mut locals = vec![None; body.local_decls.len()];
        for (index, right) in [(1, false), (2, true)] {
            locals[index] = Some(Observation::Origin(Origin {
                right,
                path: Vec::new(),
                original,
                shared: true,
            }));
        }
        let actual = certificate.block(START_BLOCK, locals)?;
        let mut expected = 1;
        for index in 0..certificate.leaves.len() {
            let leaf = certificate.relations.node(index, 0, 1)?;
            expected = certificate.relations.choose(leaf, expected, 0)?;
        }
        if negate {
            expected = certificate.relations.choose(expected, 0, 1)?;
        }
        if actual != expected {
            return Err(
                "nominal comparison does not compute all corresponding field equalities".into(),
            );
        }
        Ok(())
    }

    fn nominal_comparison_leaves(
        &self,
        original: Ty<'tcx>,
        path: &mut Vec<LeafStep>,
        leaves: &mut Vec<Vec<LeafStep>>,
        depth: usize,
        nodes: &mut usize,
        collect: bool,
    ) -> Result<(), Failure> {
        *nodes += 1;
        if depth >= 16 || *nodes > LIMIT {
            return Err(Failure::Resource(
                "nominal comparison field traversal exceeds its type budget",
            ));
        }
        if self.scalar_slice_element(original)?.is_some() {
            if collect {
                leaves.push(path.clone());
            }
            return Ok(());
        }
        if let ty::Array(child, count) = original.kind() {
            if !primitive_array_child(*child, depth + 1) {
                return Err("nominal comparison array requires exact primitive children".into());
            }
            let count = count
                .try_to_target_usize(self.tcx)
                .ok_or("nominal comparison array lacks a concrete original length")?;
            if count > 128 {
                return Err(Failure::Resource(
                    "nominal comparison array exceeds its type budget",
                ));
            }
            // A vacant array still validates and charges its complete original child tree.
            for index in 0..count.max(1) as usize {
                path.push(LeafStep::ArrayElement(index));
                self.nominal_comparison_leaves(
                    *child,
                    path,
                    leaves,
                    depth + 1,
                    nodes,
                    collect && count != 0,
                )?;
                path.pop();
            }
            return Ok(());
        }
        let children: Vec<_> = match original.kind() {
            ty::Tuple(fields) => fields.iter().collect(),
            ty::Adt(_, _) => self
                .nominal_comparison_fields(original)?
                .ok_or("nominal comparison contains an unsupported original field")?
                .into_iter()
                .map(|(_, original)| original)
                .collect(),
            _ => {
                return Err(
                    "nominal comparison field type is outside its structural grammar".into(),
                );
            }
        };
        for (index, original) in children.into_iter().enumerate() {
            path.push(LeafStep::Field(index));
            self.nominal_comparison_leaves(original, path, leaves, depth + 1, nodes, collect)?;
            path.pop();
        }
        Ok(())
    }
}

fn primitive_array_child(original: Ty<'_>, depth: usize) -> bool {
    if depth >= 16 {
        return false;
    }
    match original.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) => true,
        ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64) => true,
        ty::Array(child, _) => primitive_array_child(*child, depth + 1),
        _ => false,
    }
}

impl<'tcx> Certificate<'_, 'tcx> {
    fn local_type(&self, local: Local, value: &Observation<'tcx>) -> Result<(), Failure> {
        let actual = self.body.local_decls[local].ty;
        let valid = match value {
            Observation::Boolean(_) => actual == self.engine.tcx.types.bool,
            Observation::Origin(origin) if origin.shared => matches!(actual.kind(),
                ty::Ref(_, original, mutability)
                    if *original == origin.original && !mutability.is_mut()),
            Observation::Origin(origin) => actual == origin.original,
        };
        if !valid {
            return Err("nominal comparison temporary differs from its exact original type".into());
        }
        Ok(())
    }

    fn step(&mut self) -> Result<(), Failure> {
        *self.steps += 1;
        if *self.steps > LIMIT {
            return Err(Failure::Resource(
                "nominal comparison CFG traversal exceeds its work budget",
            ));
        }
        Ok(())
    }

    fn place(
        &self,
        locals: &[Option<Observation<'tcx>>],
        place: Place<'tcx>,
    ) -> Result<Observation<'tcx>, Failure> {
        let mut value = locals[place.local.as_usize()]
            .clone()
            .ok_or("nominal comparison reads uninitialized or consumed storage")?;
        self.local_type(place.local, &value)?;
        for projection in place.projection {
            let Observation::Origin(origin) = &mut value else {
                return Err("nominal comparison projects a Boolean temporary".into());
            };
            match projection {
                ProjectionElem::Deref if origin.shared => origin.shared = false,
                ProjectionElem::Field(index, recorded) if !origin.shared => {
                    let actual = match origin.original.kind() {
                        ty::Tuple(fields) => fields.get(index.as_usize()).copied(),
                        ty::Adt(definition, args) if definition.is_struct() => definition
                            .non_enum_variant()
                            .fields
                            .get(index)
                            .map(|field| field.ty(self.engine.tcx, args).skip_norm_wip()),
                        _ => None,
                    }
                    .ok_or("nominal comparison field lacks its original compiler type")?;
                    if actual != recorded {
                        return Err("nominal comparison has a different recorded FieldTy".into());
                    }
                    origin.path.push(LeafStep::Field(index.as_usize()));
                    origin.original = actual;
                }
                _ => return Err("nominal comparison contains an unsupported projection".into()),
            }
        }
        Ok(value)
    }

    fn operand(
        &self,
        locals: &mut [Option<Observation<'tcx>>],
        operand: &Operand<'tcx>,
    ) -> Result<Observation<'tcx>, Failure> {
        match operand {
            Operand::Copy(place) => self.place(locals, *place),
            Operand::Move(place) if place.projection.is_empty() => locals[place.local.as_usize()]
                .take()
                .ok_or("nominal comparison moves uninitialized or consumed storage".into()),
            Operand::Move(_) => Err("nominal comparison moves projected receiver storage".into()),
            Operand::Constant(constant) if constant.const_.ty() == self.engine.tcx.types.bool => {
                let value = self.engine.constant(
                    self.body.source.instance.def_id(),
                    constant.const_,
                    constant.span,
                )?;
                let Value::Bool(expression) = value else {
                    return Err(
                        "nominal comparison Boolean constant has a different carrier".into(),
                    );
                };
                match expression.constant() {
                    Some(miren::smt::Constant::Bool(value)) => {
                        Ok(Observation::Boolean(usize::from(value)))
                    }
                    _ => Err("nominal comparison Boolean constant is not concrete".into()),
                }
            }
            Operand::Constant(_) | Operand::RuntimeChecks(_) => {
                Err("nominal comparison contains an unsupported operand".into())
            }
        }
    }

    fn equality(
        &mut self,
        left: Observation<'tcx>,
        right: Observation<'tcx>,
    ) -> Result<usize, Failure> {
        let (Observation::Origin(left), Observation::Origin(right)) = (left, right) else {
            return Err("nominal comparison equality lacks two receiver origins".into());
        };
        if left.right == right.right
            || left.path != right.path
            || left.original != right.original
            || left.shared != right.shared
        {
            return Err("nominal comparison compares different or repeated receiver fields".into());
        }
        let mut result = 1;
        for (index, path) in self.leaves.iter().enumerate() {
            if path.starts_with(&left.path) {
                let leaf = self.relations.node(index, 0, 1)?;
                result = self.relations.choose(leaf, result, 0)?;
            }
        }
        Ok(result)
    }

    fn boolean(value: Observation<'tcx>) -> Result<usize, Failure> {
        match value {
            Observation::Boolean(value) => Ok(value),
            Observation::Origin(_) => Err("nominal comparison branches on receiver data".into()),
        }
    }

    fn block(
        &mut self,
        block: BasicBlock,
        mut locals: Vec<Option<Observation<'tcx>>>,
    ) -> Result<usize, Failure> {
        self.step()?;
        if self.visited.contains(&block) {
            return Err("nominal comparison contains a cyclic CFG".into());
        }
        self.visited.push(block);
        let data = &self.body.basic_blocks[block];
        for statement in &data.statements {
            self.step()?;
            match &statement.kind {
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                    locals[local.as_usize()] = None
                }
                StatementKind::Nop => {}
                StatementKind::Assign(assignment) if assignment.0.projection.is_empty() => {
                    let value = match &assignment.1 {
                        Rvalue::Use(operand, _) => self.operand(&mut locals, operand)?,
                        Rvalue::Ref(_, BorrowKind::Shared, place) => {
                            let Observation::Origin(mut origin) = self.place(&locals, *place)?
                            else {
                                return Err(
                                    "nominal comparison borrows a non-receiver temporary".into()
                                );
                            };
                            if origin.shared {
                                return Err("nominal comparison borrows a receiver handle".into());
                            }
                            origin.shared = true;
                            Observation::Origin(origin)
                        }
                        Rvalue::BinaryOp(BinOp::Eq, operands) => {
                            let left = self.operand(&mut locals, &operands.0)?;
                            let right = self.operand(&mut locals, &operands.1)?;
                            if !matches!((&left, &right),
                                (Observation::Origin(a), Observation::Origin(b))
                                if !a.shared && !b.shared
                                    && self.engine.scalar_slice_element(a.original)?.is_some())
                            {
                                return Err(
                                    "nominal comparison primitive equality has another type".into(),
                                );
                            }
                            Observation::Boolean(self.equality(left, right)?)
                        }
                        Rvalue::UnaryOp(UnOp::Not, operand) => {
                            let value = Self::boolean(self.operand(&mut locals, operand)?)?;
                            Observation::Boolean(self.relations.choose(value, 0, 1)?)
                        }
                        _ => {
                            return Err(
                                "nominal comparison contains an unsupported rvalue or effect"
                                    .into(),
                            );
                        }
                    };
                    self.local_type(assignment.0.local, &value)?;
                    locals[assignment.0.local.as_usize()] = Some(value);
                }
                _ => {
                    return Err(
                        "nominal comparison contains an unsupported statement or effect".into(),
                    );
                }
            }
        }
        let result = match &data.terminator().kind {
            TerminatorKind::Return => {
                Self::boolean(self.place(&locals, Place::from(Local::from_usize(0)))?)?
            }
            TerminatorKind::Goto { target } => self.block(*target, locals)?,
            TerminatorKind::SwitchInt { discr, targets } => {
                if discr.ty(&self.body.local_decls, self.engine.tcx) != self.engine.tcx.types.bool {
                    return Err("nominal comparison switches on a non-Boolean value".into());
                }
                let condition = Self::boolean(self.operand(&mut locals, discr)?)?;
                let no = self.block(targets.target_for_value(0), locals.clone())?;
                let yes = self.block(targets.target_for_value(1), locals)?;
                self.relations.choose(condition, yes, no)?
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } if destination.projection.is_empty() && args.len() == 2 => {
                if !matches!(func, Operand::Constant(_)) {
                    return Err(
                        "nominal comparison calls an uninitialized or indirect target".into(),
                    );
                }
                let ty::FnDef(id, arguments) =
                    func.ty(&self.body.local_decls, self.engine.tcx).kind()
                else {
                    return Err("nominal comparison calls an indirect function".into());
                };
                let eq = self
                    .engine
                    .tcx
                    .get_diagnostic_item(rustc_span::Symbol::intern("cmp_partialeq_eq"))
                    .ok_or("nominal comparison has no PartialEq identity")?;
                let left = self.operand(&mut locals, &args[0].node)?;
                let right = self.operand(&mut locals, &args[1].node)?;
                let Observation::Origin(origin) = &left else {
                    return Err("nominal comparison child has no typed receiver".into());
                };
                if !origin.shared {
                    return Err("nominal comparison child lacks a shared receiver".into());
                }
                let original = origin.original;
                let selected = self
                    .engine
                    .resolve_function_item(*id, arguments.skip_binder())?;
                let expected_args = self.engine.tcx.mk_args(&[original.into(), original.into()]);
                if selected != self.engine.resolve_function_item(eq, expected_args)? {
                    return Err(
                        "nominal comparison child has different original type arguments".into(),
                    );
                }
                if self.engine.nominal_comparison_fields(original)?.is_some() {
                    self.engine.nominal_comparison_body(
                        original,
                        selected,
                        self.depth + 1,
                        self.steps,
                    )?;
                } else {
                    self.engine.certify_pure_comparison(original, selected)?;
                }
                // The child certificate proves totality and no effects, including its cleanup.
                let relation = self.equality(left, right)?;
                let value = Observation::Boolean(relation);
                self.local_type(destination.local, &value)?;
                locals[destination.local.as_usize()] = Some(value);
                self.block(*target, locals)?
            }
            _ => {
                return Err(
                    "nominal comparison contains an unsupported terminator or effect".into(),
                );
            }
        };
        self.visited.pop();
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolean_dag_preserves_short_circuit_fields_and_refuses_missing_fields() {
        let mut relations = Relations::default();
        let left = relations.node(0, 0, 1).unwrap();
        let right = relations.node(1, 0, 1).unwrap();
        let conjunction = relations.choose(left, right, 0).unwrap();
        assert_eq!(conjunction, relations.choose(right, left, 0).unwrap());
        assert_ne!(conjunction, left);
        assert_ne!(conjunction, relations.choose(left, left, 0).unwrap());
        let not = relations.choose(conjunction, 0, 1).unwrap();
        assert_eq!(relations.choose(not, 0, 1).unwrap(), conjunction);
        assert_ne!(conjunction, 1);
        let mut bounded = Relations::default();
        for variable in 0..LIMIT {
            bounded.node(variable, 0, 1).unwrap();
        }
        assert!(matches!(
            bounded.node(LIMIT, 0, 1),
            Err(Failure::Resource(_))
        ));
    }

    #[test]
    fn selected_compiler_comparers_require_complete_typed_receiver_fields_and_no_effects() {
        struct Check {
            checked: bool,
        }
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                let config = miren::ContractConfig::default();
                let limits = miren::AnalysisLimits::default();
                let all_failures = false;
                let induction = false;
                let startup = false;
                let isolated_startup = false;
                let async_entry = false;
                let engine = Engine::new(
                    tcx,
                    &config,
                    VerificationOptions {
                        all_failures,
                        induction,
                        startup,
                        isolated_startup,
                        async_entry,
                        limits,
                    },
                );
                for original in [
                    tcx.types.bool,
                    tcx.types.char,
                    tcx.types.f32,
                    tcx.types.f64,
                    tcx.types.i16,
                    tcx.types.u16,
                ] {
                    assert!(primitive_array_child(original, 0));
                    assert!(!primitive_array_child(original, 16));
                }
                for original in [tcx.types.f16, tcx.types.f128, tcx.types.str_] {
                    assert!(!primitive_array_child(original, 0));
                }
                let eq = tcx
                    .get_diagnostic_item(rustc_span::Symbol::intern("cmp_partialeq_eq"))
                    .unwrap();
                let ne = tcx
                    .get_diagnostic_item(rustc_span::Symbol::intern("cmp_partialeq_ne"))
                    .unwrap();
                for (name, accepted) in [
                    ("record", true),
                    ("nested", true),
                    ("integer_arrays", true),
                    ("vacant_array", true),
                    ("primitive_arrays", true),
                    ("vacant_primitives", true),
                    ("nonprimitive_array", false),
                    ("wrong_array", false),
                    ("zero", true),
                    ("wrong", false),
                    ("missing", false),
                    ("panic_eq", false),
                ] {
                    let function = tcx
                        .mir_keys(())
                        .iter()
                        .copied()
                        .find(|id| {
                            tcx.def_kind(id.to_def_id()) == rustc_hir::def::DefKind::Fn
                                && tcx.item_name(id.to_def_id()).as_str() == name
                        })
                        .unwrap()
                        .to_def_id();
                    let original = tcx
                        .fn_sig(function)
                        .instantiate_identity()
                        .skip_binder()
                        .inputs()[0];
                    let args = tcx.mk_args(&[original.into(), original.into()]);
                    let instance = engine.resolve_function_item(eq, args).unwrap();
                    let result = engine.certify_nominal_comparison(original, instance);
                    assert_eq!(result.is_ok(), accepted, "{name}: {result:?}");
                    if name == "integer_arrays" || name == "vacant_array" {
                        let mut leaves = Vec::new();
                        let mut nodes = 0;
                        engine
                            .nominal_comparison_leaves(
                                original,
                                &mut Vec::new(),
                                &mut leaves,
                                0,
                                &mut nodes,
                                true,
                            )
                            .unwrap();
                        if name == "integer_arrays" {
                            assert_eq!(nodes, 9);
                            assert_eq!(leaves.len(), 5);
                            assert_eq!(
                                leaves[0],
                                vec![
                                    LeafStep::Field(0),
                                    LeafStep::ArrayElement(0),
                                    LeafStep::ArrayElement(0),
                                ]
                            );
                            assert_eq!(leaves[4], vec![LeafStep::Field(1)]);
                        } else {
                            assert_eq!(nodes, 6);
                            assert!(leaves.is_empty());
                        }
                        let mut exhausted = LIMIT;
                        assert!(
                            engine
                                .nominal_comparison_leaves(
                                    original,
                                    &mut Vec::new(),
                                    &mut Vec::new(),
                                    0,
                                    &mut exhausted,
                                    true,
                                )
                                .is_err()
                        );
                    }
                    if name == "primitive_arrays" || name == "vacant_primitives" {
                        let mut leaves = Vec::new();
                        let mut nodes = 0;
                        engine
                            .nominal_comparison_leaves(
                                original,
                                &mut Vec::new(),
                                &mut leaves,
                                0,
                                &mut nodes,
                                true,
                            )
                            .unwrap();
                        if name == "primitive_arrays" {
                            assert_eq!(nodes, 17);
                            assert_eq!(leaves.len(), 10);
                            assert_eq!(
                                leaves[4],
                                vec![LeafStep::Field(1), LeafStep::ArrayElement(0)]
                            );
                            assert_eq!(
                                leaves[9],
                                vec![LeafStep::Field(3), LeafStep::ArrayElement(1)]
                            );
                        } else {
                            assert_eq!(nodes, 7);
                            assert!(leaves.is_empty());
                        }
                    }
                    if name == "record" {
                        let fields = engine.nominal_comparison_fields(original).unwrap().unwrap();
                        let plan = super::super::pure_comparisons::PureComparison::Struct {
                            original,
                            fields: fields
                                .iter()
                                .map(|(name, ty)| {
                                    (
                                        name.clone(),
                                        super::super::pure_comparisons::PureComparison::Primitive(
                                            *ty,
                                        ),
                                    )
                                })
                                .collect(),
                        };
                        let ty::Adt(definition, _) = original.kind() else {
                            panic!("record")
                        };
                        let valid = Value::Adt {
                            name: tcx.def_path_str(definition.did()),
                            variant: 0,
                            is_option: false,
                            discriminant: 0,
                            fields: fields
                                .iter()
                                .map(|(name, _)| {
                                    (name.clone(), symbolic::integer(&engine.terms, 0, 16, false))
                                })
                                .collect(),
                        };
                        assert!(engine.pure_comparison_equal(&plan, &valid, &valid).is_ok());
                        for wrong in [
                            symbolic::integer(&engine.terms, 0, 8, false),
                            symbolic::integer(&engine.terms, 0, 16, true),
                            symbolic::integer(&Context::default(), 0, 16, false),
                        ] {
                            let mut malformed = valid.clone();
                            let Value::Adt { fields, .. } = &mut malformed else {
                                panic!("record")
                            };
                            fields[0].1 = wrong;
                            assert!(
                                engine
                                    .pure_comparison_equal(&plan, &malformed, &malformed)
                                    .is_err()
                            );
                        }
                        let mut malformed = valid.clone();
                        let Value::Adt { fields, .. } = &mut malformed else {
                            panic!("record")
                        };
                        fields.swap(0, 1);
                        assert!(
                            engine
                                .pure_comparison_equal(&plan, &malformed, &malformed)
                                .is_err()
                        );
                    }
                    if name == "record" {
                        let original_body = engine.instantiated_body(instance).unwrap();
                        let mut changed = (*original_body).clone();
                        let mut found = false;
                        for block in changed.basic_blocks.as_mut() {
                            if matches!(block.terminator().kind, TerminatorKind::Return) {
                                block.terminator_mut().kind = TerminatorKind::Unreachable;
                                found = true;
                            }
                        }
                        assert!(found);
                        engine
                            .bodies
                            .borrow_mut()
                            .insert(instance, std::rc::Rc::new(changed));
                        assert!(
                            engine
                                .certify_nominal_comparison(original, instance)
                                .is_err()
                        );
                        engine.bodies.borrow_mut().insert(instance, original_body);
                        engine
                            .certify_nominal_comparison(original, instance)
                            .unwrap();
                    }
                    if accepted {
                        let instance = engine.resolve_function_item(ne, args).unwrap();
                        engine
                            .certify_nominal_comparison(original, instance)
                            .unwrap();
                    }
                }
                self.checked = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory = std::env::temp_dir().join(format!(
            "miren-nominal-comparison-certificate-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("probe.rs");
        std::fs::write(
            &source,
            r#"
#![no_std]
#[derive(Clone, Copy, PartialEq)] pub struct Record { left: u16, right: u16 }
#[derive(Clone, Copy, PartialEq)] pub struct Nested { value: Record, flag: bool, c: char, f: f32 }
#[derive(Clone, Copy, PartialEq)] pub struct Zero;
#[derive(Clone, Copy, PartialEq)] pub struct IntegerArrays { arrays: [[i16; 2]; 2], flag: bool }
#[derive(Clone, Copy, PartialEq)] pub struct VacantArray { arrays: [[u16; 0]; 2] }
#[derive(Clone, Copy, PartialEq)] pub struct PrimitiveArrays {
    flags: [[bool; 2]; 2], characters: [char; 2], singles: [f32; 2], doubles: [f64; 2]
}
#[derive(Clone, Copy, PartialEq)] pub struct VacantPrimitives {
    flags: [bool; 0], characters: [char; 0], floats: [f64; 0]
}
#[derive(Clone, Copy, PartialEq)] pub struct NonprimitiveArray { array: [Option<u16>; 0] }
#[derive(Clone, Copy)] pub struct WrongArray { left: [u16; 2], right: [u16; 2] }
impl PartialEq for WrongArray {
    fn eq(&self, other: &Self) -> bool { self.left == other.left && self.right == other.left }
}

#[derive(Clone, Copy)] pub struct Wrong { left: u16, right: u16 }
impl PartialEq for Wrong {
    fn eq(&self, other: &Self) -> bool { self.left == other.left && self.right == other.left }
}
#[derive(Clone, Copy)] pub struct Missing { pub left: u16, pub right: u16 }
impl PartialEq for Missing { fn eq(&self, other: &Self) -> bool { self.left == other.left } }
#[derive(Clone, Copy)] pub struct PanicEq;
impl PartialEq for PanicEq { fn eq(&self, _: &Self) -> bool { panic!("effect") } }
pub fn integer_arrays(_: IntegerArrays) {} pub fn vacant_array(_: VacantArray) {}
pub fn primitive_arrays(_: PrimitiveArrays) {} pub fn vacant_primitives(_: VacantPrimitives) {}
pub fn nonprimitive_array(_: NonprimitiveArray) {} pub fn wrong_array(_: WrongArray) {}
pub fn record(_: Record) {} pub fn nested(_: Nested) {} pub fn zero(_: Zero) {}
pub fn wrong(_: Wrong) {} pub fn missing(_: Missing) {} pub fn panic_eq(_: PanicEq) {}
"#,
        )
        .unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        assert!(sysroot.status.success());
        for level in ["0", "2"] {
            let mut check = Check { checked: false };
            rustc_driver::run_compiler(
                &[
                    "rustc".into(),
                    source.to_str().unwrap().into(),
                    "--crate-type=lib".into(),
                    "--edition=2024".into(),
                    "-Zmir-opt-level=0".into(),
                    "-Cpanic=abort".into(),
                    format!("-Copt-level={level}"),
                    "--out-dir".into(),
                    directory.to_str().unwrap().into(),
                    "--sysroot".into(),
                    String::from_utf8(sysroot.stdout.clone())
                        .unwrap()
                        .trim()
                        .into(),
                ],
                &mut check,
            );
            assert!(check.checked);
        }
        std::fs::remove_dir_all(directory).unwrap();
    }
}

#[cfg(test)]
mod nominal_field_constructor_tests {
    use super::*;

    fn legacy_fields<'tcx>(
        engine: &Engine<'tcx>,
        original: Ty<'tcx>,
    ) -> Result<Option<Vec<(String, Ty<'tcx>)>>, String> {
        let ty::Adt(definition, args) = original.kind() else {
            return Ok(None);
        };
        if !definition.is_struct() || engine.owned_product_shape(original)?.is_none() {
            return Ok(None);
        }
        Ok(Some(
            definition
                .non_enum_variant()
                .fields
                .iter()
                .map(|field| {
                    (
                        field.name.to_string(),
                        field.ty(engine.tcx, args).skip_norm_wip(),
                    )
                })
                .collect(),
        ))
    }

    fn changed_root_shapes_refuse<'tcx>(engine: &Engine<'tcx>, original: Ty<'tcx>) {
        let shape = engine.owned_struct_choice_shape(original).unwrap().unwrap();
        let fields = engine
            .nominal_product_fields_from_shape(original, shape.clone())
            .unwrap();
        assert_eq!(fields[0].0, "field");
        assert_eq!(fields[0].1, engine.tcx.types.u16);
        for mutation in 0..7 {
            let mut changed = shape.clone();
            let CompositeShape::Struct { name, fields } = &mut changed else {
                panic!("fresh original struct")
            };
            match mutation {
                0 => name.push_str("::wrong"),
                1 => fields[0].0.push_str("_wrong"),
                2 => fields.clear(),
                3 => {
                    fields[0].1 = CompositeShape::Primitive(ScalarSliceElement::Integer {
                        bits: 8,
                        signed: false,
                    });
                }
                4 => {
                    fields[0].1 = CompositeShape::Primitive(ScalarSliceElement::Integer {
                        bits: 16,
                        signed: true,
                    });
                }
                5 => fields[0].1 = CompositeShape::Primitive(ScalarSliceElement::Bool),
                6 => fields[0].1 = CompositeShape::Tuple(Vec::new()),
                _ => unreachable!(),
            }
            assert!(
                engine
                    .nominal_product_fields_from_shape(original, changed)
                    .is_err()
            );
        }
        for changed in [
            CompositeShape::Primitive(ScalarSliceElement::Bool),
            CompositeShape::Tuple(Vec::new()),
            CompositeShape::Array(Vec::new()),
            CompositeShape::Sum {
                name: "wrong".into(),
                bits: 8,
                signed: false,
                is_option: false,
                variants: Vec::new(),
            },
        ] {
            assert!(
                engine
                    .nominal_product_fields_from_shape(original, changed)
                    .is_err()
            );
        }
    }

    #[test]
    fn fresh_nominal_fields_preserve_legacy_domains_and_refuse_shape_mutations() {
        struct Check {
            checked: bool,
        }
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                let config = miren::ContractConfig::default();
                let engine = Engine::new(
                    tcx,
                    &config,
                    VerificationOptions {
                        all_failures: false,
                        induction: false,
                        startup: false,
                        isolated_startup: false,
                        async_entry: false,
                        limits: miren::AnalysisLimits::default(),
                    },
                );
                let original = |name| {
                    let definition = tcx
                        .mir_keys(())
                        .iter()
                        .copied()
                        .find(|id| {
                            tcx.def_kind(id.to_def_id()) == DefKind::Fn
                                && tcx.item_name(id.to_def_id()).as_str() == name
                        })
                        .unwrap();
                    let signature = tcx
                        .fn_sig(definition)
                        .instantiate_identity()
                        .skip_norm_wip();
                    tcx.instantiate_bound_regions_with_erased(signature)
                        .inputs()[0]
                };
                for (name, accepted) in [
                    ("narrow", true),
                    ("wide", true),
                    ("unrelated", true),
                    ("pair", true),
                    ("nested", true),
                    ("floats", true),
                    ("vacant", true),
                    ("zero", true),
                    ("raw", false),
                    ("borrowed", false),
                    ("interior", false),
                    ("function", false),
                    ("noncopy", false),
                    ("dropping", false),
                    ("packed", false),
                    ("sum", false),
                ] {
                    let original = original(name);
                    let fields = engine.nominal_comparison_fields(original).unwrap();
                    assert_eq!(fields.is_some(), accepted, "{name}");
                    assert_eq!(fields, legacy_fields(&engine, original).unwrap(), "{name}");
                }
                let excessive = original("excessive");
                assert_eq!(
                    engine.nominal_comparison_fields(excessive).unwrap_err(),
                    legacy_fields(&engine, excessive).unwrap_err()
                );
                let narrow = original("narrow");
                changed_root_shapes_refuse(&engine, narrow);
                for name in ["wide", "unrelated"] {
                    let foreign = engine
                        .owned_struct_choice_shape(original(name))
                        .unwrap()
                        .unwrap();
                    assert!(
                        engine
                            .nominal_product_fields_from_shape(narrow, foreign)
                            .is_err()
                    );
                }
                for name in ["bytes", "tuple"] {
                    let original = original(name);
                    let shape = engine.owned_struct_choice_shape(original).unwrap().unwrap();
                    engine
                        .validate_nominal_product_shape(original, &shape)
                        .unwrap();
                    let mut changed = shape;
                    match &mut changed {
                        CompositeShape::Array(fields) | CompositeShape::Tuple(fields) => {
                            fields.pop().unwrap();
                        }
                        CompositeShape::Primitive(_)
                        | CompositeShape::Struct { .. }
                        | CompositeShape::NonZeroNiche(_)
                        | CompositeShape::Sum { .. } => panic!("fresh array or tuple"),
                    }
                    assert!(
                        engine
                            .validate_nominal_product_shape(original, &changed)
                            .is_err()
                    );
                }
                let bytes = original("bytes");
                let mut changed = engine.owned_struct_choice_shape(bytes).unwrap().unwrap();
                let CompositeShape::Array(fields) = &mut changed else {
                    panic!("fresh byte array")
                };
                fields[0] = CompositeShape::Primitive(ScalarSliceElement::Integer {
                    bits: 8,
                    signed: true,
                });
                assert_eq!(
                    engine
                        .validate_nominal_product_shape(bytes, &changed)
                        .unwrap_err(),
                    "owned byte array annotation differs from certified primitive shape"
                );
                let pair = original("pair");
                let mut changed = engine.owned_struct_choice_shape(pair).unwrap().unwrap();
                let CompositeShape::Struct { fields, .. } = &mut changed else {
                    panic!("fresh pair")
                };
                fields.swap(0, 1);
                assert_eq!(
                    engine
                        .nominal_product_fields_from_shape(pair, changed)
                        .unwrap_err(),
                    "owned struct annotation field identity mismatch"
                );
                let nested = original("nested");
                let mut changed = engine.owned_struct_choice_shape(nested).unwrap().unwrap();
                let CompositeShape::Struct { fields, .. } = &mut changed else {
                    panic!("fresh nested product")
                };
                let CompositeShape::Struct { name, .. } = &mut fields[0].1 else {
                    panic!("fresh nested struct")
                };
                name.push_str("::wrong");
                assert!(
                    engine
                        .nominal_product_fields_from_shape(nested, changed)
                        .is_err()
                );
                let floats = original("floats");
                let mut changed = engine.owned_struct_choice_shape(floats).unwrap().unwrap();
                let CompositeShape::Struct { fields, .. } = &mut changed else {
                    panic!("fresh legacy Float product")
                };
                fields[0].1 = CompositeShape::Primitive(ScalarSliceElement::Float { bits: 64 });
                assert!(
                    engine
                        .nominal_product_fields_from_shape(floats, changed)
                        .is_err()
                );
                self.checked = true;
                rustc_driver::Compilation::Stop
            }
        }
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "miren-common-nominal-fields-{}-{nonce}",
            std::process::id(),
        ));
        std::fs::create_dir(&directory).unwrap();
        let source = directory.join("probe.rs");
        std::fs::write(
            &source,
            r#"
#![no_std]
#![forbid(unsafe_code)]
#[derive(Clone, Copy)] pub struct Generic<T> { pub field: T }
#[derive(Clone, Copy)] pub struct Other { pub field: u16 }
#[derive(Clone, Copy)] pub struct Pair { pub left: u16, pub right: u16 }
#[derive(Clone, Copy)] pub struct Nested {
    pub inner: Other, pub data: [u8; 2], pub pair: (bool, u16)
}
#[derive(Clone, Copy)] pub struct Floats {
    pub single: f32, pub double: f64, pub vacant: [f32; 0]
}
#[derive(Clone, Copy)] pub struct Vacant { pub data: [[u16; 0]; 2] }
#[derive(Clone, Copy)] pub struct Zero;
#[derive(Clone, Copy)] pub struct Raw { pub data: [*const u16; 0] }
#[derive(Clone, Copy)] pub struct Borrowed<'a> { pub data: [&'a u16; 0] }
#[derive(Clone, Copy)] pub struct Interior<'a> { pub data: [&'a core::cell::Cell<u16>; 0] }
#[derive(Clone, Copy)] pub struct Function { pub data: [fn(u16) -> u16; 0] }
pub struct Noncopy { pub field: u16 }
pub struct Dropping { pub field: u16 }
impl Drop for Dropping { fn drop(&mut self) {} }
#[derive(Clone, Copy)] #[repr(packed)] pub struct Packed { pub field: u16 }
#[derive(Clone, Copy)] pub enum Sum { Empty, Value(u16) }
#[derive(Clone, Copy)] pub struct Excessive { pub data: [u16; 129] }
pub fn narrow(_: Generic<u16>) {} pub fn wide(_: Generic<u32>) {} pub fn unrelated(_: Other) {}
pub fn pair(_: Pair) {} pub fn nested(_: Nested) {} pub fn floats(_: Floats) {}
pub fn vacant(_: Vacant) {} pub fn zero(_: Zero) {} pub fn raw(_: Raw) {}
pub fn borrowed(_: Borrowed<'_>) {} pub fn noncopy(_: Noncopy) {} pub fn dropping(_: Dropping) {}
pub fn interior(_: Interior<'_>) {} pub fn function(_: Function) {}
pub fn packed(_: Packed) {} pub fn sum(_: Sum) {} pub fn excessive(_: Excessive) {}
pub fn bytes(_: [u8; 2]) {} pub fn tuple(_: (bool, u16)) {}
"#,
        )
        .unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        assert!(sysroot.status.success());
        let sysroot = String::from_utf8(sysroot.stdout).unwrap();
        for level in ["0", "2"] {
            let mut check = Check { checked: false };
            rustc_driver::run_compiler(
                &[
                    "rustc".into(),
                    source.to_str().unwrap().into(),
                    "--crate-type=lib".into(),
                    "--edition=2024".into(),
                    "-Cpanic=abort".into(),
                    format!("-Copt-level={level}"),
                    "--sysroot".into(),
                    sysroot.trim().into(),
                    "--out-dir".into(),
                    directory.to_str().unwrap().into(),
                ],
                &mut check,
            );
            assert!(check.checked);
        }
        std::fs::remove_dir_all(directory).unwrap();
    }
}
