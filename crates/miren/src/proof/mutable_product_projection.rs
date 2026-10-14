//! Invocation-local typed column selection, never owner, reference or frame authority.
use super::*;
use rustc_middle::mir::{Local, PlaceElem};
use std::ops::Range;

pub(super) enum Projection<'a, 'tcx> {
    Direct(Value, Ty<'tcx>, &'a CompositeShape, usize),
    Symbolic(Selection<'a, 'tcx>),
}

pub(super) struct Source<'a, 'tcx> {
    pub(super) body: &'a Body<'tcx>,
    pub(super) state: &'a State,
    pub(super) place: Place<'tcx>,
}

pub(super) struct Seed<'a, 'tcx> {
    pub(super) outer: Value,
    pub(super) original: Ty<'tcx>,
    pub(super) shape: &'a CompositeShape,
    pub(super) start: usize,
    pub(super) first: Value,
    pub(super) suffix: &'a [PlaceElem<'tcx>],
    pub(super) columns: usize,
    pub(super) prefix_scan: usize,
}

struct Budget(usize);
impl Budget {
    fn charge(&mut self, engine: &Engine<'_>, count: usize) -> Result<(), String> {
        self.0 = self.0.checked_add(count).ok_or_else(|| resource(engine))?;
        if self.0 > typed_array_choices::MAX_CHOICE_NODES {
            return Err(resource(engine));
        }
        Ok(())
    }
}
fn resource(engine: &Engine<'_>) -> String {
    engine.categorized_error(
        UnknownCategory::ResourceLimit,
        "mutable product symbolic projection exceeds its shared node or depth budget".into(),
    )
}

struct Target<'a, 'tcx> {
    original: Ty<'tcx>,
    shape: &'a CompositeShape,
    span: Range<usize>,
    mask: Term,
}

// Non-Clone and never stored in Engine/Memory. The caller retains the current backing borrow.
pub(super) struct Selection<'a, 'tcx> {
    outer: Value,
    targets: Vec<Target<'a, 'tcx>>,
    columns: usize,
    budget: Budget,
}

struct Path<'a, 'tcx> {
    original: Ty<'tcx>,
    shape: &'a CompositeShape,
    suffix: &'a [PlaceElem<'tcx>],
    start: usize,
    depth: usize,
    mask: Option<Term>,
}

struct Walk<'a, 'tcx> {
    indices: BTreeMap<Local, Value>,
    expected: Ty<'tcx>,
    targets: Vec<Target<'a, 'tcx>>,
    budget: Budget,
}

fn inventory(
    engine: &Engine<'_>,
    shape: &CompositeShape,
    depth: usize,
    budget: &mut Budget,
) -> Result<usize, String> {
    budget.charge(engine, 1)?;
    if depth >= typed_array_choices::MAX_CHOICE_DEPTH {
        return Err(resource(engine));
    }
    match shape {
        CompositeShape::Primitive(_) | CompositeShape::NonZeroNiche(_) => Ok(1),
        CompositeShape::Tuple(children) | CompositeShape::Array(children) => {
            let mut count = 0usize;
            for child in children {
                count = count
                    .checked_add(inventory(engine, child, depth + 1, budget)?)
                    .ok_or_else(|| resource(engine))?;
            }
            Ok(count)
        }
        CompositeShape::Struct { fields, .. } => {
            let mut count = 0usize;
            for (_, child) in fields {
                count = count
                    .checked_add(inventory(engine, child, depth + 1, budget)?)
                    .ok_or_else(|| resource(engine))?;
            }
            Ok(count)
        }
        CompositeShape::Sum { .. } => {
            Err("mutable product symbolic projection requires pure original storage".into())
        }
    }
}

pub(super) fn prepare<'a, 'tcx>(
    engine: &Engine<'tcx>,
    source: Source<'_, 'tcx>,
    seed: Seed<'a, 'tcx>,
) -> Result<Selection<'a, 'tcx>, String> {
    let Some(ProjectionElem::Index(first)) = seed.suffix.first() else {
        return Err("mutable product symbolic selection lost its actual Index".into());
    };
    let mut walk = Walk {
        indices: BTreeMap::new(),
        expected: source.place.ty(&source.body.local_decls, engine.tcx).ty,
        targets: Vec::new(),
        budget: Budget(0),
    };
    walk.budget.charge(engine, seed.prefix_scan)?;
    walk.indices.insert(*first, seed.first);
    // Capture initialized index locals exactly once. Never execute an operand or consume a local.
    for projection in seed.suffix {
        walk.budget.charge(engine, 1)?;
        if let ProjectionElem::Index(local) = projection {
            if source.body.local_decls[*local].ty != engine.tcx.types.usize {
                return Err("mutable product suffix requires original compiler usize".into());
            }
            if !walk.indices.contains_key(local) {
                walk.budget.charge(engine, 1)?;
                walk.indices
                    .insert(*local, engine.local(source.state, local.as_usize())?);
            }
        }
    }
    walk.visit(
        engine,
        &source,
        Path {
            original: seed.original,
            shape: seed.shape,
            suffix: seed.suffix,
            start: seed.start,
            depth: seed.prefix_scan - 1,
            mask: None,
        },
    )?;
    let mut result = Selection {
        outer: seed.outer,
        targets: walk.targets,
        columns: seed.columns,
        budget: walk.budget,
    };
    result.validate(engine, &source.state.conditions)?;
    Ok(result)
}

impl<'a, 'tcx> Walk<'a, 'tcx> {
    fn visit(
        &mut self,
        engine: &Engine<'tcx>,
        source: &Source<'_, 'tcx>,
        path: Path<'a, 'tcx>,
    ) -> Result<(), String> {
        self.budget.charge(engine, 1)?;
        if path.depth >= typed_array_choices::MAX_CHOICE_DEPTH {
            return Err(resource(engine));
        }
        let Some((projection, rest)) = path.suffix.split_first() else {
            if path.original != self.expected {
                return Err(
                    "mutable product symbolic target differs from original place Ty".into(),
                );
            }
            let width = inventory(engine, path.shape, 0, &mut self.budget)?;
            self.budget.charge(engine, 1)?;
            self.targets.push(Target {
                original: path.original,
                shape: path.shape,
                span: path.start
                    ..path
                        .start
                        .checked_add(width)
                        .ok_or_else(|| resource(engine))?,
                mask: path
                    .mask
                    .ok_or("mutable product target lacks its actual index mask")?,
            });
            return Ok(());
        };
        match (projection, path.original.kind(), path.shape) {
            (
                ProjectionElem::Field(field, recorded),
                ty::Tuple(types),
                CompositeShape::Tuple(fields),
            ) if types.len() == fields.len() => {
                let position = field.as_usize();
                let original = *types
                    .get(position)
                    .ok_or("mutable product tuple field differs")?;
                if original != *recorded {
                    return Err("mutable product original FieldTy differs".into());
                }
                let mut start = path.start;
                for child in fields.iter().take(position) {
                    start = start
                        .checked_add(inventory(engine, child, 0, &mut self.budget)?)
                        .ok_or_else(|| resource(engine))?;
                }
                self.visit(
                    engine,
                    source,
                    Path {
                        original,
                        shape: fields
                            .get(position)
                            .ok_or("mutable product tuple inventory differs")?,
                        suffix: rest,
                        start,
                        depth: path.depth + 1,
                        mask: path.mask,
                    },
                )
            }
            (
                ProjectionElem::Field(field, recorded),
                ty::Adt(def, args),
                CompositeShape::Struct { name, fields },
            ) if def.is_struct()
                && def.did().is_local()
                && engine.tcx.def_path_str(def.did()) == *name
                && def.non_enum_variant().fields.len() == fields.len() =>
            {
                let position = field.as_usize();
                let declared = &def.non_enum_variant().fields;
                for (field, (name, _)) in declared.iter().zip(fields) {
                    self.budget.charge(engine, 1)?;
                    if field.name.as_str() != name {
                        return Err("mutable product original struct field identity differs".into());
                    }
                }
                let original = declared
                    .get(*field)
                    .ok_or("mutable product struct field differs")?
                    .ty(engine.tcx, args)
                    .skip_norm_wip();
                if original != *recorded {
                    return Err("mutable product original FieldTy differs".into());
                }
                let mut start = path.start;
                for (_, child) in fields.iter().take(position) {
                    start = start
                        .checked_add(inventory(engine, child, 0, &mut self.budget)?)
                        .ok_or_else(|| resource(engine))?;
                }
                self.visit(
                    engine,
                    source,
                    Path {
                        original,
                        shape: &fields
                            .get(position)
                            .ok_or("mutable product struct inventory differs")?
                            .1,
                        suffix: rest,
                        start,
                        depth: path.depth + 1,
                        mask: path.mask,
                    },
                )
            }
            (
                ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. },
                ty::Array(element, count),
                CompositeShape::Array(children),
            ) => {
                if count.try_to_target_usize(engine.tcx) != Some(children.len() as u64) {
                    return Err("mutable product symbolic array count differs from original".into());
                }
                let bits = u32::from(engine.tcx.sess.target.pointer_width);
                let length = symbolic::integer(&engine.terms, children.len() as u128, bits, false);
                let value = match projection {
                    ProjectionElem::Index(local) => self
                        .indices
                        .get(local)
                        .ok_or("mutable product lacks captured current index")?
                        .clone(),
                    ProjectionElem::ConstantIndex {
                        offset,
                        min_length,
                        from_end,
                    } => engine.product_constant_index(
                        *offset,
                        *min_length,
                        *from_end,
                        &length,
                        &source.state.conditions,
                    )?,
                    _ => unreachable!(),
                };
                let fixed = typed_array_choices::fixed_index_value(&engine.terms, &value, bits)?;
                engine.memory_bounds(&value, &length, &source.state.conditions)?;
                let term = value.integer()?.0;
                let mut start = path.start;
                for (position, child) in children.iter().enumerate() {
                    self.budget.charge(engine, 1)?;
                    let width = inventory(engine, child, 0, &mut self.budget)?;
                    if fixed.is_none_or(|fixed| fixed == position) {
                        let mask = if fixed.is_none() {
                            self.budget.charge(engine, 1)?;
                            let equal = engine.terms.apply(
                                Op::Equal,
                                &[
                                    term.clone(),
                                    engine.terms.bit_vector(position as u128, bits)?,
                                ],
                            )?;
                            match &path.mask {
                                Some(parent) => {
                                    self.budget.charge(engine, 1)?;
                                    Some(engine.terms.apply(Op::And, &[parent.clone(), equal])?)
                                }
                                None => Some(equal),
                            }
                        } else {
                            path.mask.clone()
                        };
                        self.visit(
                            engine,
                            source,
                            Path {
                                original: *element,
                                shape: child,
                                suffix: rest,
                                start,
                                depth: path.depth + 1,
                                mask,
                            },
                        )?;
                    }
                    start = start.checked_add(width).ok_or_else(|| resource(engine))?;
                }
                if fixed.is_some_and(|fixed| fixed >= children.len()) {
                    return Err("mutable product suffix index outside original array".into());
                }
                Ok(())
            }
            _ => {
                Err("mutable product symbolic suffix needs exact pure fields/array indices".into())
            }
        }
    }
}

impl<'tcx> Selection<'_, 'tcx> {
    fn validate(&mut self, engine: &Engine<'tcx>, conditions: &[Term]) -> Result<(), String> {
        let first = self
            .targets
            .first()
            .ok_or("mutable product selection has no target")?;
        let original = first.original;
        let shape = first.shape;
        let width = first.span.len();
        self.budget.charge(engine, self.targets.len())?;
        let spans = self
            .targets
            .iter()
            .map(|target| target.span.clone())
            .collect::<Vec<_>>();
        typed_array_choices::validate_indexed_spans(&spans, self.columns, width)?;
        let mut covered = engine.terms.boolean(false);
        for target in &self.targets {
            self.budget.charge(engine, 2)?;
            if target.original != original
                || !same_shape(engine, target.shape, shape, &mut self.budget)?
                || target.mask.sort() != &Sort::Bool
                || !target.mask.belongs_to(&engine.terms)
            {
                return Err("mutable product targets differ in type, shape or mask Context".into());
            }
            covered = engine
                .terms
                .apply(Op::Or, &[covered, target.mask.clone()])?;
        }
        self.budget.charge(engine, conditions.len() + 1)?;
        let mut uncovered = conditions.to_vec();
        uncovered.push(symbolic::not(&covered));
        if engine.feasible(&uncovered)? {
            return Err("mutable product target masks do not cover the current path".into());
        }
        Ok(())
    }

    pub(super) fn read(
        &mut self,
        engine: &Engine<'tcx>,
        columns: &[Term],
        _conditions: &[Term],
    ) -> Result<Value, String> {
        if columns.len() != self.columns {
            return Err("mutable product current column inventory differs".into());
        }
        let first = self.targets.first().unwrap();
        self.budget.charge(engine, first.span.len())?;
        let mut selected = columns[first.span.clone()].to_vec();
        for target in self.targets.iter().skip(1) {
            for (relative, slot) in selected.iter_mut().enumerate() {
                self.budget.charge(engine, 1)?;
                *slot = engine.terms.apply(
                    Op::Ite,
                    &[
                        target.mask.clone(),
                        columns[target.span.start + relative].clone(),
                        slot.clone(),
                    ],
                )?;
            }
        }
        charge_traversal(engine, first.shape, &mut self.budget)?;
        let mut cursor = 0;
        let value = first.shape.observe(
            &engine.terms,
            &selected,
            &self.outer.integer()?.0,
            &mut cursor,
        )?;
        if cursor != selected.len() {
            return Err("mutable product symbolic read omitted typed columns".into());
        }
        Ok(value)
    }

    pub(super) fn store(
        &mut self,
        engine: &Engine<'tcx>,
        columns: &[Term],
        value: &Value,
        conditions: &[Term],
    ) -> Result<Vec<Term>, String> {
        if columns.len() != self.columns {
            return Err("mutable product current column inventory differs".into());
        }
        let first = self.targets.first().unwrap();
        charge_traversal(engine, first.shape, &mut self.budget)?;
        let mut replacements = Vec::new();
        engine.product_replacements(
            first.original,
            first.shape,
            value,
            conditions,
            &mut replacements,
        )?;
        if replacements.len() != first.span.len() {
            return Err("mutable product symbolic store omitted typed leaves".into());
        }
        self.budget.charge(engine, columns.len())?;
        let mut next = columns.to_vec();
        for target in &self.targets {
            for (relative, replacement) in replacements.iter().enumerate() {
                self.budget.charge(engine, 2)?;
                let position = target.span.start + relative;
                let stored = engine.terms.apply(
                    Op::Store,
                    &[
                        columns[position].clone(),
                        self.outer.integer()?.0,
                        replacement.clone(),
                    ],
                )?;
                next[position] = engine.terms.apply(
                    Op::Ite,
                    &[target.mask.clone(), stored, columns[position].clone()],
                )?;
            }
        }
        Ok(next)
    }
}

fn charge_traversal(
    engine: &Engine<'_>,
    shape: &CompositeShape,
    budget: &mut Budget,
) -> Result<(), String> {
    let before = budget.0;
    inventory(engine, shape, 0, budget)?;
    // This same budget pays the actual inventory pass and the forthcoming typed traversal.
    budget.charge(engine, budget.0 - before)
}

fn same_shape(
    engine: &Engine<'_>,
    left: &CompositeShape,
    right: &CompositeShape,
    budget: &mut Budget,
) -> Result<bool, String> {
    budget.charge(engine, 1)?;
    match (left, right) {
        (CompositeShape::Primitive(left), CompositeShape::Primitive(right)) => Ok(left == right),
        (CompositeShape::Tuple(left), CompositeShape::Tuple(right))
        | (CompositeShape::Array(left), CompositeShape::Array(right)) => {
            if left.len() != right.len() {
                return Ok(false);
            }
            for (left, right) in left.iter().zip(right) {
                if !same_shape(engine, left, right, budget)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (
            CompositeShape::Struct {
                name: left_name,
                fields: left,
            },
            CompositeShape::Struct {
                name: right_name,
                fields: right,
            },
        ) => {
            if left_name != right_name || left.len() != right.len() {
                return Ok(false);
            }
            for ((left_name, left), (right_name, right)) in left.iter().zip(right) {
                if left_name != right_name || !same_shape(engine, left, right, budget)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (
            CompositeShape::Primitive(_)
            | CompositeShape::Tuple(_)
            | CompositeShape::Array(_)
            | CompositeShape::Struct { .. }
            | CompositeShape::NonZeroNiche(_)
            | CompositeShape::Sum { .. },
            _,
        ) => Ok(false),
    }
}

#[cfg(test)]
#[path = "mutable_product_projection_probe.rs"]
mod probe;
