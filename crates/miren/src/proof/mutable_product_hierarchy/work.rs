//! Work for concrete observations and owned clones in an active Product lineage.
use super::*;
use rustc_middle::mir::visit::Visitor;

#[derive(Default)]
struct OperandInventory {
    reads: usize,
    projections: usize,
}

impl<'tcx> Visitor<'tcx> for OperandInventory {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: rustc_middle::mir::Location) {
        self.reads = self.reads.saturating_add(1);
        self.super_operand(operand, location);
    }
    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        _: rustc_middle::mir::visit::PlaceContext,
        _: rustc_middle::mir::Location,
    ) {
        self.projections = self.projections.saturating_add(place.projection.len());
    }
}

struct ClonePlan {
    nodes: usize,
}

struct DescriptorPlan {
    nodes: usize,
    names: usize,
}

impl DescriptorPlan {
    fn name(&mut self, engine: &mut Engine<'_>, bytes: usize) -> Result<usize, String> {
        pay(engine, 4)?;
        self.names = self
            .names
            .checked_add(bytes)
            .ok_or("product type metadata overflow")?;
        if self.names > MAX_INPUT_VALUES {
            return Err("product type names exceed existing metadata bound".into());
        }
        Ok(bytes + 4)
    }

    fn path(&mut self, engine: &mut Engine<'_>, id: DefId) -> Result<usize, String> {
        self.path_depth(engine, id, 0)
    }

    fn path_depth(
        &mut self,
        engine: &mut Engine<'_>,
        id: DefId,
        depth: usize,
    ) -> Result<usize, String> {
        let raw = self.raw_path_depth(engine, id, depth)?;
        let visible = self.visible_path(engine, id, depth)?.unwrap_or(0);
        pay(engine, 4)?;
        let trimmed = if engine.tcx.sess.opts.unstable_opts.trim_diagnostic_paths
            && engine.tcx.sess.opts.trimmed_def_paths
        {
            engine.tcx.trimmed_def_paths(()).get(&id).copied()
        } else {
            None
        };
        let trimmed = match trimmed {
            Some(name) => self.name(engine, name.as_str().len())? + 4,
            None => 0,
        };
        Ok(raw.max(visible).max(trimmed))
    }

    fn raw_path_depth(
        &mut self,
        engine: &mut Engine<'_>,
        mut id: DefId,
        depth: usize,
    ) -> Result<usize, String> {
        if depth >= MAX_INPUT_DEPTH {
            return Err("product printed path exceeds existing depth budget".into());
        }
        let mut work = 0usize;
        for _ in 0..MAX_INPUT_DEPTH {
            pay(engine, 6)?;
            let key = engine.tcx.def_key(id);
            if key.disambiguated_data.data == rustc_hir::definitions::DefPathData::Impl {
                // The compiler prints impl self/trait types, not just an anonymous namespace.
                // Plan their actual identity arguments before def_path_str can allocate names.
                pay(engine, 8)?;
                let self_ty = engine
                    .tcx
                    .type_of(id)
                    .instantiate_identity()
                    .skip_norm_wip();
                work += self.printed_original(engine, self_ty, depth + 1)?;
                if matches!(engine.tcx.def_kind(id), DefKind::Impl { of_trait: true }) {
                    let trait_ref = engine
                        .tcx
                        .impl_trait_ref(id)
                        .instantiate_identity()
                        .skip_norm_wip();
                    work += self.path_depth(engine, trait_ref.def_id, depth + 1)?;
                    work += self.printed_arguments(engine, &trait_ref.args[1..], depth + 1)?;
                }
            }
            if let Some(name) = key.disambiguated_data.data.get_opt_name() {
                work += self.name(engine, name.as_str().len())?;
            } else if key.parent.is_some() {
                let rustc_hir::definitions::DefPathDataName::Anon { namespace } =
                    key.disambiguated_data.data.name()
                else {
                    return Err("product definition path name classification differs".into());
                };
                work += self.name(engine, namespace.as_str().len())?;
                if let rustc_hir::definitions::DefPathData::AnonAssocTy(method) =
                    key.disambiguated_data.data
                {
                    work += self.name(engine, method.as_str().len())?;
                }
            }
            work += 64; // Separators/disambiguators of each admitted named definition component.
            let Some(parent) = key.parent else {
                pay(engine, 4)?;
                work += self.name(engine, engine.tcx.crate_name(id.krate).as_str().len())?;
                return Ok(work);
            };
            id.index = parent;
        }
        Err("product type definition path exceeds existing depth".into())
    }

    fn visible_path(
        &mut self,
        engine: &mut Engine<'_>,
        mut id: DefId,
        depth: usize,
    ) -> Result<Option<usize>, String> {
        use rustc_hir::definitions::DefPathData;
        use rustc_span::def_id::ModId;
        if depth >= MAX_INPUT_DEPTH {
            return Err("product visible path exceeds existing nesting bound".into());
        }
        if id.is_local() {
            return Ok(None);
        }
        let mut work = 0usize;
        let mut visited = [None; MAX_INPUT_DEPTH];
        for position in 0..MAX_INPUT_DEPTH {
            pay(engine, 16)?;
            if visited[..position].contains(&Some(id)) {
                return Ok(None);
            }
            visited[position] = Some(id);
            if id.as_crate_root().is_some() {
                pay(engine, 8)?;
                let external = engine.tcx.extern_crate(id.krate).copied();
                // An indirect crate can instead be reached through a visible reexport parent.
                if external.is_none_or(|external| external.is_direct()) {
                    let ordinary =
                        self.name(engine, engine.tcx.crate_name(id.krate).as_str().len())?;
                    let explicit = if let Some(external) = external
                        && !external.span.is_dummy()
                        && let rustc_crate_store::ExternCrateSource::Extern(alias) = external.src
                    {
                        self.raw_path_depth(engine, alias, depth + 1)?
                    } else {
                        0
                    };
                    return Ok(Some(work + ordinary.max(explicit) + 4));
                }
            }
            if id.is_local() {
                return Ok(Some(work + self.raw_path_depth(engine, id, depth + 1)?));
            }
            let key = engine.tcx.def_key(id);
            let parents = engine.tcx.visible_parent_map(());
            let Some(parent) = parents.get(&id).copied() else {
                return Ok(None);
            };
            let mut data = key.disambiguated_data.data;
            if matches!(data, DefPathData::Ctor) {
                let actual_parent = engine
                    .tcx
                    .opt_parent(id)
                    .ok_or("product visible constructor parent absent")?;
                data = engine.tcx.def_key(actual_parent).disambiguated_data.data;
            }
            let name = match data {
                DefPathData::TypeNs(_) if engine.tcx.opt_parent(id) != Some(parent) => {
                    pay(engine, 8)?;
                    let children = engine.tcx.module_children(ModId::new_unchecked(parent));
                    if children.len() > MAX_INPUT_VALUES {
                        return Err(
                            "product visible reexport catalogue exceeds existing512 bound".into(),
                        );
                    }
                    pay(engine, children.len() + 4)?;
                    let Some(name) = children
                        .iter()
                        .find(|child| {
                            child.res.opt_def_id() == Some(id)
                                && child.vis.is_public()
                                && child.ident.name != rustc_span::kw::Underscore
                        })
                        .map(|child| child.ident.name)
                    else {
                        return Ok(None);
                    };
                    Some(name)
                }
                DefPathData::CrateRoot => Some(engine.tcx.crate_name(id.krate)),
                _ => data.get_opt_name(),
            };
            if let Some(name) = name {
                work += self.name(engine, name.as_str().len())? + 4;
            } else if !matches!(data, DefPathData::ForeignMod | DefPathData::Ctor) {
                let rustc_hir::definitions::DefPathDataName::Anon { namespace } = data.name()
                else {
                    return Err("product visible path component classification differs".into());
                };
                work += self.name(engine, namespace.as_str().len())? + 64;
                if let DefPathData::AnonAssocTy(method) = data {
                    work += self.name(engine, method.as_str().len())? + 4;
                }
            }
            id = parent;
        }
        Err("product visible path exceeds existing16 parent bound".into())
    }

    fn printed_arguments<'tcx>(
        &mut self,
        engine: &mut Engine<'tcx>,
        arguments: &[ty::GenericArg<'tcx>],
        depth: usize,
    ) -> Result<usize, String> {
        if arguments.len() > MAX_INPUT_VALUES || depth >= MAX_INPUT_DEPTH {
            return Err("product impl printed arguments exceed existing bounds".into());
        }
        pay(engine, 4 + arguments.len())?;
        let mut work = 16usize;
        for argument in arguments {
            work += match argument.kind() {
                ty::GenericArgKind::Type(original) => {
                    self.printed_original(engine, original, depth + 1)?
                }
                ty::GenericArgKind::Lifetime(region) => self.printed_region(engine, region)?,
                ty::GenericArgKind::Const(value) => self.printed_constant(engine, value)?,
            } + 4;
        }
        Ok(work)
    }

    fn printed_region<'tcx>(
        &mut self,
        engine: &mut Engine<'tcx>,
        region: ty::Region<'tcx>,
    ) -> Result<usize, String> {
        pay(engine, 4)?;
        match region.kind() {
            ty::ReEarlyParam(parameter) => {
                Ok(8 + self.name(engine, parameter.name.as_str().len())?)
            }
            ty::ReStatic | ty::ReErased => Ok(16),
            _ => Err("product impl path region printer is unsupported".into()),
        }
    }

    fn printed_constant<'tcx>(
        &mut self,
        engine: &mut Engine<'tcx>,
        value: ty::Const<'tcx>,
    ) -> Result<usize, String> {
        pay(engine, 6)?;
        if let ty::ConstKind::Param(parameter) = value.kind() {
            return Ok(8 + self.name(engine, parameter.name.as_str().len())?);
        }
        if value.try_to_target_usize(engine.tcx).is_some() {
            // Existing target-usize constants have at most 39 decimal digits.
            return Ok(64);
        }
        Err("product impl path constant printer is unsupported".into())
    }

    fn printed_original<'tcx>(
        &mut self,
        engine: &mut Engine<'tcx>,
        original: Ty<'tcx>,
        depth: usize,
    ) -> Result<usize, String> {
        if depth >= MAX_INPUT_DEPTH || self.nodes >= MAX_INPUT_VALUES {
            return Err("product impl printed type exceeds existing expanded bounds".into());
        }
        pay(engine, 12)?;
        self.nodes += 1;
        let mut work = 64usize;
        match original.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str | ty::Never => {
            }
            ty::Param(parameter) => work += self.name(engine, parameter.name.as_str().len())?,
            ty::Tuple(fields) => {
                if fields.len() > MAX_INPUT_VALUES {
                    return Err("product impl printed tuple exceeds existing bound".into());
                }
                pay(engine, fields.len())?;
                for field in fields.iter() {
                    work += self.printed_original(engine, field, depth + 1)?;
                }
            }
            ty::Array(element, count) => {
                work += self.printed_original(engine, *element, depth + 1)?;
                work += self.printed_constant(engine, *count)?;
            }
            ty::Slice(element) | ty::RawPtr(element, _) => {
                work += self.printed_original(engine, *element, depth + 1)?;
            }
            ty::Ref(region, element, _) => {
                work += self.printed_region(engine, *region)?;
                work += self.printed_original(engine, *element, depth + 1)?;
            }
            ty::Adt(definition, arguments) => {
                work += self.path_depth(engine, definition.did(), depth + 1)?;
                work += self.printed_arguments(engine, arguments, depth + 1)?;
            }
            _ => return Err("product impl self/trait type printer is unsupported".into()),
        }
        Ok(work)
    }

    fn original<'tcx>(
        &mut self,
        engine: &mut Engine<'tcx>,
        original: Ty<'tcx>,
        depth: usize,
    ) -> Result<usize, String> {
        if depth >= MAX_INPUT_DEPTH || self.nodes >= MAX_INPUT_VALUES {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "product descriptor plan exceeds existing expanded type limits".into(),
            ));
        }
        pay(engine, 12)?;
        self.nodes += 1;
        // Freeze/Copy/Drop/layout/codec queries, owned shape construction and the subsequent
        // originals/leaf/shape/leaf-list comparisons are separate future services.
        let mut work = 64usize;
        match original.kind() {
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64) => {}
            ty::Tuple(fields) => {
                if fields.len() > MAX_INPUT_VALUES {
                    return Err("product descriptor tuple exceeds existing bound".into());
                }
                pay(engine, fields.len())?;
                for field in fields.iter() {
                    work += self.original(engine, field, depth + 1)?;
                }
            }
            ty::Array(element, count) => {
                pay(engine, 4)?;
                let count = count
                    .try_to_target_usize(engine.tcx)
                    .ok_or("product descriptor original array extent unavailable")?;
                if count > 128 {
                    return Err("product descriptor array exceeds existing 128 bound".into());
                }
                pay(engine, count as usize + 1)?;
                // The existing descriptor probes the element of a zero-length array as well.
                for _ in 0..count.max(1) {
                    work += self.original(engine, *element, depth + 1)?;
                }
            }
            ty::Adt(definition, arguments)
                if definition.is_struct() && definition.did().is_local() =>
            {
                work += self.path(engine, definition.did())?;
                let fields = &definition.non_enum_variant().fields;
                if fields.len() > MAX_INPUT_VALUES {
                    return Err("product descriptor fields exceed existing bound".into());
                }
                pay(engine, fields.len())?;
                for field in fields {
                    work += self.name(engine, field.name.as_str().len())?;
                    pay(engine, 4)?;
                    let original = field.ty(engine.tcx, arguments).skip_norm_wip();
                    work += self.original(engine, original, depth + 1)?;
                }
            }
            _ => return Err("product descriptor plan has unsupported original type".into()),
        }
        Ok(work)
    }
}

pub(in crate::proof) fn descriptor_work<'tcx>(
    engine: &mut Engine<'tcx>,
    original: Ty<'tcx>,
) -> Result<usize, String> {
    let mut plan = DescriptorPlan { nodes: 0, names: 0 };
    Ok(24 + plan.original(engine, original, 0)?)
}

struct IncomingPlan {
    nodes: usize,
    visited: Vec<usize>,
}

impl IncomingPlan {
    fn value(
        &mut self,
        engine: &mut Engine<'_>,
        value: &Value,
        memory: &Memory,
        depth: usize,
    ) -> Result<usize, String> {
        if depth >= MAX_INPUT_DEPTH || self.nodes >= MAX_INPUT_VALUES {
            return Err("product incoming graph exceeds existing node/depth limits".into());
        }
        pay(engine, 6)?;
        self.nodes += 1;
        match value {
            Value::Unit
            | Value::Uninitialized
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::MutableU16 { .. } => Ok(32),
            Value::Reference {
                allocation,
                projection,
                ..
            } => {
                if projection.len() > MAX_INPUT_DEPTH || *allocation >= memory.len() {
                    return Err("product incoming reference source/path exceeds bounds".into());
                }
                pay(engine, self.visited.len() + projection.len() + 4)?;
                let mut work = 64 + 3 * self.visited.len() + 32 * projection.len();
                let mut clones = ClonePlan { nodes: 0 };
                work += clones.value(engine, value, 0)?;
                if !self.visited.contains(allocation) {
                    pay(engine, 4)?;
                    self.visited.push(*allocation);
                    if let Some(Some(value)) = memory.get(*allocation) {
                        work += self.value(engine, value, memory, depth + 1)?;
                    }
                }
                Ok(work)
            }
            Value::Elements(values) => {
                if values.len() > MAX_INPUT_VALUES {
                    return Err("product incoming element catalogue exceeds existing bound".into());
                }
                pay(engine, values.len() + 4)?;
                let mut work = 32 + 3 * values.len();
                for value in values.iter() {
                    work += self.value(engine, value, memory, depth + 1)?;
                }
                Ok(work)
            }
            Value::OwnedArrayIterator { .. }
            | Value::OwnedRegion { .. }
            | Value::OwnedSnapshot(_)
            | Value::MaybeUninit { .. }
            | Value::StaticSlice { .. }
            | Value::StaticView { .. }
            | Value::RawPointer { .. }
            | Value::TrackedPointer { .. }
            | Value::RawSlice { .. }
            | Value::Input(_)
            | Value::Bytes { .. }
            | Value::CompositeSlice { .. }
            | Value::ScalarSlice { .. }
            | Value::Adt { .. }
            | Value::Enum { .. }
            | Value::Cell { .. }
            | Value::Atomic { .. }
            | Value::LocalAtomic { .. }
            | Value::SliceIterator { .. }
            | Value::Tuple(_)
            | Value::MetadataPointer(_)
            | Value::TraitObject { .. }
            | Value::DebugReference { .. }
            | Value::StaticText
            | Value::FormatArguments
            | Value::FunctionPointer { .. }
            | Value::Function => Err(format!(
                "product incoming graph requires an additional bounded protocol: {:?}",
                std::mem::discriminant(value)
            )),
        }
    }
}

impl ClonePlan {
    fn value(
        &mut self,
        engine: &mut Engine<'_>,
        value: &Value,
        depth: usize,
    ) -> Result<usize, String> {
        if depth >= MAX_INPUT_DEPTH || self.nodes >= MAX_INPUT_VALUES {
            return Err(engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "product owned clone exceeds existing graph bounds".into(),
            ));
        }
        pay(engine, 4)?;
        self.nodes += 1;
        let mut work = 8usize;
        match value {
            Value::OwnedSnapshot(value)
            | Value::MetadataPointer(value)
            | Value::DebugReference { source: value, .. }
            | Value::TraitObject { source: value, .. } => {
                work += self.value(engine, value, depth + 1)?;
            }
            Value::MaybeUninit { payload, .. } => {
                if let Some(value) = payload {
                    work += self.value(engine, value, depth + 1)?;
                }
            }
            Value::Bytes { length, .. } | Value::ScalarSlice { length, .. } => {
                work += self.value(engine, length, depth + 1)?;
            }
            Value::CompositeSlice { length, leaves, .. } => {
                if leaves.len() > MAX_INPUT_VALUES {
                    return Err("product clone leaf vector exceeds existing bound".into());
                }
                work += leaves.len() + self.value(engine, length, depth + 1)?;
            }
            Value::RawSlice { source, length } => {
                work += self.value(engine, source, depth + 1)?;
                work += self.value(engine, length, depth + 1)?;
            }
            Value::TrackedPointer { reference, .. } => {
                work += self.value(engine, reference, depth + 1)?;
            }
            Value::Tuple(values)
            | Value::Enum {
                variants: values, ..
            } => {
                if values.len() > MAX_INPUT_VALUES {
                    return Err("product clone field vector exceeds existing bound".into());
                }
                pay(engine, values.len())?;
                work += values.len();
                for value in values {
                    work += self.value(engine, value, depth + 1)?;
                }
                if let Value::Enum { discriminant, .. } = value {
                    work += self.value(engine, discriminant, depth + 1)?;
                }
            }
            Value::Adt { name, fields, .. } => {
                if name.len() > MAX_INPUT_VALUES {
                    return Err("product clone ADT name exceeds existing bound".into());
                }
                work += name.len();
                if fields.len() > MAX_INPUT_VALUES {
                    return Err("product projection field catalogue exceeds existing bound".into());
                }
                pay(engine, fields.len())?;
                for (name, field) in fields.iter() {
                    if name.len() > MAX_INPUT_VALUES {
                        return Err("product projection field name exceeds existing bound".into());
                    }
                    work += name.len() + 4 + self.value(engine, field, depth + 1)?;
                }
            }
            Value::Elements(fields) => {
                if fields.len() > MAX_INPUT_VALUES {
                    return Err(
                        "product projection element catalogue exceeds existing bound".into(),
                    );
                }
                pay(engine, fields.len())?;
                for field in fields.iter() {
                    work += 4 + self.value(engine, field, depth + 1)?;
                }
            }
            Value::MutableU16 {
                role: MutableU16Role::Ghost { length, .. },
                ..
            } => {
                work += self.value(engine, length, depth + 1)?;
            }
            Value::Reference { projection, .. } => {
                if projection.len() > MAX_INPUT_DEPTH {
                    return Err("product clone reference projection exceeds existing depth".into());
                }
                pay(engine, projection.len())?;
                work += projection.len() * 4;
                for step in projection {
                    match step {
                        symbolic::MemoryProjection::Index(index)
                        | symbolic::MemoryProjection::TypedIndex { index, .. } => {
                            work += self.value(engine, index, depth + 1)?;
                        }
                        symbolic::MemoryProjection::Slice { offset, length } => {
                            work += self.value(engine, offset, depth + 1)?;
                            work += self.value(engine, length, depth + 1)?;
                        }
                        symbolic::MemoryProjection::Field(_)
                        | symbolic::MemoryProjection::Variant(_)
                        | symbolic::MemoryProjection::Chunks { .. } => {}
                    }
                }
            }
            Value::StaticSlice { .. }
            | Value::SliceIterator { .. }
            | Value::OwnedArrayIterator { .. } => {
                return Err("product clone has unsupported owning adapter state".into());
            }
            Value::MutableU16 { .. }
            | Value::OwnedRegion { .. }
            | Value::Uninitialized
            | Value::StaticView { .. }
            | Value::RawPointer { .. }
            | Value::Input(_)
            | Value::Bool(_)
            | Value::Int { .. }
            | Value::Float { .. }
            | Value::Cell { .. }
            | Value::Atomic { .. }
            | Value::LocalAtomic { .. }
            | Value::StaticText
            | Value::FormatArguments
            | Value::FunctionPointer { .. }
            | Value::Function
            | Value::Unit => {}
        }
        Ok(work)
    }
}

fn masks(
    engine: &mut Engine<'_>,
    masks: &initialized_places::MissingPlaces,
) -> Result<usize, String> {
    if masks.entries().len() > MAX_INPUT_VALUES {
        return Err("product clone initialization masks exceed existing bound".into());
    }
    pay(engine, masks.entries().len() + 1)?;
    masks.entries().iter().try_fold(0usize, |work, (_, path)| {
        if path.len() > MAX_INPUT_DEPTH {
            return Err("product clone initialization path exceeds existing depth".into());
        }
        Ok(work + 3 + path.len())
    })
}

impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn mutable_product_statement_work(
        &mut self,
        body: &Body<'tcx>,
        state: &State,
        statement: &StatementKind<'tcx>,
    ) -> Result<(), String> {
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(&state.memory) {
                return Ok(());
            }
            pay_body_visits(self, body, 1)?;
            let mut inventory = OperandInventory::default();
            if let StatementKind::Assign(assignment) = statement {
                inventory.projections = assignment.0.projection.len();
                inventory.visit_rvalue(
                    &assignment.1,
                    rustc_middle::mir::Location {
                        block: rustc_middle::mir::START_BLOCK,
                        statement_index: 0,
                    },
                );
            }
            if inventory.reads > MAX_INPUT_VALUES || inventory.projections > MAX_INPUT_VALUES {
                return Err("product instruction operand inventory exceeds existing bound".into());
            }
            // Each actual operand/projection may clone a current logical value and fixed path;
            // price the complete current owned graph before any evaluation or mutable COW work.
            let mut plan = ClonePlan { nodes: 0 };
            pay(self, 4)?;
            if state.memory.len() > MAX_INPUT_VALUES {
                return Err(
                    "product instruction allocation inventory exceeds existing bound".into(),
                );
            }
            pay(self, state.memory.len() + 4)?;
            let mut memory_values = 0usize;
            for value in state.memory.iter().flatten() {
                memory_values += plan.value(self, value, 0)?;
            }
            let locals = self.product_local_clone_work(state)?;
            let memory = self.product_memory_clone_work(&state.memory)?;
            let services = 2 + 2 * inventory.reads + 2 * inventory.projections;
            pay(self, services * (locals + memory + memory_values + 32))
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_return_work(
        &mut self,
        value: &Value,
        memory: &Memory,
    ) -> Result<(), String> {
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(memory) {
                return Ok(());
            }
            let mut plan = ClonePlan { nodes: 0 };
            let work = plan.value(self, value, 0)?;
            pay(self, work)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_incoming_work(
        &mut self,
        state: &State,
        incoming: usize,
    ) -> Result<(), String> {
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(&state.memory) {
                return Ok(());
            }
            pay(self, 6)?;
            if incoming > state.memory.len() || incoming > MAX_INPUT_VALUES {
                return Err("product incoming allocation inventory exceeds existing bound".into());
            }
            pay(self, incoming + 8)?;
            let mut work = 0usize;
            let mut plan = IncomingPlan {
                nodes: 0,
                visited: Vec::new(),
            };
            for value in state.memory[..incoming].iter().flatten() {
                // Each validator has its own visited set. Bound and price each complete root walk.
                plan.visited.clear();
                work += plan.value(self, value, &state.memory, 0)?;
            }
            pay(self, work)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_stack_work(
        &mut self,
        memory: &Memory,
        count: usize,
    ) -> Result<(), String> {
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(memory) {
                return Ok(());
            }
            pay(self, 4)?;
            if count >= self.limits.max_call_depth || count >= MAX_INPUT_DEPTH {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "product call stack exceeds existing depth".into(),
                ));
            }
            pay(self, 8 + 2 * count)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_frame_name_work(
        &mut self,
        instance: ty::Instance<'tcx>,
        memory: &Memory,
    ) -> Result<usize, String> {
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(memory) {
                return Ok(0);
            }
            pay(self, 4)?;
            if instance.args.len() > MAX_INPUT_VALUES
                || self.proof.analyzed_bodies.len() > MAX_INPUT_VALUES
            {
                return Err("product frame name inventory exceeds existing bound".into());
            }
            pay(self, instance.args.len() + 4)?;
            let mut plan = DescriptorPlan { nodes: 0, names: 0 };
            let mut work = plan.path(self, instance.def_id())?;
            for argument in instance.args {
                match argument.kind() {
                    ty::GenericArgKind::Type(original) => {
                        work += plan.original(self, original, 0)?
                    }
                    ty::GenericArgKind::Lifetime(region) => {
                        pay(self, 4)?;
                        if region != self.tcx.lifetimes.re_erased {
                            return Err("product frame name needs erased original regions".into());
                        }
                        work += 16;
                    }
                    ty::GenericArgKind::Const(value) => {
                        pay(self, 6)?;
                        if value.try_to_target_usize(self.tcx).is_none() {
                            return Err(
                                "product frame name constant formatter is unsupported".into()
                            );
                        }
                        work += 64;
                    }
                }
            }
            // Future path/argument formatting, String construction, comparisons and insertion.
            pay(
                self,
                16 + 2 * work + self.proof.analyzed_bodies.len() * (work + 8),
            )?;
            Ok(work)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_frame_work(
        &mut self,
        body: &Body<'tcx>,
        values: &[Value],
        memory: &Memory,
    ) -> Result<(), String> {
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(memory) {
                return Ok(());
            }
            pay(self, 6)?;
            if values.len() != body.arg_count || body.local_decls.len() > MAX_INPUT_VALUES {
                return Err(
                    "product frame argument/local inventory differs or exceeds bound".into(),
                );
            }
            let mut plan = ClonePlan { nodes: 0 };
            pay(self, values.len())?;
            let mut work = 12 + 2 * body.local_decls.len() + body.arg_count;
            for value in values {
                work += plan.value(self, value, 0)?;
            }
            // Local/address/type vectors and the separate retained original argument clone.
            pay(self, work)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_snapshot_work(
        &mut self,
        values: &[Value],
        memory: &Memory,
    ) -> Result<(), String> {
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(memory) {
                return Ok(());
            }
            let id = memory
                .mutable_hierarchy
                .ok_or("product observation namespace is absent")?;
            self.mutable_product_backing(id, memory)?;
            pay(self, 4)?;
            if values.len() > MAX_INPUT_VALUES {
                return Err("product observations exceed existing argument bound".into());
            }
            // No detached Product payload or physical pointer is admitted by this protocol.
            pay(self, 16 * values.len() + 8)?;
            for value in values {
                match value {
                    Value::Bool(_) | Value::Int { .. } | Value::Float { .. } | Value::Unit => {}
                    Value::MutableU16 {
                        role:
                            MutableU16Role::Metadata { .. }
                            | MutableU16Role::ChildMetadata { .. }
                            | MutableU16Role::HierarchyMetadata { .. },
                        ..
                    } => {}
                    Value::OwnedArrayIterator { .. }
                    | Value::MutableU16 { .. }
                    | Value::OwnedRegion { .. }
                    | Value::OwnedSnapshot(_)
                    | Value::Uninitialized
                    | Value::MaybeUninit { .. }
                    | Value::StaticSlice { .. }
                    | Value::StaticView { .. }
                    | Value::RawPointer { .. }
                    | Value::TrackedPointer { .. }
                    | Value::RawSlice { .. }
                    | Value::Input(_)
                    | Value::Bytes { .. }
                    | Value::CompositeSlice { .. }
                    | Value::ScalarSlice { .. }
                    | Value::Adt { .. }
                    | Value::Enum { .. }
                    | Value::Cell { .. }
                    | Value::Atomic { .. }
                    | Value::LocalAtomic { .. }
                    | Value::Reference { .. }
                    | Value::SliceIterator { .. }
                    | Value::Tuple(_)
                    | Value::Elements(_)
                    | Value::MetadataPointer(_)
                    | Value::TraitObject { .. }
                    | Value::DebugReference { .. }
                    | Value::StaticText
                    | Value::FormatArguments
                    | Value::FunctionPointer { .. }
                    | Value::Function => {
                        return Err("product observation has unsupported detached domain".into());
                    }
                }
            }
            Ok(())
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_observations(
        &mut self,
        types: &[Ty<'tcx>],
        values: &[Value],
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<Vec<Value>, String> {
        require_service(self)?;
        if !self.mutable_product_hierarchy_active(memory) {
            return self.typed_coroutine_snapshots(types, values, memory, conditions);
        }
        let result = (|| {
            self.mutable_product_snapshot_work(values, memory)?;
            if types.len() != values.len() {
                return Err("product typed observations have different arity".into());
            }
            pay(self, 12 * types.len() + 4)?;
            for (original, value) in types.iter().zip(values) {
                if primitive(self, *original) {
                    if !matches!(
                        value,
                        Value::Bool(_) | Value::Int { .. } | Value::Float { .. } | Value::Unit
                    ) {
                        return Err("product primitive observation has a nonprimitive value".into());
                    }
                } else if let Value::MutableU16 { id, .. } = value {
                    if !self.mutable_u16_matches(*original, *id, memory, false)? {
                        return Err("product metadata observation original type differs".into());
                    }
                } else {
                    return Err("product observation original type has unsupported domain".into());
                }
            }
            // The independently authenticated primitive/typed Product domain excludes Coroutine.
            // Omit that repeated walk itself; execute the ordinary snapshot once with live guards.
            self.snapshots(values, memory, conditions)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_bindings(
        &mut self,
        body: &Body<'tcx>,
        values: &[Value],
        instance: ty::Instance<'tcx>,
        memory: &Memory,
    ) -> Result<BTreeMap<String, Value>, String> {
        #[cfg(test)]
        work_controls::begin(self, work_controls::Phase::Bindings, memory);
        require_service(self)?;
        if !self.mutable_product_hierarchy_active(memory) {
            return self.configured_bindings(body, values, instance);
        }
        let result = (|| {
            let id = memory
                .mutable_hierarchy
                .ok_or("product bindings namespace absent")?;
            self.mutable_product_backing(id, memory)?;
            pay(self, 4)?;
            if body.var_debug_info.len() > MAX_INPUT_VALUES || values.len() != body.arg_count {
                return Err("product binding source arity/debug inventory differs".into());
            }
            pay(self, body.var_debug_info.len() + 8)?;
            let mut plan = ClonePlan { nodes: 0 };
            let mut work = 8usize;
            for debug in &body.var_debug_info {
                if let VarDebugInfoContents::Place(place) = debug.value
                    && place.projection.is_empty()
                    && place.local.as_usize() > 0
                    && place.local.as_usize() <= body.arg_count
                {
                    let bytes = debug.name.as_str().len();
                    if bytes > MAX_INPUT_VALUES {
                        return Err("product binding source name exceeds existing bound".into());
                    }
                    work += 24
                        + 2 * bytes
                        + plan.value(self, &values[place.local.as_usize() - 1], 0)?;
                }
            }
            // Actual helper admission refuses external specifications; keep this boundary explicit
            // instead of accepting newly supplied aliases or summaries from a mutable registry.
            if self.specification(instance)?.is_some() {
                return Err("product binding external specification remains unsupported".into());
            }
            pay(self, work)?;
            let bindings = self.configured_bindings(body, values, instance)?;
            #[cfg(test)]
            work_controls::publication(work_controls::Phase::Bindings);
            Ok(bindings)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_vector_work(
        &mut self,
        memory: &Memory,
        count: usize,
    ) -> Result<(), String> {
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(memory) {
                return Ok(());
            }
            pay(self, 4)?;
            if count > MAX_INPUT_VALUES {
                return Err("product observation vector exceeds existing bound".into());
            }
            pay(self, 4 + 2 * count)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_bindings_clone_work(
        &mut self,
        bindings: &BTreeMap<String, Value>,
        memory: &Memory,
    ) -> Result<(), String> {
        #[cfg(test)]
        work_controls::begin(self, work_controls::Phase::BindingClone, memory);
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(memory) {
                return Ok(());
            }
            pay(self, 4)?;
            if bindings.len() > MAX_INPUT_VALUES {
                return Err("product contract binding map exceeds existing bound".into());
            }
            pay(self, bindings.len() + 4)?;
            let mut plan = ClonePlan { nodes: 0 };
            let mut work = 8usize;
            for (name, value) in bindings {
                if name.len() > MAX_INPUT_VALUES {
                    return Err("product contract binding name exceeds existing bound".into());
                }
                work += 8 + name.len() + plan.value(self, value, 0)?;
            }
            pay(self, work)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_binding_insert_work(
        &mut self,
        bindings: &BTreeMap<String, Value>,
        name: &str,
        prefix: usize,
        memory: &Memory,
    ) -> Result<(), String> {
        #[cfg(test)]
        work_controls::begin(
            self,
            if prefix == 6 {
                work_controls::Phase::FinalInsert
            } else {
                work_controls::Phase::ResultInsert
            },
            memory,
        );
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(memory) {
                return Ok(());
            }
            pay(self, 4)?;
            let bytes = prefix
                .checked_add(name.len())
                .ok_or("product binding name overflow")?;
            if bytes > MAX_INPUT_VALUES || bindings.len() >= MAX_INPUT_VALUES {
                return Err(
                    "product postcondition binding insertion exceeds existing bound".into(),
                );
            }
            pay(self, bindings.len() + 4)?;
            let mut keys = 0usize;
            for key in bindings.keys() {
                if key.len() > MAX_INPUT_VALUES {
                    return Err("product existing binding key exceeds existing bound".into());
                }
                keys += key.len() + 8;
            }
            // Pay key construction and every possible tree comparison before formatting/insertion.
            pay(self, 12 + bytes + keys)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    fn product_local_clone_work(&mut self, state: &State) -> Result<usize, String> {
        let count = state.locals.len();
        if count > MAX_INPUT_VALUES
            || state.addresses.len() != count
            || state.conditions.len() > MAX_INPUT_VALUES
            || state.constant_receipts.len() > MAX_INPUT_VALUES
        {
            return Err("product continuation vectors exceed existing bounds".into());
        }
        pay(self, count + 8)?;
        let mut plan = ClonePlan { nodes: 0 };
        let mut work = 16 + 2 * count + state.constant_receipts.len() * 8;
        work += masks(self, &state.missing_places)?;
        for value in state.locals.iter().flatten() {
            work += plan.value(self, value, 0)?;
        }
        Ok(work)
    }

    fn product_memory_clone_work(&mut self, memory: &Memory) -> Result<usize, String> {
        pay(self, 12)?;
        // These catalogues own payload graphs; this first whole-product scope does not
        // admit their independent constructor/static protocols.
        if !memory.startup_values.is_empty() || !memory.incoming_byte_roots.is_empty() {
            return Err("product frame has unsupported static/byte clone catalogue".into());
        }
        let locations = memory.isolated_static_types.len();
        let overwritten = memory.startup_overwritten.len();
        let uninitialized = memory.static_uninitialized.len();
        if locations > MAX_INPUT_VALUES
            || overwritten > MAX_INPUT_VALUES
            || uninitialized > MAX_INPUT_VALUES
        {
            return Err("product memory clone catalogue exceeds existing bound".into());
        }
        Ok(40
            + 8 * locations
            + 4 * overwritten
            + uninitialized
            + masks(self, &memory.missing_places)?)
    }

    pub(in crate::proof) fn mutable_product_switch_work(
        &mut self,
        state: &State,
        targets: usize,
    ) -> Result<(), String> {
        require_service(self)?;
        let result = (|| {
            if !self.mutable_product_hierarchy_active(&state.memory) {
                return Ok(());
            }
            pay(self, 4)?;
            if targets > MAX_INPUT_VALUES {
                return Err("product switch target inventory exceeds existing bound".into());
            }
            let clone = self.product_local_clone_work(state)?
                + self.product_memory_clone_work(&state.memory)?
                + state.conditions.len();
            pay(self, 8 + targets * (clone + 20))
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_retry_work(
        &mut self,
        path: &retry_frontiers::Path,
    ) -> Result<(), String> {
        require_service(self)?;
        let result = (|| {
            if self.mutable_product_access.borrow().is_some() {
                pay(self, 4)?;
                if path.len() > MAX_INPUT_VALUES {
                    return Err("product retry path exceeds existing bound".into());
                }
                pay(self, 4 + 8 * path.len())?;
            }
            Ok(())
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }

    pub(in crate::proof) fn mutable_product_adopt_return(
        &mut self,
        state: &State,
        conditions: Vec<Term>,
        memory: Memory,
        flow: activation_flow::Flow,
    ) -> Result<State, String> {
        #[cfg(test)]
        work_controls::begin(self, work_controls::Phase::Adopt, &state.memory);
        require_service(self)?;
        if !self.mutable_product_hierarchy_active(&state.memory) {
            return self.adopt_flow_return(state, conditions, memory, flow);
        }
        let result = (|| {
            let work = self.product_local_clone_work(state)?;
            pay(self, work)?;
            let continuation = self.adopt_flow_return(state, conditions, memory, flow)?;
            #[cfg(test)]
            work_controls::publication(work_controls::Phase::Adopt);
            Ok(continuation)
        })();
        if result.is_err() {
            self.mutable_product_failed.set(true);
        }
        result
    }
}

#[cfg(test)]
pub(super) fn impl_path_controls(tcx: TyCtxt<'_>) {
    let names = [
        ("InherentProductWithActualCompilerQualifiedName", true),
        ("TraitProductWithActualCompilerQualifiedName", true),
        ("ConstProduct", true),
        ("UnsupportedFunctionPrinterProduct", false),
        ("OversizedPrinterProduct", false),
    ];
    for (name, supported) in names {
        let id = tcx
            .iter_local_def_id()
            .find(|id| {
                tcx.def_kind(*id) == DefKind::Struct
                    && tcx.item_name(id.to_def_id()).as_str() == name
            })
            .unwrap();
        let mut engine = super::super::super::nonzero_niches::test_engine(tcx);
        engine.limits.max_steps = 2_000_000;
        let original = tcx.type_of(id).instantiate_identity().skip_norm_wip();
        let result = descriptor_work(&mut engine, original);
        if supported {
            let bound = result.unwrap();
            // The formatter allocates only after the actual original path plan has paid.
            pay(&mut engine, bound * 2 + 64).unwrap();
            let actual = tcx.def_path_str(id);
            assert!(
                actual.len() <= bound,
                "actual compiler name exceeds planned bytes: {name}"
            );
            assert!(engine.mutable_product_shape(original).unwrap().is_some());
            eprintln!(
                "impl product name: {name}, actual_bytes={}, bound={bound}",
                actual.len()
            );
        } else {
            assert!(
                result.is_err(),
                "unsupported printer must refuse before allocation: {name}"
            );
            eprintln!("impl product name: {name}, refused before name allocation");
        }
    }
}

#[cfg(test)]
pub(super) fn external_path_controls(tcx: TyCtxt<'_>, oversized: bool) {
    use rustc_span::def_id::{CRATE_DEF_INDEX, ModId};
    let external = tcx
        .crates(())
        .iter()
        .find(|crate_num| tcx.crate_name(**crate_num).as_str() == "d")
        .copied()
        .unwrap();
    let root = DefId {
        krate: external,
        index: CRATE_DEF_INDEX,
    };
    let children = tcx.module_children(ModId::new_unchecked(root));
    let mut count = 0;
    let mut types = 0;
    let mut constructors = 0;
    for child in children {
        if !child.vis.is_public() {
            continue;
        }
        let Some(id) = child.res.opt_def_id() else {
            continue;
        };
        match tcx.def_kind(id) {
            DefKind::Struct | DefKind::Trait => types += 1,
            DefKind::Ctor(..) => constructors += 1,
            kind => panic!("unexpected external fixture definition {kind:?}"),
        }
        let mut engine = super::super::super::nonzero_niches::test_engine(tcx);
        engine.limits.max_steps = 2_000_000;
        let mut plan = DescriptorPlan { nodes: 0, names: 0 };
        let result = plan.path(&mut engine, id);
        if oversized {
            assert!(
                result.is_err(),
                "actual oversized extern alias must refuse before allocation"
            );
            assert!(engine.bodies.borrow().is_empty());
            assert!(engine.mutable_product_sources.borrow().is_empty());
            assert!(engine.mutable_product_descriptors.is_empty());
            count += 1;
            continue;
        }
        let bound = result.unwrap();
        pay(&mut engine, bound * 2 + 64).unwrap();
        let actual = tcx.def_path_str(id);
        assert!(actual.len() <= bound);
        assert!(actual.contains("actual_external_alias_for_printer"));
        assert!(actual.contains(child.ident.name.as_str()));
        eprintln!("external compiler path: {actual}; bound={bound}");
        count += 1;
    }
    assert_eq!(types, 3);
    assert_eq!(constructors, 2);
    assert_eq!(count, 5);
    if oversized {
        eprintln!("external compiler paths: actual oversized alias refused before name allocation");
        return;
    }
    for name in ["ExternalSelfProduct", "ExternalTraitProduct"] {
        let id = tcx
            .iter_local_def_id()
            .find(|id| {
                tcx.def_kind(*id) == DefKind::Struct
                    && tcx.item_name(id.to_def_id()).as_str() == name
            })
            .unwrap();
        let mut engine = super::super::super::nonzero_niches::test_engine(tcx);
        engine.limits.max_steps = 2_000_000;
        let original = tcx.type_of(id).instantiate_identity().skip_norm_wip();
        let bound = descriptor_work(&mut engine, original).unwrap();
        pay(&mut engine, bound * 2 + 64).unwrap();
        let actual = tcx.def_path_str(id);
        assert!(actual.len() <= bound);
        assert!(actual.contains("actual_external_alias_for_printer"));
        assert!(actual.contains("ExternalArgumentWithVisibleAliasName"));
        assert!(engine.mutable_product_shape(original).unwrap().is_some());
        eprintln!("external impl product: {actual}; bound={bound}");
    }
}
