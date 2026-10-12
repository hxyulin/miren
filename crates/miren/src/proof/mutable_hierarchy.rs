//! Checked single nested whole-u16 child hierarchy with persistent generation and epoch.
use super::*;
use rustc_middle::mir::PlaceElem;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use std::rc::Rc;

// Only the new associated route uses this borrowed inventory. No selected body is cloned here.
struct AssociatedBodyWork<'a, 'tcx> {
    engine: &'a Engine<'tcx>,
    arguments: ty::GenericArgsRef<'tcx>,
    locals: usize,
    work: usize,
    error: Option<String>,
    activation_shapes: bool,
    activation_flow: Option<&'a super::activation_flow::Flow>,
}

impl<'tcx> AssociatedBodyWork<'_, 'tcx> {
    fn charge(&mut self, count: usize) -> Result<(), String> {
        self.work = self.work.saturating_add(count);
        if self.work > MAX_INPUT_VALUES {
            return Err(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "associated borrowed Body exceeds existing work budget".into(),
            ));
        }
        if let Some(flow) = self.activation_flow {
            flow.charge(count)?;
        }
        Ok(())
    }

    fn original_type(&mut self, original: Ty<'tcx>, depth: usize) -> Result<(), String> {
        self.charge(1)?;
        if depth >= MAX_INPUT_DEPTH {
            return Err(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "associated borrowed Body type exceeds existing depth budget".into(),
            ));
        }
        if self.activation_shapes {
            match original.kind() {
                ty::Tuple(fields) if !fields.is_empty() => {
                    return Err("armed activation Tuple production or copy is unsupported".into());
                }
                ty::Adt(_, _) => {
                    return Err(format!(
                        "armed activation owned shape is unsupported: {original:?}"
                    ));
                }
                ty::Array(inner, _)
                    if !matches!(
                        inner.kind(),
                        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_)
                    ) =>
                {
                    return Err("armed activation nested array payload is unsupported".into());
                }
                _ => {}
            }
        }
        match original.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str | ty::Never => {
                Ok(())
            }
            ty::Ref(_, inner, _) | ty::RawPtr(inner, _) | ty::Slice(inner) => {
                self.original_type(*inner, depth + 1)
            }
            ty::Array(inner, count) => {
                self.charge(1)?;
                if count.try_to_target_usize(self.engine.tcx).is_none() {
                    return Err("associated borrowed array extent is unsupported".into());
                }
                self.original_type(*inner, depth + 1)
            }
            ty::Tuple(fields) => {
                self.charge(fields.len())?;
                for field in fields.iter() {
                    self.original_type(field, depth + 1)?;
                }
                Ok(())
            }
            ty::Adt(_, arguments) => self.generic_arguments(arguments, depth + 1),
            ty::FnDef(_, arguments) => self.generic_arguments(arguments.skip_binder(), depth + 1),
            ty::Param(parameter) => {
                let Some(original) = self
                    .arguments
                    .get(parameter.index as usize)
                    .and_then(|argument| argument.as_type())
                else {
                    return Err("associated borrowed Body Param mapping differs".into());
                };
                self.original_type(original, depth + 1)
            }
            _ => Err("associated borrowed Body type grammar is unsupported".into()),
        }
    }

    fn generic_arguments(
        &mut self,
        arguments: ty::GenericArgsRef<'tcx>,
        depth: usize,
    ) -> Result<(), String> {
        self.charge(arguments.len())?;
        for argument in arguments.iter() {
            match argument.kind() {
                ty::GenericArgKind::Type(original) => self.original_type(original, depth)?,
                ty::GenericArgKind::Lifetime(_) => {}
                ty::GenericArgKind::Const(_) => {
                    return Err("associated borrowed const substitution is unsupported".into());
                }
            }
        }
        Ok(())
    }
}

impl<'tcx> Visitor<'tcx> for AssociatedBodyWork<'_, 'tcx> {
    fn visit_ty(&mut self, original: Ty<'tcx>, _: rustc_middle::mir::visit::TyContext) {
        if self.error.is_none() {
            self.error = self.original_type(original, 0).err();
        }
    }

    fn visit_place(
        &mut self,
        place: &Place<'tcx>,
        _: PlaceContext,
        _: rustc_middle::mir::Location,
    ) {
        if self.error.is_some() {
            return;
        }
        if place.local.as_usize() >= self.locals {
            self.error = Some("associated borrowed place local is unavailable".into());
            return;
        }
        if place.projection.len() >= MAX_INPUT_DEPTH {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "associated borrowed projection exceeds existing depth budget".into(),
            ));
            return;
        }
        self.error = self.charge(place.projection.len()).err();
        for element in place.projection {
            if self.error.is_some() {
                break;
            }
            match element {
                PlaceElem::Field(_, original) | PlaceElem::OpaqueCast(original) => {
                    self.error = self.original_type(original, 0).err();
                }
                PlaceElem::UnwrapUnsafeBinder(_) => {
                    self.error = Some("associated borrowed unsafe binder is unsupported".into());
                }
                PlaceElem::Deref
                | PlaceElem::Index(_)
                | PlaceElem::ConstantIndex { .. }
                | PlaceElem::Subslice { .. }
                | PlaceElem::Downcast(_, _)
                | PlaceElem::PhantomDeref => {}
            }
        }
    }

    fn visit_user_type_projection(&mut self, projection: &rustc_middle::mir::UserTypeProjection) {
        if self.error.is_some() {
            return;
        }
        self.error = self.charge(projection.projs.len()).err();
        if self.error.is_none() && projection.projs.len() >= MAX_INPUT_DEPTH {
            self.error = Some(self.engine.categorized_error(
                UnknownCategory::ResourceLimit,
                "associated borrowed user projection exceeds existing depth budget".into(),
            ));
        }
    }

    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: rustc_middle::mir::Location) {
        if self.error.is_none() {
            self.error = self.charge(1).err();
        }
        if self.error.is_none() {
            self.super_operand(operand, location);
        }
    }

    fn visit_const_operand(
        &mut self,
        constant: &rustc_middle::mir::ConstOperand<'tcx>,
        _: rustc_middle::mir::Location,
    ) {
        if self.error.is_some() {
            return;
        }
        match constant.const_ {
            rustc_middle::mir::Const::Val(
                rustc_middle::mir::ConstValue::Scalar(_) | rustc_middle::mir::ConstValue::ZeroSized,
                original,
            ) => self.error = self.original_type(original, 0).err(),
            _ => self.error = Some("associated borrowed constant grammar is unsupported".into()),
        }
    }

    fn visit_ty_const(&mut self, _: ty::Const<'tcx>, _: rustc_middle::mir::Location) {
        if self.error.is_none() {
            self.error = Some("associated borrowed type constant is unsupported".into());
        }
    }

    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: rustc_middle::mir::Location) {
        if self.error.is_some() {
            return;
        }
        if self.activation_shapes
            && let Rvalue::Ref(_, borrow, place) = value
            && (!matches!(
                borrow,
                rustc_middle::mir::BorrowKind::Mut { .. } | rustc_middle::mir::BorrowKind::Shared
            ) || !matches!(place.projection.as_ref(), [ProjectionElem::Deref]))
        {
            self.error = Some("armed activation partial borrow is unsupported".into());
            return;
        }
        if let Rvalue::Aggregate(kind, operands) = value {
            self.error = self.charge(operands.len()).err();
            if self.error.is_none()
                && !matches!(
                    **kind,
                    rustc_middle::mir::AggregateKind::Tuple
                        | rustc_middle::mir::AggregateKind::Array(_)
                )
            {
                self.error = Some("associated borrowed aggregate grammar is unsupported".into());
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
        if self.error.is_some() {
            return;
        }
        match &terminator.kind {
            TerminatorKind::Call { args, .. } => self.error = self.charge(args.len()).err(),
            TerminatorKind::SwitchInt { targets, .. } => {
                self.error = self.charge(targets.all_targets().len()).err();
            }
            TerminatorKind::InlineAsm { .. } => {
                self.error = Some("associated borrowed inline assembly is unsupported".into());
            }
            _ => {}
        }
        if self.error.is_none() {
            self.super_terminator(terminator, location);
        }
    }

    fn visit_statement(
        &mut self,
        statement: &rustc_middle::mir::Statement<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        if self.error.is_none() {
            self.super_statement(statement, location);
        }
    }
}

const ISSUANCE_ENABLED: bool = true;
const INTEGER_HIERARCHY_ENABLED: bool = true;
const BOOL_HIERARCHY_ENABLED: bool = true;
const CHAR_HIERARCHY_ENABLED: bool = true;
const FLOAT_HIERARCHY_ENABLED: bool = true;
const DORMANT_CALLS_ENABLED: bool = true;
const ASSOCIATED_HIERARCHY_ENABLED: bool = true;

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TestHierarchyFlag {
    Associated,
    Integer,
    Bool,
    Char,
    Float,
    Issuance,
}

#[cfg(test)]
impl TestHierarchyFlag {
    fn replace(self, value: bool) -> bool {
        match self {
            Self::Associated => TEST_ASSOCIATED_HIERARCHY.with(|cell| cell.replace(value)),
            Self::Integer => TEST_INTEGER_HIERARCHY.with(|cell| cell.replace(value)),
            Self::Bool => TEST_BOOL_HIERARCHY.with(|cell| cell.replace(value)),
            Self::Char => TEST_CHAR_HIERARCHY.with(|cell| cell.replace(value)),
            Self::Float => TEST_FLOAT_HIERARCHY.with(|cell| cell.replace(value)),
            Self::Issuance => TEST_ISSUANCE.with(|cell| cell.replace(value)),
        }
    }

    fn get(self) -> bool {
        match self {
            Self::Associated => TEST_ASSOCIATED_HIERARCHY.with(std::cell::Cell::get),
            Self::Integer => TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get),
            Self::Bool => TEST_BOOL_HIERARCHY.with(std::cell::Cell::get),
            Self::Char => TEST_CHAR_HIERARCHY.with(std::cell::Cell::get),
            Self::Float => TEST_FLOAT_HIERARCHY.with(std::cell::Cell::get),
            Self::Issuance => TEST_ISSUANCE.with(std::cell::Cell::get),
        }
    }
}

#[cfg(test)]
struct TestHierarchyOverride {
    flag: TestHierarchyFlag,
    previous: bool,
}

#[cfg(test)]
impl TestHierarchyOverride {
    fn enable(flag: TestHierarchyFlag) -> Self {
        Self {
            flag,
            previous: flag.replace(true),
        }
    }
}

#[cfg(test)]
impl Drop for TestHierarchyOverride {
    fn drop(&mut self) {
        self.flag.replace(self.previous);
    }
}

fn associated_hierarchy_enabled() -> bool {
    #[cfg(test)]
    if TEST_ASSOCIATED_HIERARCHY.with(std::cell::Cell::get) {
        return true;
    }
    ASSOCIATED_HIERARCHY_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_ASSOCIATED_HIERARCHY: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestAssociatedHierarchy {
    _scope: TestHierarchyOverride,
}

#[cfg(test)]
impl TestAssociatedHierarchy {
    fn enable() -> Self {
        Self {
            _scope: TestHierarchyOverride::enable(TestHierarchyFlag::Associated),
        }
    }
}

fn integer_hierarchy_enabled() -> bool {
    #[cfg(test)]
    if TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get) {
        return true;
    }
    INTEGER_HIERARCHY_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_INTEGER_HIERARCHY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestIntegerHierarchy {
    _scope: TestHierarchyOverride,
}

#[cfg(test)]
impl TestIntegerHierarchy {
    fn enable() -> Self {
        Self {
            _scope: TestHierarchyOverride::enable(TestHierarchyFlag::Integer),
        }
    }
}

fn bool_hierarchy_enabled() -> bool {
    #[cfg(test)]
    if TEST_BOOL_HIERARCHY.with(std::cell::Cell::get) {
        return true;
    }
    BOOL_HIERARCHY_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_BOOL_HIERARCHY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestBoolHierarchy {
    _scope: TestHierarchyOverride,
}

#[cfg(test)]
impl TestBoolHierarchy {
    fn enable() -> Self {
        Self {
            _scope: TestHierarchyOverride::enable(TestHierarchyFlag::Bool),
        }
    }
}
fn char_hierarchy_enabled() -> bool {
    #[cfg(test)]
    if TEST_CHAR_HIERARCHY.with(std::cell::Cell::get) {
        return true;
    }
    CHAR_HIERARCHY_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_CHAR_HIERARCHY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestCharHierarchy {
    _scope: TestHierarchyOverride,
}

#[cfg(test)]
impl TestCharHierarchy {
    fn enable() -> Self {
        Self {
            _scope: TestHierarchyOverride::enable(TestHierarchyFlag::Char),
        }
    }
}

fn float_hierarchy_enabled() -> bool {
    #[cfg(test)]
    if TEST_FLOAT_HIERARCHY.with(std::cell::Cell::get) {
        return true;
    }
    FLOAT_HIERARCHY_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_FLOAT_HIERARCHY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestFloatHierarchy {
    _scope: TestHierarchyOverride,
}

#[cfg(test)]
impl TestFloatHierarchy {
    fn enable() -> Self {
        Self {
            _scope: TestHierarchyOverride::enable(TestHierarchyFlag::Float),
        }
    }
}

fn issuance_enabled() -> bool {
    #[cfg(test)]
    if TEST_ISSUANCE.with(std::cell::Cell::get) {
        return true;
    }
    ISSUANCE_ENABLED
}

#[cfg(test)]
std::thread_local! {
    static TEST_ISSUANCE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
struct TestIssuance {
    _scope: TestHierarchyOverride,
}

#[cfg(test)]
impl TestIssuance {
    fn enable() -> Self {
        Self {
            _scope: TestHierarchyOverride::enable(TestHierarchyFlag::Issuance),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct Origin {
    certificate: usize,
    allocation: usize,
    capacity: Value,
    data_context: Term,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Owner {
    lease: u64,
    parent: u64,
    frames: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Tip {
    frame: usize,
    statement: usize,
    local: usize,
}

#[derive(Debug)]
enum TransitionError {
    Semantics(String),
    Resource(&'static str),
}

impl From<String> for TransitionError {
    fn from(reason: String) -> Self {
        Self::Semantics(reason)
    }
}

impl From<&str> for TransitionError {
    fn from(reason: &str) -> Self {
        Self::Semantics(reason.into())
    }
}

#[derive(Clone, Debug)]
struct Pending {
    lease: u64,
    parent: u64,
    tip: Tip,
}

#[derive(Clone, Debug)]
pub(super) struct Hierarchy {
    origin: Rc<Origin>,
    issued: u64,
    epoch: u64,
    owners: Vec<Owner>,
    pending: Option<Pending>,
}

impl Hierarchy {
    fn activation_charge_clone(&self, flow: &super::activation_flow::Flow) -> Result<(), String> {
        if matches!(flow, super::activation_flow::Flow::Unarmed) {
            return Ok(());
        }
        flow.charge(
            self.owners
                .len()
                .saturating_add(1 + usize::from(self.pending.is_some())),
        )?;
        for owner in &self.owners {
            flow.charge(owner.frames.len())?;
        }
        Ok(())
    }

    pub(super) fn role_valid(&self, role: &symbolic::MutableU16Role, initialized: bool) -> bool {
        use symbolic::MutableU16Role;
        match role {
            MutableU16Role::Root => {
                if initialized {
                    self.access(0).is_ok()
                } else {
                    self.lifetime(0).is_ok()
                }
            }
            MutableU16Role::HierarchyChild { lease } => {
                if initialized {
                    self.access(*lease).is_ok()
                } else {
                    self.lifetime(*lease).is_ok()
                }
            }
            MutableU16Role::HierarchyMetadata { lease, epoch } => self
                .observe(Metadata {
                    lease: *lease,
                    epoch: *epoch,
                })
                .is_ok(),
            MutableU16Role::Ghost { .. } => true,
            MutableU16Role::Metadata { .. }
            | MutableU16Role::Child { .. }
            | MutableU16Role::ChildMetadata { .. } => false,
        }
    }

    pub(super) fn metadata_epoch(&self, lease: u64) -> Result<u64, String> {
        Ok(self.metadata(lease)?.epoch)
    }

    pub(super) fn activation_charge_storage(
        &self,
        flow: &super::activation_flow::Flow,
    ) -> Result<(), String> {
        flow.charge(self.owners.len())
    }

    pub(super) fn storage_slots(&self) -> usize {
        // Dormant origin and counters persist even when the owner stack is empty.
        6usize
            .saturating_add(
                self.owners
                    .iter()
                    .map(|owner| 2 + owner.frames.len())
                    .sum::<usize>(),
            )
            .saturating_add(usize::from(self.pending.is_some()) * 5)
    }
}

impl<'tcx> Engine<'tcx> {
    fn activation_charge_backing_cow(
        &self,
        flow: &super::activation_flow::Flow,
        memory: &Memory,
    ) -> Result<(), String> {
        if matches!(flow, super::activation_flow::Flow::Unarmed)
            || Rc::strong_count(&memory.mutable_u16) == 1
        {
            return Ok(());
        }
        flow.charge(memory.mutable_u16.len())?;
        for backing in memory.mutable_u16.iter() {
            if backing.interval.is_some()
                || !matches!(backing.phase, super::mutable_u16_children::Phase::Idle)
            {
                return Err("armed activation legacy backing clone is unsupported".into());
            }
            flow.charge_clone_value(&backing.length)?;
            if let Some(hierarchy) = &backing.hierarchy {
                hierarchy.activation_charge_clone(flow)?;
            }
        }
        Ok(())
    }

    pub(super) fn activation_hierarchy_depth(
        &self,
        flow: &super::activation_flow::Flow,
        memory: &Memory,
    ) -> Result<usize, String> {
        let Some(id) = memory.mutable_hierarchy else {
            return Ok(0);
        };
        self.activation_charge_backing_schema(flow, memory, id)?;
        let backing = self.mutable_u16_backing(id, memory)?;
        let hierarchy = backing
            .hierarchy
            .as_ref()
            .ok_or("activation depth namespace disappeared")?;
        flow.charge(hierarchy.owners.len())?;
        Ok(hierarchy
            .owners
            .iter()
            .map(|owner| owner.frames.len())
            .sum())
    }

    pub(super) fn mutable_hierarchy_activation_origin<'a>(
        &self,
        memory: &'a Memory,
        id: usize,
    ) -> Option<&'a Rc<Origin>> {
        memory
            .mutable_u16
            .get(id)?
            .hierarchy
            .as_ref()
            .map(|h| &h.origin)
    }

    pub(super) fn activation_charge_backing_schema(
        &self,
        flow: &super::activation_flow::Flow,
        memory: &Memory,
        id: usize,
    ) -> Result<(), String> {
        if matches!(flow, super::activation_flow::Flow::Unarmed) {
            return Ok(());
        }
        // The existing backing validator checks this allocation's complete move mask,
        // then traverses the owner lineage and each owner's frame certificates.
        flow.charge(memory.missing_places.entries().len())?;
        let backing = memory
            .mutable_u16
            .get(id)
            .ok_or("activation backing disappeared")?;
        if let Some(hierarchy) = &backing.hierarchy {
            // This precharge loop and the actual validator are separate owner passes.
            flow.charge(hierarchy.owners.len().saturating_mul(2))?;
            for owner in &hierarchy.owners {
                flow.charge(owner.frames.len())?;
            }
        }
        Ok(())
    }

    pub(super) fn mutable_hierarchy_activation_snapshot(
        &self,
        memory: &Memory,
        id: usize,
        flow: &super::activation_flow::Flow,
    ) -> Result<(Rc<Origin>, u64, u64), String> {
        self.activation_charge_backing_schema(flow, memory, id)?;
        let backing = self.mutable_u16_backing(id, memory)?;
        let hierarchy = backing
            .hierarchy
            .as_ref()
            .ok_or("activation hierarchy disappeared")?;
        if hierarchy.origin.certificate != backing.certificate
            || hierarchy.origin.allocation != backing.allocation
            || hierarchy.origin.capacity.integer()? != backing.length.integer()?
            || !hierarchy.origin.data_context.belongs_to(&self.terms)
            || !backing.data.scalar()?.belongs_to(&self.terms)
            || hierarchy.origin.data_context.sort() != backing.data.scalar()?.sort()
        {
            return Err("activation backing no longer matches its issued origin".into());
        }
        Ok((hierarchy.origin.clone(), hierarchy.issued, hierarchy.epoch))
    }

    pub(super) fn mutable_hierarchy_activation_live(
        &self,
        memory: &Memory,
        id: usize,
        origin: &Rc<Origin>,
        issued: u64,
        epoch: u64,
        flow: &super::activation_flow::Flow,
    ) -> Result<(), String> {
        let (actual, current_issued, current_epoch) =
            self.mutable_hierarchy_activation_snapshot(memory, id, flow)?;
        if !Rc::ptr_eq(&actual, origin) || current_issued != issued || current_epoch != epoch {
            return Err(
                "activation current Memory lost its origin or exact observed generation".into(),
            );
        }
        Ok(())
    }

    fn activation_signature_pass(
        &self,
        flow: &super::activation_flow::Flow,
        instance: ty::Instance<'tcx>,
    ) -> Result<(), String> {
        if matches!(flow, super::activation_flow::Flow::Unarmed) {
            return Ok(());
        }
        let mut local = 0;
        self.activation_borrowed_signature(instance, &mut local, flow)?;
        // Actual selected signature substitution and region erasure are separate passes.
        flow.charge(local)?;
        flow.charge(local)
    }

    pub(super) fn activation_borrowed_signature(
        &self,
        instance: ty::Instance<'tcx>,
        work: &mut usize,
        flow: &super::activation_flow::Flow,
    ) -> Result<(), String> {
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
            || !instance.def_id().is_local()
            || !self.tcx.is_mir_available(instance.def_id())
        {
            return Err(format!(
                "armed activation requires a local available Item body: {}",
                self.tcx.def_path_str(instance.def_id())
            ));
        }
        if self.tcx.def_kind(instance.def_id()) == DefKind::AssocFn
            && self.tcx.associated_item(instance.def_id()).is_method()
        {
            return Err("armed activation method adapter is not implemented".into());
        }
        let signature = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate_identity()
            .skip_binder();
        let mut inventory = AssociatedBodyWork {
            engine: self,
            arguments: instance.args,
            locals: 0,
            work: *work,
            error: None,
            activation_shapes: true,
            activation_flow: Some(flow),
        };
        inventory.generic_arguments(instance.args, 0)?;
        inventory.charge(signature.inputs().len().saturating_add(1))?;
        for original in signature.inputs() {
            inventory.original_type(*original, 0)?;
        }
        inventory.original_type(signature.output(), 0)?;
        *work = inventory.work;
        Ok(())
    }

    pub(super) fn activation_borrowed_preflight(
        &self,
        instance: ty::Instance<'tcx>,
        work: &mut usize,
        flow: &super::activation_flow::Flow,
    ) -> Result<(), String> {
        self.activation_borrowed_signature(instance, work, flow)?;
        let original = self.tcx.instance_mir(instance.def);
        self.mutable_hierarchy_associated_borrowed_body_work(
            instance,
            original,
            work,
            true,
            Some(flow),
        )
    }

    pub(super) fn activation_borrowed_publication(
        &self,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
        work: &mut usize,
        flow: &super::activation_flow::Flow,
    ) -> Result<(), String> {
        self.mutable_hierarchy_associated_borrowed_body_work(
            instance,
            body,
            work,
            true,
            Some(flow),
        )?;
        // Raw arguments and the identity signature were bounded before substitution.
        // The activation shape grammar rejects aliases/owned recursive shapes, so no
        // normalization query or new call-signature cache is needed for this comparison.
        // Substitution and region erasure are actual input passes, not validation credits.
        flow.charge(*work)?;
        flow.charge(*work)?;
        let signature = self
            .tcx
            .fn_sig(instance.def_id())
            .instantiate(self.tcx, instance.args)
            .skip_norm_wip();
        let signature = self.tcx.instantiate_bound_regions_with_erased(signature);
        flow.charge(signature.inputs().len().saturating_add(1))?;
        *work = work.saturating_add(signature.inputs().len().saturating_add(1));
        if *work > MAX_INPUT_VALUES {
            return Err("activation signature exceeds shared work budget".into());
        }
        if body.arg_count != signature.inputs().len()
            || self.tcx.erase_and_anonymize_regions(body.return_ty())
                != self.tcx.erase_and_anonymize_regions(signature.output())
            || body
                .args_iter()
                .zip(signature.inputs())
                .any(|(local, original)| {
                    self.tcx
                        .erase_and_anonymize_regions(body.local_decls[local].ty)
                        != self.tcx.erase_and_anonymize_regions(*original)
                })
        {
            return Err("activation cached Body original signature differs".into());
        }
        Ok(())
    }

    pub(super) fn mutable_hierarchy_disabled_backing(
        &self,
        backing: &super::mutable_u16::Backing,
    ) -> Result<(), String> {
        let Some(hierarchy) = &backing.hierarchy else {
            return Ok(());
        };
        if hierarchy.owners.len() > 2 {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "hierarchy exceeds the single nested-child scope".into(),
            ));
        }
        if backing.interval.is_some()
            || backing.phase != super::mutable_u16_children::Phase::Idle
            || hierarchy.origin.certificate != backing.certificate
            || hierarchy.origin.allocation != backing.allocation
            || hierarchy.origin.capacity.integer()? != backing.length.integer()?
            || !hierarchy.origin.data_context.belongs_to(&self.terms)
            || !backing.data.scalar()?.belongs_to(&self.terms)
            || hierarchy.origin.data_context.sort() != backing.data.scalar()?.sort()
            || !self.mutable_hierarchy_element(self.mutable_interval_element(backing.certificate)?)
            || hierarchy.issued < backing.generation
        {
            return Err("disabled hierarchy original owner differs".into());
        }
        let mut parent = 0;
        let mut depth = 0usize;
        for owner in &hierarchy.owners {
            depth = depth.saturating_add(owner.frames.len());
            if owner.lease == 0
                || owner.lease > hierarchy.issued
                || owner.lease <= parent
                || owner.parent != parent
                || owner.frames.is_empty()
                || depth > MAX_INPUT_DEPTH
                || owner.frames.iter().any(|id| {
                    self.mutable_u16_frames
                        .borrow()
                        .get(*id)
                        .is_none_or(|weak| weak.upgrade().is_none())
                })
            {
                return Err("disabled hierarchy lineage differs".into());
            }
            parent = owner.lease;
        }
        if hierarchy.pending.as_ref().is_some_and(|pending| {
            pending.lease != hierarchy.issued
                || pending.lease <= pending.parent
                || pending.parent != parent
                || hierarchy.epoch == 0
                || pending.tip.local == 0
                || pending.tip.statement == 0
                || self
                    .mutable_u16_frames
                    .borrow()
                    .get(pending.tip.frame)
                    .is_none_or(|weak| weak.upgrade().is_none())
        }) {
            return Err("disabled hierarchy pending identity differs".into());
        }
        Ok(())
    }

    #[cfg(test)]
    pub(super) fn mutable_hierarchy_source(
        &self,
        body: &Body<'tcx>,
        state: &State,
        destination: Place<'tcx>,
        value: &Rvalue<'tcx>,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<(), String> {
        let mut work = body
            .local_decls
            .len()
            .saturating_add(body.basic_blocks.len());
        if work > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "hierarchy compiler facts exceed existing work budget".into(),
            ));
        }
        if body.coroutine.is_some() || body.spread_arg.is_some() || body.tainted_by_errors.is_some()
        {
            return Err("hierarchy original Body is outside bounded domain".into());
        }
        let mut actual = false;
        for block in body.basic_blocks.iter() {
            work = work.saturating_add(block.statements.len());
            if work > MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "hierarchy compiler facts exceed existing work budget".into(),
                ));
            }
            actual |= block
                .statements
                .iter()
                .any(|s| std::ptr::eq(&s.kind, occurrence));
        }
        if !actual
            || !matches!(occurrence, StatementKind::Assign(assignment)
            if assignment.0 == destination && std::ptr::eq(&assignment.1, value))
        {
            return Err("hierarchy requires actual Assignment occurrence".into());
        }
        let Rvalue::Ref(_, BorrowKind::Mut { .. }, source) = value else {
            return Err("hierarchy requires exact RefMut".into());
        };
        let Value::MutableU16 {
            id,
            role: symbolic::MutableU16Role::Child { generation },
        } = self.raw_local(state, source.local.as_usize())?
        else {
            return Err("hierarchy requires current Child source".into());
        };
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let super::mutable_u16_children::Phase::Active { frames } = &backing.phase else {
            return Err("hierarchy requires active parent".into());
        };
        self.mutable_u16_frame_top(body, frames)?;
        if backing.interval.is_some()
            || backing.generation != generation
            || source.projection.as_ref() != [ProjectionElem::Deref]
            || !destination.projection.is_empty()
            || destination.local.as_usize() <= body.arg_count
            || source.local == destination.local
            || state.addresses[destination.local.as_usize()].is_some()
            || !self.mutable_hierarchy_element(self.mutable_interval_element(backing.certificate)?)
            || !self.mutable_u16_matches(
                body.local_decls[source.local].ty,
                id,
                &state.memory,
                true,
            )?
            || !self.mutable_u16_matches(
                body.local_decls[destination.local].ty,
                id,
                &state.memory,
                true,
            )?
        {
            return Err("hierarchy original source/type/tip differs".into());
        }
        self.check_local_initialization(state, source.local.as_usize(), &[])
    }
}

impl<'tcx> Engine<'tcx> {
    fn mutable_hierarchy_transition_error(&self, error: TransitionError) -> String {
        match error {
            TransitionError::Semantics(reason) => {
                self.categorized_error(UnknownCategory::Semantics, reason)
            }
            TransitionError::Resource(reason) => {
                self.categorized_error(UnknownCategory::ResourceLimit, reason.into())
            }
        }
    }

    fn mutable_hierarchy_namespace(&self, memory: &Memory) -> Result<(), String> {
        let Some(id) = memory.mutable_hierarchy else {
            return Ok(());
        };
        let backing = self.mutable_u16_backing(id, memory)?;
        if backing.hierarchy.is_none() {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "hierarchy namespace has no issued backing".into(),
            ));
        }
        Ok(())
    }

    pub(super) fn mutable_hierarchy_call(
        &mut self,
        state: &mut State,
        call: super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        // Disabled routing performs no role observation, Body scan or term construction.
        if !issuance_enabled() && state.memory.mutable_hierarchy.is_none() {
            return Ok(None);
        }
        if !matches!(state.flow, super::activation_flow::Flow::Unarmed)
            && !self.mutable_metadata_operation(call.instance)
            && !super::super::identity::is_panic_call(self.tcx, call.instance.def_id())
            && !self.is_core_panic_helper(call.instance.def_id())
        {
            self.activation_preclone(&state.flow, call.instance)?;
        }
        if let Some(id) = state.memory.mutable_hierarchy {
            self.activation_charge_backing_schema(&state.flow, &state.memory, id)?;
        }
        self.mutable_hierarchy_namespace(&state.memory)?;
        if state.memory.mutable_hierarchy.is_none()
            && !self.mutable_hierarchy_route(state, &call)?
        {
            return Ok(None);
        }
        if self.mutable_metadata_operation(call.instance)
            || super::super::identity::is_panic_call(self.tcx, call.instance.def_id())
            || self.is_core_panic_helper(call.instance.def_id())
        {
            return Ok(None);
        }
        self.activation_preclone(&state.flow, call.instance)?;
        if DORMANT_CALLS_ENABLED
            && let Some(results) = self.mutable_hierarchy_dormant_call(state, &call)?
        {
            return Ok(Some(results));
        }
        self.mutable_hierarchy_call_transaction(state, call)
    }

    fn mutable_hierarchy_dormant_call(
        &mut self,
        state: &mut State,
        call: &super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        let Some(id) = state.memory.mutable_hierarchy else {
            return Ok(None);
        };
        self.mutable_hierarchy_namespace(&state.memory)?;
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let borrowed = backing
            .hierarchy
            .as_ref()
            .ok_or("dormant hierarchy missing")?;
        if !borrowed.owners.is_empty() || borrowed.pending.is_some() {
            return Ok(None);
        }
        state.flow.require_unarmed()?;
        let before = borrowed.clone();
        let data = backing.data.scalar()?.clone();
        let float_original = self.mutable_hierarchy_float_backing(id, &state.memory)?;
        if call.args.len() > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "dormant hierarchy arguments exceed existing certificate budget".into(),
            ));
        }
        let instance = call.instance;
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
        {
            return Ok(None);
        }
        self.activation_signature_pass(&state.flow, instance)?;
        let signature = self
            .tcx
            .instantiate_bound_regions_with_erased(self.call_poly_signature(instance)?);
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != call.args.len()
            || signature
                .inputs()
                .iter()
                .any(|t| !self.mutable_hierarchy_primitive_for(*t, float_original))
            || !(signature.output().is_unit()
                || self.mutable_hierarchy_primitive_for(signature.output(), float_original))
        {
            return Ok(None);
        }
        self.mutable_u16_body_budget(call.body)?;
        self.mutable_u16_register_current_frame(call.body, &state.flow)?;
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            ..
        } = &call.body.basic_blocks[call.block].terminator().kind
        else {
            return Err("dormant hierarchy requires actual Call".into());
        };
        if call.body.basic_blocks[call.block].is_cleanup
            || call.site.0 != call.body.source.def_id()
            || call.site.1
                != call.body.basic_blocks[call.block]
                    .terminator()
                    .source_info
                    .span
            || args.as_ptr() != call.args.as_ptr()
            || args.len() != call.args.len()
            || *destination != call.destination
            || *target != call.target
            || target.is_none()
            || !destination.projection.is_empty()
            || destination.ty(&call.body.local_decls, self.tcx).ty != signature.output()
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
            || self.specification(instance)?.is_some()
            || !self.configured_contracts(instance)?.is_empty()
        {
            return Err("dormant hierarchy original Call/normal edge differs".into());
        }
        let ty::FnDef(definition, generic) = func.ty(&call.body.local_decls, self.tcx).kind()
        else {
            return Err("dormant hierarchy requires original function Item".into());
        };
        if self.resolve_function_item(*definition, generic.skip_binder())? != instance {
            return Err("dormant hierarchy selected Instance differs".into());
        }
        for (operand, original) in args.iter().zip(signature.inputs()) {
            if operand.node.ty(&call.body.local_decls, self.tcx) != *original {
                return Err("dormant hierarchy primitive original operand type differs".into());
            }
            if let Operand::Copy(place) | Operand::Move(place) = &operand.node {
                self.mutable_hierarchy_dormant_operand(
                    call.body,
                    state,
                    *place,
                    *original,
                    float_original,
                )?;
            }
        }
        // Body availability/schema precede existing builtin priority. No new summary is issued.
        let selected = self.instantiated_body(instance)?;
        self.mutable_u16_body_budget(&selected)?;
        if selected.arg_count != args.len()
            || selected.return_ty() != signature.output()
            || selected
                .args_iter()
                .zip(signature.inputs())
                .any(|(local, t)| {
                    self.tcx
                        .erase_and_anonymize_regions(selected.local_decls[local].ty)
                        != *t
                })
            || selected.basic_blocks.iter().any(|block| {
                block.is_cleanup
                    || match &block.terminator().kind {
                        TerminatorKind::Call { unwind, .. }
                        | TerminatorKind::Drop { unwind, .. }
                        | TerminatorKind::Assert { unwind, .. } => {
                            !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
                        }
                        _ => false,
                    }
            })
        {
            return Err("dormant hierarchy selected Body/schema/unwind differs".into());
        }
        let mut values = Vec::with_capacity(args.len());
        for (arg, original) in args.iter().zip(signature.inputs()) {
            let value = self.evaluate_operand(call.site.0, call.body, state, &arg.node)?;
            self.mutable_hierarchy_primitive_value_for(
                *original,
                &value,
                &state.conditions,
                float_original,
            )?;
            values.push(value);
        }
        let results = if let Some(value) =
            self.builtin(call.body, instance, &values, &values, state, call.site.1)?
        {
            vec![Return {
                flow: activation_flow::Flow::Unarmed,
                value,
                conditions: state.conditions.clone(),
                memory: state.memory.clone(),
            }]
        } else {
            self.call_instance(
                instance,
                values,
                state.conditions.clone(),
                state.memory.clone(),
                call.stack,
                call.site,
            )?
        };
        for result in &results {
            #[cfg(test)]
            self.test_float_return(TestFloatReturnBoundary::Dormant, state, result)?;
            self.mutable_hierarchy_primitive_value_for(
                signature.output(),
                &result.value,
                &result.conditions,
                self.mutable_hierarchy_float_backing(id, &result.memory)?,
            )?;
            self.mutable_hierarchy_dormant_return(id, &before, &data, &result.memory)?;
        }
        Ok(Some(results))
    }

    fn mutable_hierarchy_dormant_operand(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        original: Ty<'tcx>,
        float_original: Option<Ty<'tcx>>,
    ) -> Result<(), String> {
        self.owned_field_footprint(body, place)?;
        let value = self.place(state, place)?;
        self.mutable_hierarchy_primitive_value_for(
            original,
            &value,
            &state.conditions,
            float_original,
        )
    }

    fn mutable_hierarchy_primitive_value(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        let valid = if original.is_unit() {
            matches!(value, Value::Unit)
                || matches!(value, Value::Tuple(fields) if fields.is_empty())
        } else if original == self.tcx.types.bool {
            matches!(value, Value::Bool(term)
                if term.belongs_to(&self.terms) && term.sort() == &Sort::Bool)
        } else if self.mutable_hierarchy_primitive(original) {
            matches!(value, Value::Int {expression,bits,signed}
                if self.integer_type(original) == Some((*bits,*signed))
                && expression.belongs_to(&self.terms) && expression.sort() == &Sort::BitVec(*bits))
        } else {
            false
        };
        if !valid {
            return Err("dormant hierarchy primitive value/type/context differs".into());
        }
        if original == self.tcx.types.char {
            self.prove_char_value(value, conditions)?;
        }
        Ok(())
    }

    fn mutable_hierarchy_dormant_return(
        &self,
        id: usize,
        before: &Hierarchy,
        data: &Term,
        memory: &Memory,
    ) -> Result<(), String> {
        self.mutable_hierarchy_namespace(memory)?;
        if memory.mutable_hierarchy != Some(id) {
            return Err("dormant primitive Return changed namespace".into());
        }
        let backing = self.mutable_u16_backing(id, memory)?;
        let returned = backing
            .hierarchy
            .as_ref()
            .ok_or("dormant Return lost hierarchy")?;
        if !Rc::ptr_eq(&returned.origin, &before.origin)
            || returned.issued < before.issued
            || returned.epoch < before.epoch
            || !returned.owners.is_empty()
            || returned.pending.is_some()
            || *backing.data.scalar()? != *data
        {
            return Err("dormant primitive Return changed origin/counters/data/state".into());
        }
        Ok(())
    }

    fn mutable_hierarchy_associated_type_work(
        &self,
        original: Ty<'tcx>,
        depth: usize,
        work: &mut usize,
    ) -> Result<(), String> {
        *work = work.saturating_add(1);
        if depth >= MAX_INPUT_DEPTH || *work > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "associated original type exceeds existing depth/work budget".into(),
            ));
        }
        match original.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str | ty::Never => {
                Ok(())
            }
            ty::Ref(_, inner, _) | ty::Slice(inner) | ty::RawPtr(inner, _) => {
                self.mutable_hierarchy_associated_type_work(*inner, depth + 1, work)
            }
            ty::Array(inner, count) => {
                *work = work.saturating_add(1);
                if *work > MAX_INPUT_VALUES {
                    return Err(self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "associated original array exceeds existing work budget".into(),
                    ));
                }
                // This accessor only reads an already-literal value; it performs no evaluation.
                if count.try_to_target_usize(self.tcx).is_none() {
                    return Err("associated original array extent is not literal".into());
                }
                self.mutable_hierarchy_associated_type_work(*inner, depth + 1, work)
            }
            ty::Tuple(fields) => {
                for field in fields.iter() {
                    self.mutable_hierarchy_associated_type_work(field, depth + 1, work)?;
                }
                Ok(())
            }
            ty::Adt(_, args) => {
                self.mutable_hierarchy_associated_argument_work(args, depth + 1, work)
            }
            ty::FnDef(_, args) => {
                self.mutable_hierarchy_associated_argument_work(args.skip_binder(), depth + 1, work)
            }
            _ => Err("associated original generic type grammar is unsupported".into()),
        }
    }

    fn mutable_hierarchy_associated_argument_work(
        &self,
        arguments: ty::GenericArgsRef<'tcx>,
        depth: usize,
        work: &mut usize,
    ) -> Result<(), String> {
        for argument in arguments.iter() {
            *work = work.saturating_add(1);
            if depth >= MAX_INPUT_DEPTH || *work > MAX_INPUT_VALUES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "associated arguments exceed existing depth/work budget".into(),
                ));
            }
            match argument.kind() {
                ty::GenericArgKind::Type(original) => {
                    self.mutable_hierarchy_associated_type_work(original, depth, work)?;
                }
                ty::GenericArgKind::Lifetime(_) => {}
                ty::GenericArgKind::Const(_) => {
                    return Err("associated original const argument is unsupported".into());
                }
            }
        }
        Ok(())
    }

    fn mutable_hierarchy_associated_signature_type_work(
        &self,
        original: Ty<'tcx>,
        arguments: ty::GenericArgsRef<'tcx>,
        depth: usize,
        work: &mut usize,
    ) -> Result<(), String> {
        *work = work.saturating_add(1);
        if depth >= MAX_INPUT_DEPTH || *work > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "associated raw signature exceeds existing depth/work budget".into(),
            ));
        }
        match original.kind() {
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Never => Ok(()),
            ty::Ref(_, inner, _) | ty::Slice(inner) => self
                .mutable_hierarchy_associated_signature_type_work(
                    *inner,
                    arguments,
                    depth + 1,
                    work,
                ),
            ty::Tuple(fields) => {
                if fields.len() > MAX_INPUT_VALUES.saturating_sub(*work) {
                    return Err(self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "associated raw signature fields exceed existing budget".into(),
                    ));
                }
                for field in fields.iter() {
                    self.mutable_hierarchy_associated_signature_type_work(
                        field,
                        arguments,
                        depth + 1,
                        work,
                    )?;
                }
                Ok(())
            }
            ty::Param(parameter) => {
                let Some(argument) = arguments.get(parameter.index as usize) else {
                    return Err(self.categorized_error(
                        UnknownCategory::Semantics,
                        "associated raw signature Param lacks original argument".into(),
                    ));
                };
                let ty::GenericArgKind::Type(substituted) = argument.kind() else {
                    return Err(self.categorized_error(
                        UnknownCategory::Semantics,
                        "associated raw signature Param argument is not a Type".into(),
                    ));
                };
                self.mutable_hierarchy_associated_signature_type_work(
                    substituted,
                    arguments,
                    depth + 1,
                    work,
                )
            }
            _ => Err(self.categorized_error(
                UnknownCategory::Semantics,
                "associated raw signature type grammar is unsupported".into(),
            )),
        }
    }

    fn mutable_hierarchy_associated_signature_work(
        &self,
        definition: DefId,
        arguments: ty::GenericArgsRef<'tcx>,
        work: &mut usize,
    ) -> Result<(), String> {
        if self.tcx.def_kind(definition) != DefKind::AssocFn
            || self.tcx.associated_item(definition).is_method()
        {
            return Err("associated raw signature requires static AssocFn".into());
        }
        // Identity access borrows the raw signature. It applies neither generic substitution
        // nor normalization.
        let signature = self
            .tcx
            .fn_sig(definition)
            .instantiate_identity()
            .skip_binder();
        if signature.inputs().len() > MAX_INPUT_VALUES.saturating_sub(*work) {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "associated raw signature input count exceeds existing budget".into(),
            ));
        }
        for original in signature.inputs() {
            self.mutable_hierarchy_associated_signature_type_work(*original, arguments, 0, work)?;
        }
        self.mutable_hierarchy_associated_signature_type_work(
            signature.output(),
            arguments,
            0,
            work,
        )
    }

    fn mutable_hierarchy_associated_borrowed_body(
        &self,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
    ) -> Result<(), String> {
        let mut work = 0;
        self.mutable_hierarchy_associated_argument_work(instance.args, 0, &mut work)?;
        self.mutable_hierarchy_associated_signature_work(
            instance.def_id(),
            instance.args,
            &mut work,
        )?;
        self.mutable_hierarchy_associated_borrowed_body_work(instance, body, &mut work, false, None)
    }

    fn mutable_hierarchy_associated_borrowed_body_work(
        &self,
        instance: ty::Instance<'tcx>,
        body: &Body<'tcx>,
        work: &mut usize,
        activation_shapes: bool,
        activation_flow: Option<&super::activation_flow::Flow>,
    ) -> Result<(), String> {
        if body.source.instance != instance.def
            || body.source.def_id() != instance.def_id()
            || body.source.promoted.is_some()
        {
            return Err("associated borrowed Body provenance differs".into());
        }
        if let Some(flow) = activation_flow {
            // Preliminary Body budget walks blocks before the separate full inventory.
            flow.charge(body.basic_blocks.len())?;
        }
        self.mutable_u16_body_budget(body)?;
        let mut inventory = AssociatedBodyWork {
            engine: self,
            arguments: instance.args,
            locals: body.local_decls.len(),
            work: *work,
            error: None,
            activation_shapes,
            activation_flow,
        };
        inventory.generic_arguments(instance.args, 0)?;
        inventory.charge(
            body.local_decls
                .len()
                .saturating_add(body.basic_blocks.len()),
        )?;
        inventory.charge(
            body.source_scopes
                .len()
                .saturating_add(body.var_debug_info.len()),
        )?;
        if !body.user_type_annotations.is_empty()
            || body.coverage_early_info.is_some()
            || body.coverage_mir_info.is_some()
            || body
                .var_debug_info
                .iter()
                .any(|info| info.composite.is_some())
            || body.local_decls.iter().any(|local| local.user_ty.is_some())
        {
            return Err("associated borrowed auxiliary Body grammar is unsupported".into());
        }
        if let Some(constants) = &body.required_consts {
            inventory.charge(constants.len())?;
        }
        if let Some(items) = &body.mentioned_items {
            inventory.charge(items.len())?;
            for item in items {
                match item.node {
                    rustc_middle::mir::MentionedItem::Fn(original)
                    | rustc_middle::mir::MentionedItem::Drop(original)
                    | rustc_middle::mir::MentionedItem::Closure(original) => {
                        inventory.original_type(original, 0)?;
                    }
                    rustc_middle::mir::MentionedItem::UnsizeCast {
                        source_ty,
                        target_ty,
                    } => {
                        inventory.original_type(source_ty, 0)?;
                        inventory.original_type(target_ty, 0)?;
                    }
                }
            }
        }
        for block in body.basic_blocks.iter() {
            inventory.charge(block.statements.len().saturating_add(1))?;
        }
        for scope in body.source_scopes.iter() {
            if let Some((instance, _)) = scope.inlined {
                inventory.generic_arguments(instance.args, 0)?;
            }
        }
        for local in body.local_decls.iter() {
            if let rustc_middle::mir::ClearCrossCrate::Set(info) = &local.local_info
                && let rustc_middle::mir::LocalInfo::User(rustc_middle::mir::BindingForm::Var(
                    binding,
                )) = info.as_ref()
            {
                inventory.charge(binding.introductions.len())?;
                if let Some((Some(place), _)) = binding.opt_match_place {
                    inventory.visit_place(
                        &place,
                        PlaceContext::NonMutatingUse(
                            rustc_middle::mir::visit::NonMutatingUseContext::Inspect,
                        ),
                        rustc_middle::mir::Location::START,
                    );
                    if let Some(error) = inventory.error.take() {
                        return Err(error);
                    }
                }
            }
        }
        inventory.visit_body(body);
        *work = inventory.work;
        inventory.error.map_or(Ok(()), Err)
    }

    fn mutable_hierarchy_associated_preflight(
        &self,
        instance: ty::Instance<'tcx>,
        work: &mut usize,
    ) -> Result<(), String> {
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || self.tcx.def_kind(instance.def_id()) != DefKind::AssocFn
            || !instance.def_id().is_local()
            || self.tcx.associated_item(instance.def_id()).is_method()
        {
            return Err("associated hierarchy requires a local static Item".into());
        }
        if !self.tcx.is_mir_available(instance.def_id()) {
            return Err(self.missing_body_reason(instance.def_id()));
        }
        // Inspect immutable compiler metadata before instantiation can clone the selected body.
        let original = self.tcx.instance_mir(instance.def);
        if original.source.instance != instance.def
            || original.source.promoted.is_some()
            || original.coroutine.is_some()
        {
            return Err("associated hierarchy original Body provenance differs".into());
        }
        self.mutable_hierarchy_associated_borrowed_body_work(
            instance, original, work, false, None,
        )?;
        if let Some(cached) = self.bodies.borrow().get(&instance) {
            self.mutable_hierarchy_associated_borrowed_body_work(
                instance, cached, work, false, None,
            )?;
        }
        Ok(())
    }

    // This branch authenticates compiler identity only; it never issues a lease.
    fn mutable_hierarchy_associated_identity(
        &self,
        original: Ty<'tcx>,
        instance: ty::Instance<'tcx>,
    ) -> Result<bool, String> {
        if !associated_hierarchy_enabled() {
            return Ok(false);
        }
        let ty::FnDef(definition, arguments) = original.kind() else {
            return Ok(false);
        };
        if self.tcx.def_kind(*definition) != DefKind::AssocFn
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || self.tcx.def_kind(instance.def_id()) != DefKind::AssocFn
            || !instance.def_id().is_local()
        {
            return Ok(false);
        }
        if self.tcx.associated_item(*definition).is_method()
            || self.tcx.associated_item(instance.def_id()).is_method()
        {
            return Ok(false);
        }
        if arguments.skip_binder().len() > MAX_INPUT_VALUES
            || instance.args.len() > MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "associated hierarchy arguments exceed existing budget".into(),
            ));
        }
        let mut work = 0;
        self.mutable_hierarchy_associated_argument_work(arguments.skip_binder(), 0, &mut work)?;
        self.mutable_hierarchy_associated_argument_work(instance.args, 0, &mut work)?;
        self.mutable_hierarchy_associated_signature_work(
            *definition,
            arguments.skip_binder(),
            &mut work,
        )?;
        self.mutable_hierarchy_associated_signature_work(
            instance.def_id(),
            instance.args,
            &mut work,
        )?;
        if self.resolve_function_item(*definition, arguments.skip_binder())? != instance {
            return Ok(false);
        }
        self.mutable_hierarchy_associated_preflight(instance, &mut work)?;
        let original_signature = self
            .tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::fully_monomorphized(),
                self.tcx
                    .fn_sig(*definition)
                    .instantiate(self.tcx, arguments.skip_binder()),
            )
            .map_err(|error| format!("associated original signature normalization: {error:?}"))?;
        let original_signature = self
            .tcx
            .instantiate_bound_regions_with_erased(original_signature);
        let selected_signature = self
            .tcx
            .instantiate_bound_regions_with_erased(self.call_poly_signature(instance)?);
        Ok(original_signature == selected_signature
            && original_signature.safety() == rustc_hir::Safety::Safe
            && original_signature.abi() == rustc_abi::ExternAbi::Rust
            && !original_signature.c_variadic())
    }

    fn mutable_hierarchy_associated_provenance(
        &self,
        instance: ty::Instance<'tcx>,
        selected: &Body<'tcx>,
    ) -> Result<(), String> {
        if self.tcx.def_kind(instance.def_id()) != DefKind::AssocFn {
            return Ok(());
        }
        if !associated_hierarchy_enabled()
            || !instance.def_id().is_local()
            || self.tcx.associated_item(instance.def_id()).is_method()
            || !self.tcx.is_mir_available(instance.def_id())
            || selected.source.instance != instance.def
            || selected.source.def_id() != instance.def_id()
            || selected.source.promoted.is_some()
            || selected.coroutine.is_some()
        {
            return Err("associated hierarchy selected Body provenance differs".into());
        }
        Ok(())
    }

    fn mutable_hierarchy_associated_body(
        &self,
        instance: ty::Instance<'tcx>,
        selected: &Body<'tcx>,
    ) -> Result<(), String> {
        self.mutable_hierarchy_associated_provenance(instance, selected)?;
        if self.tcx.def_kind(instance.def_id()) == DefKind::AssocFn {
            self.mutable_hierarchy_associated_borrowed_body(instance, selected)?;
        }
        Ok(())
    }

    fn activation_associated_body(
        &self,
        instance: ty::Instance<'tcx>,
        selected: &Body<'tcx>,
        flow: &super::activation_flow::Flow,
    ) -> Result<(), String> {
        if matches!(flow, super::activation_flow::Flow::Unarmed) {
            return self.mutable_hierarchy_associated_body(instance, selected);
        }
        self.mutable_hierarchy_associated_provenance(instance, selected)?;
        if self.tcx.def_kind(instance.def_id()) == DefKind::AssocFn {
            let mut admission = 0;
            self.activation_borrowed_signature(instance, &mut admission, flow)?;
            self.mutable_hierarchy_associated_borrowed_body_work(
                instance,
                selected,
                &mut admission,
                true,
                Some(flow),
            )?;
        }
        Ok(())
    }

    fn mutable_hierarchy_route(
        &mut self,
        state: &State,
        call: &super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<bool, String> {
        // Only original whole-u16 Root/pending-root calls may select a new namespace.
        // Routing alone never issues a grant or proves any selected body operation.
        if state.memory.mutable_u16.len() > MAX_INPUT_VALUES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "hierarchy routing exceeds existing backing budget".into(),
            ));
        }
        if state
            .memory
            .mutable_u16
            .iter()
            .any(|b| b.hierarchy.is_some())
        {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "issued hierarchy lost its Memory namespace".into(),
            ));
        }
        if state.memory.mutable_u16.is_empty() || call.args.len() > MAX_INPUT_VALUES {
            return Ok(false);
        }
        let Some(original) = call.body.basic_blocks.get(call.block) else {
            return Ok(false);
        };
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            unwind,
            ..
        } = &original.terminator().kind
        else {
            return Ok(false);
        };
        if args.as_ptr() != call.args.as_ptr()
            || args.len() != call.args.len()
            || *destination != call.destination
            || *target != call.target
            || target.is_none()
            || !destination.projection.is_empty()
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
        {
            return Ok(false);
        }
        let mut source = None;
        for (position, argument) in call.args.iter().enumerate() {
            let (Operand::Copy(place) | Operand::Move(place)) = argument.node else {
                continue;
            };
            let local = place.local.as_usize();
            if !place.projection.is_empty()
                || state.addresses.get(local).is_none_or(Option::is_some)
            {
                continue;
            }
            let Some(Some(Value::MutableU16 { id, role })) = state.locals.get(local) else {
                continue;
            };
            if source.is_some()
                || !matches!(
                    role,
                    symbolic::MutableU16Role::Root | symbolic::MutableU16Role::Child { .. }
                )
                || state.missing_places.check(local, &[]).is_err()
                || !self.mutable_hierarchy_reference(call.body.local_decls[place.local].ty)
            {
                return Ok(false);
            }
            let backing = self.mutable_u16_backing(*id, &state.memory)?;
            if backing.interval.is_some()
                || !self
                    .mutable_hierarchy_element(self.mutable_interval_element(backing.certificate)?)
                || !self.mutable_u16_matches(
                    call.body.local_decls[place.local].ty,
                    *id,
                    &state.memory,
                    true,
                )?
                || self
                    .mutable_hierarchy_bootstrap(call.body, state, place, *id, role)
                    .is_err()
            {
                return Ok(false);
            }
            source = Some(position);
        }
        let Some(position) = source else {
            return Ok(false);
        };
        self.mutable_u16_body_budget(call.body)?;
        let ty::FnDef(definition, generic) = func.ty(&call.body.local_decls, self.tcx).kind()
        else {
            return Ok(false);
        };
        if self.tcx.def_kind(*definition) == DefKind::AssocFn {
            if !self.mutable_hierarchy_associated_identity(
                func.ty(&call.body.local_decls, self.tcx),
                call.instance,
            )? {
                return Ok(false);
            }
        } else if *definition != call.instance.def_id()
            || self.resolve_function_item(*definition, generic.skip_binder())? != call.instance
        {
            return Ok(false);
        }
        self.activation_signature_pass(&state.flow, call.instance)?;
        let Some(signature) = self.mutable_hierarchy_routing_signature(
            call.instance,
            args.len(),
            self.mutable_hierarchy_float_reference_element(
                args[position].node.ty(&call.body.local_decls, self.tcx),
            ),
        )?
        else {
            return Ok(false);
        };
        if !self.mutable_hierarchy_reference(signature.inputs()[position])
            || signature.inputs().iter().enumerate().any(|(i, t)| {
                i != position
                    && !self.mutable_hierarchy_primitive_for(
                        *t,
                        self.mutable_hierarchy_float_reference_element(
                            signature.inputs()[position],
                        ),
                    )
            })
            || destination.ty(&call.body.local_decls, self.tcx).ty != signature.output()
            || self.specification(call.instance)?.is_some()
        {
            return Ok(false);
        }
        let selected = self.instantiated_body(call.instance)?;
        self.activation_associated_body(call.instance, &selected, &state.flow)?;
        self.mutable_hierarchy_selector_with_flow(&selected, position + 1, &state.flow)
    }

    fn mutable_hierarchy_element(&self, original: Ty<'tcx>) -> bool {
        original == self.tcx.types.u16
            || (integer_hierarchy_enabled()
                && matches!(original.kind(), ty::Int(_) | ty::Uint(_))
                && original != self.tcx.types.u8)
            || (bool_hierarchy_enabled() && original == self.tcx.types.bool)
            || (char_hierarchy_enabled() && original == self.tcx.types.char)
            || (float_hierarchy_enabled() && self.float_type(original).is_some())
    }

    fn mutable_hierarchy_reference(&self, original: Ty<'tcx>) -> bool {
        matches!(original.kind(), ty::Ref(_, pointee, rustc_hir::Mutability::Mut)
            if matches!(pointee.kind(), ty::Slice(element)
                if self.mutable_hierarchy_element(*element)))
    }

    fn mutable_hierarchy_routing_signature(
        &self,
        instance: ty::Instance<'tcx>,
        count: usize,
        float_original: Option<Ty<'tcx>>,
    ) -> Result<Option<ty::FnSig<'tcx>>, String> {
        if !matches!(instance.def, ty::InstanceKind::Item(_))
            || !(self.tcx.def_kind(instance.def_id()) == DefKind::Fn
                || (associated_hierarchy_enabled()
                    && instance.def_id().is_local()
                    && self.tcx.def_kind(instance.def_id()) == DefKind::AssocFn
                    && !self.tcx.associated_item(instance.def_id()).is_method()))
        {
            return Ok(None);
        }
        if self.tcx.def_kind(instance.def_id()) == DefKind::AssocFn {
            let mut work = 0;
            self.mutable_hierarchy_associated_argument_work(instance.args, 0, &mut work)?;
            self.mutable_hierarchy_associated_signature_work(
                instance.def_id(),
                instance.args,
                &mut work,
            )?;
            self.mutable_hierarchy_associated_preflight(instance, &mut work)?;
        }
        let signature = self
            .tcx
            .instantiate_bound_regions_with_erased(self.call_poly_signature(instance)?);
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != count
            || !(signature.output().is_unit()
                || self.mutable_hierarchy_primitive_for(signature.output(), float_original))
        {
            return Ok(None);
        }
        Ok(Some(signature))
    }

    fn mutable_hierarchy_call_transaction(
        &mut self,
        state: &mut State,
        call: super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        use symbolic::MutableU16Role;
        if !matches!(state.flow, super::activation_flow::Flow::Unarmed)
            && (self.specification(call.instance)?.is_some()
                || !self.contracts(call.instance.def_id()).is_empty())
        {
            return Err("armed activation contract adapter is not implemented".into());
        }
        self.mutable_hierarchy_namespace(&state.memory)?;
        let super::mutable_u16_children::ChildCall {
            body,
            block,
            instance,
            args,
            destination,
            target,
            stack,
            site,
        } = call;
        state.flow.charge(body.basic_blocks.len())?;
        self.mutable_u16_body_budget(body)?;
        let TerminatorKind::Call {
            func,
            args: original_args,
            destination: original_destination,
            target: original_target,
            unwind,
            ..
        } = &body.basic_blocks[block].terminator().kind
        else {
            return Err("hierarchy handoff requires actual Call".into());
        };
        if args.as_ptr() != original_args.as_ptr()
            || args.len() != original_args.len()
            || destination != *original_destination
            || target != *original_target
            || !(matches!(func.ty(&body.local_decls, self.tcx).kind(), ty::FnDef(d, _)
                if *d == instance.def_id())
                && matches!(instance.def, ty::InstanceKind::Item(_))
                && self.tcx.def_kind(instance.def_id()) == DefKind::Fn
                || self.mutable_hierarchy_associated_identity(
                    func.ty(&body.local_decls, self.tcx),
                    instance,
                )?)
            || !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
            || target.is_none()
            || !destination.projection.is_empty()
            || self.tcx.sess.panic_strategy() != rustc_target::spec::PanicStrategy::Abort
            || self.specification(instance)?.is_some()
        {
            return Err("hierarchy handoff original Call/signature differs".into());
        }
        let ty::FnDef(definition, actual_args) = func.ty(&body.local_decls, self.tcx).kind() else {
            return Err("hierarchy unresolved original callable".into());
        };
        if self.resolve_function_item(*definition, actual_args.skip_binder())? != instance {
            return Err("hierarchy selected Instance differs from original Call".into());
        }
        if self.tcx.def_kind(*definition) == DefKind::AssocFn
            && (site.0 != body.source.def_id()
                || site.1 != body.basic_blocks[block].terminator().source_info.span)
        {
            return Err("associated hierarchy Call occurrence differs".into());
        }
        self.activation_signature_pass(&state.flow, instance)?;
        let signature = self
            .tcx
            .instantiate_bound_regions_with_erased(self.call_poly_signature(instance)?);
        let float_original =
            self.mutable_hierarchy_float_call_element(&signature, &state.memory)?;
        if signature.safety() != rustc_hir::Safety::Safe
            || signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.inputs().len() != args.len()
            || !(signature.output().is_unit()
                || self.mutable_hierarchy_primitive_for(signature.output(), float_original))
            || destination.ty(&body.local_decls, self.tcx).ty != signature.output()
        {
            return Err("hierarchy requires synchronous primitive-return Rust Item".into());
        }
        if self.tcx.def_kind(*definition) == DefKind::AssocFn {
            for (operand, original) in args.iter().zip(signature.inputs()) {
                if self
                    .tcx
                    .erase_and_anonymize_regions(operand.node.ty(&body.local_decls, self.tcx))
                    != *original
                {
                    return Err("associated hierarchy original operand type differs".into());
                }
                if self.mutable_hierarchy_primitive_for(*original, float_original)
                    && let Operand::Copy(place) | Operand::Move(place) = operand.node
                {
                    self.mutable_hierarchy_dormant_operand(
                        body,
                        state,
                        place,
                        *original,
                        float_original,
                    )?;
                }
            }
        }
        let mut source = None;
        for (position, arg) in args.iter().enumerate() {
            if let Operand::Copy(place) | Operand::Move(place) = &arg.node {
                let value = self.raw_local(state, place.local.as_usize())?;
                if self.mutable_u16_contains(&value, &state.memory)? {
                    let Value::MutableU16 { id, role } = value else {
                        return Err("hierarchy argument contains nested authority".into());
                    };
                    if source.is_some()
                        || !place.projection.is_empty()
                        || !matches!(
                            role,
                            MutableU16Role::Root
                                | MutableU16Role::Child { .. }
                                | MutableU16Role::HierarchyChild { .. }
                        )
                    {
                        return Err(self.categorized_error(
                            UnknownCategory::Semantics,
                            "hierarchy duplicate or metadata argument".into(),
                        ));
                    }
                    self.check_local_initialization(state, place.local.as_usize(), &[])?;
                    if state.addresses[place.local.as_usize()].is_some()
                        || !self.mutable_u16_matches(
                            body.local_decls[place.local].ty,
                            id,
                            &state.memory,
                            true,
                        )?
                        || !self.mutable_u16_matches(
                            signature.inputs()[position],
                            id,
                            &state.memory,
                            true,
                        )?
                    {
                        return Err("hierarchy source original type/address differs".into());
                    }
                    source = Some((position, *place, id, role));
                }
            }
        }
        let selected = self.instantiated_body(instance)?;
        self.activation_associated_body(instance, &selected, &state.flow)?;
        // These are actual repeated visits, independent of prepare_body's admission.
        state.flow.charge(selected.basic_blocks.len())?;
        self.mutable_u16_body_budget(&selected)?;
        state.flow.charge(
            selected
                .arg_count
                .saturating_add(selected.basic_blocks.len()),
        )?;
        if selected.arg_count != args.len()
            || selected.return_ty() != signature.output()
            || selected.args_iter().zip(signature.inputs()).any(|(l, t)| {
                self.tcx
                    .erase_and_anonymize_regions(selected.local_decls[l].ty)
                    != *t
            })
            || selected.basic_blocks.iter().any(|b| {
                b.is_cleanup
                    || match &b.terminator().kind {
                        TerminatorKind::Call { unwind, .. }
                        | TerminatorKind::Drop { unwind, .. }
                        | TerminatorKind::Assert { unwind, .. } => {
                            !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable)
                        }
                        _ => false,
                    }
            })
        {
            return Err("hierarchy selected Body/schema/unwind differs".into());
        }
        let Some((position, place, id, role)) = source else {
            if signature
                .inputs()
                .iter()
                .any(|t| !self.mutable_hierarchy_primitive_for(*t, float_original))
            {
                return Err("hierarchy scalar frame has nonprimitive argument".into());
            }
            return self.mutable_hierarchy_scalar_call(
                state,
                &selected,
                super::mutable_u16_children::ChildCall {
                    body,
                    block,
                    instance,
                    args,
                    destination,
                    target,
                    stack,
                    site,
                },
            );
        };
        if signature.inputs().iter().enumerate().any(|(i, t)| {
            i != position && !self.mutable_hierarchy_primitive_for(*t, float_original)
        }) || !self.mutable_hierarchy_element(
            self.mutable_interval_element(state.memory.mutable_u16[id].certificate)?,
        ) {
            return Err("hierarchy source is not original whole u16".into());
        }
        if matches!(role, MutableU16Role::Root) && matches!(args[position].node, Operand::Move(_)) {
            return Err("hierarchy moved original Root is deferred".into());
        }
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        if backing.interval.is_some() {
            return Err("hierarchy intervals are deferred".into());
        }
        let mut hierarchy = if let Some(h) = &backing.hierarchy {
            h.activation_charge_clone(&state.flow)?;
            h.clone()
        } else {
            if !self.mutable_hierarchy_selector_with_flow(&selected, position + 1, &state.flow)? {
                return Ok(None);
            }
            self.mutable_hierarchy_bootstrap(body, state, place, id, &role)?;
            Hierarchy::dormant(backing, backing.data.scalar()?)
        };
        let caller_frame = self.mutable_u16_register_current_frame(body, &state.flow)?;
        let tip = Tip {
            frame: caller_frame,
            statement: std::ptr::from_ref(&body.basic_blocks[block].terminator().kind) as usize,
            local: place.local.as_usize(),
        };
        let lease = match role {
            MutableU16Role::Root => hierarchy
                .issue(
                    0,
                    tip.clone(),
                    state
                        .memory
                        .activation_storage_slots(&state.flow)?
                        .saturating_add(usize::from(backing.hierarchy.is_none()) * 6),
                )
                .map_err(|error| self.mutable_hierarchy_transition_error(error))?,
            MutableU16Role::Child { .. } => {
                if backing.hierarchy.is_some() {
                    return Err("legacy child cannot migrate".into());
                }
                hierarchy
                    .issue(
                        0,
                        tip.clone(),
                        state
                            .memory
                            .activation_storage_slots(&state.flow)?
                            .saturating_add(hierarchy.storage_slots()),
                    )
                    .map_err(|error| self.mutable_hierarchy_transition_error(error))?
            }
            MutableU16Role::HierarchyChild { lease } => {
                if let Some(pending) = &hierarchy.pending {
                    if pending.lease != lease
                        || pending.tip.local != place.local.as_usize()
                        || pending.tip.frame != caller_frame
                    {
                        return Err("hierarchy Call did not use current pending tip".into());
                    }
                    self.mutable_hierarchy_tip(&hierarchy, body)?;
                    let pending = hierarchy
                        .pending
                        .as_mut()
                        .ok_or("pending tip disappeared")?;
                    pending.tip = tip.clone();
                    lease
                } else {
                    let owner = hierarchy.owners.last().ok_or("hierarchy owner missing")?;
                    self.mutable_u16_frame_top(body, &owner.frames)?;
                    hierarchy
                        .issue(
                            lease,
                            tip.clone(),
                            state.memory.activation_storage_slots(&state.flow)?,
                        )
                        .map_err(|error| self.mutable_hierarchy_transition_error(error))?
                }
            }
            MutableU16Role::Metadata { .. }
            | MutableU16Role::ChildMetadata { .. }
            | MutableU16Role::HierarchyMetadata { .. }
            | MutableU16Role::Ghost { .. } => {
                return Err("hierarchy source lacks owner grant".into());
            }
        };
        let selected_frame = self.activation_register_frame(&selected, &state.flow)?;
        let ticket = hierarchy
            .enter(
                &tip,
                selected_frame,
                state
                    .memory
                    .activation_storage_slots(&state.flow)?
                    .saturating_add(usize::from(backing.hierarchy.is_none()) * 6),
            )
            .map_err(|error| self.mutable_hierarchy_transition_error(error))?;
        self.mutable_hierarchy_charge(state, id, &hierarchy)?;
        // Source/selected/duplicate checks precede every sequential argument effect.
        let mut values = Vec::with_capacity(args.len());
        for (i, arg) in args.iter().enumerate() {
            if i == position {
                if matches!(arg.node, Operand::Move(_)) {
                    state
                        .missing_places
                        .consume(place.local.as_usize(), Vec::new())?;
                }
                values.push(Value::MutableU16 {
                    id,
                    role: MutableU16Role::HierarchyChild { lease },
                });
            } else {
                self.mutable_hierarchy_float_operand(body, &arg.node, signature.inputs()[i])?;
                values.push(self.evaluate_operand(site.0, body, state, &arg.node)?);
            }
        }
        for (original, value) in signature.inputs().iter().zip(&values) {
            if *original == self.tcx.types.char {
                self.prove_char_value(value, &state.conditions)?;
            } else if self.float_type(*original).is_some() {
                let current = self.mutable_hierarchy_float_backing(id, &state.memory)?;
                self.mutable_hierarchy_primitive_value_for(
                    *original,
                    value,
                    &state.conditions,
                    current,
                )?;
            }
        }
        self.activation_charge_backing_cow(&state.flow, &state.memory)?;
        let backing = &mut Rc::make_mut(&mut state.memory.mutable_u16)[id];
        backing.phase = super::mutable_u16_children::Phase::Idle;
        backing.hierarchy = Some(hierarchy);
        state.memory.mutable_hierarchy = Some(id);
        self.activation_observe(&mut state.flow, &state.memory)?;
        state
            .flow
            .charge_call_memory(&state.conditions, &state.memory)?;
        let mut results = self.call_instance_flow(
            &mut state.flow,
            instance,
            values,
            state.conditions.clone(),
            state.memory.clone(),
            (stack, site),
        )?;
        for result in &mut results {
            if signature.output() == self.tcx.types.char {
                self.prove_char_value(&result.value, &result.conditions)?;
            } else if self.float_type(signature.output()).is_some() {
                #[cfg(test)]
                self.test_float_return(TestFloatReturnBoundary::WholeChild, state, result)?;
                let current = self.mutable_hierarchy_float_backing(id, &result.memory)?;
                self.mutable_hierarchy_primitive_value_for(
                    signature.output(),
                    &result.value,
                    &result.conditions,
                    current,
                )?;
            }
            if result.memory.mutable_hierarchy != Some(id) {
                return Err("returned hierarchy mode disappeared or changed owner".into());
            }
            self.mutable_u16_backing(id, &result.memory)?;
            if self.mutable_u16_contains(&result.value, &result.memory)? {
                return Err("hierarchy returned executable role".into());
            }
            self.activation_charge_backing_cow(&result.flow, &result.memory)?;
            let h = Rc::make_mut(&mut result.memory.mutable_u16)[id]
                .hierarchy
                .as_mut()
                .ok_or("returned hierarchy disappeared")?;
            h.release(&ticket)?;
            self.activation_observe(&mut result.flow, &result.memory)?;
            // Original masks and current updated data remain untouched on release.
        }
        Ok(Some(results))
    }

    fn mutable_hierarchy_primitive(&self, original: Ty<'tcx>) -> bool {
        matches!(
            original.kind(),
            ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_)
        )
    }

    fn mutable_hierarchy_float_reference_element(&self, original: Ty<'tcx>) -> Option<Ty<'tcx>> {
        if !float_hierarchy_enabled() {
            return None;
        }
        match original.kind() {
            ty::Ref(_, pointee, rustc_hir::Mutability::Mut) => match pointee.kind() {
                ty::Slice(element) if self.float_type(*element).is_some() => Some(*element),
                _ => None,
            },
            _ => None,
        }
    }

    fn mutable_hierarchy_float_backing(
        &self,
        id: usize,
        memory: &Memory,
    ) -> Result<Option<Ty<'tcx>>, String> {
        if !float_hierarchy_enabled() {
            return Ok(None);
        }
        let backing = self.mutable_u16_backing(id, memory)?;
        let original = self.mutable_interval_element(backing.certificate)?;
        Ok(self.float_type(original).map(|_| original))
    }

    fn mutable_hierarchy_float_call_element(
        &self,
        signature: &ty::FnSig<'tcx>,
        memory: &Memory,
    ) -> Result<Option<Ty<'tcx>>, String> {
        if !float_hierarchy_enabled() {
            return Ok(None);
        }
        if let Some(id) = memory.mutable_hierarchy {
            return self.mutable_hierarchy_float_backing(id, memory);
        }
        // Routing types select a candidate only. Actual source/backing checks still precede grant.
        let mut element = None;
        for original in signature.inputs() {
            if let Some(found) = self.mutable_hierarchy_float_reference_element(*original)
                && element.replace(found).is_some()
            {
                return Ok(None);
            }
        }
        Ok(element)
    }

    fn mutable_hierarchy_primitive_for(
        &self,
        original: Ty<'tcx>,
        float_original: Option<Ty<'tcx>>,
    ) -> bool {
        self.mutable_hierarchy_primitive(original)
            || (float_hierarchy_enabled()
                && float_original == Some(original)
                && self.float_type(original).is_some())
    }

    fn mutable_hierarchy_float_operand(
        &self,
        body: &Body<'tcx>,
        operand: &Operand<'tcx>,
        original: Ty<'tcx>,
    ) -> Result<(), String> {
        if self.float_type(original).is_none() {
            return Ok(());
        }
        if !float_hierarchy_enabled() || operand.ty(&body.local_decls, self.tcx) != original {
            return Err("hierarchy Float operand original type differs".into());
        }
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            self.owned_field_footprint(body, *place)?;
        }
        Ok(())
    }

    fn mutable_hierarchy_primitive_value_for(
        &self,
        original: Ty<'tcx>,
        value: &Value,
        conditions: &[Term],
        float_original: Option<Ty<'tcx>>,
    ) -> Result<(), String> {
        if self.float_type(original).is_none() {
            return self.mutable_hierarchy_primitive_value(original, value, conditions);
        }
        if !self.mutable_hierarchy_primitive_for(original, float_original) {
            return Err("hierarchy Float scalar differs from current original backing".into());
        }
        self.prove_float_pair(value, self.float_type(original).unwrap(), conditions)
    }

    #[cfg(test)]
    fn mutable_hierarchy_selector(
        &self,
        selected: &Body<'tcx>,
        argument: usize,
    ) -> Result<bool, String> {
        self.mutable_hierarchy_selector_with_flow(
            selected,
            argument,
            &super::activation_flow::Flow::Unarmed,
        )
    }

    fn mutable_hierarchy_selector_with_flow(
        &self,
        selected: &Body<'tcx>,
        argument: usize,
        flow: &super::activation_flow::Flow,
    ) -> Result<bool, String> {
        flow.charge(selected.basic_blocks.len())?;
        self.mutable_u16_body_budget(selected)?;
        flow.charge(selected.local_decls.len())?;
        let root = rustc_middle::mir::Local::from_usize(argument);
        if argument == 0
            || argument > selected.arg_count
            || selected
                .local_decls
                .get(root)
                .is_none_or(|d| !self.mutable_hierarchy_reference(d.ty))
        {
            return Ok(false);
        }
        let float_original =
            self.mutable_hierarchy_float_reference_element(selected.local_decls[root].ty);
        flow.charge(selected.basic_blocks.len())?;
        for block in selected.basic_blocks.iter() {
            flow.charge(block.statements.len().saturating_add(1))?;
            let mut lineage = std::collections::BTreeSet::from([root]);
            for statement in &block.statements {
                match &statement.kind {
                    StatementKind::Assign(a) if a.0.projection.is_empty() => {
                        let follows = matches!(&a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, p)
                            if p.projection.as_ref() == [ProjectionElem::Deref]
                            && lineage.contains(&p.local)
                            && selected.local_decls[p.local].ty == selected.local_decls[root].ty
                            && selected.local_decls[a.0.local].ty == selected.local_decls[root].ty
                            && self.mutable_hierarchy_reference(
                                selected.local_decls[p.local].ty)
                            && self.mutable_hierarchy_reference(
                                selected.local_decls[a.0.local].ty));
                        lineage.remove(&a.0.local);
                        if follows {
                            lineage.insert(a.0.local);
                        }
                    }
                    StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                        lineage.remove(local);
                    }
                    _ => {}
                }
            }
            let TerminatorKind::Call {
                func,
                args,
                target: Some(_),
                unwind,
                ..
            } = &block.terminator().kind
            else {
                continue;
            };
            if !matches!(unwind, rustc_middle::mir::UnwindAction::Unreachable) {
                continue;
            }
            let ty::FnDef(definition, generic) = func.ty(&selected.local_decls, self.tcx).kind()
            else {
                continue;
            };
            flow.charge(generic.skip_binder().len().saturating_add(1))?;
            let instance = self.resolve_function_item(*definition, generic.skip_binder())?;
            self.activation_signature_pass(flow, instance)?;
            if self.tcx.def_kind(*definition) == DefKind::AssocFn
                && !self.mutable_hierarchy_associated_identity(
                    func.ty(&selected.local_decls, self.tcx),
                    instance,
                )?
            {
                continue;
            }
            let Some(signature) =
                self.mutable_hierarchy_routing_signature(instance, args.len(), float_original)?
            else {
                continue;
            };
            let mut receiver = None;
            let mut eligible = true;
            flow.charge(args.len())?;
            for (position, (operand, original)) in args.iter().zip(signature.inputs()).enumerate() {
                if self.mutable_hierarchy_reference(*original) {
                    let follows = matches!(operand.node, Operand::Copy(p) | Operand::Move(p)
                        if p.projection.is_empty() && lineage.contains(&p.local)
                        && *original == selected.local_decls[root].ty
                        && selected.local_decls[p.local].ty == selected.local_decls[root].ty
                        && self.mutable_hierarchy_reference(
                                selected.local_decls[p.local].ty));
                    if !follows || receiver.replace(position).is_some() {
                        eligible = false;
                    }
                } else if !self.mutable_hierarchy_primitive_for(*original, float_original) {
                    eligible = false;
                }
            }
            if eligible && receiver.is_some() {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn mutable_u16_register_current_frame(
        &self,
        body: &Body<'tcx>,
        flow: &super::activation_flow::Flow,
    ) -> Result<usize, String> {
        flow.charge(self.bodies.borrow().len())?;
        let original = self
            .bodies
            .borrow()
            .values()
            .find(|candidate| std::ptr::eq(candidate.as_ref(), body))
            .cloned()
            .ok_or("hierarchy current instantiated Body unavailable")?;
        self.activation_register_frame(&original, flow)
    }

    fn activation_register_frame(
        &self,
        body: &Rc<Body<'tcx>>,
        flow: &super::activation_flow::Flow,
    ) -> Result<usize, String> {
        flow.charge(
            body.basic_blocks
                .len()
                .saturating_add(self.mutable_u16_frames.borrow().len())
                .saturating_add(1),
        )?;
        self.mutable_u16_register_frame(body)
    }

    fn mutable_hierarchy_charge(
        &self,
        state: &State,
        id: usize,
        next: &Hierarchy,
    ) -> Result<(), String> {
        if let Some(old) = &state.memory.mutable_u16[id].hierarchy {
            old.activation_charge_storage(&state.flow)?;
        }
        next.activation_charge_storage(&state.flow)?;
        let old = state.memory.mutable_u16[id]
            .hierarchy
            .as_ref()
            .map_or(0, Hierarchy::storage_slots);
        if state
            .memory
            .activation_storage_slots(&state.flow)?
            .saturating_sub(old)
            .saturating_add(next.storage_slots())
            .saturating_add(usize::from(state.memory.mutable_hierarchy.is_none()))
            > MAX_INPUT_VALUES
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "hierarchy exceeds existing combined storage budget".into(),
            ));
        }
        Ok(())
    }

    fn mutable_hierarchy_tip(
        &self,
        hierarchy: &Hierarchy,
        body: &Body<'tcx>,
    ) -> Result<(), String> {
        let tip = &hierarchy
            .pending
            .as_ref()
            .ok_or("pending hierarchy missing")?
            .tip;
        self.mutable_u16_frame_top(body, &[tip.frame])?;
        self.mutable_u16_body_budget(body)?;
        if !body.basic_blocks.iter().any(|b| {
            b.statements
                .iter()
                .any(|s| std::ptr::from_ref(&s.kind) as usize == tip.statement)
        }) {
            return Err("hierarchy pending occurrence not in current Body".into());
        }
        Ok(())
    }

    fn mutable_hierarchy_bootstrap(
        &self,
        body: &Body<'tcx>,
        state: &State,
        place: Place<'tcx>,
        id: usize,
        role: &symbolic::MutableU16Role,
    ) -> Result<(), String> {
        match role {
            symbolic::MutableU16Role::Root => self.mutable_u16_role_live(id, role, &state.memory),
            symbolic::MutableU16Role::Child { generation } => {
                self.mutable_u16_staging_tip(body, state, place.local.as_usize(), id, *generation)?;
                let backing = &state.memory.mutable_u16[id];
                let super::mutable_u16_children::Phase::Pending { certificate } = backing.phase
                else {
                    return Err("bootstrap is not original pending root handoff".into());
                };
                let source = self.mutable_u16_original_staging_source(certificate, body)?;
                self.check_local_initialization(state, source, &[])?;
                if !matches!(self.raw_local(state, source)?, Value::MutableU16 { id: other,
                    role: symbolic::MutableU16Role::Root } if other == id)
                {
                    return Err("legacy active child cannot bootstrap hierarchy".into());
                }
                Ok(())
            }
            symbolic::MutableU16Role::Metadata { .. }
            | symbolic::MutableU16Role::ChildMetadata { .. }
            | symbolic::MutableU16Role::HierarchyChild { .. }
            | symbolic::MutableU16Role::HierarchyMetadata { .. }
            | symbolic::MutableU16Role::Ghost { .. } => {
                Err("bootstrap source is not original root handoff".into())
            }
        }
    }
}

impl Hierarchy {
    fn dormant(backing: &super::mutable_u16::Backing, data: &Term) -> Self {
        Self {
            origin: Rc::new(Origin {
                certificate: backing.certificate,
                allocation: backing.allocation,
                capacity: backing.length.clone(),
                data_context: data.clone(),
            }),
            issued: backing.generation,
            epoch: 0,
            owners: Vec::new(),
            pending: None,
        }
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn mutable_hierarchy_stage(
        &self,
        body: &Body<'tcx>,
        state: &mut State,
        destination: Place<'tcx>,
        value: &Rvalue<'tcx>,
        occurrence: &StatementKind<'tcx>,
    ) -> Result<bool, String> {
        if !issuance_enabled() && state.memory.mutable_hierarchy.is_none() {
            return Ok(false);
        }
        self.mutable_hierarchy_namespace(&state.memory)?;
        let Rvalue::Ref(_, BorrowKind::Mut { .. }, source) = value else {
            return Ok(false);
        };
        let Value::MutableU16 { id, role } = self.raw_local(state, source.local.as_usize())? else {
            return Ok(false);
        };
        if state.memory.mutable_u16[id].hierarchy.is_none() {
            return Ok(false);
        }
        let lease = match role {
            symbolic::MutableU16Role::Root => 0,
            symbolic::MutableU16Role::HierarchyChild { lease } => lease,
            symbolic::MutableU16Role::Metadata { .. }
            | symbolic::MutableU16Role::Child { .. }
            | symbolic::MutableU16Role::ChildMetadata { .. }
            | symbolic::MutableU16Role::HierarchyMetadata { .. }
            | symbolic::MutableU16Role::Ghost { .. } => {
                return Err("legacy/metadata source cannot stage hierarchy".into());
            }
        };
        self.mutable_u16_body_budget(body)?;
        if !matches!(occurrence, StatementKind::Assign(a)
            if a.0 == destination && std::ptr::eq(&a.1, value))
            || !body.basic_blocks.iter().any(|b| {
                b.statements
                    .iter()
                    .any(|s| std::ptr::eq(&s.kind, occurrence))
            })
            || source.projection.as_ref() != [ProjectionElem::Deref]
            || !destination.projection.is_empty()
            || destination.local.as_usize() <= body.arg_count
            || source.local == destination.local
            || state.addresses[source.local.as_usize()].is_some()
            || state.addresses[destination.local.as_usize()].is_some()
            || !self.mutable_u16_matches(
                body.local_decls[source.local].ty,
                id,
                &state.memory,
                true,
            )?
            || !self.mutable_u16_matches(
                body.local_decls[destination.local].ty,
                id,
                &state.memory,
                true,
            )?
        {
            return Err("hierarchy staging original occurrence/type/private source differs".into());
        }
        self.check_local_initialization(state, source.local.as_usize(), &[])?;
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let borrowed = backing
            .hierarchy
            .as_ref()
            .ok_or("hierarchy staging namespace missing")?;
        borrowed.activation_charge_clone(&state.flow)?;
        let mut h = borrowed.clone();
        let frame = self.mutable_u16_register_current_frame(body, &state.flow)?;
        let next = Tip {
            frame,
            statement: std::ptr::from_ref(occurrence) as usize,
            local: destination.local.as_usize(),
        };
        let next_lease = if let Some(pending) = &h.pending {
            if pending.lease != lease || pending.tip.local != source.local.as_usize() {
                return Err("hierarchy old staging tip cannot advance".into());
            }
            self.mutable_hierarchy_tip(&h, body)?;
            let old = pending.tip.clone();
            h.advance(&old, next, source.local.as_usize())?;
            lease
        } else {
            if let Some(owner) = h.owners.last() {
                self.mutable_u16_frame_top(body, &owner.frames)?;
            } else if lease != 0 {
                return Err("hierarchy source has no current owner".into());
            }
            h.issue(
                lease,
                next,
                state.memory.activation_storage_slots(&state.flow)?,
            )
            .map_err(|error| self.mutable_hierarchy_transition_error(error))?
        };
        self.mutable_hierarchy_charge(state, id, &h)?;
        self.activation_charge_backing_cow(&state.flow, &state.memory)?;
        Rc::make_mut(&mut state.memory.mutable_u16)[id].hierarchy = Some(h);
        // Sole private destination was authenticated before this ordinary exact write.
        self.write(
            state,
            destination,
            Value::MutableU16 {
                id,
                role: symbolic::MutableU16Role::HierarchyChild { lease: next_lease },
            },
        )?;
        Ok(true)
    }

    pub(super) fn mutable_hierarchy_exit(
        &self,
        body: &Body<'tcx>,
        arguments: &[Value],
        id: usize,
        memory: &Memory,
        flow: &super::activation_flow::Flow,
    ) -> Result<(), String> {
        self.activation_charge_backing_schema(flow, memory, id)?;
        let backing = self.mutable_u16_backing(id, memory)?;
        let h = backing
            .hierarchy
            .as_ref()
            .ok_or("hierarchy exit namespace missing")?;
        if h.pending.is_some() {
            return Err("pending hierarchy cannot leave frame".into());
        }
        let Some(owner) = h.owners.last() else {
            return Ok(());
        };
        self.mutable_u16_frame_top(body, &owner.frames)?;
        flow.charge(arguments.len())?;
        let count = arguments
            .iter()
            .filter(|v| {
                matches!(v,
            Value::MutableU16 { id: other,
                role: symbolic::MutableU16Role::HierarchyChild { lease } }
                if *other == id && *lease == owner.lease)
            })
            .count();
        if count != usize::from(owner.frames.len() == 1) {
            return Err("hierarchy Return lacks exact owning frame argument".into());
        }
        Ok(())
    }

    fn mutable_hierarchy_scalar_call(
        &mut self,
        state: &mut State,
        selected: &Rc<Body<'tcx>>,
        call: super::mutable_u16_children::ChildCall<'_, 'tcx>,
    ) -> Result<Option<Vec<Return>>, String> {
        let super::mutable_u16_children::ChildCall {
            body,
            instance,
            args,
            stack,
            site,
            ..
        } = call;
        let Some(id) = state.memory.mutable_hierarchy else {
            return Ok(None);
        };
        let backing = self.mutable_u16_backing(id, &state.memory)?;
        let float_original = self.mutable_hierarchy_float_backing(id, &state.memory)?;
        let borrowed = backing
            .hierarchy
            .as_ref()
            .ok_or("scalar hierarchy namespace missing")?;
        borrowed.activation_charge_clone(&state.flow)?;
        let before = borrowed.clone();
        if before.owners.is_empty() {
            return Ok(None);
        }
        if before.pending.is_some() {
            return Err("pending hierarchy cannot call scalar".into());
        }
        let owner = before.owners.last().unwrap();
        self.mutable_u16_frame_top(body, &owner.frames)?;
        let depth = before.owners.iter().map(|o| o.frames.len()).sum::<usize>();
        if depth >= MAX_INPUT_DEPTH {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "hierarchy scalar depth exceeds existing budget".into(),
            ));
        }
        let frame = self.activation_register_frame(selected, &state.flow)?;
        before.activation_charge_clone(&state.flow)?;
        let mut entered = before.clone();
        entered.owners.last_mut().unwrap().frames.push(frame);
        self.mutable_hierarchy_charge(state, id, &entered)?;
        let mut values = Vec::with_capacity(args.len());
        for (arg, local) in args.iter().zip(selected.args_iter()) {
            self.mutable_hierarchy_float_operand(body, &arg.node, selected.local_decls[local].ty)?;
            values.push(self.evaluate_operand(site.0, body, state, &arg.node)?);
        }
        for (local, value) in selected.args_iter().zip(&values) {
            if selected.local_decls[local].ty == self.tcx.types.char {
                self.prove_char_value(value, &state.conditions)?;
            } else if self.float_type(selected.local_decls[local].ty).is_some() {
                self.mutable_hierarchy_primitive_value_for(
                    selected.local_decls[local].ty,
                    value,
                    &state.conditions,
                    float_original,
                )?;
            }
        }
        entered.activation_charge_clone(&state.flow)?;
        self.activation_charge_backing_cow(&state.flow, &state.memory)?;
        Rc::make_mut(&mut state.memory.mutable_u16)[id].hierarchy = Some(entered.clone());
        self.activation_observe(&mut state.flow, &state.memory)?;
        state
            .flow
            .charge_call_memory(&state.conditions, &state.memory)?;
        #[cfg(test)]
        let before_steps = self.steps;
        let mut results = self.call_instance_flow(
            &mut state.flow,
            instance,
            values,
            state.conditions.clone(),
            state.memory.clone(),
            (stack, site),
        )?;
        for result in &mut results {
            if selected.return_ty() == self.tcx.types.char {
                self.prove_char_value(&result.value, &result.conditions)?;
            } else if self.float_type(selected.return_ty()).is_some() {
                #[cfg(test)]
                self.test_float_return(TestFloatReturnBoundary::ActiveScalar, state, result)?;
                let current = self.mutable_hierarchy_float_backing(id, &result.memory)?;
                self.mutable_hierarchy_primitive_value_for(
                    selected.return_ty(),
                    &result.value,
                    &result.conditions,
                    current,
                )?;
            }
            if result.memory.mutable_hierarchy != Some(id) {
                return Err("scalar returned hierarchy mode differs".into());
            }
            self.mutable_u16_backing(id, &result.memory)?;
            if self.mutable_u16_contains(&result.value, &result.memory)? {
                return Err("hierarchy scalar result carries role".into());
            }
            self.activation_charge_backing_cow(&result.flow, &result.memory)?;
            let returned = Rc::make_mut(&mut result.memory.mutable_u16)[id]
                .hierarchy
                .as_mut()
                .ok_or("hierarchy scalar returned namespace disappeared")?;
            if !Rc::ptr_eq(&returned.origin, &entered.origin)
                || returned.pending.is_some()
                || returned.issued < entered.issued
                || returned.epoch < entered.epoch
                || returned.owners != entered.owners
            {
                return Err("hierarchy scalar Return changed issuer/prefix/top".into());
            }
            self.mutable_u16_frame_top(selected, &returned.owners.last().unwrap().frames)?;
            returned.owners.last_mut().unwrap().frames.pop();
            self.activation_observe(&mut result.flow, &result.memory)?;
        }
        #[cfg(test)]
        if !matches!(state.flow, super::activation_flow::Flow::Unarmed) {
            let actual_name = format!(
                "{} {:?}",
                self.tcx.def_path_str(instance.def_id()),
                instance.args
            );
            assert!(self.steps > before_steps);
            assert!(!results.is_empty());
            assert!(
                self.proof
                    .body_entries
                    .iter()
                    .any(|e| e.instance == actual_name)
            );
            assert!(
                self.bodies
                    .borrow()
                    .get(&instance)
                    .is_some_and(|actual| Rc::ptr_eq(actual, selected))
            );
            eprintln!(
                "carrier actual Armed scalar Body={actual_name} Returns={}",
                results.len()
            );
        }
        Ok(Some(results))
    }
}

#[cfg(test)]
pub(super) fn compiler_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    outer: &Rc<Body<'tcx>>,
    leaf: &Rc<Body<'tcx>>,
    base: &State,
) -> String {
    tests::run(engine, root, outer, leaf, base);
    tests::production_call(engine, root, base);
    "original is_empty uses its certified metadata relation".into()
}

#[cfg(test)]
impl Engine<'_> {
    pub(super) fn mutable_hierarchy_primitive_value_probe(
        &self,
        value: &Value,
    ) -> Result<(), String> {
        self.mutable_hierarchy_primitive_value(self.tcx.types.bool, value, &[])
    }
    pub(super) fn mutable_hierarchy_char_value_probe(
        &self,
        value: &Value,
        conditions: &[Term],
    ) -> Result<(), String> {
        self.mutable_hierarchy_primitive_value(self.tcx.types.char, value, conditions)
    }
}

#[cfg(test)]
pub(super) fn compiler_element_boundary_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    element: Ty<'tcx>,
    wrong: Ty<'tcx>,
) {
    let (block, data) = root
        .basic_blocks
        .iter_enumerated()
        .find(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&root.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let value = engine
        .mutable_u16_input(element, &mut memory, &mut conditions)
        .unwrap();
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; root.local_decls.len()],
        addresses: vec![None; root.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: Default::default(),
        conditions,
        memory,
    };
    state.locals[1] = Some(value);
    for statement in &data.statements {
        if let StatementKind::Assign(a) = &statement.kind
            && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
        {
            assert!(
                engine
                    .mutable_u16_stage(root, &mut state, a.0, &a.1, &statement.kind)
                    .unwrap()
            );
        }
    }
    let call = || super::mutable_u16_children::ChildCall {
        body: root,
        block,
        instance,
        args,
        destination: *destination,
        target: *target,
        stack: &[],
        site: (root.source.def_id(), data.terminator().source_info.span),
    };
    let is_bool = element == engine.tcx.types.bool;
    let is_char = element == engine.tcx.types.char;
    assert_eq!(
        engine.mutable_hierarchy_route(&state, &call()).unwrap(),
        if is_bool {
            BOOL_HIERARCHY_ENABLED
        } else if is_char {
            CHAR_HIERARCHY_ENABLED
        } else {
            INTEGER_HIERARCHY_ENABLED
        }
    );
    if is_char && !CHAR_HIERARCHY_ENABLED {
        let mut disabled = state.clone();
        let slots = disabled.memory.storage_slots();
        let data = disabled.memory.mutable_u16[0].data.clone();
        let conditions = disabled.conditions.clone();
        assert!(
            engine
                .mutable_hierarchy_call(&mut disabled, call())
                .unwrap()
                .is_none()
        );
        assert!(disabled.memory.mutable_hierarchy.is_none());
        assert_eq!(disabled.memory.storage_slots(), slots);
        assert_eq!(disabled.memory.mutable_u16[0].data, data);
        assert_eq!(disabled.conditions, conditions);
    }
    let _integer_scope = (!is_bool && !is_char).then(TestIntegerHierarchy::enable);
    let _char_scope = is_char.then(TestCharHierarchy::enable);
    let _bool_scope = is_bool.then(TestBoolHierarchy::enable);
    assert!(engine.mutable_hierarchy_route(&state, &call()).unwrap());
    for excluded in [
        engine.tcx.types.u8,
        engine.tcx.types.bool,
        engine.tcx.types.char,
        engine.tcx.types.f32,
        engine.tcx.types.f64,
    ] {
        assert_eq!(
            engine.mutable_hierarchy_element(excluded),
            (bool_hierarchy_enabled() && excluded == engine.tcx.types.bool)
                || (char_hierarchy_enabled() && excluded == engine.tcx.types.char)
                || (float_hierarchy_enabled() && engine.float_type(excluded).is_some())
        );
    }
    let selected = engine.instantiated_body(instance).unwrap();
    assert!(engine.mutable_hierarchy_selector(&selected, 1).unwrap());
    let mut forged = (*selected).clone();
    let wrong_ref = Ty::new_mut_ref(
        engine.tcx,
        engine.tcx.lifetimes.re_erased,
        Ty::new_slice(engine.tcx, wrong),
    );
    for declaration in forged.local_decls.iter_mut().skip(forged.arg_count + 1) {
        if declaration.ty == root.local_decls[rustc_middle::mir::Local::from_usize(1)].ty {
            declaration.ty = wrong_ref;
        }
    }
    assert!(!engine.mutable_hierarchy_selector(&forged, 1).unwrap());
    let mut wrong_memory = Memory::default();
    let mut wrong_conditions = Vec::new();
    let wrong_value = engine
        .mutable_u16_input(wrong, &mut wrong_memory, &mut wrong_conditions)
        .unwrap();
    let mut wrong_state = state.clone();
    wrong_state.memory = wrong_memory;
    wrong_state.conditions = wrong_conditions;
    let source = match args[0].node {
        Operand::Copy(p) | Operand::Move(p) => p.local.as_usize(),
        _ => unreachable!(),
    };
    wrong_state.locals[source] = Some(wrong_value);
    assert!(
        !engine
            .mutable_hierarchy_route(&wrong_state, &call())
            .unwrap()
    );
    let before = wrong_state.memory.mutable_u16[0].data.clone();
    assert!(
        engine
            .mutable_hierarchy_call(&mut wrong_state, call())
            .unwrap()
            .is_none()
    );
    assert_eq!(wrong_state.memory.mutable_u16[0].data, before);
    if is_char {
        super::mutable_u16::compiler_char_hierarchy_backing_probe(engine, &state.memory);
    }
    if is_bool || is_char {
        if is_bool {
            super::mutable_u16::compiler_bool_hierarchy_backing_probe(engine, &state.memory);
        }
        let mut consumed = state.clone();
        consumed.missing_places.consume(source, Vec::new()).unwrap();
        assert!(!engine.mutable_hierarchy_route(&consumed, &call()).unwrap());
        let original_data = consumed.memory.mutable_u16[0].data.clone();
        assert!(
            engine
                .mutable_hierarchy_call(&mut consumed, call())
                .unwrap()
                .is_none()
        );
        assert_eq!(consumed.memory.mutable_u16[0].data, original_data);
        let mut consumed_backing = state.clone();
        let allocation = consumed_backing.memory.mutable_u16[0].allocation;
        consumed_backing
            .memory
            .missing_places
            .consume(allocation, Vec::new())
            .unwrap();
        assert!(
            engine
                .mutable_hierarchy_route(&consumed_backing, &call())
                .is_err()
        );
    }
    let results = engine
        .mutable_hierarchy_call(&mut state, call())
        .unwrap()
        .unwrap();
    assert!(!results.is_empty());
    let associated_char =
        engine.tcx.item_name(root.source.def_id()).as_str() == "root_associated_char";
    let leaf_name = if associated_char {
        "AssociatedDomains::leaf_char"
    } else if is_bool {
        "leaf_bool"
    } else if is_char {
        "leaf_char"
    } else if element == engine.tcx.types.i32 {
        "leaf_i32"
    } else {
        assert_eq!(element, engine.tcx.types.usize);
        "leaf_usize"
    };
    assert!(
        engine
            .proof
            .body_entries
            .iter()
            .any(|entry| entry.function == leaf_name)
    );
    if is_char {
        assert!(engine.proof.body_entries.iter().any(|entry| entry.function
            == if associated_char {
                "AssociatedDomains::scalar_char"
            } else {
                "scalar_char"
            }));
    }
    for result in results {
        let backing = engine.mutable_u16_backing(0, &result.memory).unwrap();
        assert_eq!(
            engine
                .mutable_interval_element(backing.certificate)
                .unwrap(),
            element
        );
        let hierarchy = backing.hierarchy.as_ref().unwrap();
        assert!(hierarchy.owners.is_empty() && hierarchy.pending.is_none());
        assert!(hierarchy.issued >= 2);
        if is_bool {
            compiler_bool_return_probe(engine, root, block, source, &result);
        } else if is_char {
            compiler_char_return_probe(engine, root, block, source, &result);
            compiler_char_scalar_probe(engine, &result, associated_char);
        }
    }
}

#[cfg(test)]
fn compiler_bool_return_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    block: rustc_middle::mir::BasicBlock,
    source: usize,
    result: &Return,
) {
    super::mutable_u16::compiler_bool_hierarchy_backing_probe(engine, &result.memory);
    let backing = engine
        .mutable_u16_backing(0, &result.memory)
        .unwrap()
        .clone();
    let original = backing.hierarchy.as_ref().unwrap();
    let current = original.metadata(0).unwrap();
    original.observe(current).unwrap();
    assert!(
        original
            .observe(Metadata {
                epoch: current.epoch - 1,
                ..current
            })
            .is_err()
    );
    assert!(
        engine
            .mutable_u16_role_live(
                0,
                &symbolic::MutableU16Role::HierarchyChild {
                    lease: original.issued
                },
                &result.memory
            )
            .is_err()
    );
    let mut no_namespace = result.memory.clone();
    no_namespace.mutable_hierarchy = None;
    assert!(engine.mutable_u16_backing(0, &no_namespace).is_err());
    let mut stale_generation = result.memory.clone();
    Rc::make_mut(&mut stale_generation.mutable_u16)[0].generation = original.issued + 1;
    assert!(engine.mutable_u16_backing(0, &stale_generation).is_err());
    let mut missing = result.memory.clone();
    missing
        .missing_places
        .consume(backing.allocation, Vec::new())
        .unwrap();
    assert!(engine.mutable_u16_backing(0, &missing).is_err());
    let frame = engine.mutable_u16_register_frame(root).unwrap();
    let tip = Tip {
        frame,
        statement: block.as_usize(),
        local: source,
    };
    let mut next = original.clone();
    let slots = result.memory.storage_slots();
    let lease = next.issue(0, tip.clone(), slots).unwrap();
    assert!(next.access(0).is_err());
    let mut wrong_tip = tip.clone();
    wrong_tip.local += 1;
    assert!(next.enter(&wrong_tip, frame, slots).is_err());
    let ticket = next.enter(&tip, frame, slots).unwrap();
    next.access(lease).unwrap();
    assert!(next.access(0).is_err());
    let mut rollback = next.clone();
    rollback.epoch = ticket.epoch_floor - 1;
    assert!(rollback.release(&ticket).is_err());
    next.release(&ticket).unwrap();
    next.access(0).unwrap();
    assert!(next.access(lease).is_err());
    let mut exhausted = original.clone();
    assert!(matches!(
        exhausted.issue(0, tip, MAX_INPUT_VALUES),
        Err(TransitionError::Resource(_))
    ));
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    let zero = symbolic::integer(&engine.terms, 0, bits, false);
    let nonempty = symbolic::binary(&engine.terms, "lt", zero.clone(), backing.length.clone())
        .unwrap()
        .boolean()
        .unwrap();
    let observed = engine
        .terms
        .apply(
            Op::Select,
            &[
                backing.data.scalar().unwrap().clone(),
                zero.integer().unwrap().0.clone(),
            ],
        )
        .unwrap();
    assert_eq!(observed.sort(), &Sort::Bool);
    let mut denied = result.conditions.clone();
    denied.push(nonempty);
    denied.push(symbolic::not(&observed));
    assert!(!engine.feasible(&denied).unwrap());
}

#[cfg(test)]
pub(super) fn compiler_associated_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    output: &std::path::Path,
) {
    assert!(!TEST_ASSOCIATED_HIERARCHY.with(std::cell::Cell::get));
    assert_eq!(associated_hierarchy_enabled(), ASSOCIATED_HIERARCHY_ENABLED);
    let (block, data) = root
        .basic_blocks
        .iter_enumerated()
        .find(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let original = func.ty(&root.local_decls, engine.tcx);
    let ty::FnDef(definition, generic) = original.kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let unused_const_root = engine
        .tcx
        .iter_local_def_id()
        .find(|local| {
            engine.tcx.def_kind(local.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(local.to_def_id()).as_str() == "root_unused_const"
        })
        .unwrap()
        .to_def_id();
    let unused_body = engine
        .tcx
        .instance_mir(ty::InstanceKind::Item(unused_const_root));
    let unused_func = unused_body
        .basic_blocks
        .iter()
        .find_map(|block| {
            if let TerminatorKind::Call { func, .. } = &block.terminator().kind {
                Some(func)
            } else {
                None
            }
        })
        .unwrap();
    let unused_original = unused_func.ty(&unused_body.local_decls, engine.tcx);
    let ty::FnDef(unused_definition, unused_arguments) = unused_original.kind() else {
        unreachable!()
    };
    // The unchanged dispatcher can already resolve the item. The following check is route-local.
    let unused_instance = engine
        .resolve_function_item(*unused_definition, unused_arguments.skip_binder())
        .unwrap();
    let bodies_before = engine.bodies.borrow().len();
    let signatures_before = engine.call_signatures.borrow().len();
    assert!(
        engine
            .mutable_hierarchy_associated_identity(unused_original, unused_instance)
            .unwrap_err()
            .contains("const argument")
    );
    let nonliteral = ty::Const::new_param(
        engine.tcx,
        ty::ParamConst {
            index: 0,
            name: rustc_span::Symbol::intern("N"),
        },
    );
    let array = Ty::new_array_with_const_len(engine.tcx, engine.tcx.types.u16, nonliteral);
    let mut work = 0;
    assert!(
        engine
            .mutable_hierarchy_associated_type_work(array, 0, &mut work)
            .unwrap_err()
            .contains("not literal")
    );
    assert_eq!(engine.bodies.borrow().len(), bodies_before);
    assert_eq!(engine.call_signatures.borrow().len(), signatures_before);

    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let value = engine
        .mutable_u16_input(engine.tcx.types.u16, &mut memory, &mut conditions)
        .unwrap();
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; root.local_decls.len()],
        addresses: vec![None; root.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: Default::default(),
        conditions,
        memory,
    };
    state.locals[1] = Some(value);
    for statement in &data.statements {
        if let StatementKind::Assign(a) = &statement.kind
            && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
        {
            assert!(
                engine
                    .mutable_u16_stage(root, &mut state, a.0, &a.1, &statement.kind)
                    .unwrap()
            );
        }
    }
    let call = || super::mutable_u16_children::ChildCall {
        body: root,
        block,
        instance,
        args,
        destination: *destination,
        target: *target,
        stack: &[],
        site: (root.source.def_id(), data.terminator().source_info.span),
    };
    if !ASSOCIATED_HIERARCHY_ENABLED {
        assert!(!engine.mutable_hierarchy_route(&state, &call()).unwrap());
    }
    let _scope = TestAssociatedHierarchy::enable();
    if engine.tcx.def_kind(instance.def_id()) == DefKind::AssocFn
        && engine.tcx.associated_item(instance.def_id()).is_method()
    {
        assert!(
            !engine
                .mutable_hierarchy_associated_identity(original, instance)
                .unwrap()
        );
        assert!(
            engine
                .mutable_hierarchy_routing_signature(instance, args.len(), None)
                .unwrap()
                .is_none()
        );
        assert!(!engine.mutable_hierarchy_route(&state, &call()).unwrap());
        let data_before = state.memory.mutable_u16[0].data.clone();
        assert!(
            engine
                .mutable_hierarchy_call(&mut state, call())
                .unwrap()
                .is_none()
        );
        assert_eq!(state.memory.mutable_u16[0].data, data_before);
        assert!(state.memory.mutable_hierarchy.is_none());
        return;
    }
    assert!(engine.mutable_hierarchy_route(&state, &call()).unwrap());
    let named_static = |name: &str| {
        engine
            .tcx
            .iter_local_def_id()
            .map(|id| id.to_def_id())
            .find(|id| {
                engine.tcx.def_kind(*id) == DefKind::AssocFn
                    && engine.tcx.item_name(*id).as_str() == name
            })
            .unwrap()
    };
    let no_args = engine.tcx.mk_args(&[]);
    let deep_signature = named_static("signature_deep");
    let deep_instance = ty::Instance {
        def: ty::InstanceKind::Item(deep_signature),
        args: no_args,
    };
    assert!(
        engine
            .call_signatures
            .borrow()
            .get(&deep_instance)
            .is_none()
    );
    let mut work = 0;
    assert!(
        engine
            .mutable_hierarchy_associated_signature_work(deep_signature, no_args, &mut work,)
            .is_err()
    );
    assert!(
        engine
            .mutable_hierarchy_routing_signature(deep_instance, 1, None)
            .is_err()
    );
    assert!(
        engine
            .call_signatures
            .borrow()
            .get(&deep_instance)
            .is_none()
    );
    let wide_signature = named_static("signature_wide");
    let mut work = 0;
    engine
        .mutable_hierarchy_associated_signature_work(wide_signature, no_args, &mut work)
        .unwrap();
    assert!(work > 255);
    assert!(
        engine
            .mutable_hierarchy_associated_signature_work(wide_signature, no_args, &mut work,)
            .is_err()
    );
    let wide_instance = ty::Instance {
        def: ty::InstanceKind::Item(wide_signature),
        args: no_args,
    };
    let wide_original = Ty::new_fn_def(engine.tcx, wide_signature, ty::Binder::dummy(no_args));
    assert!(
        engine
            .mutable_hierarchy_associated_identity(wide_original, wide_instance)
            .is_err()
    );
    assert!(
        engine
            .call_signatures
            .borrow()
            .get(&wide_instance)
            .is_none()
    );
    let generic_signature = named_static("signature_generic");
    let mut substituted = engine.tcx.types.u16;
    for _ in 0..14 {
        substituted = Ty::new_imm_ref(engine.tcx, engine.tcx.lifetimes.re_erased, substituted);
    }
    let generic_args = engine.tcx.mk_args(&[substituted.into()]);
    let mut work = 0;
    engine
        .mutable_hierarchy_associated_argument_work(generic_args, 0, &mut work)
        .unwrap();
    assert!(engine.mutable_hierarchy_associated_signature_work(
        generic_signature, generic_args, &mut work,
    ).is_err());
    assert!(
        engine
            .mutable_hierarchy_associated_signature_work(generic_signature, no_args, &mut 0,)
            .is_err()
    );
    let wrong_kind = engine.tcx.mk_args(&[engine.tcx.lifetimes.re_erased.into()]);
    assert!(
        engine
            .mutable_hierarchy_associated_signature_work(generic_signature, wrong_kind, &mut 0,)
            .is_err()
    );
    let raw_signature = engine
        .tcx
        .fn_sig(generic_signature)
        .instantiate_identity()
        .skip_binder();
    let ty::Ref(_, inner, _) = raw_signature.inputs()[0].kind() else {
        unreachable!()
    };
    let ty::Ref(_, parameter, _) = inner.kind() else {
        unreachable!()
    };
    let recursive_args = engine.tcx.mk_args(&[(*parameter).into()]);
    assert!(
        engine
            .mutable_hierarchy_associated_signature_work(generic_signature, recursive_args, &mut 0,)
            .is_err()
    );
    let alias_signature = engine
        .tcx
        .iter_local_def_id()
        .map(|id| id.to_def_id())
        .find(|id| {
            engine.tcx.def_kind(*id) == DefKind::AssocFn
                && engine.tcx.item_name(*id).as_str() == "signature_alias"
                && engine.tcx.def_kind(engine.tcx.parent(*id)) == DefKind::Trait
        })
        .unwrap();
    assert!(
        engine
            .mutable_hierarchy_associated_signature_work(alias_signature, no_args, &mut 0,)
            .is_err()
    );
    assert!(
        engine
            .call_signatures
            .borrow()
            .keys()
            .all(|instance| instance.def_id() != generic_signature
                && instance.def_id() != alias_signature)
    );
    let reason = engine
        .mutable_hierarchy_associated_signature_work(deep_signature, no_args, &mut 0)
        .unwrap_err();
    assert_eq!(
        engine.unknown_causes.borrow().get(&reason),
        Some(&UnknownCategory::ResourceLimit),
    );
    let mut work = 0;
    engine
        .mutable_hierarchy_associated_signature_work(wide_signature, no_args, &mut work)
        .unwrap();
    let reason = engine
        .mutable_hierarchy_associated_signature_work(wide_signature, no_args, &mut work)
        .unwrap_err();
    assert_eq!(
        engine.unknown_causes.borrow().get(&reason),
        Some(&UnknownCategory::ResourceLimit),
    );
    for (definition, arguments) in [
        (generic_signature, no_args),
        (generic_signature, wrong_kind),
        (alias_signature, no_args),
    ] {
        let reason = engine
            .mutable_hierarchy_associated_signature_work(definition, arguments, &mut 0)
            .unwrap_err();
        assert_eq!(
            engine.unknown_causes.borrow().get(&reason),
            Some(&UnknownCategory::Semantics),
        );
    }
    let closure = engine
        .tcx
        .iter_local_def_id()
        .find(|local| {
            engine.tcx.def_kind(local.to_def_id()) == DefKind::Closure
                && engine.tcx.coroutine_kind(local.to_def_id()).is_none()
        })
        .unwrap()
        .to_def_id();
    let closure_instance = ty::Instance {
        def: ty::InstanceKind::Item(closure),
        args: engine.tcx.mk_args(&[]),
    };
    assert!(
        engine
            .mutable_hierarchy_routing_signature(closure_instance, 0, None)
            .unwrap()
            .is_none()
    );
    let closure_original = Ty::new_fn_def(
        engine.tcx,
        closure,
        ty::Binder::dummy(engine.tcx.mk_args(&[])),
    );
    assert!(
        !engine
            .mutable_hierarchy_associated_identity(closure_original, closure_instance)
            .unwrap()
    );
    if engine.tcx.def_kind(*definition) == DefKind::AssocFn {
        assert!(
            engine
                .mutable_hierarchy_associated_identity(original, instance)
                .unwrap()
        );
        let wrong = ty::Instance {
            def: ty::InstanceKind::Item(root.source.def_id()),
            args: engine.tcx.mk_args(&[]),
        };
        assert!(
            !engine
                .mutable_hierarchy_associated_identity(original, wrong)
                .unwrap()
        );
        if !instance.args.is_empty() {
            let wrong_arguments = ty::Instance {
                def: instance.def,
                args: engine.tcx.mk_args(&[engine.tcx.types.u16.into()]),
            };
            assert!(
                !engine
                    .mutable_hierarchy_associated_identity(original, wrong_arguments)
                    .unwrap()
            );
        }
        let selected_signature = engine.call_poly_signature(instance).unwrap();
        engine.call_signatures.borrow_mut().insert(
            instance,
            selected_signature
                .map_bound(|signature| signature.set_safety(rustc_hir::Safety::Unsafe)),
        );
        assert!(
            !engine
                .mutable_hierarchy_associated_identity(original, instance)
                .unwrap()
        );
        engine
            .call_signatures
            .borrow_mut()
            .insert(instance, selected_signature);
        let mut deep = engine.tcx.types.u16;
        for _ in 0..17 {
            deep = Ty::new_slice(engine.tcx, deep);
        }
        let forged_original = Ty::new_fn_def(
            engine.tcx,
            *definition,
            ty::Binder::dummy(engine.tcx.mk_args(&[deep.into()])),
        );
        assert!(
            engine
                .mutable_hierarchy_associated_identity(forged_original, instance)
                .is_err()
        );
        let too_many = engine
            .tcx
            .mk_args_from_iter((0..513).map(|_| ty::GenericArg::from(engine.tcx.types.u16)));
        let forged_original = Ty::new_fn_def(engine.tcx, *definition, ty::Binder::dummy(too_many));
        assert!(
            engine
                .mutable_hierarchy_associated_identity(forged_original, instance)
                .is_err()
        );
        let selected = engine.instantiated_body(instance).unwrap();
        // Hostile cached MIR is bounded before normalization, effect or cache publication.
        let mut huge_aggregate = (*selected).clone();
        let statement = huge_aggregate
            .basic_blocks
            .as_mut()
            .iter_mut()
            .flat_map(|block| &mut block.statements)
            .find(|statement| matches!(statement.kind, StatementKind::Assign(_)))
            .unwrap();
        let StatementKind::Assign(assignment) = &mut statement.kind else {
            unreachable!()
        };
        assignment.1 = Rvalue::Aggregate(
            Box::new(rustc_middle::mir::AggregateKind::Tuple),
            (0..513)
                .map(|_| Operand::Copy(rustc_middle::mir::RETURN_PLACE.into()))
                .collect(),
        );
        let error = engine
            .mutable_hierarchy_associated_borrowed_body(instance, &huge_aggregate)
            .unwrap_err();
        assert!(error.contains("work budget"));
        engine
            .bodies
            .borrow_mut()
            .insert(instance, Rc::new(huge_aggregate));
        assert!(engine.mutable_hierarchy_route(&state, &call()).is_err());
        engine
            .bodies
            .borrow_mut()
            .insert(instance, selected.clone());
        let mut projection = (*selected).clone();
        let statement = projection
            .basic_blocks
            .as_mut()
            .iter_mut()
            .flat_map(|block| &mut block.statements)
            .find(|statement| matches!(statement.kind, StatementKind::Assign(_)))
            .unwrap();
        let StatementKind::Assign(assignment) = &mut statement.kind else {
            unreachable!()
        };
        assignment.1 = Rvalue::Use(
            Operand::Copy(Place {
                local: rustc_middle::mir::RETURN_PLACE,
                projection: engine.tcx.mk_place_elems(&[ProjectionElem::Deref; 17]),
            }),
            rustc_middle::mir::WithRetag::No,
        );
        assert!(
            engine
                .mutable_hierarchy_associated_borrowed_body(instance, &projection)
                .unwrap_err()
                .contains("depth budget")
        );
        let mut deep_original = engine.tcx.types.u16;
        for _ in 0..17 {
            deep_original = Ty::new_slice(engine.tcx, deep_original);
        }
        let mut unwrap = (*selected).clone();
        let statement = unwrap
            .basic_blocks
            .as_mut()
            .iter_mut()
            .flat_map(|block| &mut block.statements)
            .find(|statement| matches!(statement.kind, StatementKind::Assign(_)))
            .unwrap();
        let StatementKind::Assign(assignment) = &mut statement.kind else {
            unreachable!()
        };
        assignment.1 = Rvalue::Use(
            Operand::Copy(Place {
                local: rustc_middle::mir::RETURN_PLACE,
                projection: engine
                    .tcx
                    .mk_place_elems(&[PlaceElem::UnwrapUnsafeBinder(deep_original)]),
            }),
            rustc_middle::mir::WithRetag::No,
        );
        assert!(
            engine
                .mutable_hierarchy_associated_borrowed_body(instance, &unwrap)
                .unwrap_err()
                .contains("unsafe binder")
        );
        for count in [17, 513] {
            let mut ascribe = (*selected).clone();
            let mut statement = ascribe
                .basic_blocks
                .iter()
                .flat_map(|block| &block.statements)
                .next()
                .unwrap()
                .clone();
            statement.kind = StatementKind::AscribeUserType(
                Box::new((
                    Place::from(rustc_middle::mir::RETURN_PLACE),
                    rustc_middle::mir::UserTypeProjection {
                        base: ty::UserTypeAnnotationIndex::from_usize(0),
                        projs: vec![ProjectionElem::Deref; count],
                    },
                )),
                ty::Variance::Invariant,
            );
            ascribe.basic_blocks.as_mut()[rustc_middle::mir::START_BLOCK]
                .statements
                .push(statement);
            assert!(
                engine
                    .mutable_hierarchy_associated_borrowed_body(instance, &ascribe)
                    .unwrap_err()
                    .contains("budget")
            );
        }
        let mut deep_local = (*selected).clone();
        deep_local.local_decls[rustc_middle::mir::RETURN_PLACE].ty = deep_original;
        assert!(
            engine
                .mutable_hierarchy_associated_borrowed_body(instance, &deep_local)
                .unwrap_err()
                .contains("depth budget")
        );
        let mut wide_local = (*selected).clone();
        wide_local.local_decls[rustc_middle::mir::RETURN_PLACE].ty =
            Ty::new_tup(engine.tcx, &vec![engine.tcx.types.u16; 513]);
        assert!(
            engine
                .mutable_hierarchy_associated_borrowed_body(instance, &wide_local)
                .unwrap_err()
                .contains("work budget")
        );
        let mut function_operand = (*selected).clone();
        let statement = function_operand
            .basic_blocks
            .as_mut()
            .iter_mut()
            .flat_map(|block| &mut block.statements)
            .find(|statement| matches!(statement.kind, StatementKind::Assign(_)))
            .unwrap();
        let StatementKind::Assign(assignment) = &mut statement.kind else {
            unreachable!()
        };
        assignment.1 = Rvalue::Use(
            Operand::Constant(Box::new(rustc_middle::mir::ConstOperand {
                span: rustc_span::DUMMY_SP,
                user_ty: None,
                const_: rustc_middle::mir::Const::Val(
                    rustc_middle::mir::ConstValue::ZeroSized,
                    Ty::new_fn_def(engine.tcx, *definition, ty::Binder::dummy(too_many)),
                ),
            })),
            rustc_middle::mir::WithRetag::No,
        );
        assert!(
            engine
                .mutable_hierarchy_associated_borrowed_body(instance, &function_operand)
                .unwrap_err()
                .contains("work budget")
        );
        let bodies_before = engine.bodies.borrow().len();
        let signatures_before = engine.call_signatures.borrow().len();
        let mut introductions = (*selected).clone();
        introductions.local_decls[rustc_middle::mir::RETURN_PLACE].local_info =
            rustc_middle::mir::ClearCrossCrate::Set(Box::new(rustc_middle::mir::LocalInfo::User(
                rustc_middle::mir::BindingForm::Var(rustc_middle::mir::VarBindingForm {
                    binding_mode: rustc_hir::BindingMode::NONE,
                    opt_ty_info: None,
                    opt_match_place: None,
                    pat_span: rustc_span::DUMMY_SP,
                    introductions: (0..513)
                        .map(|_| rustc_middle::mir::VarBindingIntroduction {
                            span: rustc_span::DUMMY_SP,
                            is_shorthand: false,
                        })
                        .collect(),
                }),
            )));
        assert!(
            engine
                .mutable_hierarchy_associated_borrowed_body(instance, &introductions)
                .unwrap_err()
                .contains("work budget")
        );
        let mut array_kind = (*selected).clone();
        let statement = array_kind
            .basic_blocks
            .as_mut()
            .iter_mut()
            .flat_map(|block| &mut block.statements)
            .find(|statement| matches!(statement.kind, StatementKind::Assign(_)))
            .unwrap();
        let StatementKind::Assign(assignment) = &mut statement.kind else {
            unreachable!()
        };
        assignment.1 = Rvalue::Aggregate(
            Box::new(rustc_middle::mir::AggregateKind::Array(deep_original)),
            std::iter::empty().collect(),
        );
        assert!(
            engine
                .mutable_hierarchy_associated_borrowed_body(instance, &array_kind)
                .unwrap_err()
                .contains("depth budget")
        );
        let mut mentioned = (*selected).clone();
        mentioned.mentioned_items = Some(vec![rustc_span::Spanned {
            node: rustc_middle::mir::MentionedItem::Fn(Ty::new_fn_def(
                engine.tcx,
                *definition,
                ty::Binder::dummy(too_many),
            )),
            span: rustc_span::DUMMY_SP,
        }]);
        assert!(
            engine
                .mutable_hierarchy_associated_borrowed_body(instance, &mentioned)
                .unwrap_err()
                .contains("work budget")
        );
        assert_eq!(engine.bodies.borrow().len(), bodies_before);
        assert_eq!(engine.call_signatures.borrow().len(), signatures_before);
        let mut wrong_mapping = (*selected).clone();
        wrong_mapping.local_decls[rustc_middle::mir::RETURN_PLACE].ty =
            Ty::new_param(engine.tcx, 513, rustc_span::Symbol::intern("T"));
        assert!(
            engine
                .mutable_hierarchy_associated_borrowed_body(instance, &wrong_mapping)
                .unwrap_err()
                .contains("Param mapping")
        );
        let mut forged = (*selected).clone();
        forged.source.instance = wrong.def;
        assert!(
            engine
                .mutable_hierarchy_associated_body(instance, &forged)
                .is_err()
        );
        engine.bodies.borrow_mut().insert(instance, Rc::new(forged));
        assert!(engine.mutable_hierarchy_route(&state, &call()).is_err());
        let mut promoted = (*selected).clone();
        promoted.source.promoted = Some(rustc_middle::mir::Promoted::from_usize(0));
        assert!(
            engine
                .mutable_hierarchy_associated_body(instance, &promoted)
                .is_err()
        );
        let coroutine = engine
            .tcx
            .iter_local_def_id()
            .find(|local| engine.tcx.coroutine_kind(local.to_def_id()).is_some())
            .unwrap()
            .to_def_id();
        let metadata = engine
            .tcx
            .instance_mir(ty::InstanceKind::Item(coroutine))
            .coroutine
            .clone()
            .unwrap();
        let mut coroutine_body = (*selected).clone();
        coroutine_body.coroutine = Some(metadata);
        assert!(
            engine
                .mutable_hierarchy_associated_body(instance, &coroutine_body)
                .is_err()
        );
        let mut spread = (*selected).clone();
        spread.spread_arg = Some(rustc_middle::mir::Local::from_usize(1));
        assert!(
            engine
                .mutable_hierarchy_associated_body(instance, &spread)
                .is_err()
        );
        engine.bodies.borrow_mut().insert(instance, selected);
    }
    let source = match args[0].node {
        Operand::Copy(p) | Operand::Move(p) => p.local.as_usize(),
        _ => unreachable!(),
    };
    let mut consumed = state.clone();
    consumed.missing_places.consume(source, Vec::new()).unwrap();
    assert!(!engine.mutable_hierarchy_route(&consumed, &call()).unwrap());
    if engine.tcx.def_kind(*definition) == DefKind::AssocFn {
        let mut wrong_site = call();
        wrong_site.site.1 = rustc_span::DUMMY_SP;
        let mut rejected = state.clone();
        let data_before = rejected.memory.mutable_u16[0].data.clone();
        assert!(
            engine
                .mutable_hierarchy_call(&mut rejected, wrong_site)
                .is_err()
        );
        assert_eq!(rejected.memory.mutable_u16[0].data, data_before);
        assert!(rejected.memory.mutable_hierarchy.is_none());
        let copied_args = args.to_vec();
        let mut copied_call = call();
        copied_call.args = &copied_args;
        assert!(!matches!(
            engine.mutable_hierarchy_call(&mut rejected, copied_call),
            Ok(Some(_))
        ));
        assert_eq!(rejected.memory.mutable_u16[0].data, data_before);
        assert!(rejected.memory.mutable_hierarchy.is_none());
        let duplicate_body = Rc::new((**root).clone());
        let duplicate_data = &duplicate_body.basic_blocks[block];
        let TerminatorKind::Call {
            args: duplicate_args,
            ..
        } = &duplicate_data.terminator().kind
        else {
            unreachable!()
        };
        let mut duplicate_call = call();
        duplicate_call.body = &duplicate_body;
        duplicate_call.args = duplicate_args;
        assert!(!matches!(
            engine.mutable_hierarchy_route(&state, &duplicate_call),
            Ok(true)
        ));
        assert_eq!(state.memory.mutable_u16[0].data, data_before);
        assert!(state.memory.mutable_hierarchy.is_none());
    }
    let earlier_entries = std::mem::take(&mut engine.proof.body_entries);
    let results = engine
        .mutable_hierarchy_call(&mut state, call())
        .unwrap()
        .unwrap();
    assert!(!results.is_empty());
    for result in results {
        engine.mutable_hierarchy_namespace(&result.memory).unwrap();
        assert!(
            result.memory.mutable_u16[0]
                .hierarchy
                .as_ref()
                .unwrap()
                .owners
                .is_empty()
        );
    }
    assert!(
        engine
            .proof
            .body_entries
            .iter()
            .any(|entry| entry.function.contains("leaf"))
    );
    assert!(
        engine
            .proof
            .body_entries
            .iter()
            .any(|entry| entry.function == engine.tcx.def_path_str(instance.def_id()))
    );
    let selected = engine.instantiated_body(instance).unwrap();
    let label = engine
        .tcx
        .item_name(root.source.def_id())
        .as_str()
        .to_string();
    std::fs::write(
        output.join(format!("{label}-selected.mir")),
        format!("{selected:#?}"),
    )
    .unwrap();
    std::fs::write(
        output.join(format!("{label}-selected.json")),
        serde_json::to_string_pretty(&serde_json::json!({
            "original": format!("{original:?}"),
            "selected_instance": format!("{instance:?}"),
            "selected_signature": format!("{:?}", engine.call_poly_signature(instance).unwrap()),
            "original_definition": format!("{definition:?}"),
            "selected_definition": format!("{:?}", instance.def_id()),
            "entered_bodies": engine.proof.body_entries,
        }))
        .unwrap(),
    )
    .unwrap();
    engine.proof.body_entries.extend(earlier_entries);
}

#[cfg(test)]
fn compiler_char_return_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    block: rustc_middle::mir::BasicBlock,
    source: usize,
    result: &Return,
) {
    super::mutable_u16::compiler_char_hierarchy_backing_probe(engine, &result.memory);
    let backing = engine
        .mutable_u16_backing(0, &result.memory)
        .unwrap()
        .clone();
    let original = backing.hierarchy.as_ref().unwrap();
    let current = original.metadata(0).unwrap();
    original.observe(current).unwrap();
    assert!(
        original
            .observe(Metadata {
                epoch: current.epoch - 1,
                ..current
            })
            .is_err()
    );
    assert!(
        engine
            .mutable_u16_role_live(
                0,
                &symbolic::MutableU16Role::HierarchyChild {
                    lease: original.issued
                },
                &result.memory
            )
            .is_err()
    );
    let mut no_namespace = result.memory.clone();
    no_namespace.mutable_hierarchy = None;
    assert!(engine.mutable_u16_backing(0, &no_namespace).is_err());
    let mut stale_generation = result.memory.clone();
    Rc::make_mut(&mut stale_generation.mutable_u16)[0].generation = original.issued + 1;
    assert!(engine.mutable_u16_backing(0, &stale_generation).is_err());
    let mut missing = result.memory.clone();
    missing
        .missing_places
        .consume(backing.allocation, Vec::new())
        .unwrap();
    assert!(engine.mutable_u16_backing(0, &missing).is_err());
    let frame = engine.mutable_u16_register_frame(root).unwrap();
    let tip = Tip {
        frame,
        statement: block.as_usize(),
        local: source,
    };
    let mut next = original.clone();
    let slots = result.memory.storage_slots();
    let lease = next.issue(0, tip.clone(), slots).unwrap();
    assert!(next.access(0).is_err());
    let mut wrong_tip = tip.clone();
    wrong_tip.local += 1;
    assert!(next.enter(&wrong_tip, frame, slots).is_err());
    let ticket = next.enter(&tip, frame, slots).unwrap();
    next.access(lease).unwrap();
    assert!(next.access(0).is_err());
    let mut rollback = next.clone();
    rollback.epoch = ticket.epoch_floor - 1;
    assert!(rollback.release(&ticket).is_err());
    next.release(&ticket).unwrap();
    next.access(0).unwrap();
    assert!(next.access(lease).is_err());
    let mut exhausted = original.clone();
    assert!(matches!(
        exhausted.issue(0, tip, MAX_INPUT_VALUES),
        Err(TransitionError::Resource(_))
    ));
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    let zero = symbolic::integer(&engine.terms, 0, bits, false);
    let nonempty = symbolic::binary(&engine.terms, "lt", zero.clone(), backing.length.clone())
        .unwrap()
        .boolean()
        .unwrap();
    let observed = engine
        .terms
        .apply(
            Op::Select,
            &[
                backing.data.scalar().unwrap().clone(),
                zero.integer().unwrap().0.clone(),
            ],
        )
        .unwrap();
    assert_eq!(observed.sort(), &Sort::BitVec(32));
    let expected = engine.terms.bit_vector(u128::from('a'), 32).unwrap();
    let equal = engine
        .terms
        .apply(Op::Equal, &[observed, expected])
        .unwrap();
    let mut denied = result.conditions.clone();
    denied.push(nonempty);
    denied.push(symbolic::not(&equal));
    assert!(!engine.feasible(&denied).unwrap());
}

#[cfg(test)]
fn compiler_char_scalar_probe<'tcx>(engine: &mut Engine<'tcx>, result: &Return, associated: bool) {
    let root_name = if associated {
        "root_associated_scalar_char"
    } else {
        "root_scalar_char"
    };
    let definition = engine
        .tcx
        .iter_local_def_id()
        .find(|d| {
            engine.tcx.def_kind(d.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(d.to_def_id()).as_str() == root_name
        })
        .unwrap()
        .to_def_id();
    let root_instance = engine
        .resolve_function_item(definition, engine.tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(root_instance).unwrap();
    let (block, data) = body
        .basic_blocks
        .iter_enumerated()
        .find(|(_, b)| matches!(b.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&body.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let selected = engine.instantiated_body(instance).unwrap();
    let (Operand::Copy(source) | Operand::Move(source)) = args[0].node else {
        unreachable!()
    };
    let call = || super::mutable_u16_children::ChildCall {
        body: &body,
        block,
        instance,
        args,
        destination: *destination,
        target: *target,
        stack: &[],
        site: (body.source.def_id(), data.terminator().source_info.span),
    };
    let base = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        addresses: vec![None; body.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: Default::default(),
        conditions: result.conditions.clone(),
        memory: result.memory.clone(),
    };
    let prepare = |engine: &mut Engine<'tcx>, value: Value| {
        let mut state = base.clone();
        state.locals[1] = Some(value);
        for statement in &data.statements {
            if let StatementKind::Assign(a) = &statement.kind {
                let value = engine
                    .rvalue(body.source.def_id(), &body, &mut state, &a.1)
                    .unwrap();
                engine
                    .store_assignment_value(&body, &mut state, a.0, value, &statement.kind)
                    .unwrap();
            }
        }
        state
    };
    let pair_def = engine
        .tcx
        .iter_local_def_id()
        .find(|d| {
            engine.tcx.def_kind(d.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(d.to_def_id()).as_str() == "root_pair_char"
        })
        .unwrap()
        .to_def_id();
    let pair_instance = engine
        .resolve_function_item(pair_def, engine.tcx.mk_args(&[]))
        .unwrap();
    let pair = engine.instantiated_body(pair_instance).unwrap();
    let mut pair_state = base.clone();
    pair_state.locals = vec![None; pair.local_decls.len()];
    pair_state.addresses = vec![None; pair.local_decls.len()];
    pair_state.locals[1] = Some(Value::Tuple(vec![
        symbolic::integer(&engine.terms, 65, 32, false),
        symbolic::integer(&engine.terms, 65, 32, false),
    ]));
    for (index, valid) in [(1, true), (0, false)] {
        let place = Place {
            local: rustc_middle::mir::Local::from_usize(1),
            projection: engine.tcx.mk_place_elems(&[ProjectionElem::Field(
                rustc_abi::FieldIdx::from_usize(index),
                engine.tcx.types.char,
            )]),
        };
        assert_eq!(
            engine
                .mutable_hierarchy_dormant_operand(
                    &pair,
                    &pair_state,
                    place,
                    engine.tcx.types.char,
                    None,
                )
                .is_ok(),
            valid
        );
    }
    let frame = engine.mutable_u16_register_frame(&body).unwrap();
    let foreign = Context::default();
    for value in [
        symbolic::integer(&engine.terms, 0xd800, 32, false),
        symbolic::integer(&engine.terms, 0xdfff, 32, false),
        symbolic::integer(&engine.terms, 0x110000, 32, false),
        symbolic::integer(&engine.terms, 65, 32, true),
        symbolic::integer(&engine.terms, 65, 16, false),
        symbolic::integer(&foreign, 65, 32, false),
        Value::Bool(engine.terms.boolean(true)),
    ] {
        let mut dormant = prepare(engine, symbolic::integer(&engine.terms, 65, 32, false));
        dormant.locals[source.local.as_usize()] = Some(value.clone());
        let before = dormant.clone();
        assert!(engine.mutable_hierarchy_call(&mut dormant, call()).is_err());
        assert_eq!(dormant.conditions, before.conditions);
        assert_eq!(
            dormant.memory.mutable_u16[0].data,
            before.memory.mutable_u16[0].data
        );
        let mut active = before;
        let slots = active.memory.storage_slots();
        let hierarchy = Rc::make_mut(&mut active.memory.mutable_u16)[0]
            .hierarchy
            .as_mut()
            .unwrap();
        let tip = Tip {
            frame,
            statement: block.as_usize(),
            local: source.local.as_usize(),
        };
        hierarchy.issue(0, tip.clone(), slots).unwrap();
        hierarchy.enter(&tip, frame, slots).unwrap();
        let before = active.clone();
        assert!(
            engine
                .mutable_hierarchy_scalar_call(&mut active, &selected, call())
                .is_err()
        );
        assert_eq!(active.conditions, before.conditions);
        assert_eq!(
            active.memory.mutable_u16[0].data,
            before.memory.mutable_u16[0].data
        );
    }
    for scalar in [0, 0xd7ff, 0xe000, 0x10ffff] {
        let value = symbolic::integer(&engine.terms, scalar, 32, false);
        let mut state = prepare(engine, value.clone());
        let returns = engine
            .mutable_hierarchy_call(&mut state, call())
            .unwrap()
            .unwrap();
        for returned in returns {
            assert_eq!(returned.value.integer().unwrap(), value.integer().unwrap());
            engine
                .mutable_hierarchy_char_value_probe(&returned.value, &returned.conditions)
                .unwrap();
            assert_eq!(
                returned.memory.mutable_u16[0].data,
                base.memory.mutable_u16[0].data
            );
        }
    }
    for wrong_local in [
        rustc_middle::mir::RETURN_PLACE,
        rustc_middle::mir::Local::from_usize(1),
    ] {
        let mut forged = (*selected).clone();
        forged.local_decls[wrong_local].ty = engine.tcx.types.u32;
        engine.bodies.borrow_mut().insert(instance, Rc::new(forged));
        let mut state = prepare(engine, symbolic::integer(&engine.terms, 65, 32, false));
        let before = state.clone();
        assert!(engine.mutable_hierarchy_call(&mut state, call()).is_err());
        assert_eq!(
            state.memory.mutable_u16[0].data,
            before.memory.mutable_u16[0].data
        );
        assert_eq!(state.conditions, before.conditions);
        engine
            .bodies
            .borrow_mut()
            .insert(instance, selected.clone());
    }
    // A malformed cached MIR constant is a boundary control, never native invalid Char.
    for invalid in [0xd800_u128, 0xdfff, 0x110000] {
        let mut forged = (*selected).clone();
        let assignment = forged
            .basic_blocks
            .as_mut()
            .iter_mut()
            .flat_map(|b| &mut b.statements)
            .find_map(|s| match &mut s.kind {
                StatementKind::Assign(a) if a.0.local == rustc_middle::mir::RETURN_PLACE => Some(a),
                _ => None,
            })
            .unwrap();
        let Rvalue::Use(operand, _) = &mut assignment.1 else {
            unreachable!()
        };
        *operand = Operand::Constant(Box::new(rustc_middle::mir::ConstOperand {
            span: rustc_span::DUMMY_SP,
            user_ty: None,
            const_: rustc_middle::mir::Const::Val(
                rustc_middle::mir::ConstValue::Scalar(
                    rustc_middle::mir::interpret::Scalar::from_uint(
                        invalid,
                        rustc_abi::Size::from_bytes(4),
                    ),
                ),
                engine.tcx.types.char,
            ),
        }));
        let forged = Rc::new(forged);
        engine.bodies.borrow_mut().insert(instance, forged.clone());
        let mut state = prepare(engine, symbolic::integer(&engine.terms, 65, 32, false));
        let before = state.clone();
        assert!(engine.mutable_hierarchy_call(&mut state, call()).is_err());
        assert_eq!(
            state.memory.mutable_u16[0].data,
            before.memory.mutable_u16[0].data
        );
        assert_eq!(state.conditions, before.conditions);
        let mut active = before;
        let slots = active.memory.storage_slots();
        let hierarchy = Rc::make_mut(&mut active.memory.mutable_u16)[0]
            .hierarchy
            .as_mut()
            .unwrap();
        let tip = Tip {
            frame,
            statement: block.as_usize(),
            local: source.local.as_usize(),
        };
        hierarchy.issue(0, tip.clone(), slots).unwrap();
        hierarchy.enter(&tip, frame, slots).unwrap();
        assert!(
            engine
                .mutable_hierarchy_scalar_call(&mut active, &forged, call())
                .is_err()
        );
        engine
            .bodies
            .borrow_mut()
            .insert(instance, selected.clone());
    }
}

#[cfg(test)]
pub(super) fn compiler_production_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    base: &State,
) {
    tests::production_call(engine, root, base);
}

#[cfg(test)]
pub(super) fn compiler_activation_contract_refusal<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    base: &State,
) {
    let (block, data) = root
        .basic_blocks
        .iter_enumerated()
        .find(|(_, b)| matches!(b.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&root.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    assert!(
        engine.specification(instance).unwrap().is_some()
            || !engine.contracts(instance.def_id()).is_empty()
    );
    let root_instance = engine
        .bodies
        .borrow()
        .iter()
        .find(|(_, b)| Rc::ptr_eq(b, root))
        .map(|(i, _)| *i)
        .unwrap();
    let mut state = base.clone();
    state.locals.resize(root.local_decls.len(), None);
    state.addresses.resize(root.local_decls.len(), None);
    state.flow = engine.activation_test_root(root_instance, root).unwrap();
    let before_data = state.memory.mutable_u16[0].data.clone();
    let before_backings = state.memory.mutable_u16.clone();
    let before_locals = format!("{:?}", state.locals);
    let before_masks = state.missing_places.entries().to_vec();
    let before_work = engine.activation_test_work_used(&state.flow);
    let before_queries = engine.proof.obligations.len();
    let before_entries = engine.proof.body_entries.len();
    let before_cache = engine.bodies.borrow().len();
    let sentinel = if engine.specification(instance).unwrap().is_some() {
        0x51ef_2261
    } else {
        0x51ef_2251
    };
    let before_terms = engine.terms.bit_vector(sentinel, 64).unwrap();
    assert!(state.flow.validate_return().is_ok());
    assert!(
        matches!(engine.activation_armed_call_route(&state.flow, instance),
        Err(e) if e.contains("contract adapter"))
    );
    assert!(
        matches!(engine.mutable_hierarchy_call_transaction(&mut state,
        super::mutable_u16_children::ChildCall {
            body: root, block, instance, args, destination: *destination, target: *target,
            stack: &[], site: (root.source.def_id(), data.terminator().source_info.span),
        }), Err(e) if e.contains("contract adapter"))
    );
    let after_terms = engine.terms.bit_vector(sentinel + 1, 64).unwrap();
    assert_eq!(after_terms.id(), before_terms.id() + 1);
    assert_eq!(engine.proof.obligations.len(), before_queries);
    assert_eq!(engine.activation_test_work_used(&state.flow), before_work);
    assert_eq!(engine.proof.body_entries.len(), before_entries);
    assert_eq!(engine.bodies.borrow().len(), before_cache);
    assert_eq!(state.memory.mutable_u16[0].data, before_data);
    assert!(Rc::ptr_eq(&state.memory.mutable_u16, &before_backings));
    assert_eq!(format!("{:?}", state.locals), before_locals);
    assert_eq!(state.missing_places.entries(), before_masks.as_slice());
    assert!(state.flow.validate_return().is_ok());
    eprintln!("carrier configured/annotated contracts refused before effects");
}

#[cfg(test)]
fn compiler_activation_pending_count<'tcx>(
    engine: &Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    state: &State,
) {
    assert!(matches!(
        state.memory.mutable_u16[0].phase,
        super::mutable_u16_children::Phase::Pending { .. }
    ));
    let instance = engine
        .bodies
        .borrow()
        .iter()
        .find(|(_, body)| Rc::ptr_eq(body, root))
        .map(|(i, _)| *i)
        .unwrap();
    // Independent test-only invocation; it never replenishes the actual root's Work.
    let flow = engine.activation_test_root(instance, root).unwrap();
    let before_backings = state.memory.mutable_u16.clone();
    let before_data = state.memory.mutable_u16[0].data.clone();
    let before_locals = format!("{:?}", state.locals);
    let before_masks = state.missing_places.entries().to_vec();
    let before_queries = engine.proof.obligations.len();
    let before_pending = state.flow.validate_return();
    let expected = state.memory.storage_slots();
    let before_term = engine.fresh(Sort::Bool);
    assert_eq!(
        state.memory.activation_storage_slots(&flow).unwrap(),
        expected
    );
    let after_term = engine.fresh(Sort::Bool);
    assert_eq!(after_term.id(), before_term.id() + 1);
    assert_eq!(engine.proof.obligations.len(), before_queries);
    assert_eq!(state.flow.validate_return(), before_pending);
    assert!(Rc::ptr_eq(&state.memory.mutable_u16, &before_backings));
    assert_eq!(state.memory.mutable_u16[0].data, before_data);
    assert_eq!(format!("{:?}", state.locals), before_locals);
    assert_eq!(state.missing_places.entries(), before_masks.as_slice());
    let mut active = state.memory.clone();
    Rc::make_mut(&mut active.mutable_u16)[0].phase =
        super::mutable_u16_children::Phase::Active { frames: vec![0] };
    let retained = active.clone();
    assert!(matches!(active.activation_storage_slots(&flow),
        Err(e) if e.contains("storage namespace")));
    assert!(
        matches!(engine.activation_charge_backing_cow(&flow, &active),
        Err(e) if e.contains("legacy backing clone"))
    );
    assert!(Rc::ptr_eq(&active.mutable_u16, &retained.mutable_u16));
    assert!(matches!(
        active.mutable_u16[0].phase,
        super::mutable_u16_children::Phase::Active { .. }
    ));
    eprintln!("carrier Pending count unchanged; Active count and COW refused");
}

#[cfg(test)]
pub(super) fn compiler_activation_scalar_registration<'tcx>(
    engine: &Engine<'tcx>,
    instance: ty::Instance<'tcx>,
    body: &Rc<Body<'tcx>>,
) {
    let flow = engine.activation_test_root(instance, body).unwrap();
    let frames = engine.mutable_u16_frames.borrow().len();
    let before = engine.activation_test_work_used(&flow);
    let first = engine.activation_register_frame(body, &flow).unwrap();
    let expected = body
        .basic_blocks
        .len()
        .saturating_add(frames)
        .saturating_add(1);
    assert_eq!(engine.activation_test_work_used(&flow) - before, expected);
    let frames = engine.mutable_u16_frames.borrow().len();
    let before = engine.activation_test_work_used(&flow);
    assert_eq!(
        engine.activation_register_frame(body, &flow).unwrap(),
        first
    );
    let expected = body
        .basic_blocks
        .len()
        .saturating_add(frames)
        .saturating_add(1);
    assert_eq!(engine.activation_test_work_used(&flow) - before, expected);
    eprintln!("carrier Armed scalar registration charges budget and certificate scan");
}

#[cfg(test)]
pub(super) fn compiler_return_transport_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    base: &State,
) {
    compiler_return_transport_with_flow(
        engine,
        root,
        base,
        false,
        false,
        super::activation_flow_probe::ReturnFault::Erased,
    )
    .unwrap();
}

#[cfg(test)]
pub(super) fn compiler_return_transport_with_flow<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    base: &State,
    armed: bool,
    legacy512: bool,
    hostile_control: super::activation_flow_probe::ReturnFault,
) -> Result<Option<Memory>, String> {
    let (block, data) = root
        .basic_blocks
        .iter_enumerated()
        .find(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&root.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let mut state = base.clone();
    if armed {
        let root_instance = engine
            .bodies
            .borrow()
            .iter()
            .find(|(_, body)| Rc::ptr_eq(body, root))
            .map(|(instance, _)| *instance)
            .unwrap();
        state.flow = if legacy512 {
            engine.activation_test_legacy_root(root_instance, root)?
        } else {
            engine.activation_test_root(root_instance, root)?
        };
    }
    let untouched = symbolic::integer(&engine.terms, 43, 16, false);
    let replacement = symbolic::integer(&engine.terms, 61, 16, false);
    state.locals[2] = Some(Value::Elements(
        vec![
            symbolic::integer(&engine.terms, 41, 16, false),
            untouched.clone(),
        ]
        .into(),
    ));
    let bits = u32::from(engine.tcx.sess.target.pointer_width);
    state.locals[3] = Some(symbolic::integer(&engine.terms, 0, bits, false));
    // Rust lowers this Call through a temporary. This projected publication is a direct
    // typed boundary control, not a claim about ordinary projected Call lowering.
    let projected = Place {
        local: rustc_middle::mir::Local::from_usize(2),
        projection: engine.tcx.mk_place_elems(&[ProjectionElem::Index(
            rustc_middle::mir::Local::from_usize(3),
        )]),
    };
    let captured = engine
        .capture_call_destination(root, &state, projected)
        .unwrap();
    assert!(captured.is_some());
    for statement in &data.statements {
        if let StatementKind::Assign(a) = &statement.kind
            && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
        {
            assert!(
                engine
                    .mutable_u16_stage(root, &mut state, a.0, &a.1, &statement.kind)
                    .unwrap()
            );
        }
    }
    if armed && !legacy512 && hostile_control == super::activation_flow_probe::ReturnFault::Erased {
        compiler_activation_pending_count(engine, root, &state);
    }
    let before = state.memory.mutable_u16[0].data.clone();
    let _scope = TestIssuance::enable();
    let results = engine
        .mutable_hierarchy_call(
            &mut state,
            super::mutable_u16_children::ChildCall {
                body: root,
                block,
                instance,
                args,
                destination: *destination,
                target: *target,
                stack: &[],
                site: (root.source.def_id(), data.terminator().source_info.span),
            },
        )?
        .ok_or("carrier actual hierarchy Call was not selected")?;
    assert_eq!(results.len(), 2, "two actual symbolic Returns required");
    if armed {
        engine.activation_test_sibling_receipts(&results[0], &results[1]);
    }
    // The index changes after capture; a consumed unrelated place must remain consumed.
    state.locals[3] = Some(symbolic::integer(&engine.terms, 1, bits, false));
    state.missing_places.consume(0, Vec::new()).unwrap();
    let origin = results[0].memory.mutable_u16[0]
        .hierarchy
        .as_ref()
        .unwrap()
        .origin
        .clone();
    let mut continuations = Vec::new();
    for returned in results {
        let backing = &returned.memory.mutable_u16[0];
        let hierarchy = backing.hierarchy.as_ref().unwrap();
        assert!(hierarchy.owners.is_empty() && hierarchy.pending.is_none());
        assert!(hierarchy.role_valid(&symbolic::MutableU16Role::Root, true));
        assert!(Rc::ptr_eq(&origin, &hierarchy.origin));
        let mut forged = hierarchy.clone();
        forged.origin = Rc::new((*origin).clone());
        assert!(!Rc::ptr_eq(&origin, &forged.origin));
        let conditions = returned.conditions.clone();
        let current = backing.data.clone();
        if armed {
            eprintln!(
                "carrier control={hostile_control:?} branch={} before-control-work={}",
                continuations.len(),
                engine.activation_test_work_used(&returned.flow)
            );
        }
        if armed && continuations.is_empty() {
            super::activation_flow_probe::return_controls(
                engine,
                &state,
                &returned,
                hostile_control,
            );
            if hostile_control != super::activation_flow_probe::ReturnFault::Erased {
                // This root invocation is a hostile-envelope experiment, not a continuation.
                // The separate positive invocation adopts and publishes both real Returns.
                return Ok(None);
            }
        }
        if armed {
            eprintln!(
                "carrier control={hostile_control:?} before-adoption-work={}",
                engine.activation_test_work_used(&returned.flow)
            );
        }
        let mut next = if armed {
            engine.adopt_flow_return(&state, returned.conditions, returned.memory, returned.flow)?
        } else {
            state.continuation(returned.conditions, returned.memory)
        };
        assert_eq!(next.conditions, conditions);
        assert_eq!(next.memory.mutable_u16[0].data, current);
        if current != before {
            let substituted = state.continuation(next.conditions.clone(), base.memory.clone());
            assert_ne!(substituted.memory.mutable_u16[0].data, current);
        }
        assert!(next.missing_places.check(0, &[]).is_err());
        if armed {
            eprintln!(
                "carrier control={hostile_control:?} before-store-work={}",
                engine.activation_test_work_used(&next.flow)
            );
        }
        engine.store_call_result(
            root,
            &mut next,
            projected,
            captured.as_ref(),
            returned.value.clone(),
        )?;
        let Value::Elements(out) = next.locals[2].as_ref().unwrap() else {
            unreachable!()
        };
        assert_eq!(out[0].integer().unwrap(), returned.value.integer().unwrap());
        assert_eq!(out[1].integer().unwrap(), untouched.integer().unwrap());
        assert!(next.missing_places.check(0, &[]).is_err());
        continuations.push(next);
    }
    assert_ne!(continuations[0].conditions, continuations[1].conditions);
    assert!(
        continuations
            .iter()
            .any(|s| s.memory.mutable_u16[0].data != before)
    );
    let sibling_data = continuations[1].memory.mutable_u16[0].data.clone();
    let sibling_out = continuations[1].locals[2].clone().unwrap();
    Rc::make_mut(&mut continuations[0].memory.mutable_u16)[0].data = before.clone();
    if armed {
        // The two real typed publications above are the admitted execution. This subsequent
        // host-only COW perturbation tests isolation without pretending to execute another Call.
        let Some(Value::Elements(out)) = &mut continuations[0].locals[2] else {
            unreachable!()
        };
        out[0] = replacement;
    } else {
        engine
            .store_call_result(
                root,
                &mut continuations[0],
                projected,
                captured.as_ref(),
                replacement,
            )
            .unwrap();
    }
    if armed {
        let used = engine.activation_test_work_used(&continuations[0].flow);
        assert!(used <= continuations[0].flow.structural_limit().unwrap());
        eprintln!("carrier actual two-return publication work={used}");
    }
    assert_eq!(continuations[1].memory.mutable_u16[0].data, sibling_data);
    let Value::Elements(out) = continuations[1].locals[2].as_ref().unwrap() else {
        unreachable!()
    };
    let Value::Elements(original) = sibling_out else {
        unreachable!()
    };
    assert_eq!(out[0].integer().unwrap(), original[0].integer().unwrap());
    Ok(armed.then(|| continuations[0].memory.clone()))
}

#[cfg(test)]
pub(super) fn compiler_non_candidate_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    base: &State,
) {
    let (block, data) = root
        .basic_blocks
        .iter_enumerated()
        .find(|(_, data)| matches!(data.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&root.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let mut state = base.clone();
    if root.local_decls[rustc_middle::mir::Local::from_usize(1)].ty == engine.tcx.types.u16 {
        state.locals[1] = Some(symbolic::integer(&engine.terms, 17, 16, false));
    }
    for statement in &data.statements {
        if let StatementKind::Assign(a) = &statement.kind
            && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
        {
            assert!(
                engine
                    .mutable_u16_stage(root, &mut state, a.0, &a.1, &statement.kind)
                    .unwrap()
            );
        }
    }
    let before = state.memory.mutable_u16[0].data.clone();
    let slots = state.memory.storage_slots();
    let _scope = TestIssuance::enable();
    assert!(
        engine
            .mutable_hierarchy_call(
                &mut state,
                super::mutable_u16_children::ChildCall {
                    body: root,
                    block,
                    instance,
                    args,
                    destination: *destination,
                    target: *target,
                    stack: &[],
                    site: (root.source.def_id(), data.terminator().source_info.span),
                }
            )
            .unwrap()
            .is_none()
    );
    assert_eq!(state.memory.mutable_hierarchy, None);
    assert!(state.memory.mutable_u16[0].hierarchy.is_none());
    assert_eq!(state.memory.mutable_u16[0].data, before);
    assert_eq!(state.memory.storage_slots(), slots);
}

#[cfg(test)]
fn compiler_dormant_probe<'tcx>(engine: &mut Engine<'tcx>, memory: &Memory, conditions: &[Term]) {
    let definition = engine
        .tcx
        .iter_local_def_id()
        .find(|d| {
            engine.tcx.def_kind(d.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(d.to_def_id()).as_str() == "root_wrapping"
        })
        .unwrap()
        .to_def_id();
    let root_instance = engine
        .resolve_function_item(definition, engine.tcx.mk_args(&[]))
        .unwrap();
    let body = engine.instantiated_body(root_instance).unwrap();
    let (block, data) = body
        .basic_blocks
        .iter_enumerated()
        .find(|(_, b)| matches!(b.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&body.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; body.local_decls.len()],
        addresses: vec![None; body.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: Default::default(),
        memory: memory.clone(),
        conditions: conditions.to_vec(),
    };
    state.locals[1] = Some(symbolic::integer(&engine.terms, 17, 16, false));
    for statement in &data.statements {
        if let StatementKind::Assign(a) = &statement.kind {
            let value = engine
                .rvalue(body.source.def_id(), &body, &mut state, &a.1)
                .unwrap();
            engine
                .store_assignment_value(&body, &mut state, a.0, value, &statement.kind)
                .unwrap();
        }
    }
    let call = || super::mutable_u16_children::ChildCall {
        body: &body,
        block,
        instance,
        args,
        destination: *destination,
        target: *target,
        stack: &[],
        site: (body.source.def_id(), data.terminator().source_info.span),
    };
    let id = state.memory.mutable_hierarchy.unwrap();
    let backing = &state.memory.mutable_u16[id];
    let before = backing.hierarchy.as_ref().unwrap().clone();
    let data_term = backing.data.scalar().unwrap().clone();
    let mut malformed = call();
    malformed.site.1 = rustc_span::DUMMY_SP;
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut state.clone(), &malformed)
            .is_err()
    );
    let mut malformed = call();
    malformed.site.0 = engine.tcx.lang_items().get(LangItem::SliceLen).unwrap();
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut state.clone(), &malformed)
            .is_err()
    );
    let pair_def = engine
        .tcx
        .iter_local_def_id()
        .find(|d| {
            engine.tcx.def_kind(d.to_def_id()) == DefKind::Fn
                && engine.tcx.item_name(d.to_def_id()).as_str() == "root_pair"
        })
        .unwrap()
        .to_def_id();
    let pair_instance = engine
        .resolve_function_item(pair_def, engine.tcx.mk_args(&[]))
        .unwrap();
    let pair = engine.instantiated_body(pair_instance).unwrap();
    let mut pair_state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; pair.local_decls.len()],
        addresses: vec![None; pair.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: Default::default(),
        conditions: conditions.to_vec(),
        memory: memory.clone(),
    };
    pair_state.locals[1] = Some(Value::Tuple(vec![
        symbolic::integer(&engine.terms, 17, 16, true),
        symbolic::integer(&engine.terms, 17, 16, false),
    ]));
    let pair_local = rustc_middle::mir::Local::from_usize(1);
    let valid_field = Place {
        local: pair_local,
        projection: engine.tcx.mk_place_elems(&[ProjectionElem::Field(
            rustc_abi::FieldIdx::from_usize(1),
            engine.tcx.types.u16,
        )]),
    };
    engine
        .mutable_hierarchy_dormant_operand(
            &pair,
            &pair_state,
            valid_field,
            engine.tcx.types.u16,
            None,
        )
        .unwrap();
    let forged_field = Place {
        local: pair_local,
        projection: engine.tcx.mk_place_elems(&[ProjectionElem::Field(
            rustc_abi::FieldIdx::from_usize(0),
            engine.tcx.types.u16,
        )]),
    };
    assert!(
        engine
            .mutable_hierarchy_dormant_operand(
                &pair,
                &pair_state,
                forged_field,
                engine.tcx.types.u16,
                None,
            )
            .is_err()
    );
    let mut malformed = call();
    malformed.target = None;
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut state.clone(), &malformed)
            .is_err()
    );
    let mut consumed = state.clone();
    let (Operand::Move(source) | Operand::Copy(source)) = args[0].node else {
        unreachable!()
    };
    consumed
        .missing_places
        .consume(source.local.as_usize(), Vec::new())
        .unwrap();
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut consumed, &call())
            .is_err()
    );
    let mut wrong_type = state.clone();
    wrong_type.locals[source.local.as_usize()] =
        Some(symbolic::integer(&engine.terms, 17, 16, true));
    assert!(
        engine
            .mutable_hierarchy_dormant_call(&mut wrong_type, &call())
            .is_err()
    );
    let results = engine
        .mutable_hierarchy_dormant_call(&mut state, &call())
        .unwrap()
        .unwrap();
    assert!(
        state
            .missing_places
            .check(source.local.as_usize(), &[])
            .is_err()
    );
    for result in results {
        assert_eq!(
            result.value.integer().unwrap().0.constant(),
            symbolic::integer(&engine.terms, 18, 16, false)
                .integer()
                .unwrap()
                .0
                .constant()
        );
        engine
            .mutable_hierarchy_dormant_return(id, &before, &data_term, &result.memory)
            .unwrap();
        let mut lost = result.memory.clone();
        lost.mutable_hierarchy = None;
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &lost)
                .is_err()
        );
        let mut floor = result.memory.clone();
        Rc::make_mut(&mut floor.mutable_u16)[id]
            .hierarchy
            .as_mut()
            .unwrap()
            .issued = before.issued - 1;
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &floor)
                .is_err()
        );
        let mut epoch = result.memory.clone();
        Rc::make_mut(&mut epoch.mutable_u16)[id]
            .hierarchy
            .as_mut()
            .unwrap()
            .epoch = before.epoch - 1;
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &epoch)
                .is_err()
        );
        let mut origin = result.memory.clone();
        Rc::make_mut(&mut origin.mutable_u16)[id]
            .hierarchy
            .as_mut()
            .unwrap()
            .origin = Rc::new((*before.origin).clone());
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &origin)
                .is_err()
        );
        let mut dead = result.memory.clone();
        dead.missing_places
            .consume(before.origin.allocation, Vec::new())
            .unwrap();
        assert!(
            engine
                .mutable_hierarchy_dormant_return(id, &before, &data_term, &dead)
                .is_err()
        );
    }
}

// Compiler transition tests remain separate from production Call/Return adapters.
pub(super) struct Ticket {
    origin: Rc<Origin>,
    lease: u64,
    issued_floor: u64,
    epoch_floor: u64,
    prefix: Vec<Owner>,
    frame: usize,
}

#[derive(Clone, Copy)]
pub(super) struct Metadata {
    lease: u64,
    epoch: u64,
}

impl Hierarchy {
    #[cfg(test)]
    fn from_parent(backing: &super::mutable_u16::Backing, frame: usize) -> Result<Self, String> {
        if backing.interval.is_some() || backing.generation == 0 {
            return Err("whole existing parent only".into());
        }
        Ok(Self {
            origin: Rc::new(Origin {
                certificate: backing.certificate,
                allocation: backing.allocation,
                capacity: backing.length.clone(),
                data_context: backing.data.scalar()?.clone(),
            }),
            issued: backing.generation,
            epoch: 0,
            owners: vec![Owner {
                lease: backing.generation,
                parent: 0,
                frames: vec![frame],
            }],
            pending: None,
        })
    }

    #[cfg(test)]
    fn current(&self, engine: &Engine<'_>, state: &State) -> Result<(), String> {
        let backing = state.memory.mutable_u16.first().ok_or("backing missing")?;
        if backing.interval.is_some()
            || backing.certificate != self.origin.certificate
            || backing.allocation != self.origin.allocation
            || backing.length.integer()? != self.origin.capacity.integer()?
            || !backing.data.scalar()?.belongs_to(&engine.terms)
            || !self.origin.data_context.belongs_to(&engine.terms)
            || backing.data.scalar()?.sort() != self.origin.data_context.sort()
            || !matches!(
                state.memory.get(backing.allocation),
                Some(Some(Value::Unit))
            )
        {
            return Err("current issued owner differs".into());
        }
        state
            .memory
            .check_projection_initialization(backing.allocation, &[])?;
        for owner in &self.owners {
            if owner.lease > self.issued
                || owner.frames.is_empty()
                || owner.frames.iter().any(|id| {
                    engine
                        .mutable_u16_frames
                        .borrow()
                        .get(*id)
                        .is_none_or(|weak| weak.upgrade().is_none())
                })
            {
                return Err("current live owner lineage differs".into());
            }
        }
        Ok(())
    }

    fn access(&self, lease: u64) -> Result<(), String> {
        if self.pending.is_none() && self.owners.last().map_or(lease == 0, |o| o.lease == lease) {
            Ok(())
        } else {
            Err("suspended or revoked lease".into())
        }
    }

    fn lifetime(&self, lease: u64) -> Result<(), String> {
        if lease == 0 || self.owners.iter().any(|o| o.lease == lease) {
            Ok(())
        } else {
            Err("revoked is not ancestor".into())
        }
    }

    fn metadata(&self, lease: u64) -> Result<Metadata, String> {
        self.access(lease)?;
        Ok(Metadata {
            lease,
            epoch: self.epoch,
        })
    }

    fn observe(&self, metadata: Metadata) -> Result<(), String> {
        self.access(metadata.lease)?;
        if metadata.epoch == self.epoch {
            Ok(())
        } else {
            Err("stale epoch".into())
        }
    }

    fn issue(&mut self, parent: u64, tip: Tip, slots: usize) -> Result<u64, TransitionError> {
        self.access(parent)?;
        if self.owners.len() >= 2 {
            return Err(TransitionError::Semantics(
                "hierarchy exceeds the single nested-child scope".into(),
            ));
        }
        if self.owners.iter().map(|o| o.frames.len()).sum::<usize>() >= MAX_INPUT_DEPTH
            || slots.saturating_add(5) > MAX_INPUT_VALUES
        {
            return Err(TransitionError::Resource(
                "hierarchy cumulative budget/depth",
            ));
        }
        let issued = self.issued.checked_add(1).ok_or(TransitionError::Resource(
            "hierarchy issuer counter exhausted",
        ))?;
        let epoch = self.epoch.checked_add(1).ok_or(TransitionError::Resource(
            "hierarchy epoch counter exhausted",
        ))?;
        self.pending = Some(Pending {
            lease: issued,
            parent,
            tip,
        });
        self.issued = issued;
        self.epoch = epoch;
        Ok(issued)
    }

    fn advance(&mut self, old: &Tip, next: Tip, original_source: usize) -> Result<(), String> {
        let pending = self.pending.as_mut().ok_or("pending missing")?;
        if &pending.tip != old
            || old.frame != next.frame
            || old.local == next.local
            || old.local != original_source
        {
            return Err("old tip/Body cannot advance".into());
        }
        pending.tip = next;
        Ok(())
    }

    fn enter(&mut self, tip: &Tip, frame: usize, slots: usize) -> Result<Ticket, TransitionError> {
        let pending = self.pending.as_ref().ok_or("pending missing")?;
        if &pending.tip != tip || self.owners.last().map_or(0, |o| o.lease) != pending.parent {
            return Err("current pending handoff differs".into());
        }
        if slots.saturating_add(3) > MAX_INPUT_VALUES {
            return Err(TransitionError::Resource(
                "hierarchy handoff exceeds storage budget",
            ));
        }
        let ticket = Ticket {
            origin: self.origin.clone(),
            lease: pending.lease,
            issued_floor: self.issued,
            epoch_floor: self.epoch,
            prefix: self.owners.clone(),
            frame,
        };
        self.owners.push(Owner {
            lease: pending.lease,
            parent: pending.parent,
            frames: vec![frame],
        });
        self.pending = None;
        Ok(ticket)
    }

    fn release(&mut self, ticket: &Ticket) -> Result<(), String> {
        if !Rc::ptr_eq(&self.origin, &ticket.origin)
            || self.pending.is_some()
            || self.issued < ticket.issued_floor
            || self.epoch < ticket.epoch_floor
            || self.owners.len() != ticket.prefix.len() + 1
            || self.owners[..ticket.prefix.len()] != ticket.prefix
            || self
                .owners
                .last()
                .is_none_or(|o| o.lease != ticket.lease || o.frames != [ticket.frame])
        {
            return Err("returned Memory rollback/top/prefix".into());
        }
        let epoch = self.epoch.checked_add(1).ok_or("epoch overflow")?;
        self.owners.pop();
        self.epoch = epoch;
        Ok(())
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TestFloatReturnBoundary {
    ActiveScalar,
    WholeChild,
    Dormant,
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TestFloatReturnFault {
    WrongWidth,
    MissingRaw,
    SwappedRaw,
    ChangedBinding,
}

#[cfg(test)]
std::thread_local! {
    static TEST_FLOAT_RETURN:
        std::cell::Cell<Option<(TestFloatReturnBoundary, TestFloatReturnFault)>> =
        const { std::cell::Cell::new(None) };
    static TEST_FLOAT_RETURN_BINDING_VALUE: std::cell::RefCell<Option<Value>> =
        const { std::cell::RefCell::new(None) };
    static TEST_FLOAT_RETURN_OBSERVED: std::cell::RefCell<Vec<TestFloatReturnObserved>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(test)]
struct TestFloatReturnObserved {
    label: String,
    caller: String,
    returned_data_changed: bool,
}

#[cfg(test)]
struct TestFloatReturn {
    previous: Option<(TestFloatReturnBoundary, TestFloatReturnFault)>,
    previous_value: Option<Value>,
}

#[cfg(test)]
impl TestFloatReturn {
    fn enter(
        boundary: TestFloatReturnBoundary,
        fault: TestFloatReturnFault,
        issued: &Value,
    ) -> Self {
        Self {
            previous: TEST_FLOAT_RETURN.with(|value| value.replace(Some((boundary, fault)))),
            previous_value: TEST_FLOAT_RETURN_BINDING_VALUE
                .with(|value| value.replace(Some(issued.clone()))),
        }
    }
}

#[cfg(test)]
impl Drop for TestFloatReturn {
    fn drop(&mut self) {
        TEST_FLOAT_RETURN.with(|value| value.set(self.previous));
        TEST_FLOAT_RETURN_BINDING_VALUE.with(|value| {
            value.replace(self.previous_value.take());
        });
    }
}

#[cfg(test)]
fn test_float_return_state(state: &State) -> String {
    format!(
        "{:?}",
        (
            &state.locals,
            &state.addresses,
            &state.missing_places,
            &state.conditions,
            &*state.memory,
            &state.memory.mutable_u16,
            state.memory.mutable_hierarchy,
            &state.memory.missing_places,
        )
    )
}

#[cfg(test)]
impl Engine<'_> {
    fn test_float_return(
        &mut self,
        boundary: TestFloatReturnBoundary,
        caller: &State,
        result: &Return,
    ) -> Result<(), String> {
        let Some((selected, fault)) = TEST_FLOAT_RETURN.with(std::cell::Cell::get) else {
            return Ok(());
        };
        if selected != boundary {
            return Ok(());
        }
        let Value::Float { bits, .. } = &result.value else {
            return Ok(());
        };
        let id = result.memory.mutable_hierarchy.unwrap();
        if boundary == TestFloatReturnBoundary::WholeChild
            && caller.memory.mutable_u16[id].data == result.memory.mutable_u16[id].data
        {
            // Target an actual returned branch with a completed valid callee Store.
            return Ok(());
        }
        let before = test_float_return_state(caller);
        let returned_before = format!(
            "{:?}",
            (
                &result.value,
                &result.conditions,
                &*result.memory,
                &result.memory.mutable_u16,
                result.memory.mutable_hierarchy,
                &result.memory.missing_places,
            )
        );
        let bindings_before = self.float_encodings.clone();
        let mut injected = result.value.clone();
        let mut binding_restore = None;
        match fault {
            TestFloatReturnFault::WrongWidth => {
                injected = symbolic::float_from_bits(
                    &self.terms,
                    self.terms
                        .bit_vector(0, if *bits == 32 { 64 } else { 32 })
                        .unwrap(),
                    if *bits == 32 { 64 } else { 32 },
                );
            }
            TestFloatReturnFault::MissingRaw => {
                let Value::Float { raw_bits, .. } = &mut injected else {
                    unreachable!()
                };
                *raw_bits = None;
            }
            TestFloatReturnFault::SwappedRaw => {
                let Value::Float { raw_bits, .. } = &mut injected else {
                    unreachable!()
                };
                // A valid copied NaN with a different payload is not the copied pair.
                *raw_bits = Some(
                    self.terms
                        .bit_vector(
                            if *bits == 32 {
                                0x7fc0_0456
                            } else {
                                0x7ff8_0000_0000_0456
                            },
                            *bits,
                        )
                        .unwrap(),
                );
            }
            TestFloatReturnFault::ChangedBinding => {
                injected = TEST_FLOAT_RETURN_BINDING_VALUE
                    .with(|value| value.borrow().as_ref().unwrap().clone());
                let Value::Float {
                    raw_bits: Some(raw),
                    ..
                } = &injected
                else {
                    unreachable!()
                };
                let symbol = raw.symbol_index().unwrap();
                let issued = self.float_encodings.remove(&symbol).unwrap();
                self.float_encodings
                    .insert(symbol, self.terms.boolean(false));
                binding_restore = Some((symbol, issued));
            }
        }
        let original = self
            .mutable_hierarchy_float_backing(id, &result.memory)?
            .unwrap();
        let refused = self.mutable_hierarchy_primitive_value_for(
            original,
            &injected,
            &result.conditions,
            Some(original),
        );
        // Restore the issuer binding explicitly, then the complete pre-fault map.
        if let Some((symbol, issued)) = binding_restore {
            self.float_encodings.insert(symbol, issued);
        }
        self.float_encodings = bindings_before;
        assert!(
            refused.is_err(),
            "actual {boundary:?} {fault:?} must refuse"
        );
        assert_eq!(test_float_return_state(caller), before);
        assert_eq!(
            format!(
                "{:?}",
                (
                    &result.value,
                    &result.conditions,
                    &*result.memory,
                    &result.memory.mutable_u16,
                    result.memory.mutable_hierarchy,
                    &result.memory.missing_places,
                )
            ),
            returned_before
        );
        TEST_FLOAT_RETURN_OBSERVED.with(|observed| {
            observed.borrow_mut().push(TestFloatReturnObserved {
                label: format!("{boundary:?}/{fault:?}/{bits}"),
                caller: before,
                returned_data_changed: caller.memory.mutable_u16[id].data
                    != result.memory.mutable_u16[id].data,
            });
        });
        Err(format!(
            "test-only actual Float Return refusal: {boundary:?}/{fault:?}"
        ))
    }
}

#[cfg(test)]
pub(super) fn compiler_float_boundary_probe<'tcx>(
    engine: &mut Engine<'tcx>,
    root: &Rc<Body<'tcx>>,
    element: Ty<'tcx>,
) {
    let (block, data) = root
        .basic_blocks
        .iter_enumerated()
        .find(|(_, b)| matches!(b.terminator().kind, TerminatorKind::Call { .. }))
        .unwrap();
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        ..
    } = &data.terminator().kind
    else {
        unreachable!()
    };
    let ty::FnDef(definition, generic) = func.ty(&root.local_decls, engine.tcx).kind() else {
        unreachable!()
    };
    let instance = engine
        .resolve_function_item(*definition, generic.skip_binder())
        .unwrap();
    let mut memory = Memory::default();
    let mut conditions = Vec::new();
    let value = engine
        .mutable_u16_input(element, &mut memory, &mut conditions)
        .unwrap();
    let mut state = State {
        flow: activation_flow::Flow::Unarmed,
        locals: vec![None; root.local_decls.len()],
        addresses: vec![None; root.local_decls.len()],
        constant_receipts: constant_reference_receipts::Slots::default(),
        missing_places: Default::default(),
        conditions,
        memory,
    };
    state.locals[1] = Some(value);
    for statement in &data.statements {
        if let StatementKind::Assign(a) = &statement.kind
            && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
        {
            assert!(
                engine
                    .mutable_u16_stage(root, &mut state, a.0, &a.1, &statement.kind)
                    .unwrap()
            );
        }
    }
    let call = || super::mutable_u16_children::ChildCall {
        body: root,
        block,
        instance,
        args,
        destination: *destination,
        target: *target,
        stack: &[],
        site: (root.source.def_id(), data.terminator().source_info.span),
    };
    assert!(!TEST_FLOAT_HIERARCHY.with(std::cell::Cell::get));
    assert_eq!(float_hierarchy_enabled(), FLOAT_HIERARCHY_ENABLED);
    assert_eq!(
        engine.mutable_hierarchy_route(&state, &call()).unwrap(),
        FLOAT_HIERARCHY_ENABLED,
    );
    {
        let _scope = TestFloatHierarchy::enable();
        assert!(float_hierarchy_enabled());
        assert!(TEST_FLOAT_HIERARCHY.with(std::cell::Cell::get));
        {
            let _nested = TestFloatHierarchy::enable();
            assert!(float_hierarchy_enabled());
            assert!(TEST_FLOAT_HIERARCHY.with(std::cell::Cell::get));
        }
        assert!(float_hierarchy_enabled());
        assert!(TEST_FLOAT_HIERARCHY.with(std::cell::Cell::get));
        let panicked = std::panic::catch_unwind(|| {
            let _nested = TestFloatHierarchy::enable();
            panic!("Float hierarchy restoration probe");
        });
        assert!(panicked.is_err());
        assert!(float_hierarchy_enabled());
        assert!(TEST_FLOAT_HIERARCHY.with(std::cell::Cell::get));
        assert!(engine.mutable_hierarchy_route(&state, &call()).unwrap());
        let width = engine.float_type(element).unwrap();
        let mut forged_body = (**root).clone();
        let wrong_integer = if width == 32 {
            engine.tcx.types.u32
        } else {
            engine.tcx.types.u64
        };
        let raw_local = rustc_middle::mir::Local::from_usize(1);
        forged_body.local_decls[raw_local].ty = Ty::new_tup(engine.tcx, &[wrong_integer]);
        let forged_field = Place {
            local: raw_local,
            projection: engine.tcx.mk_place_elems(&[ProjectionElem::Field(
                rustc_abi::FieldIdx::from_usize(0),
                element,
            )]),
        };
        assert!(
            engine
                .mutable_hierarchy_float_operand(
                    &forged_body,
                    &Operand::Copy(forged_field),
                    element
                )
                .is_err()
        );
        let mut wrong_memory = Memory::default();
        let mut wrong_conditions = Vec::new();
        let wrong_role = engine
            .mutable_u16_input(wrong_integer, &mut wrong_memory, &mut wrong_conditions)
            .unwrap();
        let mut wrong_state = state.clone();
        wrong_state.memory = wrong_memory;
        wrong_state.conditions = wrong_conditions;
        let source = match args[0].node {
            Operand::Copy(p) | Operand::Move(p) => p.local.as_usize(),
            Operand::Constant(_) | Operand::RuntimeChecks(_) => unreachable!(),
        };
        wrong_state.locals[source] = Some(wrong_role);
        assert!(
            !engine
                .mutable_hierarchy_route(&wrong_state, &call())
                .unwrap()
        );

        let nan = if width == 32 {
            0x7fc0_0123
        } else {
            0x7ff8_0000_0000_0123
        };
        let valid = symbolic::float_from_bits(
            &engine.terms,
            engine.terms.bit_vector(nan, width).unwrap(),
            width,
        );
        engine
            .mutable_hierarchy_primitive_value_for(
                element,
                &valid,
                &state.conditions,
                Some(element),
            )
            .unwrap();
        let mut swapped = valid.clone();
        if let Value::Float { raw_bits, .. } = &mut swapped {
            *raw_bits = Some(engine.terms.bit_vector(nan + 1, width).unwrap());
        }
        let mut absent = valid.clone();
        if let Value::Float { raw_bits, .. } = &mut absent {
            *raw_bits = None;
        }
        let foreign = Context::default();
        let other_width = if width == 32 { 64 } else { 32 };
        for bad in [
            swapped,
            absent,
            symbolic::float_from_bits(&foreign, foreign.bit_vector(nan, width).unwrap(), width),
            symbolic::float_from_bits(
                &engine.terms,
                engine.terms.bit_vector(0, other_width).unwrap(),
                other_width,
            ),
        ] {
            let before = state.memory.mutable_u16[0].clone();
            assert!(
                engine
                    .mutable_hierarchy_primitive_value_for(
                        element,
                        &bad,
                        &state.conditions,
                        Some(element)
                    )
                    .is_err()
            );
            let after = &state.memory.mutable_u16[0];
            assert_eq!(before.data, after.data);
            assert_eq!(before.phase, after.phase);
            assert_eq!(before.generation, after.generation);
        }
        assert!(
            engine
                .mutable_hierarchy_primitive_value_for(
                    element,
                    &valid,
                    &state.conditions,
                    Some(engine.tcx.types.u32)
                )
                .is_err()
        );
        let Value::Float { expression, .. } = &valid else {
            unreachable!()
        };
        let produced = engine.materialize_float(Value::Float {
            expression: engine
                .terms
                .apply(Op::FpNeg, std::slice::from_ref(expression))
                .unwrap(),
            bits: width,
            raw_bits: None,
        });
        engine
            .mutable_hierarchy_primitive_value_for(
                element,
                &produced,
                &state.conditions,
                Some(element),
            )
            .unwrap();
        let Value::Float {
            raw_bits: Some(raw),
            ..
        } = &produced
        else {
            unreachable!()
        };
        let symbol = raw.symbol_index().unwrap();
        let binding = engine.float_encodings.remove(&symbol).unwrap();
        assert!(
            engine
                .mutable_hierarchy_primitive_value_for(
                    element,
                    &produced,
                    &state.conditions,
                    Some(element)
                )
                .is_err()
        );
        engine.float_encodings.insert(symbol, binding);
        let mut deep = valid.clone();
        let alternative = symbolic::float_from_bits(
            &engine.terms,
            engine.terms.bit_vector(0, width).unwrap(),
            width,
        );
        for _ in 0..17 {
            let condition = engine.fresh(Sort::Bool);
            deep = engine
                .float_pairs
                .selected(&engine.terms, &condition, &deep, &alternative)
                .unwrap();
        }
        assert!(
            engine
                .mutable_hierarchy_primitive_value_for(
                    element,
                    &deep,
                    &state.conditions,
                    Some(element)
                )
                .is_err()
        );
        assert!(TEST_FLOAT_RETURN.with(std::cell::Cell::get).is_none());
        for boundary in [
            TestFloatReturnBoundary::ActiveScalar,
            TestFloatReturnBoundary::WholeChild,
        ] {
            for fault in [
                TestFloatReturnFault::WrongWidth,
                TestFloatReturnFault::MissingRaw,
                TestFloatReturnFault::SwappedRaw,
                TestFloatReturnFault::ChangedBinding,
            ] {
                TEST_FLOAT_RETURN_OBSERVED.with(|v| v.borrow_mut().clear());
                let bindings = engine.float_encodings.clone();
                {
                    let _fault = TestFloatReturn::enter(boundary, fault, &produced);
                    {
                        let _nested = TestFloatReturn::enter(
                            TestFloatReturnBoundary::Dormant,
                            TestFloatReturnFault::MissingRaw,
                            &produced,
                        );
                    }
                    assert_eq!(
                        TEST_FLOAT_RETURN.with(std::cell::Cell::get),
                        Some((boundary, fault))
                    );
                    let panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        let _nested = TestFloatReturn::enter(
                            TestFloatReturnBoundary::Dormant,
                            TestFloatReturnFault::WrongWidth,
                            &produced,
                        );
                        panic!("Float Return fault restoration probe");
                    }));
                    assert!(panicked.is_err());
                    assert_eq!(
                        TEST_FLOAT_RETURN.with(std::cell::Cell::get),
                        Some((boundary, fault))
                    );
                    let error = engine
                        .mutable_hierarchy_call(&mut state.clone(), call())
                        .err()
                        .expect("actual Float Return boundary must refuse");
                    assert!(
                        error.contains("test-only actual Float Return refusal"),
                        "{error}"
                    );
                }
                assert!(TEST_FLOAT_RETURN.with(std::cell::Cell::get).is_none());
                // Normal callee execution may issue bindings; the injected binding itself
                // is restored.
                for (symbol, binding) in bindings {
                    assert_eq!(engine.float_encodings.get(&symbol), Some(&binding));
                }
                TEST_FLOAT_RETURN_OBSERVED.with(|observed| {
                    let observed = observed.borrow();
                    assert_eq!(observed.len(), 1);
                    assert_eq!(observed[0].label, format!("{boundary:?}/{fault:?}/{width}"));
                    if boundary == TestFloatReturnBoundary::WholeChild {
                        assert!(observed[0].returned_data_changed);
                    }
                    eprintln!(
                        "Stage211 actual Return transactional: {} returned-data-changed={}",
                        observed[0].label, observed[0].returned_data_changed,
                    );
                });
            }
        }
        let results = engine
            .mutable_hierarchy_call(&mut state.clone(), call())
            .unwrap()
            .unwrap();
        // Use the actual leaf's scalar Call in a valid returned dormant namespace.
        let outer = engine.instantiated_body(instance).unwrap();
        let leaf_instance = outer
            .basic_blocks
            .iter()
            .find_map(|b| {
                let TerminatorKind::Call { func, .. } = &b.terminator().kind else {
                    return None;
                };
                let ty::FnDef(d, a) = func.ty(&outer.local_decls, engine.tcx).kind() else {
                    return None;
                };
                engine.resolve_function_item(*d, a.skip_binder()).ok()
            })
            .unwrap();
        let leaf = engine.instantiated_body(leaf_instance).unwrap();
        let (scalar_block, scalar_data) = leaf
            .basic_blocks
            .iter_enumerated()
            .find(|(_, b)| {
                let TerminatorKind::Call { func, .. } = &b.terminator().kind else {
                    return false;
                };
                let ty::FnDef(d, a) = func.ty(&leaf.local_decls, engine.tcx).kind() else {
                    return false;
                };
                let selected = engine.resolve_function_item(*d, a.skip_binder()).unwrap();
                let signature = engine.call_signature(selected).unwrap();
                signature.inputs() == [element] && signature.output() == element
            })
            .unwrap();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = &scalar_data.terminator().kind
        else {
            unreachable!()
        };
        let ty::FnDef(d, a) = func.ty(&leaf.local_decls, engine.tcx).kind() else {
            unreachable!()
        };
        let scalar_instance = engine.resolve_function_item(*d, a.skip_binder()).unwrap();
        let mut dormant = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; leaf.local_decls.len()],
            addresses: vec![None; leaf.local_decls.len()],
            constant_receipts: constant_reference_receipts::Slots::default(),
            missing_places: Default::default(),
            conditions: results[0].conditions.clone(),
            memory: results[0].memory.clone(),
        };
        let (Operand::Copy(source) | Operand::Move(source)) = args[0].node else {
            unreachable!()
        };
        assert!(source.projection.is_empty());
        dormant.locals[source.local.as_usize()] = Some(valid.clone());
        let dormant_call = || super::mutable_u16_children::ChildCall {
            body: &leaf,
            block: scalar_block,
            instance: scalar_instance,
            args,
            destination: *destination,
            target: *target,
            stack: &[],
            site: (
                leaf.source.def_id(),
                scalar_data.terminator().source_info.span,
            ),
        };
        assert!(
            engine
                .mutable_hierarchy_call(&mut dormant.clone(), dormant_call())
                .unwrap()
                .is_some()
        );
        for fault in [
            TestFloatReturnFault::WrongWidth,
            TestFloatReturnFault::MissingRaw,
            TestFloatReturnFault::SwappedRaw,
            TestFloatReturnFault::ChangedBinding,
        ] {
            let mut caller = dormant.clone();
            TEST_FLOAT_RETURN_OBSERVED.with(|v| v.borrow_mut().clear());
            {
                let _fault =
                    TestFloatReturn::enter(TestFloatReturnBoundary::Dormant, fault, &produced);
                let error = engine
                    .mutable_hierarchy_call(&mut caller, dormant_call())
                    .err()
                    .expect("actual dormant Float Return must refuse");
                assert!(
                    error.contains("test-only actual Float Return refusal"),
                    "{error}"
                );
            }
            assert!(TEST_FLOAT_RETURN.with(std::cell::Cell::get).is_none());
            TEST_FLOAT_RETURN_OBSERVED.with(|observed| {
                let observed = observed.borrow();
                assert_eq!(observed.len(), 1);
                assert_eq!(observed[0].label, format!("Dormant/{fault:?}/{width}"));
                // Argument Move consumption precedes this boundary and is not rolled back.
                assert_eq!(test_float_return_state(&caller), observed[0].caller);
                eprintln!(
                    "Stage211 actual Return transactional: {} returned-data-changed={}",
                    observed[0].label, observed[0].returned_data_changed,
                );
            });
        }
        assert!(!results.is_empty());
        for result in &results {
            let current = engine
                .mutable_hierarchy_float_backing(0, &result.memory)
                .unwrap();
            engine
                .mutable_hierarchy_primitive_value_for(
                    element,
                    &result.value,
                    &result.conditions,
                    current,
                )
                .unwrap();
            let backing = engine.mutable_u16_backing(0, &result.memory).unwrap();
            let hierarchy = backing.hierarchy.as_ref().unwrap();
            assert!(hierarchy.owners.is_empty() && hierarchy.pending.is_none());
            let mut changed = result.memory.clone();
            Rc::make_mut(&mut changed.mutable_u16)[0].data = super::mutable_u16::Storage::Scalar(
                engine.fresh(backing.data.scalar().unwrap().sort().clone()),
            );
            assert!(
                engine
                    .mutable_hierarchy_dormant_return(
                        0,
                        hierarchy,
                        backing.data.scalar().unwrap(),
                        &changed
                    )
                    .is_err()
            );
            let mut foreign_data = result.memory.clone();
            Rc::make_mut(&mut foreign_data.mutable_u16)[0].data =
                super::mutable_u16::Storage::Scalar(
                    foreign
                        .symbol(0, backing.data.scalar().unwrap().sort().clone())
                        .unwrap(),
                );
            assert!(
                engine
                    .mutable_hierarchy_float_backing(0, &foreign_data)
                    .is_err()
            );
            let mut stale = result.memory.clone();
            Rc::make_mut(&mut stale.mutable_u16)[0].generation = hierarchy.issued + 1;
            assert!(engine.mutable_hierarchy_float_backing(0, &stale).is_err());
            let mut masked = result.memory.clone();
            masked
                .missing_places
                .consume(backing.allocation, Vec::new())
                .unwrap();
            assert!(engine.mutable_hierarchy_float_backing(0, &masked).is_err());
            let mut wrong = result.memory.clone();
            wrong.mutable_hierarchy = Some(usize::MAX);
            assert!(engine.mutable_hierarchy_namespace(&wrong).is_err());
            let mut rollback = hierarchy.clone();
            let tip = Tip {
                frame: engine.mutable_u16_register_frame(root).unwrap(),
                statement: 1,
                local: 1,
            };
            let slots = result.memory.storage_slots();
            rollback.issue(0, tip.clone(), slots).unwrap();
            let ticket = rollback.enter(&tip, tip.frame, slots).unwrap();
            rollback.epoch = ticket.epoch_floor - 1;
            assert!(rollback.release(&ticket).is_err());
        }
    }
    assert!(!TEST_FLOAT_HIERARCHY.with(std::cell::Cell::get));
    assert_eq!(float_hierarchy_enabled(), FLOAT_HIERARCHY_ENABLED);
}

#[cfg(test)]
mod tests {
    use super::*;

    const HIERARCHY_FLAGS: [TestHierarchyFlag; 6] = [
        TestHierarchyFlag::Associated,
        TestHierarchyFlag::Integer,
        TestHierarchyFlag::Bool,
        TestHierarchyFlag::Char,
        TestHierarchyFlag::Float,
        TestHierarchyFlag::Issuance,
    ];

    fn hierarchy_overrides() -> [bool; 6] {
        HIERARCHY_FLAGS.map(TestHierarchyFlag::get)
    }

    #[test]
    fn all_hierarchy_overrides_restore_previous_true_after_nested_panic() {
        assert_eq!(hierarchy_overrides(), [false; 6]);
        for flag in HIERARCHY_FLAGS {
            {
                let _outer = TestHierarchyOverride::enable(flag);
                assert!(flag.get());
                {
                    let _inner = TestHierarchyOverride::enable(flag);
                    assert!(flag.get());
                }
                assert!(flag.get());
                assert!(
                    std::panic::catch_unwind(|| {
                        let _inner = TestHierarchyOverride::enable(flag);
                        assert!(flag.get());
                        panic!("nested hierarchy override restoration");
                    })
                    .is_err()
                );
                assert!(flag.get());
            }
            assert_eq!(hierarchy_overrides(), [false; 6]);
            assert!(
                std::panic::catch_unwind(|| {
                    let _scope = TestHierarchyOverride::enable(flag);
                    assert!(flag.get());
                    panic!("outer hierarchy override restoration");
                })
                .is_err()
            );
            assert_eq!(hierarchy_overrides(), [false; 6]);
        }
    }

    #[test]
    fn hierarchy_overrides_restore_each_cross_domain_independently() {
        for (outer_index, outer) in HIERARCHY_FLAGS.into_iter().enumerate() {
            for (inner_index, inner) in HIERARCHY_FLAGS.into_iter().enumerate() {
                if outer == inner {
                    continue;
                }
                assert_eq!(hierarchy_overrides(), [false; 6]);
                {
                    let _outer = TestHierarchyOverride::enable(outer);
                    let mut expected = [false; 6];
                    expected[outer_index] = true;
                    assert_eq!(hierarchy_overrides(), expected);
                    assert!(
                        std::panic::catch_unwind(|| {
                            let _inner = TestHierarchyOverride::enable(inner);
                            let mut nested = expected;
                            nested[inner_index] = true;
                            assert_eq!(hierarchy_overrides(), nested);
                            panic!("cross-domain hierarchy restoration");
                        })
                        .is_err()
                    );
                    assert_eq!(hierarchy_overrides(), expected);
                }
                assert_eq!(hierarchy_overrides(), [false; 6]);
            }
        }
    }

    #[test]
    fn hierarchy_overrides_are_isolated_between_two_worker_threads() {
        assert_eq!(hierarchy_overrides(), [false; 6]);
        let observations;
        let main_enabled;
        let main_after_workers;
        {
            let _main_scope = TestFloatHierarchy::enable();
            main_enabled = hierarchy_overrides();
            let (ready, ready_receiver) = std::sync::mpsc::channel();
            let mut releases = Vec::new();
            let workers: Vec<_> = [0, 5]
                .into_iter()
                .map(|index| {
                    let ready = ready.clone();
                    let (release, release_receiver) = std::sync::mpsc::channel();
                    releases.push(release);
                    std::thread::spawn(move || {
                        let initial = hierarchy_overrides();
                        let enabled;
                        let after_panic;
                        let released;
                        let panicked;
                        {
                            let flag = HIERARCHY_FLAGS[index];
                            let _outer = TestHierarchyOverride::enable(flag);
                            enabled = hierarchy_overrides();
                            let _ = ready.send((index, enabled));
                            released = release_receiver
                                .recv_timeout(std::time::Duration::from_secs(5))
                                .is_ok();
                            panicked = std::panic::catch_unwind(|| {
                                let _inner = TestHierarchyOverride::enable(flag);
                                panic!("worker hierarchy restoration");
                            })
                            .is_err();
                            after_panic = hierarchy_overrides();
                        }
                        (
                            index,
                            initial,
                            enabled,
                            after_panic,
                            hierarchy_overrides(),
                            released,
                            panicked,
                        )
                    })
                })
                .collect();
            drop(ready);
            let ready_results: Vec<_> = (0..2)
                .map(|_| ready_receiver.recv_timeout(std::time::Duration::from_secs(5)))
                .collect();
            let release_results: Vec<_> = releases.iter().map(|release| release.send(())).collect();
            let worker_results: Vec<_> = workers.into_iter().map(|worker| worker.join()).collect();
            main_after_workers = hierarchy_overrides();
            observations = (ready_results, release_results, worker_results);
        }
        assert_eq!(hierarchy_overrides(), [false; 6]);
        let mut main_expected = [false; 6];
        main_expected[4] = true;
        assert_eq!(main_enabled, main_expected);
        assert_eq!(main_after_workers, main_expected);
        let (ready_results, release_results, worker_results) = observations;
        for result in ready_results {
            let (index, observed) = result.unwrap();
            let mut expected = [false; 6];
            expected[index] = true;
            assert_eq!(observed, expected);
        }
        assert!(release_results.iter().all(Result::is_ok));
        for result in worker_results {
            let (index, initial, enabled, after_panic, final_state, released, panicked) =
                result.unwrap();
            let mut expected = [false; 6];
            expected[index] = true;
            assert_eq!(initial, [false; 6]);
            assert_eq!(enabled, expected);
            assert_eq!(after_panic, expected);
            assert_eq!(final_state, [false; 6]);
            assert!(released && panicked);
        }
        std::thread::spawn(|| assert_eq!(hierarchy_overrides(), [false; 6]))
            .join()
            .unwrap();
    }

    #[test]
    fn scoped_public_issuance_restores_nested_and_panicking_tests() {
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        assert_eq!(issuance_enabled(), ISSUANCE_ENABLED);
        {
            let _outer = TestIssuance::enable();
            assert!(issuance_enabled());
            {
                let _inner = TestIssuance::enable();
                assert!(issuance_enabled());
            }
            assert!(issuance_enabled());
        }
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        assert_eq!(issuance_enabled(), ISSUANCE_ENABLED);
        assert!(
            std::panic::catch_unwind(|| {
                let _scope = TestIssuance::enable();
                assert!(issuance_enabled());
                panic!("test scoped issuer restoration");
            })
            .is_err()
        );
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        assert_eq!(issuance_enabled(), ISSUANCE_ENABLED);
    }

    #[test]
    fn scoped_bool_selection_restores_nested_and_panicking_tests() {
        assert!(!TEST_BOOL_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(bool_hierarchy_enabled(), BOOL_HIERARCHY_ENABLED);
        {
            let _outer = TestBoolHierarchy::enable();
            assert!(TEST_BOOL_HIERARCHY.with(std::cell::Cell::get));
            assert!(bool_hierarchy_enabled());
            {
                let _inner = TestBoolHierarchy::enable();
                assert!(TEST_BOOL_HIERARCHY.with(std::cell::Cell::get));
                assert!(bool_hierarchy_enabled());
            }
            assert!(TEST_BOOL_HIERARCHY.with(std::cell::Cell::get));
            assert!(bool_hierarchy_enabled());
        }
        assert!(!TEST_BOOL_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(bool_hierarchy_enabled(), BOOL_HIERARCHY_ENABLED);
        assert!(
            std::panic::catch_unwind(|| {
                let _scope = TestBoolHierarchy::enable();
                assert!(TEST_BOOL_HIERARCHY.with(std::cell::Cell::get));
                assert!(bool_hierarchy_enabled());
                panic!("test scoped bool restoration");
            })
            .is_err()
        );
        assert!(!TEST_BOOL_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(bool_hierarchy_enabled(), BOOL_HIERARCHY_ENABLED);
    }

    #[test]
    fn scoped_char_selection_restores_nested_and_panicking_tests() {
        assert!(!TEST_CHAR_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(char_hierarchy_enabled(), CHAR_HIERARCHY_ENABLED);
        {
            let _outer = TestCharHierarchy::enable();
            assert!(TEST_CHAR_HIERARCHY.with(std::cell::Cell::get));
            assert!(char_hierarchy_enabled());
            {
                let _inner = TestCharHierarchy::enable();
                assert!(TEST_CHAR_HIERARCHY.with(std::cell::Cell::get));
                assert!(char_hierarchy_enabled());
            }
            assert!(TEST_CHAR_HIERARCHY.with(std::cell::Cell::get));
            assert!(char_hierarchy_enabled());
        }
        assert!(!TEST_CHAR_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(char_hierarchy_enabled(), CHAR_HIERARCHY_ENABLED);
        assert!(
            std::panic::catch_unwind(|| {
                let _scope = TestCharHierarchy::enable();
                assert!(TEST_CHAR_HIERARCHY.with(std::cell::Cell::get));
                assert!(char_hierarchy_enabled());
                panic!("test scoped Char restoration");
            })
            .is_err()
        );
        assert!(!TEST_CHAR_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(char_hierarchy_enabled(), CHAR_HIERARCHY_ENABLED);
    }

    #[test]
    fn scoped_associated_selection_restores_nested_and_panicking_tests() {
        assert!(!TEST_ASSOCIATED_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(associated_hierarchy_enabled(), ASSOCIATED_HIERARCHY_ENABLED);
        {
            let _outer = TestAssociatedHierarchy::enable();
            assert!(TEST_ASSOCIATED_HIERARCHY.with(std::cell::Cell::get));
            {
                let _inner = TestAssociatedHierarchy::enable();
                assert!(associated_hierarchy_enabled());
            }
            assert!(TEST_ASSOCIATED_HIERARCHY.with(std::cell::Cell::get));
        }
        assert!(!TEST_ASSOCIATED_HIERARCHY.with(std::cell::Cell::get));
        assert!(
            std::panic::catch_unwind(|| {
                let _scope = TestAssociatedHierarchy::enable();
                assert!(TEST_ASSOCIATED_HIERARCHY.with(std::cell::Cell::get));
                panic!("test associated restoration");
            })
            .is_err()
        );
        assert!(!TEST_ASSOCIATED_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(associated_hierarchy_enabled(), ASSOCIATED_HIERARCHY_ENABLED);
    }

    #[test]
    fn scoped_integer_selection_restores_nested_and_panicking_tests() {
        assert!(!TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
        {
            let _outer = TestIntegerHierarchy::enable();
            assert!(TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
            {
                let _inner = TestIntegerHierarchy::enable();
                assert!(TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
            }
            assert!(TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
        }
        assert!(!TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
        assert!(
            std::panic::catch_unwind(|| {
                let _scope = TestIntegerHierarchy::enable();
                panic!("test issuer restoration");
            })
            .is_err()
        );
        assert!(!TEST_INTEGER_HIERARCHY.with(std::cell::Cell::get));
        assert_eq!(integer_hierarchy_enabled(), INTEGER_HIERARCHY_ENABLED);
    }

    pub(super) fn production_call<'tcx>(
        engine: &mut Engine<'tcx>,
        root: &Rc<Body<'tcx>>,
        base: &State,
    ) {
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        let (block, call) = root
            .basic_blocks
            .iter_enumerated()
            .find_map(|(block, data)| {
                matches!(data.terminator().kind, TerminatorKind::Call { .. })
                    .then_some((block, &data.terminator().kind))
            })
            .unwrap();
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target,
            ..
        } = call
        else {
            unreachable!()
        };
        let ty::FnDef(definition, generic) = func.ty(&root.local_decls, engine.tcx).kind() else {
            unreachable!()
        };
        let instance = engine
            .resolve_function_item(*definition, generic.skip_binder())
            .unwrap();
        let mut state = base.clone();
        for statement in &root.basic_blocks[block].statements {
            if let StatementKind::Assign(a) = &statement.kind
                && matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _))
            {
                assert!(
                    engine
                        .mutable_u16_stage(root, &mut state, a.0, &a.1, &statement.kind)
                        .unwrap()
                );
            }
        }
        let before = state.memory.mutable_u16[0].data.clone();
        // Preserve the disabled default-route assertion in archived/checkpoint test builds.
        let call = || super::super::mutable_u16_children::ChildCall {
            body: root,
            block,
            instance,
            args,
            destination: *destination,
            target: *target,
            stack: &[],
            site: (
                root.source.def_id(),
                root.basic_blocks[block].terminator().source_info.span,
            ),
        };
        if !ISSUANCE_ENABLED {
            assert!(
                engine
                    .mutable_hierarchy_call(&mut state.clone(), call())
                    .unwrap()
                    .is_none()
            );
        }
        assert!(engine.mutable_hierarchy_route(&state, &call()).unwrap());
        let selected = engine.instantiated_body(instance).unwrap();
        assert!(engine.mutable_hierarchy_selector(&selected, 1).unwrap());
        for entry in ["scalar", "leaf_len"] {
            let definition = engine
                .tcx
                .iter_local_def_id()
                .find(|d| {
                    engine.tcx.def_kind(d.to_def_id()) == DefKind::Fn
                        && engine.tcx.item_name(d.to_def_id()).as_str() == entry
                })
                .unwrap()
                .to_def_id();
            let instance = engine
                .resolve_function_item(definition, engine.tcx.mk_args(&[]))
                .unwrap();
            let ordinary = engine.instantiated_body(instance).unwrap();
            assert!(!engine.mutable_hierarchy_selector(&ordinary, 1).unwrap());
        }
        let source = match args[0].node {
            Operand::Copy(place) | Operand::Move(place) => place.local.as_usize(),
            Operand::Constant(_) => unreachable!(),
            Operand::RuntimeChecks(_) => unreachable!(),
        };
        // A routing cache cannot issue authority or recover a missing namespace.
        let mut unissued = state.clone();
        unissued.memory.mutable_hierarchy = Some(0);
        assert!(
            engine
                .mutable_hierarchy_namespace(&unissued.memory)
                .is_err()
        );
        assert!(
            engine
                .mutable_hierarchy_call(&mut unissued, call())
                .is_err()
        );
        let mut wrong = state.clone();
        wrong.memory.mutable_hierarchy = Some(usize::MAX);
        assert!(engine.mutable_hierarchy_call(&mut wrong, call()).is_err());
        let mut consumed = state.clone();
        consumed.missing_places.consume(source, Vec::new()).unwrap();
        assert!(!engine.mutable_hierarchy_route(&consumed, &call()).unwrap());
        let mut active_legacy = state.clone();
        let frame = engine.mutable_u16_register_frame(root).unwrap();
        Rc::make_mut(&mut active_legacy.memory.mutable_u16)[0].phase =
            super::super::mutable_u16_children::Phase::Active {
                frames: vec![frame],
            };
        assert!(
            !engine
                .mutable_hierarchy_route(&active_legacy, &call())
                .unwrap()
        );

        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut consumed, call())
                .is_err()
        );
        let mut ghost = state.clone();
        ghost.locals[source] = Some(Value::Unit);
        assert!(!engine.mutable_hierarchy_route(&ghost, &call()).unwrap());
        for element in [engine.tcx.types.i16, engine.tcx.types.f32] {
            let mut memory = Memory::default();
            let mut conditions = Vec::new();
            let role = engine
                .mutable_u16_input(element, &mut memory, &mut conditions)
                .unwrap();
            let mut other = state.clone();
            other.memory = memory;
            other.conditions = conditions;
            other.locals[source] = Some(role);
            assert!(!engine.mutable_hierarchy_route(&other, &call()).unwrap());
            let _scope = TestIssuance::enable();
            assert!(
                engine
                    .mutable_hierarchy_call(&mut other, call())
                    .unwrap()
                    .is_none()
            );
        }

        let other_args = args.to_vec();
        let mut forged = call();
        forged.args = &other_args;
        assert!(!engine.mutable_hierarchy_route(&state, &forged).unwrap());
        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut state.clone(), forged)
                .is_err()
        );
        let different = Rc::new((**root).clone());
        let mut forged = call();
        forged.body = &different;
        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut state.clone(), forged)
                .is_err()
        );
        let mut forged = call();
        forged.target = None;
        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut state.clone(), forged)
                .is_err()
        );
        let mut forged = call();
        forged.destination = Place::from(rustc_middle::mir::RETURN_PLACE);
        assert!(
            engine
                .mutable_hierarchy_call_transaction(&mut state.clone(), forged)
                .is_err()
        );
        // Exercise the public Call route and all actual child staging/Return hooks. The scoped
        // test switch changes only issuer selection; the production constant remains false.
        let _issuance = TestIssuance::enable();
        assert!(issuance_enabled());
        for mut noncandidate in [consumed.clone(), active_legacy.clone(), ghost.clone()] {
            assert!(
                engine
                    .mutable_hierarchy_call(&mut noncandidate, call())
                    .unwrap()
                    .is_none()
            );
        }
        let mut forged = call();
        forged.args = &other_args;
        assert!(
            engine
                .mutable_hierarchy_call(&mut state.clone(), forged)
                .unwrap()
                .is_none()
        );
        let mut forged = call();
        forged.target = None;
        assert!(
            engine
                .mutable_hierarchy_call(&mut state.clone(), forged)
                .unwrap()
                .is_none()
        );
        let outcome = engine.mutable_hierarchy_call(&mut state, call());
        let results = outcome.unwrap().unwrap();
        assert!(!results.is_empty());
        let mut observed_current_store = false;
        for result in results {
            assert!(matches!(result.value, Value::Unit));
            assert_eq!(result.memory.mutable_hierarchy, Some(0));
            let backing = &result.memory.mutable_u16[0];
            observed_current_store |= backing.data != before;
            compiler_dormant_probe(engine, &result.memory, &result.conditions);
            let h = backing.hierarchy.as_ref().unwrap();
            assert!(h.owners.is_empty() && h.pending.is_none());
            assert!(h.issued >= 3 && h.epoch >= 6);
            assert!(h.role_valid(&symbolic::MutableU16Role::Root, true));
            assert!(!h.role_valid(&symbolic::MutableU16Role::Child { generation: 1 }, true));
            assert!(!h.role_valid(
                &symbolic::MutableU16Role::HierarchyChild { lease: h.issued },
                false
            ));
            assert!(!h.role_valid(
                &symbolic::MutableU16Role::HierarchyMetadata { lease: 0, epoch: 0 },
                true
            ));
            engine.mutable_hierarchy_namespace(&result.memory).unwrap();
            let mut absent = result.memory.clone();
            absent.mutable_hierarchy = None;
            assert!(engine.mutable_u16_backing(0, &absent).is_err());
            let mut cache_lost = state.clone();
            cache_lost.memory = absent.clone();
            assert!(
                engine
                    .mutable_hierarchy_route(&cache_lost, &call())
                    .is_err()
            );
            assert!(
                engine
                    .mutable_hierarchy_call(&mut cache_lost, call())
                    .is_err()
            );
            let mut wrong = result.memory.clone();
            wrong.mutable_hierarchy = Some(usize::MAX);
            assert!(engine.mutable_hierarchy_namespace(&wrong).is_err());
            let clone = result.memory.clone();
            assert_eq!(clone.storage_slots(), result.memory.storage_slots());
            assert_eq!(clone.mutable_hierarchy, Some(0));
            let mut grown = clone.clone();
            grown.push(Some(Value::Unit));
            assert_eq!(grown.storage_slots(), clone.storage_slots() + 1);
            let mut reopened = h.clone();
            let old_epoch = reopened.epoch;
            let old_issued = reopened.issued;
            let tip = Tip {
                frame: 0,
                statement: 1,
                local: 1,
            };
            reopened
                .issue(0, tip, result.memory.storage_slots())
                .unwrap();
            assert!(reopened.epoch > old_epoch && reopened.issued > old_issued);
            assert!(!reopened.role_valid(&symbolic::MutableU16Role::Root, true));
            assert!(reopened.role_valid(&symbolic::MutableU16Role::Root, false));
            assert!(!reopened.role_valid(
                &symbolic::MutableU16Role::HierarchyMetadata {
                    lease: 0,
                    epoch: old_epoch
                },
                false,
            ));
            assert!(backing.data.scalar().unwrap().belongs_to(&engine.terms));
            assert_eq!(
                backing.data.scalar().unwrap().sort(),
                before.scalar().unwrap().sort()
            );
        }
        assert!(
            observed_current_store,
            "normal Return must retain actual child Store data"
        );
        assert!(
            engine
                .proof
                .body_entries
                .iter()
                .any(|entry| entry.function.contains("scalar"))
        );
        assert!(
            engine
                .proof
                .body_entries
                .iter()
                .any(|entry| entry.function.contains("leaf"))
        );
    }

    pub(super) fn run<'tcx>(
        engine: &mut Engine<'tcx>,
        root: &Rc<Body<'tcx>>,
        outer: &Rc<Body<'tcx>>,
        leaf: &Rc<Body<'tcx>>,
        base: &State,
    ) {
        assert!(!TEST_ISSUANCE.with(std::cell::Cell::get));
        let root_frame = engine.mutable_u16_register_frame(root).unwrap();
        let outer_frame = engine.mutable_u16_register_frame(outer).unwrap();
        let leaf_frame = engine.mutable_u16_register_frame(leaf).unwrap();
        let statement = outer
            .basic_blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find(|s| {
                matches!(&s.kind, StatementKind::Assign(a)
                if matches!(a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, _)))
            })
            .unwrap();
        let StatementKind::Assign(assignment) = &statement.kind else {
            unreachable!()
        };
        let Rvalue::Ref(_, _, source) = &assignment.1 else {
            unreachable!()
        };
        let mut state = State {
            flow: activation_flow::Flow::Unarmed,
            locals: vec![None; outer.local_decls.len()],
            addresses: vec![None; outer.local_decls.len()],
            constant_receipts: constant_reference_receipts::Slots::default(),
            missing_places: Default::default(),
            conditions: base.conditions.clone(),
            memory: base.memory.clone(),
        };
        state.locals[source.local.as_usize()] = Some(Value::MutableU16 {
            id: 0,
            role: symbolic::MutableU16Role::Child { generation: 1 },
        });
        {
            let backing = &mut Rc::make_mut(&mut state.memory.mutable_u16)[0];
            backing.generation = 1;
            backing.phase = super::super::mutable_u16_children::Phase::Active {
                frames: vec![outer_frame],
            };
        }
        engine
            .mutable_hierarchy_source(outer, &state, assignment.0, &assignment.1, &statement.kind)
            .unwrap();
        let mut consumed = state.clone();
        consumed
            .missing_places
            .consume(source.local.as_usize(), Vec::new())
            .unwrap();
        assert!(
            engine
                .mutable_hierarchy_source(
                    outer,
                    &consumed,
                    assignment.0,
                    &assignment.1,
                    &statement.kind
                )
                .is_err()
        );
        let different = Rc::new((**outer).clone());
        assert!(
            engine
                .mutable_hierarchy_source(
                    &different,
                    &state,
                    assignment.0,
                    &assignment.1,
                    &statement.kind
                )
                .is_err()
        );
        let mut wrong_role = state.clone();
        wrong_role.locals[source.local.as_usize()] = Some(Value::MutableU16 {
            id: 0,
            role: symbolic::MutableU16Role::Root,
        });
        assert!(
            engine
                .mutable_hierarchy_source(
                    outer,
                    &wrong_role,
                    assignment.0,
                    &assignment.1,
                    &statement.kind
                )
                .is_err()
        );
        let mut hierarchy =
            Hierarchy::from_parent(&state.memory.mutable_u16[0], outer_frame).unwrap();
        let outer_ticket = Ticket {
            origin: hierarchy.origin.clone(),
            lease: 1,
            issued_floor: 1,
            epoch_floor: 0,
            prefix: Vec::new(),
            frame: outer_frame,
        };
        let old_parent_meta = hierarchy.metadata(1).unwrap();
        let first = Tip {
            frame: outer_frame,
            statement: &statement.kind as *const _ as usize,
            local: assignment.0.local.as_usize(),
        };
        let lease = hierarchy
            .issue(
                1,
                first.clone(),
                state.memory.storage_slots() + hierarchy.storage_slots(),
            )
            .unwrap();
        assert_eq!(lease, 2);
        assert!(hierarchy.access(1).is_err());
        hierarchy.lifetime(1).unwrap();
        let next_statement = outer
            .basic_blocks
            .iter()
            .flat_map(|b| &b.statements)
            .find(|s| {
                matches!(&s.kind, StatementKind::Assign(a)
                if matches!(&a.1, Rvalue::Ref(_, BorrowKind::Mut { .. }, place)
                    if place.local.as_usize() == first.local))
            })
            .unwrap();
        let StatementKind::Assign(next_assignment) = &next_statement.kind else {
            unreachable!()
        };
        let next = Tip {
            frame: outer_frame,
            statement: &next_statement.kind as *const _ as usize,
            local: next_assignment.0.local.as_usize(),
        };
        hierarchy
            .advance(&first, next.clone(), first.local)
            .unwrap();
        assert!(
            hierarchy
                .advance(&first, next.clone(), first.local)
                .is_err()
        );
        assert!(
            hierarchy
                .enter(
                    &first,
                    leaf_frame,
                    state.memory.storage_slots() + hierarchy.storage_slots()
                )
                .is_err()
        );
        let ticket = hierarchy
            .enter(
                &next,
                leaf_frame,
                state.memory.storage_slots() + hierarchy.storage_slots(),
            )
            .unwrap();
        let child_meta = hierarchy.metadata(2).unwrap();
        // Actual graph modes distinguish a suspended ancestor from current access.
        let mut graph = state.clone();
        graph.memory.mutable_hierarchy = Some(0);
        {
            let backing = &mut Rc::make_mut(&mut graph.memory.mutable_u16)[0];
            backing.phase = super::super::mutable_u16_children::Phase::Idle;
            backing.hierarchy = Some(hierarchy.clone());
        }
        engine.mutable_hierarchy_namespace(&graph.memory).unwrap();
        let ancestor = Value::MutableU16 {
            id: 0,
            role: symbolic::MutableU16Role::HierarchyChild { lease: 1 },
        };
        assert!(engine.validate_tracked_value(&ancestor, &graph).is_err());
        Engine::mutable_hierarchy_test_lifetime_graph(&ancestor, &graph).unwrap();
        let current = Value::MutableU16 {
            id: 0,
            role: symbolic::MutableU16Role::HierarchyChild { lease: 2 },
        };
        engine.validate_tracked_value(&current, &graph).unwrap();
        let mut revoked = graph.clone();
        Rc::make_mut(&mut revoked.memory.mutable_u16)[0]
            .hierarchy
            .as_mut()
            .unwrap()
            .release(&ticket)
            .unwrap();
        assert!(Engine::mutable_hierarchy_test_lifetime_graph(&current, &revoked).is_err());
        let mut absent = graph.clone();
        absent.memory.mutable_hierarchy = None;
        assert!(Engine::mutable_hierarchy_test_lifetime_graph(&ancestor, &absent).is_err());
        assert!(
            Engine::validate_reference_graph(&current, &graph, Some(1), &mut Vec::new()).is_err()
        );

        let mut rolled = hierarchy.clone();
        rolled.issued = ticket.issued_floor - 1;
        assert!(rolled.release(&ticket).is_err());
        let mut rolled = hierarchy.clone();
        rolled.epoch = ticket.epoch_floor - 1;
        assert!(rolled.release(&ticket).is_err());
        let mut wrong_origin = hierarchy.clone();
        wrong_origin.origin = Rc::new((*hierarchy.origin).clone());
        assert!(wrong_origin.release(&ticket).is_err());
        let mut wrong_prefix = hierarchy.clone();
        wrong_prefix.owners[0].frames = vec![root_frame];
        assert!(wrong_prefix.release(&ticket).is_err());
        let mut early = hierarchy.clone();
        early.owners.last_mut().unwrap().frames.push(outer_frame);
        assert!(early.release(&ticket).is_err());
        hierarchy.current(engine, &state).unwrap();
        Rc::make_mut(&mut state.memory.mutable_u16)[0].hierarchy = Some(hierarchy.clone());
        let slots = state.memory.storage_slots();
        assert!(slots >= hierarchy.storage_slots());
        assert!(engine.mutable_u16_backing(0, &state.memory).is_err());
        assert!(!super::super::mutable_u16_children::role_live(
            &state.memory.mutable_u16[0],
            &symbolic::MutableU16Role::Child { generation: 2 }
        ));
        assert!(
            engine
                .validate_tracked_value(
                    state.locals[source.local.as_usize()].as_ref().unwrap(),
                    &state
                )
                .is_err()
        );
        hierarchy.release(&ticket).unwrap();
        hierarchy.access(1).unwrap();
        assert!(hierarchy.lifetime(2).is_err());
        assert!(hierarchy.observe(old_parent_meta).is_err());
        assert!(hierarchy.observe(child_meta).is_err());
        let second = hierarchy.issue(1, first.clone(), slots).unwrap();
        assert_eq!(second, 3);
        let second_ticket = hierarchy.enter(&first, leaf_frame, slots).unwrap();
        hierarchy.release(&second_ticket).unwrap();
        hierarchy.release(&outer_ticket).unwrap();
        assert!(hierarchy.owners.is_empty());
        assert_eq!(hierarchy.issued, 3);
        hierarchy.access(0).unwrap();
        let dormant_meta = hierarchy.metadata(0).unwrap();
        let dormant_epoch = hierarchy.epoch;
        Rc::make_mut(&mut state.memory.mutable_u16)[0].hierarchy = Some(hierarchy.clone());
        let dormant_slots = state.memory.storage_slots();
        assert_eq!(hierarchy.storage_slots(), 6);
        let mut branch = state.memory.clone();
        let h = Rc::make_mut(&mut branch.mutable_u16)[0]
            .hierarchy
            .as_mut()
            .unwrap();
        let next_root_tip = Tip {
            frame: root_frame,
            statement: first.statement,
            local: first.local,
        };
        assert_eq!(h.issue(0, next_root_tip.clone(), dormant_slots).unwrap(), 4);
        let next_ticket = h
            .enter(&next_root_tip, outer_frame, dormant_slots + 5)
            .unwrap();
        h.release(&next_ticket).unwrap();
        assert!(h.observe(dormant_meta).is_err());
        assert_eq!(
            state.memory.mutable_u16[0]
                .hierarchy
                .as_ref()
                .unwrap()
                .epoch,
            dormant_epoch
        );
        assert_eq!(
            state.memory.mutable_u16[0]
                .hierarchy
                .as_ref()
                .unwrap()
                .issued,
            3
        );
        assert_eq!(branch.mutable_u16[0].hierarchy.as_ref().unwrap().issued, 4);
        assert!(matches!(
            hierarchy.issue(0, first.clone(), MAX_INPUT_VALUES),
            Err(TransitionError::Resource(_))
        ));
        let mut exhausted = hierarchy.clone();
        exhausted.issued = u64::MAX;
        assert!(matches!(
            exhausted.issue(0, first.clone(), 0),
            Err(TransitionError::Resource(_))
        ));

        assert_eq!(hierarchy.issued, 3);
        let held = Rc::new((**leaf).clone());
        let expired_id = engine.mutable_u16_register_frame(&held).unwrap();
        drop(held);
        let mut expired = hierarchy.clone();
        expired.owners.push(Owner {
            lease: 3,
            parent: 0,
            frames: vec![expired_id],
        });
        assert!(expired.current(engine, &state).is_err());
        assert!(
            consumed
                .missing_places
                .check(source.local.as_usize(), &[])
                .is_err()
        );
        // No producer or graph validation above clears the original parent source mask.
    }
}
