//! Exact original payloads for the private compiler-aligned zero-sized Box region.
use super::*;
use typed_array_choices::OwnedChoiceShape;

/// Issued only after the complete ordinary product and original zero-leaf checks.
pub(super) struct Certificate<'tcx> {
    original: Ty<'tcx>,
    layout: ZeroLayout,
}

/// Concrete arithmetic facts derived from the original compiler layout, never pointer rights.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ZeroLayout {
    alignment: u128,
    bits: u32,
}

impl ZeroLayout {
    pub(super) fn for_type<'tcx>(tcx: TyCtxt<'tcx>, original: Ty<'tcx>) -> Result<Self, String> {
        let layout = tcx
            .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(original))
            .map_err(|error| format!("owned Box payload layout is unavailable: {error:?}"))?;
        if layout.size.bytes() != 0 {
            return Err("owned nominal Box payload requires compiler size zero".into());
        }
        Self::new(
            u128::from(layout.align.abi.bytes()),
            u32::from(tcx.sess.target.pointer_width),
        )
    }

    fn new(alignment: u128, bits: u32) -> Result<Self, String> {
        if !matches!(bits, 32 | 64)
            || !alignment.is_power_of_two()
            || (1_u128 << (bits - 1)).checked_sub(alignment).is_none()
        {
            return Err("Box zero layout lacks exact target-valid compiler alignment".into());
        }
        Ok(Self { alignment, bits })
    }

    pub(super) fn alignment(self) -> u128 {
        self.alignment
    }

    pub(super) fn bits(self) -> u32 {
        self.bits
    }
}

impl<'tcx> Certificate<'tcx> {
    pub(super) fn new(original: Ty<'tcx>, layout: ZeroLayout) -> Self {
        Self { original, layout }
    }
    pub(super) fn original(&self) -> Ty<'tcx> {
        self.original
    }

    pub(super) fn layout(&self) -> ZeroLayout {
        self.layout
    }
}

pub(super) fn certify_nominal_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
) -> Result<usize, String> {
    if !matches!(original.kind(), ty::Adt(def, _) if def.is_struct() && def.did().is_local()) {
        return Err("owned Box payload requires an exact local nominal zero-sized struct".into());
    }
    ZeroLayout::for_type(tcx, original)?;
    let mut nodes = 0;
    original_children(tcx, original, 0, &mut nodes)?;
    Ok(nodes)
}

fn original_children<'tcx>(
    tcx: TyCtxt<'tcx>,
    original: Ty<'tcx>,
    depth: usize,
    nodes: &mut usize,
) -> Result<(), String> {
    if depth >= 16 || *nodes >= 512 {
        return Err("owned nominal Box payload exceeds its original type budget".into());
    }
    *nodes += 1;
    let env = ty::TypingEnv::fully_monomorphized();
    if !original.is_freeze(tcx, env)
        || !tcx.type_is_copy_modulo_regions(env, original)
        || original.needs_drop(tcx, env)
    {
        return Err("owned nominal Box payload requires Copy, Freeze and no drop glue".into());
    }
    match original.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) => Ok(()),
        ty::Float(ty::FloatTy::F32 | ty::FloatTy::F64) => Ok(()),
        ty::Tuple(fields) => {
            for field in fields.iter() {
                original_children(tcx, field, depth + 1, nodes)?;
            }
            Ok(())
        }
        ty::Array(child, count) => {
            let count = count
                .try_to_target_usize(tcx)
                .ok_or("owned nominal Box array lacks an original concrete length")?;
            if count > 128 {
                return Err("owned nominal Box array exceeds its original type budget".into());
            }
            for _ in 0..count.max(1) {
                original_children(tcx, *child, depth + 1, nodes)?;
            }
            Ok(())
        }
        ty::Adt(def, args) if def.is_struct() && def.did().is_local() && !def.repr().packed() => {
            for field in &def.non_enum_variant().fields {
                original_children(tcx, field.ty(tcx, args).skip_norm_wip(), depth + 1, nodes)?;
            }
            Ok(())
        }
        _ => Err("owned nominal Box payload contains an unsupported original child type".into()),
    }
}

fn closed_shape(shape: &OwnedChoiceShape) -> bool {
    match shape {
        OwnedChoiceShape::Primitive(_) => false,
        OwnedChoiceShape::ByteArray(count) => *count == 0,
        OwnedChoiceShape::Tuple(fields) | OwnedChoiceShape::Array(fields) => {
            fields.iter().all(closed_shape)
        }
        OwnedChoiceShape::Struct { fields, .. } => {
            fields.iter().all(|(_, field)| closed_shape(field))
        }
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn nominal_box_shape(
        &self,
        original: Ty<'tcx>,
    ) -> Result<(OwnedChoiceShape, usize), String> {
        let nodes = certify_nominal_type(self.tcx, original).map_err(|reason| {
            let category = if reason.contains("budget") {
                UnknownCategory::ResourceLimit
            } else {
                UnknownCategory::Semantics
            };
            self.categorized_error(category, reason)
        })?;
        let shape = self
            .owned_product_shape(original)?
            .ok_or("owned nominal Box requires a complete original pure product certificate")?;
        if !closed_shape(&shape) {
            return Err("owned nominal Box payload has observable scalar leaves".into());
        }
        Ok((shape, nodes))
    }

    pub(super) fn certify_owned_box_protocol(
        &self,
        instance: ty::Instance<'tcx>,
        original: Ty<'tcx>,
    ) -> Result<(), String> {
        if original == self.tcx.types.unit {
            return owned_box_templates::certify_unit_protocol(self.tcx, instance);
        }
        if original.needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized()) {
            let certificate = owned_box_effect_free_drop::certify_type(self.tcx, original)
                .map_err(|reason| self.effect_free_drop_error(reason))?;
            return owned_box_templates::certify_effect_free_protocol(self, instance, &certificate)
                .map_err(|reason| self.effect_free_drop_error(reason));
        }
        self.nominal_box_shape(original)?;
        let certificate = Certificate {
            original,
            layout: ZeroLayout::for_type(self.tcx, original)?,
        };
        owned_box_templates::certify_nominal_protocol(self.tcx, instance, &certificate)
    }

    pub(super) fn box_payload_value(
        &self,
        entry: &owned_boxes::BoxType<'tcx>,
        value: &Value,
    ) -> Result<Value, String> {
        if entry.payload == self.tcx.types.unit {
            if matches!(value, Value::Unit)
                || matches!(value, Value::Tuple(fields) if fields.is_empty())
            {
                return Ok(Value::Unit);
            }
            return Err("Box constructor payload differs from initialized Unit".into());
        }
        if entry
            .payload
            .needs_drop(self.tcx, ty::TypingEnv::fully_monomorphized())
        {
            let certificate = owned_box_effect_free_drop::certify_type(self.tcx, entry.payload)
                .map_err(|reason| self.effect_free_drop_error(reason))?;
            return owned_box_effect_free_drop::validate_value(self.tcx, &certificate, value)
                .map_err(|reason| self.effect_free_drop_error(reason));
        }
        let shape = entry
            .shape
            .as_ref()
            .ok_or("nominal Box payload lacks its immutable original product shape")?;
        let prepared = self.prepare_typed_product(entry.payload, shape, value, 0)?;
        self.validate_owned_product(entry.payload, &prepared, &[])?;
        Ok(prepared)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_layout_uses_exact_target_alignment_and_checked_rounding() {
        for bits in [32, 64] {
            for exponent in 0..bits {
                let alignment = 1_u128 << exponent;
                let layout = ZeroLayout::new(alignment, bits).unwrap();
                assert_eq!(layout.alignment(), alignment);
                assert_eq!(layout.bits(), bits);
            }
            for alignment in [0, 3, (1_u128 << bits)] {
                assert!(ZeroLayout::new(alignment, bits).is_err());
            }
        }
        for bits in [0, 16, 128] {
            assert!(ZeroLayout::new(1, bits).is_err());
        }
    }

    #[test]
    fn exact_nominal_box_payload_and_complete_glue_refuse_mutations() {
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
                let mut engine = Engine::new(
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

                let mut checked = 0;
                for local in tcx.mir_keys(()).iter().copied() {
                    if !matches!(tcx.def_kind(local), rustc_hir::def::DefKind::Fn) {
                        continue;
                    }
                    let symbol = tcx.item_name(local.to_def_id());
                    let name = symbol.as_str();
                    if !matches!(
                        name,
                        "marker" | "nested" | "restricted" | "aligned" | "large"
                    ) {
                        continue;
                    }
                    let payload = tcx
                        .fn_sig(local)
                        .instantiate_identity()
                        .skip_binder()
                        .inputs()[0];
                    if name == "restricted" {
                        assert!(engine.nominal_box_shape(payload).is_err());
                        continue;
                    }
                    let (shape, _) = engine.nominal_box_shape(payload).unwrap();
                    let certificate = Certificate {
                        original: payload,
                        layout: ZeroLayout::for_type(tcx, payload).unwrap(),
                    };
                    let owner = engine.original_box_type(payload).unwrap();
                    let constructor = tcx
                        .get_diagnostic_item(rustc_span::Symbol::intern("box_new"))
                        .unwrap();
                    let constructor = ty::Instance::try_resolve(
                        tcx,
                        ty::TypingEnv::fully_monomorphized(),
                        constructor,
                        tcx.mk_args(&[payload.into()]),
                    )
                    .unwrap()
                    .unwrap();
                    let constructor_body = constructor
                        .try_instantiate_mir_and_normalize_erasing_regions(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            ty::EarlyBinder::bind(tcx, tcx.instance_mir(constructor.def).clone()),
                        )
                        .unwrap();
                    let TerminatorKind::Call { args, .. } = &constructor_body.basic_blocks
                        [rustc_middle::mir::BasicBlock::from_usize(0)]
                    .terminator()
                    .kind
                    else {
                        unreachable!()
                    };
                    assert!(
                        owned_box_templates::compiler_zero_layout(
                            tcx,
                            &args[0].node,
                            certificate.layout,
                        )
                        .is_ok()
                    );
                    if matches!(name, "aligned" | "large") {
                        assert_eq!(
                            certificate.layout.alignment(),
                            if name == "aligned" { 8 } else { 4096 }
                        );
                        let changed = Certificate {
                            original: payload,
                            layout: ZeroLayout::for_type(tcx, tcx.types.unit).unwrap(),
                        };
                        assert!(
                            owned_box_templates::compiler_zero_layout(
                                tcx,
                                &args[0].node,
                                changed.layout,
                            )
                            .is_err()
                        );
                        let instance = ty::Instance::resolve_drop_glue(tcx, owner);
                        assert!(
                            owned_box_templates::certify_nominal_protocol(tcx, instance, &changed)
                                .is_err()
                        );
                    }
                    let instance = ty::Instance::resolve_drop_glue(tcx, owner);
                    let generic = tcx.instance_mir(instance.def);
                    let body = instance
                        .try_instantiate_mir_and_normalize_erasing_regions(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            ty::EarlyBinder::bind(tcx, generic.clone()),
                        )
                        .unwrap();
                    let check = |body: &Body<'tcx>| {
                        owned_box_glue::nominal_glue(tcx, instance, body, &certificate, owner)
                    };
                    assert!(check(&body).is_ok());
                    for index in 0..body.basic_blocks.len() {
                        let mut changed = body.clone();
                        changed.basic_blocks.as_mut()
                            [rustc_middle::mir::BasicBlock::from_usize(index)]
                        .is_cleanup = true;
                        assert!(check(&changed).is_err());
                    }
                    let mut changed = body.clone();
                    let block = &mut changed.basic_blocks.as_mut()
                        [rustc_middle::mir::BasicBlock::from_usize(0)];
                    let mut extra = block.statements[0].clone();
                    extra.kind = StatementKind::Nop;
                    block.statements.push(extra);
                    assert!(check(&changed).is_err());
                    let mut changed = body.clone();
                    changed.basic_blocks.as_mut()[rustc_middle::mir::BasicBlock::from_usize(1)]
                        .terminator_mut()
                        .kind = TerminatorKind::Unreachable;
                    assert!(check(&changed).is_err());
                    let mut changed = body.clone();
                    let TerminatorKind::Call { func, .. } = &mut changed.basic_blocks.as_mut()
                        [rustc_middle::mir::BasicBlock::from_usize(2)]
                    .terminator_mut()
                    .kind
                    else {
                        unreachable!()
                    };
                    *func = Operand::Copy(Place::from(rustc_middle::mir::Local::from_usize(2)));
                    assert!(check(&changed).is_err());
                    let mut changed = body.clone();
                    let StatementKind::Assign(assignment) = &mut changed.basic_blocks.as_mut()
                        [rustc_middle::mir::BasicBlock::from_usize(0)]
                    .statements[0]
                        .kind
                    else {
                        unreachable!()
                    };
                    let Rvalue::Cast(_, _, target) = &mut assignment.1 else {
                        unreachable!()
                    };
                    *target = tcx.types.unit;
                    assert!(check(&changed).is_err());
                    let no_drop = ty::Instance::resolve_drop_glue(tcx, payload);
                    let generic = tcx.instance_mir(no_drop.def);
                    let mut body = no_drop
                        .try_instantiate_mir_and_normalize_erasing_regions(
                            tcx,
                            ty::TypingEnv::fully_monomorphized(),
                            ty::EarlyBinder::bind(tcx, generic.clone()),
                        )
                        .unwrap();
                    assert!(
                        owned_box_glue::nominal_glue(tcx, no_drop, &body, &certificate, owner,)
                            .is_ok()
                    );
                    body.basic_blocks.as_mut()[rustc_middle::mir::BasicBlock::from_usize(0)]
                        .is_cleanup = true;
                    assert!(
                        owned_box_glue::nominal_glue(tcx, no_drop, &body, &certificate, owner,)
                            .is_err()
                    );
                    let entry = owned_boxes::BoxType {
                        original: owner,
                        payload,
                        shape: Some(shape),
                        slots: 1,
                    };
                    assert!(engine.box_payload_value(&entry, &Value::Unit).is_err());
                    let ty::Adt(def, _) = payload.kind() else {
                        unreachable!()
                    };
                    let marker = tcx
                        .mir_keys(())
                        .iter()
                        .copied()
                        .find(|local| {
                            matches!(tcx.def_kind(*local), rustc_hir::def::DefKind::Fn)
                                && tcx.item_name(local.to_def_id()).as_str() == "marker"
                        })
                        .unwrap();
                    let marker_ty = tcx
                        .fn_sig(marker)
                        .instantiate_identity()
                        .skip_binder()
                        .inputs()[0];
                    let ty::Adt(marker_def, _) = marker_ty.kind() else {
                        unreachable!()
                    };
                    let marker_value = Value::Adt {
                        name: tcx.def_path_str(marker_def.did()),
                        variant: 0,
                        is_option: false,
                        discriminant: 0,
                        fields: Vec::new().into(),
                    };
                    let fields = if name == "nested" {
                        vec![
                            ("a".into(), marker_value.clone()),
                            ("b".into(), Value::Elements(Vec::new().into())),
                            ("c".into(), Value::Unit),
                        ]
                    } else {
                        Vec::new()
                    };
                    let value = Value::Adt {
                        name: tcx.def_path_str(def.did()),
                        variant: 0,
                        is_option: false,
                        discriminant: 0,
                        fields: fields.into(),
                    };
                    assert!(engine.box_payload_value(&entry, &value).is_ok());
                    let mut changed = value.clone();
                    let Value::Adt { name, .. } = &mut changed else {
                        unreachable!()
                    };
                    *name = "other::Marker".into();
                    assert!(engine.box_payload_value(&entry, &changed).is_err());
                    let mut changed = value.clone();
                    let Value::Adt { fields, .. } = &mut changed else {
                        unreachable!()
                    };
                    fields.push(("extra".into(), Value::Unit));
                    assert!(engine.box_payload_value(&entry, &changed).is_err());
                    if let Value::Adt { fields, .. } = &value
                        && !fields.is_empty()
                    {
                        let mut changed = value.clone();
                        let Value::Adt { fields, .. } = &mut changed else {
                            unreachable!()
                        };
                        fields.swap(0, 1);
                        assert!(engine.box_payload_value(&entry, &changed).is_err());
                    }
                    let index = engine.owned_box_types.len();
                    engine.owned_box_types.push(entry);
                    let owner_value = Value::OwnedRegion {
                        key: 17,
                        certificate: index,
                        kind: symbolic::OwnedRegionKind::Owner,
                    };
                    let mut memory = Memory::default();
                    memory.issue_owned_region(17, index).unwrap();
                    memory.initialize_owned_region(17, index, value).unwrap();
                    memory.seal_owned_region(17, index).unwrap();
                    assert!(engine.validate_owned_region(&owner_value, &memory).is_ok());
                    assert!(
                        engine
                            .owned_box_type_value(
                                engine.unit_box_type().unwrap(),
                                &owner_value,
                                &memory,
                            )
                            .is_err()
                    );
                    let mut malformed = Memory::default();
                    malformed.issue_owned_region(17, index).unwrap();
                    malformed
                        .initialize_owned_region(17, index, Value::Unit)
                        .unwrap();
                    malformed.seal_owned_region(17, index).unwrap();
                    assert!(
                        engine
                            .validate_owned_region(&owner_value, &malformed)
                            .is_err()
                    );

                    checked += 1;
                }
                assert_eq!(checked, 4);
                self.checked = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory = std::env::temp_dir()
            .join(format!("miren-nominal-box-metadata-{}", std::process::id(),));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("probe.rs");
        std::fs::write(
            &source,
            concat!(
                "#![no_std]\nextern crate alloc;\n#[derive(Clone,Copy)]pub struct Marker;\n",
                "#[derive(Clone,Copy)]pub struct Nested{pub a:Marker,pub b:[Marker;0],pub c:()}\n",
                "#[derive(Clone,Copy)]pub struct Restricted{pub a:[&'static u16;0]}\n",
                "pub fn marker(_:Marker){} pub fn nested(_:Nested){}\n",
                "pub fn restricted(_:Restricted){}\n",
                "#[repr(align(8))]#[derive(Clone,Copy)]pub struct Aligned;\n",
                "#[repr(align(4096))]#[derive(Clone,Copy)]pub struct Large;\n",
                "pub fn aligned(_:Aligned){} pub fn large(_:Large){}\n",
            ),
        )
        .unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        for target in [None, Some("thumbv7em-none-eabihf")] {
            for optimized in [false, true] {
                let mut arguments = vec![
                    "rustc".into(),
                    source.to_str().unwrap().into(),
                    "--crate-type=lib".into(),
                    "--edition=2024".into(),
                    "-Zmir-opt-level=0".into(),
                    "-Cpanic=abort".into(),
                    "--out-dir".into(),
                    directory.to_str().unwrap().into(),
                    "--sysroot".into(),
                    String::from_utf8(sysroot.stdout.clone())
                        .unwrap()
                        .trim()
                        .into(),
                ];
                if let Some(target) = target {
                    arguments.extend(["--target".into(), target.into()]);
                }
                if optimized {
                    arguments.push("-Copt-level=2".into());
                }
                let mut check = Check { checked: false };
                rustc_driver::run_compiler(&arguments, &mut check);
                assert!(check.checked);
            }
        }
        std::fs::remove_dir_all(directory).unwrap();
    }
}
