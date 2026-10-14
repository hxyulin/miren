//! Source inventory for a paid mutable niche codec design. Inventory grants no storage rights.
use super::*;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{Location, PlaceElem, PlaceRef};

#[derive(Default)]
struct Forms {
    assignments: usize,
    discriminants: usize,
    downcasts: usize,
}

impl<'tcx> Visitor<'tcx> for Forms {
    fn visit_statement(
        &mut self,
        statement: &rustc_middle::mir::Statement<'tcx>,
        location: Location,
    ) {
        match &statement.kind {
            StatementKind::Assign(_) => self.assignments += 1,
            StatementKind::SetDiscriminant { .. } => self.discriminants += 1,
            _ => {}
        }
        self.super_statement(statement, location);
    }

    fn visit_projection_elem(
        &mut self,
        _: PlaceRef<'tcx>,
        element: PlaceElem<'tcx>,
        _: rustc_middle::mir::visit::PlaceContext,
        _: Location,
    ) {
        if matches!(element, ProjectionElem::Downcast(..)) {
            self.downcasts += 1;
        }
    }
}

#[test]
fn actual_mutable_niche_source_inventory_remains_unsupported() {
    struct Check(bool);
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let engine = super::super::nonzero_niches::test_engine(tcx);
            let pointer = u32::from(tcx.sess.target.pointer_width);
            let mut checked = 0;
            for id in tcx.hir_body_owners() {
                if tcx.def_kind(id.to_def_id()) != DefKind::Fn {
                    continue;
                }
                let name = tcx.item_name(id.to_def_id()).to_string();
                let Some((family, primitive)) = name.split_once('_') else {
                    continue;
                };
                if !matches!(family, "option" | "empty" | "payload") {
                    continue;
                }
                let (bits, signed) = match primitive {
                    "u8" => (8, false),
                    "u16" => (16, false),
                    "u32" => (32, false),
                    "u64" => (64, false),
                    "u128" => (128, false),
                    "usize" => (pointer, false),
                    "i8" => (8, true),
                    "i16" => (16, true),
                    "i32" => (32, true),
                    "i64" => (64, true),
                    "i128" => (128, true),
                    "isize" => (pointer, true),
                    _ => panic!("unexpected source domain"),
                };
                let instance = ty::Instance::mono(tcx, id.to_def_id());
                let signature = tcx.fn_sig(id).instantiate_identity();
                let ty::Ref(_, slice, mutable) = signature.skip_binder().inputs()[0].kind() else {
                    panic!("original mutable reference");
                };
                assert!(mutable.is_mut());
                let ty::Slice(product) = slice.kind() else {
                    panic!("original slice")
                };
                let ty::Tuple(fields) = product.kind() else {
                    panic!("original tuple")
                };
                assert_eq!(fields.len(), 2);
                let original = fields[0];
                let schema = engine
                    .nonzero_niche_shape(original, 0, &mut 0)
                    .unwrap()
                    .unwrap();
                assert_eq!(schema.payload_bits(), bits);
                assert_eq!(schema.payload_signed(), signed);
                assert_eq!(schema.item_bytes(), u64::from(bits / 8));
                let layout = engine.static_layout(original).unwrap();
                let rustc_abi::Variants::Multiple {
                    tag_encoding:
                        rustc_abi::TagEncoding::Niche {
                            untagged_variant, ..
                        },
                    ..
                } = &layout.variants
                else {
                    panic!("actual zero-only niche layout")
                };
                assert_eq!(
                    untagged_variant.as_usize(),
                    usize::from(family != "payload")
                );
                eprintln!("MUTABLE_NICHE_SCHEMA name={name} schema={schema:#?} layout={layout:#?}");
                assert!(engine.mutable_product_shape(*product).unwrap().is_none());
                let current = engine.instantiated_body(instance).unwrap();
                let original_body = tcx.instance_mir(instance.def);
                let mut forms = Forms::default();
                forms.visit_body(&current);
                assert!(forms.assignments > 0);
                eprintln!(
                    "MUTABLE_NICHE_SOURCE name={name} width={bits} signed={signed} \
                     assignments={} set_discriminant={} downcasts={} target={} opt={:?}",
                    forms.assignments,
                    forms.discriminants,
                    forms.downcasts,
                    tcx.sess.target.llvm_target,
                    tcx.sess.opts.optimize,
                );
                eprintln!(
                    concat!(
                        "MUTABLE_NICHE_ORIGINAL name={name} ",
                        "signature={signature:?} body={original_body:#?}"
                    ),
                    name = name,
                    signature = signature,
                    original_body = original_body,
                );
                eprintln!("MUTABLE_NICHE_CURRENT name={name} body={current:#?}");
                checked += 1;
            }
            assert_eq!(checked, 36);
            self.0 = true;
            rustc_driver::Compilation::Stop
        }
    }
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/mutable_product_niche_source.rs");
    for target in [None, Some("thumbv7em-none-eabihf")] {
        for level in [0, 2] {
            let mut check = Check(false);
            let mut args = vec![
                "miren-mutable-niche-source".into(),
                fixture.display().to_string(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Zmir-opt-level=0".into(),
                "-Cpanic=abort".into(),
                "-Coverflow-checks=yes".into(),
                format!("-Copt-level={level}"),
                "-o".into(),
                "/dev/null".into(),
            ];
            if let Some(target) = target {
                args.extend(["--target".into(), target.into()]);
            }
            rustc_driver::run_compiler(&args, &mut check);
            assert!(check.0);
        }
    }
}
