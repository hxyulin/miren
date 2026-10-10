use super::*;
use initialized_places::Step;
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{Local, Location};

fn footprint(place: Place<'_>) -> Vec<Step> {
    place
        .projection
        .iter()
        .map_while(|part| match part {
            ProjectionElem::Field(index, _) => Some(Step::Field(index.as_usize())),
            ProjectionElem::Downcast(_, variant) => Some(Step::Variant(variant.as_usize())),
            _ => None,
        })
        .collect()
}

struct Observation<'a> {
    owner: usize,
    missing: &'a [Step],
    observed: bool,
}

impl<'tcx> Visitor<'tcx> for Observation<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if place.local.as_usize() == self.owner {
            let path = footprint(*place);
            if path.len() != place.projection.len()
                || path.starts_with(self.missing)
                || self.missing.starts_with(&path)
            {
                self.observed = true;
            }
        }
        // Projection indices are independent local operands; a sibling path can still use them.
        self.visit_projection(place.as_ref(), context, location);
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
        if local.as_usize() == self.owner && !matches!(context, PlaceContext::NonUse(_)) {
            self.observed = true;
        }
    }
}

/// Omits only a private Horn temporary, never a real allocation or observable initialized value.
pub(super) fn unobserved_until_assignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    start: Location,
    owner: usize,
    missing: &[Step],
    budget: usize,
) -> Result<bool, String> {
    let mut pending = vec![start];
    let mut visited = BTreeSet::new();
    let mut work = 0;
    while let Some(location) = pending.pop() {
        if !visited.insert(location) {
            continue;
        }
        work += 1;
        if work > budget {
            return Err("inductive initialization-use scan exceeds the step budget".into());
        }
        let block = &body.basic_blocks[location.block];
        let mut observed = Observation {
            owner,
            missing,
            observed: false,
        };
        if let Some(statement) = block.statements.get(location.statement_index) {
            if let StatementKind::Assign(assignment) = &statement.kind {
                let tag_only = if let Rvalue::Discriminant(place) = &assignment.1 {
                    let path = footprint(*place);
                    place.local.as_usize() == owner
                        && path.len() == place.projection.len()
                        && initialized_places::compiler_field_footprint(tcx, body, *place).is_ok()
                        && matches!(place.ty(&body.local_decls, tcx).ty.kind(),
                            ty::Adt(definition, _) if definition.is_enum())
                        && missing.starts_with(&path)
                        && matches!(
                            &missing[path.len()..],
                            [Step::Variant(_), Step::Field(_), ..]
                        )
                } else {
                    false
                };
                if !tag_only {
                    observed.visit_rvalue(&assignment.1, location);
                }

                if observed.observed {
                    return Ok(false);
                }
                let destination = assignment.0;
                let path = footprint(destination);
                if destination.local.as_usize() == owner
                    && path.len() == destination.projection.len()
                    && missing.starts_with(&path)
                {
                    continue;
                }
                observed.visit_place(
                    &destination,
                    PlaceContext::MutatingUse(rustc_middle::mir::visit::MutatingUseContext::Store),
                    location,
                );
            } else {
                observed.visit_statement(statement, location);
            }
            if observed.observed {
                return Ok(false);
            }
            pending.push(Location {
                statement_index: location.statement_index + 1,
                ..location
            });
        } else {
            if let TerminatorKind::Drop { place, target, .. } = &block.terminator().kind
                && !place
                    .ty(&body.local_decls, tcx)
                    .ty
                    .needs_drop(tcx, ty::TypingEnv::fully_monomorphized())
            {
                pending.push(Location {
                    block: *target,
                    statement_index: 0,
                });
                continue;
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                unwind,
                ..
            } = &block.terminator().kind
            {
                observed.visit_operand(func, location);
                for argument in args {
                    observed.visit_operand(&argument.node, location);
                }
                if observed.observed {
                    return Ok(false);
                }
                let path = footprint(*destination);
                if destination.local.as_usize() == owner
                    && path.len() == destination.projection.len()
                    && missing.starts_with(&path)
                {
                    // Only a successful return performs this exact destination assignment.
                    if let rustc_middle::mir::UnwindAction::Cleanup(block) = unwind {
                        pending.push(Location {
                            block: *block,
                            statement_index: 0,
                        });
                    }
                    continue;
                }
            }
            observed.visit_terminator(block.terminator(), location);
            if observed.observed {
                return Ok(false);
            }
            pending.extend(block.terminator().successors().map(|block| Location {
                block,
                statement_index: 0,
            }));
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_mir_scan_keeps_overlapping_uses_and_checks_repairs_before_omission() {
        struct Check(bool);
        impl rustc_driver::Callbacks for Check {
            fn after_analysis<'tcx>(
                &mut self,
                _: &rustc_interface::interface::Compiler,
                tcx: TyCtxt<'tcx>,
            ) -> rustc_driver::Compilation {
                for (name, expected) in [
                    ("sibling", true),
                    ("same", false),
                    ("ancestor", false),
                    ("borrow_sibling", true),
                    ("repair", true),
                    ("rhs_repair", false),
                    ("loopback", false),
                    ("unknown_projection", true),
                    ("call_repair", true),
                    ("call_rhs_repair", false),
                ] {
                    let id = tcx
                        .mir_keys(())
                        .iter()
                        .copied()
                        .find(|id| {
                            tcx.def_kind(id.to_def_id()) == rustc_hir::def::DefKind::Fn
                                && tcx.item_name(id.to_def_id()).as_str() == name
                        })
                        .unwrap();
                    let body = tcx.optimized_mir(id);
                    let start = Location {
                        block: START_BLOCK,
                        statement_index: 0,
                    };
                    assert_eq!(
                        unobserved_until_assignment(tcx, body, start, 1, &[Step::Field(1)], 8192)
                            .unwrap(),
                        expected,
                        "{name}"
                    );
                    assert!(
                        unobserved_until_assignment(tcx, body, start, 1, &[Step::Field(1)], 0)
                            .is_err()
                    );
                    if name == "unknown_projection" {
                        let ty::Tuple(fields) = body.local_decls[Local::from_usize(1)].ty.kind()
                        else {
                            panic!("tuple owner")
                        };
                        let place = Place::from(Local::from_usize(1)).project_deeper(
                            &[
                                ProjectionElem::Field(
                                    rustc_abi::FieldIdx::from_usize(0),
                                    fields[0],
                                ),
                                ProjectionElem::Deref,
                            ],
                            tcx,
                        );
                        let mut observed = Observation {
                            owner: 1,
                            missing: &[Step::Field(1)],
                            observed: false,
                        };
                        observed.visit_place(
                            &place,
                            PlaceContext::NonMutatingUse(
                                rustc_middle::mir::visit::NonMutatingUseContext::Copy,
                            ),
                            start,
                        );
                        assert!(observed.observed);
                    }
                    if name == "same" {
                        let mut marker = body.clone();
                        marker.basic_blocks.as_mut()[START_BLOCK].statements.insert(
                            0,
                            rustc_middle::mir::Statement::new(
                                body.basic_blocks[START_BLOCK].terminator().source_info,
                                StatementKind::StorageDead(Local::from_usize(1)),
                            ),
                        );
                        assert!(
                            !unobserved_until_assignment(
                                tcx,
                                &marker,
                                start,
                                1,
                                &[Step::Field(1)],
                                8192
                            )
                            .unwrap()
                        );
                    }
                }
                let id = tcx
                    .mir_keys(())
                    .iter()
                    .copied()
                    .find(|id| tcx.item_name(id.to_def_id()).as_str() == "tag_owner")
                    .unwrap();
                let mut body = tcx.optimized_mir(id).clone();
                let ty::Tuple(fields) = body.local_decls[Local::from_usize(1)].ty.kind() else {
                    panic!("original tuple schema")
                };
                let enum_ty = fields[0];
                let start = Location {
                    block: START_BLOCK,
                    statement_index: 0,
                };
                let place = Place::from(Local::from_usize(1)).project_deeper(
                    &[ProjectionElem::Field(
                        rustc_abi::FieldIdx::from_usize(0),
                        enum_ty,
                    )],
                    tcx,
                );
                let source_info = body.basic_blocks[START_BLOCK].terminator().source_info;
                body.basic_blocks.as_mut()[START_BLOCK].statements =
                    vec![rustc_middle::mir::Statement::new(
                        source_info,
                        StatementKind::Assign(Box::new((
                            Place::from(rustc_middle::mir::RETURN_PLACE),
                            Rvalue::Discriminant(place),
                        ))),
                    )];
                body.basic_blocks.as_mut()[START_BLOCK]
                    .terminator_mut()
                    .kind = TerminatorKind::Return;
                let payload = [Step::Field(0), Step::Variant(1), Step::Field(0)];
                assert!(unobserved_until_assignment(tcx, &body, start, 1, &payload, 8192).unwrap());
                for whole in [&[][..], &[Step::Field(0)][..]] {
                    assert!(
                        !unobserved_until_assignment(tcx, &body, start, 1, whole, 8192).unwrap()
                    );
                }
                let forged = Place::from(Local::from_usize(1)).project_deeper(
                    &[ProjectionElem::Field(
                        rustc_abi::FieldIdx::from_usize(1),
                        enum_ty,
                    )],
                    tcx,
                );
                body.basic_blocks.as_mut()[START_BLOCK].statements[0].kind =
                    StatementKind::Assign(Box::new((
                        Place::from(rustc_middle::mir::RETURN_PLACE),
                        Rvalue::Discriminant(forged),
                    )));
                let forged_payload = [Step::Field(1), Step::Variant(1), Step::Field(0)];
                assert!(
                    !unobserved_until_assignment(tcx, &body, start, 1, &forged_payload, 8192)
                        .unwrap()
                );
                self.0 = true;
                rustc_driver::Compilation::Stop
            }
        }
        let directory =
            std::env::temp_dir().join(format!("miren-initialization-scan-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let source = directory.join("probe.rs");
        std::fs::write(
            &source,
            "#![no_std]\n\
            pub fn tag_owner(_value:(Option<u16>,()))->isize{0}\n\
            pub fn sibling(pair:(u16,u16))->u16{pair.0}\n\
            pub fn same(pair:(u16,u16))->u16{pair.1}\n\
            pub fn ancestor(pair:(u16,u16))->u16{let borrow=&pair;borrow.0}\n\
            pub fn borrow_sibling(pair:(u16,u16))->u16{let borrow=&pair.0;*borrow}\n\
            pub fn repair(mut pair:(u16,u16))->u16{pair.1=7;pair.1}\n\
            pub fn rhs_repair(mut pair:(u16,u16))->u16{pair.1=pair.1 ^ 1;pair.1}\n\
            pub fn loopback(pair:(u16,u16),flag:bool)->u16{loop{if flag{return pair.1;}}}\n\
            pub fn unknown_projection(pair:(&u16,u16))->u16{*pair.0}\n\
            #[inline(never)]fn seven()->u16{7}\n\
            #[inline(never)]fn identity(value:u16)->u16{value}\n\
            pub fn call_repair(mut pair:(u16,u16))->u16{pair.1=seven();pair.1}\n\
            pub fn call_rhs_repair(mut pair:(u16,u16))->u16{pair.1=identity(pair.1);pair.1}\n",
        )
        .unwrap();
        let sysroot = std::process::Command::new("rustc")
            .args(["--print", "sysroot"])
            .output()
            .unwrap();
        assert!(sysroot.status.success());
        let mut check = Check(false);
        rustc_driver::run_compiler(
            &[
                "rustc".into(),
                source.to_str().unwrap().into(),
                "--crate-type=lib".into(),
                "--edition=2024".into(),
                "-Cpanic=abort".into(),
                "--out-dir".into(),
                directory.to_str().unwrap().into(),
                "--sysroot".into(),
                String::from_utf8(sysroot.stdout).unwrap().trim().into(),
            ],
            &mut check,
        );
        assert!(check.0);
        std::fs::remove_dir_all(directory).unwrap();
    }
}
