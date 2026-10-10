//! Narrow Cortex-M interrupt-register instructions, without interrupt exclusion guarantees.

use super::*;
use rustc_ast::{InlineAsmOptions, InlineAsmTemplatePiece};
use rustc_middle::mir::{BasicBlock, InlineAsmMacro, InlineAsmOperand, UnwindAction};
use rustc_target::asm::{ArmInlineAsmRegClass, InlineAsmRegClass, InlineAsmRegOrRegClass};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Instruction {
    Read,
    Write,
    Disable,
    Enable,
}

fn instruction(template: &[InlineAsmTemplatePiece]) -> Option<Instruction> {
    match template {
        [InlineAsmTemplatePiece::String(text)] if text == "cpsid i" => Some(Instruction::Disable),
        [InlineAsmTemplatePiece::String(text)] if text == "cpsie i" => Some(Instruction::Enable),
        [
            InlineAsmTemplatePiece::String(prefix),
            InlineAsmTemplatePiece::Placeholder {
                operand_idx: 0,
                modifier: None,
                ..
            },
            InlineAsmTemplatePiece::String(suffix),
        ] if prefix == "mrs " && suffix == ", PRIMASK" => Some(Instruction::Read),
        [
            InlineAsmTemplatePiece::String(prefix),
            InlineAsmTemplatePiece::Placeholder {
                operand_idx: 0,
                modifier: None,
                ..
            },
        ] if prefix == "msr PRIMASK, " => Some(Instruction::Write),
        _ => None,
    }
}

fn unsupported_template(template: &[InlineAsmTemplatePiece]) -> String {
    match template {
        [InlineAsmTemplatePiece::String(text)]
            if text == "sev" || text == "wfe" || text == "wfi" =>
        {
            format!(
                "unsupported Cortex-M instruction `{text}`; \
                 hardware event/wait semantics are unmodeled"
            )
        }
        _ => "unsupported Cortex-M interrupt-register assembly template".to_owned(),
    }
}

fn general_register(reg: InlineAsmRegOrRegClass) -> bool {
    matches!(
        reg,
        InlineAsmRegOrRegClass::RegClass(InlineAsmRegClass::Arm(ArmInlineAsmRegClass::reg))
    )
}

fn supported_target(arch: &rustc_target::spec::Arch, width: u16, llvm: &str) -> bool {
    *arch == rustc_target::spec::Arch::Arm
        && width == 32
        && matches!(
            llvm,
            "thumbv6m-none-eabi"
                | "thumbv7m-none-eabi"
                | "thumbv7em-none-eabi"
                | "thumbv7em-none-eabihf"
        )
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn arm_interrupt_asm(
        &mut self,
        id: DefId,
        body: &Body<'tcx>,
        state: &mut State,
        terminator: &TerminatorKind<'tcx>,
    ) -> Result<BasicBlock, String> {
        let TerminatorKind::InlineAsm {
            asm_macro,
            template,
            operands,
            options,
            targets,
            unwind,
            ..
        } = terminator
        else {
            return Err("interrupt-register model requires compiler inline assembly".into());
        };
        let target = &self.tcx.sess.target;
        if !supported_target(&target.arch, target.pointer_width, &target.llvm_target) {
            return Err("interrupt-register assembly requires a supported Cortex-M target".into());
        }
        let operation = instruction(template).ok_or_else(|| {
            let category = match &template[..] {
                [InlineAsmTemplatePiece::String(text)]
                    if text == "sev" || text == "wfe" || text == "wfi" =>
                {
                    UnknownCategory::ExternalEnvironment
                }
                _ => UnknownCategory::Semantics,
            };
            self.categorized_error(category, unsupported_template(template))
        })?;
        let required =
            InlineAsmOptions::NOMEM | InlineAsmOptions::NOSTACK | InlineAsmOptions::PRESERVES_FLAGS;
        let [destination] = targets.as_ref() else {
            return Err("interrupt-register assembly requires one fallthrough edge".into());
        };
        if *asm_macro != InlineAsmMacro::Asm
            || *options != required
            || !matches!(unwind, UnwindAction::Unreachable)
        {
            return Err("interrupt-register assembly options or unwind shape unsupported".into());
        }
        match operation {
            Instruction::Read => {
                let [
                    InlineAsmOperand::Out {
                        reg,
                        late: false,
                        place: Some(place),
                    },
                ] = operands.as_ref()
                else {
                    return Err("PRIMASK read requires one ordinary output operand".into());
                };
                if !general_register(*reg)
                    || place.ty(&body.local_decls, self.tcx).ty != self.tcx.types.u32
                {
                    return Err(
                        "PRIMASK read requires a compiler u32 general-register output".into(),
                    );
                }
                // Upper reserved bits stay unconstrained; no startup privilege or stable CPU state
                // is assumed. Repeated reads intentionally need not agree.
                let expression = self.fresh_abstraction(
                    Sort::BitVec(32),
                    "Cortex-M PRIMASK read without startup or stable interrupt-state history",
                );
                self.write(
                    state,
                    *place,
                    Value::Int {
                        expression,
                        bits: 32,
                        signed: false,
                    },
                )?;
            }
            Instruction::Write => {
                let [InlineAsmOperand::In { reg, value }] = operands.as_ref() else {
                    return Err("PRIMASK write requires one input operand".into());
                };
                if !general_register(*reg)
                    || value.ty(&body.local_decls, self.tcx) != self.tcx.types.u32
                {
                    return Err(
                        "PRIMASK write requires a compiler u32 general-register input".into(),
                    );
                }
                let value = self.evaluate_operand(id, body, state, value)?;
                if !matches!(
                    value,
                    Value::Int {
                        bits: 32,
                        signed: false,
                        ..
                    }
                ) {
                    return Err("PRIMASK write input has no u32 symbolic encoding".into());
                }
                let mut memory = state.memory.clone();
                if !self.isolated_startup {
                    Self::invalidate_published_atomics(state, &mut memory)?;
                }
                state.memory = memory;
            }
            Instruction::Disable | Instruction::Enable => {
                if !operands.is_empty() {
                    return Err("interrupt mask instruction requires no operands".into());
                }
                // Interrupt mask writes do not establish an exclusion or restore startup facts.
                let mut memory = state.memory.clone();
                if !self.isolated_startup {
                    Self::invalidate_published_atomics(state, &mut memory)?;
                }
                state.memory = memory;
            }
        }
        let model = "Cortex-M PRIMASK assembly".to_owned();
        if !self.proof.models.contains(&model) {
            self.proof.models.push(model);
        }
        Ok(*destination)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_span::DUMMY_SP;

    fn text(value: &'static str) -> InlineAsmTemplatePiece {
        InlineAsmTemplatePiece::String(value.into())
    }

    fn placeholder(index: usize, modifier: Option<char>) -> InlineAsmTemplatePiece {
        InlineAsmTemplatePiece::Placeholder {
            operand_idx: index,
            modifier,
            span: DUMMY_SP,
        }
    }

    #[test]
    fn target_selection_excludes_application_profile_and_non_arm_architectures() {
        use rustc_target::spec::Arch;
        for llvm in [
            "thumbv6m-none-eabi",
            "thumbv7m-none-eabi",
            "thumbv7em-none-eabi",
            "thumbv7em-none-eabihf",
        ] {
            assert!(supported_target(&Arch::Arm, 32, llvm));
            assert!(!supported_target(&Arch::AArch64, 32, llvm));
            assert!(!supported_target(&Arch::Arm, 64, llvm));
        }
        for llvm in [
            "thumbv7a-none-eabi",
            "armv7-unknown-linux-gnueabihf",
            "thumbv8m.main-none-eabi",
            "aarch64-unknown-linux-gnu",
        ] {
            assert!(!supported_target(&Arch::Arm, 32, llvm));
        }
    }

    #[test]
    fn exact_templates_reject_other_registers_instructions_and_operands() {
        assert_eq!(instruction(&[text("cpsid i")]), Some(Instruction::Disable));
        assert_eq!(instruction(&[text("cpsie i")]), Some(Instruction::Enable));
        assert_eq!(
            instruction(&[text("mrs "), placeholder(0, None), text(", PRIMASK")]),
            Some(Instruction::Read)
        );
        assert_eq!(
            instruction(&[text("msr PRIMASK, "), placeholder(0, None)]),
            Some(Instruction::Write)
        );
        for template in [
            vec![text("mrs "), placeholder(0, None), text(", BASEPRI")],
            vec![text("mrs "), placeholder(1, None), text(", PRIMASK")],
            vec![text("mrs "), placeholder(0, Some('r')), text(", PRIMASK")],
            vec![
                text("mrs "),
                placeholder(0, None),
                text(", PRIMASK\ncpsid i"),
            ],
            vec![text("cpsid f")],
            vec![text("cpsie f")],
            vec![text("nop")],
            vec![text("msr CONTROL, "), placeholder(0, None)],
        ] {
            assert_eq!(instruction(&template), None, "{template:?}");
        }
    }
}
