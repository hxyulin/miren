//! Transactional finite replacement under the separately certified copy/source/origin premises.
use super::*;
use rustc_middle::mir::BasicBlock;

impl<'tcx> Engine<'tcx> {
    pub(super) fn finite_byte_copy_candidate(
        &self,
        instance: ty::Instance<'tcx>,
        raw_values: &[Value],
        state: &State,
    ) -> bool {
        let Some(core) = self.tcx.lang_items().sized_trait().map(|id| id.krate) else {
            return false;
        };
        if instance.def_id().krate != core
            || !matches!(instance.def, ty::InstanceKind::Item(_))
            || !matches!(
                self.tcx.def_kind(instance.def_id()),
                DefKind::Fn | DefKind::AssocFn
            )
            || self.tcx.item_name(instance.def_id()).as_str() != "copy_from_slice"
        {
            return false;
        }
        let [
            Value::Reference {
                allocation,
                projection,
                mutable: true,
            },
            _,
        ] = raw_values
        else {
            return false;
        };
        let Some(Some(Value::Bytes { length, .. })) = state.memory.get(*allocation) else {
            return false;
        };
        !projection.is_empty()
            && length
                .integer()
                .is_ok_and(|(term, _, _)| symbolic::constant(&term).is_none())
    }

    pub(super) fn finite_byte_copy(
        &mut self,
        id: DefId,
        body: &Body<'tcx>,
        block: BasicBlock,
        raw_destination: &Value,
        sources: (&Value, &Value),
        state: &mut State,
    ) -> Result<Value, String> {
        self.finite_byte_copy_transaction(id, body, block, raw_destination, sources, state)
            .map_err(|reason| {
                if self.unknown_causes.borrow().contains_key(&reason) {
                    reason
                } else {
                    self.categorized_error(UnknownCategory::Semantics, reason)
                }
            })
    }

    fn finite_byte_copy_transaction(
        &mut self,
        id: DefId,
        body: &Body<'tcx>,
        block: BasicBlock,
        raw_destination: &Value,
        sources: (&Value, &Value),
        state: &mut State,
    ) -> Result<Value, String> {
        let (raw_source, source) = sources;
        let Value::Reference { projection, .. } = raw_destination else {
            return Err("finite byte copy needs an evaluated tracked destination".into());
        };
        if projection.len() > 16 {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "finite byte copy view exceeds the existing 16-depth budget".into(),
            ));
        }
        let terminator = body.basic_blocks[block].terminator();
        let TerminatorKind::Call {
            func,
            args,
            target: Some(_),
            ..
        } = &terminator.kind
        else {
            return Err("finite byte copy needs its exact current Call occurrence".into());
        };
        if args.len() != 2
            || !matches!(args[0].node.ty(&body.local_decls, self.tcx).kind(),
                ty::Ref(_, target, rustc_hir::Mutability::Mut)
                    if matches!(target.kind(), ty::Slice(element) if *element == self.tcx.types.u8))
        {
            return Err(
                "finite byte copy destination lacks original mutable byte slice type".into(),
            );
        }
        let ty::FnDef(callee, generic) = func.ty(&body.local_decls, self.tcx).kind() else {
            return Err("finite byte copy requires a direct original selected Item".into());
        };
        let instance = self.resolve_function_item(*callee, generic.skip_binder())?;
        let origin = byte_copy_origins::source_origin(self.tcx, body, block, &args[1].node)
            .map_err(|error| self.categorized_error(error.category, error.reason))?;
        let count = match &origin {
            byte_copy_origins::SourceOrigin::Constant(bytes) => bytes.len(),
            byte_copy_origins::SourceOrigin::LocalArray { count, .. } => *count as usize,
        };
        super::byte_copy_templates::certify(self.tcx, instance, count as u128)
            .map_err(|error| self.categorized_error(error.category, error.reason))?;
        let work = count
            .checked_mul(2)
            .and_then(|nodes| nodes.checked_add(projection.len()));
        if work.is_none_or(|nodes| nodes > 512) {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "finite byte copy replacement/view work exceeds the 512-node budget".into(),
            ));
        }
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let Value::Bytes {
            length: source_length,
            data: source_data,
        } = source
        else {
            return Err("finite byte copy source has a different evaluated carrier".into());
        };
        match &origin {
            byte_copy_origins::SourceOrigin::Constant(bytes) => {
                let mut expected = self.terms.apply(
                    Op::ConstArray { index_bits: bits },
                    &[self.terms.bit_vector(0, 8)?],
                )?;
                for (index, byte) in bytes.iter().enumerate() {
                    expected = self.terms.apply(
                        Op::Store,
                        &[
                            expected,
                            self.terms.bit_vector(index as u128, bits)?,
                            self.terms.bit_vector(u128::from(*byte), 8)?,
                        ],
                    )?;
                }
                let (source_count, source_bits, source_signed) = source_length.integer()?;
                if source_signed
                    || source_bits != bits
                    || source_data != &expected
                    || symbolic::constant(&source_count)
                        != Some(symbolic::Constant::BitVec {
                            value: bytes.len() as u128,
                            bits,
                        })
                {
                    return Err(
                        "finite byte copy evaluated source differs from its original constant"
                            .into(),
                    );
                }
            }
            byte_copy_origins::SourceOrigin::LocalArray { .. } => {
                self.byte_copy_local_source(
                    body,
                    &origin,
                    raw_source,
                    source,
                    raw_destination,
                    state,
                )?;
            }
        }
        let (allocation, mut current) =
            self.byte_copy_current_destination(raw_destination, state)?;
        let Value::Reference { projection, .. } = raw_destination else {
            return Err("finite byte copy destination carrier changed".into());
        };
        let mut view = current.clone();
        let mut absolute = self.terms.bit_vector(0, bits)?;
        for step in projection {
            let symbolic::MemoryProjection::Slice { offset, .. } = step else {
                return Err("finite byte copy destination has a non-slice path".into());
            };
            // Existing view validation proves each nested offset and length fit the current
            // parent. With the issued isize::MAX extent this also excludes additive wrap.
            view = self.memory_projection(view, step, &state.conditions)?;
            let (offset, width, signed) = offset.integer()?;
            if signed || width != bits {
                return Err("finite byte copy destination offset has a different codec".into());
            }
            absolute = self.terms.apply(Op::BvAdd, &[absolute, offset])?;
        }
        let Value::Bytes {
            length: destination_length,
            ..
        } = view
        else {
            return Err("finite byte copy destination view is not original byte storage".into());
        };
        let equal = symbolic::binary(
            &self.terms,
            "eq",
            (*destination_length).clone(),
            (**source_length).clone(),
        )?
        .boolean()?;
        self.record_model(
            *callee,
            match origin {
                byte_copy_origins::SourceOrigin::Constant(_) => {
                    "certified core byte copy; fixed immutable source and current incoming view"
                }
                byte_copy_origins::SourceOrigin::LocalArray { .. } => {
                    "certified core byte copy; initialized local array and current incoming view"
                }
            },
        );
        self.require(
            id,
            terminator.source_info.span,
            &state.conditions,
            &equal,
            ObligationKind::PanicSafety,
            "byte copy requires equal lengths".into(),
        )?;
        state.conditions.push(equal);
        let Value::Bytes { data, .. } = &mut current else {
            return Err("finite byte copy current owner changed during preflight".into());
        };
        let mut updated = data.clone();
        for index in 0..count {
            let cell = self.terms.bit_vector(index as u128, bits)?;
            let target = self
                .terms
                .apply(Op::BvAdd, &[absolute.clone(), cell.clone()])?;
            let byte = self.terms.apply(Op::Select, &[source_data.clone(), cell])?;
            updated = self.terms.apply(Op::Store, &[updated, target, byte])?;
        }
        *data = updated;
        // Whole-root initialization was checked above. The single commit preserves every
        // allocation/mask/provenance record and the original symbolic capacity.
        state.memory[allocation] = Some(current);
        Ok(Value::Unit)
    }
}
