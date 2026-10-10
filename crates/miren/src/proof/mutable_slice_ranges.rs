//! Checked mutable ranges retain the original allocation and projection chain.
use super::*;
use rustc_span::Symbol;
use symbolic::MemoryProjection;

impl<'tcx> Engine<'tcx> {
    pub(super) fn mutable_slice_range(
        &mut self,
        instance: ty::Instance<'tcx>,
        raw_values: &[Value],
        state: &State,
        site: (DefId, Span),
    ) -> Result<Option<Vec<Return>>, String> {
        let callee = instance.def_id();
        let parent = self.tcx.parent(callee);
        if self.tcx.item_name(callee) != Symbol::intern("index_mut")
            || !matches!(self.tcx.def_kind(parent), DefKind::Impl { of_trait: true })
        {
            return Ok(None);
        }
        let Some(slice_index) = self.tcx.get_diagnostic_item(Symbol::intern("SliceIndex")) else {
            return Ok(None);
        };
        if callee.krate != slice_index.krate
            || self
                .tcx
                .impl_trait_ref(parent)
                .instantiate(self.tcx, instance.args)
                .skip_norm_wip()
                .def_id
                != slice_index
        {
            return Ok(None);
        }
        let signature = self.call_signature(instance)?;
        if signature.abi() != rustc_abi::ExternAbi::Rust
            || signature.c_variadic()
            || signature.safety() != rustc_hir::Safety::Safe
        {
            return Ok(None);
        }
        let [range, receiver] = signature.inputs() else {
            return Ok(None);
        };
        let ty::Adt(def, args) = range.kind() else {
            return Ok(None);
        };
        if self.tcx.lang_items().get(LangItem::Range) != Some(def.did())
            || args.type_at(0) != self.tcx.types.usize
        {
            return Ok(None);
        }
        let ty::Ref(_, slice, mutability) = receiver.kind() else {
            return Ok(None);
        };
        let ty::Slice(element) = slice.kind() else {
            return Ok(None);
        };
        let byte_slice = *element == self.tcx.types.u8;
        if (!byte_slice && !Self::finite_range_element_type(*element, 0))
            || !mutability.is_mut()
            || !matches!(signature.output().kind(), ty::Ref(_, output, mutability)
                if *output == *slice && mutability.is_mut())
        {
            return Ok(None);
        }
        let domain = if byte_slice { "byte" } else { "finite element" };
        let [
            range,
            reference @ Value::Reference {
                allocation,
                projection,
                mutable: true,
            },
        ] = raw_values
        else {
            return Err(format!(
                "mutable {domain} range requires retained writable slice provenance"
            ));
        };
        self.validate_tracked_value(reference, state)?;
        let range = range.clone().materialize()?;
        if !matches!(&range, Value::Adt { name, variant: 0, fields, .. }
            if *name == self.tcx.def_path_str(def.did()) && fields.len() == 2)
        {
            return Err(format!(
                "mutable {domain} range requires exact compiler Range storage"
            ));
        }
        let start = range.field("start")?;
        let end = range.field("end")?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for bound in [&start, &end] {
            let (_, width, signed) = bound.integer()?;
            if width != bits || signed {
                return Err(format!("{domain} range bounds must be target usize"));
            }
        }
        let storage = self
            .reference_value(reference, &state.memory, &state.conditions)?
            .materialize()?;
        let capacity = if let Value::Bytes { length, .. } = storage {
            if !byte_slice {
                return Err("finite mutable range requires typed element storage".into());
            }
            *length
        } else if let Value::Elements(elements) = storage {
            if byte_slice
                || !elements
                    .iter()
                    .all(|value| self.finite_range_element_matches(*element, value, 0))
            {
                return Err("finite mutable range requires integer or tuple elements".into());
            }
            symbolic::integer(&self.terms, elements.len() as u128, bits, false)
        } else {
            return Err("mutable range backing is not retained finite storage".into());
        };
        let ordered = symbolic::binary(&self.terms, "le", start.clone(), end.clone())?.boolean()?;
        let inside = symbolic::binary(&self.terms, "le", end.clone(), capacity)?.boolean()?;
        let safe = self.terms.apply(Op::And, &[ordered, inside])?;
        self.require(
            site.0,
            site.1,
            &state.conditions,
            &safe,
            ObligationKind::PanicSafety,
            format!("mutable {domain} range requires start <= end <= slice length"),
        )?;
        let mut conditions = state.conditions.clone();
        conditions.push(safe);
        let length = symbolic::binary(&self.terms, "sub", end, start.clone())?;
        let mut projection = projection.clone();
        projection.push(MemoryProjection::Slice {
            offset: Box::new(start),
            length: Box::new(length),
        });
        let value = Value::Reference {
            allocation: *allocation,
            projection,
            mutable: true,
        };
        self.record_model(
            callee,
            if byte_slice {
                "checked mutable byte range; retained allocation and nested projections, \
                no raw fat-pointer or static storage grant"
            } else {
                "checked mutable finite element range; retained allocation and projections"
            },
        );
        Ok(Some(vec![Return {
            value,
            conditions,
            memory: state.memory.clone(),
        }]))
    }

    fn finite_range_element_type(element: Ty<'tcx>, depth: usize) -> bool {
        if depth >= 16 {
            return false;
        }
        if matches!(element.kind(), ty::Int(_) | ty::Uint(_)) {
            return true;
        }
        if let ty::Tuple(fields) = element.kind() {
            return !fields.is_empty()
                && fields
                    .iter()
                    .all(|field| Self::finite_range_element_type(field, depth + 1));
        }
        false
    }

    fn finite_range_element_matches(&self, element: Ty<'tcx>, value: &Value, depth: usize) -> bool {
        if depth >= 16 {
            return false;
        }
        if let Some((bits, signed)) = self.integer_type(element) {
            if let Value::Int {
                expression,
                bits: width,
                signed: sign,
            } = value
            {
                return bits == *width
                    && signed == *sign
                    && expression.sort() == &symbolic::Sort::BitVec(bits)
                    && expression.belongs_to(&self.terms);
            }
            return false;
        }
        if let ty::Tuple(types) = element.kind()
            && let Value::Tuple(fields) = value
        {
            return types.len() == fields.len()
                && !fields.is_empty()
                && types
                    .iter()
                    .zip(fields)
                    .all(|(ty, value)| self.finite_range_element_matches(ty, value, depth + 1));
        }
        false
    }

    pub(super) fn finite_range_element_value(value: &Value) -> bool {
        if let Value::Int { .. } = value {
            return true;
        }
        if let Value::Tuple(fields) = value {
            return !fields.is_empty() && fields.iter().all(Self::finite_range_element_value);
        }
        false
    }

    pub(super) fn finite_element_region(
        &self,
        storage: &Value,
        offset: &Value,
        length: &Value,
        conditions: &[Term],
    ) -> Result<bool, String> {
        let Value::Elements(elements) = storage.clone().materialize()? else {
            return Ok(false);
        };
        if !elements.iter().all(Self::finite_range_element_value) {
            return Ok(false);
        }
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for bound in [offset, length] {
            let (_, width, signed) = bound.integer()?;
            if width != bits || signed {
                return Err("finite element region requires target usize bounds".into());
            }
        }
        let capacity = symbolic::integer(&self.terms, elements.len() as u128, bits, false);
        let valid_offset =
            symbolic::binary(&self.terms, "le", offset.clone(), capacity.clone())?.boolean()?;
        let available = symbolic::binary(&self.terms, "sub", capacity, offset.clone())?;
        let valid_length =
            symbolic::binary(&self.terms, "le", length.clone(), available)?.boolean()?;
        let safe = self.terms.apply(Op::And, &[valid_offset, valid_length])?;
        if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&safe)]].concat())? {
            return Err("finite element view lacks proven region bounds".into());
        }
        Ok(true)
    }

    pub(super) fn finite_element_slice_length(
        &self,
        reference: &Value,
        memory: &Memory,
        conditions: &[Term],
    ) -> Result<Option<Value>, String> {
        let Value::Reference {
            allocation,
            projection,
            mutable: true,
        } = reference
        else {
            return Ok(None);
        };
        let Some((MemoryProjection::Slice { offset, length }, parent)) = projection.split_last()
        else {
            return Ok(None);
        };
        let parent = Value::Reference {
            allocation: *allocation,
            projection: parent.to_vec(),
            mutable: true,
        };
        let storage = self.reference_value(&parent, memory, conditions)?;
        if self.finite_element_region(&storage, offset, length, conditions)? {
            return Ok(Some((**length).clone()));
        }
        Ok(None)
    }
}
