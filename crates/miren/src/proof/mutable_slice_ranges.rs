//! Checked mutable byte ranges retain the original allocation and projection chain.
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
        if signature.abi() != rustc_abi::ExternAbi::Rust || signature.c_variadic() {
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
        let byte_slice = Ty::new_slice(self.tcx, self.tcx.types.u8);
        if *slice != byte_slice
            || !mutability.is_mut()
            || !matches!(signature.output().kind(), ty::Ref(_, output, mutability)
                if *output == byte_slice && mutability.is_mut())
        {
            return Ok(None);
        }
        let [
            range,
            reference @ Value::Reference {
                allocation,
                projection,
                mutable: true,
            },
        ] = raw_values
        else {
            return Err("mutable byte range requires retained writable slice provenance".into());
        };
        self.validate_tracked_value(reference, state)?;
        let range = range.clone().materialize()?;
        if !matches!(&range, Value::Adt { name, variant: 0, fields, .. }
            if *name == self.tcx.def_path_str(def.did()) && fields.len() == 2)
        {
            return Err("mutable byte range requires exact compiler Range storage".into());
        }
        let start = range.field("start")?;
        let end = range.field("end")?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for bound in [&start, &end] {
            let (_, width, signed) = bound.integer()?;
            if width != bits || signed {
                return Err("byte range bounds must be target usize".into());
            }
        }
        let Value::Bytes {
            length: capacity, ..
        } = self
            .reference_value(reference, &state.memory, &state.conditions)?
            .materialize()?
        else {
            return Err("mutable byte range backing is not retained byte storage".into());
        };
        let ordered = symbolic::binary(&self.terms, "le", start.clone(), end.clone())?.boolean()?;
        let inside = symbolic::binary(&self.terms, "le", end.clone(), *capacity)?.boolean()?;
        let safe = self.terms.apply(Op::And, &[ordered, inside])?;
        self.require(
            site.0,
            site.1,
            &state.conditions,
            &safe,
            ObligationKind::PanicSafety,
            "mutable byte range requires start <= end <= slice length".into(),
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
            "checked mutable byte range; retained allocation and nested \
            projections, no raw fat-pointer or static storage grant",
        );
        Ok(Some(vec![Return {
            value,
            conditions,
            memory: state.memory.clone(),
        }]))
    }
}
