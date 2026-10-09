use super::*;
use rustc_abi::FieldIdx;
use rustc_const_eval::const_eval::{CompileTimeInterpCx, mk_eval_cx_for_const_val};
use rustc_const_eval::interpret::{OpTy, Projectable};
use rustc_middle::mir::Const;
use std::collections::HashMap;

const MAX_CONSTANT_VALUES: usize = 2048;
const MAX_CONSTANT_ELEMENTS: u64 = 128;
const MAX_CONSTANT_SCALAR_ELEMENTS: u64 = 256;
const MAX_CONSTANT_DEPTH: usize = 16;

#[derive(Hash, PartialEq, Eq)]
enum ConstantStorageKey {
    Unit,
    Bool(Term),
    Int(Term, u32, bool),
    Float(Term, u32, Option<Term>),
    Address(Term, u32),
    Bytes(Term, Box<ConstantStorageKey>),
    Tuple(Vec<ConstantStorageKey>),
    Elements(Vec<ConstantStorageKey>),
    Adt(String, usize, bool, u128, Vec<(String, ConstantStorageKey)>),
}

#[derive(Default)]
struct ConstantStorage<'tcx> {
    values: usize,
    shared: HashMap<(Ty<'tcx>, ConstantStorageKey), Value>,
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn constant(
        &self,
        _id: DefId,
        constant: Const<'tcx>,
        span: Span,
    ) -> Result<Value, String> {
        let typing_env = ty::TypingEnv::fully_monomorphized();
        let value = constant.eval(self.tcx, typing_env, span).map_err(|error| {
            format!("unsupported MIR constant {constant:?} evaluation: {error:?}")
        })?;
        if let ty::Ref(_, element, mutability) = constant.ty().kind()
            && !mutability.is_mut()
            && let Some(value) = self.atomic_container(*element, 0)
        {
            return Ok(value);
        }
        if let Some(value) = self.atomic_shape(constant.ty()) {
            return Ok(value);
        }
        let (ecx, operand) =
            mk_eval_cx_for_const_val(self.tcx.at(span), typing_env, value, constant.ty())
                .ok_or("unsupported constant layout")?;
        self.constant_value(&ecx, &operand, 0, &mut ConstantStorage::default())
    }

    fn constant_value(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        operand: &OpTy<'tcx>,
        depth: usize,
        storage: &mut ConstantStorage<'tcx>,
    ) -> Result<Value, String> {
        if depth >= MAX_CONSTANT_DEPTH || storage.values >= MAX_CONSTANT_VALUES {
            return Err("unsupported constant shape exceeds depth or value budget".to_owned());
        }
        storage.values += 1;
        let value = self.decode_constant_value(ecx, operand, depth, storage)?;
        // Reuse only decoded initialized values with an exact type and lossless storage key.
        // Every occurrence is still evaluated and checked, so padding or an unsupported field
        // cannot be hidden by a previously successful constant with the same outer shape.
        if let Some(key) = constant_storage_key(&value) {
            let key = (operand.layout.ty, key);
            if let Some(existing) = storage.shared.get(&key) {
                return Ok(existing.clone());
            }
            storage.shared.insert(key, value.clone());
        }
        Ok(value)
    }

    fn decode_constant_value(
        &self,
        ecx: &CompileTimeInterpCx<'tcx>,
        operand: &OpTy<'tcx>,
        depth: usize,
        storage: &mut ConstantStorage<'tcx>,
    ) -> Result<Value, String> {
        let ty = match operand.layout.ty.kind() {
            ty::Pat(base, _) => *base,
            _ => operand.layout.ty,
        };
        if let Some(value) = self.atomic_shape(ty) {
            return Ok(value);
        }
        if matches!(ty.kind(), ty::Ref(_, _, mutability) if !mutability.is_mut()) {
            let pointee = ecx
                .deref_pointer(operand)
                .discard_err()
                .ok_or("unsupported constant reference")?;
            if !ecx.type_is_freeze(pointee.layout.ty) {
                return Err("unsupported constant reference to interior mutable storage".to_owned());
            }
            return self.constant_value(ecx, &pointee.into(), depth + 1, storage);
        }
        if self.thin_raw_pointer(ty) {
            let address = ecx
                .read_scalar(operand)
                .discard_err()
                .and_then(|scalar| scalar.to_bits(operand.layout.size).discard_err())
                .ok_or("pointer constant has unsupported allocation provenance")?;
            let bits = u32::from(self.tcx.sess.target.pointer_width);
            return Ok(Value::RawPointer {
                address: self.terms.bit_vector(address, bits)?,
                bits,
            });
        }
        if ty.is_bool() || self.float_type(ty).is_some() || self.integer_type(ty).is_some() {
            let scalar = ecx
                .read_scalar(operand)
                .discard_err()
                .ok_or("unsupported constant scalar read; memory may be uninitialized")?;
            if ty.is_bool() {
                return scalar
                    .to_bool()
                    .discard_err()
                    .map(|value| Value::Bool(self.terms.boolean(value)))
                    .ok_or_else(|| "unsupported constant boolean".to_owned());
            }
            let bits = scalar
                .to_bits(operand.layout.size)
                .discard_err()
                .ok_or("unsupported constant scalar bits")?;
            if let Some(width) = self.float_type(ty) {
                return Ok(symbolic::float(&self.terms, bits, width));
            }
            let (width, signed) = self.integer_type(ty).ok_or("unsupported constant type")?;
            return Ok(symbolic::integer(&self.terms, bits, width, signed));
        }
        match ty.kind() {
            ty::Closure(id, args) => {
                if !args.as_closure().upvar_tys().is_empty() {
                    return Err("unsupported constant closure with captures".to_owned());
                }
                if self.tcx.def_kind(*id) != DefKind::Closure
                    || operand.layout.fields.count() != 0
                    || operand.layout.size.bytes() != 0
                {
                    return Err("unsupported constant closure layout".to_owned());
                }
                Ok(Value::Adt {
                    name: self.tcx.def_path_str(*id),
                    variant: 0,
                    is_option: false,
                    discriminant: 0,
                    fields: Vec::new().into(),
                })
            }
            ty::Adt(def, _) if def.is_struct() || def.is_enum() => {
                let variant = ecx
                    .read_discriminant(operand)
                    .discard_err()
                    .ok_or("unsupported constant discriminant")?;
                let down = ecx
                    .project_downcast(operand, variant)
                    .discard_err()
                    .ok_or("unsupported constant variant projection")?;
                let fields = (0..def.variant(variant).fields.len())
                    .map(|index| {
                        let field = ecx
                            .project_field(&down, FieldIdx::from_usize(index))
                            .discard_err()
                            .ok_or("unsupported constant field projection")?;
                        self.constant_value(ecx, &field, depth + 1, storage)
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                self.constructed(ty, variant.as_usize(), fields)
            }
            ty::Tuple(fields) => {
                if fields.is_empty() {
                    return Ok(Value::Unit);
                }
                Ok(Value::Tuple(
                    (0..fields.len())
                        .map(|index| {
                            let field = ecx
                                .project_field(operand, FieldIdx::from_usize(index))
                                .discard_err()
                                .ok_or("unsupported constant tuple projection")?;
                            self.constant_value(ecx, &field, depth + 1, storage)
                        })
                        .collect::<Result<_, String>>()?,
                ))
            }
            ty::Array(element, _) | ty::Slice(element) => {
                let count = operand
                    .len(ecx)
                    .discard_err()
                    .ok_or("unsupported constant array length")?;
                let bytes = *element == self.tcx.types.u8;
                // Scalar tables use the existing lossless decoder and bounded scalar selection.
                // Composite arrays retain their lower fanout limit; total visits still count.
                let scalar = element.is_bool()
                    || self.integer_type(*element).is_some()
                    || self.float_type(*element).is_some();
                let limit = if scalar {
                    MAX_CONSTANT_SCALAR_ELEMENTS
                } else {
                    MAX_CONSTANT_ELEMENTS
                };
                if count > limit {
                    return Err("unsupported constant array exceeds element budget".to_owned());
                }
                let elements = (0..count)
                    .map(|index| {
                        let element = ecx
                            .project_index(operand, index)
                            .discard_err()
                            .ok_or("unsupported constant element projection")?;
                        self.constant_value(ecx, &element, depth + 1, storage)
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                if !bytes {
                    return Ok(Value::Elements(elements.into()));
                }
                let width = u32::from(self.tcx.sess.target.pointer_width);
                let mut data = self.terms.apply(
                    Op::ConstArray { index_bits: width },
                    &[self.terms.bit_vector(0, 8)?],
                )?;
                for (index, element) in elements.iter().enumerate() {
                    let (expression, _, _) = element.integer()?;
                    data = self.terms.apply(
                        Op::Store,
                        &[
                            data.clone(),
                            self.terms.bit_vector(index as u128, width)?,
                            expression.clone(),
                        ],
                    )?;
                }
                Ok(Value::Bytes {
                    length: Box::new(symbolic::integer(
                        &self.terms,
                        u128::from(count),
                        width,
                        false,
                    )),
                    data,
                })
            }
            _ => Err(format!("unsupported constant type {ty}")),
        }
    }
}

fn constant_storage_key(value: &Value) -> Option<ConstantStorageKey> {
    match value {
        Value::Unit => Some(ConstantStorageKey::Unit),
        Value::Bool(term) => Some(ConstantStorageKey::Bool(term.clone())),
        Value::Int {
            expression,
            bits,
            signed,
        } => Some(ConstantStorageKey::Int(expression.clone(), *bits, *signed)),
        Value::Float {
            expression,
            bits,
            raw_bits,
        } => Some(ConstantStorageKey::Float(
            expression.clone(),
            *bits,
            raw_bits.clone(),
        )),
        Value::RawPointer { address, bits } => {
            Some(ConstantStorageKey::Address(address.clone(), *bits))
        }
        Value::Bytes { length, data } => Some(ConstantStorageKey::Bytes(
            data.clone(),
            Box::new(constant_storage_key(length)?),
        )),
        Value::Tuple(fields) => Some(ConstantStorageKey::Tuple(
            fields
                .iter()
                .map(constant_storage_key)
                .collect::<Option<_>>()?,
        )),
        Value::Elements(fields) => Some(ConstantStorageKey::Elements(
            fields
                .iter()
                .map(constant_storage_key)
                .collect::<Option<_>>()?,
        )),
        Value::Adt {
            name,
            variant,
            is_option,
            discriminant,
            fields,
        } => {
            let fields = fields
                .iter()
                .map(|(name, value)| Some((name.clone(), constant_storage_key(value)?)))
                .collect::<Option<_>>()?;
            Some(ConstantStorageKey::Adt(
                name.clone(),
                *variant,
                *is_option,
                *discriminant,
                fields,
            ))
        }
        Value::Input(_)
        | Value::Enum { .. }
        | Value::Cell { .. }
        | Value::Atomic { .. }
        | Value::LocalAtomic { .. }
        | Value::RawSlice { .. }
        | Value::TrackedPointer { .. }
        | Value::Reference { .. }
        | Value::SliceIterator { .. }
        | Value::MetadataPointer(_)
        | Value::StaticText
        | Value::FormatArguments
        | Value::StaticSlice { .. }
        | Value::StaticView { .. }
        | Value::CompositeSlice { .. }
        | Value::ScalarSlice { .. }
        | Value::MaybeUninit { .. }
        | Value::Uninitialized
        | Value::TraitObject { .. }
        | Value::DebugReference { .. }
        | Value::FunctionPointer { .. }
        | Value::Function => None,
    }
}
