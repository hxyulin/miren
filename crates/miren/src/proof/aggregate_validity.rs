//! Exact aggregate metadata and scalar validity correlation with compiler field layouts.
use super::{Context, Sort, Term, Value, symbolic};
use rustc_abi::BackendRepr;

pub(super) fn scalar_fields_match(
    representation: BackendRepr,
    fields: &[(u64, BackendRepr)],
) -> bool {
    match representation {
        BackendRepr::Scalar(scalar) => matches!(fields,
                [(0, BackendRepr::Scalar(field))] if *field == scalar),
        BackendRepr::ScalarPair {
            a: first,
            b: second,
            b_offset,
        } => match fields {
            [
                (
                    0,
                    BackendRepr::ScalarPair {
                        a,
                        b,
                        b_offset: offset,
                    },
                ),
            ] => *a == first && *b == second && *offset == b_offset,
            [
                (0, BackendRepr::Scalar(a)),
                (offset, BackendRepr::Scalar(b)),
            ] => *a == first && *b == second && *offset == b_offset.bytes(),
            _ => false,
        },
        BackendRepr::SimdVector { .. } | BackendRepr::SimdScalableVector { .. } => false,
        BackendRepr::Memory { .. } => true,
    }
}

pub(super) fn byte_array_payload_matches(
    context: &Context,
    pointer_bits: u32,
    count: u64,
    length: &Value,
    data: &Term,
) -> Result<bool, String> {
    let (length, bits, signed) = length.integer()?;
    Ok(bits == pointer_bits
        && !signed
        && length.belongs_to(context)
        && length.sort() == &Sort::BitVec(pointer_bits)
        && symbolic::constant(&length)
            == Some(symbolic::Constant::BitVec {
                value: u128::from(count),
                bits: pointer_bits,
            })
        && data.belongs_to(context)
        && data.sort()
            == &Sort::Array(
                Box::new(Sort::BitVec(pointer_bits)),
                Box::new(Sort::BitVec(8)),
            ))
}
