//! Exact aggregate scalar validity correlation with actual compiler field layouts.
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
