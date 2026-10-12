//! Original same-block immutable byte source provenance and exact local-array borrow origins.
use super::byte_copy_templates::CertificateError;
use super::*;
use rustc_middle::mir::{BasicBlock, ConstOperand, Local};

pub(super) enum SourceOrigin {
    Constant(Vec<u8>),
    LocalArray { local: Local, count: u64 },
}

fn immutable_bytes<'tcx>(tcx: TyCtxt<'tcx>, original: Ty<'tcx>) -> Option<Option<u64>> {
    let ty::Ref(_, pointee, rustc_hir::Mutability::Not) = original.kind() else {
        return None;
    };
    match pointee.kind() {
        ty::Array(element, count) if *element == tcx.types.u8 => {
            count.try_to_target_usize(tcx).map(Some)
        }
        ty::Slice(element) if *element == tcx.types.u8 => Some(None),
        _ => None,
    }
}

fn constant_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &ConstOperand<'tcx>,
) -> Result<Vec<u8>, CertificateError> {
    use rustc_abi::Size;
    use rustc_middle::mir::interpret::{GlobalAlloc, alloc_range};
    let original = immutable_bytes(tcx, operand.const_.ty())
        .ok_or("byte copy source constant has a different original type")?;
    if original.is_some_and(|count| count > 128) {
        return Err(CertificateError::resource(
            "byte copy source exceeds the fixed replacement budget",
        ));
    }
    let value = operand
        .const_
        .eval(tcx, ty::TypingEnv::fully_monomorphized(), operand.span)
        .map_err(|_| "byte copy source constant is unavailable")?;
    let (id, offset, count) = match (original, value) {
        (
            Some(count),
            rustc_middle::mir::ConstValue::Scalar(rustc_middle::mir::interpret::Scalar::Ptr(
                pointer,
                _,
            )),
        ) => {
            let (provenance, offset) = pointer.prov_and_relative_offset();
            if !provenance.immutable() || !provenance.shared_ref() {
                return Err("byte copy source lacks immutable shared compiler provenance".into());
            }
            (provenance.alloc_id(), offset, count)
        }
        (None, rustc_middle::mir::ConstValue::Slice { alloc_id, meta }) => {
            (alloc_id, Size::ZERO, meta)
        }
        _ => return Err("byte copy source constant has unsupported pointer storage".into()),
    };
    if count > 128 {
        return Err(CertificateError::resource(
            "byte copy source exceeds the fixed replacement budget",
        ));
    }
    let Some(GlobalAlloc::Memory(allocation)) = tcx.try_get_global_alloc(id) else {
        return Err("byte copy source lacks actual immutable compiler memory".into());
    };
    let allocation = allocation.inner();
    let end = offset
        .bytes()
        .checked_add(count)
        .ok_or("byte source extent overflow")?;
    let range = alloc_range(offset, Size::from_bytes(count));
    if allocation.mutability.is_mut()
        || end > allocation.len() as u64
        || !allocation.provenance().range_empty(range, &tcx)
    {
        return Err("byte copy source has mutable, indirect or invalid backing".into());
    }
    allocation
        .get_bytes_strip_provenance(&tcx, range)
        .map(|bytes| bytes.to_vec())
        .map_err(|_| "byte copy source contains unavailable or uninitialized bytes".into())
}

#[cfg(test)]
pub(super) fn original_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    block: BasicBlock,
    source: &Operand<'tcx>,
) -> Result<Vec<u8>, CertificateError> {
    match source_origin(tcx, body, block, source)? {
        SourceOrigin::Constant(bytes) => Ok(bytes),
        SourceOrigin::LocalArray { .. } => {
            Err("byte copy source has uncertified transport or effects".into())
        }
    }
}

pub(super) fn source_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    block: BasicBlock,
    source: &Operand<'tcx>,
) -> Result<SourceOrigin, CertificateError> {
    let statements = &body.basic_blocks[block].statements;
    if statements.len() > 512 {
        return Err(CertificateError::resource(
            "byte copy source occurrence exceeds its original work budget",
        ));
    }
    let mut operand = source.clone();
    let mut before = statements.len();
    let mut work = 0;
    for _ in 0..16 {
        match &operand {
            Operand::Constant(value) => {
                return constant_bytes(tcx, value).map(SourceOrigin::Constant);
            }
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                let original = body.local_decls[place.local].ty;
                if immutable_bytes(tcx, original).is_none() {
                    return Err(
                        "byte copy source chain has a mutable or nonbyte original type".into(),
                    );
                }
                let mut found = None;
                for index in (0..before).rev() {
                    work += 1;
                    if work > 512 {
                        return Err(CertificateError::resource(
                            "byte copy source scan exceeds its original work budget",
                        ));
                    }
                    if let StatementKind::Assign(assignment) = &statements[index].kind
                        && assignment.0.local == place.local
                    {
                        found = Some((index, assignment));
                        break;
                    }
                }
                let (index, assignment) =
                    found.ok_or("byte source crosses ambiguous CFG origin")?;
                if !assignment.0.projection.is_empty() {
                    return Err("byte source has an overlapping projected definition".into());
                }
                before = index;
                operand = match &assignment.1 {
                    Rvalue::Use(value, _) if value.ty(&body.local_decls, tcx) == original => {
                        value.clone()
                    }
                    Rvalue::Ref(_, BorrowKind::Shared, value) if value.projection.is_empty() => {
                        let ty::Array(element, count) = body.local_decls[value.local].ty.kind()
                        else {
                            return Err("byte copy shared source is not an original array".into());
                        };
                        let count = count
                            .try_to_target_usize(tcx)
                            .ok_or("byte copy shared source lacks a concrete extent")?;
                        if *element != tcx.types.u8
                            || immutable_bytes(tcx, original) != Some(Some(count))
                        {
                            return Err(
                                "byte copy shared source has a different original type".into()
                            );
                        }
                        if count > 128 {
                            return Err(CertificateError::resource(
                                "byte copy source exceeds the fixed replacement budget",
                            ));
                        }
                        return Ok(SourceOrigin::LocalArray {
                            local: value.local,
                            count,
                        });
                    }
                    Rvalue::Ref(_, BorrowKind::Shared, value)
                        if value.projection.as_ref() == [ProjectionElem::Deref]
                            && body.local_decls[value.local].ty == original =>
                    {
                        Operand::Copy(Place::from(value.local))
                    }
                    Rvalue::Cast(
                        CastKind::PointerCoercion(
                            rustc_middle::ty::adjustment::PointerCoercion::Unsize,
                            _,
                        ),
                        value,
                        target,
                    ) if *target == original
                        && immutable_bytes(tcx, original) == Some(None)
                        && immutable_bytes(tcx, value.ty(&body.local_decls, tcx))
                            .is_some_and(|count| count.is_some()) =>
                    {
                        value.clone()
                    }
                    _ => return Err("byte copy source has uncertified transport or effects".into()),
                };
            }
            _ => return Err("byte copy source has an unsupported original operand".into()),
        }
    }
    Err(CertificateError::resource(
        "byte copy source chain exceeds its original depth budget",
    ))
}
