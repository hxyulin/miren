//! Typed incoming aggregate slice observations, without physical or mutable access rights.
use super::*;
use aggregate_validity::scalar_fields_match;
use rustc_abi::{BackendRepr, Primitive, Scalar, TagEncoding, Variants};
use rustc_middle::ty::AdtFlags;
use rustc_span::def_id::CrateNum;
use scalar_slices::{decode_scalar_element, scalar_slice_sort};
use symbolic::ScalarSliceElement;

const MAX_SHAPE_NODES: usize = 512;
const MAX_SHAPE_DEPTH: usize = 16;
const MAX_TYPE_ARRAY: u64 = 128;

fn slice_extent_limit(pointer_bits: u32, stride: u64) -> Result<u128, String> {
    if !(1..=128).contains(&pointer_bits) {
        return Err("slice extent requires a valid target pointer width".into());
    }
    let unsigned_max = u128::MAX >> (128 - pointer_bits);
    Ok(if stride == 0 {
        unsigned_max
    } else {
        (unsigned_max >> 1) / u128::from(stride)
    })
}

#[derive(Clone, Debug)]
pub(super) enum CompositeShape {
    Primitive(ScalarSliceElement),
    Tuple(Vec<CompositeShape>),
    Array(Vec<CompositeShape>),
    Struct {
        name: String,
        fields: Vec<(String, CompositeShape)>,
    },
    NonZeroNiche(Box<nonzero_niches::Schema>),
    Sum {
        name: String,
        bits: u32,
        signed: bool,
        is_option: bool,
        variants: Vec<CompositeVariant>,
    },
}

#[derive(Clone, Debug)]
pub(super) struct CompositeVariant {
    name: String,
    discriminant: u128,
    fields: Vec<(String, CompositeShape)>,
}

#[derive(Clone, Debug)]
pub(super) struct CompositeType<'tcx> {
    pub(super) ty: Ty<'tcx>,
    pub(super) shape: CompositeShape,
    pub(super) leaves: Vec<ScalarSliceElement>,
    pub(super) bytes: u64,
}

fn ordinary_struct_flags(flags: AdtFlags) -> bool {
    // Accept only ordinary structural flags. Unknown future compiler-special flags fail
    // conservatively, and tuple/fieldless constructors do not imply a value invariant.
    flags == AdtFlags::IS_STRUCT || flags == (AdtFlags::IS_STRUCT | AdtFlags::HAS_CTOR)
}

fn local_sum_payload_struct_policy(is_local: bool, flags: AdtFlags) -> bool {
    is_local && ordinary_struct_flags(flags)
}

fn ordinary_external_struct_policy(
    defining_crate: CrateNum,
    core_crate: Option<CrateNum>,
    flags: AdtFlags,
) -> bool {
    core_crate.is_some_and(|core| defining_crate != core && ordinary_struct_flags(flags))
}

#[derive(Clone, Copy)]
enum ShapePolicy {
    Products,
    ReadonlySums,
    CertifiedNiches,
}

impl ShapePolicy {
    fn niches(self) -> bool {
        match self {
            Self::Products => false,
            Self::ReadonlySums => true,
            Self::CertifiedNiches => true,
        }
    }
    fn sums(self) -> bool {
        match self {
            Self::Products => false,
            Self::ReadonlySums => true,
            Self::CertifiedNiches => false,
        }
    }
}

impl<'tcx> Engine<'tcx> {
    pub(super) fn plain_composite_struct(&self, def: ty::AdtDef<'tcx>) -> bool {
        if !def.is_struct() {
            return false;
        }
        if def.did().is_local() {
            // Preserve the prior local domain; only the new external domain needs this filter.
            return true;
        }
        ordinary_external_struct_policy(
            def.did().krate,
            self.tcx
                .lang_items()
                .sized_trait()
                .map(|anchor| anchor.krate),
            def.flags(),
        )
    }

    pub(super) fn owned_struct_choice_shape(
        &self,
        ty: Ty<'tcx>,
    ) -> Result<Option<CompositeShape>, String> {
        Ok(self
            .composite_shape_with_sums(ty, false)?
            .map(|descriptor| descriptor.shape))
    }

    pub(super) fn composite_slice_shape(
        &self,
        ty: Ty<'tcx>,
    ) -> Result<Option<CompositeType<'tcx>>, String> {
        self.composite_shape_with_sums(ty, true)
    }

    pub(super) fn composite_shape_with_sums(
        &self,
        ty: Ty<'tcx>,
        allow_sums: bool,
    ) -> Result<Option<CompositeType<'tcx>>, String> {
        self.composite_shape_policy(
            ty,
            if allow_sums {
                ShapePolicy::ReadonlySums
            } else {
                ShapePolicy::Products
            },
        )
    }

    pub(in crate::proof) fn composite_shape_with_niches(
        &self,
        original: Ty<'tcx>,
    ) -> Result<Option<CompositeType<'tcx>>, String> {
        self.composite_shape_policy(original, ShapePolicy::CertifiedNiches)
    }

    fn composite_shape_policy(
        &self,
        ty: Ty<'tcx>,
        policy: ShapePolicy,
    ) -> Result<Option<CompositeType<'tcx>>, String> {
        if !matches!(ty.kind(), ty::Tuple(_) | ty::Array(..) | ty::Adt(..)) {
            return Ok(None);
        }
        let mut nodes = 0;
        let Some(shape) = self.composite_shape_depth(ty, 0, &mut nodes, policy, false)? else {
            return Ok(None);
        };
        let bytes = self.static_layout(ty)?.size.bytes();
        let mut leaves = Vec::new();
        shape.leaves(&mut leaves);
        if bytes == 0 && !leaves.is_empty() {
            return Err("zero-sized composite shape has primitive storage leaves".into());
        }
        Ok(Some(CompositeType {
            ty,
            shape,
            leaves,
            bytes,
        }))
    }

    fn composite_shape_depth(
        &self,
        ty: Ty<'tcx>,
        depth: usize,
        nodes: &mut usize,
        policy: ShapePolicy,
        enum_payload: bool,
    ) -> Result<Option<CompositeShape>, String> {
        if depth >= MAX_SHAPE_DEPTH || *nodes >= MAX_SHAPE_NODES {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "composite slice type exceeds its depth or expanded node budget".into(),
            ));
        }
        *nodes += 1;
        // Original kinds are inspected before any normalization: Pat and identity-bearing
        // wrappers remain unsupported even beneath zero-length arrays.
        let env = ty::TypingEnv::fully_monomorphized();
        if !ty.is_freeze(self.tcx, env)
            || !self.tcx.type_is_copy_modulo_regions(env, ty)
            || ty.needs_drop(self.tcx, env)
        {
            return Ok(None);
        }
        let layout = self.static_layout(ty)?;
        if layout.align.abi.bytes() == 0 || !layout.align.abi.bytes().is_power_of_two() {
            return Err("composite slice type has inconsistent compiler alignment".into());
        }
        if let Some(leaf) = self.scalar_slice_element(ty)? {
            return Ok(Some(CompositeShape::Primitive(leaf)));
        }
        match ty.kind() {
            ty::Tuple(fields) => {
                let mut shapes = Vec::new();
                for field in fields.iter() {
                    let Some(shape) =
                        self.composite_shape_depth(field, depth + 1, nodes, policy, enum_payload)?
                    else {
                        return Ok(None);
                    };
                    shapes.push(shape);
                }
                Ok(Some(CompositeShape::Tuple(shapes)))
            }
            ty::Array(element, count) => {
                let Some(count) = count.try_to_target_usize(self.tcx) else {
                    return Ok(None);
                };
                if count > MAX_TYPE_ARRAY {
                    return Err(self.categorized_error(
                        UnknownCategory::ResourceLimit,
                        "composite slice type array exceeds the 128-element shape budget".into(),
                    ));
                }
                // Certify the original element even for N=0, then charge every actual
                // occurrence independently. A zero array's type probe is conservative.
                let Some(first) =
                    self.composite_shape_depth(*element, depth + 1, nodes, policy, enum_payload)?
                else {
                    return Ok(None);
                };
                let mut shapes = Vec::new();
                if count > 0 {
                    shapes.push(first);
                    for _ in 1..count {
                        let Some(shape) = self.composite_shape_depth(
                            *element,
                            depth + 1,
                            nodes,
                            policy,
                            enum_payload,
                        )?
                        else {
                            return Ok(None);
                        };
                        shapes.push(shape);
                    }
                }
                Ok(Some(CompositeShape::Array(shapes)))
            }
            ty::Adt(def, args) if policy.niches() && def.is_enum() => {
                if let Some(schema) = self.nonzero_niche_shape(ty, depth, nodes)? {
                    return Ok(Some(CompositeShape::NonZeroNiche(Box::new(schema))));
                }
                if policy.sums() {
                    self.readonly_sum_shape(ty, *def, args, depth, nodes)
                } else {
                    Ok(None)
                }
            }
            ty::Adt(def, _)
                if self.plain_composite_struct(*def)
                    && (!enum_payload
                        || local_sum_payload_struct_policy(def.did().is_local(), def.flags())) =>
            {
                self.composite_struct_shape(ty, layout, depth, nodes, policy, enum_payload)
            }
            _ => Ok(None),
        }
    }

    fn composite_struct_shape(
        &self,
        original: Ty<'tcx>,
        layout: rustc_middle::ty::layout::TyAndLayout<'tcx>,
        depth: usize,
        nodes: &mut usize,
        policy: ShapePolicy,
        enum_payload: bool,
    ) -> Result<Option<CompositeShape>, String> {
        let ty::Adt(def, args) = original.kind() else {
            return Err("composite struct certificate requires original compiler ADT".into());
        };
        if def.repr().pack.is_some()
            || matches!(
                layout.backend_repr,
                BackendRepr::SimdVector { .. } | BackendRepr::SimdScalableVector { .. }
            )
        {
            return Ok(None);
        }
        let mut fields = Vec::new();
        let mut physical_fields = Vec::new();
        for (position, field) in def.non_enum_variant().fields.iter().enumerate() {
            // Keep original instantiated kinds: normalization must not erase Pat or
            // turn opaque wrappers into ordinary primitive fields, even beneath N=0.
            let field_ty = field.ty(self.tcx, args).skip_norm_wip();
            let Some(shape) =
                self.composite_shape_depth(field_ty, depth + 1, nodes, policy, enum_payload)?
            else {
                return Ok(None);
            };
            let field_layout = self.static_layout(field_ty)?;
            if field_layout.size.bytes() != 0 {
                physical_fields.push((
                    layout.fields.offset(position).bytes(),
                    field_layout.backend_repr,
                ));
            }
            fields.push((field.name.as_str().to_owned(), shape));
        }
        physical_fields.sort_by_key(|(offset, _)| *offset);
        if !scalar_fields_match(layout.backend_repr, &physical_fields) {
            return Err("composite struct validity exceeds its original typed fields".into());
        }
        let shape = CompositeShape::Struct {
            name: self.tcx.def_path_str(def.did()),
            fields,
        };
        shape.validate_zero_storage(layout.size.bytes())?;
        Ok(Some(shape))
    }

    fn readonly_sum_shape(
        &self,
        original: Ty<'tcx>,
        def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<Option<CompositeShape>, String> {
        let is_option = self.tcx.lang_items().get(LangItem::Option) == Some(def.did());
        let ordinary = def.did().is_local()
            && (def.flags() == AdtFlags::IS_ENUM
                || def.flags() == (AdtFlags::IS_ENUM | AdtFlags::HAS_CTOR));
        if (!ordinary && !is_option)
            || def.repr().pack.is_some()
            || def.variants().len() < 2
            || def.variants().len() > aggregates::MAX_ENUM_VARIANTS
        {
            return Ok(None);
        }
        let layout = self.static_layout(original)?;
        if matches!(
            layout.variants,
            Variants::Multiple {
                tag_encoding: TagEncoding::Niche { .. },
                ..
            }
        ) {
            if matches!(
                layout.backend_repr,
                BackendRepr::Scalar(Scalar::Initialized {
                    value: Primitive::Int(rustc_abi::Integer::I32, false),
                    ..
                })
            ) {
                return self.char_niche_sum_shape(original, def, args, depth, nodes);
            }
            return self.bool_niche_sum_shape(original, def, args, depth, nodes);
        }
        if is_option && args.type_at(0) != self.tcx.types.u16 {
            return Ok(None);
        }
        let Variants::Multiple {
            tag,
            tag_encoding: TagEncoding::Direct,
            tag_field,
            variants,
        } = &layout.variants
        else {
            return Ok(None);
        };
        let Scalar::Initialized {
            value: Primitive::Int(width, _),
            valid_range,
        } = tag
        else {
            return Ok(None);
        };
        let (bits, signed) = self
            .integer_type(original.discriminant_ty(self.tcx))
            .ok_or("direct enum lacks its compiler discriminant type")?;
        let tag_bits = width.size().bits() as u32;
        let tag_mask = if tag_bits == 128 {
            u128::MAX
        } else {
            (1u128 << tag_bits) - 1
        };
        let tag_offset = layout.fields.offset(tag_field.as_usize()).bytes();
        if variants.len() != def.variants().len()
            || layout.uninhabited
            || tag_offset != 0
            || width.size() > layout.size
            || tag_bits > bits
        {
            return Err("direct enum tag layout differs from original compiler schema".into());
        }
        let mut inventory = Vec::new();
        let mut physical_tags = Vec::new();
        for (position, variant) in def.variants().iter_enumerated() {
            if *nodes >= MAX_SHAPE_NODES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "composite enum exceeds its expanded node budget".into(),
                ));
            }
            *nodes += 1;
            let tag_value = def.discriminant_for_variant(self.tcx, position).val;
            let physical_tag = tag_value & tag_mask;
            if !valid_range.contains(physical_tag) || physical_tags.contains(&physical_tag) {
                return Err("direct enum discriminants differ from its initialized tag".into());
            }
            physical_tags.push(physical_tag);
            let variant_layout = &variants[position];
            if variant_layout.is_uninhabited()
                || variant_layout.field_offsets.len() != variant.fields.len()
                || variant_layout.size > layout.size
            {
                return Err("direct enum variant extent differs from compiler inventory".into());
            }
            let mut fields = Vec::new();
            let mut physical = Vec::new();
            for (index, field) in variant.fields.iter().enumerate() {
                let field_ty = field.ty(self.tcx, args).skip_norm_wip();
                let Some(shape) = self.composite_shape_depth(
                    field_ty,
                    depth + 1,
                    nodes,
                    ShapePolicy::ReadonlySums,
                    true,
                )?
                else {
                    return Ok(None);
                };
                let field_layout = self.static_layout(field_ty)?;
                let offset = variant_layout.field_offsets[rustc_abi::FieldIdx::from_usize(index)];
                if offset.bytes() % field_layout.align.abi.bytes() != 0
                    || offset
                        .bytes()
                        .checked_add(field_layout.size.bytes())
                        .is_none_or(|end| end > variant_layout.size.bytes())
                    || (field_layout.size.bytes() != 0 && offset < width.size())
                {
                    return Err(
                        "direct enum payload offset differs from original field layout".into(),
                    );
                }
                if field_layout.size.bytes() != 0 {
                    physical.push((offset.bytes(), field_layout.backend_repr));
                }
                fields.push((field.name.as_str().to_owned(), shape));
            }
            physical.sort_by_key(|(offset, _)| *offset);
            if !direct_enum_backend_matches(layout.backend_repr, *tag, &physical)
                || !direct_enum_backend_matches(variant_layout.backend_repr, *tag, &physical)
            {
                return Err(
                    "direct enum scalar validity exceeds its active payload certificate".into(),
                );
            }
            inventory.push(CompositeVariant {
                name: variant.name.as_str().to_owned(),
                discriminant: tag_value,
                fields,
            });
        }
        validate_sum_inventory(bits, &inventory)?;
        Ok(Some(CompositeShape::Sum {
            name: self.tcx.def_path_str(def.did()),
            bits,
            signed,
            is_option,
            variants: inventory,
        }))
    }

    fn bool_niche_sum_shape(
        &self,
        original: Ty<'tcx>,
        def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<Option<CompositeShape>, String> {
        let is_option = self.tcx.lang_items().get(LangItem::Option) == Some(def.did());
        if def.variants().len() != 2 || (is_option && args.type_at(0) != self.tcx.types.bool) {
            return Ok(None);
        }
        let layout = self.static_layout(original)?;
        let Variants::Multiple {
            tag,
            tag_encoding:
                TagEncoding::Niche {
                    untagged_variant,
                    niche_variants,
                    niche_start,
                },
            tag_field,
            variants,
        } = &layout.variants
        else {
            return Ok(None);
        };
        let bool_layout = self.static_layout(self.tcx.types.bool)?;
        let BackendRepr::Scalar(bool_scalar) = bool_layout.backend_repr else {
            return Err("original Bool lacks its initialized scalar ABI".into());
        };
        if !bool_niche_mapping_matches(
            *tag,
            bool_scalar,
            untagged_variant.as_usize(),
            niche_variants.start.as_usize(),
            niche_variants.last.as_usize(),
            *niche_start,
        ) || layout.uninhabited
            || layout.size.bytes() != 1
            || layout.align.abi.bytes() != 1
            || bool_layout.size.bytes() != 1
            || bool_layout.align.abi.bytes() != 1
            || layout.fields.count() != 1
            || tag_field.as_usize() != 0
            || layout.fields.offset(tag_field.as_usize()).bytes() != 0
            || layout.backend_repr != BackendRepr::Scalar(*tag)
            || variants.len() != 2
        {
            return Ok(None);
        }
        let (bits, signed) = self
            .integer_type(original.discriminant_ty(self.tcx))
            .ok_or("Bool niche enum lacks its compiler discriminant type")?;
        let mut inventory = Vec::new();
        for (position, variant) in def.variants().iter_enumerated() {
            if *nodes >= MAX_SHAPE_NODES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "composite enum exceeds its expanded node budget".into(),
                ));
            }
            *nodes += 1;
            let actual = &variants[position];
            let discriminant = def.discriminant_for_variant(self.tcx, position).val;
            if discriminant != position.as_usize() as u128 || actual.is_uninhabited() {
                return Ok(None);
            }
            let mut fields = Vec::new();
            if position == *untagged_variant {
                if variant.fields.len() != 1
                    || actual.field_offsets.len() != 1
                    || actual.field_offsets[rustc_abi::FieldIdx::from_usize(0)].bytes() != 0
                    || actual.size != bool_layout.size
                    || actual.backend_repr != BackendRepr::Scalar(bool_scalar)
                {
                    return Ok(None);
                }
                let field = &variant.fields[rustc_abi::FieldIdx::from_usize(0)];
                let original_field = field.ty(self.tcx, args).skip_norm_wip();
                if original_field != self.tcx.types.bool {
                    return Ok(None);
                }
                let Some(shape) = self.composite_shape_depth(
                    original_field,
                    depth + 1,
                    nodes,
                    ShapePolicy::ReadonlySums,
                    true,
                )?
                else {
                    return Ok(None);
                };
                fields.push((field.name.as_str().to_owned(), shape));
            } else if !variant.fields.is_empty()
                || !actual.field_offsets.is_empty()
                || actual.size.bytes() != 0
                || actual.backend_repr != (BackendRepr::Memory { sized: true })
            {
                return Ok(None);
            }
            inventory.push(CompositeVariant {
                name: variant.name.as_str().to_owned(),
                discriminant,
                fields,
            });
        }
        validate_sum_inventory(bits, &inventory)?;
        Ok(Some(CompositeShape::Sum {
            name: self.tcx.def_path_str(def.did()),
            bits,
            signed,
            is_option,
            variants: inventory,
        }))
    }

    fn char_niche_sum_shape(
        &self,
        original: Ty<'tcx>,
        def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
        depth: usize,
        nodes: &mut usize,
    ) -> Result<Option<CompositeShape>, String> {
        let is_option = self.tcx.lang_items().get(LangItem::Option) == Some(def.did());
        if def.variants().len() != 2 || (is_option && args.type_at(0) != self.tcx.types.char) {
            return Ok(None);
        }
        let layout = self.static_layout(original)?;
        let Variants::Multiple {
            tag,
            tag_encoding:
                TagEncoding::Niche {
                    untagged_variant,
                    niche_variants,
                    niche_start,
                },
            tag_field,
            variants,
        } = &layout.variants
        else {
            return Ok(None);
        };
        let char_layout = self.static_layout(self.tcx.types.char)?;
        let BackendRepr::Scalar(char_scalar) = char_layout.backend_repr else {
            return Err("original Char lacks its initialized scalar ABI".into());
        };
        if !char_niche_mapping_matches(
            *tag,
            char_scalar,
            untagged_variant.as_usize(),
            niche_variants.start.as_usize(),
            niche_variants.last.as_usize(),
            *niche_start,
        ) || layout.uninhabited
            || layout.size.bytes() != 4
            || layout.align.abi.bytes() != 4
            || char_layout.size.bytes() != 4
            || char_layout.align.abi.bytes() != 4
            || layout.fields.count() != 1
            || tag_field.as_usize() != 0
            || layout.fields.offset(tag_field.as_usize()).bytes() != 0
            || layout.backend_repr != BackendRepr::Scalar(*tag)
            || variants.len() != 2
        {
            return Ok(None);
        }
        let (bits, signed) = self
            .integer_type(original.discriminant_ty(self.tcx))
            .ok_or("Char niche enum lacks its compiler discriminant type")?;
        let mut inventory = Vec::new();
        for (position, variant) in def.variants().iter_enumerated() {
            if *nodes >= MAX_SHAPE_NODES {
                return Err(self.categorized_error(
                    UnknownCategory::ResourceLimit,
                    "composite enum exceeds its expanded node budget".into(),
                ));
            }
            *nodes += 1;
            let actual = &variants[position];
            let discriminant = def.discriminant_for_variant(self.tcx, position).val;
            if discriminant != position.as_usize() as u128 || actual.is_uninhabited() {
                return Ok(None);
            }
            let mut fields = Vec::new();
            if position == *untagged_variant {
                if variant.fields.len() != 1
                    || actual.field_offsets.len() != 1
                    || actual.field_offsets[rustc_abi::FieldIdx::from_usize(0)].bytes() != 0
                    || actual.size != char_layout.size
                    || actual.backend_repr != BackendRepr::Scalar(char_scalar)
                {
                    return Ok(None);
                }
                let field = &variant.fields[rustc_abi::FieldIdx::from_usize(0)];
                let original_field = field.ty(self.tcx, args).skip_norm_wip();
                if original_field != self.tcx.types.char {
                    return Ok(None);
                }
                let Some(shape) = self.composite_shape_depth(
                    original_field,
                    depth + 1,
                    nodes,
                    ShapePolicy::ReadonlySums,
                    true,
                )?
                else {
                    return Ok(None);
                };
                fields.push((field.name.as_str().to_owned(), shape));
            } else if !variant.fields.is_empty()
                || !actual.field_offsets.is_empty()
                || actual.size.bytes() != 0
                || actual.backend_repr != (BackendRepr::Memory { sized: true })
            {
                return Ok(None);
            }
            inventory.push(CompositeVariant {
                name: variant.name.as_str().to_owned(),
                discriminant,
                fields,
            });
        }
        validate_sum_inventory(bits, &inventory)?;
        Ok(Some(CompositeShape::Sum {
            name: self.tcx.def_path_str(def.did()),
            bits,
            signed,
            is_option,
            variants: inventory,
        }))
    }

    pub(super) fn composite_slice_input(
        &mut self,
        root: DefId,
        ty: Ty<'tcx>,
        conditions: &mut Vec<Term>,
    ) -> Result<Value, String> {
        if self.building_mutable_input {
            return Err(self.categorized_error(
                UnknownCategory::Semantics,
                "mutable composite slice input is unsupported".into(),
            ));
        }
        let descriptor = self.composite_slice_shape(ty)?.ok_or_else(|| {
            self.categorized_error(
                UnknownCategory::Semantics,
                "composite slice requires a pure product or direct-tag enum element".into(),
            )
        })?;
        let count = descriptor.leaves.len() + 1;
        if self
            .input_values
            .checked_add(count)
            .is_none_or(|n| n > MAX_INPUT_VALUES)
        {
            return Err(self.categorized_error(
                UnknownCategory::ResourceLimit,
                "composite slice input exceeds the 512-value budget".into(),
            ));
        }
        self.input_values += count;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let length = self.fresh(Sort::BitVec(bits));
        let max = slice_extent_limit(bits, descriptor.bytes)?;
        conditions.push(self.terms.apply(
            Op::BvUnsignedLe,
            &[length.clone(), self.terms.bit_vector(max, bits)?],
        )?);
        let leaves = descriptor
            .leaves
            .iter()
            .map(|leaf| {
                Ok(self.fresh(Sort::Array(
                    Box::new(Sort::BitVec(bits)),
                    Box::new(scalar_slice_sort(*leaf)?),
                )))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let id = if let Some(id) = self.composite_slice_types.iter().position(|d| d.ty == ty) {
            id
        } else {
            let id = self.composite_slice_types.len();
            self.composite_slice_types.push(descriptor);
            id
        };
        self.record_model(
            root,
            if self.composite_slice_types[id].shape.contains_sum() {
                "readonly tagged slice; legal tag and correlated latent payload columns"
            } else {
                concat!(
                    "readonly composite slice; exact compiler shape ",
                    "and independent primitive leaf arrays"
                )
            },
        );
        Ok(Value::CompositeSlice {
            id,
            length: Box::new(Value::Int {
                expression: length,
                bits,
                signed: false,
            }),
            leaves,
        })
    }

    pub(super) fn composite_slice_length(
        &self,
        value: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let Value::CompositeSlice { id, length, leaves } = value else {
            return Err("expected initialized readonly composite slice".into());
        };
        let descriptor = self
            .composite_slice_types
            .get(*id)
            .ok_or("composite slice compiler descriptor is absent")?;
        if descriptor.bytes == 0 && !descriptor.leaves.is_empty() {
            return Err("zero-sized composite descriptor has primitive storage leaves".into());
        }
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        validate_terms(&self.terms, bits, &descriptor.leaves, length, leaves)?;
        let max = slice_extent_limit(bits, descriptor.bytes)?;
        let safe = self.terms.apply(
            Op::BvUnsignedLe,
            &[length.integer()?.0, self.terms.bit_vector(max, bits)?],
        )?;
        if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&safe)]].concat())? {
            return Err("composite slice lacks valid target allocation extent".into());
        }
        Ok((**length).clone())
    }

    pub(super) fn composite_slice_select(
        &self,
        source: &Value,
        index: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let length = self.composite_slice_length(source, conditions)?;
        let (term, bits, signed) = index.integer()?;
        if bits != u32::from(self.tcx.sess.target.pointer_width)
            || signed
            || term.sort() != &Sort::BitVec(bits)
            || !term.belongs_to(&self.terms)
        {
            return Err("composite slice index requires exact target usize".into());
        }
        self.memory_bounds(index, &length, conditions)?;
        let Value::CompositeSlice { id, leaves, .. } = source else {
            unreachable!()
        };
        let descriptor = &self.composite_slice_types[*id];
        let mut cursor = 0;
        let value = descriptor
            .shape
            .observe(&self.terms, leaves, &term, &mut cursor)?;
        if cursor != leaves.len() {
            return Err("composite observation omitted primitive leaf storage".into());
        }
        Ok(value)
    }

    /// Pure logical observation after free source/type/extent certification. The index may be
    /// lexically bound, so this method performs no feasibility or memory-access query.
    pub(super) fn composite_slice_logical_item(
        &self,
        source: &Value,
        original: Ty<'tcx>,
        index: &Term,
    ) -> Result<Value, String> {
        let Value::CompositeSlice { id, length, leaves } = source else {
            return Err("logical composite observation requires a readonly descriptor".into());
        };
        let descriptor = self
            .composite_slice_types
            .get(*id)
            .ok_or("logical composite observation has an invalid type certificate")?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        let (length, width, signed) = length.integer()?;
        if descriptor.ty != original
            || width != bits
            || signed
            || length.sort() != &Sort::BitVec(bits)
            || !length.belongs_to(&self.terms)
            || index.sort() != &Sort::BitVec(bits)
            || !index.belongs_to(&self.terms)
            || leaves.len() != descriptor.leaves.len()
        {
            return Err("logical composite observation differs from its compiler metadata".into());
        }
        for (leaf, kind) in leaves.iter().zip(&descriptor.leaves) {
            if !leaf.belongs_to(&self.terms)
                || leaf.sort()
                    != &Sort::Array(
                        Box::new(Sort::BitVec(bits)),
                        Box::new(scalar_slice_sort(*kind)?),
                    )
            {
                return Err("logical composite observation has invalid leaf storage".into());
            }
        }
        let mut cursor = 0;
        let value = descriptor
            .shape
            .observe(&self.terms, leaves, index, &mut cursor)?;
        if cursor != leaves.len() {
            return Err("logical composite observation omitted leaf storage".into());
        }
        Ok(value)
    }

    pub(super) fn composite_slice_region(
        &self,
        source: &Value,
        offset: &Value,
        length: &Value,
        conditions: &[Term],
    ) -> Result<Value, String> {
        let capacity = self.composite_slice_length(source, conditions)?;
        let bits = u32::from(self.tcx.sess.target.pointer_width);
        for value in [offset, length] {
            let (term, width, signed) = value.integer()?;
            if width != bits
                || signed
                || term.sort() != &Sort::BitVec(bits)
                || !term.belongs_to(&self.terms)
            {
                return Err("composite slice region requires exact target usize".into());
            }
        }
        let within =
            symbolic::binary(&self.terms, "le", offset.clone(), capacity.clone())?.boolean()?;
        let available = symbolic::binary(&self.terms, "sub", capacity, offset.clone())?;
        let fits = symbolic::binary(&self.terms, "le", length.clone(), available)?.boolean()?;
        let safe = self.terms.apply(Op::And, &[within, fits])?;
        if self.feasible(&[conditions.to_vec(), vec![symbolic::not(&safe)]].concat())? {
            return Err("composite slice view lacks proven region bounds".into());
        }
        let Value::CompositeSlice { id, leaves, .. } = source else {
            unreachable!()
        };
        Ok(Value::CompositeSlice {
            id: *id,
            length: Box::new(length.clone()),
            leaves: leaves
                .iter()
                .map(|data| {
                    self.terms
                        .apply(Op::ArrayOffset, &[data.clone(), offset.integer()?.0])
                })
                .collect::<Result<_, _>>()?,
        })
    }
}

fn validate_terms(
    context: &Context,
    pointer_bits: u32,
    types: &[ScalarSliceElement],
    length: &Value,
    leaves: &[Term],
) -> Result<(), String> {
    let (term, bits, signed) = length.integer()?;
    if bits != pointer_bits
        || signed
        || term.sort() != &Sort::BitVec(bits)
        || !term.belongs_to(context)
        || leaves.len() != types.len()
    {
        return Err("composite slice length or leaf inventory metadata mismatch".into());
    }
    for (data, leaf) in leaves.iter().zip(types) {
        let expected = Sort::Array(
            Box::new(Sort::BitVec(bits)),
            Box::new(scalar_slice_sort(*leaf)?),
        );
        if data.sort() != &expected || !data.belongs_to(context) {
            return Err("composite slice leaf has incorrect sort or analysis context".into());
        }
    }
    Ok(())
}

impl CompositeShape {
    fn validate_zero_storage(&self, bytes: u64) -> Result<(), String> {
        if bytes == 0 && self.has_primitive_storage() {
            return Err("zero-sized composite shape has primitive storage leaves".into());
        }
        Ok(())
    }

    fn contains_sum(&self) -> bool {
        match self {
            Self::Sum { .. } | Self::NonZeroNiche(_) => true,
            Self::Primitive(_) => false,
            Self::Tuple(fields) | Self::Array(fields) => fields.iter().any(Self::contains_sum),
            Self::Struct { fields, .. } => fields.iter().any(|(_, field)| field.contains_sum()),
        }
    }

    fn has_primitive_storage(&self) -> bool {
        match self {
            Self::Primitive(_) | Self::Sum { .. } | Self::NonZeroNiche(_) => true,
            Self::Tuple(fields) | Self::Array(fields) => {
                fields.iter().any(Self::has_primitive_storage)
            }
            Self::Struct { fields, .. } => fields
                .iter()
                .any(|(_, field)| field.has_primitive_storage()),
        }
    }

    fn leaves(&self, output: &mut Vec<ScalarSliceElement>) {
        match self {
            Self::NonZeroNiche(schema) => output.push(schema.payload_element()),
            Self::Sum {
                bits,
                signed,
                variants,
                ..
            } => {
                output.push(ScalarSliceElement::Integer {
                    bits: *bits,
                    signed: *signed,
                });
                for variant in variants {
                    for (_, field) in &variant.fields {
                        field.leaves(output);
                    }
                }
            }
            Self::Primitive(leaf) => output.push(*leaf),
            Self::Tuple(fields) | Self::Array(fields) => {
                for field in fields {
                    field.leaves(output);
                }
            }
            Self::Struct { fields, .. } => {
                for (_, field) in fields {
                    field.leaves(output);
                }
            }
        }
    }

    pub(super) fn observe(
        &self,
        context: &Context,
        leaves: &[Term],
        index: &Term,
        cursor: &mut usize,
    ) -> Result<Value, String> {
        match self {
            Self::NonZeroNiche(schema) => schema.observe(context, leaves, index, cursor),
            Self::Sum {
                name,
                bits,
                signed,
                is_option,
                variants,
            } => {
                validate_sum_inventory(*bits, variants)?;
                let data = leaves.get(*cursor).ok_or("sum tag storage missing")?;
                *cursor += 1;
                let selector = context.apply(Op::Select, &[data.clone(), index.clone()])?;
                let mut tag = context.bit_vector(variants[0].discriminant, *bits)?;
                for (position, variant) in variants.iter().enumerate().skip(1) {
                    let choice = context.apply(
                        Op::Equal,
                        &[
                            selector.clone(),
                            context.bit_vector(position as u128, *bits)?,
                        ],
                    )?;
                    tag = context.apply(
                        Op::Ite,
                        &[
                            choice,
                            context.bit_vector(variant.discriminant, *bits)?,
                            tag,
                        ],
                    )?;
                }
                let payloads = variants
                    .iter()
                    .enumerate()
                    .map(|(variant, schema)| {
                        Ok(Value::Adt {
                            name: name.clone(),
                            variant,
                            discriminant: schema.discriminant,
                            is_option: *is_option,
                            fields: schema
                                .fields
                                .iter()
                                .map(|(name, field)| {
                                    Ok((
                                        name.clone(),
                                        field.observe(context, leaves, index, cursor)?,
                                    ))
                                })
                                .collect::<Result<Vec<_>, String>>()?
                                .into(),
                        })
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                Ok(Value::Enum {
                    discriminant: Box::new(Value::Int {
                        expression: tag,
                        bits: *bits,
                        signed: *signed,
                    }),
                    variants: payloads,
                    is_option: *is_option,
                })
            }
            Self::Struct { name, fields } => Ok(Value::Adt {
                name: name.clone(),
                variant: 0,
                discriminant: 0,
                is_option: false,
                fields: fields
                    .iter()
                    .map(|(name, field)| {
                        Ok((name.clone(), field.observe(context, leaves, index, cursor)?))
                    })
                    .collect::<Result<Vec<_>, String>>()?
                    .into(),
            }),
            Self::Primitive(leaf) => {
                let data = leaves
                    .get(*cursor)
                    .ok_or("composite leaf storage missing")?;
                *cursor += 1;
                decode_scalar_element(
                    context,
                    *leaf,
                    context.apply(Op::Select, &[data.clone(), index.clone()])?,
                )
            }
            Self::Tuple(fields) | Self::Array(fields) => {
                let values = fields
                    .iter()
                    .map(|field| field.observe(context, leaves, index, cursor))
                    .collect::<Result<Vec<_>, _>>()?;
                match self {
                    Self::Tuple(_) if values.is_empty() => Ok(Value::Unit),
                    Self::Tuple(_) => Ok(Value::Tuple(values)),
                    Self::Array(_) => Ok(Value::Elements(values.into())),
                    Self::Primitive(_)
                    | Self::Struct { .. }
                    | Self::Sum { .. }
                    | Self::NonZeroNiche(_) => unreachable!(),
                }
            }
        }
    }
}

fn validate_sum_inventory(bits: u32, variants: &[CompositeVariant]) -> Result<(), String> {
    if !(1..=128).contains(&bits)
        || variants.len() < 2
        || variants.len() > aggregates::MAX_ENUM_VARIANTS
    {
        return Err("sum observation lacks its exact variant inventory".into());
    }
    let mask = u128::MAX >> (128 - bits);
    for (position, variant) in variants.iter().enumerate() {
        if variant.name.is_empty()
            || variants[..position].iter().any(|prior| {
                prior.name == variant.name
                    || (prior.discriminant & mask) == (variant.discriminant & mask)
            })
            || variant.fields.iter().enumerate().any(|(index, (name, _))| {
                name.is_empty()
                    || variant.fields[..index]
                        .iter()
                        .any(|(prior, _)| prior == name)
            })
        {
            return Err("sum observation has inconsistent nominal variant metadata".into());
        }
    }
    Ok(())
}

// The niche tag overlaps Bool storage. Only the three concrete initialized encodings
// are admitted; the empty variant never initializes or reads the latent Bool payload.
fn bool_niche_mapping_matches(
    tag: Scalar,
    payload: Scalar,
    untagged: usize,
    first: usize,
    last: usize,
    niche_start: u128,
) -> bool {
    let bool_scalar = Scalar::Initialized {
        value: Primitive::Int(rustc_abi::Integer::I8, false),
        valid_range: rustc_abi::WrappingRange { start: 0, end: 1 },
    };
    let enum_scalar = Scalar::Initialized {
        value: Primitive::Int(rustc_abi::Integer::I8, false),
        valid_range: rustc_abi::WrappingRange { start: 0, end: 2 },
    };
    payload == bool_scalar
        && tag == enum_scalar
        && untagged < 2
        && first == last
        && first == 1 - untagged
        && niche_start == 2
}

// Char's ABI interval includes surrogates, but its typed logical observation does not.
// The singleton empty encoding is -1 at I32 width; it never becomes a Char payload.
fn char_niche_mapping_matches(
    tag: Scalar,
    payload: Scalar,
    untagged: usize,
    first: usize,
    last: usize,
    niche_start: u128,
) -> bool {
    let char_scalar = Scalar::Initialized {
        value: Primitive::Int(rustc_abi::Integer::I32, false),
        valid_range: rustc_abi::WrappingRange {
            start: 0,
            end: 0x10ffff,
        },
    };
    let enum_scalar = Scalar::Initialized {
        value: Primitive::Int(rustc_abi::Integer::I32, false),
        valid_range: rustc_abi::WrappingRange {
            start: 0xffff_ffff,
            end: 0x10ffff,
        },
    };
    payload == char_scalar
        && tag == enum_scalar
        && untagged < 2
        && first == last
        && first == 1 - untagged
        && niche_start == 0xffff_ffff
}

// The initialized tag is always present. A scalar-pair payload may be absent in a
// fieldless variant; union/full-range ABI storage does not initialize that inactive payload.
fn direct_enum_backend_matches(
    representation: BackendRepr,
    tag: Scalar,
    fields: &[(u64, BackendRepr)],
) -> bool {
    match representation {
        BackendRepr::Memory { .. } => true,
        BackendRepr::Scalar(actual) => actual == tag && fields.is_empty(),
        BackendRepr::ScalarPair { a, b, b_offset } => {
            a == tag
                && match fields {
                    [] => b.is_uninit_valid(),
                    [(offset, BackendRepr::Scalar(field))] => {
                        *offset == b_offset.bytes()
                            && b.primitive() == field.primitive()
                            && (b == *field || b.is_uninit_valid() || unrestricted_scalar_range(b))
                    }
                    _ => false,
                }
        }
        BackendRepr::SimdVector { .. } | BackendRepr::SimdScalableVector { .. } => false,
    }
}

fn unrestricted_scalar_range(scalar: Scalar) -> bool {
    let Scalar::Initialized { value, valid_range } = scalar else {
        return false;
    };
    let size = match value {
        Primitive::Int(width, _) => width.size(),
        Primitive::Float(width) => width.size(),
        Primitive::Pointer(_) => return false,
    };
    valid_range.is_full_for(size)
}

impl<'tcx> Engine<'tcx> {
    // Caller prepays the fixed descriptor reads before entering this borrowed service.
    pub(super) fn niche_membership_descriptor(
        &self,
        original: Ty<'tcx>,
        value: &Value,
    ) -> Result<&nonzero_niches::Schema, String> {
        let Value::CompositeSlice { id, .. } = value else {
            return Err("niche membership descriptor carrier differs".into());
        };
        let descriptor = self
            .composite_slice_types
            .get(*id)
            .ok_or("niche membership descriptor is unavailable")?;
        let CompositeShape::NonZeroNiche(schema) = &descriptor.shape else {
            return Err("niche membership descriptor original shape differs".into());
        };
        if descriptor.ty != original
            || descriptor.bytes != schema.item_bytes()
            || descriptor.leaves.as_slice() != [schema.payload_element()]
        {
            return Err("niche membership descriptor original extent/column differs".into());
        }
        Ok(schema)
    }

    #[cfg(test)]
    pub(super) fn test_niche_descriptor_fault(&mut self, value: &Value, fault: usize) -> Value {
        let Value::CompositeSlice { id, length, leaves } = value else {
            unreachable!()
        };
        let mut descriptor = self.composite_slice_types[*id].clone();
        match fault {
            0 => descriptor.bytes = if descriptor.bytes == 2 { 4 } else { 2 },
            1 => {
                descriptor.shape = CompositeShape::Primitive(ScalarSliceElement::Integer {
                    bits: 16,
                    signed: false,
                })
            }
            2 => {
                let width = if matches!(
                    descriptor.leaves.as_slice(),
                    [ScalarSliceElement::Integer {
                        bits: 32,
                        signed: false
                    }]
                ) {
                    16
                } else {
                    32
                };
                descriptor.leaves = vec![ScalarSliceElement::Integer {
                    bits: width,
                    signed: false,
                }]
            }
            _ => panic!("unknown descriptor fault"),
        }
        let changed = self.composite_slice_types.len();
        self.composite_slice_types.push(descriptor);
        Value::CompositeSlice {
            id: changed,
            length: length.clone(),
            leaves: leaves.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn bool_niche_metadata_requires_exact_initialized_three_value_mapping() {
        let payload = Scalar::Initialized {
            value: Primitive::Int(rustc_abi::Integer::I8, false),
            valid_range: rustc_abi::WrappingRange { start: 0, end: 1 },
        };
        let tag = Scalar::Initialized {
            value: Primitive::Int(rustc_abi::Integer::I8, false),
            valid_range: rustc_abi::WrappingRange { start: 0, end: 2 },
        };
        for untagged in [0, 1] {
            let empty = 1 - untagged;
            assert!(bool_niche_mapping_matches(
                tag, payload, untagged, empty, empty, 2
            ));
            assert!(!bool_niche_mapping_matches(
                tag, payload, untagged, empty, empty, 0
            ));
            assert!(!bool_niche_mapping_matches(
                tag, payload, untagged, empty, empty, 1
            ));
            assert!(!bool_niche_mapping_matches(
                tag, payload, untagged, empty, empty, 258
            ));
            assert!(!bool_niche_mapping_matches(
                tag, payload, untagged, untagged, untagged, 2
            ));
        }
        assert!(!bool_niche_mapping_matches(tag, payload, 2, 0, 0, 2));
        assert!(!bool_niche_mapping_matches(tag, payload, 1, 0, 1, 2));
        for scalar in [
            Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I8, true),
                valid_range: rustc_abi::WrappingRange { start: 0, end: 2 },
            },
            Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I16, false),
                valid_range: rustc_abi::WrappingRange { start: 0, end: 2 },
            },
            Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I8, false),
                valid_range: rustc_abi::WrappingRange { start: 0, end: 255 },
            },
            Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I8, false),
                valid_range: rustc_abi::WrappingRange { start: 255, end: 2 },
            },
            Scalar::Union {
                value: Primitive::Int(rustc_abi::Integer::I8, false),
            },
        ] {
            assert!(!bool_niche_mapping_matches(scalar, payload, 1, 0, 0, 2));
        }
        assert!(!bool_niche_mapping_matches(tag, tag, 1, 0, 0, 2));
    }
    use super::*;

    #[test]
    fn char_niche_requires_exact_wrapping_abi_and_empty_mapping() {
        let payload = Scalar::Initialized {
            value: Primitive::Int(rustc_abi::Integer::I32, false),
            valid_range: rustc_abi::WrappingRange {
                start: 0,
                end: 0x10ffff,
            },
        };
        let tag = Scalar::Initialized {
            value: Primitive::Int(rustc_abi::Integer::I32, false),
            valid_range: rustc_abi::WrappingRange {
                start: 0xffff_ffff,
                end: 0x10ffff,
            },
        };
        for untagged in [0, 1] {
            let empty = 1 - untagged;
            assert!(char_niche_mapping_matches(
                tag,
                payload,
                untagged,
                empty,
                empty,
                0xffff_ffff
            ));
            for start in [0, 0xd800, 0xdfff, 0x110000, 0xffff_fffe, 0x1_ffff_ffff] {
                assert!(!char_niche_mapping_matches(
                    tag, payload, untagged, empty, empty, start
                ));
            }
            assert!(!char_niche_mapping_matches(
                tag,
                payload,
                untagged,
                untagged,
                untagged,
                0xffff_ffff
            ));
        }
        assert!(!char_niche_mapping_matches(
            tag,
            payload,
            2,
            0,
            0,
            0xffff_ffff
        ));
        assert!(!char_niche_mapping_matches(
            tag,
            payload,
            1,
            0,
            1,
            0xffff_ffff
        ));
        for invalid in [
            Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I32, true),
                valid_range: rustc_abi::WrappingRange {
                    start: 0xffff_ffff,
                    end: 0x10ffff,
                },
            },
            Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I64, false),
                valid_range: rustc_abi::WrappingRange {
                    start: 0xffff_ffff,
                    end: 0x10ffff,
                },
            },
            Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I32, false),
                valid_range: rustc_abi::WrappingRange {
                    start: 0,
                    end: 0x110000,
                },
            },
            Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I32, false),
                valid_range: rustc_abi::WrappingRange {
                    start: 0xffff_fffe,
                    end: 0x10ffff,
                },
            },
            Scalar::Initialized {
                value: Primitive::Int(rustc_abi::Integer::I32, false),
                valid_range: rustc_abi::WrappingRange {
                    start: 0xffff_ffff,
                    end: 0x110000,
                },
            },
            Scalar::Union {
                value: Primitive::Int(rustc_abi::Integer::I32, false),
            },
        ] {
            assert!(!char_niche_mapping_matches(
                invalid,
                payload,
                1,
                0,
                0,
                0xffff_ffff
            ));
            assert!(!char_niche_mapping_matches(
                tag,
                invalid,
                1,
                0,
                0,
                0xffff_ffff
            ));
        }
        assert!(!char_niche_mapping_matches(tag, tag, 1, 0, 0, 0xffff_ffff));
    }

    #[test]
    fn sum_payload_struct_policy_does_not_widen_external_or_special_types() {
        for flags in [
            AdtFlags::IS_STRUCT,
            AdtFlags::IS_STRUCT | AdtFlags::HAS_CTOR,
        ] {
            assert!(local_sum_payload_struct_policy(true, flags));
            assert!(!local_sum_payload_struct_policy(false, flags));
        }
        for flags in [
            AdtFlags::IS_ENUM,
            AdtFlags::IS_UNION,
            AdtFlags::IS_PHANTOM_DATA,
            AdtFlags::IS_UNSAFE_CELL,
            AdtFlags::IS_MANUALLY_DROP,
            AdtFlags::IS_STRUCT | AdtFlags::IS_FUNDAMENTAL,
            AdtFlags::IS_STRUCT | AdtFlags::from_bits_retain(1 << 15),
        ] {
            assert!(!local_sum_payload_struct_policy(true, flags));
            assert!(!local_sum_payload_struct_policy(false, flags));
        }
    }

    #[test]
    fn nominal_sum_payloads_keep_field_identity_occurrences_and_zero_members() {
        let context = Context::default();
        let index = context.bit_vector(0, 32).unwrap();
        let integer = CompositeShape::Primitive(ScalarSliceElement::Integer {
            bits: 16,
            signed: false,
        });
        let record = CompositeShape::Struct {
            name: "Record".into(),
            fields: vec![
                ("left".into(), integer.clone()),
                ("right".into(), integer),
                (
                    "marker".into(),
                    CompositeShape::Struct {
                        name: "Marker".into(),
                        fields: vec![],
                    },
                ),
            ],
        };
        let shape = CompositeShape::Sum {
            name: "Packet".into(),
            bits: 8,
            signed: false,
            is_option: false,
            variants: vec![
                CompositeVariant {
                    name: "Empty".into(),
                    discriminant: 3,
                    fields: vec![],
                },
                CompositeVariant {
                    name: "Repeated".into(),
                    discriminant: 7,
                    fields: vec![("0".into(), record.clone()), ("1".into(), record)],
                },
            ],
        };
        let mut kinds = Vec::new();
        shape.leaves(&mut kinds);
        assert_eq!(kinds.len(), 5);
        let mut arrays = Vec::new();
        for (column, kind) in kinds.iter().enumerate() {
            let data = context
                .symbol(
                    u32::try_from(column).unwrap(),
                    Sort::Array(
                        Box::new(Sort::BitVec(32)),
                        Box::new(scalar_slice_sort(*kind).unwrap()),
                    ),
                )
                .unwrap();
            arrays.push(
                context
                    .apply(
                        Op::Store,
                        &[
                            data,
                            index.clone(),
                            context
                                .bit_vector(
                                    if column == 0 { 1 } else { column as u128 * 17 },
                                    if column == 0 { 8 } else { 16 },
                                )
                                .unwrap(),
                        ],
                    )
                    .unwrap(),
            );
        }
        let Value::Enum { variants, .. } =
            shape.observe(&context, &arrays, &index, &mut 0).unwrap()
        else {
            panic!("sum carrier lost");
        };
        let Value::Adt {
            fields: variant_fields,
            ..
        } = &variants[1]
        else {
            panic!("active inventory lost");
        };
        for (position, (_, payload)) in variant_fields.iter().enumerate() {
            let Value::Adt {
                name,
                variant,
                discriminant,
                is_option,
                fields,
            } = payload
            else {
                panic!("nominal payload collapsed");
            };
            assert_eq!(
                (name.as_str(), *variant, *discriminant, *is_option),
                ("Record", 0, 0, false)
            );
            assert_eq!(
                fields
                    .iter()
                    .map(|(name, _)| name.as_str())
                    .collect::<Vec<_>>(),
                ["left", "right", "marker"]
            );
            for (column, (_, value)) in fields.iter().take(2).enumerate() {
                assert_eq!(
                    symbolic::constant(&value.integer().unwrap().0),
                    Some(symbolic::Constant::BitVec {
                        value: (position * 2 + column + 1) as u128 * 17,
                        bits: 16,
                    })
                );
            }
            let Value::Adt { name, fields, .. } = &fields[2].1 else {
                panic!("zero-sized nominal member collapsed");
            };
            assert_eq!(name, "Marker");
            assert!(fields.is_empty());
        }
        let length = Value::Int {
            expression: context.bit_vector(1, 32).unwrap(),
            bits: 32,
            signed: false,
        };
        assert!(validate_terms(&context, 32, &kinds, &length, &arrays).is_ok());
        assert!(validate_terms(&context, 32, &kinds, &length, &arrays[..4]).is_err());
        let mut wrong = arrays.clone();
        wrong[1] = Context::default()
            .symbol(0, arrays[1].sort().clone())
            .unwrap();
        assert!(validate_terms(&context, 32, &kinds, &length, &wrong).is_err());
    }

    #[test]
    fn direct_sum_columns_preserve_legal_tags_nominal_payloads_and_occurrences() {
        let context = Context::default();
        let index = context.bit_vector(0, 32).unwrap();
        let next = context.bit_vector(1, 32).unwrap();
        let integer = CompositeShape::Primitive(ScalarSliceElement::Integer {
            bits: 16,
            signed: false,
        });
        let variants = vec![
            CompositeVariant {
                name: "Missing".into(),
                discriminant: 3,
                fields: vec![],
            },
            CompositeVariant {
                name: "Word".into(),
                discriminant: 7,
                fields: vec![("0".into(), integer.clone())],
            },
            CompositeVariant {
                name: "Pair".into(),
                discriminant: 11,
                fields: vec![("0".into(), integer.clone()), ("1".into(), integer)],
            },
        ];
        let shape = CompositeShape::Sum {
            name: "Reading".into(),
            bits: 8,
            signed: false,
            is_option: false,
            variants: variants.clone(),
        };
        let mut kinds = Vec::new();
        shape.leaves(&mut kinds);
        assert_eq!(kinds.len(), 4);
        let mut arrays = Vec::new();
        for (position, kind) in kinds.iter().enumerate() {
            arrays.push(
                context
                    .symbol(
                        u32::try_from(position).unwrap(),
                        Sort::Array(
                            Box::new(Sort::BitVec(32)),
                            Box::new(scalar_slice_sort(*kind).unwrap()),
                        ),
                    )
                    .unwrap(),
            );
        }
        arrays[0] = context
            .apply(
                Op::Store,
                &[
                    arrays[0].clone(),
                    index.clone(),
                    context.bit_vector(1, 8).unwrap(),
                ],
            )
            .unwrap();
        arrays[0] = context
            .apply(
                Op::Store,
                &[
                    arrays[0].clone(),
                    next.clone(),
                    context.bit_vector(2, 8).unwrap(),
                ],
            )
            .unwrap();
        for (slot, value) in [(1, 37), (2, 71), (3, 19)] {
            arrays[slot] = context
                .apply(
                    Op::Store,
                    &[
                        arrays[slot].clone(),
                        index.clone(),
                        context.bit_vector(value, 16).unwrap(),
                    ],
                )
                .unwrap();
        }
        let Value::Enum {
            discriminant,
            variants: payloads,
            is_option,
        } = shape.observe(&context, &arrays, &index, &mut 0).unwrap()
        else {
            panic!("nominal enum lost");
        };
        assert!(!is_option);
        assert_eq!(
            symbolic::constant(&discriminant.integer().unwrap().0),
            Some(symbolic::Constant::BitVec { value: 7, bits: 8 })
        );
        let Value::Adt {
            name,
            variant,
            discriminant: tag,
            fields,
            ..
        } = &payloads[1]
        else {
            panic!("active payload lost nominal metadata");
        };
        assert_eq!((name.as_str(), *variant, *tag), ("Reading", 1, 7));
        assert_eq!(fields[0].0, "0");
        assert_eq!(
            symbolic::constant(&fields[0].1.integer().unwrap().0),
            Some(symbolic::Constant::BitVec {
                value: 37,
                bits: 16
            })
        );
        let Value::Adt {
            variant, fields, ..
        } = &payloads[2]
        else {
            panic!("latent payload lost nominal metadata");
        };
        assert_eq!((*variant, fields.len()), (2, 2));
        assert_ne!(
            fields[0].1.integer().unwrap().0,
            fields[1].1.integer().unwrap().0
        );
        let Value::Enum { discriminant, .. } =
            shape.observe(&context, &arrays, &next, &mut 0).unwrap()
        else {
            panic!("second occurrence lost");
        };
        assert_eq!(
            symbolic::constant(&discriminant.integer().unwrap().0),
            Some(symbolic::Constant::BitVec { value: 11, bits: 8 })
        );
        arrays[0] = context
            .apply(
                Op::Store,
                &[
                    arrays[0].clone(),
                    next.clone(),
                    context.bit_vector(255, 8).unwrap(),
                ],
            )
            .unwrap();
        let Value::Enum { discriminant, .. } =
            shape.observe(&context, &arrays, &next, &mut 0).unwrap()
        else {
            panic!("fallback lost");
        };
        assert_eq!(
            symbolic::constant(&discriminant.integer().unwrap().0),
            Some(symbolic::Constant::BitVec { value: 3, bits: 8 })
        );
        assert!(validate_sum_inventory(8, &[]).is_err());
        let mut changed = variants.clone();
        changed[2].discriminant = 263;
        assert!(validate_sum_inventory(8, &changed).is_err());
        changed = variants;
        changed[2].name = "Word".into();
        assert!(validate_sum_inventory(8, &changed).is_err());
        assert!(
            shape
                .observe(&context, &arrays[..3], &index, &mut 0)
                .is_err()
        );
        let foreign = Context::default();
        let length = symbolic::integer(&context, 2, 32, false);
        arrays[0] = foreign
            .symbol(
                0,
                Sort::Array(Box::new(Sort::BitVec(32)), Box::new(Sort::BitVec(8))),
            )
            .unwrap();
        assert!(validate_terms(&context, 32, &kinds, &length, &arrays).is_err());
    }

    #[test]
    fn direct_sum_abi_keeps_tag_and_inactive_storage_separate() {
        use rustc_abi::{Integer, Size, WrappingRange};
        let tag = Scalar::Initialized {
            value: Primitive::Int(Integer::I8, false),
            valid_range: WrappingRange { start: 0, end: 1 },
        };
        let payload = Scalar::Initialized {
            value: Primitive::Int(Integer::I16, false),
            valid_range: WrappingRange::full(Size::from_bytes(2)),
        };
        let pair = BackendRepr::ScalarPair {
            a: tag,
            b: payload.to_union(),
            b_offset: Size::from_bytes(2),
        };
        assert!(direct_enum_backend_matches(pair, tag, &[]));
        assert!(direct_enum_backend_matches(
            pair,
            tag,
            &[(2, BackendRepr::Scalar(payload))]
        ));
        assert!(!direct_enum_backend_matches(
            pair,
            tag,
            &[(1, BackendRepr::Scalar(payload))]
        ));
        let restricted = Scalar::Initialized {
            value: payload.primitive(),
            valid_range: WrappingRange { start: 1, end: 9 },
        };
        assert!(!direct_enum_backend_matches(
            BackendRepr::ScalarPair {
                a: tag,
                b: restricted,
                b_offset: Size::from_bytes(2)
            },
            tag,
            &[(2, BackendRepr::Scalar(payload))]
        ));
        assert!(!direct_enum_backend_matches(
            BackendRepr::ScalarPair {
                a: tag,
                b: payload,
                b_offset: Size::from_bytes(2)
            },
            tag,
            &[]
        ));
        assert!(!direct_enum_backend_matches(
            BackendRepr::Scalar(payload),
            tag,
            &[]
        ));
        assert!(direct_enum_backend_matches(
            BackendRepr::Scalar(tag),
            tag,
            &[]
        ));
    }

    #[test]
    fn dependency_struct_policy_admits_only_ordinary_structural_flags() {
        let core = CrateNum::from_u32(1);
        let dependency = CrateNum::from_u32(2);
        assert!(ordinary_external_struct_policy(
            dependency,
            Some(core),
            AdtFlags::IS_STRUCT
        ));
        assert!(!ordinary_external_struct_policy(
            core,
            Some(core),
            AdtFlags::IS_STRUCT
        ));
        assert!(!ordinary_external_struct_policy(
            dependency,
            None,
            AdtFlags::IS_STRUCT
        ));
        assert!(ordinary_struct_flags(AdtFlags::IS_STRUCT));
        assert!(ordinary_struct_flags(
            AdtFlags::IS_STRUCT | AdtFlags::HAS_CTOR
        ));
        for special in [
            AdtFlags::IS_ENUM,
            AdtFlags::IS_UNION,
            AdtFlags::IS_PHANTOM_DATA,
            AdtFlags::IS_FUNDAMENTAL,
            AdtFlags::IS_BOX,
            AdtFlags::IS_MANUALLY_DROP,
            AdtFlags::IS_VARIANT_LIST_NON_EXHAUSTIVE,
            AdtFlags::IS_UNSAFE_CELL,
            AdtFlags::IS_UNSAFE_PINNED,
            AdtFlags::IS_PIN,
            AdtFlags::IS_PIN_PROJECT,
            AdtFlags::IS_FIELD_REPRESENTING_TYPE,
            AdtFlags::IS_MAYBE_DANGLING,
        ] {
            assert!(!ordinary_struct_flags(special));
            assert!(!ordinary_struct_flags(AdtFlags::IS_STRUCT | special));
            assert!(!ordinary_struct_flags(
                AdtFlags::IS_STRUCT | AdtFlags::HAS_CTOR | special
            ));
        }
        assert!(!ordinary_struct_flags(AdtFlags::NO_ADT_FLAGS));
        assert!(!ordinary_struct_flags(AdtFlags::from_bits_retain(1 << 15)));
    }

    #[test]
    fn zero_sized_structs_preserve_nominal_metadata_and_reject_storage_leaves() {
        let shape = CompositeShape::Struct {
            name: "fixture::Outer".into(),
            fields: vec![
                ("marker".into(), CompositeShape::Tuple(vec![])),
                (
                    "inner".into(),
                    CompositeShape::Struct {
                        name: "fixture::Inner".into(),
                        fields: vec![("empty".into(), CompositeShape::Array(vec![]))],
                    },
                ),
            ],
        };
        shape.validate_zero_storage(0).unwrap();
        let context = Context::default();
        let index = context.bit_vector(u64::MAX as u128, 64).unwrap();
        let mut cursor = 0;
        let Value::Adt {
            name,
            variant,
            discriminant,
            is_option,
            fields,
        } = shape.observe(&context, &[], &index, &mut cursor).unwrap()
        else {
            panic!("a nominal zero-sized struct must not collapse to Unit");
        };
        assert_eq!(
            (name.as_str(), variant, discriminant, is_option),
            ("fixture::Outer", 0, 0, false)
        );
        assert_eq!(fields[0].0, "marker");
        assert!(matches!(fields[0].1, Value::Unit));
        let Value::Adt {
            name,
            variant,
            discriminant,
            is_option,
            fields,
        } = &fields[1].1
        else {
            panic!("nested nominal metadata must remain intact");
        };
        assert_eq!(
            (name.as_str(), *variant, *discriminant, *is_option),
            ("fixture::Inner", 0, 0, false)
        );
        assert_eq!(fields[0].0, "empty");
        assert!(matches!(&fields[0].1, Value::Elements(values) if values.is_empty()));
        assert_eq!(cursor, 0);
        let invalid = CompositeShape::Struct {
            name: "fixture::Invalid".into(),
            fields: vec![(
                "nested".into(),
                CompositeShape::Array(vec![CompositeShape::Primitive(ScalarSliceElement::Bool)]),
            )],
        };
        assert!(invalid.validate_zero_storage(0).is_err());
        invalid.validate_zero_storage(1).unwrap();
    }

    #[test]
    fn struct_observation_preserves_named_fields_and_independent_same_index_leaves() {
        let context = Context::default();
        let kind = ScalarSliceElement::Integer {
            bits: 16,
            signed: false,
        };
        let shape = CompositeShape::Struct {
            name: "fixture::Pair".into(),
            fields: vec![
                ("left".into(), CompositeShape::Primitive(kind)),
                ("right".into(), CompositeShape::Primitive(kind)),
                ("marker".into(), CompositeShape::Tuple(vec![])),
            ],
        };
        let mut kinds = Vec::new();
        shape.leaves(&mut kinds);
        assert_eq!(kinds, vec![kind; 2]);
        let leaves = (0..2)
            .map(|i| {
                context
                    .symbol(
                        i,
                        Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(16))),
                    )
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let index = context.symbol(2, Sort::BitVec(64)).unwrap();
        let mut cursor = 0;
        let value = shape
            .observe(&context, &leaves, &index, &mut cursor)
            .unwrap();
        let Value::Adt {
            name,
            variant,
            discriminant,
            is_option,
            fields,
        } = value
        else {
            panic!("struct observation must retain its ADT carrier");
        };
        assert_eq!(name, "fixture::Pair");
        assert_eq!(variant, 0);
        assert_eq!(discriminant, 0);
        assert!(!is_option);
        assert_eq!(
            fields
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            vec!["left", "right", "marker"]
        );
        assert!(matches!(&fields[2].1, Value::Unit));
        assert_eq!(cursor, 2);
        for i in 0..2 {
            assert_eq!(
                fields[i].1.integer().unwrap().0,
                context
                    .apply(Op::Select, &[leaves[i].clone(), index.clone()])
                    .unwrap()
            );
        }
        assert_ne!(
            fields[0].1.integer().unwrap().0,
            fields[1].1.integer().unwrap().0
        );
        let mut repeated_cursor = 0;
        let repeated = shape
            .observe(&context, &leaves, &index, &mut repeated_cursor)
            .unwrap();
        let Value::Adt {
            fields: repeated_fields,
            ..
        } = repeated
        else {
            unreachable!();
        };
        assert_eq!(
            fields[0].1.integer().unwrap().0,
            repeated_fields[0].1.integer().unwrap().0
        );
        assert!(
            shape
                .observe(&context, &leaves[..1], &index, &mut 0)
                .is_err()
        );
    }

    #[test]
    fn zero_sized_slice_extent_and_values_preserve_full_target_length() {
        for bits in [32, 64] {
            let max = (1_u128 << bits) - 1;
            assert_eq!(slice_extent_limit(bits, 0).unwrap(), max);
            assert_eq!(slice_extent_limit(bits, 1).unwrap(), max >> 1);
            assert_eq!(slice_extent_limit(bits, 4).unwrap(), (max >> 1) / 4);
            let context = Context::default();
            let length = symbolic::integer(&context, max, bits, false);
            assert!(validate_terms(&context, bits, &[], &length, &[]).is_ok());
            let shape = CompositeShape::Tuple(vec![
                CompositeShape::Tuple(vec![]),
                CompositeShape::Array(vec![]),
            ]);
            let mut leaves = Vec::new();
            shape.leaves(&mut leaves);
            assert!(leaves.is_empty());
            let index = context.bit_vector(max - 1, bits).unwrap();
            let mut cursor = 0;
            let value = shape.observe(&context, &[], &index, &mut cursor).unwrap();
            assert!(matches!(value, Value::Tuple(fields)
                if matches!(&fields[0], Value::Unit)
                && matches!(&fields[1], Value::Elements(values) if values.is_empty())));
            assert_eq!(cursor, 0);
        }
        assert!(slice_extent_limit(0, 0).is_err());
        assert!(slice_extent_limit(129, 0).is_err());
    }

    #[test]
    fn composite_metadata_rejects_foreign_sorts_lengths_and_leaf_inventories() {
        let context = Context::default();
        let kinds = [
            ScalarSliceElement::Integer {
                bits: 16,
                signed: false,
            },
            ScalarSliceElement::Bool,
        ];
        let length = symbolic::integer(&context, 2, 64, false);
        let leaves: Vec<_> = kinds
            .iter()
            .enumerate()
            .map(|(i, leaf)| {
                context
                    .symbol(
                        i as u32,
                        Sort::Array(
                            Box::new(Sort::BitVec(64)),
                            Box::new(scalar_slice_sort(*leaf).unwrap()),
                        ),
                    )
                    .unwrap()
            })
            .collect();
        assert!(validate_terms(&context, 64, &kinds, &length, &leaves).is_ok());
        assert!(validate_terms(&context, 64, &kinds, &length, &leaves[..1]).is_err());
        let mut swapped = leaves.clone();
        swapped.swap(0, 1);
        assert!(validate_terms(&context, 64, &kinds, &length, &swapped).is_err());
        assert!(validate_terms(&context, 32, &kinds, &length, &leaves).is_err());
        let signed = symbolic::integer(&context, 2, 64, true);
        assert!(validate_terms(&context, 64, &kinds, &signed, &leaves).is_err());
        let other = Context::default();
        let foreign = symbolic::integer(&other, 2, 64, false);
        assert!(validate_terms(&context, 64, &kinds, &foreign, &leaves).is_err());
        let foreign_leaf = other.symbol(0, leaves[0].sort().clone()).unwrap();
        let bad = [foreign_leaf, leaves[1].clone()];
        assert!(validate_terms(&context, 64, &kinds, &length, &bad).is_err());
    }

    #[test]
    fn composite_occurrences_reconstruct_distinct_slots_and_stable_selected_values() {
        let context = Context::default();
        let kind = ScalarSliceElement::Integer {
            bits: 16,
            signed: false,
        };
        let shape = CompositeShape::Tuple(vec![
            CompositeShape::Primitive(kind),
            CompositeShape::Array(vec![
                CompositeShape::Primitive(kind),
                CompositeShape::Primitive(kind),
            ]),
            CompositeShape::Tuple(Vec::new()),
        ]);
        let mut types = Vec::new();
        shape.leaves(&mut types);
        assert_eq!(types, vec![kind; 3]);
        let leaves: Vec<_> = (0..3)
            .map(|i| {
                context
                    .symbol(
                        i,
                        Sort::Array(Box::new(Sort::BitVec(64)), Box::new(Sort::BitVec(16))),
                    )
                    .unwrap()
            })
            .collect();
        let index = context.symbol(3, Sort::BitVec(64)).unwrap();
        let mut cursor = 0;
        let first = shape
            .observe(&context, &leaves, &index, &mut cursor)
            .unwrap();
        assert_eq!(cursor, 3);
        let Value::Tuple(fields) = &first else {
            panic!("tuple reconstruction")
        };
        let Value::Elements(inner) = &fields[1] else {
            panic!("array reconstruction")
        };
        let terms = [&fields[0], &inner[0], &inner[1]].map(|v| v.integer().unwrap().0);
        for (i, term) in terms.iter().enumerate() {
            assert_eq!(
                term.symbols(),
                std::collections::BTreeSet::from([i as u32, 3])
            );
        }
        assert_ne!(terms[0], terms[1]);
        assert_ne!(terms[1], terms[2]);
        assert!(matches!(fields[2], Value::Unit));
        let mut cursor = 0;
        let Value::Tuple(second) = shape
            .observe(&context, &leaves, &index, &mut cursor)
            .unwrap()
        else {
            panic!("stable reconstruction")
        };
        assert_eq!(
            fields[0].integer().unwrap().0,
            second[0].integer().unwrap().0
        );
        let mut cursor = 0;
        assert!(
            shape
                .observe(&context, &leaves[..2], &index, &mut cursor)
                .is_err()
        );
    }
}
