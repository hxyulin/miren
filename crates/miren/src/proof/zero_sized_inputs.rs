//! Bounded exact zero-sized input shapes, without symbolic scalar slots.
use super::*;
use symbolic::input::{InputKind, InputShape, InputValue};

const MAX_ZERO_SIZED_NODES: usize = 2048;
const MAX_ZERO_SIZED_ARRAY: u64 = 256;

impl<'tcx> Engine<'tcx> {
    pub(super) fn zero_sized_argument(&mut self, ty: Ty<'tcx>) -> Result<Option<Value>, String> {
        let layout = match self
            .tcx
            .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        {
            Ok(layout) => layout,
            Err(_) => return Ok(None),
        };
        if layout.size.bytes() != 0 || layout.is_uninhabited() {
            return Ok(None);
        }
        let mut cache = self.zero_sized_inputs.clone();
        let mut nodes = self.zero_sized_input_nodes;
        let Some(shape) = self.zero_sized_shape(ty, self.input_depth, &mut cache, &mut nodes)?
        else {
            return Ok(None);
        };
        if self.input_values >= MAX_INPUT_VALUES {
            return Err("input shape exceeds the 512-value budget".to_owned());
        }
        // One deterministic payload occupies one input slot. Descriptor construction has its own
        // bounded node budget; it does not hide an unbounded eager aggregate expansion.
        self.input_values += 1;
        self.zero_sized_inputs = cache;
        self.zero_sized_input_nodes = nodes;
        let input = InputValue {
            shape,
            start: 0,
            seed: self.terms.boolean(false),
        };
        // Materializing one level keeps ordinary unit and fieldless struct values concrete.
        // Nested shapes retain shared descriptors; their slots are zero, so no symbols are emitted.
        Ok(Some(input.materialize()?))
    }

    fn zero_sized_shape(
        &self,
        ty: Ty<'tcx>,
        depth: usize,
        cache: &mut std::collections::HashMap<Ty<'tcx>, std::rc::Rc<InputShape>>,
        nodes: &mut usize,
    ) -> Result<Option<std::rc::Rc<InputShape>>, String> {
        if depth >= MAX_INPUT_DEPTH {
            return Err("zero-sized input shape exceeds 16 levels of nesting".into());
        }
        if let Some(shape) = cache.get(&ty) {
            if depth + shape.height > MAX_INPUT_DEPTH {
                return Err("zero-sized input shape exceeds 16 levels of nesting".into());
            }
            return Ok(Some(shape.clone()));
        }
        let layout = match self
            .tcx
            .layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))
        {
            Ok(layout) => layout,
            Err(_) => return Ok(None),
        };
        if layout.size.bytes() != 0 || layout.is_uninhabited() {
            return Ok(None);
        }
        Self::zero_sized_node(nodes)?;
        let (kind, height) = match ty.kind() {
            ty::Tuple(fields) if fields.is_empty() => (InputKind::Unit, 1),
            ty::Tuple(fields) => {
                let mut shapes = Vec::new();
                for field in fields.iter() {
                    Self::zero_sized_node(nodes)?;
                    let Some(shape) = self.zero_sized_shape(field, depth + 1, cache, nodes)? else {
                        return Ok(None);
                    };
                    shapes.push(shape);
                }
                let height = 1 + shapes.iter().map(|shape| shape.height).max().unwrap_or(0);
                (InputKind::Tuple(shapes), height)
            }
            ty::Array(element, length) => {
                let Some(count) = length.try_to_target_usize(self.tcx) else {
                    return Ok(None);
                };
                if count > MAX_ZERO_SIZED_ARRAY {
                    return Err("fixed array input exceeds 256 elements".into());
                }
                // Validate the element domain too: an empty array does not establish a model for
                // references, unions or uninhabited element types.
                let Some(element) = self.zero_sized_shape(*element, depth + 1, cache, nodes)?
                else {
                    return Ok(None);
                };
                for _ in 0..count {
                    Self::zero_sized_node(nodes)?;
                }
                let height = 1 + element.height;
                (
                    InputKind::Array {
                        element,
                        count: count as usize,
                    },
                    height,
                )
            }
            ty::Adt(def, args)
                if def.is_struct()
                    && self.tcx.lang_items().get(LangItem::UnsafeCell) != Some(def.did()) =>
            {
                let mut fields = Vec::new();
                for field in &def.non_enum_variant().fields {
                    Self::zero_sized_node(nodes)?;
                    let field_ty = self
                        .tcx
                        .try_normalize_erasing_regions(
                            ty::TypingEnv::fully_monomorphized(),
                            field.ty(self.tcx, args),
                        )
                        .map_err(|error| {
                            format!("zero-sized input field normalization failed: {error:?}")
                        })?;
                    let Some(shape) = self.zero_sized_shape(field_ty, depth + 1, cache, nodes)?
                    else {
                        return Ok(None);
                    };
                    fields.push((field.name.as_str().to_owned(), shape));
                }
                let height = 1 + fields
                    .iter()
                    .map(|(_, shape)| shape.height)
                    .max()
                    .unwrap_or(0);
                (
                    InputKind::Struct {
                        name: self.tcx.def_path_str(def.did()),
                        fields,
                    },
                    height,
                )
            }
            // Layout size alone cannot establish a value, variant or reference provenance.
            _ => return Ok(None),
        };
        let shape = std::rc::Rc::new(InputShape {
            kind,
            slots: 0,
            height,
        });
        cache.insert(ty, shape.clone());
        Ok(Some(shape))
    }

    fn zero_sized_node(nodes: &mut usize) -> Result<(), String> {
        if *nodes >= MAX_ZERO_SIZED_NODES {
            return Err("zero-sized input descriptors exceed the 2048-node budget".into());
        }
        *nodes += 1;
        Ok(())
    }
}
