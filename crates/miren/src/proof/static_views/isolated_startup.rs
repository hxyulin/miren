//! Typed history under the separately recorded absence of external Rust storage mutations.
use super::*;
use startup_memory::StaticLocation;
use symbolic::MemoryProjection;

impl<'tcx> Engine<'tcx> {
    pub(in crate::proof) fn isolated_static_read(
        &self,
        view: static_views::StaticView<'tcx>,
        state: &State,
    ) -> Result<Option<Value>, String> {
        if !self.isolated_startup || state.memory.startup_invalidated {
            return Ok(None);
        }
        let location = self.isolated_static_location(view)?;
        if let Some(id) = state.memory.isolated_static_types.get(&location) {
            let views = self.static_views.borrow();
            let stored_view = views
                .get(*id)
                .ok_or("isolated static store type unavailable")?;
            if stored_view.ty == view.ty {
                let value = state
                    .memory
                    .startup_values
                    .get(&location)
                    .ok_or("isolated static store value unavailable")?;
                self.static_store_value(view.ty, value, state, 0, &mut 0)?;
                self.validate_tracked_value(value, state)?;
                return Ok(Some(value.clone()));
            }
        }
        if let Some((parent, parent_view, path)) = self.isolated_stored_parent(view, state)? {
            let mut value = state
                .memory
                .startup_values
                .get(&parent)
                .ok_or("isolated stored parent value unavailable")?
                .clone();
            self.static_store_value(parent_view.ty, &value, state, 0, &mut 0)?;
            for projection in path {
                value = self.memory_projection(value, &projection, &state.conditions)?;
            }
            self.static_store_value(view.ty, &value, state, 0, &mut 0)?;
            self.validate_tracked_value(&value, state)?;
            return Ok(Some(value));
        }
        if state
            .memory
            .startup_overwritten
            .iter()
            .any(|other| location.overlaps(*other))
        {
            return Err(
                "isolated static read overlaps a write without an exact typed value".into(),
            );
        }
        Ok(None)
    }

    pub(in crate::proof) fn store_isolated_static(
        &self,
        view: static_views::StaticView<'tcx>,
        value: &Value,
        state: &mut State,
    ) -> Result<bool, String> {
        if !self.isolated_startup {
            return Ok(false);
        }
        if state.memory.startup_invalidated {
            return Ok(true);
        }
        let location = self.isolated_static_location(view)?;
        if location.bytes == 0 {
            return Err("isolated static history requires a nonzero typed footprint".into());
        }
        if let Some((parent, parent_view, path)) = self.isolated_stored_parent(view, state)? {
            let mut stored = state
                .memory
                .startup_values
                .get(&parent)
                .ok_or("isolated stored parent value unavailable")?
                .clone();
            self.static_store_value(parent_view.ty, &stored, state, 0, &mut 0)?;
            self.validate_tracked_value(&stored, state)?;
            self.write_projection(&mut stored, &path, value.clone(), &state.conditions)?;
            self.static_store_value(parent_view.ty, &stored, state, 0, &mut 0)?;
            self.validate_tracked_value(&stored, state)?;
            state.memory.startup_values.insert(parent, stored);
            return Ok(true);
        }
        self.forget_isolated_static(location, state)?;
        if state.memory.startup_values.len() >= startup::MAX_STARTUP_LOCATIONS {
            return Err("isolated static history exceeds the 128-location budget".into());
        }
        let Value::StaticView { id, .. } = self.intern_static_view(view)? else {
            return Err("isolated static typed identity unavailable".into());
        };
        state.memory.startup_values.insert(location, value.clone());
        state.memory.isolated_static_types.insert(location, id);
        Ok(true)
    }

    pub(in crate::proof) fn retire_isolated_static(
        &self,
        view: static_views::StaticView<'tcx>,
        state: &mut State,
    ) -> Result<bool, String> {
        if !self.isolated_startup {
            return Ok(false);
        }
        if !state.memory.startup_invalidated {
            self.forget_isolated_static(self.isolated_static_location(view)?, state)?;
        }
        Ok(true)
    }

    fn forget_isolated_static(
        &self,
        location: StaticLocation,
        state: &mut State,
    ) -> Result<(), String> {
        if state.memory.startup_overwritten.len() >= startup::MAX_STARTUP_LOCATIONS
            && !state.memory.startup_overwritten.contains(&location)
        {
            return Err("isolated static writes exceed the 128-location budget".into());
        }
        let overlaps: Vec<_> = state
            .memory
            .startup_values
            .keys()
            .copied()
            .filter(|other| location.overlaps(*other))
            .collect();
        for other in overlaps {
            state.memory.startup_values.remove(&other);
            state.memory.isolated_static_types.remove(&other);
        }
        if !state.memory.startup_overwritten.contains(&location) {
            state.memory.startup_overwritten.push(location);
        }
        Ok(())
    }

    fn isolated_stored_parent(
        &self,
        view: StaticView<'tcx>,
        state: &State,
    ) -> Result<Option<(StaticLocation, StaticView<'tcx>, Vec<MemoryProjection>)>, String> {
        if view.ty != view.certified || view.kind != ViewKind::Place {
            return Ok(None);
        }
        let location = self.isolated_static_location(view)?;
        let end = location
            .offset
            .checked_add(location.bytes)
            .ok_or("isolated field footprint overflow")?;
        let views = self.static_views.borrow();
        let mut selected = None;
        for (parent, identity) in &state.memory.isolated_static_types {
            if parent.definition != location.definition || parent.offset > location.offset {
                continue;
            }
            let parent_end = parent
                .offset
                .checked_add(parent.bytes)
                .ok_or("isolated parent footprint overflow")?;
            if parent_end < end {
                continue;
            }
            let parent_view = *views
                .get(*identity)
                .ok_or("isolated stored parent type unavailable")?;
            if parent_view.original != view.original
                || parent_view.ty != parent_view.certified
                || (*parent == location && parent_view.ty == view.ty)
            {
                continue;
            }
            let Some(path) = self.isolated_field_path(
                parent_view.ty,
                location.offset - parent.offset,
                view.ty,
                0,
                &mut 0,
            )?
            else {
                continue;
            };
            if selected.is_some() {
                return Err("isolated field has multiple retained parent identities".into());
            }
            selected = Some((*parent, parent_view, path));
        }
        Ok(selected)
    }

    fn isolated_field_path(
        &self,
        ty: Ty<'tcx>,
        offset: u64,
        target: Ty<'tcx>,
        depth: usize,
        visited: &mut usize,
    ) -> Result<Option<Vec<MemoryProjection>>, String> {
        if depth >= 8 || *visited >= 256 {
            return Err("isolated field path exceeds depth or value budget".into());
        }
        *visited += 1;
        if ty == target && offset == 0 {
            return Ok(Some(Vec::new()));
        }
        let fields = match ty.kind() {
            ty::Adt(def, args) if def.is_struct() => def
                .non_enum_variant()
                .fields
                .iter()
                .map(|field| field.ty(self.tcx, args))
                .collect::<Vec<_>>(),
            ty::Tuple(fields) => fields.iter().map(ty::Unnormalized::new_wip).collect(),
            _ => return Ok(None),
        };
        if fields.len() > 128 {
            return Err("isolated field path exceeds the field budget".into());
        }
        let layout = self.static_layout(ty)?;
        let mut selected = None;
        for (index, field) in fields.into_iter().enumerate() {
            let field = self
                .tcx
                .try_normalize_erasing_regions(ty::TypingEnv::fully_monomorphized(), field)
                .map_err(|error| format!("isolated field type normalization failed: {error:?}"))?;
            let start = layout.fields.offset(index).bytes();
            let size = self.static_layout(field)?.size.bytes();
            if offset < start || offset - start >= size {
                continue;
            }
            if let Some(mut path) =
                self.isolated_field_path(field, offset - start, target, depth + 1, visited)?
            {
                path.insert(0, MemoryProjection::Field(index));
                if selected.replace(path).is_some() {
                    return Err("isolated field path has ambiguous compiler offsets".into());
                }
            }
        }
        Ok(selected)
    }

    fn isolated_static_location(
        &self,
        view: static_views::StaticView<'tcx>,
    ) -> Result<StaticLocation, String> {
        Ok(StaticLocation {
            definition: view.static_id,
            offset: view.offset,
            bytes: self.static_layout(view.ty)?.size.bytes(),
        })
    }

    pub(in crate::proof) fn isolated_pointer_atomic_store(
        &self,
        receiver: &Value,
        receiver_ty: Ty<'tcx>,
        pointer_ty: Ty<'tcx>,
        value: Value,
        state: &mut State,
    ) -> Result<(), String> {
        self.static_atomic_storage(receiver, receiver_ty, pointer_ty, state)?;
        let mut view = self.static_view(receiver, state)?;
        view.ty = pointer_ty;
        view.certified = pointer_ty;
        view.kind = static_views::ViewKind::Place;
        view.writable = true;
        self.static_store_value(pointer_ty, &value, state, 0, &mut 0)?;
        self.retain_static_store_references(&value, state)?;
        if !self.store_isolated_static(view, &value, state)? {
            return Err("isolated pointer store requires its explicit entry domain".into());
        }
        Ok(())
    }
}
