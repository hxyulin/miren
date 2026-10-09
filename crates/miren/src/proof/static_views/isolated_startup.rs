//! Typed history under the separately recorded absence of external Rust storage mutations.
use super::*;
use startup_memory::StaticLocation;

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
            if stored_view.ty != view.ty {
                return Err("isolated static read has an incompatible stored type".into());
            }
            let value = state
                .memory
                .startup_values
                .get(&location)
                .ok_or("isolated static store value unavailable")?;
            self.static_store_value(view.ty, value, state, 0, &mut 0)?;
            self.validate_tracked_value(value, state)?;
            return Ok(Some(value.clone()));
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
