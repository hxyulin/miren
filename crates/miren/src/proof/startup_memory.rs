use super::*;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) struct StaticLocation {
    pub(super) definition: DefId,
    pub(super) offset: u64,
    pub(super) bytes: u64,
}

impl StaticLocation {
    pub(super) fn overlaps(self, other: Self) -> bool {
        self.definition == other.definition
            && self.offset < other.offset + other.bytes
            && other.offset < self.offset + self.bytes
    }
}

#[derive(Clone, Debug)]
pub(super) struct OwnedRegion {
    pub(super) key: u64,
    pub(super) certificate: usize,
    pub(super) slots: usize,
    pub(super) payload: Option<Value>,
    pub(super) construction: Option<usize>,
    pub(super) sealed: bool,
    pub(super) live: bool,
}

#[derive(Clone, Default)]
pub(super) struct Memory {
    pub(super) incoming_byte_roots: Vec<super::byte_copy_provenance::IncomingByteRoot>,
    pub(super) byte_copy_opaque: bool,
    pub(super) mutable_u16: Rc<Vec<super::mutable_u16::Backing>>,
    pub(super) mutable_hierarchy: Option<usize>,
    allocations: Rc<Vec<Option<Value>>>,
    pub(super) owned_regions: Rc<Vec<OwnedRegion>>,
    pub(super) missing_places: initialized_places::MissingPlaces,
    pub(super) initialized_owners: Rc<Vec<(usize, initialized_places::Owner)>>,
    pub(super) startup_values: std::collections::HashMap<StaticLocation, Value>,
    pub(super) startup_invalidated: bool,
    pub(super) isolated_static_types: std::collections::HashMap<StaticLocation, usize>,
    pub(super) startup_overwritten: Vec<StaticLocation>,
    pub(super) static_uninitialized: Vec<usize>,
}

impl Memory {
    pub(super) fn activation_supported(
        &self,
        flow: &super::activation_flow::Flow,
    ) -> Result<(), String> {
        if matches!(flow, super::activation_flow::Flow::Unarmed) {
            return Ok(());
        }
        if !self.incoming_byte_roots.is_empty()
            || !self.owned_regions.is_empty()
            || !self.initialized_owners.is_empty()
            || !self.startup_values.is_empty()
            || !self.isolated_static_types.is_empty()
            || !self.startup_overwritten.is_empty()
            || !self.static_uninitialized.is_empty()
        {
            return Err(
                "armed activation startup, owned or byte Memory clone is unsupported".into(),
            );
        }
        Ok(())
    }

    pub(super) fn activation_charge_clone(
        &self,
        flow: &super::activation_flow::Flow,
    ) -> Result<(), String> {
        if matches!(flow, super::activation_flow::Flow::Unarmed) {
            return Ok(());
        }
        self.activation_supported(flow)?;
        // Allocations, owned regions, u16 backings and initialization owners are Rc vectors.
        // No payload clone occurs; detached backing vectors are charged at mutation seams.
        flow.charge(4)?;
        flow.charge_masks(&self.missing_places)
    }

    pub(super) fn activation_storage_slots(
        &self,
        flow: &super::activation_flow::Flow,
    ) -> Result<usize, String> {
        if matches!(flow, super::activation_flow::Flow::Unarmed) {
            return Ok(self.storage_slots());
        }
        self.activation_supported(flow)?;
        flow.charge(2)?; // Actual new initialization-owner length read and slot-sum addition.
        // storage_slots makes four distinct backing-vector passes; its owner sum
        // visits owners but only reads each immutable frames vector's length.
        flow.charge(self.mutable_u16.len().saturating_mul(5))?;
        for backing in self.mutable_u16.iter() {
            if backing.interval.is_some() {
                return Err("armed activation storage namespace is unsupported".into());
            }
            match &backing.phase {
                super::mutable_u16_children::Phase::Idle
                | super::mutable_u16_children::Phase::Pending { .. } => {}
                super::mutable_u16_children::Phase::Active { .. } => {
                    return Err("armed activation storage namespace is unsupported".into());
                }
            }
            if let Some(hierarchy) = &backing.hierarchy {
                hierarchy.activation_charge_storage(flow)?;
            }
        }
        Ok(self.storage_slots())
    }

    pub(super) fn storage_slots(&self) -> usize {
        self.allocations
            .len()
            .saturating_add(self.owned_regions.iter().map(|region| region.slots).sum())
            .saturating_add(self.initialized_owners.len())
            .saturating_add(self.mutable_u16.len())
            .saturating_add(usize::from(self.mutable_hierarchy.is_some()))
            .saturating_add(
                self.mutable_u16
                    .iter()
                    .filter_map(|backing| backing.hierarchy.as_ref())
                    .map(super::mutable_hierarchy::Hierarchy::storage_slots)
                    .sum::<usize>(),
            )
            .saturating_add(
                self.mutable_u16
                    .iter()
                    .filter_map(|backing| backing.interval.as_ref())
                    .map(super::mutable_interval::Descriptor::storage_slots)
                    .sum::<usize>(),
            )
            .saturating_add(
                self.mutable_u16
                    .iter()
                    .map(|backing| {
                        let frames = match &backing.phase {
                            super::mutable_u16_children::Phase::Active { frames } => frames.len(),
                            super::mutable_u16_children::Phase::Idle
                            | super::mutable_u16_children::Phase::Pending { .. } => 0,
                        };
                        // The existing owner slot covers Scalar's one column and Product's
                        // first column (or empty owner). Fuse extra columns into this existing
                        // backing pass; no additional Rust allocation or traversal is created.
                        let additional = match &backing.data {
                            super::mutable_u16::Storage::Scalar(_) => 0,
                            super::mutable_u16::Storage::Product(columns) => {
                                columns.len().saturating_sub(1)
                            }
                        };
                        frames.saturating_add(additional)
                    })
                    .sum::<usize>(),
            )
    }

    pub(super) fn owned_region(
        &self,
        key: u64,
        certificate: usize,
    ) -> Result<&OwnedRegion, String> {
        self.owned_regions
            .iter()
            .find(|region| region.key == key && region.certificate == certificate && region.live)
            .ok_or_else(|| "owned region is unavailable or has different type identity".into())
    }

    pub(super) fn owned_region_mut(
        &mut self,
        key: u64,
        certificate: usize,
    ) -> Result<&mut OwnedRegion, String> {
        Rc::make_mut(&mut self.owned_regions)
            .iter_mut()
            .find(|region| region.key == key && region.certificate == certificate && region.live)
            .ok_or_else(|| "owned region is unavailable or has different type identity".into())
    }

    pub(super) fn issue_owned_region(
        &mut self,
        key: u64,
        certificate: usize,
    ) -> Result<(), String> {
        self.issue_owned_region_with_slots(key, certificate, 1)
    }

    pub(super) fn issue_owned_region_with_slots(
        &mut self,
        key: u64,
        certificate: usize,
        slots: usize,
    ) -> Result<(), String> {
        if slots == 0 || slots > super::memory::MAX_ALLOCATIONS.saturating_sub(self.storage_slots())
        {
            return Err("owned region exceeds the cumulative 512-storage budget".into());
        }
        if self.owned_regions.iter().any(|region| region.key == key) {
            return Err("owned region identity has already been issued".into());
        }
        Rc::make_mut(&mut self.owned_regions).push(OwnedRegion {
            key,
            certificate,
            slots,
            payload: None,
            construction: None,
            sealed: false,
            live: true,
        });
        Ok(())
    }

    pub(super) fn initialize_owned_region(
        &mut self,
        key: u64,
        certificate: usize,
        payload: Value,
    ) -> Result<(), String> {
        let region = self.owned_region_mut(key, certificate)?;
        if region.sealed || region.payload.is_some() {
            return Err("owned constructor payload has already been initialized".into());
        }
        region.payload = Some(payload);
        Ok(())
    }

    pub(super) fn seal_owned_region(&mut self, key: u64, certificate: usize) -> Result<(), String> {
        let region = self.owned_region_mut(key, certificate)?;
        if region.sealed || region.payload.is_none() {
            return Err("owned constructor requires exactly one initialized payload".into());
        }
        region.sealed = true;
        Ok(())
    }

    pub(super) fn owned_region_payload(
        &self,
        key: u64,
        certificate: usize,
    ) -> Result<&Value, String> {
        let region = self.owned_region(key, certificate)?;
        if !region.sealed {
            return Err("owned constructor has not sealed its payload".into());
        }
        region
            .payload
            .as_ref()
            .ok_or_else(|| "owned payload is unavailable".into())
    }

    pub(super) fn retire_owned_region(
        &mut self,
        key: u64,
        certificate: usize,
    ) -> Result<(), String> {
        self.owned_region_payload(key, certificate)?;
        self.owned_region_mut(key, certificate)?.live = false;
        Ok(())
    }

    pub(super) fn startup_initializer_available(&self, location: StaticLocation) -> bool {
        !self.startup_invalidated
            && !self
                .startup_overwritten
                .iter()
                .any(|other| location.overlaps(*other))
            && !self
                .startup_values
                .keys()
                .any(|other| location.overlaps(*other))
    }

    pub(super) fn invalidate_startup(&mut self) {
        self.startup_values.clear();
        self.isolated_static_types.clear();
        self.startup_overwritten.clear();
        self.startup_invalidated = true;
    }
}

impl Deref for Memory {
    type Target = Vec<Option<Value>>;

    fn deref(&self) -> &Self::Target {
        &self.allocations
    }
}

impl DerefMut for Memory {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Rc::make_mut(&mut self.allocations)
    }
}

impl From<Vec<Option<Value>>> for Memory {
    fn from(allocations: Vec<Option<Value>>) -> Self {
        Self {
            allocations: Rc::new(allocations),
            ..Self::default()
        }
    }
}

impl FromIterator<Option<Value>> for Memory {
    fn from_iter<T: IntoIterator<Item = Option<Value>>>(values: T) -> Self {
        Vec::from_iter(values).into()
    }
}

impl<'a> IntoIterator for &'a Memory {
    type Item = &'a Option<Value>;
    type IntoIter = std::slice::Iter<'a, Option<Value>>;

    fn into_iter(self) -> Self::IntoIter {
        self.allocations.iter()
    }
}

impl<'a> IntoIterator for &'a mut Memory {
    type Item = &'a mut Option<Value>;
    type IntoIter = std::slice::IterMut<'a, Option<Value>>;

    fn into_iter(self) -> Self::IntoIter {
        Rc::make_mut(&mut self.allocations).iter_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atomic_location(index: usize) -> StaticLocation {
        StaticLocation {
            definition: DefId {
                krate: rustc_span::def_id::LOCAL_CRATE,
                index: rustc_span::def_id::DefIndex::from_usize(index),
            },
            offset: 0,
            bytes: 4,
        }
    }

    #[test]
    fn branch_reads_share_allocations_and_writes_preserve_other_branches() {
        let original: Memory = vec![
            Some(Value::Reference {
                allocation: 1,
                projection: Vec::new(),
                mutable: true,
            }),
            Some(Value::Unit),
        ]
        .into();
        let mut branch = original.clone();
        assert!(Rc::ptr_eq(&original.allocations, &branch.allocations));
        assert_eq!(branch.iter().count(), 2);
        assert!(Rc::ptr_eq(&original.allocations, &branch.allocations));
        branch[1] = None;
        branch.push(Some(Value::Uninitialized));
        assert!(!Rc::ptr_eq(&original.allocations, &branch.allocations));
        assert!(matches!(original[1], Some(Value::Unit)));
        assert!(branch[1].is_none());
        assert_eq!(original.len(), 2);
        assert_eq!(branch.len(), 3);
        for memory in [&original, &branch] {
            assert!(matches!(
                memory[0],
                Some(Value::Reference { allocation: 1, .. })
            ));
        }
    }

    #[test]
    fn owned_region_phases_and_retirement_preserve_branch_identity() {
        let mut original = Memory::default();
        original.issue_owned_region(17, 3).unwrap();
        assert!(original.owned_region_payload(17, 3).is_err());
        assert!(original.seal_owned_region(17, 3).is_err());
        assert!(original.owned_region(17, 4).is_err());
        assert!(original.issue_owned_region(17, 4).is_err());
        original
            .initialize_owned_region(17, 3, Value::Unit)
            .unwrap();
        assert!(
            original
                .initialize_owned_region(17, 3, Value::Unit)
                .is_err()
        );
        original.seal_owned_region(17, 3).unwrap();
        assert!(original.seal_owned_region(17, 3).is_err());
        let mut branch = original.clone();
        assert!(Rc::ptr_eq(&original.owned_regions, &branch.owned_regions));
        branch.retire_owned_region(17, 3).unwrap();
        assert!(branch.owned_region_payload(17, 3).is_err());
        assert!(branch.retire_owned_region(17, 3).is_err());
        assert!(branch.issue_owned_region(17, 3).is_err());
        assert!(matches!(
            original.owned_region_payload(17, 3),
            Ok(Value::Unit)
        ));
        assert!(!Rc::ptr_eq(&original.owned_regions, &branch.owned_regions));
        assert!(Rc::ptr_eq(&original.allocations, &branch.allocations));
        assert_eq!(original.len(), 0);
        assert_eq!(original.storage_slots(), 1);
    }

    #[test]
    fn owned_regions_share_the_existing_storage_budget_with_frames() {
        let mut memory: Memory = vec![Some(Value::Unit); 511].into();
        memory.issue_owned_region(1, 0).unwrap();
        assert_eq!(memory.storage_slots(), 512);
        assert!(memory.issue_owned_region(2, 0).is_err());
        let mut memory: Memory = vec![Some(Value::Unit); 512].into();
        assert!(memory.issue_owned_region(1, 0).is_err());
    }

    #[test]
    fn nominal_owned_regions_charge_each_original_payload_node() {
        let mut memory: Memory = vec![Some(Value::Unit); 509].into();
        memory.issue_owned_region_with_slots(1, 0, 3).unwrap();
        assert_eq!(memory.storage_slots(), 512);
        assert!(memory.issue_owned_region(2, 0).is_err());
        assert!(
            Memory::default()
                .issue_owned_region_with_slots(1, 0, 0)
                .is_err()
        );
        assert!(
            Memory::default()
                .issue_owned_region_with_slots(1, 0, 513)
                .is_err()
        );
    }

    #[test]
    fn mutating_iteration_detaches_shared_allocations() {
        let original: Memory = vec![Some(Value::Uninitialized), None].into();
        let mut branch = original.clone();
        for slot in &mut branch {
            *slot = Some(Value::Unit);
        }
        assert!(matches!(original[0], Some(Value::Uninitialized)));
        assert!(original[1].is_none());
        assert!(branch.iter().all(|slot| matches!(slot, Some(Value::Unit))));
        assert!(!Rc::ptr_eq(&original.allocations, &branch.allocations));
    }

    #[test]
    fn unique_allocation_writes_reuse_the_vector() {
        let mut memory: Memory = vec![Some(Value::Uninitialized)].into();
        let address = Rc::as_ptr(&memory.allocations);
        memory[0] = Some(Value::Unit);
        assert_eq!(address, Rc::as_ptr(&memory.allocations));
        assert!(matches!(memory[0], Some(Value::Unit)));
    }

    #[test]
    fn startup_history_updates_and_invalidation_remain_branch_local() {
        let location = atomic_location(7);
        let other_location = atomic_location(8);
        let mut original: Memory = vec![Some(Value::Unit)].into();
        original.startup_values.insert(location, Value::Unit);
        original.static_uninitialized.push(4);
        let mut branch = original.clone();
        branch.static_uninitialized.clear();
        assert_eq!(original.static_uninitialized, vec![4]);
        branch.startup_values.insert(location, Value::Uninitialized);
        branch.startup_values.insert(other_location, Value::Unit);
        assert!(matches!(original.startup_values[&location], Value::Unit));
        assert!(!original.startup_values.contains_key(&other_location));
        branch.invalidate_startup();
        assert!(branch.startup_values.is_empty());
        assert!(branch.startup_invalidated);
        assert!(!original.startup_invalidated);
        assert_eq!(original.startup_values.len(), 1);
        let invalidated_branch = branch.clone();
        assert!(invalidated_branch.startup_invalidated);
        assert!(invalidated_branch.startup_values.is_empty());
        assert!(Rc::ptr_eq(&original.allocations, &branch.allocations));
        assert!(Rc::ptr_eq(
            &branch.allocations,
            &invalidated_branch.allocations
        ));
    }
}
