//! One Engine-wide counter. Domain wrappers retain their own failure and payment policies.
use std::cell::Cell;

#[derive(Default)]
pub(super) struct SharedSteps {
    used: Cell<usize>,
}

pub(super) enum ReserveFailure {
    Overflow,
    Limit,
}

impl SharedSteps {
    pub(super) fn used(&self) -> usize {
        self.used.get()
    }

    pub(super) fn checked_add_commit(&self, cost: usize) -> Option<usize> {
        let next = self.used.get().checked_add(cost)?;
        self.used.set(next);
        Some(next)
    }

    pub(super) fn saturating_add_commit(&self, cost: usize) -> usize {
        let next = self.used.get().saturating_add(cost);
        self.used.set(next);
        next
    }

    // Preserve the three existing ordinary +=1 policies until overflow changes separately.
    pub(super) fn legacy_increment(&self) -> usize {
        let next = self.used.get() + 1;
        self.used.set(next);
        next
    }

    pub(super) fn reserve_checked(
        &self,
        cost: usize,
        limit: usize,
    ) -> Result<usize, ReserveFailure> {
        let next = self
            .used
            .get()
            .checked_add(cost)
            .ok_or(ReserveFailure::Overflow)?;
        if next > limit {
            return Err(ReserveFailure::Limit);
        }
        self.used.set(next);
        Ok(next)
    }

    pub(super) fn mark_max(&self) {
        self.used.set(usize::MAX);
    }

    #[cfg(test)]
    pub(super) fn set_for_test(&self, used: usize) {
        self.used.set(used);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn borrowed_services_share_the_counter_and_reservation_denial_does_not_commit() {
        let counter = SharedSteps::default();
        let first = &counter;
        let second = &counter;
        assert_eq!(first.checked_add_commit(3), Some(3));
        assert_eq!(second.reserve_checked(2, 5).ok(), Some(5));
        assert!(matches!(
            first.reserve_checked(1, 5),
            Err(ReserveFailure::Limit)
        ));
        assert_eq!(second.used(), 5);
        assert_eq!(second.checked_add_commit(1), Some(6));
    }

    #[test]
    fn arithmetic_policies_preserve_the_existing_overflow_commit_behavior() {
        let counter = SharedSteps::default();
        counter.set_for_test(usize::MAX - 1);
        assert_eq!(counter.checked_add_commit(1), Some(usize::MAX));
        assert_eq!(counter.checked_add_commit(1), None);
        assert_eq!(counter.used(), usize::MAX);
        assert!(matches!(
            counter.reserve_checked(1, usize::MAX),
            Err(ReserveFailure::Overflow)
        ));
        assert_eq!(counter.saturating_add_commit(1), usize::MAX);
        counter.set_for_test(1);
        counter.mark_max();
        assert_eq!(counter.used(), usize::MAX);
    }
}
