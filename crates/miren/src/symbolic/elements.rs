use super::Value;
use std::ops::{Deref, DerefMut};
use std::rc::Rc;

#[derive(Clone, Debug, Default)]
pub struct Elements(Rc<Vec<Value>>);

impl Elements {
    /// Host COW bookkeeping only; this observation grants no guest ownership or access.
    pub(crate) fn is_shared(&self) -> bool {
        Rc::strong_count(&self.0) > 1
    }
}

impl Deref for Elements {
    type Target = Vec<Value>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Elements {
    fn deref_mut(&mut self) -> &mut Self::Target {
        Rc::make_mut(&mut self.0)
    }
}

impl From<Vec<Value>> for Elements {
    fn from(fields: Vec<Value>) -> Self {
        Self(Rc::new(fields))
    }
}

impl FromIterator<Value> for Elements {
    fn from_iter<T: IntoIterator<Item = Value>>(values: T) -> Self {
        Vec::from_iter(values).into()
    }
}

impl IntoIterator for Elements {
    type Item = Value;
    type IntoIter = std::vec::IntoIter<Value>;

    fn into_iter(self) -> Self::IntoIter {
        Rc::unwrap_or_clone(self.0).into_iter()
    }
}

impl<'a> IntoIterator for &'a Elements {
    type Item = &'a Value;
    type IntoIter = std::slice::Iter<'a, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a> IntoIterator for &'a mut Elements {
    type Item = &'a mut Value;
    type IntoIter = std::slice::IterMut<'a, Value>;

    fn into_iter(self) -> Self::IntoIter {
        Rc::make_mut(&mut self.0).iter_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{Context, integer};

    fn elements(value: &Value) -> &Elements {
        let Value::Elements(elements) = value else {
            panic!("expected an initialized array");
        };
        elements
    }

    #[test]
    fn repeated_rows_share_storage_and_writes_detach_only_the_changed_path() {
        let context = Context::default();
        let row = Value::Elements(vec![integer(&context, 0, 32, false); 6].into());
        assert_eq!(row.owned_repeat_size(), Some(7));
        assert_eq!(row.owned_repeat_clone_size(), Some(1));
        let original = Value::Elements(vec![row; 40].into());
        assert!(Rc::ptr_eq(
            &elements(&elements(&original)[0]).0,
            &elements(&elements(&original)[39]).0
        ));
        let mut changed = original.clone();
        let Value::Elements(rows) = &mut changed else {
            panic!("expected an initialized array");
        };
        let Value::Elements(row) = &mut rows[0] else {
            panic!("expected an initialized row");
        };
        row[0] = integer(&context, 17, 32, false);
        assert!(!Rc::ptr_eq(&elements(&original).0, &elements(&changed).0));
        assert!(!Rc::ptr_eq(
            &elements(&elements(&original)[0]).0,
            &elements(&elements(&changed)[0]).0
        ));
        assert!(Rc::ptr_eq(
            &elements(&elements(&original)[39]).0,
            &elements(&elements(&changed)[39]).0
        ));
        assert_eq!(
            elements(&elements(&original)[0])[0].integer().unwrap().0,
            integer(&context, 0, 32, false).integer().unwrap().0
        );
        assert_eq!(
            elements(&elements(&changed)[0])[0].integer().unwrap().0,
            integer(&context, 17, 32, false).integer().unwrap().0
        );
        // The 40x6 initialized matrix retains two vectors: 40 row handles and six scalars.
        assert_eq!(
            elements(&original).len() + elements(&elements(&original)[0]).len(),
            46
        );
    }

    #[test]
    fn consuming_shared_arrays_and_mutating_iteration_preserve_other_owners() {
        let context = Context::default();
        let original: Elements = vec![integer(&context, 23, 16, false)].into();
        let mut consumed: Vec<_> = original.clone().into_iter().collect();
        consumed[0] = Value::Unit;
        let mut changed = original.clone();
        for value in &mut changed {
            *value = Value::Unit;
        }
        assert!(matches!(changed[0], Value::Unit));
        assert_eq!(
            original[0].integer().unwrap().0,
            integer(&context, 23, 16, false).integer().unwrap().0
        );
    }
}
