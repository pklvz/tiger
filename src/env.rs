use crate::{ast::WithPos, error::Error};
use std::{
    borrow::Borrow,
    collections::{HashMap, LinkedList},
};

pub struct Env<'a, T>(pub(crate) HashMap<&'a str, LinkedList<T>>);

impl<'a, T> Env<'a, T> {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn insert(&mut self, name: &'a str, value: T) {
        self.0.entry(name).or_default().push_front(value);
    }

    pub fn remove(&mut self, name: &str) {
        let values = self.0.get_mut(name).unwrap();
        values.pop_front().unwrap();
        if values.is_empty() {
            self.0.remove(name);
        }
    }

    pub fn get<'b, K>(&self, name: &'b WithPos<K>) -> Result<&T, Error>
    where
        K: Borrow<str>,
        &'b WithPos<K>: Into<WithPos<String>>,
    {
        self.0
            .get(name.inner.borrow())
            .map(|values| values.front().unwrap())
            .ok_or_else(|| Error::NotDefined(name.into()))
    }

    pub fn get_mut<'b, K>(&mut self, name: &'b WithPos<K>) -> Result<&mut T, Error>
    where
        K: Borrow<str>,
        &'b WithPos<K>: Into<WithPos<String>>,
    {
        self.0
            .get_mut(name.inner.borrow())
            .map(|values| values.front_mut().unwrap())
            .ok_or_else(|| Error::NotDefined(name.into()))
    }
}
