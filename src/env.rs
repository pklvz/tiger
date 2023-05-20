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

    pub fn insert(&mut self, name: &'a str, val: T) {
        self.0.entry(name).or_default().push_front(val);
    }

    pub fn remove(&mut self, name: &str) {
        let vals = self.0.get_mut(name).unwrap();
        vals.pop_front().unwrap();
        if vals.is_empty() {
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
            .map(|vals| vals.front().unwrap())
            .ok_or_else(|| Error::NotDefined(name.into()))
    }

    pub fn get_mut(&mut self, name: &str) -> Option<&mut T> {
        self.0.get_mut(name).map(|vals| vals.front_mut().unwrap())
    }
}
