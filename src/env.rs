use std::collections::{HashMap, LinkedList};

pub struct Env<'a, T>(pub(crate) HashMap<&'a str, LinkedList<T>>);

impl<'a, T> Env<'a, T> {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn insert(&mut self, name: &'a str, val: T) {
        self.0.entry(name).or_default().push_front(val);
    }

    pub fn remove(&mut self, name: &str) -> Option<T> {
        let vals = self.0.get_mut(name)?;
        let val = vals.pop_front().unwrap();
        if vals.is_empty() {
            self.0.remove(name);
        }
        Some(val)
    }

    pub fn get(&self, name: &str) -> Option<&T> {
        self.0.get(name).map(|vals| vals.front().unwrap())
    }

    pub fn get_mut(&mut self, name: &str) -> Option<&mut T> {
        self.0.get_mut(name).map(|vals| vals.front_mut().unwrap())
    }
}
