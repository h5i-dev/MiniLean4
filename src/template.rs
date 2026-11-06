use crate::kernel::Result;
use std::collections::HashMap;

use crate::term::{app, lam, Term};

/// A tactic builds a proof template; every hole must be filled before kernel checking.
#[derive(Clone, Debug)]
pub enum Template {
    Fixed(Term),
    Hole(usize),
    App(Box<Template>, Box<Template>),
    Lam(String, Term, Box<Template>),
}

impl Template {
    /// Substitutes the solved holes and leaves the unsolved ones in place.
    /// Used to display the partial proof term while a proof is in progress.
    pub fn instantiate(&self, slots: &HashMap<usize, Template>) -> Template {
        match self {
            Template::Fixed(t) => Template::Fixed(t.clone()),
            Template::Hole(i) => match slots.get(i) {
                Some(solution) => solution.instantiate(slots),
                None => Template::Hole(*i),
            },
            Template::App(f, a) => Template::App(
                Box::new(f.instantiate(slots)),
                Box::new(a.instantiate(slots)),
            ),
            Template::Lam(x, a, b) => Template::Lam(x.clone(), a.clone(), Box::new(b.instantiate(slots))),
        }
    }

    pub fn materialize(&self, slots: &HashMap<usize, Template>) -> Result<Term> {
        match self {
            Template::Fixed(t) => Ok(t.clone()),
            Template::Hole(i) => slots
                .get(i)
                .ok_or_else(|| format!("unsolved goal ?{i}"))?
                .materialize(slots),
            Template::App(f, a) => Ok(app(f.materialize(slots)?, a.materialize(slots)?)),
            Template::Lam(x, a, b) => Ok(lam(x, a.clone(), b.materialize(slots)?)),
        }
    }
}
