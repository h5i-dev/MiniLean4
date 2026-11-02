use std::collections::HashMap;
use crate::kernel::Result;

use crate::term::{Term, app, lam};

/// A tactic builds a proof template; every hole must be filled before kernel checking.
#[derive(Clone,Debug)]
pub enum Template { Fixed(Term), Hole(usize), App(Box<Template>,Box<Template>), Lam(String,Term,Box<Template>) }

impl Template {
    pub fn materialize(&self, slots:&HashMap<usize,Template>)->Result<Term>{
        match self {
            Template::Fixed(t)=>Ok(t.clone()),
            Template::Hole(i)=>slots.get(i).ok_or_else(||format!("unsolved goal ?{i}"))?
                .materialize(slots),
            Template::App(f,a)=>Ok(app(f.materialize(slots)?,a.materialize(slots)?)),
            Template::Lam(x,a,b)=>Ok(lam(x,a.clone(),b.materialize(slots)?)),
        }
    }
}