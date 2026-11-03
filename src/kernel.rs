//! The kernel state (the signature `Sigma`) and its public API for adding
//! declarations.
//!
//! The rest of the kernel is split by topic, in the order the text presents it:
//! - [`crate::typecheck`]: `Infer`, `Check`, and `infer_sort`.
//! - [`crate::reduction`]: `Whnf` with beta, delta, iota; `Normalize`; definitional equality.
//! - [`crate::inductive`]: checking inductive declarations and generating recursors.

use std::collections::HashMap;

use crate::{
    declaration::{ConstructorSpec, Decl, DeclKind, InductiveInfo, InductiveSpec},
    inductive::recursor::recursor_namespace,
    term::{
        const_term, var,
        Term::{self, Sort},
    },
};

pub type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug, Default)]
pub struct Kernel {
    /// Every constant in the signature, with its type.
    pub decls: HashMap<String, Decl>,
    /// The checked inductive types, by the name of their type former.
    pub(crate) inductives: HashMap<String, InductiveInfo>,
}

impl Kernel {
    pub fn empty() -> Self {
        Self::default()
    }

    /// A kernel with `Nat` and `Eq` already declared.
    pub fn standard() -> Self {
        let mut k = Self::empty();
        k.add_inductive(InductiveSpec {
            name: "Nat".into(),
            params: vec![],
            indices: vec![],
            universe_level: 1,
            constructors: vec![
                ConstructorSpec {
                    name: "Nat.zero".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
                ConstructorSpec {
                    name: "Nat.succ".into(),
                    fields: vec![("n".into(), const_term("Nat"))],
                    result_indices: vec![],
                },
            ],
        })
        .expect("Nat is valid");
        k.add_inductive(InductiveSpec {
            name: "Eq".into(),
            params: vec![("A".into(), Sort(1)), ("a".into(), var("A"))],
            indices: vec![("b".into(), var("A"))],
            universe_level: 0,
            constructors: vec![ConstructorSpec {
                name: "Eq.refl".into(),
                fields: vec![],
                result_indices: vec![var("a")],
            }],
        })
        .expect("Eq is valid");
        k
    }

    pub fn type_of_const(&self, name: &str) -> Option<&Term> {
        self.decls.get(name).map(|d| &d.ty)
    }

    /// The checked data of the inductive type `name`, if it exists.
    pub fn inductive(&self, name: &str) -> Option<&InductiveInfo> {
        self.inductives.get(name)
    }

    /// Adds `name : ty` without a body.
    pub fn axiom(&mut self, name: &str, ty: Term) -> Result<()> {
        self.ensure_new(name)?;
        self.infer_sort(&vec![], &ty)?;
        self.decls.insert(
            name.into(),
            Decl {
                ty,
                kind: DeclKind::Axiom,
            },
        );
        Ok(())
    }

    /// Adds `name : ty := body` after checking `body : ty`.
    pub fn define(&mut self, name: &str, ty: Term, body: Term) -> Result<()> {
        self.ensure_new(name)?;
        self.infer_sort(&vec![], &ty)?;
        self.check(&vec![], &body, &ty)?;
        self.decls.insert(
            name.into(),
            Decl {
                ty,
                kind: DeclKind::Definition(body),
            },
        );
        Ok(())
    }

    /// Fails if `name` is already declared, or lies in the namespace `I.rec...`
    /// reserved for the recursors of an existing inductive type `I`.
    pub(crate) fn ensure_new(&self, name: &str) -> Result<()> {
        if self
            .inductives
            .keys()
            .any(|inductive| name.starts_with(&recursor_namespace(inductive)))
        {
            return Err("cannot shadow a generated recursor namespace".into());
        }
        if self.decls.contains_key(name) {
            Err(format!("duplicate declaration: {name}"))
        } else {
            Ok(())
        }
    }
}
