//! Type inference and checking (`Infer` and `Check` in the text).

use crate::{
    declaration::Context,
    kernel::{Kernel, Result},
    substitution::{all_names, fresh, subst},
    term::{var, Term},
};

/// Before extending `ctx` with a binder `x`, renames `x` in `body` if `ctx`
/// already binds `x`. Otherwise the new entry would shadow the old one and the
/// types in `ctx` that mention the old `x` would be misread (see "A Pitfall:
/// Variable Capture in Contexts" in the text).
fn rename_binder_if_needed(ctx: &Context, x: &str, body: &Term) -> (String, Term) {
    if !ctx.iter().any(|(name, _)| name == x) {
        return (x.into(), body.clone());
    }
    let mut used = all_names(body);
    for (name, ty) in ctx {
        used.insert(name.clone());
        used.extend(all_names(ty));
    }
    let renamed = fresh(x, &used);
    let renamed_body = subst(body, x, &var(&renamed));
    (renamed, renamed_body)
}

impl Kernel {
    /// Infers the type of `t` and requires it to be a universe `Sort u`.
    /// Returns `u`.
    pub fn infer_sort(&self, ctx: &Context, t: &Term) -> Result<u64> {
        match self.whnf(&self.infer(ctx, t)?)? {
            Term::Sort(u) => Ok(u),
            other => Err(format!("expected a type, got {other:?}")),
        }
    }

    /// `Gamma |- t : ?`
    pub fn infer(&self, ctx: &Context, t: &Term) -> Result<Term> {
        match t {
            // T-Sort
            Term::Sort(u) => Ok(Term::Sort(u.checked_add(1).ok_or("universe overflow")?)),
            // T-Var
            Term::Var(x) => ctx
                .iter()
                .rev()
                .find(|(name, _)| name == x)
                .map(|(_, ty)| ty.clone())
                .ok_or_else(|| format!("unbound local: {x}")),
            // T-Const
            Term::Const(c) => self
                .decls
                .get(c)
                .map(|decl| decl.ty.clone())
                .ok_or_else(|| format!("unknown constant: {c}")),
            // T-Pi: Sort 0 is impredicative.
            Term::Pi(x, domain, body) => {
                let domain_level = self.infer_sort(ctx, domain)?;
                let (x, body) = rename_binder_if_needed(ctx, x, body);
                let mut extended = ctx.clone();
                extended.push((x, (**domain).clone()));
                let body_level = self.infer_sort(&extended, &body)?;
                Ok(Term::Sort(if body_level == 0 {
                    0
                } else {
                    domain_level.max(body_level)
                }))
            }
            // T-Lam
            Term::Lam(x, domain, body) => {
                self.infer_sort(ctx, domain)?;
                let (x, body) = rename_binder_if_needed(ctx, x, body);
                let mut extended = ctx.clone();
                extended.push((x.clone(), (**domain).clone()));
                let body_type = self.infer(&extended, &body)?;
                Ok(Term::Pi(x, domain.clone(), Box::new(body_type)))
            }
            // T-App
            Term::App(f, a) => match self.whnf(&self.infer(ctx, f)?)? {
                Term::Pi(x, domain, codomain) => {
                    self.check(ctx, a, &domain)?;
                    Ok(subst(&codomain, &x, a))
                }
                ty => Err(format!("application of non-function: {ty:?}")),
            },
        }
    }

    /// `Gamma |- t : expected`, using T-Conv to compare the inferred type.
    pub fn check(&self, ctx: &Context, t: &Term, expected: &Term) -> Result<()> {
        self.infer_sort(ctx, expected)?;
        let actual = self.infer(ctx, t)?;
        if self.is_def_eq(&actual, expected)? {
            Ok(())
        } else {
            Err(format!(
                "type mismatch: actual {actual:?}, expected {expected:?}"
            ))
        }
    }
}
