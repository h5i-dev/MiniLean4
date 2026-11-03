//! Reduction (`Whnf` with beta, delta, iota and `Normalize` in the text) and the
//! definitional equality `==` built on them.

use std::collections::HashMap;

use crate::{
    declaration::{ConstructorInfo, Decl, DeclKind, InductiveInfo, RecursiveFieldInfo, RecursorInfo},
    kernel::{Kernel, Result},
    substitution::{alpha, subst, subst_many},
    term::{apps, spine, var, Term},
};

/// The maximum number of reduction steps per top-level call, so that a kernel
/// bug cannot loop forever.
const REDUCTION_FUEL: usize = 20000;

impl Kernel {
    /// Definitional equality `a == b`: the normal forms are alpha-equivalent.
    pub fn is_def_eq(&self, a: &Term, b: &Term) -> Result<bool> {
        let mut fuel = REDUCTION_FUEL;
        self.is_def_eq_with_fuel(a, b, &mut fuel)
    }

    /// Weak head normal form.
    pub fn whnf(&self, t: &Term) -> Result<Term> {
        let mut fuel = REDUCTION_FUEL;
        self.whnf_with_fuel(t, &mut fuel)
    }

    /// Full normal form.
    pub fn normalize(&self, t: &Term) -> Result<Term> {
        let mut fuel = REDUCTION_FUEL;
        self.normalize_with_fuel(t, &mut fuel)
    }

    fn is_def_eq_with_fuel(&self, a: &Term, b: &Term, fuel: &mut usize) -> Result<bool> {
        Ok(alpha(
            &self.normalize_with_fuel(a, fuel)?,
            &self.normalize_with_fuel(b, fuel)?,
        ))
    }

    /// Algorithm "Whnf with delta and iota": write `t` as a spine `h a_1 ... a_n`, and
    /// reduce at the head until no rule applies.
    fn whnf_with_fuel(&self, t: &Term, fuel: &mut usize) -> Result<Term> {
        let mut t = t.clone();
        loop {
            if *fuel == 0 {
                return Err("reduction fuel exhausted".into());
            }
            *fuel -= 1;
            let (head, args) = spine(&t);
            let reduced = match head {
                // beta: (fun x. b) a_1 a_2 ... a_n  ~>  b[x := a_1] a_2 ... a_n
                Term::Lam(x, _, body) if !args.is_empty() => Some(apps(
                    subst(&body, &x, &args[0]),
                    args[1..].iter().cloned(),
                )),
                Term::Const(c) => match self.decls.get(&c) {
                    // delta: c as  ~>  d as   where (c := d) in Sigma
                    Some(Decl {
                        kind: DeclKind::Definition(body),
                        ..
                    }) => Some(apps(body.clone(), args)),
                    // iota: I.rec ps M ms is (c_j ps' as)  ~>  m_j as hs
                    Some(Decl {
                        kind: DeclKind::Recursor(recursor),
                        ..
                    }) => self.iota_reduce(&c, recursor, &args, fuel)?,
                    _ => None,
                },
                _ => None,
            };
            match reduced {
                Some(next) => t = next,
                None => return Ok(t),
            }
        }
    }

    /// One iota-step for the recursor application `recursor_name args`:
    ///
    /// ```text
    /// I.rec_v ps M ms is (c_j ps' as) extras  ~>  m_j as hs extras
    /// ```
    ///
    /// Returns `None` if the term is stuck: too few arguments, or the major
    /// premise does not reduce to a constructor applied to all its arguments.
    fn iota_reduce(
        &self,
        recursor_name: &str,
        recursor: &RecursorInfo,
        args: &[Term],
        fuel: &mut usize,
    ) -> Result<Option<Term>> {
        let major_index = recursor.major_argument_index;
        if args.len() <= major_index {
            return Ok(None);
        }
        let Some(inductive) = self.inductives.get(&recursor.inductive) else {
            return Ok(None);
        };
        let (major_head, major_args) = spine(&self.whnf_with_fuel(&args[major_index], fuel)?);
        let Term::Const(constructor_name) = major_head else {
            return Ok(None);
        };
        let Some((j, constructor)) = inductive
            .constructors
            .iter()
            .enumerate()
            .find(|(_, c)| c.name == constructor_name)
        else {
            return Ok(None);
        };
        let num_params = inductive.params.len();
        if major_args.len() != num_params + constructor.fields.len() {
            return Ok(None);
        }
        // The parameters ps' of the constructor must match the recursor's ps.
        for (constructor_param, recursor_param) in major_args.iter().zip(&args[..num_params]) {
            if !self.is_def_eq_with_fuel(constructor_param, recursor_param, fuel)? {
                return Ok(None);
            }
        }
        let field_values = &major_args[num_params..];
        let induction_hypotheses = constructor.recursive_fields.iter().map(|recursive_field| {
            induction_hypothesis(
                recursor_name,
                inductive,
                constructor,
                recursive_field,
                args,
                field_values,
            )
        });
        let minor_premise = args[num_params + 1 + j].clone();
        Ok(Some(apps(
            minor_premise,
            field_values
                .iter()
                .cloned()
                .chain(induction_hypotheses)
                .chain(args[major_index + 1..].iter().cloned()),
        )))
    }

    fn normalize_with_fuel(&self, t: &Term, fuel: &mut usize) -> Result<Term> {
        match self.whnf_with_fuel(t, fuel)? {
            Term::Pi(x, a, b) => Ok(Term::Pi(
                x,
                Box::new(self.normalize_with_fuel(&a, fuel)?),
                Box::new(self.normalize_with_fuel(&b, fuel)?),
            )),
            Term::Lam(x, a, b) => Ok(Term::Lam(
                x,
                Box::new(self.normalize_with_fuel(&a, fuel)?),
                Box::new(self.normalize_with_fuel(&b, fuel)?),
            )),
            Term::App(f, a) => {
                // Normalizing the arguments may expose a new redex at the head,
                // e.g. a recursor whose major premise became a constructor.
                let rebuilt = Term::App(
                    Box::new(self.normalize_with_fuel(&f, fuel)?),
                    Box::new(self.normalize_with_fuel(&a, fuel)?),
                );
                let reduced = self.whnf_with_fuel(&rebuilt, fuel)?;
                if reduced == rebuilt {
                    Ok(rebuilt)
                } else {
                    self.normalize_with_fuel(&reduced, fuel)
                }
            }
            other => Ok(other),
        }
    }
}

/// The induction hypothesis passed to the minor premise for one recursive
/// field `a_k : Pi (ys : Bs). I ps ss`:
///
/// ```text
/// h_k = fun (ys : Bs). I.rec_v ps M ms ss (a_k ys)
/// ```
///
/// `Bs` and `ss` are stated in terms of the declared parameter and field names,
/// so they are instantiated with the actual parameters and field values first.
fn induction_hypothesis(
    recursor_name: &str,
    inductive: &InductiveInfo,
    constructor: &ConstructorInfo,
    recursive_field: &RecursiveFieldInfo,
    recursor_args: &[Term],
    field_values: &[Term],
) -> Term {
    let mut instantiation: HashMap<String, Term> = HashMap::new();
    for ((param, _), value) in inductive.params.iter().zip(recursor_args) {
        instantiation.insert(param.clone(), value.clone());
    }
    for ((field, _), value) in constructor.fields.iter().zip(field_values) {
        instantiation.insert(field.clone(), value.clone());
    }
    let argument_binders: Vec<(String, Term)> = recursive_field
        .argument_binders
        .iter()
        .map(|(y, ty)| (y.clone(), subst_many(ty, &instantiation)))
        .collect();
    let target_indices = recursive_field
        .target_indices
        .iter()
        .map(|s| subst_many(s, &instantiation));
    // a_k ys
    let applied_field = apps(
        field_values[recursive_field.constructor_field_index].clone(),
        argument_binders.iter().map(|(y, _)| var(y)),
    );
    // I.rec_v ps M ms, then ss and (a_k ys).
    let num_leading_args = inductive.params.len() + 1 + inductive.constructors.len();
    let recursive_call = apps(
        Term::Const(recursor_name.to_string()),
        recursor_args[..num_leading_args]
            .iter()
            .cloned()
            .chain(target_indices)
            .chain(std::iter::once(applied_field)),
    );
    argument_binders
        .iter()
        .rev()
        .fold(recursive_call, |body, (y, ty)| {
            Term::Lam(y.clone(), Box::new(ty.clone()), Box::new(body))
        })
}
