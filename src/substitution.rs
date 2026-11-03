//! Free variables, capture-avoiding substitution, and alpha-equivalence.

use std::collections::{HashMap, HashSet};

use crate::term::{app, var, Term};

/// The free variables `FV(t)`.
pub fn fv(t: &Term) -> HashSet<String> {
    match t {
        Term::Sort(_) | Term::Const(_) => HashSet::new(),
        Term::Var(x) => HashSet::from([x.clone()]),
        Term::App(f, a) => {
            let mut names = fv(f);
            names.extend(fv(a));
            names
        }
        Term::Pi(x, a, b) | Term::Lam(x, a, b) => {
            let mut names = fv(a);
            let mut body_names = fv(b);
            body_names.remove(x);
            names.extend(body_names);
            names
        }
    }
}

/// Every variable name in `t`, bound or free.
pub fn all_names(t: &Term) -> HashSet<String> {
    match t {
        Term::Sort(_) | Term::Const(_) => HashSet::new(),
        Term::Var(x) => HashSet::from([x.clone()]),
        Term::App(f, a) => {
            let mut names = all_names(f);
            names.extend(all_names(a));
            names
        }
        Term::Pi(x, a, b) | Term::Lam(x, a, b) => {
            let mut names = all_names(a);
            names.extend(all_names(b));
            names.insert(x.clone());
            names
        }
    }
}

/// A name based on `hint` that is not in `avoid`, made by appending primes.
pub fn fresh(hint: &str, avoid: &HashSet<String>) -> String {
    let mut name = hint.to_string();
    while avoid.contains(&name) {
        name.push('\'');
    }
    name
}

/// Capture-avoiding substitution `t[x := replacement]`.
///
/// Under a binder `y`, there are three cases:
/// 1. `y = x`, or `x` is not free in the body: the body is unchanged.
/// 2. `y` is not free in `replacement`: substitute in the body directly.
/// 3. Otherwise substituting would capture `y`, so first rename `y` to a
///    fresh `z` in the body, then substitute.
pub fn subst(t: &Term, x: &str, replacement: &Term) -> Term {
    match t {
        Term::Sort(_) | Term::Const(_) => t.clone(),
        Term::Var(y) => {
            if y == x {
                replacement.clone()
            } else {
                t.clone()
            }
        }
        Term::App(f, a) => app(subst(f, x, replacement), subst(a, x, replacement)),
        Term::Pi(y, domain, body) | Term::Lam(y, domain, body) => {
            let substituted_domain = subst(domain, x, replacement);
            let (renamed_binder, substituted_body) = if y == x || !fv(body).contains(x) {
                (y.clone(), (**body).clone())
            } else if !fv(replacement).contains(y) {
                (y.clone(), subst(body, x, replacement))
            } else {
                let mut avoid = all_names(body);
                avoid.extend(all_names(domain));
                avoid.extend(all_names(replacement));
                avoid.insert(x.to_string());
                let z = fresh(y, &avoid);
                let body_with_z = subst(body, y, &var(&z));
                (z, subst(&body_with_z, x, replacement))
            };
            let domain = Box::new(substituted_domain);
            let body = Box::new(substituted_body);
            if matches!(t, Term::Pi(..)) {
                Term::Pi(renamed_binder, domain, body)
            } else {
                Term::Lam(renamed_binder, domain, body)
            }
        }
    }
}

/// Simultaneous capture-avoiding substitution `t[x_1 := v_1, ..., x_n := v_n]`.
///
/// Each `x_i` is first replaced by a fresh placeholder, and only then are the
/// placeholders replaced by the values, so that the free variables of one
/// value are never touched by a later substitution.
pub fn subst_many(t: &Term, replacements: &HashMap<String, Term>) -> Term {
    let mut used = all_names(t);
    let mut keys: Vec<&String> = replacements.keys().collect();
    keys.sort();
    for (name, value) in replacements {
        used.insert(name.clone());
        used.extend(all_names(value));
    }
    let mut staged = t.clone();
    let mut placeholders = vec![];
    for key in keys {
        let placeholder = fresh("__subst", &used);
        used.insert(placeholder.clone());
        staged = subst(&staged, key, &var(&placeholder));
        placeholders.push((placeholder, replacements[key].clone()));
    }
    for (placeholder, value) in placeholders {
        staged = subst(&staged, &placeholder, &value);
    }
    staged
}

/// Alpha-equivalence: equality up to renaming of bound variables.
///
/// A bound variable is compared by its distance to its binder (as with de
/// Bruijn indices); a free variable is compared by name.
pub fn alpha(a: &Term, b: &Term) -> bool {
    fn binder_distance(bound: &[String], x: &str) -> Option<usize> {
        bound.iter().rev().position(|name| name == x)
    }
    fn go(a: &Term, b: &Term, bound_a: &mut Vec<String>, bound_b: &mut Vec<String>) -> bool {
        match (a, b) {
            (Term::Sort(u), Term::Sort(v)) => u == v,
            (Term::Const(c), Term::Const(d)) => c == d,
            (Term::Var(x), Term::Var(y)) => {
                match (binder_distance(bound_a, x), binder_distance(bound_b, y)) {
                    (Some(i), Some(j)) => i == j,
                    (None, None) => x == y,
                    _ => false,
                }
            }
            (Term::App(f, a), Term::App(g, b)) => {
                go(f, g, bound_a, bound_b) && go(a, b, bound_a, bound_b)
            }
            (Term::Pi(x, a, b), Term::Pi(y, c, d)) | (Term::Lam(x, a, b), Term::Lam(y, c, d)) => {
                if !go(a, c, bound_a, bound_b) {
                    return false;
                }
                bound_a.push(x.clone());
                bound_b.push(y.clone());
                let bodies_equal = go(b, d, bound_a, bound_b);
                bound_a.pop();
                bound_b.pop();
                bodies_equal
            }
            _ => false,
        }
    }
    go(a, b, &mut vec![], &mut vec![])
}
