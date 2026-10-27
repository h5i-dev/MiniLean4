/*
(x : A) ∈ Γ（most recently added one）
───────────────────────────────────── Var
Γ ⊢ x : A

───────────────────────── Sort
Γ ⊢ Sort u : Sort (u+1)

Γ ⊢ A : Sort u     Γ, x:A ⊢ B : Sort v
────────────────────────────────────── Pi
Γ ⊢ Π(x:A). B : Sort (max u v)

Γ ⊢ A : Sort u     Γ, x:A ⊢ t : B
────────────────────────────────── Lam
Γ ⊢ λ(x:A). t : Π(x:A). B
*/

#[derive(Clone, Debug, PartialEq, Eq)]
enum Term {
    Sort(u64),
    Var(String),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>)
}

type Context = Vec<(String, Term)>;

pub fn infer(gamma: &Context, t: &Term) -> Result<Term, ()> {
    match t {
        Term::Sort(u) => Ok(Term::Sort(u + 1)),
        Term::Var(x) => {
            for (y, a) in gamma.iter().rev() {
                if y == x {
                    return Ok(a.clone());
                }
            }
            Err(())
        },
        Term::Pi(x, a, b) => {
            if let Ok(u) = infer_sort(gamma, a) {
                let mut new_gamma = gamma.clone();
                new_gamma.push((x.clone(), *a.clone()));
                if let Ok(v) = infer_sort(gamma, b) {
                    return Ok(Term::Sort(std::cmp::max(u, v)));
                }
            }
            Err(())
        },
        Term::Lam(x, a, b) => {
            if let Ok(_) = infer_sort(gamma, a) {
                let mut new_gamma = gamma.clone();
                new_gamma.push((x.clone(), *a.clone()));
                return Ok(Term::Pi(x.clone(), a.clone(), b.clone()));
            }
            Err(())
        },
        Term::App(_, _) => todo!()
    }
}

pub fn infer_sort(gamma: &Context, t: &Term) -> Result<u64, ()> {
    match infer(gamma, t) {
        Ok(s) => match s {
            Term::Sort(u) => Ok(u),
            _ => Err(())
        },
        Err(_) => Err(()),
    }
}

pub fn fv(t: &Term) -> std::collections::HashSet<String> {
    match t {
        Term::Sort(_) => std::collections::HashSet::new(),
        Term::Var(x) => vec![x.clone()].into_iter().collect::<std::collections::HashSet<String>>(),
        Term::App(t_1, t_2) => {
            let mut fv_1 = fv(t_1);
            fv_1.extend(fv(t_2));
            fv_1
        },
        Term::Pi(x, a, b) => {
            let mut fv_1 = fv(a);
            fv_1.extend(fv(b));
            fv_1.remove(x);
            fv_1
        },
        Term::Lam(x, a, b) => {
            let mut fv_1 = fv(a);
            fv_1.extend(fv(b));
            fv_1.remove(x);
            fv_1
        },
    }
}

pub fn fresh(s: &Term, b: &Term, x: &String, y: &String) -> String {
    let mut fv_s = fv(s);
    fv_s.extend(fv(b));
    fv_s.extend([x.clone()].into_iter());
    let mut z = y.clone();
    while fv_s.contains(&z) {
        z = z + "'";
    }
    z
}

pub fn substitute (t: &Term, x: &String, s: &Term) -> Term {
    match t {
        Term::Var(y) => {
            if y == x {
                s.clone()
            } else {
                Term::Var(y.clone())
            }
        },
        Term::Sort(y) => Term::Sort(*y),
        Term::App(t_1, t_2) => {
            Term::App(
                Box::new(substitute(t_1, x, s)), 
                Box::new(substitute(t_2, x, s))
            )
        },
        Term::Pi(y, a, b) => {
            if y == x {
                Term::Pi(
                    x.clone(), 
                    Box::new(substitute(a, x, s)), 
                    Box::new(substitute(b, x, s))
                )
            } else {
                if !fv(s).contains(y) {
                    Term::Pi(
                        y.clone(), 
                        Box::new(substitute(a, x, s)), 
                        Box::new(substitute(b, x, s))
                    )
                } else {
                    let z = fresh(s, b, x, y);
                    Term::Pi(
                        z.clone(), 
                        Box::new(substitute(a, x, s)), 
                        Box::new(substitute(&substitute(b, y, &Term::Var(z)), x, s)), 
                    )
                }
            }
        },
        Term::Lam(y, a, b) => {
            if y == x {
                Term::Pi(
                    x.clone(), 
                    Box::new(substitute(a, x, s)), 
                    Box::new(substitute(b, x, s))
                )
            } else {
                if !fv(s).contains(y) {
                    Term::Pi(
                        y.clone(), 
                        Box::new(substitute(a, x, s)), 
                        Box::new(substitute(b, x, s))
                    )
                } else {
                    let z = fresh(s, b, x, y);
                    Term::Pi(
                        z.clone(), 
                        Box::new(substitute(a, x, s)), 
                        Box::new(substitute(&substitute(b, y, &Term::Var(z)), x, s)), 
                    )
                }
            }
        },
    }
}

pub fn whfn(t: &mut Term) {
    while true {
        if let Term::App(t_1, t_2) = t {
        }
        
    }
}



pub fn get_pos_in_context(gamma: &Context, var_name: &String) -> Option<usize> {
    for (i, (s, _, )) in gamma.into_iter().rev().enumerate() {
        if s == var_name {
            return Some(i);
        }
    }
    
    None
}

pub fn alpha(a: &Term, b: &Term, gamma_a: &Context, gamma_b: &Context) -> bool {
    match (a, b) {
        (Term::Sort(u), Term::Sort(v)) => u == v,
        (Term::Var(x), Term::Var(y)) => {
            let i = get_pos_in_context(gamma_a, x);
            let j = get_pos_in_context(gamma_b, y);
            match (i, j) {
                (Some(i), Some(j)) => i == j,
                (None, None) => x == y,
                _ => false
            }
        },
        (Term::Pi(x, a_1, b_1), Term::Pi(y, a_2, b_2)) => {
            if !alpha(a_1, a_2, gamma_a, gamma_b) {
                return false;
            }
            return alpha(b_1, b_2, gamma_a, gamma_b);
        },
        (Term::Lam(x, a_1, a_2), Term::Lam(y, b_1, b_2)) => {
            if !alpha(a_1, a_2, gamma_a, gamma_b) {
                return false;
            }
            return alpha(b_1, b_2, gamma_a, gamma_b);
        },
        _ => false
    }
}