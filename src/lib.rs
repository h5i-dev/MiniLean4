use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Sort(u64),
    Var(String),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>)
}

pub type Context = Vec<(String, Term)>;

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
                let (x_p, b_p) = fresh_from_context(gamma, x, b);
                let mut new_gamma = gamma.clone();
                new_gamma.push((x_p.clone(), *a.clone()));
                if let Ok(v) = infer_sort(&new_gamma, &b_p) {
                    return Ok(Term::Sort(std::cmp::max(u, v)));
                }
            }
            Err(())
        },
        Term::Lam(x, a, s) => {
            if let Ok(_) = infer_sort(gamma, a) {
                let (x_p, s_p) = fresh_from_context(gamma, x, s);
                let mut new_gamma = gamma.clone();
                new_gamma.push((x_p.clone(), *a.clone()));
                if let Ok(b) = infer(&new_gamma, &s_p) {
                    return Ok(Term::Pi(x_p.clone(), a.clone(), Box::new(b)));
                }
            }
            Err(())
        },
        Term::App(f, a) => {
            if let Ok(f_p) = infer(gamma, f) {
                let t = normalize(&f_p);
                if let Term::Pi(x, a_cap, b) = t {
                    if let Ok(true) = check(gamma, a, &a_cap) {
                        return Ok(substitute(&b, &x, &a));
                    }
                }
            }
            Err(())
        }
    }
}

pub fn check(gamma: &Context, t:&Term, t_cap: &Term) -> Result<bool, ()> {
    if let Ok(t_cap_p) = infer(gamma, t) {
        Ok(alpha(&normalize(t_cap), &normalize(&t_cap_p), gamma, gamma))
    } else {
        Err(())
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
        (Term::Sort(u), Term::Sort(v)) => u == v, // alpha-Sort
        (Term::Var(x), Term::Var(y)) => {
            let i = get_pos_in_context(gamma_a, x);
            let j = get_pos_in_context(gamma_b, y);
            match (i, j) {
                (Some(i), Some(j)) => i == j, // alpha-Bound
                (None, None) => x == y,                     // alpha-Free
                _ => false
            }
        },
        (Term::Pi(x, a_1, b_1), Term::Pi(y, a_2, b_2)) 
        | (Term::Lam(x, a_1, b_1), Term::Lam(y, a_2, b_2)) => {
            if !alpha(a_1, a_2, gamma_a, gamma_b) {
                return false;
            }
            let mut gamma_a_prime = gamma_a.clone();
            let mut gamma_b_prime = gamma_b.clone();
            gamma_a_prime.push((x.clone(), Term::Sort(0)));
            gamma_b_prime.push((y.clone(), Term::Sort(0)));
            alpha(b_1, b_2, &gamma_a_prime, &gamma_b_prime) // alpha-Pi
        },
        (Term::App(a_1, b_1), Term::App(a_2, b_2)) => {
            alpha(a_1, a_2, gamma_a, gamma_b) && alpha(b_1, b_2, gamma_a, gamma_b) // alpha-App
        }
        _ => false
    }
}

pub fn infer_sort(gamma: &Context, t: &Term) -> Result<u64, ()> {
    match infer(gamma, t) {
        Ok(s) => match normalize(&s) {
            Term::Sort(u) => Ok(u),
            _ => Err(())
        },
        Err(_) => Err(()),
    }
}

pub fn fv(t: &Term) -> HashSet<String> {
    match t {
        Term::Sort(_) => HashSet::new(),
        Term::Var(x) => vec![x.clone()].into_iter().collect::<HashSet<String>>(),
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

pub fn fresh_from_context(gamma: &Context, x: &String, b: &Term) -> (String, Term) {
    let mut var_name_set: HashSet<String> = gamma.into_iter().map(|(n, _)| n.clone()).collect();
    if var_name_set.contains(x) {
        var_name_set.extend(fv(b));
        let mut x_p = x.clone();
        while var_name_set.contains(&x_p) {
            x_p = x_p + "'";
        }

        (x_p.clone(), substitute(b, x, &Term::Var(x_p)))
    } else {
        (x.clone(), b.clone())
    }
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
                    b.clone()
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
                Term::Lam(
                    x.clone(), 
                    Box::new(substitute(a, x, s)), 
                    b.clone()
                )
            } else {
                if !fv(s).contains(y) {
                    Term::Lam(
                        y.clone(), 
                        Box::new(substitute(a, x, s)), 
                        Box::new(substitute(b, x, s))
                    )
                } else {
                    let z = fresh(s, b, x, y);
                    Term::Lam(
                        z.clone(), 
                        Box::new(substitute(a, x, s)), 
                        Box::new(substitute(&substitute(b, y, &Term::Var(z)), x, s)), 
                    )
                }
            }
        },
    }
}

pub fn whnf(t: &Term) -> Term {
    match t {
        Term::App(f, a) => {
            let f = whnf(f);                      // 関数側（spine の左）を先に whnf
            match f {
                Term::Lam(x, _, body) => whnf(&substitute(&body, &x, a)), // β して続ける
                _ => Term::App(Box::new(f), a.clone()),                    // 先頭が λ でなければ止まる
            }
        }
        _ => t.clone(), // Sort, Var, Pi, Lam はそのまま（weak なので中に入らない）
    }
}

pub fn normalize(t: &Term) -> Term {
    match whnf(t) {
        Term::Pi(x, a, b) => Term::Pi(x, Box::new(normalize(&a)), Box::new(normalize(&b))),
        Term::Lam(x, a, b) => Term::Lam(x, Box::new(normalize(&a)), Box::new(normalize(&b))),
        Term::App(f, a) => Term::App(Box::new(normalize(&f)), Box::new(normalize(&a))),
        other => other, // Sort, Var
    }
}