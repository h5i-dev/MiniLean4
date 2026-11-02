use std::collections::HashMap;

use crate::{
    decl::{ConstructorSpec, Context, DeclKind, InductiveSpec},
    kernel::{Kernel, Result},
    template::Template,
    term::{
        all_names, alpha, app, apps, arrow, fresh, fv, konst, lam, pi, spine, subst, var,
        Term::{self, App, Const, Lam, Pi},
    },
};

fn hole(i: usize) -> Template {
    Template::Hole(i)
}
fn tapp(f: Template, a: Template) -> Template {
    Template::App(Box::new(f), Box::new(a))
}
fn tapps(f: Template, args: impl IntoIterator<Item = Template>) -> Template {
    args.into_iter().fold(f, tapp)
}

#[derive(Clone, Debug)]
pub struct Goal {
    pub id: usize,
    pub context: Context,
    pub target: Term,
}

#[derive(Clone, Debug)]
pub struct ProofState {
    root: Template,
    pending: Vec<Goal>,
    solutions: HashMap<usize, Template>,
    next: usize,
    original: Term,
}

impl ProofState {
    pub fn new(kernel: &Kernel, target: Term) -> Result<Self> {
        kernel.infer_sort(&vec![], &target)?;
        Ok(Self {
            root: hole(0),
            pending: vec![Goal {
                id: 0,
                context: vec![],
                target: target.clone(),
            }],
            solutions: HashMap::new(),
            next: 1,
            original: target,
        })
    }

    pub fn goals(&self) -> &[Goal] {
        &self.pending
    }

    fn current(&self) -> Result<Goal> {
        self.pending.first().cloned().ok_or("no goals".into())
    }

    fn replace(&mut self, id: usize, solution: Template, new_goals: Vec<Goal>) {
        self.solutions.insert(id, solution);
        self.pending.remove(0);
        for (i, g) in new_goals.into_iter().enumerate() {
            self.pending.insert(i, g);
        }
    }

    fn new_id(&mut self) -> usize {
        let n = self.next;
        self.next += 1;
        n
    }

    pub fn intro(&mut self, k: &Kernel, name: &str) -> Result<()> {
        let goal = self.current()?;
        match k.whnf(&goal.target)? {
            Term::Pi(x, a, b) => {
                if goal.context.iter().any(|(n, _)| n == name) {
                    return Err("binder name already in context".into());
                }
                let target = subst(&b, &x, &var(name));
                let mut ctx = goal.context;
                ctx.push((name.into(), (*a).clone()));
                let id = self.new_id();
                self.replace(
                    goal.id,
                    Template::Lam(name.into(), *a, Box::new(hole(id))),
                    vec![Goal {
                        id,
                        context: ctx,
                        target,
                    }],
                );
                Ok(())
            }
            _ => Err("intro expects a Pi/arrow goal".into()),
        }
    }

    pub fn exact(&mut self, k: &Kernel, term: Term) -> Result<()> {
        let g = self.current()?;
        k.check(&g.context, &term, &g.target)?;
        self.replace(g.id, Template::Fixed(term), vec![]);
        Ok(())
    }

    pub fn apply(&mut self, k: &Kernel, f: Term) -> Result<()> {
        let g = self.current()?;
        let mut ft = k.infer(&g.context, &f)?;
        let mut subgoals = vec![];
        let mut proof = Template::Fixed(f);
        loop {
            ft = k.whnf(&ft)?;
            if k.conv(&ft, &g.target)? {
                break;
            }
            match ft {
                Term::Pi(x, a, b) => {
                    // For a dependent Pi, an uninstantiated argument would occur in b.
                    // Explicitly reject this case until unification is implemented.
                    if fv(&b).contains(&x) {
                        return Err("dependent apply requires elaboration/unification".into());
                    }
                    let id = self.new_id();
                    subgoals.push(Goal {
                        id,
                        context: g.context.clone(),
                        target: (*a).clone(),
                    });
                    proof = Template::App(Box::new(proof), Box::new(hole(id)));
                    ft = *b;
                }
                _ => return Err("apply result does not match the goal".into()),
            }
        }
        self.replace(g.id, proof, subgoals);
        Ok(())
    }

    pub fn change(&mut self, k: &Kernel, ty: Term) -> Result<()> {
        let g = self.current()?;
        k.infer_sort(&g.context, &ty)?;
        if !k.conv(&g.target, &ty)? {
            return Err("change expects definitionally equal target".into());
        }
        self.pending[0].target = ty;
        Ok(())
    }
    pub fn rfl(&mut self, k: &Kernel) -> Result<()> {
        let g = self.current()?;
        let (h, args) = spine(&k.whnf(&g.target)?);
        if h != konst("Eq") || args.len() != 3 {
            return Err("rfl expects Eq A lhs rhs".into());
        }
        if !k.conv(&args[1], &args[2])? {
            return Err("rfl: sides are not definitionally equal".into());
        }
        self.exact(
            k,
            apps(konst("Eq.refl"), [args[0].clone(), args[1].clone()]),
        )
    }
    /// Constructor-generic induction for non-indexed inductive families.
    /// Index-dependent motive inference is deliberately left to elaboration.
    pub fn induction(&mut self, k: &Kernel, n: &str) -> Result<()> {
        let g = self.current()?;
        let pos = g
            .context
            .iter()
            .position(|(x, _)| x == n)
            .ok_or("no such local".to_string())?;
        if g.context[pos + 1..]
            .iter()
            .any(|(_, ty)| fv(ty).contains(n))
        {
            return Err("induction: revert dependent hypotheses first".into());
        }
        let ty = k.whnf(&g.context[pos].1)?;
        let (head, args) = spine(&ty);
        let name = match head {
            Const(name) => name,
            _ => return Err("induction expects an inductive type".into()),
        };
        let decl = k.decls.get(&name).ok_or("unknown inductive")?;
        if !matches!(decl.kind, DeclKind::Inductive) {
            return Err("induction expects inductive type".into());
        }
        let level = k.infer_sort(&g.context, &g.target)?;
        let rec_name = format!("{name}.rec{level}");
        let rec_info = match k.decls.get(&rec_name).map(|d| &d.kind) {
            Some(DeclKind::Recursor { spec }) => spec,
            _ => return Err("no elimination recursor at target universe".into()),
        };
        if !rec_info.indices.is_empty() {
            return Err(
                "indexed induction requires motive/index elaboration (not implemented)".into(),
            );
        }
        if args.len() != rec_info.params.len() {
            return Err("inductive parameter arity mismatch".into());
        }
        let mut used = all_names(&g.target);
        for (x, ty) in &g.context {
            used.insert(x.clone());
            used.extend(all_names(ty));
        }
        let x = fresh("ind_x", &used);
        let motive = lam(&x, ty.clone(), subst(&g.target, n, &var(&x)));
        let mut prefix: Vec<Term> = args.clone();
        prefix.push(motive);
        // The generated recursor *type* determines the branch binders and IHs.
        let mut rec_ty = k.infer(&g.context, &apps(konst(&rec_name), prefix.clone()))?;
        let mut new_goals = vec![];
        let mut proof_args = vec![];
        for ctor in &rec_info.constructors {
            let mut branch: Vec<(String, Term)> = vec![];
            let (minor_name, minor_ty, rest) = match k.whnf(&rec_ty)? {
                Term::Pi(old, domain, body) => (old, *domain, *body),
                _ => return Err("recursor missing a minor premise".into()),
            };
            let mut target = minor_ty;
            let mut fields = vec![];
            let binders = ctor.fields.len() + ctor.recursive.len();
            for _ in 0..binders {
                match target {
                    Term::Pi(old, domain, body) => {
                        let mut avoid = used.clone();
                        for (name, ty) in &branch {
                            avoid.insert(name.clone());
                            avoid.extend(all_names(ty));
                        }
                        // Readable names for the standard Nat induction example.
                        let preferred = if old.starts_with("__ih_") {
                            "ih"
                        } else if old == "n" && avoid.contains("n") {
                            "k"
                        } else {
                            &old
                        };
                        let fresh_name = fresh(preferred, &avoid);
                        let body = subst(&body, &old, &var(&fresh_name));
                        branch.push((fresh_name, (*domain).clone()));
                        target = body;
                    }
                    _ => return Err("invalid generated constructor minor type".into()),
                }
            }
            fields.extend(branch.clone());
            let id = self.new_id();
            let mut context = g.context.clone();
            context.extend(fields);
            let subgoal = Goal {
                id,
                context,
                target,
            };
            let template = branch.iter().rev().fold(hole(id), |body, (name, ty)| {
                Template::Lam(name.clone(), ty.clone(), Box::new(body))
            });
            // Infer the instantiated type after supplying a minor branch.
            // A temporary local is used because the proof body still contains a hole.
            // The result type after the minor is independent of its proof term.
            if fv(&rest).contains(&minor_name) {
                return Err("dependent minor premises unsupported".into());
            }
            rec_ty = rest;
            proof_args.push(template);
            new_goals.push(subgoal);
        }
        // Need to apply the recursor to the original induction variable.
        let proof = tapps(
            Template::Fixed(apps(konst(&rec_name), prefix)),
            proof_args
                .into_iter()
                .chain(std::iter::once(Template::Fixed(var(n)))),
        );
        self.replace(g.id, proof, new_goals);
        Ok(())
    }

    pub fn induction_nat(&mut self, k: &Kernel, n: &str) -> Result<()> {
        self.induction(k, n)
    }

    pub fn rw(&mut self, k: &Kernel, equality: Term) -> Result<()> {
        let g = self.current()?;
        let (h, args) = spine(&k.whnf(&k.infer(&g.context, &equality)?)?);
        if h != konst("Eq") || args.len() != 3 {
            return Err("rw expects proof of equality".into());
        }
        let (a, lhs, rhs) = (args[0].clone(), args[1].clone(), args[2].clone());
        let mut used = all_names(&g.target);
        used.extend(all_names(&lhs));
        used.extend(all_names(&rhs));
        for (name, ty) in &g.context {
            used.insert(name.clone());
            used.extend(all_names(ty));
        }
        let v = fresh("rw_x", &used);
        // Replace syntactic occurrences; does not descend under binders that would capture v.
        let (abstracted, found) = replace_exact(&g.target, &lhs, &var(&v));
        if !found {
            return Err("rw: no syntactic occurrence of lhs in goal; use change first".into());
        }
        let old = g.target.clone();
        let new = subst(&abstracted, &v, &rhs);
        let c = lam(&v, a.clone(), abstracted);
        // Eq.rec M a base b eq : M b, with M x = C x -> old.
        let eq_proof = fresh("__eqproof", &used);
        let transport_motive = lam(
            &v,
            a.clone(),
            lam(
                &eq_proof,
                apps(konst("Eq"), [a.clone(), lhs.clone(), var(&v)]),
                arrow(app(c.clone(), var(&v)), old.clone()),
            ),
        );
        let base = lam("rw_proof", old.clone(), var("rw_proof"));
        let transport = apps(
            konst("Eq.rec0"),
            [a, lhs, transport_motive, base, rhs, equality],
        );
        let id = self.new_id();
        let assembled = tapp(Template::Fixed(transport.clone()), hole(id));
        // Check the generated transport's type before committing state.
        check_transport(k, &g.context, &old, &new, &transport)?;
        self.replace(
            g.id,
            assembled,
            vec![Goal {
                id,
                context: g.context,
                target: new,
            }],
        );
        Ok(())
    }
    pub fn finish(&self, k: &Kernel) -> Result<Term> {
        if !self.pending.is_empty() {
            return Err(format!("{} goals remain", self.pending.len()));
        }
        let result = self.root.materialize(&self.solutions)?;
        k.check(&vec![], &result, &self.original)?;
        Ok(result)
    }
}
// A placeholder is not needed to check the complete proof; this helper checks the
// transport as a function from the rewritten goal to the original goal.
fn check_transport(
    k: &Kernel,
    ctx: &Context,
    old: &Term,
    new: &Term,
    transport: &Term,
) -> Result<()> {
    k.check(ctx, transport, &arrow(new.clone(), old.clone()))
}
fn replace_exact(t: &Term, from: &Term, to: &Term) -> (Term, bool) {
    if alpha(t, from) {
        return (to.clone(), true);
    }
    match t {
        App(f, a) => {
            let (f1, yes1) = replace_exact(f, from, to);
            let (a1, yes2) = replace_exact(a, from, to);
            (app(f1, a1), yes1 || yes2)
        }
        Pi(x, a, b) | Lam(x, a, b) => {
            let (a1, yes1) = replace_exact(a, from, to);
            let (b1, yes2) = if fv(to).contains(x) {
                ((**b).clone(), false)
            } else {
                replace_exact(b, from, to)
            };
            let t1 = if matches!(t, Pi(..)) {
                pi(x, a1, b1)
            } else {
                lam(x, a1, b1)
            };
            (t1, yes1 || yes2)
        }
        _ => (t.clone(), false),
    }
}

#[cfg(test)]
mod tests {
    use crate::term::Term::Sort;

    use super::*;

    #[test]
    fn generic_list_induction_tactic() {
        let mut k = Kernel::standard();
        k.add_inductive(InductiveSpec {
            name: "List".into(),
            params: vec![("A".into(), Sort(1))],
            indices: vec![],
            sort: 1,
            constructors: vec![
                ConstructorSpec {
                    name: "List.nil".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
                ConstructorSpec {
                    name: "List.cons".into(),
                    fields: vec![
                        ("head".into(), var("A")),
                        ("tail".into(), app(konst("List"), var("A"))),
                    ],
                    result_indices: vec![],
                },
            ],
        })
        .unwrap();
        let nat = konst("Nat");
        let list_nat = app(konst("List"), nat);
        let goal = pi(
            "xs",
            list_nat.clone(),
            apps(konst("Eq"), [list_nat, var("xs"), var("xs")]),
        );
        let mut state = ProofState::new(&k, goal).unwrap();
        state.intro(&k, "xs").unwrap();
        state.induction(&k, "xs").unwrap();
        assert_eq!(state.goals().len(), 2);
        state.rfl(&k).unwrap();
        state.rfl(&k).unwrap();
        state.finish(&k).unwrap();
    }

    #[test]
    fn generic_indexed_vec_recursor_reduces() {
        let mut k = Kernel::standard();
        let nat = konst("Nat");
        k.add_inductive(InductiveSpec {
            name: "Vec".into(),
            params: vec![("A".into(), Sort(1))],
            indices: vec![("len".into(), nat.clone())],
            sort: 1,
            constructors: vec![
                ConstructorSpec {
                    name: "Vec.nil".into(),
                    fields: vec![],
                    result_indices: vec![konst("Nat.zero")],
                },
                ConstructorSpec {
                    name: "Vec.cons".into(),
                    fields: vec![
                        ("n".into(), nat.clone()),
                        ("head".into(), var("A")),
                        ("tail".into(), apps(konst("Vec"), [var("A"), var("n")])),
                    ],
                    result_indices: vec![app(konst("Nat.succ"), var("n"))],
                },
            ],
        })
        .unwrap();
        let vec_nat = apps(konst("Vec"), [nat.clone(), konst("Nat.zero")]);
        let nil = app(konst("Vec.nil"), nat.clone());
        k.check(&vec![], &nil, &vec_nat).unwrap();
        let motive = lam(
            "n",
            nat.clone(),
            lam(
                "xs",
                apps(konst("Vec"), [nat.clone(), var("n")]),
                nat.clone(),
            ),
        );
        let succ = lam(
            "n",
            nat.clone(),
            lam(
                "head",
                nat.clone(),
                lam(
                    "tail",
                    apps(konst("Vec"), [nat.clone(), var("n")]),
                    lam("ih", nat.clone(), app(konst("Nat.succ"), var("ih"))),
                ),
            ),
        );
        let t = apps(
            konst("Vec.rec1"),
            [
                nat.clone(),
                motive,
                konst("Nat.zero"),
                succ,
                konst("Nat.zero"),
                nil,
            ],
        );
        k.check(&vec![], &t, &nat).unwrap();
        assert!(k.conv(&t, &konst("Nat.zero")).unwrap());
    }
    #[test]
    fn rejects_negative_recursive_field() {
        let mut k = Kernel::standard();
        let bad = InductiveSpec {
            name: "Bad".into(),
            params: vec![],
            indices: vec![],
            sort: 1,
            constructors: vec![ConstructorSpec {
                name: "Bad.mk".into(),
                fields: vec![("f".into(), arrow(konst("Bad"), konst("Nat")))],
                result_indices: vec![],
            }],
        };
        assert!(k.add_inductive(bad).is_err());
        assert!(k.type_of_const("Bad").is_none());
    }

    #[test]
    fn identity_proof() {
        let k = Kernel::standard();
        let prop = pi("P", Sort(0), arrow(var("P"), var("P")));
        let proof = lam("P", Sort(0), lam("h", var("P"), var("h")));
        k.check(&vec![], &proof, &prop).unwrap();
    }

    #[test]
    fn nat_rec_reduction() {
        let k = Kernel::standard();
        let nat = konst("Nat");
        let m = lam("n", nat.clone(), nat.clone());
        let succ = lam(
            "n",
            nat.clone(),
            lam("x", nat.clone(), app(konst("Nat.succ"), var("x"))),
        );
        let two = app(konst("Nat.succ"), app(konst("Nat.succ"), konst("Nat.zero")));
        let t = apps(konst("Nat.rec1"), [m, konst("Nat.zero"), succ, two.clone()]);
        k.check(&vec![], &t, &nat).unwrap();
        assert!(k.conv(&t, &two).unwrap());
    }
    #[test]
    fn eq_refl_and_rec() {
        let k = Kernel::standard();
        let nat = konst("Nat");
        let z = konst("Nat.zero");
        let refl = apps(konst("Eq.refl"), [nat.clone(), z.clone()]);
        let goal = apps(konst("Eq"), [nat.clone(), z.clone(), z.clone()]);
        k.check(&vec![], &refl, &goal).unwrap();
        let motive = lam("n", nat.clone(), goal.clone());
        let dependent_motive = lam(
            "b",
            nat.clone(),
            lam(
                "p",
                apps(konst("Eq"), [nat.clone(), z.clone(), var("b")]),
                goal.clone(),
            ),
        );
        let rec = apps(
            konst("Eq.rec0"),
            [
                nat,
                z,
                dependent_motive,
                refl.clone(),
                konst("Nat.zero"),
                refl.clone(),
            ],
        );
        k.check(&vec![], &rec, &goal).unwrap();
        assert!(k.conv(&rec, &refl).unwrap());
    }
    #[test]
    fn intro_exact_tactic() {
        let k = Kernel::standard();
        let goal = pi("P", Sort(0), arrow(var("P"), var("P")));
        let mut s = ProofState::new(&k, goal).unwrap();
        s.intro(&k, "P").unwrap();
        s.intro(&k, "p").unwrap();
        s.exact(&k, var("p")).unwrap();
        s.finish(&k).unwrap();
    }
    #[test]
    fn rw_tactic() {
        let k = Kernel::standard();
        let nat = konst("Nat");
        let lhs = apps(konst("Eq"), [nat.clone(), var("a"), var("b")]);
        let refl_goal = apps(konst("Eq"), [nat.clone(), var("a"), var("a")]);
        let goal = pi(
            "a",
            nat.clone(),
            pi("b", nat.clone(), arrow(lhs, refl_goal)),
        );
        let mut s = ProofState::new(&k, goal).unwrap();
        s.intro(&k, "a").unwrap();
        s.intro(&k, "b").unwrap();
        s.intro(&k, "h").unwrap();
        s.rw(&k, var("h")).unwrap();
        s.rfl(&k).unwrap();
        s.finish(&k).unwrap();
    }
    #[test]
    fn conversion_renormalizes_exposed_redex() {
        let k = Kernel::standard();
        let t = app(
            app(
                lam("f", arrow(konst("Nat"), konst("Nat")), var("f")),
                lam("x", konst("Nat"), var("x")),
            ),
            konst("Nat.zero"),
        );
        assert!(k.conv(&t, &konst("Nat.zero")).unwrap());
    }
    #[test]
    fn induction_tactic() {
        let k = Kernel::standard();
        let goal = pi(
            "n",
            konst("Nat"),
            apps(konst("Eq"), [konst("Nat"), var("n"), var("n")]),
        );
        let mut s = ProofState::new(&k, goal).unwrap();
        s.intro(&k, "n").unwrap();
        s.induction_nat(&k, "n").unwrap();
        s.rfl(&k).unwrap();
        s.rfl(&k).unwrap();
        s.finish(&k).unwrap();
    }
}

#[cfg(test)]
mod textbook_completion_tests {
    use super::*;
    fn nat() -> Term {
        konst("Nat")
    }
    fn zero() -> Term {
        konst("Nat.zero")
    }
    fn succ(t: Term) -> Term {
        app(konst("Nat.succ"), t)
    }
    fn eq_nat(a: Term, b: Term) -> Term {
        apps(konst("Eq"), [nat(), a, b])
    }
    fn add(a: Term, b: Term) -> Term {
        apps(konst("add"), [a, b])
    }
    fn with_add() -> Kernel {
        let mut k = Kernel::standard();
        let motive = lam("_n", nat(), nat());
        let step = lam("k", nat(), lam("r", nat(), succ(var("r"))));
        let body = lam(
            "m",
            nat(),
            lam(
                "n",
                nat(),
                apps(konst("Nat.rec1"), [motive, var("m"), step, var("n")]),
            ),
        );
        k.define("add", arrow(nat(), arrow(nat(), nat())), body)
            .unwrap();
        k
    }

    #[test]
    fn textbook_zero_add_tactic_proof() {
        let k = with_add();
        let n = var("n");
        let target = pi("n", nat(), eq_nat(add(zero(), n.clone()), n));
        let mut state = ProofState::new(&k, target.clone()).unwrap();
        state.intro(&k, "n").unwrap();
        state.induction(&k, "n").unwrap();
        state.rfl(&k).unwrap();
        let k_var = var("k");
        state
            .change(
                &k,
                eq_nat(succ(add(zero(), k_var.clone())), succ(k_var.clone())),
            )
            .unwrap();
        let ih = var("ih");
        state.rw(&k, ih).unwrap();
        state.rfl(&k).unwrap();
        let proof = state.finish(&k).unwrap();
        k.check(&vec![], &proof, &target).unwrap();
    }
}
