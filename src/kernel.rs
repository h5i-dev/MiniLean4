use std::collections::{HashMap, HashSet};

use crate::{
    decl::{
        ConstructorInfo, ConstructorSpec, Context, Decl, DeclKind, FamilyInfo, InductiveSpec,
        RecursiveField, RecursorInfo,
    },
    term::{
        all_names, alpha, app, apps, arrow, fresh, fv, konst, pi, spine, subst,
        subst_many, var,
        Term::{self, Sort},
    },
};

#[derive(Clone, Debug, Default)]
pub struct Kernel {
    pub decls: HashMap<String, Decl>,
    families: HashMap<String, FamilyInfo>,
}

pub type Result<T> = std::result::Result<T, String>;

// A recursor specification, with its inductive type, parameters, indices, constructors, level, and major index.
fn telescope(ctx: &Context, tail: Term) -> Term {
    ctx.iter()
        .rev()
        .fold(tail, |body, (n, ty)| pi(n, ty.clone(), body))
}

fn occurs_const(t: &Term, name: &str) -> bool {
    match t {
        Term::Const(n) => n == name,
        Term::App(f, a) => occurs_const(f, name) || occurs_const(a, name),
        Term::Pi(_, a, b) | Term::Lam(_, a, b) => occurs_const(a, name) || occurs_const(b, name),
        _ => false,
    }
}

fn rec_field(
    t: &Term,
    ind: &str,
    params: &Context,
    nindices: usize,
) -> Option<(Context, Vec<Term>)> {
    let mut binders = vec![];
    let mut cur = t;
    while let Term::Pi(x, a, b) = cur {
        if occurs_const(a, ind) {
            return None;
        }
        binders.push((x.clone(), (**a).clone()));
        cur = b;
    }
    let (h, args) = spine(cur);
    if h != konst(ind) || args.len() != params.len() + nindices {
        return None;
    }
    for (a, (p, _)) in args.iter().zip(params.iter()) {
        if a != &var(p) {
            return None;
        }
    }
    if args[params.len()..].iter().any(|x| occurs_const(x, ind)) {
        return None;
    }
    Some((binders, args[params.len()..].to_vec()))
}

fn motive_app(indices: &[Term], value: Term) -> Term {
    apps(
        var("__motive"),
        indices.iter().cloned().chain(std::iter::once(value)),
    )
}

fn freshen(ctx: &Context, x: &str, body: &Term) -> (String, Term) {
    let mut used = all_names(body);
    for (n, ty) in ctx {
        used.insert(n.clone());
        used.extend(all_names(ty));
    }
    if !ctx.iter().any(|(n, _)| n == x) {
        (x.into(), body.clone())
    } else {
        let z = fresh(x, &used);
        (z.clone(), subst(body, x, &var(&z)))
    }
}

impl Kernel {
    pub fn empty() -> Self {
        Self::default()
    }

    // Create a standard kernel with the natural numbers and equality types preloaded.
    pub fn standard() -> Self {
        let mut k = Self::empty();
        k.add_inductive(InductiveSpec {
            name: "Nat".into(),
            params: vec![],
            indices: vec![],
            sort: 1,
            constructors: vec![
                ConstructorSpec {
                    name: "Nat.zero".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
                ConstructorSpec {
                    name: "Nat.succ".into(),
                    fields: vec![("n".into(), konst("Nat"))],
                    result_indices: vec![],
                },
            ],
        })
        .expect("Nat is valid");
        k.add_inductive(InductiveSpec {
            name: "Eq".into(),
            params: vec![("A".into(), Sort(1)), ("a".into(), var("A"))],
            indices: vec![("b".into(), var("A"))],
            sort: 0,
            constructors: vec![ConstructorSpec {
                name: "Eq.refl".into(),
                fields: vec![],
                result_indices: vec![var("a")],
            }],
        })
        .expect("Eq is valid");
        k
    }

    /// Only the checked declaration API can populate constructor/reduction metadata.
    pub fn add_inductive(&mut self, spec: InductiveSpec) -> Result<()> {
        self.ensure_new(&spec.name)?;
        if spec.name.contains(".rec") {
            return Err("reserved recursor namespace".into());
        }
        if spec
            .params
            .iter()
            .chain(spec.indices.iter())
            .any(|(n, _)| n.starts_with("__") || n == "_")
        {
            return Err("reserved binder name".into());
        }
        // Recursor levels are materialized lazily by ensure_recursor_level.
        for level in 0..=1 {
            self.ensure_new(&format!("{}.rec{level}", spec.name))?;
        }
        let mut seen = HashSet::new();
        for (n, _) in spec.params.iter().chain(spec.indices.iter()) {
            if !seen.insert(n.clone()) {
                return Err(format!("duplicate binder {n}"));
            }
        }
        for c in &spec.constructors {
            self.ensure_new(&c.name)?;
            if c.name == spec.name || !c.name.starts_with(&(spec.name.clone() + ".")) {
                return Err("constructor must be qualified by its inductive name".into());
            }
            if c.fields
                .iter()
                .any(|(n, _)| n.starts_with("__") || n == "_")
            {
                return Err("reserved field name".into());
            }
            if !seen.insert(c.name.clone()) {
                return Err("duplicate constructor".into());
            }
            if c.name.starts_with(&(spec.name.clone() + ".rec")) {
                return Err("constructor conflicts with generated recursor".into());
            }
            if c.result_indices.len() != spec.indices.len() {
                return Err("incorrect constructor index arity".into());
            }
        }
        let mut ctx = vec![];
        for (n, ty) in spec.params.iter().chain(spec.indices.iter()) {
            self.infer_sort(&ctx, ty)?;
            ctx.push((n.clone(), ty.clone()));
        }
        // The inductive's type is checked before its constructors are made visible.
        let ind_ty = telescope(&spec.params, telescope(&spec.indices, Sort(spec.sort)));
        self.decls.insert(
            spec.name.clone(),
            Decl {
                ty: ind_ty,
                kind: DeclKind::Inductive,
            },
        );
        let build = (|| -> Result<Vec<ConstructorInfo>> {
            let mut infos = vec![];
            for c in &spec.constructors {
                let mut local = spec.params.clone();
                let mut recursive = vec![];
                for (i, (n, ty)) in c.fields.iter().enumerate() {
                    if local.iter().any(|(prev, _)| prev == n) {
                        return Err("duplicate field or parameter".into());
                    }
                    let field_universe = self.infer_sort(&local, ty)?;
                    if spec.sort >= 1 && field_universe > spec.sort {
                        return Err(format!("field {n} lives in Sort {field_universe}, exceeding inductive universe Sort {}",spec.sort));
                    }
                    if occurs_const(ty, &spec.name) {
                        let (binders, indices) =
                            rec_field(ty, &spec.name, &spec.params, spec.indices.len())
                                .ok_or("non-strictly-positive / unsupported recursive field")?;
                        recursive.push(RecursiveField {
                            field_index: i,
                            binders,
                            indices,
                        });
                    }
                    local.push((n.clone(), ty.clone()));
                }
                let mut ret = konst(&spec.name);
                for (n, _) in &spec.params {
                    ret = app(ret, var(n));
                }
                for idx in &c.result_indices {
                    if occurs_const(idx, &spec.name) {
                        return Err("inductive occurrence inside result index".into());
                    }
                    ret = app(ret, idx.clone());
                }
                if self.infer_sort(&local, &ret)? != spec.sort {
                    return Err("constructor result has wrong universe".into());
                }
                infos.push(ConstructorInfo {
                    name: c.name.clone(),
                    fields: c.fields.clone(),
                    result_indices: c.result_indices.clone(),
                    recursive,
                });
            }
            Ok(infos)
        })();
        let infos = match build {
            Ok(v) => v,
            Err(e) => {
                self.decls.remove(&spec.name);
                return Err(e);
            }
        };
        // Constructor type, then one recursor per permitted result universe.
        for c in &infos {
            let result = apps(
                konst(&spec.name),
                spec.params
                    .iter()
                    .map(|(n, _)| var(n))
                    .chain(c.result_indices.iter().cloned()),
            );
            let ty = telescope(&spec.params, telescope(&c.fields, result));
            self.decls.insert(
                c.name.clone(),
                Decl {
                    ty,
                    kind: DeclKind::Constructor,
                },
            );
        }
        // Compute the PDF's subsingleton criterion before exposing recursors.
        let mut large_elimination = infos.len() <= 1;
        if spec.sort == 0 {
            for c in &infos {
                let mut local = spec.params.clone();
                for (field, ty) in &c.fields {
                    let is_proof = self.infer_sort(&local, ty)? == 0;
                    let in_indices = c.result_indices.iter().any(|idx| fv(idx).contains(field));
                    if !is_proof && !in_indices {
                        large_elimination = false;
                    }
                    local.push((field.clone(), ty.clone()));
                }
            }
        } else {
            large_elimination = true;
        }
        self.families.insert(
            spec.name.clone(),
            FamilyInfo {
                params: spec.params.clone(),
                indices: spec.indices.clone(),
                sort: spec.sort,
                constructors: infos,
                large_elimination,
            },
        );
        self.ensure_recursor_level(&spec.name, 0)?;
        if large_elimination {
            self.ensure_recursor_level(&spec.name, 1)?;
        }
        Ok(())
    }

    /// Materialize any admissible recursor universe, including levels above 1.
    /// Call this before parsing/using `I.recN` for N > 1.
    pub fn ensure_recursor_level(&mut self, inductive: &str, level: u64) -> Result<()> {
        let family = self
            .families
            .get(inductive)
            .cloned()
            .ok_or_else(|| format!("unknown inductive family: {inductive}"))?;
        if family.sort == 0 && level > 0 && !family.large_elimination {
            return Err(format!(
                "{inductive} is not a subsingleton proposition; cannot eliminate into Sort {level}"
            ));
        }
        let name = format!("{inductive}.rec{level}");
        if self.decls.contains_key(&name) {
            return Ok(());
        }
        let mut index_ctx = family.indices.clone();
        // Avoid conflict between generated motive index names and constructor field names.
        let index_args: Vec<Term> = index_ctx.iter().map(|(n, _)| var(n)).collect();
        let ind = apps(
            konst(&inductive),
            family
                .params
                .iter()
                .map(|(n, _)| var(n))
                .chain(index_args.iter().cloned()),
        );
        let motive_ty = telescope(&index_ctx, arrow(ind.clone(), Sort(level)));
        let mut minors = vec![];
        for (j, c) in family.constructors.iter().enumerate() {
            let ctor = apps(
                konst(&c.name),
                family
                    .params
                    .iter()
                    .map(|(n, _)| var(n))
                    .chain(c.fields.iter().map(|(n, _)| var(n))),
            );
            let mut branches = c.fields.clone();
            for (i, rf) in c.recursive.iter().enumerate() {
                let field = var(&c.fields[rf.field_index].0);
                let rec_value = apps(field, rf.binders.iter().map(|(n, _)| var(n)));
                let ih_ty = telescope(&rf.binders, motive_app(&rf.indices, rec_value));
                branches.push((format!("__ih_{j}_{i}"), ih_ty));
            }
            let goal = motive_app(&c.result_indices, ctor);
            minors.push((format!("__minor_{j}"), telescope(&branches, goal)));
        }
        let result = telescope(
            &index_ctx,
            pi("__major", ind, motive_app(&index_args, var("__major"))),
        );
        let rec_ty = telescope(
            &family.params,
            pi("__motive", motive_ty, telescope(&minors, result)),
        );
        let name = format!("{inductive}.rec{level}");
        if self.decls.contains_key(&name) {
            return Err("recursor name collision".into());
        }
        let major_index =
            family.params.len() + 1 + family.constructors.len() + family.indices.len();
        self.decls.insert(
            name,
            Decl {
                ty: rec_ty,
                kind: DeclKind::Recursor {
                    spec: RecursorInfo {
                        inductive: inductive.to_string(),
                        params: family.params.clone(),
                        indices: index_ctx.clone(),
                        constructors: family.constructors.clone(),
                        level,
                        major_index,
                    },
                },
            },
        );
        Ok(())
    }

    pub fn type_of_const(&self, name: &str) -> Option<&Term> {
        self.decls.get(name).map(|d| &d.ty)
    }

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

    fn ensure_new(&self, name: &str) -> Result<()> {
        if self
            .families
            .keys()
            .any(|family| name.starts_with(&format!("{family}.rec")))
        {
            return Err("cannot shadow a generated recursor namespace".into());
        }
        if self.decls.contains_key(name) {
            Err(format!("duplicate declaration: {name}"))
        } else {
            Ok(())
        }
    }

    pub fn infer_sort(&self, ctx: &Context, t: &Term) -> Result<u64> {
        match self.whnf(&self.infer(ctx, t)?)? {
            Term::Sort(u) => Ok(u),
            other => Err(format!("expected a type, got {other:?}")),
        }
    }

    pub fn infer(&self, ctx: &Context, t: &Term) -> Result<Term> {
        match t {
            Term::Sort(u) => Ok(Term::Sort(u.checked_add(1).ok_or("universe overflow")?)),
            Term::Var(x) => ctx
                .iter()
                .rev()
                .find(|(n, _)| n == x)
                .map(|(_, t)| t.clone())
                .ok_or_else(|| format!("unbound local: {x}")),
            Term::Const(c) => self
                .decls
                .get(c)
                .map(|d| d.ty.clone())
                .ok_or_else(|| format!("unknown constant: {c}")),
            Term::Pi(x, a, b) => {
                let u = self.infer_sort(ctx, a)?;
                let (name, body) = freshen(ctx, x, b);
                let mut ext = ctx.clone();
                ext.push((name, (**a).clone()));
                let v = self.infer_sort(&ext, &body)?;
                Ok(Term::Sort(if v == 0 { 0 } else { u.max(v) }))
            }
            Term::Lam(x, a, b) => {
                self.infer_sort(ctx, a)?;
                let (name, body) = freshen(ctx, x, b);
                let mut ext = ctx.clone();
                ext.push((name.clone(), (**a).clone()));
                let ty = self.infer(&ext, &body)?;
                Ok(Term::Pi(
                    name,
                    Box::new(<Term as Clone>::clone(&**a)),
                    Box::new(ty),
                ))
            }
            Term::App(f, a) => match self.whnf(&self.infer(ctx, f)?)? {
                Term::Pi(x, dom, cod) => {
                    self.check(ctx, a, &dom)?;
                    Ok(subst(&cod, &x, a))
                }
                ty => Err(format!("application of non-function: {ty:?}")),
            },
        }
    }

    pub fn check(&self, ctx: &Context, t: &Term, expected: &Term) -> Result<()> {
        self.infer_sort(ctx, expected)?;
        let actual = self.infer(ctx, t)?;
        if self.conv(&actual, expected)? {
            Ok(())
        } else {
            Err(format!(
                "type mismatch: actual {actual:?}, expected {expected:?}"
            ))
        }
    }

    pub fn conv(&self, a: &Term, b: &Term) -> Result<bool> {
        Ok(alpha(&self.normalize(a)?, &self.normalize(b)?))
    }

    pub fn whnf(&self, t: &Term) -> Result<Term> {
        let mut fuel = 20000;
        self.whnf_inner(t, &mut fuel)
    }

    fn whnf_inner(&self, t: &Term, fuel: &mut usize) -> Result<Term> {
        let mut t = t.clone();
        loop {
            if *fuel == 0 {
                return Err("reduction fuel exhausted".into());
            }
            *fuel -= 1;
            let (head, args) = spine(&t);
            match head {
                Term::Lam(x, _, b) if !args.is_empty() => {
                    t = apps(subst(&b, &x, &args[0]), args[1..].iter().cloned());
                }
                Term::Const(c) => {
                    if let Some(Decl {
                        kind: DeclKind::Definition(body),
                        ..
                    }) = self.decls.get(&c)
                    {
                        t = apps(body.clone(), args);
                        continue;
                    }
                    if let Some(Decl {
                        kind: DeclKind::Recursor { spec },
                        ..
                    }) = self.decls.get(&c)
                    {
                        if args.len() <= spec.major_index {
                            return Ok(t);
                        }
                        let (head, ctor_args) =
                            spine(&self.whnf_inner(&args[spec.major_index], fuel)?);
                        if let Term::Const(ctor_name) = head {
                            if let Some((j, ctor)) = spec
                                .constructors
                                .iter()
                                .enumerate()
                                .find(|(_, r)| r.name == ctor_name)
                            {
                                let nparams = spec.params.len();
                                if ctor_args.len() == nparams + ctor.fields.len() {
                                    for (parameter, actual) in ctor_args
                                        .iter()
                                        .take(nparams)
                                        .zip(args.iter().take(nparams))
                                    {
                                        if !self.conv_with_fuel(parameter, actual, fuel)? {
                                            return Ok(t);
                                        }
                                    }
                                    let fields = &ctor_args[nparams..];
                                    let mut minor_args = fields.to_vec();
                                    for rf in &ctor.recursive {
                                        let rec_field_term = fields[rf.field_index].clone();
                                        let mut replacements: HashMap<String, Term> =
                                            HashMap::new();
                                        for ((n, _), a) in spec.params.iter().zip(args.iter()) {
                                            replacements.insert(n.clone(), a.clone());
                                        }
                                        for ((n, _), a) in ctor.fields.iter().zip(fields.iter()) {
                                            replacements.insert(n.clone(), a.clone());
                                        }
                                        let mut binders = vec![];
                                        for (n, ty) in &rf.binders {
                                            let instantiated = subst_many(ty, &replacements);
                                            binders.push((n.clone(), instantiated));
                                        }
                                        let recursive_indices: Vec<Term> = rf
                                            .indices
                                            .iter()
                                            .map(|t| subst_many(t, &replacements))
                                            .collect();
                                        let applied_field = apps(
                                            rec_field_term,
                                            rf.binders.iter().map(|(n, _)| var(n)),
                                        );
                                        let next = apps(
                                            Term::Const(c.clone()),
                                            args[..nparams + 1 + spec.constructors.len()]
                                                .iter()
                                                .cloned()
                                                .chain(recursive_indices)
                                                .chain(std::iter::once(applied_field)),
                                        );
                                        let ih = binders.iter().rev().fold(next, |acc, (n, ty)| {
                                            Term::Lam(
                                                n.to_string(),
                                                Box::new(ty.clone()),
                                                Box::new(acc),
                                            )
                                        });
                                        minor_args.push(ih);
                                    }
                                    let minor = args[nparams + 1 + j].clone();
                                    t = apps(
                                        minor,
                                        minor_args
                                            .into_iter()
                                            .chain(args[spec.major_index + 1..].iter().cloned()),
                                    );
                                    continue;
                                }
                            }
                        }
                    }
                    return Ok(t);
                }
                _ => return Ok(t),
            }
        }
    }

    fn conv_with_fuel(&self, a: &Term, b: &Term, fuel: &mut usize) -> Result<bool> {
        Ok(alpha(&self.nf_inner(a, fuel)?, &self.nf_inner(b, fuel)?))
    }

    pub fn normalize(&self, t: &Term) -> Result<Term> {
        let mut fuel = 20000;
        self.nf_inner(t, &mut fuel)
    }

    fn nf_inner(&self, t: &Term, fuel: &mut usize) -> Result<Term> {
        let n = self.whnf_inner(t, fuel)?;
        match n {
            Term::Pi(x, a, b) => Ok(Term::Pi(
                x,
                Box::new(self.nf_inner(&a, fuel)?),
                Box::new(self.nf_inner(&b, fuel)?),
            )),
            Term::Lam(x, a, b) => Ok(Term::Lam(
                x,
                Box::new(self.nf_inner(&a, fuel)?),
                Box::new(self.nf_inner(&b, fuel)?),
            )),
            Term::App(f, a) => {
                let rebuilt = Term::App(
                    Box::new(self.nf_inner(&f, fuel)?),
                    Box::new(self.nf_inner(&a, fuel)?),
                );
                let reduced = self.whnf_inner(&rebuilt, fuel)?;
                if reduced == rebuilt {
                    Ok(rebuilt)
                } else {
                    self.nf_inner(&reduced, fuel)
                }
            }
            other => Ok(other),
        }
    }
}

mod inductive_tests {

    //
    //! Put this file at `tests/inductive_examples.rs` in MiniLean4.
    //! Run: cargo test --test inductive_examples -- --nocapture
    use crate::term::lam;

    use super::*;

    fn nat() -> Term {
        konst("Nat")
    }
    fn zero() -> Term {
        konst("Nat.zero")
    }
    fn succ(n: Term) -> Term {
        app(konst("Nat.succ"), n)
    }
    fn numeral(n: usize) -> Term {
        (0..n).fold(zero(), |t, _| succ(t))
    }

    fn add_tree(k: &mut Kernel) {
        // inductive Tree where
        // | leaf : Tree
        // | node : Tree -> Tree
        // | branch : Tree -> Tree -> Tree
        k.add_inductive(InductiveSpec {
            name: "Tree".into(),
            params: vec![],
            indices: vec![],
            sort: 1,
            constructors: vec![
                ConstructorSpec {
                    name: "Tree.leaf".into(),
                    fields: vec![],
                    result_indices: vec![],
                },
                ConstructorSpec {
                    name: "Tree.node".into(),
                    fields: vec![("child".into(), konst("Tree"))],
                    result_indices: vec![],
                },
                ConstructorSpec {
                    name: "Tree.branch".into(),
                    fields: vec![
                        ("left".into(), konst("Tree")),
                        ("right".into(), konst("Tree")),
                    ],
                    result_indices: vec![],
                },
            ],
        })
        .unwrap();
    }

    fn leaf() -> Term {
        konst("Tree.leaf")
    }
    fn node(child: Term) -> Term {
        app(konst("Tree.node"), child)
    }
    fn branch(left: Term, right: Term) -> Term {
        apps(konst("Tree.branch"), [left, right])
    }

    fn add_list(k: &mut Kernel) {
        // inductive List (A : Type) where
        // | nil : List A
        // | cons : A -> List A -> List A
        k.add_inductive(InductiveSpec {
            name: "List".into(),
            params: vec![("A".into(), Term::Sort(1))],
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
    }

    fn list_nat() -> Term {
        app(konst("List"), nat())
    }
    fn nil() -> Term {
        app(konst("List.nil"), nat())
    }
    fn cons(head: Term, tail: Term) -> Term {
        apps(konst("List.cons"), [nat(), head, tail])
    }

    // Nat addition, defined only using the existing Nat.rec1:
    // add(x, y) = Nat.rec1 (fun _ => Nat) y (fun _ ih => succ ih) x
    fn add(x: Term, y: Term) -> Term {
        apps(
            konst("Nat.rec1"),
            [
                lam("_n", nat(), nat()),
                y,
                lam("_n", nat(), lam("ih", nat(), succ(var("ih")))),
                x,
            ],
        )
    }

    // count(Tree): leaf=1, node(child)=1+count(child),
    // branch(l,r)=1+count(l)+count(r).
    fn tree_size(t: Term) -> Term {
        let tree = konst("Tree");
        let motive = lam("t", tree.clone(), nat());
        let on_leaf = numeral(1);
        let on_node = lam("child", tree.clone(), lam("ih", nat(), succ(var("ih"))));
        let on_branch = lam(
            "left",
            tree.clone(),
            lam(
                "right",
                tree,
                lam(
                    "ih_left",
                    nat(),
                    lam(
                        "ih_right",
                        nat(),
                        succ(add(var("ih_left"), var("ih_right"))),
                    ),
                ),
            ),
        );
        apps(konst("Tree.rec1"), [motive, on_leaf, on_node, on_branch, t])
    }

    // length(List Nat): nil=0, cons(head, tail)=1+length(tail).
    fn list_length(xs: Term) -> Term {
        let list = list_nat();
        let motive = lam("xs", list.clone(), nat());
        let on_nil = zero();
        let on_cons = lam(
            "head",
            nat(),
            lam("tail", list, lam("ih", nat(), succ(var("ih")))),
        );
        apps(konst("List.rec1"), [nat(), motive, on_nil, on_cons, xs])
    }

    #[test]
    fn tree_constructors_have_expected_types() {
        let mut k = Kernel::standard();
        add_tree(&mut k);
        let tree = konst("Tree");
        assert!(k
            .conv(k.type_of_const("Tree.leaf").unwrap(), &tree)
            .unwrap());
    }
}

mod textbook_kernel_tests {
    use super::*;
    use crate::term::lam;

    #[test]
    fn generic_list_recursor_reduces() {
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
        let list_nat = app(konst("List"), nat.clone());
        let nil = app(konst("List.nil"), nat.clone());
        let singleton = apps(
            konst("List.cons"),
            [nat.clone(), konst("Nat.zero"), nil.clone()],
        );
        k.check(&vec![], &singleton, &list_nat).unwrap();
        let motive = lam("xs", list_nat.clone(), nat.clone());
        let succ = lam(
            "head",
            nat.clone(),
            lam(
                "tail",
                list_nat.clone(),
                lam("ih", nat.clone(), app(konst("Nat.succ"), var("ih"))),
            ),
        );
        let count = apps(
            konst("List.rec1"),
            [nat, motive, konst("Nat.zero"), succ, singleton],
        );
        assert!(k
            .conv(&count, &app(konst("Nat.succ"), konst("Nat.zero")))
            .unwrap());
    }

    #[test]
    fn arbitrary_recursor_levels() {
        let mut k = Kernel::standard();
        k.ensure_recursor_level("Nat", 4).unwrap();
        k.ensure_recursor_level("Eq", 5).unwrap();
        assert!(k.type_of_const("Nat.rec4").is_some());
        assert!(k.type_of_const("Eq.rec5").is_some());
    }

    #[test]
    fn reject_constructor_universe_overflow() {
        let mut k = Kernel::standard();
        let bad = InductiveSpec {
            name: "TooLarge".into(),
            params: vec![],
            indices: vec![],
            sort: 1,
            constructors: vec![ConstructorSpec {
                name: "TooLarge.mk".into(),
                fields: vec![("x".into(), Sort(1))],
                result_indices: vec![],
            }],
        };
        assert!(k.add_inductive(bad).is_err());
    }

    #[test]
    fn proposition_elimination_policy() {
        let mut k = Kernel::standard();
        k.add_inductive(InductiveSpec {
            name: "Either".into(),
            params: vec![("P".into(), Sort(0)), ("Q".into(), Sort(0))],
            indices: vec![],
            sort: 0,
            constructors: vec![
                ConstructorSpec {
                    name: "Either.left".into(),
                    fields: vec![("p".into(), var("P"))],
                    result_indices: vec![],
                },
                ConstructorSpec {
                    name: "Either.right".into(),
                    fields: vec![("q".into(), var("Q"))],
                    result_indices: vec![],
                },
            ],
        })
        .unwrap();
        assert!(k.ensure_recursor_level("Either", 3).is_err());
        k.add_inductive(InductiveSpec {
            name: "Both".into(),
            params: vec![("P".into(), Sort(0)), ("Q".into(), Sort(0))],
            indices: vec![],
            sort: 0,
            constructors: vec![ConstructorSpec {
                name: "Both.mk".into(),
                fields: vec![("p".into(), var("P")), ("q".into(), var("Q"))],
                result_indices: vec![],
            }],
        })
        .unwrap();
        k.ensure_recursor_level("Both", 3).unwrap();
    }
}
