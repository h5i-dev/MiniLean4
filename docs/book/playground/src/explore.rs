//! Structured views of the kernel for the ebook's explorers.
//!
//! Every operation takes a text request and returns JSON. The request is
//! `op` on the first line, followed by the operation's arguments, one per
//! line; a final multi-line argument (a prelude script, or a proof script)
//! follows a line containing only `---`.
//!
//! Operations:
//!   ast      term                         syntax tree of a term
//!   derive   term [--- prelude]           typing derivation, mirroring `infer`
//!   reduce   term [--- prelude]           head reduction steps and normal form
//!   scope    term                         tokens with binder identities
//!   subst    term \n var \n replacement   naive vs capture-avoiding substitution
//!   trace    --- script                   proof state after every command
//!   ctree    term [--- prelude]           constructor tree of a value with recursor cases

use std::collections::HashMap;

use mini_lean4::{
    declaration::{Context, DeclKind, InductiveInfo},
    kernel::{Kernel, Result},
    substitution::{all_names, fresh, fv, subst, subst_many},
    syntax::parse_term,
    template::Template,
    term::{apps, spine, var, Term},
};
use std::fmt::Write as _;

use crate::{beta_head, prettify_debug_terms, run_setup_line};

// ---------------------------------------------------------------------------
// JSON helpers (the crate has no dependencies)
// ---------------------------------------------------------------------------

fn jstr(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn jarr(items: Vec<String>) -> String {
    format!("[{}]", items.join(","))
}

fn jobj(fields: Vec<(&str, String)>) -> String {
    let body: Vec<String> = fields
        .into_iter()
        .map(|(k, v)| format!("{}:{}", jstr(k), v))
        .collect();
    format!("{{{}}}", body.join(","))
}

fn jerr(message: &str) -> String {
    jobj(vec![("error", jstr(&prettify_debug_terms(message)))])
}

// ---------------------------------------------------------------------------
// Tokens: a term as a list of coloured pieces
// ---------------------------------------------------------------------------

/// One piece of printed term. `kind` is one of sort, binder, bound, free,
/// const, kw, punct, hole; `id` links a binder to the occurrences it binds.
struct Tok {
    text: String,
    kind: &'static str,
    id: i64,
    mark: bool,
}

struct Printer {
    toks: Vec<Tok>,
    scope: Vec<(String, i64)>,
    next_id: i64,
    marking: bool,
}

impl Printer {
    fn new() -> Self {
        Printer { toks: vec![], scope: vec![], next_id: 0, marking: false }
    }

    fn push(&mut self, text: &str, kind: &'static str, id: i64) {
        let mark = self.marking;
        self.toks.push(Tok { text: text.to_string(), kind, id, mark });
    }

    fn lookup(&self, name: &str) -> Option<i64> {
        self.scope.iter().rev().find(|(n, _)| n == name).map(|(_, id)| *id)
    }

    fn var(&mut self, name: &str) {
        if let Some(stripped) = name.strip_prefix('?') {
            let id = stripped.parse::<i64>().unwrap_or(-1);
            self.push(name, "hole", id);
        } else if let Some(id) = self.lookup(name) {
            self.push(name, "bound", id);
        } else {
            self.push(name, "free", -1);
        }
    }

    fn term(&mut self, t: &Term) {
        match t {
            Term::Sort(u) => {
                self.push("Sort", "sort", -1);
                self.push(" ", "punct", -1);
                self.push(&u.to_string(), "sort", -1);
            }
            Term::Var(x) => self.var(x),
            Term::Const(c) => self.push(c, "const", -1),
            Term::Pi(x, a, b) => {
                if x == "_" || !fv(b).contains(x) {
                    let paren = matches!(**a, Term::Pi(..) | Term::Lam(..));
                    if paren {
                        self.push("(", "punct", -1);
                    }
                    self.term(a);
                    if paren {
                        self.push(")", "punct", -1);
                    }
                    self.push(" -> ", "punct", -1);
                    // The anonymous binder still enters the scope so that a
                    // shadowed name inside the body resolves correctly.
                    let id = self.next_id;
                    self.next_id += 1;
                    self.scope.push((x.clone(), id));
                    self.term(b);
                    self.scope.pop();
                } else {
                    self.binder("forall", x, a, b, ", ");
                }
            }
            Term::Lam(x, a, b) => self.binder("fun", x, a, b, " => "),
            Term::App(..) => {
                let (head, args) = spine(t);
                self.head(&head);
                for a in &args {
                    self.push(" ", "punct", -1);
                    self.arg(a);
                }
            }
        }
    }

    fn binder(&mut self, kw: &str, x: &str, a: &Term, b: &Term, sep: &str) {
        let id = self.next_id;
        self.next_id += 1;
        self.push(kw, "kw", -1);
        self.push(" (", "punct", -1);
        self.push(x, "binder", id);
        self.push(" : ", "punct", -1);
        self.term(a);
        self.push(")", "punct", -1);
        self.push(sep, "punct", -1);
        self.scope.push((x.to_string(), id));
        self.term(b);
        self.scope.pop();
    }

    fn head(&mut self, h: &Term) {
        if matches!(h, Term::Pi(..) | Term::Lam(..)) {
            self.push("(", "punct", -1);
            self.term(h);
            self.push(")", "punct", -1);
        } else {
            self.term(h);
        }
    }

    fn arg(&mut self, a: &Term) {
        if matches!(a, Term::Var(_) | Term::Const(_)) {
            self.term(a);
        } else {
            self.push("(", "punct", -1);
            self.term(a);
            self.push(")", "punct", -1);
        }
    }

    /// Prints `t`, marking the head redex: the head applied to its first
    /// `redex_args` arguments.
    fn term_marked(&mut self, t: &Term, redex_args: usize) {
        let (head, args) = spine(t);
        if args.len() < redex_args || (redex_args == 0 && !args.is_empty()) {
            // Mark the head only.
            self.marking = true;
            self.head(&head);
            self.marking = false;
            for a in &args {
                self.push(" ", "punct", -1);
                self.arg(a);
            }
            return;
        }
        self.marking = true;
        self.head(&head);
        for a in &args[..redex_args] {
            self.push(" ", "punct", -1);
            self.arg(a);
        }
        self.marking = false;
        for a in &args[redex_args..] {
            self.push(" ", "punct", -1);
            self.arg(a);
        }
    }

    fn json(&self) -> String {
        jarr(
            self.toks
                .iter()
                .map(|t| {
                    jobj(vec![
                        ("t", jstr(&t.text)),
                        ("k", jstr(t.kind)),
                        ("id", t.id.to_string()),
                        ("m", (if t.mark { "true" } else { "false" }).to_string()),
                    ])
                })
                .collect(),
        )
    }
}

fn tokens(t: &Term) -> String {
    let mut p = Printer::new();
    p.term(t);
    p.json()
}

fn tokens_marked(t: &Term, redex_args: usize) -> String {
    let mut p = Printer::new();
    p.term_marked(t, redex_args);
    p.json()
}

fn tokens_in_context(ctx: &Context, t: &Term) -> String {
    // Context variables are free from the term's point of view, which is what
    // the "free" colour means.
    let _ = ctx;
    tokens(t)
}

// ---------------------------------------------------------------------------
// Requests
// ---------------------------------------------------------------------------

struct Request<'a> {
    args: Vec<&'a str>,
    tail: Option<&'a str>,
}

fn parse_request(input: &str) -> (String, Request<'_>) {
    let (head, tail) = match input.find("\n---\n") {
        Some(pos) => (&input[..pos], Some(&input[pos + 5..])),
        None => (input, None),
    };
    let mut lines = head.lines();
    let op = lines.next().unwrap_or("").trim().to_string();
    let args: Vec<&str> = lines.collect();
    (op, Request { args, tail })
}

/// Runs a prelude script (definitions and inductive declarations) on a fresh
/// standard kernel. Tactic commands are rejected: the prelude only sets up
/// the signature.
fn kernel_with_prelude(prelude: Option<&str>) -> std::result::Result<Kernel, String> {
    let mut k = Kernel::standard();
    let Some(script) = prelude else { return Ok(k) };
    let lines: Vec<String> = script.lines().map(|s| s.to_string()).collect();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();
        if line.starts_with("inductive ") {
            let mut block = vec![lines[i].clone()];
            i += 1;
            while i < lines.len() && (lines[i].trim().starts_with('|') || lines[i].trim().is_empty()) {
                if !lines[i].trim().is_empty() {
                    block.push(lines[i].clone());
                }
                i += 1;
            }
            let spec = mini_lean4::syntax::parse_inductive(&k, &block)?;
            k.add_inductive(spec)?;
        } else {
            run_setup_line(&mut k, line)?;
            i += 1;
        }
    }
    Ok(k)
}

pub fn explore(input: &str) -> String {
    let (op, req) = parse_request(input);
    let result = match op.as_str() {
        "ast" => op_ast(&req),
        "derive" => op_derive(&req),
        "reduce" => op_reduce(&req),
        "scope" => op_scope(&req),
        "subst" => op_subst(&req),
        "trace" => op_trace(&req),
        "ctree" => op_ctree(&req),
        other => Err(format!("unknown operation: {other}")),
    };
    match result {
        Ok(json) => json,
        Err(e) => jerr(&e),
    }
}

fn arg<'a>(req: &Request<'a>, i: usize, what: &str) -> std::result::Result<&'a str, String> {
    req.args.get(i).map(|s| s.trim()).filter(|s| !s.is_empty()).ok_or_else(|| format!("missing {what}"))
}

/// Parses `name : type` entries separated by `;` into a context, checking
/// each type in the context built so far.
fn parse_context(k: &Kernel, spec: &str) -> std::result::Result<Context, String> {
    let mut ctx: Context = vec![];
    for entry in spec.split(';') {
        let entry = entry.trim();
        if entry.is_empty() {
            continue;
        }
        let (name, ty) = entry.split_once(':').ok_or("context entries look like `x : A`")?;
        let ty = parse_term(k, &ctx, ty.trim())?;
        k.infer_sort(&ctx, &ty)?;
        ctx.push((name.trim().to_string(), ty));
    }
    Ok(ctx)
}

// ---------------------------------------------------------------------------
// ast
// ---------------------------------------------------------------------------

fn ast_json(t: &Term) -> String {
    let (kind, label, children): (&str, String, Vec<&Term>) = match t {
        Term::Sort(u) => ("Sort", format!("Sort {u}"), vec![]),
        Term::Var(x) => ("Var", x.clone(), vec![]),
        Term::Const(c) => ("Const", c.clone(), vec![]),
        Term::Pi(x, a, b) => ("Pi", x.clone(), vec![a, b]),
        Term::Lam(x, a, b) => ("Lam", x.clone(), vec![a, b]),
        Term::App(f, a) => ("App", String::new(), vec![f, a]),
    };
    jobj(vec![
        ("kind", jstr(kind)),
        ("label", jstr(&label)),
        ("pretty", jstr(&crate::pretty(t))),
        ("children", jarr(children.into_iter().map(ast_json).collect())),
    ])
}

fn op_ast(req: &Request) -> std::result::Result<String, String> {
    let k = kernel_with_prelude(req.tail)?;
    let t = parse_term(&k, &vec![], arg(req, 0, "term")?)?;
    Ok(jobj(vec![("ast", ast_json(&t)), ("tokens", tokens(&t))]))
}

// ---------------------------------------------------------------------------
// derive: a tracing mirror of Kernel::infer
// ---------------------------------------------------------------------------

struct Node {
    rule: String,
    premise: String,
    ctx: Context,
    term: Term,
    result: std::result::Result<Term, String>,
    note: String,
    children: Vec<Node>,
}

fn node_json(n: &Node) -> String {
    let ctx = jarr(
        n.ctx
            .iter()
            .map(|(x, ty)| jobj(vec![("name", jstr(x)), ("type", jstr(&crate::pretty(ty)))]))
            .collect(),
    );
    let (ok, result) = match &n.result {
        Ok(t) => ("true", jstr(&crate::pretty(t))),
        Err(e) => ("false", jstr(&prettify_debug_terms(e))),
    };
    jobj(vec![
        ("rule", jstr(&n.rule)),
        ("premise", jstr(&n.premise)),
        ("ctx", ctx),
        ("term", jstr(&crate::pretty(&n.term))),
        ("ok", ok.to_string()),
        ("result", result),
        ("note", jstr(&n.note)),
        ("children", jarr(n.children.iter().map(node_json).collect())),
    ])
}

fn rename_binder_if_needed(ctx: &Context, x: &str, body: &Term) -> (String, Term, bool) {
    if !ctx.iter().any(|(name, _)| name == x) {
        return (x.into(), body.clone(), false);
    }
    let mut used = all_names(body);
    for (name, ty) in ctx {
        used.insert(name.clone());
        used.extend(all_names(ty));
    }
    let renamed = fresh(x, &used);
    (renamed.clone(), subst(body, x, &var(&renamed)), true)
}

fn imax(u: u64, v: u64) -> u64 {
    if v == 0 { 0 } else { u.max(v) }
}

/// Infers the type of `t` while recording the derivation. Mirrors
/// `Kernel::infer` case by case; the kernel's own `whnf` and `is_def_eq`
/// do the computation.
fn derive(k: &Kernel, ctx: &Context, t: &Term, premise: &str) -> Node {
    let mut node = Node {
        rule: String::new(),
        premise: premise.to_string(),
        ctx: ctx.clone(),
        term: t.clone(),
        result: Err(String::new()),
        note: String::new(),
        children: vec![],
    };
    match t {
        Term::Sort(u) => {
            node.rule = "T-Sort".into();
            node.result = u
                .checked_add(1)
                .map(Term::Sort)
                .ok_or_else(|| "universe overflow".to_string());
        }
        Term::Var(x) => {
            node.rule = "T-Var".into();
            node.result = ctx
                .iter()
                .rev()
                .find(|(name, _)| name == x)
                .map(|(_, ty)| ty.clone())
                .ok_or_else(|| format!("unbound local: {x}"));
        }
        Term::Const(c) => {
            node.rule = "T-Const".into();
            node.result = k
                .decls
                .get(c)
                .map(|d| d.ty.clone())
                .ok_or_else(|| format!("unknown constant: {c}"));
        }
        Term::Pi(x, a, b) | Term::Lam(x, a, b) => {
            let is_pi = matches!(t, Term::Pi(..));
            node.rule = (if is_pi { "T-Pi" } else { "T-Lam" }).into();
            let dom = derive_sort(k, ctx, a, "the annotation is a type");
            let dom_level = dom.1;
            node.children.push(dom.0);
            let Some(u) = dom_level else {
                node.result = Err("the binder's type is not a type".into());
                return node;
            };
            let (x2, body, renamed) = rename_binder_if_needed(ctx, x, b);
            if renamed {
                node.note = format!("Freshen: the binder {x} already occurs in the context, so it is renamed to {x2} before entering");
            }
            let mut extended = ctx.clone();
            extended.push((x2.clone(), (**a).clone()));
            if is_pi {
                let (child, level) = derive_sort(k, &extended, &body, "the body is a type under the new assumption");
                node.children.push(child);
                node.result = match level {
                    Some(v) => Ok(Term::Sort(imax(u, v))),
                    None => Err("the body of the Pi is not a type".into()),
                };
                if let Some(v) = level {
                    let _ = write!(node.note, "{}imax({u}, {v}) = {}", if node.note.is_empty() { "" } else { "; " }, imax(u, v));
                }
            } else {
                let child = derive(k, &extended, &body, "the body, under the new assumption");
                let body_type = child.result.clone();
                node.children.push(child);
                node.result = body_type.map(|bt| Term::Pi(x2, a.clone(), Box::new(bt)));
            }
        }
        Term::App(f, a) => {
            node.rule = "T-App".into();
            let fnode = derive(k, ctx, f, "the function");
            let ftype = fnode.result.clone();
            node.children.push(fnode);
            let ftype = match ftype {
                Ok(ty) => ty,
                Err(_) => {
                    node.result = Err("the function is ill typed".into());
                    return node;
                }
            };
            let whnf = match k.whnf(&ftype) {
                Ok(w) => w,
                Err(e) => {
                    node.result = Err(e);
                    return node;
                }
            };
            if whnf != ftype {
                node.note = format!("Whnf exposes the function type: {} computes to {}", crate::pretty(&ftype), crate::pretty(&whnf));
            }
            match whnf {
                Term::Pi(x, domain, codomain) => {
                    let mut anode = derive(k, ctx, a, "the argument");
                    if let Ok(actual) = anode.result.clone() {
                        match k.is_def_eq(&actual, &domain) {
                            Ok(true) => {
                                anode.note = if actual == *domain {
                                    "Check: the argument has exactly the expected type".into()
                                } else {
                                    format!("Check: {} is definitionally equal to the expected {}", crate::pretty(&actual), crate::pretty(&domain))
                                };
                            }
                            Ok(false) => {
                                let msg = format!("type mismatch: the argument has type {} but {} was expected", crate::pretty(&actual), crate::pretty(&domain));
                                anode.note = msg.clone();
                                node.children.push(anode);
                                node.result = Err(msg);
                                return node;
                            }
                            Err(e) => {
                                node.children.push(anode);
                                node.result = Err(e);
                                return node;
                            }
                        }
                    }
                    let ok = anode.result.is_ok();
                    node.children.push(anode);
                    if ok {
                        node.result = Ok(subst(&codomain, &x, a));
                        if fv(&codomain).contains(&x) {
                            let _ = write!(node.note, "{}substitute {} for {x} in the codomain", if node.note.is_empty() { "" } else { "; " }, crate::pretty(a));
                        }
                    } else {
                        node.result = Err("the argument is ill typed".into());
                    }
                }
                other => {
                    node.result = Err(format!("application of non-function: {}", crate::pretty(&other)));
                }
            }
        }
    }
    node
}

/// InferSort as a node: derive the type, then require a universe.
fn derive_sort(k: &Kernel, ctx: &Context, t: &Term, premise: &str) -> (Node, Option<u64>) {
    let mut node = derive(k, ctx, t, premise);
    let level = match &node.result {
        Ok(ty) => match k.whnf(ty) {
            Ok(Term::Sort(u)) => {
                if !matches!(ty, Term::Sort(_)) {
                    let _ = write!(node.note, "{}InferSort: {} computes to Sort {u}", if node.note.is_empty() { "" } else { "; " }, crate::pretty(ty));
                }
                Some(u)
            }
            Ok(other) => {
                node.note = format!("InferSort fails: expected a universe, got {}", crate::pretty(&other));
                None
            }
            Err(e) => {
                node.note = e;
                None
            }
        },
        Err(_) => None,
    };
    (node, level)
}

fn op_derive(req: &Request) -> std::result::Result<String, String> {
    let k = kernel_with_prelude(req.tail)?;
    let ctx = match req.args.get(1) {
        Some(spec) => parse_context(&k, spec)?,
        None => vec![],
    };
    let t = parse_term(&k, &ctx, arg(req, 0, "term")?)?;
    let node = derive(&k, &ctx, &t, "");
    Ok(jobj(vec![("derivation", node_json(&node))]))
}

// ---------------------------------------------------------------------------
// reduce: single head steps, mirroring Whnf
// ---------------------------------------------------------------------------

fn constructor_of<'a>(k: &'a Kernel, name: &str) -> Option<(&'a InductiveInfo, usize)> {
    for (iname, decl) in &k.decls {
        if !matches!(decl.kind, DeclKind::Inductive) {
            continue;
        }
        if let Some(info) = k.inductive(iname) {
            if let Some(j) = info.constructors.iter().position(|c| c.name == name) {
                return Some((info, j));
            }
        }
    }
    None
}

/// One head reduction step: Some((kind, result, redex_args)) or None if stuck.
fn step(k: &Kernel, t: &Term) -> std::result::Result<Option<(&'static str, Term, usize)>, String> {
    let (head, args) = spine(t);
    match &head {
        Term::Lam(x, _, body) if !args.is_empty() => {
            let next = apps(subst(body, x, &args[0]), args[1..].iter().cloned());
            Ok(Some(("beta", next, 1)))
        }
        Term::Const(c) => match k.decls.get(c).map(|d| &d.kind) {
            Some(DeclKind::Definition(body)) => Ok(Some(("delta", apps(body.clone(), args.clone()), 0))),
            Some(DeclKind::Recursor(rec)) => {
                let major = rec.major_argument_index;
                if args.len() <= major {
                    return Ok(None);
                }
                let Some(info) = k.inductive(&rec.inductive) else { return Ok(None) };
                let major_whnf = k.whnf(&args[major])?;
                let (mhead, margs) = spine(&major_whnf);
                let Term::Const(cname) = mhead else { return Ok(None) };
                let Some(j) = info.constructors.iter().position(|c| c.name == cname) else { return Ok(None) };
                let constructor = &info.constructors[j];
                let num_params = info.params.len();
                if margs.len() != num_params + constructor.fields.len() {
                    return Ok(None);
                }
                let field_values = &margs[num_params..];
                let mut inst: HashMap<String, Term> = HashMap::new();
                for ((p, _), v) in info.params.iter().zip(&args) {
                    inst.insert(p.clone(), v.clone());
                }
                for ((f, _), v) in constructor.fields.iter().zip(field_values) {
                    inst.insert(f.clone(), v.clone());
                }
                let leading = num_params + 1 + info.constructors.len();
                let ihs: Vec<Term> = constructor
                    .recursive_fields
                    .iter()
                    .map(|rf| {
                        let binders: Vec<(String, Term)> = rf
                            .argument_binders
                            .iter()
                            .map(|(y, ty)| (y.clone(), subst_many(ty, &inst)))
                            .collect();
                        let targets = rf.target_indices.iter().map(|s| subst_many(s, &inst));
                        let applied = apps(field_values[rf.constructor_field_index].clone(), binders.iter().map(|(y, _)| var(y)));
                        let call = apps(
                            Term::Const(c.clone()),
                            args[..leading].iter().cloned().chain(targets).chain(std::iter::once(applied)),
                        );
                        binders.iter().rev().fold(call, |body, (y, ty)| Term::Lam(y.clone(), Box::new(ty.clone()), Box::new(body)))
                    })
                    .collect();
                let minor = args[num_params + 1 + j].clone();
                let mut new_args = args.clone();
                // The major premise is shown in weak head normal form so the
                // constructor is visible in the marked redex.
                new_args[major] = major_whnf;
                let next = apps(minor, field_values.iter().cloned().chain(ihs).chain(args[major + 1..].iter().cloned()));
                let _ = new_args;
                Ok(Some(("iota", next, major + 1)))
            }
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

fn op_reduce(req: &Request) -> std::result::Result<String, String> {
    let k = kernel_with_prelude(req.tail)?;
    let ctx = match req.args.get(1) {
        Some(spec) => parse_context(&k, spec)?,
        None => vec![],
    };
    let mut t = parse_term(&k, &ctx, arg(req, 0, "term")?)?;
    let mut steps: Vec<String> = vec![];
    let mut current = t.clone();
    let mut guard = 0;
    loop {
        guard += 1;
        if guard > 60 {
            steps.push(jobj(vec![("kind", jstr("limit")), ("note", jstr("stopped after 60 steps"))]));
            break;
        }
        match step(&k, &current)? {
            Some((kind, next, redex_args)) => {
                // If the major premise of an iota step still needed computing,
                // show that computation first as its own step.
                if kind == "iota" {
                    let (_, args) = spine(&current);
                    let major = redex_args - 1;
                    let w = k.whnf(&args[major])?;
                    if w != args[major] {
                        let mut shown = args.clone();
                        shown[major] = w;
                        let (head, _) = spine(&current);
                        let exposed = apps(head, shown);
                        steps.push(jobj(vec![
                            ("kind", jstr("major")),
                            ("before", tokens_marked(&current, redex_args)),
                            ("after", tokens_marked(&exposed, redex_args)),
                            ("note", jstr(&format!("the major premise {} is put in weak head normal form first", crate::pretty(&args[major])))),
                        ]));
                        current = exposed;
                    }
                }
                steps.push(jobj(vec![
                    ("kind", jstr(kind)),
                    ("before", tokens_marked(&current, redex_args)),
                    ("after", tokens(&next)),
                    ("note", jstr("")),
                ]));
                current = next;
            }
            None => break,
        }
    }
    let whnf = current.clone();
    let normal = k.normalize(&t)?;
    let stuck_note = {
        let (head, args) = spine(&whnf);
        match &head {
            Term::Const(c) if matches!(k.decls.get(c).map(|d| &d.kind), Some(DeclKind::Recursor(_))) => {
                let rec_major = if let Some(DeclKind::Recursor(r)) = k.decls.get(c).map(|d| &d.kind) { r.major_argument_index } else { 0 };
                if args.len() > rec_major {
                    format!("stuck: the major premise {} is not a constructor application", crate::pretty(&k.whnf(&args[rec_major])?))
                } else {
                    "stuck: the recursor is waiting for its major premise".into()
                }
            }
            Term::Var(x) => format!("the head is the variable {x}: nothing to compute"),
            Term::Const(c) => format!("the head is the constant {c}, which has no body"),
            Term::Lam(..) => "the head is a function with no argument: weak head normal form".into(),
            Term::Pi(..) => "a Pi type: weak head normal form".into(),
            Term::Sort(_) => "a universe: normal form".into(),
            Term::App(..) => String::new(),
        }
    };
    t = normal;
    Ok(jobj(vec![
        ("steps", jarr(steps)),
        ("whnf", tokens(&whnf)),
        ("normal", tokens(&t)),
        ("whnfIsNormal", (if whnf == t { "true" } else { "false" }).to_string()),
        ("stuck", jstr(&stuck_note)),
    ]))
}

// ---------------------------------------------------------------------------
// scope and subst
// ---------------------------------------------------------------------------

fn op_scope(req: &Request) -> std::result::Result<String, String> {
    let k = kernel_with_prelude(req.tail)?;
    let t = parse_loose(&k, arg(req, 0, "term")?)?;
    let free: Vec<String> = {
        let mut v: Vec<String> = fv(&t).into_iter().collect();
        v.sort();
        v
    };
    Ok(jobj(vec![
        ("tokens", tokens(&t)),
        ("free", jarr(free.iter().map(|x| jstr(x)).collect())),
    ]))
}

/// Parses a term in which unknown identifiers are allowed as free variables,
/// which the scope and substitution explorers need (the kernel's parser
/// rejects them). Free names are collected by a pre-pass over the text.
fn parse_loose(k: &Kernel, text: &str) -> std::result::Result<Term, String> {
    let mut names: Vec<String> = vec![];
    let mut cur = String::new();
    for ch in text.chars().chain(std::iter::once(' ')) {
        if ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '.' {
            cur.push(ch);
        } else {
            if !cur.is_empty() && !cur.chars().next().unwrap().is_ascii_digit() && !names.contains(&cur) {
                names.push(cur.clone());
            }
            cur.clear();
        }
    }
    let reserved = ["fun", "forall", "Sort"];
    let ctx: Context = names
        .iter()
        .filter(|n| !reserved.contains(&n.as_str()) && k.type_of_const(n).is_none())
        .map(|n| (n.clone(), Term::Sort(0)))
        .collect();
    // The context types are placeholders: scope only needs the names.
    parse_term(k, &ctx, text)
}

fn naive_subst(t: &Term, x: &str, s: &Term) -> Term {
    match t {
        Term::Sort(_) | Term::Const(_) => t.clone(),
        Term::Var(y) => if y == x { s.clone() } else { t.clone() },
        Term::App(f, a) => Term::App(Box::new(naive_subst(f, x, s)), Box::new(naive_subst(a, x, s))),
        Term::Pi(y, a, b) => {
            let body = if y == x { (**b).clone() } else { naive_subst(b, x, s) };
            Term::Pi(y.clone(), Box::new(naive_subst(a, x, s)), Box::new(body))
        }
        Term::Lam(y, a, b) => {
            let body = if y == x { (**b).clone() } else { naive_subst(b, x, s) };
            Term::Lam(y.clone(), Box::new(naive_subst(a, x, s)), Box::new(body))
        }
    }
}

fn op_subst(req: &Request) -> std::result::Result<String, String> {
    let k = kernel_with_prelude(req.tail)?;
    let t = parse_loose(&k, arg(req, 0, "term")?)?;
    let x = arg(req, 1, "variable")?;
    let s = parse_loose(&k, arg(req, 2, "replacement")?)?;
    let naive = naive_subst(&t, x, &s);
    let safe = subst(&t, x, &s);
    let captured = naive != safe;
    let note = if !fv(&t).contains(x) {
        format!("{x} does not occur free in the term, so nothing is replaced")
    } else if captured {
        let caught: Vec<String> = fv(&s).into_iter().filter(|v| {
            // A free variable of the replacement that some binder in t would capture.
            fn binds(t: &Term, v: &str) -> bool {
                match t {
                    Term::Pi(y, a, b) | Term::Lam(y, a, b) => y == v || binds(a, v) || binds(b, v),
                    Term::App(f, a) => binds(f, v) || binds(a, v),
                    _ => false,
                }
            }
            binds(&t, v)
        }).collect();
        format!("the replacement mentions {}, which a binder in the term would capture; capture-avoiding substitution renames that binder first", caught.join(", "))
    } else {
        "no binder in the term binds a free variable of the replacement, so both substitutions agree".into()
    };
    Ok(jobj(vec![
        ("term", tokens(&t)),
        ("replacement", tokens(&s)),
        ("naive", tokens(&naive)),
        ("safe", tokens(&safe)),
        ("captured", (if captured { "true" } else { "false" }).to_string()),
        ("note", jstr(&note)),
    ]))
}

// ---------------------------------------------------------------------------
// trace: the proof state after every command
// ---------------------------------------------------------------------------

fn template_to_term(t: &Template) -> Term {
    match t {
        Template::Fixed(x) => x.clone(),
        Template::Hole(i) => Term::Var(format!("?{i}")),
        Template::App(f, a) => Term::App(Box::new(template_to_term(f)), Box::new(template_to_term(a))),
        Template::Lam(x, a, b) => Term::Lam(x.clone(), Box::new(a.clone()), Box::new(template_to_term(b))),
    }
}

fn goals_json(s: &mini_lean4::proof::ProofState) -> String {
    jarr(
        s.goals()
            .iter()
            .map(|g| {
                jobj(vec![
                    ("id", g.id.to_string()),
                    ("hyps", jarr(g.context.iter().map(|(x, ty)| jobj(vec![("name", jstr(x)), ("type", jstr(&crate::pretty(&beta_head(ty))))])).collect())),
                    ("target", jstr(&crate::pretty(&beta_head(&g.target)))),
                ])
            })
            .collect(),
    )
}

fn op_trace(req: &Request) -> std::result::Result<String, String> {
    let script = req.tail.ok_or("missing script")?;
    let mut k = Kernel::standard();
    let mut state: Option<mini_lean4::proof::ProofState> = None;
    let lines: Vec<String> = script.lines().map(|s| s.to_string()).collect();
    let mut steps: Vec<String> = vec![];
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim().to_string();
        let start = i;
        if line.is_empty() || line.starts_with('#') {
            i += 1;
            continue;
        }
        let mut sink = String::new();
        let result: Result<()> = if line.starts_with("inductive ") {
            let mut block = vec![lines[i].clone()];
            i += 1;
            while i < lines.len() && (lines[i].trim().starts_with('|') || lines[i].trim().is_empty()) {
                if !lines[i].trim().is_empty() {
                    block.push(lines[i].clone());
                }
                i += 1;
            }
            mini_lean4::syntax::parse_inductive(&k, &block).and_then(|spec| k.add_inductive(spec))
        } else {
            i += 1;
            crate::run_line(&mut k, &mut state, &line, &mut sink)
        };
        let kind = if line.starts_with("goal ") {
            "goal"
        } else if line.starts_with("def ") || line.starts_with("axiom ") || line.starts_with("inductive ") || line.starts_with("recursor ") {
            "setup"
        } else if line == "qed" {
            "qed"
        } else {
            "tactic"
        };
        let (goals, term, current) = match &state {
            Some(s) => (
                goals_json(s),
                tokens(&template_to_term(&s.partial_proof())),
                s.goals().first().map(|g| g.id as i64).unwrap_or(-1),
            ),
            None => ("[]".to_string(), "[]".to_string(), -1),
        };
        let mut fields = vec![
            ("line", (start + 1).to_string()),
            ("command", jstr(&line)),
            ("kind", jstr(kind)),
            ("goals", goals),
            ("term", term),
            ("current", current.to_string()),
        ];
        match result {
            Ok(()) => {
                if kind == "qed" {
                    // The transcript contains the checked term.
                    let checked = sink.lines().skip(2).collect::<Vec<_>>().join("\n");
                    fields.push(("checked", jstr(&checked)));
                }
                fields.push(("error", "null".to_string()));
                steps.push(jobj(fields));
            }
            Err(e) => {
                fields.push(("error", jstr(&prettify_debug_terms(&e))));
                steps.push(jobj(fields));
                break;
            }
        }
    }
    Ok(jobj(vec![("steps", jarr(steps))]))
}

// ---------------------------------------------------------------------------
// ctree: a value as a tree of constructor applications
// ---------------------------------------------------------------------------

fn ctree_json(k: &Kernel, t: &Term) -> String {
    let (head, args) = spine(t);
    if let Term::Const(c) = &head {
        if let Some((info, j)) = constructor_of(k, c) {
            let ctor = &info.constructors[j];
            let np = info.params.len();
            if args.len() == np + ctor.fields.len() {
                let mut fields: Vec<String> = vec![];
                let mut case = format!("m_{}", ctor.name.rsplit('.').next().unwrap_or(&ctor.name));
                let mut ihs: Vec<String> = vec![];
                for (fi, (fname, _)) in ctor.fields.iter().enumerate() {
                    let value = &args[np + fi];
                    let recursive = ctor.recursive_fields.iter().any(|rf| rf.constructor_field_index == fi);
                    let child = if recursive { ctree_json(k, value) } else { "null".to_string() };
                    fields.push(jobj(vec![
                        ("name", jstr(fname)),
                        ("value", jstr(&crate::pretty(value))),
                        ("recursive", (if recursive { "true" } else { "false" }).to_string()),
                        ("child", child),
                    ]));
                    let _ = write!(case, " {fname}");
                    if recursive {
                        ihs.push(format!("(R {fname})"));
                    }
                }
                for ih in &ihs {
                    let _ = write!(case, " {ih}");
                }
                return jobj(vec![
                    ("ctor", jstr(&ctor.name)),
                    ("inductive", jstr(&info.name)),
                    ("params", jarr(args[..np].iter().map(|p| jstr(&crate::pretty(p))).collect())),
                    ("fields", jarr(fields)),
                    ("case", jstr(&case)),
                    ("pretty", jstr(&crate::pretty(t))),
                ]);
            }
        }
    }
    jobj(vec![("leaf", jstr(&crate::pretty(t))), ("pretty", jstr(&crate::pretty(t)))])
}

fn op_ctree(req: &Request) -> std::result::Result<String, String> {
    let k = kernel_with_prelude(req.tail)?;
    let t = parse_term(&k, &vec![], arg(req, 0, "term")?)?;
    let value = k.normalize(&t)?;
    Ok(jobj(vec![("tree", ctree_json(&k, &value)), ("tokens", tokens_in_context(&vec![], &value))]))
}
