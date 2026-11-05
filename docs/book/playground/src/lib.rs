//! WebAssembly entry point for the ebook playground.
//!
//! Mirrors the script semantics of `src/main.rs` in the root crate, but
//! accumulates the transcript into a buffer that JavaScript reads back.

use mini_lean4::{
    declaration::Context,
    kernel::{Kernel, Result},
    proof::{Goal, ProofState},
    substitution::{fv, subst},
    syntax::{parse_inductive, parse_term},
    term::{apps, spine, Term},
};
use std::fmt::Write as _;

// ---------------------------------------------------------------------------
// C ABI: memory management and the result buffer
// ---------------------------------------------------------------------------

static mut RESULT: Vec<u8> = Vec::new();

#[no_mangle]
pub extern "C" fn alloc(len: usize) -> *mut u8 {
    let mut buf = Vec::<u8>::with_capacity(len.max(1));
    let ptr = buf.as_mut_ptr();
    std::mem::forget(buf);
    ptr
}

/// # Safety
/// `ptr` must come from `alloc(len)`.
#[no_mangle]
pub unsafe extern "C" fn dealloc(ptr: *mut u8, len: usize) {
    drop(Vec::from_raw_parts(ptr, 0, len.max(1)));
}

/// # Safety
/// `ptr..ptr+len` must be readable UTF-8 bytes.
#[no_mangle]
pub unsafe extern "C" fn run_script(ptr: *const u8, len: usize) -> usize {
    let bytes = std::slice::from_raw_parts(ptr, len);
    let script = String::from_utf8_lossy(bytes);
    let out = run(&script);
    let result = &mut *std::ptr::addr_of_mut!(RESULT);
    *result = out.into_bytes();
    result.len()
}

#[no_mangle]
pub extern "C" fn result_ptr() -> *const u8 {
    unsafe { (*std::ptr::addr_of!(RESULT)).as_ptr() }
}

#[no_mangle]
pub extern "C" fn result_len() -> usize {
    unsafe { (*std::ptr::addr_of!(RESULT)).len() }
}

// ---------------------------------------------------------------------------
// Pretty-printing in leanmini surface syntax
// ---------------------------------------------------------------------------

fn is_atom(t: &Term) -> bool {
    matches!(t, Term::Var(_) | Term::Const(_))
}

fn is_binder(t: &Term) -> bool {
    matches!(t, Term::Pi(..) | Term::Lam(..))
}

/// Surface syntax that `syntax::parse_term` reads back.
pub fn pretty(t: &Term) -> String {
    match t {
        Term::Sort(u) => format!("Sort {u}"),
        Term::Var(x) | Term::Const(x) => x.clone(),
        Term::Pi(x, a, b) => {
            if x == "_" || !fv(b).contains(x) {
                // The domain of an arrow may itself be an arrow or binder.
                let dom = if is_binder(a) {
                    format!("({})", pretty(a))
                } else {
                    pretty(a)
                };
                format!("{dom} -> {}", pretty(b))
            } else {
                format!("forall ({x} : {}), {}", pretty(a), pretty(b))
            }
        }
        Term::Lam(x, a, b) => format!("fun ({x} : {}) => {}", pretty(a), pretty(b)),
        Term::App(f, a) => {
            let fs = if is_binder(f) {
                format!("({})", pretty(f))
            } else {
                pretty(f)
            };
            let arg = if is_atom(a) {
                pretty(a)
            } else {
                format!("({})", pretty(a))
            };
            format!("{fs} {arg}")
        }
    }
}

/// Beta-reduces at the head only, so that a goal produced by `induction`,
/// such as `(fun (x : Nat) => P x) Nat.zero`, is displayed as `P Nat.zero`.
/// Definitions are not unfolded and nothing below the head is touched.
fn beta_head(t: &Term) -> Term {
    let (head, args) = spine(t);
    let mut head = head;
    let mut rest = args.as_slice();
    while let (Term::Lam(x, _, body), [first, tail @ ..]) = (&head, rest) {
        head = subst(body, x, first);
        rest = tail;
    }
    apps(head, rest.iter().cloned())
}

fn print_goal(out: &mut String, g: &Goal) {
    let _ = writeln!(out, "?{}:", g.id);
    for (x, t) in &g.context {
        let _ = writeln!(out, "  {x} : {}", pretty(&beta_head(t)));
    }
    let _ = writeln!(out, "  \u{22a2} {}", pretty(&beta_head(&g.target)));
}

fn print_goals(out: &mut String, s: &ProofState) {
    if s.goals().is_empty() {
        out.push_str("No goals. Run 'qed' to kernel-check.\n");
    } else {
        for g in s.goals() {
            print_goal(out, g);
        }
    }
}

// ---------------------------------------------------------------------------
// Script runner (same commands as src/main.rs)
// ---------------------------------------------------------------------------

fn run_line(k: &mut Kernel, state: &mut Option<ProofState>, line: &str, out: &mut String) -> Result<()> {
    let line = line.trim();
    if line.is_empty() || line.starts_with('#') {
        return Ok(());
    }
    if line == "quit" || line == "exit" {
        return Ok(());
    }
    let _ = writeln!(out, "> {line}");
    if let Some(rest) = line.strip_prefix("recursor ") {
        let (name, level) = rest.split_once(' ').ok_or("recursor I <level>")?;
        let level = level
            .trim()
            .parse::<u64>()
            .map_err(|_| "invalid universe level")?;
        k.register_recursor(name.trim(), level)?;
        let _ = writeln!(out, "generated {}.rec{}", name.trim(), level);
        return Ok(());
    }
    if let Some(rest) = line.strip_prefix("axiom ") {
        let (name, ty) = rest.split_once(':').ok_or("axiom name : type")?;
        let t = parse_term(k, &vec![], ty.trim())?;
        k.axiom(name.trim(), t)?;
        let _ = writeln!(out, "added axiom {}", name.trim());
        return Ok(());
    }
    if let Some(rest) = line.strip_prefix("def ") {
        let (name_and_ty, body) = rest.split_once(":=").ok_or("def name : type := term")?;
        let (name, ty) = name_and_ty
            .split_once(':')
            .ok_or("def name : type := term")?;
        let ty = parse_term(k, &vec![], ty.trim())?;
        let body = parse_term(k, &vec![], body.trim())?;
        k.define(name.trim(), ty, body)?;
        let _ = writeln!(out, "defined {}", name.trim());
        return Ok(());
    }
    if let Some(rest) = line.strip_prefix("goal ") {
        let ty = parse_term(k, &vec![], rest)?;
        let s = ProofState::new(k, ty)?;
        print_goals(out, &s);
        *state = Some(s);
        return Ok(());
    }
    let s = state.as_mut().ok_or("start with 'goal <type>'")?;
    let goal = s.goals().first().cloned();
    let ctx_of = |g: &Option<Goal>| -> Result<Context> {
        Ok(g.as_ref().ok_or("no goals")?.context.clone())
    };
    if let Some(name) = line.strip_prefix("intro ") {
        s.intro(k, name.trim())?;
    } else if let Some(n) = line.strip_prefix("induction ") {
        s.induction(k, n.trim())?;
    } else if let Some(input) = line.strip_prefix("exact ") {
        let t = parse_term(k, &ctx_of(&goal)?, input)?;
        s.exact(k, t)?;
    } else if let Some(input) = line.strip_prefix("apply ") {
        let t = parse_term(k, &ctx_of(&goal)?, input)?;
        s.apply(k, t)?;
    } else if let Some(input) = line.strip_prefix("change ") {
        let t = parse_term(k, &ctx_of(&goal)?, input)?;
        s.change(k, t)?;
    } else if let Some(input) = line.strip_prefix("rw ") {
        let t = parse_term(k, &ctx_of(&goal)?, input)?;
        s.rw(k, t)?;
    } else if line == "rfl" {
        s.rfl(k)?;
    } else if line == "qed" {
        let term = s.finish(k)?;
        let _ = writeln!(out, "QED. Kernel checked proof:\n{}", pretty(&term));
        *state = None;
        return Ok(());
    } else if line != "show" {
        return Err(format!("unknown command: {line}"));
    }
    print_goals(out, s);
    Ok(())
}

/// Runs a whole `.leanmini` script and returns the transcript.
pub fn run(script: &str) -> String {
    let mut out = String::new();
    let mut k = Kernel::standard();
    let mut state: Option<ProofState> = None;
    let lines: Vec<String> = script.lines().map(|s| s.to_string()).collect();
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();
        let start = i;
        let result: Result<()> = if line.starts_with("inductive ") {
            let mut block = vec![lines[i].clone()];
            i += 1;
            while i < lines.len()
                && (lines[i].trim().starts_with('|') || lines[i].trim().is_empty())
            {
                if !lines[i].trim().is_empty() {
                    block.push(lines[i].clone());
                }
                i += 1;
            }
            for l in &block {
                let _ = writeln!(&mut out, "> {}", l.trim());
            }
            parse_inductive(&k, &block).and_then(|spec| {
                let name = spec.name.clone();
                k.add_inductive(spec)?;
                let _ = writeln!(&mut out, "inductive {name} registered");
                Ok(())
            })
        } else {
            let r = run_line(&mut k, &mut state, &lines[i], &mut out);
            i += 1;
            r
        };
        if let Err(e) = result {
            let _ = writeln!(&mut out, "error (line {}): {}", start + 1, prettify_debug_terms(&e));
            break;
        }
    }
    if out.is_empty() {
        out.push_str("(empty script)\n");
    }
    out
}

// ---------------------------------------------------------------------------
// Kernel errors embed terms in Rust `Debug` syntax, e.g. `Pi("h", Var("P"), Sort(0))`.
// Rewrite every such fragment in leanmini syntax so the transcript stays readable.
// ---------------------------------------------------------------------------

fn prettify_debug_terms(message: &str) -> String {
    let bytes = message.as_bytes();
    let mut out = String::new();
    let mut i = 0;
    while i < bytes.len() {
        match parse_debug_term(bytes, i) {
            Some((term, next)) => {
                out.push_str(&pretty(&term));
                i = next;
            }
            None => {
                let ch = message[i..].chars().next().unwrap();
                out.push(ch);
                i += ch.len_utf8();
            }
        }
    }
    out
}

fn parse_debug_term(s: &[u8], i: usize) -> Option<(Term, usize)> {
    fn starts(s: &[u8], i: usize, pat: &str) -> bool {
        s[i..].starts_with(pat.as_bytes())
    }
    fn quoted(s: &[u8], i: usize) -> Option<(String, usize)> {
        if s.get(i) != Some(&b'"') {
            return None;
        }
        let end = i + 1 + s[i + 1..].iter().position(|&b| b == b'"')?;
        Some((String::from_utf8_lossy(&s[i + 1..end]).into_owned(), end + 1))
    }
    fn comma(s: &[u8], i: usize) -> Option<usize> {
        if starts(s, i, ", ") { Some(i + 2) } else { None }
    }
    fn close(s: &[u8], i: usize) -> Option<usize> {
        if s.get(i) == Some(&b')') { Some(i + 1) } else { None }
    }
    if starts(s, i, "Sort(") {
        let j = i + 5;
        let end = j + s[j..].iter().position(|&b| b == b')')?;
        let level: u64 = std::str::from_utf8(&s[j..end]).ok()?.parse().ok()?;
        return Some((Term::Sort(level), end + 1));
    }
    if starts(s, i, "Var(") {
        let (name, j) = quoted(s, i + 4)?;
        return Some((Term::Var(name), close(s, j)?));
    }
    if starts(s, i, "Const(") {
        let (name, j) = quoted(s, i + 6)?;
        return Some((Term::Const(name), close(s, j)?));
    }
    if starts(s, i, "Pi(") || starts(s, i, "Lam(") {
        let is_pi = starts(s, i, "Pi(");
        let (name, j) = quoted(s, if is_pi { i + 3 } else { i + 4 })?;
        let j = comma(s, j)?;
        let (domain, j) = parse_debug_term(s, j)?;
        let j = comma(s, j)?;
        let (body, j) = parse_debug_term(s, j)?;
        let j = close(s, j)?;
        let term = if is_pi {
            Term::Pi(name, Box::new(domain), Box::new(body))
        } else {
            Term::Lam(name, Box::new(domain), Box::new(body))
        };
        return Some((term, j));
    }
    if starts(s, i, "App(") {
        let (f, j) = parse_debug_term(s, i + 4)?;
        let j = comma(s, j)?;
        let (a, j) = parse_debug_term(s, j)?;
        let j = close(s, j)?;
        return Some((Term::App(Box::new(f), Box::new(a)), j));
    }
    None
}
