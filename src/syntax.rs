//! Tiny, explicit-input frontend. Not a full Lean 4 elaborator.

use crate::{
    declaration::{ConstructorSpec, Context, InductiveSpec},
    kernel::{Kernel, Result},
    term::{
        app, arrow, const_term, lam, pi, var,
        Term::{self, Sort},
    },
};

fn tokenize(input: &str) -> Result<Vec<String>> {
    let mut out = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(c) = chars.next() {
        if c.is_whitespace() {
            continue;
        }
        if c == '-' && chars.peek() == Some(&'>') {
            chars.next();
            out.push("->".into());
            continue;
        }
        if c == '=' && chars.peek() == Some(&'>') {
            chars.next();
            out.push("=>".into());
            continue;
        }
        if "(),:".contains(c) {
            out.push(c.to_string());
            continue;
        }
        if c == '→' {
            out.push("->".into());
            continue;
        }
        if c == 'λ' {
            out.push("fun".into());
            continue;
        }
        if c == '∀' {
            out.push("forall".into());
            continue;
        }
        if c.is_alphanumeric() || c == '_' || c == '\'' || c == '.' {
            let mut s = c.to_string();
            while let Some(d) = chars.peek() {
                if d.is_alphanumeric() || *d == '_' || *d == '\'' || *d == '.' {
                    s.push(*d);
                    chars.next();
                } else {
                    break;
                }
            }
            out.push(s);
            continue;
        }
        return Err(format!("unexpected character: {c}"));
    }
    Ok(out)
}
struct Parser<'a> {
    toks: Vec<String>,
    at: usize,
    k: &'a Kernel,
    locals: Vec<String>,
    known: Vec<String>,
}
impl Parser<'_> {
    fn peek(&self) -> Option<&str> {
        self.toks.get(self.at).map(|s| s.as_str())
    }
    fn take(&mut self) -> Result<String> {
        let s = self.peek().ok_or("unexpected end of term")?.to_string();
        self.at += 1;
        Ok(s)
    }
    fn eat(&mut self, s: &str) -> bool {
        if self.peek() == Some(s) {
            self.at += 1;
            true
        } else {
            false
        }
    }
    fn expect(&mut self, s: &str) -> Result<()> {
        if self.eat(s) {
            Ok(())
        } else {
            Err(format!("expected '{s}', got {:?}", self.peek()))
        }
    }
    fn starts_atom(&self) -> bool {
        match self.peek() {
            Some("(") => true,
            Some("fun") | Some("forall") | Some(")") | Some(",") | Some("->") | Some("=>")
            | Some(":") | None => false,
            Some(_) => true,
        }
    }
    fn term(&mut self) -> Result<Term> {
        if self.eat("fun") {
            self.expect("(")?;
            let name = self.take()?;
            self.expect(":")?;
            let ty = self.term()?;
            self.expect(")")?;
            self.expect("=>")?;
            self.locals.push(name.clone());
            let b = self.term()?;
            self.locals.pop();
            return Ok(lam(&name, ty, b));
        }
        if self.eat("forall") {
            self.expect("(")?;
            let name = self.take()?;
            self.expect(":")?;
            let ty = self.term()?;
            self.expect(")")?;
            self.expect(",")?;
            self.locals.push(name.clone());
            let b = self.term()?;
            self.locals.pop();
            return Ok(pi(&name, ty, b));
        }
        let lhs = self.application()?;
        if self.eat("->") {
            Ok(arrow(lhs, self.term()?))
        } else {
            Ok(lhs)
        }
    }
    fn application(&mut self) -> Result<Term> {
        let mut t = self.atom()?;
        while self.starts_atom() {
            t = app(t, self.atom()?);
        }
        Ok(t)
    }
    fn atom(&mut self) -> Result<Term> {
        if self.eat("(") {
            let t = self.term()?;
            self.expect(")")?;
            return Ok(t);
        }
        let name = self.take()?;
        if name == "Sort" {
            let level = self
                .take()?
                .parse::<u64>()
                .map_err(|_| "expected universe level")?;
            return Ok(Sort(level));
        }
        if self.locals.iter().any(|x| x == &name) {
            Ok(var(&name))
        } else if self.k.type_of_const(&name).is_some() || self.known.contains(&name) {
            Ok(const_term(&name))
        } else {
            Err(format!("unknown identifier: {name}"))
        }
    }
}
pub fn parse_term(k: &Kernel, ctx: &Context, input: &str) -> Result<Term> {
    parse_term_known(k, ctx, input, &[])
}
pub fn parse_term_known(k: &Kernel, ctx: &Context, input: &str, known: &[String]) -> Result<Term> {
    let toks = tokenize(input)?;
    let mut p = Parser {
        toks,
        at: 0,
        k,
        locals: ctx.iter().map(|(x, _)| x.clone()).collect(),
        known: known.to_vec(),
    };
    let t = p.term()?;
    if p.peek().is_some() {
        Err(format!("unexpected token: {:?}", p.peek()))
    } else {
        Ok(t)
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn parse_identity() {
        let k = Kernel::standard();
        let t = parse_term(&k, &vec![], "fun (P : Sort 0) => fun (p : P) => p").unwrap();
        let ty = parse_term(&k, &vec![], "forall (P : Sort 0), P -> P").unwrap();
        k.check(&vec![], &t, &ty).unwrap();
    }
}

/// Educational surface format:
/// `inductive List (A : Sort 1) : Sort 1 where`
/// `| nil`
/// `| cons (head : A) (tail : List A)`
/// and indexed:
/// `inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where`
/// `| nil : Vec A Nat.zero`
/// `| cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)`
/// The grammar requires explicit constructor fields; names and universe levels are explicit.
fn binder_chunks(src: &str) -> Result<(Vec<(bool, String, String)>, String)> {
    let mut text = src.trim();
    let mut out = vec![];
    while text.starts_with('(') {
        let end = text.find(')').ok_or("unclosed binder")?;
        let body = text[1..end].trim();
        let (flag, body) = if let Some(t) = body.strip_prefix("index ") {
            (true, t)
        } else {
            (false, body)
        };
        let (name, ty) = body.split_once(':').ok_or("expected (name : type)")?;
        let name = name.trim();
        if name.is_empty() || name.contains(' ') {
            return Err("invalid binder name".into());
        }
        out.push((flag, name.into(), ty.trim().into()));
        text = text[end + 1..].trim_start();
    }
    Ok((out, text.to_string()))
}
fn extract_result(t: Term, ind: &str, params: &Context, nindices: usize) -> Result<Vec<Term>> {
    let mut args = vec![];
    let mut head = &t;
    while let Term::App(f, a) = head {
        args.push((**a).clone());
        head = f;
    }
    args.reverse();
    if head != &Term::Const(ind.into()) || args.len() != params.len() + nindices {
        return Err(format!(
            "constructor result must be {ind} applied to parameters and indices"
        ));
    }
    for (a, (p, _)) in args.iter().zip(params.iter()) {
        if a != &var(p) {
            return Err("constructor parameters must be uniform".into());
        }
    }
    Ok(args[params.len()..].to_vec())
}
pub fn parse_inductive(k: &Kernel, lines: &[String]) -> Result<InductiveSpec> {
    let header = lines.first().ok_or("missing inductive header")?.trim();
    let rest = header
        .strip_prefix("inductive ")
        .ok_or("expected inductive declaration")?;
    let split = rest
        .find(|c: char| c == ' ' || c == ':')
        .unwrap_or(rest.len());
    let name = &rest[..split];
    if name.is_empty() {
        return Err("missing inductive name".into());
    }
    let (bindings, tail) = binder_chunks(&rest[split..])?;
    let universe = tail
        .strip_prefix(':')
        .ok_or("expected : Sort u where")?
        .trim();
    let universe = universe
        .strip_suffix("where")
        .ok_or("expected where")?
        .trim();
    let mut params = vec![];
    let mut indices = vec![];
    let mut index_started = false;
    for (index, n, ty) in bindings {
        if !index && index_started {
            return Err("parameters must precede indices".into());
        }
        index_started |= index;
        let mut ctx = params.clone();
        ctx.extend(indices.clone());
        let t = parse_term(k, &ctx, &ty)?;
        if index {
            indices.push((n, t));
        } else {
            params.push((n, t));
        }
    }
    let mut header_ctx = params.clone();
    header_ctx.extend(indices.clone());
    let universe_level = match parse_term(k, &header_ctx, universe)? {
        Term::Sort(u) => u,
        _ => return Err("inductive result must be Sort u".into()),
    };
    let mut constructors = vec![];
    for line in lines.iter().skip(1) {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let line = line
            .strip_prefix('|')
            .ok_or("constructor lines must begin with |")?
            .trim();
        let split = line
            .find(|c: char| c == ' ' || c == '(' || c == ':')
            .unwrap_or(line.len());
        let ctor = &line[..split];
        if ctor.is_empty() {
            return Err("empty constructor".into());
        }
        let (binders, tail) = binder_chunks(&line[split..])?;
        let mut fields = vec![];
        let mut ctx = params.clone();
        let known = vec![name.to_string()];
        for (is_index, n, ty) in binders {
            if is_index {
                return Err("index binder only permitted in header".into());
            }
            let t = parse_term_known(k, &ctx, &ty, &known)?;
            ctx.push((n.clone(), t.clone()));
            fields.push((n, t));
        }
        let result_indices = if tail.trim().is_empty() {
            if !indices.is_empty() {
                return Err("indexed constructor requires explicit result type".into());
            }
            vec![]
        } else {
            let result = tail
                .trim()
                .strip_prefix(':')
                .ok_or("expected : result type")?
                .trim();
            extract_result(
                parse_term_known(k, &ctx, result, &known)?,
                name,
                &params,
                indices.len(),
            )?
        };
        constructors.push(ConstructorSpec {
            name: format!("{name}.{ctor}"),
            fields,
            result_indices,
        });
    }
    Ok(InductiveSpec {
        name: name.into(),
        params,
        indices,
        universe_level,
        constructors,
    })
}

#[cfg(test)]
mod inductive_parser_tests {
    use super::*;
    #[test]
    fn parse_list_and_indexed_vec() {
        let mut k = Kernel::standard();
        let list = parse_inductive(
            &k,
            &[
                "inductive List (A : Sort 1) : Sort 1 where".into(),
                "| nil".into(),
                "| cons (head : A) (tail : List A)".into(),
            ],
        )
        .unwrap();
        k.add_inductive(list).unwrap();
        assert!(k.type_of_const("List.rec1").is_some());
        let vec = parse_inductive(
            &k,
            &[
                "inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where".into(),
                "| nil : Vec A Nat.zero".into(),
                "| cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)".into(),
            ],
        )
        .unwrap();
        k.add_inductive(vec).unwrap();
        assert!(k.type_of_const("Vec.rec1").is_some());
    }
}
