use mini_lean4::{
    kernel::{Kernel, Result},
    proof::ProofState,
    syntax::{parse_inductive, parse_term},
};
use std::{
    env, fs,
    io::{self, BufRead},
};

fn run_line(k: &mut Kernel, state: &mut Option<ProofState>, line: &str) -> Result<bool> {
    let line = line.trim();
    if line.is_empty() || line.starts_with('#') {
        return Ok(true);
    }
    if line == "quit" || line == "exit" {
        return Ok(false);
    }
    if let Some(rest) = line.strip_prefix("recursor ") {
        let (name, level) = rest.split_once(' ').ok_or("recursor I <level>")?;
        let level = level
            .trim()
            .parse::<u64>()
            .map_err(|_| "invalid universe level")?;
        k.ensure_recursor_level(name.trim(), level)?;
        println!("generated {}.rec{}", name.trim(), level);
        return Ok(true);
    }
    if let Some(rest) = line.strip_prefix("axiom ") {
        let (name, ty) = rest.split_once(':').ok_or("axiom name : type")?;
        let t = parse_term(k, &vec![], ty.trim())?;
        k.axiom(name.trim(), t)?;
        println!("added axiom {}", name.trim());
        return Ok(true);
    }
    if let Some(rest) = line.strip_prefix("def ") {
        let (name_and_ty, body) = rest.split_once(":=").ok_or("def name : type := term")?;
        let (name, ty) = name_and_ty
            .split_once(':')
            .ok_or("def name : type := term")?;
        let ty = parse_term(k, &vec![], ty.trim())?;
        let body = parse_term(k, &vec![], body.trim())?;
        k.define(name.trim(), ty, body)?;
        println!("defined {}", name.trim());
        return Ok(true);
    }
    if let Some(rest) = line.strip_prefix("goal ") {
        let ty = parse_term(k, &vec![], rest)?;
        *state = Some(ProofState::new(k, ty)?);
        return Ok(true);
    }
    let s = state.as_mut().ok_or("start with 'goal <type>'")?;
    let goal = s.goals().first().cloned();
    if let Some(name) = line.strip_prefix("intro ") {
        s.intro(k, name.trim())?;
    } else if let Some(n) = line.strip_prefix("induction ") {
        s.induction(k, n.trim())?;
    } else if let Some(input) = line.strip_prefix("exact ") {
        let g = goal.ok_or("no goals")?;
        let t = parse_term(k, &g.context, input)?;
        s.exact(k, t)?;
    } else if let Some(input) = line.strip_prefix("apply ") {
        let g = goal.ok_or("no goals")?;
        let t = parse_term(k, &g.context, input)?;
        s.apply(k, t)?;
    } else if let Some(input) = line.strip_prefix("change ") {
        let g = goal.ok_or("no goals")?;
        let t = parse_term(k, &g.context, input)?;
        s.change(k, t)?;
    } else if let Some(input) = line.strip_prefix("rw ") {
        let g = goal.ok_or("no goals")?;
        let t = parse_term(k, &g.context, input)?;
        s.rw(k, t)?;
    } else if line == "rfl" {
        s.rfl(k)?;
    } else if line == "qed" {
        let term = s.finish(k)?;
        println!("QED. Kernel checked proof:\n{term:#?}");
        *state = None;
        return Ok(true);
    } else if line != "show" {
        return Err(format!("unknown command: {line}"));
    }
    if s.goals().is_empty() {
        println!("No goals. Run 'qed' to kernel-check.");
    } else {
        for g in s.goals() {
            println!("?{}:", g.id);
            for (x, t) in &g.context {
                println!("  {x} : {t:?}");
            }
            println!("  ⊢ {:?}", g.target);
        }
    }
    Ok(true)
}
fn main() {
    let mut k = Kernel::standard();
    let mut state = None;
    let input = env::args().nth(1).and_then(|p| fs::read_to_string(p).ok());
    if let Some(script) = input {
        let lines: Vec<String> = script.lines().map(|s| s.to_string()).collect();
        let mut i = 0;
        while i < lines.len() {
            let line = lines[i].trim();
            let result = if line.starts_with("inductive ") {
                let start = i;
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
                parse_inductive(&k, &block)
                    .and_then(|spec| {
                        let name = spec.name.clone();
                        k.add_inductive(spec)?;
                        println!("inductive {name} registered");
                        Ok(())
                    })
                    .map_err(|e| format!("line {}: {e}", start + 1))
            } else {
                let out = run_line(&mut k, &mut state, &lines[i]).map(|_| ());
                i += 1;
                out
            };
            if let Err(e) = result {
                eprintln!("{e}");
                std::process::exit(1);
            }
        }
    } else {
        println!("mini-lean: inductive, goal, intro, exact, apply, induction, rw, change, rfl, qed, quit");
        println!("Interactive inductive blocks finish with 'end'.");
        let mut block: Option<Vec<String>> = None;
        for line in io::stdin().lock().lines() {
            match line {
                Ok(l) => {
                    let line = l.trim();
                    if let Some(lines) = block.as_mut() {
                        if line == "end" {
                            let result = parse_inductive(&k, lines).and_then(|spec| {
                                let name = spec.name.clone();
                                k.add_inductive(spec)?;
                                println!("inductive {name} registered");
                                Ok(())
                            });
                            if let Err(e) = result {
                                eprintln!("error: {e}");
                            }
                            block = None;
                        } else if line.starts_with('|') || line.is_empty() {
                            if !line.is_empty() {
                                lines.push(line.to_string());
                            }
                        } else {
                            eprintln!(
                                "error: inside inductive block expected constructor or 'end'"
                            );
                        }
                    } else if line.starts_with("inductive ") {
                        block = Some(vec![line.to_string()]);
                        println!("Enter constructors with '|', then 'end'.");
                    } else {
                        match run_line(&mut k, &mut state, line) {
                            Ok(false) => break,
                            Err(e) => eprintln!("error: {e}"),
                            _ => {}
                        }
                    }
                }
                Err(_) => break,
            }
        }
    }
}
