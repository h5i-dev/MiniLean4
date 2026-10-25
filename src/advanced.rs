//! Chapters 11–14: a deliberately small concrete syntax, metavariable store,
//! bidirectional elaboration, and kernel-checked goal refinements.
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok { Id(String), Sym(char), Arrow, FatArrow }
fn lex(input: &str) -> Result<Vec<Tok>, String> {
    let b = input.as_bytes(); let mut i = 0; let mut out = Vec::new();
    while i < b.len() {
        if b[i].is_ascii_whitespace() { i += 1; continue }
        if i+1 < b.len() && b[i] == b'-' && b[i+1] == b'>' {out.push(Tok::Arrow);i+=2;continue}
        if i+1 < b.len() && b[i] == b'=' && b[i+1] == b'>' {out.push(Tok::FatArrow);i+=2;continue}
        if b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] == b'?' || b[i] == b'#' {
            let start=i;i+=1; while i < b.len() && (b[i].is_ascii_alphanumeric() || [b'_',b'?',b'#'].contains(&b[i])) {i+=1}
            out.push(Tok::Id(input[start..i].to_string()));continue
        }
        match b[i] as char { '('|')'|','|':' => out.push(Tok::Sym(b[i] as char)), c=>return Err(format!("unexpected token {c}")) };i+=1;
    }
    Ok(out)
}
struct Parser {t:Vec<Tok>,i:usize}
impl Parser {
    fn eat(&mut self,x:&Tok)->bool {if self.t.get(self.i)==Some(x){self.i+=1;true}else{false}}
    fn expect(&mut self,x:Tok)->Result<(),String>{if self.eat(&x){Ok(())}else{Err(format!("expected {x:?}, at {:?}",self.t.get(self.i)))}}
    fn name(&mut self)->Result<String,String>{match self.t.get(self.i).cloned(){Some(Tok::Id(x))=>{self.i+=1;Ok(x)},_=>Err("expected identifier".into())}}
    fn expr(&mut self)->Result<Term,String>{
        if self.eat(&Tok::Id("fun".into())) {let x=self.name()?;self.expect(Tok::Sym(':'))?;let a=self.expr()?;self.expect(Tok::FatArrow)?;let b=self.expr()?;return Ok(lam(&x,a,b))}
        // The parenthesized dependent product (x : A) -> B
        let saved=self.i;
        if self.eat(&Tok::Sym('(')) {
            if let Ok(x)=self.name() { if self.eat(&Tok::Sym(':')) {
                if let Ok(a)=self.expr() {if self.eat(&Tok::Sym(')')) && self.eat(&Tok::Arrow) {let b=self.expr()?;return Ok(pi(&x,a,b))}}
            }}
        }
        self.i=saved;
        let lhs=self.atom()?;
        if self.eat(&Tok::Arrow) {return Ok(arrow(lhs,self.expr()?))}
        Ok(lhs)
    }
    fn atom(&mut self)->Result<Term,String>{
        if self.eat(&Tok::Sym('(')){let x=self.expr()?;self.expect(Tok::Sym(')'))?;return Ok(self.calls(x)?)}
        let s=self.name()?;
        let t=match s.as_str(){"Nat"=>Nat,"zero"=>Zero,"Sort0"=>Sort(0),"Sort1"=>Sort(1),"Sort2"=>Sort(2),_=>v(&s)};
        self.calls(t)
    }
    fn calls(&mut self,mut t:Term)->Result<Term,String>{
        while self.eat(&Tok::Sym('(')) {
            let mut args=Vec::new();
            if !self.eat(&Tok::Sym(')')) {
                loop{args.push(self.expr()?);if self.eat(&Tok::Sym(')')){break}self.expect(Tok::Sym(','))?;}
            }
            if let Var(x)=t.clone() {
                t=match (x.as_str(),args.as_slice()) {
                    ("succ",[a])=>Succ(bx(a.clone())),
                    ("refl",[a])=>Refl(bx(a.clone())),
                    ("Eq",[a,b,c])=>eq(a.clone(),b.clone(),c.clone()),
                    ("natrec",[a,b,c,d])=>nat_rec(a.clone(),b.clone(),c.clone(),d.clone()),
                    ("eqrec",[a,b,c])=>eq_rec(a.clone(),b.clone(),c.clone()),
                    _=>args.into_iter().fold(t,app),
                }; 
            } else {t=args.into_iter().fold(t,app)}
        }
        Ok(t)
    }
}
/// Small expression parser; syntax includes `fun x : Nat => x`, `(x : Nat) -> Nat`,
/// `Nat -> Nat`, `Eq(Nat,zero,zero)`, `succ(zero)`, and `f(x)`.
pub fn parse(input:&str)->Result<Term,String>{let mut p=Parser{t:lex(input)?,i:0};let t=p.expr()?;if p.i!=p.t.len(){Err(format!("trailing tokens: {:?}",&p.t[p.i..]))}else{Ok(t)}}

/// Metavariables are *not* trusted kernel terms. They carry their own local
/// context, so no solution may refer to a variable outside its scope.
#[derive(Clone,Debug)]
pub struct Meta {pub ctx:Context,pub target:Term,pub value:Option<Term>}
#[derive(Default,Clone,Debug)]
pub struct MetaStore {pub entries:Vec<Meta>}
impl MetaStore {
    pub fn fresh(&mut self,ctx:Context,target:Term)->usize{let id=self.entries.len();self.entries.push(Meta{ctx,target,value:None});id}
    pub fn assign(&mut self,id:usize,t:Term)->Result<(),String>{
        let m=self.entries.get(id).ok_or("unknown metavariable")?;
        if m.value.is_some(){return Err("metavariable already assigned".into())}
        check(&m.ctx,&t,&m.target)?;
        self.entries[id].value=Some(t);Ok(())
    }
    pub fn solve(&self,id:usize)->Result<Term,String>{self.entries.get(id).and_then(|m|m.value.clone()).ok_or("unsolved metavariable".into())}
    pub fn unsolved(&self)->Vec<usize>{self.entries.iter().enumerate().filter(|(_,m)|m.value.is_none()).map(|(i,_)|i).collect()}
}

/// A proof skeleton never enters the kernel until ALL holes are filled.
#[derive(Clone,Debug)]
enum Skeleton {
    Hole(usize), Term(Term), Lam(String,Term,Box<Skeleton>), App(Box<Skeleton>,Box<Skeleton>),
    NatRec(Term,Box<Skeleton>,Box<Skeleton>,Term),
    EqRec(Term,Box<Skeleton>,Term),
}
fn fill(s:&Skeleton,metas:&MetaStore)->Result<Term,String>{Ok(match s {
    Skeleton::Hole(i)=>metas.solve(*i)?,Skeleton::Term(t)=>t.clone(),
    Skeleton::Lam(x,a,b)=>lam(x,a.clone(),fill(b,metas)?),
    Skeleton::App(f,a)=>app(fill(f,metas)?,fill(a,metas)?),
    Skeleton::NatRec(m,b,s,n)=>nat_rec(m.clone(),fill(b,metas)?,fill(s,metas)?,n.clone()),
    Skeleton::EqRec(m,v,p)=>eq_rec(m.clone(),fill(v,metas)?,p.clone()),
})}
fn replace(s:&mut Skeleton,id:usize,new:Skeleton)->bool {
    match s {
        Skeleton::Hole(i) if *i==id=>{*s=new;true},
        Skeleton::Lam(_,_,body)=>replace(body,id,new),
        Skeleton::App(f,a)=>if replace(f,id,new.clone()){true}else{replace(a,id,new)},
        Skeleton::NatRec(_,b,step,_)=>if replace(b,id,new.clone()){true}else{replace(step,id,new)},
        Skeleton::EqRec(_,v,_)=>replace(v,id,new),
        _=>false,
    }
}

/// A multi-goal tactic engine. No skeleton is trusted: `finish` calls kernel `check`.
pub struct AdvancedProof {
    pub metas:MetaStore,
    root:Skeleton,
    target:Term,
    retired:HashSet<usize>,
}
impl AdvancedProof {
    pub fn new(target:Term)->Self{let mut metas=MetaStore::default();let id=metas.fresh(vec![],target.clone());Self{metas,root:Skeleton::Hole(id),target,retired:HashSet::new()}}
    pub fn goals(&self)->Vec<(usize,Goal)>{self.metas.unsolved().into_iter().filter(|i|!self.retired.contains(i)).map(|i|(i,Goal{ctx:self.metas.entries[i].ctx.clone(),target:self.metas.entries[i].target.clone()})).collect()}
    fn focused(&self)->Result<(usize,Meta),String>{let i=self.metas.unsolved().into_iter().find(|i|!self.retired.contains(i)).ok_or("no remaining goals")?;Ok((i,self.metas.entries[i].clone()))}
    pub fn intro(&mut self,name:&str)->Result<(),String>{
        let (id,m)=self.focused()?;
        let Pi(x,a,b)=whnf(&m.target,&mut 100_000)? else{return Err("intro requires Pi".into())};
        if m.ctx.iter().any(|(x,_)|x==name){return Err("duplicate variable".into())}
        let mut c=m.ctx;c.push((name.to_owned(),(*a).clone()));
        let child=self.metas.fresh(c,subst(&b,&x,&v(name)));
        replace(&mut self.root,id,Skeleton::Lam(name.into(),*a,Box::new(Skeleton::Hole(child))));
        self.retired.insert(id);
        Ok(())
    }
    pub fn exact(&mut self,t:Term)->Result<(),String>{let (id,m)=self.focused()?;check(&m.ctx,&t,&m.target)?;
        replace(&mut self.root,id,Skeleton::Term(t.clone()));self.metas.assign(id,t)
    }
    pub fn apply(&mut self,t:Term)->Result<(),String>{
        let (id,m)=self.focused()?;let ty=whnf(&infer(&m.ctx,&t)?,&mut 100_000)?;
        let Pi(x,a,b)=ty else{return Err("apply requires a function".into())};
        if free(&b).contains(&x){return Err("dependent apply is not supported by this strategy".into())}
        if !convertible(&b,&m.target)?{return Err("conclusion does not match goal".into())}
        let sub=self.metas.fresh(m.ctx,*a);
        replace(&mut self.root,id,Skeleton::App(Box::new(Skeleton::Term(t)),Box::new(Skeleton::Hole(sub))));
        self.retired.insert(id);Ok(())
    }
    /// Induction on a Nat local. Requires that the target may depend on that local.
    pub fn induction(&mut self,var:&str,ih:&str)->Result<(),String>{
        let (id,m)=self.focused()?;
        let ty=m.ctx.iter().rev().find(|(x,_)|x==var).ok_or("unknown induction variable")?.1.clone();
        if !convertible(&ty,&Nat)?{return Err("induction variable is not Nat".into())}
        if m.ctx.iter().any(|(x,_)|x==ih || x=="k") {return Err("reserved induction name conflict".into())}
        // Close over the case variable in a motive. Other free locals remain parameters.
        let motive=lam(var,Nat,m.target.clone());
        let base_target=subst(&m.target,var,&Zero);
        let step_target=subst(&m.target,var,&Succ(bx(v("k"))));
        let prev_target=subst(&m.target,var,&v("k"));
        let mut case_ctx=m.ctx.clone();
        // Hide original induction variable to avoid unsound shadowed references in cases.
        case_ctx.retain(|(x,_)|x!=var);
        let base=self.metas.fresh(case_ctx.clone(),base_target);
        case_ctx.push(("k".into(),Nat));case_ctx.push((ih.into(),prev_target.clone()));
        let step=self.metas.fresh(case_ctx,step_target);
        let step_skel=Skeleton::Lam("k".into(),Nat,Box::new(Skeleton::Lam(ih.into(),prev_target,Box::new(Skeleton::Hole(step)))));
        replace(&mut self.root,id,Skeleton::NatRec(motive,Box::new(Skeleton::Hole(base)),Box::new(step_skel),v(var)));
        self.retired.insert(id);Ok(())
    }
    /// Rewrite a *closed* subterm in the goal using `lhs = rhs`.
    /// `rw` changes a goal C[lhs] into C[rhs], rebuilding via equality symmetry.
    pub fn rw(&mut self,proof:Term)->Result<(),String>{
        let (id,m)=self.focused()?;
        let Eq(ty,lhs,rhs)=whnf(&infer(&m.ctx,&proof)?,&mut 100_000)? else {return Err("rw expects equality proof".into())};
        if !free(&lhs).is_empty() || !free(&rhs).is_empty(){return Err("rw requires closed equality endpoints".into())}
        let marker=fresh("$rewrite",&free(&m.target));
        let (body,count)=replace_term(&m.target,&lhs,&v(&marker));
        if count==0 {return Err("rw: lhs not found in target".into())}
        let motive=lam(&marker,(*ty).clone(),body);
        let next_target=app(motive.clone(),(*rhs).clone());
        let sub=self.metas.fresh(m.ctx,next_target);
        // symm : rhs = lhs, constructed solely using EqRec.
        let symm=eq_rec(lam("z",(*ty).clone(),eq((*ty).clone(),v("z"),(*lhs).clone())),Refl(bx((*lhs).clone())),proof);
        replace(&mut self.root,id,Skeleton::EqRec(motive,Box::new(Skeleton::Hole(sub)),symm));
        self.retired.insert(id);Ok(())
    }
    pub fn finish(self)->Result<Term,String>{if self.metas.unsolved().iter().any(|i|!self.retired.contains(i)){return Err("unsolved goals".into())}
        let proof=fill(&self.root,&self.metas)?;check(&vec![],&proof,&self.target)?;Ok(proof)}
}
fn replace_term(t:&Term,find:&Term,with:&Term)->(Term,usize){
    if alpha(t,find,&mut vec![],&mut vec![]){return (with.clone(),1)}
    match t {
        App(f,a)=>{let (x,n)=replace_term(f,find,with);let (y,m)=replace_term(a,find,with);(app(x,y),n+m)},
        Succ(x)=>{let (y,n)=replace_term(x,find,with);(Succ(bx(y)),n)},
        Eq(a,x,y)=>{let (a1,n)=replace_term(a,find,with);let (x1,m)=replace_term(x,find,with);let (y1,k)=replace_term(y,find,with);(eq(a1,x1,y1),n+m+k)},
        Pi(x,a,b)=>{let (a1,n)=replace_term(a,find,with);let (b1,m)=replace_term(b,find,with);(pi(x,a1,b1),n+m)},
        _=>(t.clone(),0),
    }
}

/// Very small bidirectional elaborator. `_` is a contextual metavariable;
/// checking an underscore creates a goal, which must be solved before export.
pub struct Elaborator {pub metas:MetaStore}
impl Default for Elaborator{fn default()->Self{Self{metas:MetaStore::default()}}}
impl Elaborator {
    pub fn check_text(&mut self,ctx:&Context,source:&str,expected:&Term)->Result<usize,String>{
        let term=parse(source)?;
        if term==v("_"){return Ok(self.metas.fresh(ctx.clone(),expected.clone()))}
        check(ctx,&term,expected)?;
        let id=self.metas.fresh(ctx.clone(),expected.clone());self.metas.assign(id,term)?;Ok(id)
    }
    pub fn result(&self,id:usize)->Result<Term,String>{self.metas.solve(id)}
}

/// A line-oriented tactic script frontend. Expressions use the parser above.
pub fn run_script(goal:Term,script:&str)->Result<Term,String>{
    let mut state=AdvancedProof::new(goal);
    for raw in script.lines(){let line=raw.trim();if line.is_empty()||line.starts_with("--"){continue}
        let (command,arg)=line.split_once(' ').unwrap_or((line,""));
        match command {
            "intro"=>state.intro(arg.trim())?,
            "exact"=>state.exact(parse(arg.trim())?)?,
            "apply"=>state.apply(parse(arg.trim())?)?,
            "rw"=>state.rw(parse(arg.trim())?)?,
            "induction"=>{let (x,ih)=arg.trim().split_once(' ').ok_or("induction syntax: induction n ih")?;state.induction(x,ih)?},
            "rfl"=>{let (_,m)=state.focused()?;let Eq(_,x,y)=m.target else{return Err("rfl expects equality goal".into())};
                if !convertible(&x,&y)?{return Err("rfl: unequal sides".into())};state.exact(Refl(x))?},
            _=>return Err(format!("unknown tactic {command}")),
        }
    }
    state.finish()
}

#[cfg(test)] mod tests {
    use super::*;
    #[test] fn syntax(){assert_eq!(parse("fun x : Nat => x").unwrap(),lam("x",Nat,v("x")));assert_eq!(parse("Nat -> Nat").unwrap(),arrow(Nat,Nat));assert_eq!(parse("(x : Nat) -> Eq(Nat,x,x)").unwrap(),pi("x",Nat,eq(Nat,v("x"),v("x"))));}
    #[test] fn script_identity(){let g=arrow(Nat,Nat);let p=run_script(g.clone(),"intro n\nexact n").unwrap();check(&vec![],&p,&g).unwrap()}
    #[test] fn meta_scope(){let mut s=MetaStore::default();let id=s.fresh(vec![],Nat);assert!(s.assign(id,v("x")).is_err());s.assign(id,Zero).unwrap();assert_eq!(s.solve(id).unwrap(),Zero)}
    #[test] fn elaboration_hole(){let mut e=Elaborator::default();let id=e.check_text(&vec![],"_",&Nat).unwrap();assert!(e.result(id).is_err());e.metas.assign(id,Zero).unwrap();assert_eq!(e.result(id).unwrap(),Zero)}
    #[test] fn induction_natural(){let g=pi("n",Nat,eq(Nat,v("n"),v("n")));let p=run_script(g.clone(),"intro n\ninduction n ih\nrfl\nrfl").unwrap();check(&vec![],&p,&g).unwrap()}
    #[test] fn rewrite_natural(){let goal=arrow(eq(Nat,Zero,Succ(bx(Zero))),eq(Nat,Zero,Zero));let mut p=AdvancedProof::new(goal.clone());p.intro("h").unwrap();
        // This rewrite creates a goal with unequal endpoints, and must not produce an invalid theorem.
        assert!(p.rw(v("h")).is_ok());assert!(p.finish().is_err());}
    #[test] fn reject_unfinished(){assert!(AdvancedProof::new(Nat).finish().is_err())}
}
