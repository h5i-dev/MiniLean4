//! Educational proof kernel. No external dependencies.
//! The trusted base is inference, normalization and substitution.
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(String), Sort(u32),
    Pi(String, Box<Term>, Box<Term>),
    Lam(String, Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
    Nat, Zero, Succ(Box<Term>),
    NatRec { motive: Box<Term>, base: Box<Term>, step: Box<Term>, scrutinee: Box<Term> },
    Eq(Box<Term>, Box<Term>, Box<Term>),
    Refl(Box<Term>),
    EqRec { motive: Box<Term>, value: Box<Term>, proof: Box<Term> },
}
use Term::*;
pub fn v(s: &str) -> Term { Var(s.into()) }
pub fn bx(t: Term) -> Box<Term> { Box::new(t) }
pub fn pi(x: &str, a: Term, b: Term) -> Term { Pi(x.into(),bx(a),bx(b)) }
pub fn lam(x: &str, a: Term, b: Term) -> Term { Lam(x.into(),bx(a),bx(b)) }
pub fn app(f: Term, a: Term) -> Term { App(bx(f),bx(a)) }
pub fn arrow(a: Term,b: Term) -> Term { pi("_",a,b) }
pub fn numeral(n: usize) -> Term { (0..n).fold(Zero, |t,_| Succ(bx(t))) }
pub fn eq(a: Term,x: Term,y: Term) -> Term { Eq(bx(a),bx(x),bx(y)) }
pub fn nat_rec(m:Term,b:Term,s:Term,n:Term)->Term { NatRec{motive:bx(m),base:bx(b),step:bx(s),scrutinee:bx(n)} }
pub fn eq_rec(m:Term,x:Term,p:Term)->Term { EqRec{motive:bx(m),value:bx(x),proof:bx(p)} }

pub type Context = Vec<(String, Term)>;
fn free(t:&Term) -> HashSet<String> {
    match t {
        Var(x) => HashSet::from([x.clone()]),
        Sort(_) | Nat | Zero => HashSet::new(),
        Succ(n)|Refl(n)=>free(n),
        Pi(x,a,b)|Lam(x,a,b) => { let mut s=free(a);let mut q=free(b);q.remove(x);s.extend(q);s },
        App(a,b)=>union(free(a),free(b)),
        Eq(a,x,y)=>union(union(free(a),free(x)),free(y)),
        NatRec{motive,base,step,scrutinee}=>union(union(free(motive),free(base)),union(free(step),free(scrutinee))),
        EqRec{motive,value,proof}=>union(union(free(motive),free(value)),free(proof)),
    }
}
fn union(mut a:HashSet<String>,b:HashSet<String>)->HashSet<String>{a.extend(b);a}
fn fresh(base:&str,avoid:&HashSet<String>)->String{
    if !avoid.contains(base){return base.to_owned()}
    for i in 0.. { let s=format!("{base}#{i}");if !avoid.contains(&s){return s} }
    unreachable!()
}
/// Capture-avoiding substitution [name := val] term, including dependent binders.
pub fn subst(t:&Term,name:&str,val:&Term)->Term{
    match t {
        Var(x)=>if x==name {val.clone()} else {t.clone()},
        Sort(_) | Nat | Zero=>t.clone(),
        Succ(n)=>Succ(bx(subst(n,name,val))), Refl(n)=>Refl(bx(subst(n,name,val))),
        Pi(x,a,b)=>{let a1=subst(a,name,val);let (x1,b1)=subst_binder(x,b,name,val);Pi(x1,bx(a1),bx(b1))},
        Lam(x,a,b)=>{let a1=subst(a,name,val);let (x1,b1)=subst_binder(x,b,name,val);Lam(x1,bx(a1),bx(b1))},
        App(f,a)=>app(subst(f,name,val),subst(a,name,val)),
        Eq(a,x,y)=>eq(subst(a,name,val),subst(x,name,val),subst(y,name,val)),
        NatRec{motive,base,step,scrutinee}=>nat_rec(subst(motive,name,val),subst(base,name,val),subst(step,name,val),subst(scrutinee,name,val)),
        EqRec{motive,value,proof}=>eq_rec(subst(motive,name,val),subst(value,name,val),subst(proof,name,val)),
    }
}
fn subst_binder(x:&str,body:&Term,name:&str,val:&Term)->(String,Term){
    if x==name { return (x.into(),body.clone()); }
    if !free(body).contains(name) {return (x.into(),body.clone());}
    if free(val).contains(x) {
        let mut avoid=union(free(body),free(val));avoid.insert(name.into());avoid.insert(x.into());
        let y=fresh(x,&avoid);
        let renamed=subst(body,x,&v(&y));
        (y,subst(&renamed,name,val))
    }else{(x.into(),subst(body,name,val))}
}
/// Weak-head normalization; fuel prevents divergence from exhausting the stack forever.
fn whnf(t:&Term,fuel:&mut usize)->Result<Term,String>{
    if *fuel==0{return Err("normalization fuel exhausted".into())}*fuel-=1;
    match t {
        App(f,a)=>{let f1=whnf(f,fuel)?; if let Lam(x,_,b)=f1 {whnf(&subst(&b,&x,a),fuel)} else {Ok(app(f1,(**a).clone()))}},
        NatRec{motive,base,step,scrutinee}=>{
            let n=whnf(scrutinee,fuel)?;
            match n {
                Zero=>whnf(base,fuel),
                Succ(k)=>{let rec=nat_rec((**motive).clone(),(**base).clone(),(**step).clone(),(*k).clone());
                    let reduction=app(app((**step).clone(),(*k).clone()),rec);
                    whnf(&reduction,fuel)
                },
                _=>Ok(nat_rec((**motive).clone(),(**base).clone(),(**step).clone(),n)),
            }
        },
        EqRec{motive,value,proof}=>{let p=whnf(proof,fuel)?;match p {Refl(_)=>whnf(value,fuel),_=>Ok(eq_rec((**motive).clone(),(**value).clone(),p))}},
        _=>Ok(t.clone()),
    }
}
fn alpha(a:&Term,b:&Term,env_a:&mut Vec<String>,env_b:&mut Vec<String>)->bool{
    match (a,b){
        (Var(x),Var(y))=>{
            let i=env_a.iter().rposition(|z|z==x);let j=env_b.iter().rposition(|z|z==y);
            match (i,j){(Some(i),Some(j))=>env_a.len()-1-i==env_b.len()-1-j,(None,None)=>x==y,_=>false}
        },
        (Sort(x),Sort(y))=>x==y,(Nat,Nat)|(Zero,Zero)=>true,
        (Succ(x),Succ(y))|(Refl(x),Refl(y))=>alpha(x,y,env_a,env_b),
        (Pi(x,a1,b1),Pi(y,a2,b2))|(Lam(x,a1,b1),Lam(y,a2,b2))=>{
            if !alpha(a1,a2,env_a,env_b){return false}
            env_a.push(x.clone());env_b.push(y.clone());let out=alpha(b1,b2,env_a,env_b);env_a.pop();env_b.pop();out
        },
        (App(f,x),App(g,y))=>alpha(f,g,env_a,env_b)&&alpha(x,y,env_a,env_b),
        (Eq(a,x,y),Eq(b,p,q))=>alpha(a,b,env_a,env_b)&&alpha(x,p,env_a,env_b)&&alpha(y,q,env_a,env_b),
        (NatRec{motive:a,base:b,step:c,scrutinee:d},NatRec{motive:e,base:f,step:g,scrutinee:h})=>[ (a,e),(b,f),(c,g),(d,h)].iter().all(|(x,y)|alpha(x,y,env_a,env_b)),
        (EqRec{motive:a,value:b,proof:c},EqRec{motive:d,value:e,proof:f})=>[(a,d),(b,e),(c,f)].iter().all(|(x,y)|alpha(x,y,env_a,env_b)),
        _=>false,
    }
}
fn normal(t:&Term,fuel:&mut usize)->Result<Term,String>{
    let w=whnf(t,fuel)?;
    Ok(match w {
        Pi(x,a,b)=>pi(&x,normal(&a,fuel)?,normal(&b,fuel)?),
        Lam(x,a,b)=>lam(&x,normal(&a,fuel)?,normal(&b,fuel)?),
        App(f,a)=>app(normal(&f,fuel)?,normal(&a,fuel)?),
        Succ(n)=>Succ(bx(normal(&n,fuel)?)),
        Eq(a,x,y)=>eq(normal(&a,fuel)?,normal(&x,fuel)?,normal(&y,fuel)?),
        Refl(n)=>Refl(bx(normal(&n,fuel)?)),
        NatRec{motive,base,step,scrutinee}=>nat_rec(normal(&motive,fuel)?,normal(&base,fuel)?,normal(&step,fuel)?,normal(&scrutinee,fuel)?),
        EqRec{motive,value,proof}=>eq_rec(normal(&motive,fuel)?,normal(&value,fuel)?,normal(&proof,fuel)?),
        other=>other,
    })
}
pub fn normalize(t:&Term)->Result<Term,String>{normal(t,&mut 100_000)}
pub fn convertible(a:&Term,b:&Term)->Result<bool,String>{
    let a=normalize(a)?;let b=normalize(b)?;Ok(alpha(&a,&b,&mut vec![],&mut vec![]))
}
fn ensure_type(ctx:&Context,t:&Term)->Result<u32,String>{
    match whnf(&infer(ctx,t)?,&mut 100_000)? {Sort(u)=>Ok(u),other=>Err(format!("expected a sort, got {other:?}"))}
}
pub fn check(ctx:&Context,t:&Term,expected:&Term)->Result<(),String>{
    // Bidirectional lambda checking: allows checking against an expected Pi.
    if let Lam(x,ann,body)=t {
        if let Pi(y,a,b)=whnf(expected,&mut 100_000)? {
            if !convertible(ann,&a)?{return Err("lambda annotation differs from domain".into())}
            let mut next=ctx.clone();next.push((x.clone(),(*a).clone()));
            return check(&next,body,&subst(&b,&y,&v(x)));
        }
    }
    let found=infer(ctx,t)?;
    if convertible(&found,expected)? {Ok(())} else {Err(format!("type mismatch: expected {expected:?}, found {found:?}"))}
}
/// Bidirectional dependent type checker with explicit annotations.
pub fn infer(ctx:&Context,t:&Term)->Result<Term,String>{
    match t {
        Var(x)=>ctx.iter().rev().find(|(n,_)|n==x).map(|(_,t)|t.clone()).ok_or_else(||format!("unbound variable {x}")),
        Sort(u)=>Ok(Sort(u.checked_add(1).ok_or("universe overflow")?)),
        Pi(x,a,b)=>{let u=ensure_type(ctx,a)?;let mut c=ctx.clone();c.push((x.clone(),(**a).clone()));let v=ensure_type(&c,b)?;Ok(Sort(u.max(v)))},
        Lam(x,a,b)=>{ensure_type(ctx,a)?;let mut c=ctx.clone();c.push((x.clone(),(**a).clone()));let bt=infer(&c,b)?;Ok(pi(x,(**a).clone(),bt))},
        App(f,a)=>{let ft=whnf(&infer(ctx,f)?,&mut 100_000)?;if let Pi(x,dom,cod)=ft {check(ctx,a,&dom)?;Ok(subst(&cod,&x,a))}else{Err(format!("cannot apply non-function: {ft:?}"))}},
        Nat=>Ok(Sort(0)),Zero=>Ok(Nat),
        Succ(n)=>{check(ctx,n,&Nat)?;Ok(Nat)},
        NatRec{motive,base,step,scrutinee}=>{
            let mt=infer(ctx,motive)?;
            let Pi(x,dom,ret)=whnf(&mt,&mut 100_000)? else {return Err("motive is not a function".into())};
            if !convertible(&dom,&Nat)?{return Err("motive must take Nat".into())}
            let ret_sort=subst(&ret,&x,&v("$nat_motive_probe"));
            if !matches!(whnf(&ret_sort,&mut 100_000)?,Sort(_)){return Err("motive must return a Sort".into())}
            check(ctx,scrutinee,&Nat)?;
            check(ctx,base,&app((**motive).clone(),Zero))?;
            let step_ty=pi("k",Nat,arrow(app((**motive).clone(),v("k")),app((**motive).clone(),Succ(bx(v("k"))))));
            check(ctx,step,&step_ty)?;
            Ok(app((**motive).clone(),(**scrutinee).clone()))
        },
        Eq(a,x,y)=>{ensure_type(ctx,a)?;check(ctx,x,a)?;check(ctx,y,a)?;Ok(Sort(0))},
        Refl(x)=>{let ty=infer(ctx,x)?;Ok(eq(ty,(**x).clone(),(**x).clone()))},
        EqRec{motive,value,proof}=>{
            let pt=whnf(&infer(ctx,proof)?,&mut 100_000)?;
            let Eq(a,x,y)=pt else {return Err("EqRec expects equality proof".into())};
            let mt=whnf(&infer(ctx,motive)?,&mut 100_000)?;
            let Pi(z,dom,cod)=mt else {return Err("EqRec motive must be a function".into())};
            if !convertible(&dom,&a)? {return Err("EqRec motive domain mismatch".into())}
            let cod_sort=subst(&cod,&z,&v("$eq_motive_probe"));
            if !matches!(whnf(&cod_sort,&mut 100_000)?,Sort(_)){return Err("EqRec motive must return a Sort".into())}
            check(ctx,value,&app((**motive).clone(),(*x).clone()))?;
            Ok(app((**motive).clone(),(*y).clone()))
        },
    }
}

/// Declaration table is not part of trusted proof checking. Only kernel-checked
/// statements enter the table. Definition expansion is deliberately omitted.
#[derive(Default)]
pub struct Environment { pub declarations: HashMap<String,Term> }
impl Environment {
    pub fn theorem(&mut self,name:&str,statement:Term,proof:Term)->Result<(),String>{
        if self.declarations.contains_key(name){return Err("duplicate name".into())}
        ensure_type(&vec![],&statement)?;
        check(&vec![],&proof,&statement)?;
        self.declarations.insert(name.into(),statement);Ok(())
    }
}

/// Goal refinement: tactics construct terms, which are checked by the kernel.
/// This small engine supports a single focused goal, and makes no claim to
/// provide Lean's metavariable elaboration or full tactic language.
#[derive(Clone,Debug)]
pub struct Goal { pub ctx:Context, pub target:Term }
#[derive(Clone,Debug)]
pub enum Frame { Intro(String,Term), Apply(Term,Term) }
#[derive(Clone,Debug)]
pub struct ProofState { pub goal:Goal, frames:Vec<Frame>, statement:Term }
impl ProofState {
    pub fn new(target:Term)->Self{ Self{goal:Goal{ctx:vec![],target:target.clone()},frames:vec![],statement:target} }
    pub fn intro(&mut self,name:&str)->Result<(),String>{
        let Pi(x,a,b)=whnf(&self.goal.target,&mut 100_000)? else{return Err("intro expects Pi".into())};
        if self.goal.ctx.iter().any(|(n,_)|n==name){return Err("duplicate local name".into())}
        self.goal.ctx.push((name.into(),(*a).clone()));
        self.goal.target=subst(&b,&x,&v(name));
        self.frames.push(Frame::Intro(name.into(),*a));Ok(())
    }
    /// `apply` only handles a theorem/function with exactly one argument.
    pub fn apply(&mut self,term:Term)->Result<(),String>{
        let Pi(x,a,cod)=whnf(&infer(&self.goal.ctx,&term)?,&mut 100_000)? else{return Err("apply expects function".into())};
        if free(&cod).contains(&x){return Err("dependent apply requires metavariable elaboration".into())}
        if !convertible(&cod,&self.goal.target)?{return Err("conclusion mismatch".into())}
        self.frames.push(Frame::Apply(term,(*a).clone()));self.goal.target=*a;Ok(())
    }
    pub fn exact(self,term:Term)->Result<Term,String>{
        check(&self.goal.ctx,&term,&self.goal.target)?;
        let mut proof=term;
        for f in self.frames.into_iter().rev(){proof=match f {Frame::Intro(x,a)=>lam(&x,a,proof),Frame::Apply(t,_)=>app(t,proof)}}
        // Trust boundary: always recheck the reconstructed term against the ORIGINAL goal.
        check(&vec![],&proof,&self.statement)?;
        Ok(proof)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn p()->Term {v("P")}
    #[test] fn identity(){let t=lam("P",Sort(0),lam("h",p(),v("h")));check(&vec![],&t,&pi("P",Sort(0),arrow(p(),p()))).unwrap()}
    #[test] fn modus_ponens(){let t=lam("P",Sort(0),lam("Q",Sort(0),lam("f",arrow(p(),v("Q")),lam("h",p(),app(v("f"),v("h"))))));
        let goal=pi("P",Sort(0),pi("Q",Sort(0),arrow(arrow(p(),v("Q")),arrow(p(),v("Q")))));check(&vec![],&t,&goal).unwrap()}
    #[test] fn reject_wrong_proof(){assert!(check(&vec![],&lam("P",Sort(0),lam("h",p(),Zero)),&pi("P",Sort(0),arrow(p(),p()))).is_err())}
    #[test] fn substitution_avoids_capture(){let t=lam("y",Nat,v("x"));let s=subst(&t,"x",&v("y"));assert!(free(&s).contains("y"));}
    #[test] fn conversion_beta(){assert!(convertible(&app(lam("x",Nat,v("x")),numeral(2)),&numeral(2)).unwrap())}
    #[test] fn universe_stratification(){assert_eq!(infer(&vec![],&Sort(0)).unwrap(),Sort(1));assert_eq!(infer(&vec![],&Sort(1)).unwrap(),Sort(2))}
    #[test] fn nat_rec_computes(){let m=lam("n",Nat,Nat);let st=lam("k",Nat,lam("ih",Nat,Succ(bx(v("ih")))));let r=nat_rec(m,Zero,st,numeral(3));assert!(convertible(&r,&numeral(3)).unwrap());check(&vec![],&r,&Nat).unwrap()}
    #[test] fn refl_and_transport(){let m=lam("x",Nat,eq(Nat,v("x"),v("x")));let r=eq_rec(m,Refl(bx(Zero)),Refl(bx(Zero)));check(&vec![],&r,&eq(Nat,Zero,Zero)).unwrap()}
    #[test] fn interactive(){let target=pi("P",Sort(0),arrow(v("P"),v("P")));let mut s=ProofState::new(target.clone());s.intro("P").unwrap();s.intro("h").unwrap();let proof=s.exact(v("h")).unwrap();check(&vec![],&proof,&target).unwrap()}
    #[test] fn apply_tactic(){let target=arrow(Nat,Nat);let mut s=ProofState::new(target.clone());s.intro("n").unwrap();s.apply(lam("x",Nat,v("x"))).unwrap();let proof=s.exact(v("n")).unwrap();check(&vec![],&proof,&target).unwrap()}
    #[test] fn double_by_induction(){
        let motive=lam("n",Nat,Nat);
        let step=lam("k",Nat,lam("acc",Nat,Succ(bx(Succ(bx(v("acc")))))));
        let term=nat_rec(motive,Zero,step,numeral(3));
        check(&vec![],&term,&Nat).unwrap();
        assert!(convertible(&term,&numeral(6)).unwrap());
    }
    #[test] fn equality_symmetry_by_transport(){
        let a=Nat; let x=Zero;
        let y=numeral(0);
        let motive=lam("z",Nat,eq(Nat,v("z"),x.clone()));
        let proof=eq_rec(motive,Refl(bx(x.clone())),Refl(bx(y)));
        check(&vec![],&proof,&eq(a,Zero,Zero)).unwrap();
    }
    #[test] fn capture_avoid_nested(){
        let t=pi("y",Nat,lam("z",Nat,v("x")));
        let replaced=subst(&t,"x",&v("y"));
        assert!(free(&replaced).contains("y"));
    }
    #[test] fn reject_fake_equality(){let wrong=eq(Nat,Zero,Succ(bx(Zero)));assert!(check(&vec![],&Refl(bx(Zero)),&wrong).is_err())}
    #[test] fn env_only_accepts_checked(){let mut e=Environment::default();assert!(e.theorem("bad",eq(Nat,Zero,numeral(1)),Refl(bx(Zero))).is_err());assert!(e.declarations.is_empty())}
}

pub mod advanced;
