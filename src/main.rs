use mini_lean::*;
fn main() -> Result<(),String> {
    let statement = pi("P",Term::Sort(0),arrow(v("P"),v("P")));
    let mut proof = ProofState::new(statement.clone());
    println!("Initial goal: {:?}",proof.goal.target);
    proof.intro("P")?;
    proof.intro("h")?;
    println!("After intro: {:?} |- {:?}",proof.goal.ctx,proof.goal.target);
    let term=proof.exact(v("h"))?;
    check(&vec![],&term,&statement)?;
    println!("Proof checked: {term:?}");
    let motive=lam("_",Term::Nat,Term::Nat);
    let step=lam("k",Term::Nat,lam("ih",Term::Nat,Term::Succ(bx(v("ih")))));
    let recursion=nat_rec(motive,Term::Zero,step,numeral(4));
    check(&vec![],&recursion,&Term::Nat)?;
    println!("Nat induction computation: {:?}",normalize(&recursion)?);
    Ok(())
}
