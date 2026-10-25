# 第7章 Interactive Proofs: goals と tactics

## 到達目標

`intro`、`exact`、限定的な `apply` の実装によって、証明状態が proof term に変換される機構を理解する。

## 理論

`intro h` はゴール `A → B` を、文脈 `h:A` の下のゴール B に変更する。内部では `λ(h:A). ...` を構築する。`exact t` は `Γ ⊢ t : goal` を要求する。`apply f` は `f : A → B` で現在の goal が B の場合、残った goal A を作る。

## 実装

`ProofState` は `Goal { ctx,target }` と `Frame` のスタックで実装する。`intro` と `apply` は proof constructor の穴を push し、`exact` は reverse fold で proof term を組み立てる。

`apply` は一引数、非依存結論のみ対応。Lean の複数 goal、unification、metavariables、backtracking、tactic macros とは異なる。

```rust
let target = pi("P",Term::Sort(0),arrow(v("P"),v("P")));
let mut s = ProofState::new(target.clone());
s.intro("P")?;
s.intro("h")?;
let proof = s.exact(v("h"))?;
check(&vec![], &proof, &target)?;
```

## 演習

`Nat → Nat` を `intro n; exact n` で証明する。次に `apply (λx:Nat.x)` により一段遠回りして同じ証明をする。

## テスト

`cargo test interactive` と `cargo test apply_tactic`。
