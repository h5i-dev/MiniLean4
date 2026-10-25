# 第1章 Curry–Howard 対応: なぜ型検査で証明できるのか

## 到達目標

論理式を型に、証明をプログラムに対応させる。`P → P` の証明を実際の項として構築し、Rust kernel に渡す。

## 理論

判断 `Γ ⊢ t : A` は、文脈 Γ のもとで項 t の型が A であることを意味する。関数型は含意に対応する。

```
Γ, x : A ⊢ t : B
────────────────────── Π-introduction
Γ ⊢ λ(x : A).t : Π(x : A).B
```

B が x に依存しなければ `Π(x : A).B` を `A → B` と表記する。`λ(h : P).h` は `P → P` の証明。

## 実装

`src/lib.rs` の `Term::{Var,Pi,Lam,App}`、`infer` の `Lam` と `Var` 分岐を読む。`Pi` は型を表し、`Lam` は証明の値を表す。

```rust
let goal = pi("P", Term::Sort(0), arrow(v("P"), v("P")));
let proof = lam("P", Term::Sort(0), lam("h", v("P"), v("h")));
check(&vec![], &proof, &goal)?;
```

`P` は命題変数として `Sort(0)` に住む。これは Lean の `Prop` とは同一でない（本実装は命題消去の制約と proof irrelevance を実装しない）。

## 考える

`λ(h : P).h` 以外の `P → P` の inhabitant を、追加の公理なしに作れるだろうか。なぜ `P` 自体の inhabitant を文脈なしでは構築できないのだろうか。

## 演習

`P → Q → P` を証明せよ。解答例は `lam("P",Sort(0),lam("Q",Sort(0),lam("p",v("P"),lam("q",v("Q"),v("p")))))`。

## テスト

`cargo test identity` と `cargo test reject_wrong_proof`。
