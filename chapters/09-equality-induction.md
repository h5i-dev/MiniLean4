# 第9章 等式、rfl、rewrite、induction

## 到達目標

命題としての等式と computation による definitional equality を区別し、transport と自然数の帰納法を構成する。

## 理論

`Eq A x y` は「A の x と y が等しい」という**命題型**、`Refl(x) : Eq A x x` は反射律の証明項。

`EqRec M value proof` は、`M : A → Sort u`、`value : M x`、`proof : Eq A x y` から `M y` を作る。これは equality transport であり、rewrite の核心である。

`rfl` は、ゴール `Eq A x y` の両端が conversion で一致するとき `Refl(x)` を置けばよい。教材の `Term::Refl` が対応する。`rw` は適切な `M` を見つけて EqRec を組み立てる作業。

`induction n` の核心は NatRec の `motive` と `step` を用意することである。本教材は **NatRec を直接実装**しており、`induction` / `rw` という構文の自動生成 tactic は実装していない。これらを「完成済み」と呼ばない。

## 実装

`Term::{Eq,Refl,EqRec,NatRec}` と各推論規則を参照する。`EqRec` の `proof` が `Refl` に簡約されれば結果は `value` に計算できる。

## 演習

`Eq Nat Zero Zero` を `Refl(Zero)` で証明せよ。`Eq Nat Zero (Succ Zero)` が証明できないことを確かめよ。等式対称律を EqRec と motive `λz. Eq A z x` で構成することも可能。

## テスト

`cargo test refl_and_transport` と `cargo test reject_fake_equality`。
