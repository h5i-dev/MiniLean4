# 第3章 Operational Semantics: β簡約と正規化

## 到達目標

計算と証明の接点を理解し、項が同じ計算結果を持つか判定する。

## 理論

β簡約は `(λx.t) a ↦ t[x := a]`。このほか Nat の recursor は以下の計算規則を持つ。

```
NatRec M z s Zero        ↦ z
NatRec M z s (Succ n)    ↦ s n (NatRec M z s n)
```

等式の eliminator は refl に対して簡約する。本教材では δ簡約（定義展開）、η同値、商型や再帰定義の評価を省略する。

## 実装

`whnf` は外側が計算可能なところまで簡約する（weak-head normal form）。`normal` は内部まで巡回し、`convertible` が `normalize + alpha` で definitional equality の教育用近似を実装する。fuel は無限計算や病的入力を抑えるための防御であり、完備な変換判定器とは限らない。

## 演習

`(λx : Nat. x) (Succ Zero)` が `Succ Zero` と convertible なことをテストで示す。なぜ Rust の `==` による AST 比較では不十分なのか説明せよ。

## テスト

`cargo test conversion_beta` と `cargo test nat_rec_computes`。
