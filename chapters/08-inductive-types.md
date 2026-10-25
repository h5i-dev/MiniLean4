# 第8章 Inductive Types と再帰子

## 到達目標

Nat を `zero` と `succ` から構築し、帰納法原理がなぜ計算と証明の双方に使えるかを理解する。

## 理論

Nat は `Zero : Nat` と `Succ : Nat → Nat` を持つ。dependent eliminator の型（概念的な表記）は以下。

```
NatRec : (M : Nat → Sort u)
       → M Zero
       → (∀ n : Nat, M n → M (Succ n))
       → (n : Nat) → M n
```

`M` に命題族を渡せば数学的帰納法、定数の `Nat` を渡せば自然数の再帰計算となる。

## 実装

`Term::{Nat,Zero,Succ,NatRec}`、`infer` の `NatRec` の枝、`whnf` の recursor 計算規則を見る。例は `NatRec (λ_ . Nat) Zero (λk ih . Succ ih) 3` が 3 に簡約するというもの。

## 演習

`double(n)` を NatRec で `step = λk ih. Succ(Succ ih)` として実装し、`double 3 = 6` を definitional equality で確認せよ。

## テスト

`cargo test nat_rec_computes`。
