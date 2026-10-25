# 第4章 Dependent Types と Π型

## 到達目標

結果型が引数の値に依存できる理由を理解し、Pi を型検査する。

## 理論

単純関数型 `A → B` の一般化が `Π(x : A).B(x)`。本実装は cumulative subtyping を持たない階層的 universe `Sort(u)` を使い、`Sort(u) : Sort(u+1)` とする。

```
Γ ⊢ A : Sort(u)     Γ,x:A ⊢ B : Sort(v)
───────────────────────────────────────
Γ ⊢ Π(x:A).B : Sort(max(u,v))
```

Lean 4 では別途 `Prop`、universe polymorphism、impredicativity があり、ここでの規則は正確な Lean kernel のコピーではない。

## 実装

`infer` の `Sort`、`Pi`、`Lam`、`App` と `ensure_type` に対応する。`App` は `B[x:=a]` を返す。`Sort(0)` に `Sort(0)` を型付けする `Type : Type` は不整合を招くため採用しない。

## 演習

`Π(P : Sort 0). P → P` の universe を求めよ。また `Nat : Sort 0` と `Sort 0 : Sort 1` が両立することをチェックせよ。

## テスト

`cargo test universe_stratification`。
