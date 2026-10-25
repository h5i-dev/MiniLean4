# 第2章 Lambda 計算と変数の束縛

## 到達目標

変数の scope、関数適用、α同値、capture-avoiding substitution を理解する。

## 理論

関数適用の型規則は次の通り。

```
Γ ⊢ f : Π(x : A).B     Γ ⊢ a : A
────────────────────────────────── Π-elimination
Γ ⊢ f a : B[x := a]
```

束縛変数の名前は証明の意味を変えない。`λx.x` と `λy.y` は α同値。一方、置換 `x := y` を `λy.x` に適用した結果は `λy.y` ではない。束縛変数を freshen しなければ自由変数 y が捕獲される。

## 実装

`free` は自由変数を収集し、`subst_binder` は置換対象の自由変数が束縛変数と衝突するときに fresh name を生成する。`alpha` は binder environment で bound variable の距離を比較する。

名前付き表現は読みやすい反面、実用的には de Bruijn index / level や locally nameless も有力。Lean の内部表現そのものとは異なる。

## 演習

`λ(x : Nat). λ(y : Nat). x` に `y` を代入するとき、実際に何が変わるか。`subst` の分岐ごとに手で追う。

## テスト

`cargo test substitution_avoids_capture` および `cargo test modus_ponens`。
