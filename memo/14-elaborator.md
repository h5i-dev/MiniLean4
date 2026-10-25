# 第14章: Bidirectional elaboration の最小実装

## Kernel と elaborator の違い

Kernel は明示的な core term `Γ ⊢ t : T` を検査する。Elaborator はユーザーが書いた surface syntax から、その core term と metavariable constraints を生成する。

Bidirectional typing には二つの判断がある。

\[
\Gamma \vdash e \Rightarrow A \qquad\text{(型を合成する)}
\]
\[
\Gamma \vdash e \Leftarrow A \qquad\text{(期待型と照らして検査する)}.
\]

Lambda の期待型が Pi なら binder 型を伝播できるため、checking mode は elaboration に重要。

## 最小実装

`Elaborator::check_text(Γ,source,expected)` は parser と kernel check を連結する。`_` なら文脈付き meta を生成し、未解決のままでは `result` は失敗する。明示 AST がある場合は kernel が型を検査する。

```rust
use mini_lean::{Nat, Zero};
use mini_lean::advanced::Elaborator;
let mut elab = Elaborator::default();
let hole = elab.check_text(&vec![], "_", &Nat).unwrap();
assert!(elab.result(hole).is_err());
elab.metas.assign(hole, Zero).unwrap();
assert_eq!(elab.result(hole).unwrap(), Zero);
```

## 一般の elaborator へ

上記は **型付き parser と穴の checking frontend** であり、Lean 4 と同等の「完全な elaborator」ではない。完全な elaboration を目指すなら、(1) unresolved metavariable expressions、(2) higher-order pattern unification、(3) postponed constraints、(4) implicit argument insertion、(5) coercion / type class inference、(6) universe constraints を実装する必要がある。

## 演習

最初に term 内部の `f(_)` を `SurfaceTerm::Hole` として扱う。その後、function application から argument type を推論し、hole に expected type を伝播する。最後に constrained metavariables の occurs check と constraint worklist を追加する。
