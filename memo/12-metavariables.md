# 第12章: Metavariables と goal refinement

## なぜ metavariable が要るか

`intro n` の後に残る `⊢ P n` には、まだ証明項がない。穴 `?m` を持った partial proof term と、それに対応する型付き goal `(Γ ⊢ ?m : P n)` を保持する。

形式的には meta-context を `Σ = {?m : (Γ_m ⊢ T_m)}` として表す。解 `?m := t` を登録する条件は `Γ_m ⊢ t : T_m`。任意の global variable を参照させてはならない。

## 実装

`MetaStore` の各 entry は `ctx`, `target`, `value` を保持する。`assign` は **必ず kernel `check` を呼ぶ**。`AdvancedProof` は `Skeleton` を保持し、`intro` では `Lam` の本体を新しい穴に、`apply` では引数を新しい穴にする。`finish` がすべてを埋めて最初の命題に対して `check([], proof, original_goal)` を行う。

```rust
use mini_lean::{Nat, Zero};
use mini_lean::advanced::MetaStore;
let mut metas = MetaStore::default();
let m = metas.fresh(vec![], Nat);
assert!(metas.solve(m).is_err());
metas.assign(m, Zero).unwrap();
```

## 理論との対応

Elaboration の一般形は higher-order unification だが、ここでは `?m := t` という**明示代入による制約解決**に限定している。Lean 4 の higher-order pattern unification、occurs-check 付き項統一、deferred constraints、dependent `apply` はまだ実装していない。proof skeleton 内部の穴は kernel `Term` ではなく、これにより未解決の穴を kernel に渡さない。

## 演習

`?m` を別の `?n` を含む項へ代入できるようにし、occurs check と依存関係グラフを追加する。複数の goal の順序を操作する `focus`、`all_goals` を実装する。
