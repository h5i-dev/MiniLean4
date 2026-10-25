# 第13章: `rw` と `induction` を proof term にコンパイルする

## `rw`: equality elimination

`h : a = b` があり、目標が `C[a]` のとき、`rw h` で目標を `C[b]` に変える。最終的な証明は `EqRec` によって逆向きに輸送される。`EqRec` の型は概略次の通り。

\[
\frac{p:a=b\quad v:C(a)}{\mathrm{EqRec}(C,v,p):C(b)}.
\]

目標の向きを逆にしたいので `EqRec` で `symm(h):b=a` を生成し、サブゴール `C[b]` から `C[a]` を復元する。

この教材では両端が *closed term* の等式に限定する。これは単純な再帰的 subtree replacement で variable capture を避けるため。一般の `rw` には binder-aware rewriting、congruence、equality reasoning が必要。

## `induction`: Nat recursor

`n : Nat ⊢ P(n)` を証明するために:

- base goal: `⊢ P(0)`
- step goal: `k:Nat, ih:P(k) ⊢ P(succ(k))`

の二つを生成する。proof term は `NatRec (fun n => P(n)) base (fun k ih => step) n`。

```rust
use mini_lean::{Nat, eq, pi, v};
use mini_lean::advanced::run_script;
let theorem = pi("n", Nat, eq(Nat,v("n"),v("n")));
let proof = run_script(theorem.clone(),
    "intro n\ninduction n ih\nrfl\nrfl"
).unwrap();
mini_lean::check(&vec![], &proof, &theorem).unwrap();
```

Tactic は正しいことを仮定せず、proof term を組み立てた後に kernel が最初の目標を再検査する。

## 制限と発展課題

`induction` は Nat 型のローカル変数専用。依存変数の generalization、constructor parameter、arbitrary inductive type は未対応。`rw` は式全体を探索する単純な syntactic rewriting で、正規化された subexpression や binder 内の一般的な rewriting は未対応。`rfl` は definitional equality を利用する。

**演習:** `rw <- h` を入れる。`induction` で step 変数の名前を指定できるようにする。等式について `symm` / `trans` を tactic として実装する。
