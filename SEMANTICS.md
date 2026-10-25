# コア言語の形式意味論

## 1. Syntax

```text
t ::= x | Sort u | Π(x:t).t | λ(x:t).t | t t
    | Nat | Zero | Succ t | NatRec M z s n
    | Eq A x y | Refl x | EqRec M v p
```

Γ は型付き束縛変数の有限列。すべての変数と binder は明示的に名前を持つ。shadowing 自体は構文上可能だが tactic は重複する local name を拒否する。

## 2. 主な推論規則

### Sort

`Γ ⊢ Sort u : Sort (u+1)`。同一宇宙への自己型付けは禁止する。

### Π formation

`Γ ⊢ A : Sort u` と `Γ,x:A ⊢ B : Sort v` なら `Γ ⊢ Π(x:A).B : Sort max(u,v)`。

### Lambda

`Γ ⊢ A : Sort u` と `Γ,x:A ⊢ t : B` なら `Γ ⊢ λ(x:A).t : Π(x:A).B`。

### Application

`Γ ⊢ f : Π(x:A).B` かつ `Γ ⊢ a : A` なら `Γ ⊢ f a : B[x:=a]`。

### Conversion

`Γ ⊢ t : A`、`A ≡ B` のとき `Γ ⊢ t : B`。この実装の `≡` は β、NatRec の iota、EqRec の refl 簡約後の α同値。

### Naturals

`Γ ⊢ Nat : Sort 0`、`Γ ⊢ Zero : Nat`、`Γ ⊢ n : Nat` なら `Γ ⊢ Succ n : Nat`。

### NatRec

`Γ ⊢ M : Π(n:Nat).Sort u`、`Γ ⊢ z : M Zero`、`Γ ⊢ s : Π(n:Nat).M n → M(Succ n)`、`Γ ⊢ n : Nat` なら `Γ ⊢ NatRec M z s n : M n`。

### Equality

`Γ ⊢ A : Sort u`、`Γ ⊢ x:A`、`Γ ⊢ y:A` のとき `Γ ⊢ Eq A x y : Sort 0`。`Γ ⊢ x:A` なら `Γ ⊢ Refl x : Eq A x x`。

### EqRec

`Γ ⊢ p : Eq A x y`、`Γ ⊢ M : Π(z:A).Sort u`、`Γ ⊢ v:M x` なら `Γ ⊢ EqRec M v p : M y`。

## 3. β, ι reductions

```text
(λx.t) a                   ↦ t[x:=a]
NatRec M z s Zero          ↦ z
NatRec M z s (Succ n)      ↦ s n (NatRec M z s n)
EqRec M v (Refl x)         ↦ v
```

型変換に使う equality は **propositional equality ではない**。`Eq A x y` の証明が存在するからといって x と y が judgmentally convertible になるわけではない。

## 4. Invariants と危険箇所

- `subst` は自由変数の捕獲を回避しなくてはならない。
- `infer` / `check` は文脈にない変数を拒否する。
- kernel が型エラーを「曖昧だが成功」と扱うことは許されない。
- `normalize` が fuel exhaustion したら変換チェックも失敗。
- `ProofState` が構築した term は元の statement に対して独立に型検査される。

## 5. Lean 4 との違い

Lean 4 の dependent type theory は proof irrelevance、impredicative Prop、universe levels などを含むさらに複雑なものである。この kernel は全く別の小規模な educational calculus である。ここでの証明は本教材の公理系についてのものに限られる。
