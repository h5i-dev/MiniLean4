# 第5章 Definitional Equality と型検査

## 到達目標

「型が構文的に同じ」と「計算により同じ」の違いを理解する。

## 理論

型 `B[x:=a]` と期待型 C が β簡約などで同一なら、明示的な等式証明を要求せずに型検査を通せる。これが conversion rule。

```
Γ ⊢ t : A     A ≡ B     Γ ⊢ B : Sort(u)
──────────────────────────────────────
Γ ⊢ t : B
```

本実装の `check` は `infer` 後に `convertible` を呼び出す。`convertible` の失敗・成功が trusted base の一部を形成する。

## 実装

`normalize` は capture-avoiding substitution と alpha equality を利用する。fuel 切れは `Err` として扱い、証明の成功扱いにしない。ユーザー提供の任意の「同じ型」を無条件に認めることは決してしない。

## 演習

正しい：`(λx : Nat. Nat) Zero` と `Nat`。不正：`Nat` と `Sort 0`。両者を `convertible` で調べる。

## テスト

`cargo test conversion_beta`。
