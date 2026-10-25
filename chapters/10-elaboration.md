# 第10章 Elaborator とプログラミング言語設計

## 到達目標

ユーザーが書く便利な構文と、kernel が検査する小さな core term を分ける設計を理解する。

## 理論

Lean の `by intro h; exact h` は、最終的に `λh. h` のような proof term を生成する。elaboration は表面構文の名前解決、暗黙引数の挿入、unification、metavariables の解決、tactic expansion などを担う。kernel に直接暗黙引数や syntax sugar を持ち込む必要はない。

## 実装

現在の Rust API (`pi`, `lam`, `app`, `ProofState`) 自体を **最小の手動 elaboration interface** と位置付ける。`ProofState` が `intro` / `exact` / 制約付き `apply` を AST に展開し、最終的に `check` が承認する。

**本実装の明示的な非対応範囲:** テキスト lexer/parser、暗黙引数 inference、metavariable solver、型クラス、universes polymorphism、複数 goals、`rw` と `induction` の tactic 構文、Lean 言語互換、エディタ連携。第10章はこれらを実装したと偽らず、正確なアルゴリズム設計と拡張計画を学ぶ章である。

## 追加実装課題

1. surface AST と core AST を分ける。
2. `λx => t` に型注釈がない場合に期待型から x の型を得る bidirectional checking。
3. `?m` に型・文脈・解決状態を持たせ、occurs check と scope check を実装する。
4. `apply f` が生成する複数の subgoal を管理する。
5. kernel で定理を再検証する最終チェックを固定する。

## テスト

`cargo test` で core kernel と tactic 変換の既存の回帰テストを全部実行する。
