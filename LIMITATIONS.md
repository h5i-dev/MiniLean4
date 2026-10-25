# 実装範囲と品質・安全上の注意

| 機能 | 状態 |
|---|---|
| 明示的 Pi、lambda、application | Rust 実装あり |
| 名前付き変数の capture-avoiding substitution | Rust 実装あり |
| Sort(u) の階層 | Rust 実装あり（universe polymorphism なし） |
| β / NatRec / EqRec 簡約 | Rust 実装あり |
| 型推論・照合・conversion | Rust 実装あり |
| Nat、induction principle | NatRec として Rust 実装あり |
| 等式と equality transport | Eq / Refl / EqRec として Rust 実装あり |
| intro/exact/apply | Rust 実装あり（apply は非依存の1引数のみ） |
| 複数の goal、metavariables | 未実装 |
| rw/induction tactic の構文と自動化 | 未実装（基礎 eliminator は実装済み） |
| 文字列ソースの parser/elaborator | 未実装（設計解説のみ） |
| 独立した Prop、証明無関係性、商型 | 未実装 |
| 一般の定義展開/再帰定義 | 未実装 |
| Lean 4 の互換性、Lean 4 の kernel を再現 | 対象外 |
| proof checker 自身の soundness proof | 未実施 |
| Rust compile/test | この環境では未実行 |

## 健全性・セキュリティ

normalization には fuel limit があり、極端に大きい AST は stack overflow や資源枯渇を引き起こす可能性がある。教育用コードを不信な入力に直接公開しないこと。実用的な ITP を構築する際は、より厳密な binding representation、termination/canonicity の議論、universe constraints、信頼できる primitive eliminators、プロパティテストや fuzzing、kernel の機械検証が望ましい。

## 次に追加する順序

1. de Bruijn levels と explicit substitution
2. コマンドライン parser と pretty-printer
3. metavariables と occurs/scope check
4. unification と複数 goals
5. `apply` / `rw` / `induction` の実用 tactic
6. universe polymorphism と Prop
7. declaration/definition delta reduction
8. general inductive definitions と termination checks
9. editor protocol と豊富な diagnostics
10. trusted kernel の計算モデルに対する metatheory

## Chapters 11–14 added

`src/advanced.rs` now implements a small expression parser, local-context metavariable assignment, a multi-goal proof skeleton with kernel-checked finalization, first-order closed-endpoint rewriting, Nat induction, and a minimal `Elaborator::check_text` facade. These are **subsets**, not Lean 4 compatible tactics or a general higher-order unifier. In particular, hole propagation inside arbitrary syntax, deferred constraints, implicit arguments, and general dependent `apply` remain unsupported.
