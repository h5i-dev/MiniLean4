# Rust で作る小さな Lean 4: Proof Kernel から Tactics まで

**実装しながら学ぶ Interactive Theorem Prover (日本語・全10章)**

Rust 標準ライブラリのみで、簡単な dependent type theory の kernel と対話的な proof state を構築する教材です。`Sort` の宇宙階層、`Pi` / lambda / application、capture-avoiding substitution、β正規化、definitional equality、Nat の recursor、等式の transport、`intro` / `exact` / 限定版 `apply` を実装します。

## すぐ試す

```bash
cargo test
cargo run
```

## 目次

1. [Curry–Howard と証明項](chapters/01-curry-howard.md)
2. [Lambda calculus と束縛](chapters/02-lambda-calculus.md)
3. [β簡約と operational semantics](chapters/03-reduction.md)
4. [Dependent types と universes](chapters/04-dependent-types.md)
5. [Definitional equality と conversion](chapters/05-conversion.md)
6. [Trusted kernel の境界](chapters/06-trusted-kernel.md)
7. [Goal、intro、exact、apply](chapters/07-tactics.md)
8. [Nat inductive type と recursor](chapters/08-inductive-types.md)
9. [Equality、rfl、transport、induction](chapters/09-equality-induction.md)
10. [Elaborator の設計と未実装機能](chapters/10-elaboration.md)

補足: [言語の意味論と形式的ルール](SEMANTICS.md) / [設計上の制限と今後の課題](LIMITATIONS.md)

## ソースの読み方

- `src/lib.rs`: kernel、証明状態、テスト (同じ実装をすべての章で参照)
- `src/main.rs`: 対話的証明と NatRec の実行デモ

**信頼境界:** tactics は証明項の組み立てしか行わず、`ProofState::exact` は最初の goal に対して必ず空文脈の `check` を実行します。`Environment::theorem` も証明を再チェックします。

## 重要な非対応範囲

これは Lean 4 互換実装ではありません。独立した `Prop`、proof irrelevance、定義展開、完全な inductive declarations、universe polymorphism、metavariable unification、lexer/parser、エディタプロトコル、`rw` や `induction` **tactic commands** はありません。第9章はそれらの基礎となる core eliminators を実装して説明し、第10章は設計を扱います。詳しくは `LIMITATIONS.md`。

## 検証状況

この実行環境には Rust コンパイラ / Cargo がなく、`cargo test` は未実行です。プロジェクトをコンパイルできる環境で必ずテストしてください。安全性と soundness について形式的保証はありません。

## 追加章: フロントエンド、穴、rewrite と induction

11. [Lexer / Parser](chapters/11-parser.md)
12. [Metavariables / Goal Refinement](chapters/12-metavariables.md)
13. [`rw` / `induction` tactics](chapters/13-rewrite-induction.md)
14. [Bidirectional elaboration の最小実装](chapters/14-elaborator.md)

`src/advanced.rs` にこれらの実装を追加。`run_script` は改行区切りの `intro`, `exact`, `apply`, `rfl`, `rw`, `induction` を受け取り、kernel-checked proof term を返します。

**注意:** 第10章の未実装範囲の一部が埋まりましたが、完全な higher-order metavariable solver、Lean 4 syntax や general-purpose elaborator は未実装です。第12・14章で未対応範囲と拡張方法を明記しています。コンパイル・テストの未実施にも注意してください。
