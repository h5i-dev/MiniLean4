# 第11章: Lexer と recursive descent parser

## 到達目標

文字列 `fun x : Nat => x` を kernel の `Term::Lam` に変換する。重要なのは、**構文解析は定理の真偽を決めない**こと。parser が生成した項も kernel の型検査を通る。

## 形式文法（実装済みの部分集合）

```text
expr   := "fun" IDENT ":" expr "=>" expr
        | "(" IDENT ":" expr ")" "->" expr
        | atom "->" expr
        | atom
atom   := IDENT call* | "(" expr ")" call*
call   := "(" [expr ("," expr)*] ")"
```

`Nat`, `zero`, `Sort0`, `Sort1`, `Sort2` は特別扱いする。`succ(t)`, `refl(t)`, `Eq(A,x,y)`, `natrec(m,b,s,n)` および `eqrec(m,v,p)` を core AST に落とす。`f(x)` は関数適用。`A -> B` は `Pi("_", A, B)` の略記で右結合。`(x : A) -> B` は依存関数型。

## 実装

`src/advanced.rs` の `lex`、`Parser::expr`、`Parser::atom`、`parse` を読む。トークンはキーワードを含めて単純な列挙型で表現する。重要なのは (1) 関数型の右結合、(2) `(` による dependent binder とグルーピングの曖昧性を backtracking で解くこと、(3) parse 後に入力をすべて消費したか確認すること。

```rust
use mini_lean::{Nat, lam, v};
use mini_lean::advanced::parse;
assert_eq!(parse("fun x : Nat => x").unwrap(), lam("x", Nat, v("x")));
```

## 演習

(1) ソース位置を lexer の token に保持して parse error に行番号を追加する。(2) `--` で始まるコメントを式中でもスキップする。(3) infix equality と precedence climbing を実装する。

## 制限

この parser は Lean 4 syntax parser ではない。マクロ、layout、`by` ブロック、名前空間、暗黙引数はサポートしない。`fun` の型注釈は省略できない。
