<div class="lead" markdown="1">

本書のカーネルは、わずか 5 種類の項から出発します。これだけで、命題についての量化を含む命題論理を表現できます。型検査器を書く前に、まず文法と記法を決め、対応する Rust の `Term` 型を用意しましょう。

</div>

## 5 種類の項

核となる言語は小さな依存型理論で、項は次の文法で生成されます。

$$
t, A, B \;::=\; \Sort{u} \;\mid\; x \;\mid\; \tPi{x}{A}{B} \;\mid\; \tLam{x}{A}{t} \;\mid\; t\;s
$$

ここで $u$ は自然数、$x$ は変数名です。それぞれの形の役割は次のとおりです。

- $\Sort{u}$ は**宇宙**（universe）、つまり要素そのものが型であるような型で、数 $u$ はその*レベル*を表します。$\Sort{0}$ は命題の宇宙です。宇宙が一つではなく階層全体になっている理由は[第 13 章](13-universes.md)で説明します。
- $x$ は**変数**です。何を指すかは現れる場所で決まり、外側を囲む $\lambda$ や $\Pi$ の束縛子か、型付け文脈の仮定のどちらかを指します。
- $\tPi{x}{A}{B}$ は **$\Pi$ 型**、[第 1 章](01-propositions-as-types.md)の依存関数型です。$x : A$ を受け取って型 $B$ の値を返す関数の型で、$B$ の中に $x$ が現れてもかまいません。
- $\tLam{x}{A}{t}$ は **$\lambda$ 抽象**で、型 $A$ の引数 $x$ を受け取って $t$ を返す関数です。
- $t\;s$ は $t$ の $s$ への**適用**です。

この文法は型と項を区別しません。命題 $\tPi{P}{\Sort{0}}{P \to P}$ もその証明 $\tLam{P}{\Sort{0}}{\tLam{p}{P}{p}}$ も、同じ 5 つの構成子から組み立てた項です。

$$
\underbrace{\tLam{P}{\Sort{0}}{\tLam{p}{P}{p}}}_{\text{proof}}
\quad : \quad
\underbrace{\tPi{P}{\Sort{0}}{P \to P}}_{\text{proposition, the type of the proof}}.
$$

この二つの項を木として描くと、同じ文法を共有していることがよく分かります。どの節点も 5 つの構成子のどれかで、$\Pi$ や $\lambda$ の節点に付いた名前は、その節点が束縛する変数です。節点をクリックすると対応する部分項が表示され、別の項を入力して試すこともできます。

<div class="explorer" data-kind="ast" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

ある項が妥当な*型*かどうかは構文だけでは決まらず、型検査器が判定します。項が型であるのは、その項自身の型が宇宙であるとき、かつそのときに限ります（[第 5 章](05-algorithm.md)）。

<aside class="note" markdown="1">

第 II 部ではもう一つの形、**定数** $c$ を加えます。定数は、$\mathsf{Nat}$ や $\mathsf{Nat.succ}$ のようにカーネルのシグネチャで宣言されたものを指す名前です。型を大域的な表から引いてくる自由変数のように振る舞い、束縛されることはありません。第 I 部の内容は定数なしで成り立つので、導入は必要になる[第 7 章](07-inductive-nat.md)まで待ちますが、下の Rust の型にはすでに含めてあります。

</aside>

## 記法の約束

本書では次の文字を一貫して使います。

| 文字 | 意味 |
|---|---|
| $s, t, a, b, f$ および $A, B, C, T$（プライムや添字が付くこともある） | 項 |
| $x, y, z$ および $\Pi$ や $\lambda$ で束縛される任意の名前 | 変数名 |
| $u, v, w$ | 宇宙レベル |
| $\Gamma$ | 型付け文脈（[第 3 章](03-typing-rules.md)） |
| $\Sigma$ | 定数のシグネチャ（[第 7 章](07-inductive-nat.md)） |

項を読みやすくするために、三つの略記を使います。

**`->`。** $B$ に $x$ が現れないとき、$\tPi{x}{A}{B}$ を $A \to B$ と書きます。つまり、ふつうの関数型は依存関数型の特殊な場合であり、同じように含意は全称量化の特殊な場合です。実装では、`->` の束縛子に予約名 `_` を使います。

**結合性。** 適用は左に、`->` は右に結合します。

$$
f\;a\;b \;=\; (f\;a)\;b,
\qquad
A \to B \to C \;=\; A \to (B \to C).
$$

**カリー化。** 二引数の関数とは、一つ目の引数を受け取って、二つ目を待つ関数を返す関数です。たとえば $\tLam{a}{A}{\tLam{b}{B}{a}}$ は型 $A \to B \to A$ を持ち、これを $x : A$ と $y : B$ に適用した式は、次のように読みます。

$$
(\tLam{a}{A}{\tLam{b}{B}{a}})\;x\;y \;=\; ((\tLam{a}{A}{\tLam{b}{B}{a}})\;x)\;y.
$$

二つの結合性の約束は、うまく噛み合うように選んであります。型 $A \to B \to C$ のカリー化された関数を $f\;a\;b$ のように適用するとき、型の側にも項の側にも括弧は要りません。

<aside class="intuition" markdown="1">

カリー化のおかげで、言語全体が一引数関数だけで済みます。$A \to B \to C$ の証明は、$A$ の証明を与えられると $B \to C$ の証明を返す関数であり、その証明もまた関数です。「$A$ と $B$ を仮定する」は入れ子になった二つの仮定になり、証明項に現れる二つの $\lambda$ がちょうどそれに対応しています。

</aside>

## 束縛とスコープ

$\tLam{x}{A}{t}$ と $\tPi{x}{A}{B}$ では、変数 $x$ は*束縛*されています。その*スコープ*は本体 $t$ または $B$ で、注釈 $A$ はスコープに含まれません。$\tLam{x}{x}{x}$ では、注釈の中の $x$ は項の外にある何かを指し、本体の $x$ は引数を指します。変数の出現のうち、それを束縛する束縛子のスコープに入っていないものを*自由*な出現といいます。たとえば $\tLam{x}{P}{f\;x\;y}$ では、変数 $P$、$f$、$y$ が自由で、$x$ が束縛されています。

束縛変数については、本書全体を通じて重要になる事実が二つあります。どちらも[第 11 章](11-substitution-alpha.md)で形式化します。

1. 束縛変数の名前には意味がなく、$\tLam{x}{A}{x}$ と $\tLam{y}{A}{y}$ は同じ関数です。束縛変数の名前だけが異なる項を *α 同値*（alpha-equivalent）と呼び、カーネルはそれらを等しいものとして扱わなければなりません。
2. 変数を項で置き換える操作は型付け規則にも計算にも必要だが、その際に自由変数をうっかり同じ名前の束縛子の下に持ち込んではいけません。これを正しく行うことを*捕獲回避代入*（capture-avoiding substitution）と呼びます。

どちらも述べるだけなら簡単ですが、実際の証明検査器で本物のバグを何度も引き起こしてきました。一章を割いて扱うのはそのためです。

## コードでは

<aside class="code" markdown="1">

項は `src/term.rs` にある Rust の列挙型 `Term` で表します。項の種類ごとにバリアントが一つずつあり、第 II 部の定数の分も加えてあります。

```rust
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Sort(u64),                          // Sort u
    Var(String),                        // x        (local, bound or in the context)
    Const(String),                      // c        (global, from the signature)
    Pi(String, Box<Term>, Box<Term>),   // Pi (x : A). B
    Lam(String, Box<Term>, Box<Term>),  // fun (x : A). b
    App(Box<Term>, Box<Term>),          // f a
}
```

変数は名前の文字列で表し、束縛子は自分が束縛する名前を持ちます。もっとも素直で読みやすい表現ですが、そのぶん[第 11 章](11-substitution-alpha.md)で扱う名前の問題からは逃れられません。本書のねらいはその問題を実際に目にして解くことにあるので、これはあえて選んだ表現です。

</aside>

同じファイルには、`Box::new` を入れ子にせずに項を書けるよう、小さな構成関数も用意してあります。`var("x")`、`const_term("Nat")`、`app(f, a)`、`pi("x", a, b)`、`lam("x", a, b)`、そして `pi("_", a, b)` を作る `arrow(a, b)` です。さらに次の三つの補助関数は、本章の約束をそのままコードにしたものです。

```rust
/// f a_1 ... a_n   (left-associated application)
pub fn apps(f: Term, args: impl IntoIterator<Item = Term>) -> Term {
    args.into_iter().fold(f, app)
}

/// Pi (x_1 : A_1) ... Pi (x_k : A_k). tail   (a telescope of binders)
pub fn telescope(binders: &[(String, Term)], tail: Term) -> Term {
    binders.iter().rev().fold(tail, |body, (name, ty)| pi(name, ty.clone(), body))
}

/// Decomposes t into its spine: a head that is not an application, and its arguments.
/// f a b  becomes  (f, [a, b]);  a non-application becomes  (t, []).
pub fn spine(t: &Term) -> (Term, Vec<Term>) {
    match t {
        Term::App(f, a) => {
            let (head, mut args) = spine(f);
            args.push((**a).clone());
            (head, args)
        }
        _ => (t.clone(), vec![]),
    }
}
```

`apps` と `spine` は互いに逆であり、`apps(h, args)` が左に入れ子になった適用 $h\;a_1 \cdots a_n$ を組み立て、`spine` がそれを再びばらします。[第 12 章](12-reduction-conversion.md)の簡約エンジンは項をこの背骨（spine）の形で見るので、今のうちに慣れておいてください。入れ子の項 $((f\;a)\;b)\;c$ の頭部は $f$、引数は $[a, b, c]$ です。各適用の関数側をたどって下りていくと頭部に着き、途中で集めた引数を内側から外側へ読めば正しい順序になります。

本書を通じて使う `.leanmini` スクリプトの表層構文では、同じ項を `Sort 0`、`forall (x : A), B`、`A -> B`、`fun (x : A) => b` と書き、適用は項を並べて表します。完全な文法は[付録 E](e-leanmini-reference.md)にまとめてあります。

## 演習

<div class="exercise" markdown="1">

命題「すべての命題 $P$ と $Q$ について、$P$ ならば $Q$ ならば $P$」を項として書き、その証明項を与えてください。

<details markdown="1">
<summary>解答</summary>

この命題は $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q \to P}}$ で、展開すると
$\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{\tPi{\_}{P}{\tPi{\_}{Q}{P}}}}$ になります。
証明の一つは $\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{\tLam{q}{Q}{p}}}}$ です。leanmini の構文では次のようになります。

```leanmini
goal forall (P : Sort 0), forall (Q : Sort 0), P -> Q -> P
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (p : P) => fun (q : Q) => p
qed
```

</details>

</div>

<div class="exercise" markdown="1">

$f\;a\;(g\;b)\;c$ と $A \to (B \to C) \to D$ に括弧を完全に付け、さらに前者の背骨を与えてください。

<details markdown="1">
<summary>解答</summary>

$f\;a\;(g\;b)\;c = ((f\;a)\;(g\;b))\;c$ で、頭部は $f$、引数は $[a,\; g\;b,\; c]$ です。括弧があるので $g\;b$ は一つの引数のままである点に注意してください。
$A \to (B \to C) \to D = A \to ((B \to C) \to D)$ で、これは $\tPi{\_}{A}{\tPi{\_}{(\tPi{\_}{B}{C})}{D}}$ です。

</details>

</div>

<div class="exercise" markdown="1">

$\tLam{x}{A}{\tLam{y}{x}{\tLam{x}{\Sort{0}}{y}}}$ において、$x$ の各出現はどの束縛子を指しますか。自由変数はどれですか。

<details markdown="1">
<summary>解答</summary>

$y$ の注釈にある $x$ は、まだ内側の $\lambda(x : \Sort{0})$ のスコープに入っていないので、外側の束縛子 $\lambda(x : A)$ を指します。いちばん内側の $x$ は内側の束縛子に束縛されていますが、使われていません。自由変数は $A$ だけです。この項は[第 11 章](11-substitution-alpha.md)で再び登場し、シャドーイングの扱いが雑な型検査器を破綻させます。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 項は宇宙 $\Sort{u}$、変数、$\Pi$ 型、$\lambda$ 抽象、適用の 5 種類で、型と項は同じ文法を共有します。
- $A \to B$ は本体が変数を使わない $\Pi$ 型の略記です。適用は左結合、`->` は右結合で、関数はカリー化されています。
- 束縛変数の名前は任意で、代入は変数の捕獲を避けなければなりません。どちらも第 11 章で扱います。
- Rust では `Term` は形ごとにバリアントを一つ持つ列挙型です。`spine`/`apps` は、入れ子の適用と「頭部と引数のリスト」を相互に変換します。

</div>
