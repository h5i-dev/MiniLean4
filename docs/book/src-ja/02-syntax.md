<div class="lead" markdown="1">

カーネルが何かを検査するには、その前に正確な項の言語が要る。本書の言語には 5 種類の項があり、命題の上の量化を含む命題論理を表現するにはそれで足りる。本章では文法、本書の残りで使う記法の約束、そして項を表す Rust の型を定める。

</div>

## 5 種類の項

核となる言語は小さな依存型理論であり、その項は次の文法で生成される。

$$
t, A, B \;::=\; \Sort{u} \;\mid\; x \;\mid\; \tPi{x}{A}{B} \;\mid\; \tLam{x}{A}{t} \;\mid\; t\;s
$$

ここで $u$ は自然数、$x$ は変数名である。各形には役割がある。

- $\Sort{u}$ は**宇宙**（universe）、すなわち要素がそれ自体型であるような型で、数 $u$ はその*レベル*である。$\Sort{0}$ は命題の宇宙である。宇宙が一つではなく階層全体になっている理由は[第 13 章](13-universes.md)で説明する。
- $x$ は**変数**であり、その意味は現れる文脈、すなわちそれを囲む $\lambda$ か $\Pi$ の束縛子か、型付け文脈の仮定から決まる。
- $\tPi{x}{A}{B}$ は **$\Pi$ 型**、[第 1 章](01-propositions-as-types.md)の依存関数型である。$x : A$ を受け取って型 $B$ のものを返す関数の型であり、$B$ は $x$ に言及してよい。
- $\tLam{x}{A}{t}$ は **$\lambda$ 抽象**で、型 $A$ の引数 $x$ を受け取って $t$ を返す関数である。
- $t\;s$ は $t$ の $s$ への**適用**である。

この文法は型と項を区別せず、命題 $\tPi{P}{\Sort{0}}{P \to P}$ もその証明 $\tLam{P}{\Sort{0}}{\tLam{p}{P}{p}}$ も、同じ 5 つの構成子から組み立てた項である。

$$
\underbrace{\tLam{P}{\Sort{0}}{\tLam{p}{P}{p}}}_{\text{proof}}
\quad : \quad
\underbrace{\tPi{P}{\Sort{0}}{P \to P}}_{\text{proposition, the type of the proof}}.
$$

この二つの項を木として見ると文法が共有されていることが目に見え、どの節点も 5 つの構成子のどれかで、$\Pi$ や $\lambda$ の節点に付いた名前はそれが束縛する変数である。節点をクリックすればそれが表す部分項が見えるし、別の項を入力してもよい。

<div class="explorer" data-kind="ast" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

項が妥当な*型*であるかどうかは構文的な性質ではなく、型検査器が決める。項が型であるのは、その項自身の型が宇宙であるとき、そのときに限る（[第 5 章](05-algorithm.md)）。

<aside class="note" markdown="1">

第 II 部ではもう一つの形、**定数** $c$ を加える。定数はカーネルのシグネチャで宣言されたもの、たとえば $\mathsf{Nat}$ や $\mathsf{Nat.succ}$ を名指し、型が大域的な表から来る自由変数のように振る舞って、束縛されることはない。第 I 部の内容は定数なしで成り立つので、必要になる[第 7 章](07-inductive-nat.md)で導入するが、下の Rust の型には定数がすでに含まれている。

</aside>

## 記法の約束

本書では次の文字を一貫して使う。

| 文字 | 意味 |
|---|---|
| $s, t, a, b, f$ および $A, B, C, T$（プライムや添字が付くこともある） | 項 |
| $x, y, z$ および $\Pi$ や $\lambda$ で束縛される任意の名前 | 変数名 |
| $u, v, w$ | 宇宙レベル |
| $\Gamma$ | 型付け文脈（[第 3 章](03-typing-rules.md)） |
| $\Sigma$ | 定数のシグネチャ（[第 7 章](07-inductive-nat.md)） |

項を読みやすくするために、三つの略記を使う。

**`->`。** $B$ が $x$ に言及しないとき、$\tPi{x}{A}{B}$ を $A \to B$ と書く。したがってふつうの関数型は依存関数型の特別な場合であり、含意は全称量化の特別な場合である。実装では、`->` の束縛子は予約された名前 `_` である。

**結合性。** 適用は左に、`->` は右に結合する。

$$
f\;a\;b \;=\; (f\;a)\;b,
\qquad
A \to B \to C \;=\; A \to (B \to C).
$$

**カリー化。** 二引数の関数とは、一つ目の引数を受け取って、二つ目を待つ関数を返す関数である。たとえば $\tLam{a}{A}{\tLam{b}{B}{a}}$ は型 $A \to B \to A$ を持ち、これを $x : A$ と $y : B$ に適用することを次のように書く。

$$
(\tLam{a}{A}{\tLam{b}{B}{a}})\;x\;y \;=\; ((\tLam{a}{A}{\tLam{b}{B}{a}})\;x)\;y.
$$

二つの結合性の約束は噛み合うように決めてあり、型 $A \to B \to C$ のカリー化された関数を $f\;a\;b$ と適用するとき、どちらの側にも括弧は要らない。

<aside class="intuition" markdown="1">

カリー化のおかげで、言語全体が一引数関数だけで済む。$A \to B \to C$ の証明は、$A$ の証明を与えられると $B \to C$ の証明を返す関数であり、その証明もまた関数である。「$A$ と $B$ を仮定する」は入れ子になった二つの仮定になり、証明項の二つの $\lambda$ がそれを映している。

</aside>

## 束縛とスコープ

$\tLam{x}{A}{t}$ と $\tPi{x}{A}{B}$ において、変数 $x$ は*束縛*されており、その*スコープ*は本体 $t$ または $B$ であり、注釈 $A$ はスコープの外にある。$\tLam{x}{x}{x}$ では、注釈の中の $x$ は項の外にある何かを指し、本体の $x$ は引数を指す。自分を束縛する束縛子のスコープの中にない変数の出現は*自由*である。たとえば $\tLam{x}{P}{f\;x\;y}$ では、変数 $P$、$f$、$y$ が自由で、$x$ が束縛されている。

束縛変数については、本書全体で重要になる事実が二つあり、どちらも[第 11 章](11-substitution-alpha.md)で形式化する。

1. 束縛変数の名前には意味がなく、$\tLam{x}{A}{x}$ と $\tLam{y}{A}{y}$ は同じ関数である。束縛変数の名前だけが異なる項を *α 同値*（alpha-equivalent）と呼び、カーネルはそれらを等しいものとして扱わなければならない。
2. 変数を項で置き換える操作は型付け規則にも計算にも必要だが、その際に自由変数をうっかり同じ名前の束縛子の下に持ち込んではならない。これを正しく行うことを*捕獲回避代入*（capture-avoiding substitution）と呼ぶ。

どちらの事実も述べるのは簡単だが、どちらも実際の証明検査器で本物のバグを引き起こしてきたからこそ、一章を割いている。

## コードでは

<aside class="code" markdown="1">

項は `src/term.rs` の Rust の列挙型 `Term` であり、項の種類ごとにひとつのバリアントがあって、それに第 II 部の定数が加わる。

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

変数は名前の文字列で表し、束縛子は束縛する名前を保持する。これはもっとも直接的で読みやすい表現であり、同時に[第 11 章](11-substitution-alpha.md)の名前の問題を避けられなくする表現でもある。本書の目的はその問題を目にして解くことにあるので、それは意図したことである。

</aside>

同じファイルには、入れ子の `Box::new` 呼び出しなしで項を書けるように、小さな構成関数も用意してある。`var("x")`、`const_term("Nat")`、`app(f, a)`、`pi("x", a, b)`、`lam("x", a, b)`、そして `pi("_", a, b)` を作る `arrow(a, b)` である。さらに三つの補助関数が、本章の約束をそのままコードにしている。

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

`apps` と `spine` は互いに逆であり、`apps(h, args)` が左に入れ子になった適用 $h\;a_1 \cdots a_n$ を組み立て、`spine` がそれを再びばらす。[第 12 章](12-reduction-conversion.md)の簡約エンジンは項をこの背骨（spine）の形で見るので、今のうちに慣れておいてほしい。入れ子の項 $((f\;a)\;b)\;c$ の頭部は $f$、引数は $[a, b, c]$ である。各適用の関数側をたどって下りていくと頭部に着き、途中で集めた引数を内側から外側へ読めば正しい順序になる。

本書全体で使う `.leanmini` スクリプトの表層構文では、同じ項を `Sort 0`、`forall (x : A), B`、`A -> B`、`fun (x : A) => b` と書き、適用は並置で表す。完全な文法は[付録 E](e-leanmini-reference.md)にある。

## 演習

<div class="exercise" markdown="1">

命題「すべての命題 $P$ と $Q$ について、$P$ ならば $Q$ ならば $P$」を項として書き、その証明項を与えよ。

<details markdown="1">
<summary>解答</summary>

この命題は $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q \to P}}$ であり、展開すると
$\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{\tPi{\_}{P}{\tPi{\_}{Q}{P}}}}$ になる。
証明の一つは $\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{\tLam{q}{Q}{p}}}}$ である。leanmini の構文では次のようになる。

```leanmini
goal forall (P : Sort 0), forall (Q : Sort 0), P -> Q -> P
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (p : P) => fun (q : Q) => p
qed
```

</details>

</div>

<div class="exercise" markdown="1">

$f\;a\;(g\;b)\;c$ と $A \to (B \to C) \to D$ に括弧を完全に付け、さらに前者の背骨を与えよ。

<details markdown="1">
<summary>解答</summary>

$f\;a\;(g\;b)\;c = ((f\;a)\;(g\;b))\;c$ で、頭部は $f$、引数は $[a,\; g\;b,\; c]$ である。括弧があるので $g\;b$ は一つの引数のままであることに注意。
$A \to (B \to C) \to D = A \to ((B \to C) \to D)$ で、これは $\tPi{\_}{A}{\tPi{\_}{(\tPi{\_}{B}{C})}{D}}$ である。

</details>

</div>

<div class="exercise" markdown="1">

$\tLam{x}{A}{\tLam{y}{x}{\tLam{x}{\Sort{0}}{y}}}$ において、$x$ の各出現はどの束縛子を指すか。自由変数はどれか。

<details markdown="1">
<summary>解答</summary>

$y$ の注釈にある $x$ は、内側の $\lambda(x : \Sort{0})$ にはまだ入っていないので、外側の束縛子 $\lambda(x : A)$ を指す。いちばん内側の $x$ は内側の束縛子に束縛されているが、使われていない。自由変数は $A$ だけである。この項は[第 11 章](11-substitution-alpha.md)に再登場し、シャドーイングを雑に扱う型検査器を壊す。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 項は宇宙 $\Sort{u}$、変数、$\Pi$ 型、$\lambda$ 抽象、適用であり、型と項は一つの文法を共有する。
- $A \to B$ は本体が変数を使わない $\Pi$ 型の略記である。適用は左結合、`->` は右結合で、関数はカリー化されている。
- 束縛変数の名前は任意であり、代入は捕獲を避けなければならず、どちらも第 11 章で扱う。
- Rust では `Term` が形ごとに一つのバリアントを持つ列挙型であり、`spine`/`apps` が入れ子の適用と「頭部と引数のリスト」の間を相互に変換する。

</div>
