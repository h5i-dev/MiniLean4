<div class="lead" markdown="1">

这个内核从五种项开始，它们足以表达带命题量化的命题逻辑。编写类型检查器之前，先确定项的文法和记法，再给出对应的 Rust `Term` 类型。

</div>

## 五种项

核心语言是一个小型依赖类型论，它的项由如下文法生成

$$
t, A, B \;::=\; \Sort{u} \;\mid\; x \;\mid\; \tPi{x}{A}{B} \;\mid\; \tLam{x}{A}{t} \;\mid\; t\;s
$$

其中 $u$ 是自然数，$x$ 是变量名。每种形式各有角色。

- $\Sort{u}$ 是**宇宙**（universe）：一种元素本身也是类型的类型，数 $u$ 是它的*层级*，而 $\Sort{0}$ 是命题的宇宙。[第 13 章](13-universes.md)解释为什么需要整个层级结构，而不是单个宇宙。
- $x$ 是**变量**，它的含义来自所在的上下文：要么是包围它的某个 $\lambda$ 或 $\Pi$ 绑定子，要么是类型上下文中的一条假设。
- $\tPi{x}{A}{B}$ 是 **$\Pi$ 类型**，即[第 1 章](01-propositions-as-types.md)的依赖函数类型，也就是这样一类函数的类型：接收一个 $x : A$，返回类型为 $B$ 的东西，而 $B$ 可以提到 $x$。
- $\tLam{x}{A}{t}$ 是 **$\lambda$ 抽象**，即接收类型为 $A$ 的参数 $x$ 并返回 $t$ 的函数。
- $t\;s$ 是 $t$ 对 $s$ 的**应用**。

文法不区分类型和项，命题 $\tPi{P}{\Sort{0}}{P \to P}$ 和它的证明 $\tLam{P}{\Sort{0}}{\tLam{p}{P}{p}}$ 都是由同样五种构造子搭建的项：

$$
\underbrace{\tLam{P}{\Sort{0}}{\tLam{p}{P}{p}}}_{\text{proof}}
\quad : \quad
\underbrace{\tPi{P}{\Sort{0}}{P \to P}}_{\text{proposition, the type of the proof}}.
$$

把这两个项画成树，共用的文法就一目了然。每个节点都是五种构造子之一；$\Pi$ 或 $\lambda$ 节点上的名字是它绑定的变量。点击节点可以查看它代表的子项，也可以输入另一个项。

<div class="explorer" data-kind="ast" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

一个项是否为合法的*类型*，不是语法性质，而是由类型检查器判定的：一个项是类型，当且仅当它自己的类型是一个宇宙（[第 5 章](05-algorithm.md)）。

<aside class="note" markdown="1">

第二部分会再加一种形式：**常量** $c$，它命名内核签名中声明的东西，比如 $\mathsf{Nat}$ 或 $\mathsf{Nat.succ}$。常量的行为像自由变量，只是类型来自一张全局表，而且永远不会被绑定。第一部分的所有内容都不需要常量，因此它们在需要时，也就是[第 7 章](07-inductive-nat.md)，才正式引入，不过下面的 Rust 类型已经包含了它们。

</aside>

## 约定

本书始终如一地使用以下字母。

| 字母 | 表示 |
|---|---|
| $s, t, a, b, f$ 以及 $A, B, C, T$（可带撇号或下标） | 项 |
| $x, y, z$ 以及任何由 $\Pi$ 或 $\lambda$ 绑定的名字 | 变量名 |
| $u, v, w$ | 宇宙层级 |
| $\Gamma$ | 类型上下文（[第 3 章](03-typing-rules.md)） |
| $\Sigma$ | 常量签名（[第 7 章](07-inductive-nat.md)） |

三个缩写让项保持可读。

**`->`。**当 $B$ 不提到 $x$ 时，我们把 $\tPi{x}{A}{B}$ 写作 $A \to B$。于是普通函数类型是依赖函数类型的特例，蕴含是全称量化的特例。在实现中，`->` 的绑定子是保留名 `_`。

**结合性。**应用向左结合，`->` 向右结合：

$$
f\;a\;b \;=\; (f\;a)\;b,
\qquad
A \to B \to C \;=\; A \to (B \to C).
$$

**柯里化。**两个参数的函数，就是接收第一个参数后返回一个等待第二个参数的函数。例如，$\tLam{a}{A}{\tLam{b}{B}{a}}$ 的类型是 $A \to B \to A$，把它应用于 $x : A$ 和 $y : B$ 写作

$$
(\tLam{a}{A}{\tLam{b}{B}{a}})\;x\;y \;=\; ((\tLam{a}{A}{\tLam{b}{B}{a}})\;x)\;y.
$$

两条结合性约定是配套设计的：类型为 $A \to B \to C$ 的柯里化函数以 $f\;a\;b$ 的形式应用时，两边都不需要括号。

<aside class="intuition" markdown="1">

柯里化是整个语言只需要单参数函数的原因。$A \to B \to C$ 的证明是一个函数：给定 $A$ 的证明，返回 $B \to C$ 的证明，而后者本身又是函数。“假设 $A$ 和 $B$”变成两层嵌套的假设，证明项中的两个 $\lambda$ 正与之对应。

</aside>

## 绑定与作用域

在 $\tLam{x}{A}{t}$ 和 $\tPi{x}{A}{B}$ 中，变量 $x$ 是*约束的*（bound），它的*作用域*是函数体 $t$ 或 $B$。标注 $A$ 在作用域之外：在 $\tLam{x}{x}{x}$ 中，标注里的 $x$ 指向项外部的某个东西，而函数体里的 $x$ 指向参数。不处于任何对应绑定子作用域内的变量出现称为*自由的*（free）。例如，在 $\tLam{x}{P}{f\;x\;y}$ 中，变量 $P$、$f$ 和 $y$ 是自由的，$x$ 是约束的。

关于约束变量有两个事实贯穿全书，两者都在[第 11 章](11-substitution-alpha.md)中形式化。

1. 约束变量的名字没有意义：$\tLam{x}{A}{x}$ 和 $\tLam{y}{A}{y}$ 是同一个函数。仅在约束变量名上有差异的项称为 *α 等价*的，内核必须把它们视为相等。
2. 用项替换变量（类型规则和计算都需要这一操作）时，绝不能意外地把自由变量带进同名绑定子之下。把这件事做对就叫*避免捕获的替换*。

这两个事实都容易陈述，也都在真实的证明检查器中造成过真实的错误，所以它们有专门的一章。

## 代码中

<aside class="code" markdown="1">

项是 `src/term.rs` 中的 Rust 枚举 `Term`，每种项对应一个变体，另加第二部分的常量。

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

变量用字符串形式的名字表示，绑定子存储所绑定的名字。这是最直接、最易读的表示，也正是让[第 11 章](11-substitution-alpha.md)的命名问题无法回避的表示。这是有意为之，因为本书的要点就是看清这些问题并解决它们。

</aside>

同一文件还提供了一些小的构造函数，使得写项时不必嵌套 `Box::new` 调用：`var("x")`、`const_term("Nat")`、`app(f, a)`、`pi("x", a, b)`、`lam("x", a, b)`，以及构造 `pi("_", a, b)` 的 `arrow(a, b)`。三个辅助函数直接编码了本章的约定。

```rust
/// f a_1 ... a_n   （左结合的应用）
pub fn apps(f: Term, args: impl IntoIterator<Item = Term>) -> Term {
    args.into_iter().fold(f, app)
}

/// Pi (x_1 : A_1) ... Pi (x_k : A_k). tail   （由绑定子组成的 telescope）
pub fn telescope(binders: &[(String, Term)], tail: Term) -> Term {
    binders.iter().rev().fold(tail, |body, (name, ty)| pi(name, ty.clone(), body))
}

/// 把 t 分解为它的脊（spine）：一个不是应用的头部，以及它的参数。
/// f a b  变成  (f, [a, b])；非应用的项变成  (t, [])。
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

`apps` 和 `spine` 互为逆操作：`apps(h, args)` 构造左嵌套的应用 $h\;a_1 \cdots a_n$，`spine` 再把它拆开。脊（spine）视角是[第 12 章](12-reduction-conversion.md)的归约引擎看待项的方式，所以现在就熟悉它。嵌套项 $((f\;a)\;b)\;c$ 的头部是 $f$，参数是 $[a, b, c]$；沿每个应用的函数一侧向下走就到达头部，沿途收集的参数由内向外读，顺序正好。

本书通篇使用的 `.leanmini` 脚本的表层语法把同样的项写成 `Sort 0`、`forall (x : A), B`、`A -> B`、`fun (x : A) => b`，应用则用并置表示。[附录 E](e-leanmini-reference.md)给出完整文法。

## 练习

<div class="exercise" markdown="1">

把命题“对所有命题 $P$ 和 $Q$，$P$ 蕴含 $Q$ 蕴含 $P$”写成一个项，并给出它的证明项。

<details markdown="1">
<summary>解答</summary>

该命题是 $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q \to P}}$，展开后为
$\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{\tPi{\_}{P}{\tPi{\_}{Q}{P}}}}$。
一个证明是 $\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{\tLam{q}{Q}{p}}}}$。用 leanmini 语法写出：

```leanmini
goal forall (P : Sort 0), forall (Q : Sort 0), P -> Q -> P
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (p : P) => fun (q : Q) => p
qed
```

</details>

</div>

<div class="exercise" markdown="1">

给 $f\;a\;(g\;b)\;c$ 和 $A \to (B \to C) \to D$ 加上全部括号，然后给出第一个项的脊。

<details markdown="1">
<summary>解答</summary>

$f\;a\;(g\;b)\;c = ((f\;a)\;(g\;b))\;c$，头部为 $f$，参数为 $[a,\; g\;b,\; c]$。注意由于括号的存在，$g\;b$ 仍是单个参数。
$A \to (B \to C) \to D = A \to ((B \to C) \to D)$，即 $\tPi{\_}{A}{\tPi{\_}{(\tPi{\_}{B}{C})}{D}}$。

</details>

</div>

<div class="exercise" markdown="1">

在 $\tLam{x}{A}{\tLam{y}{x}{\tLam{x}{\Sort{0}}{y}}}$ 中，各处出现的 $x$ 分别指向哪个绑定子？哪些变量是自由的？

<details markdown="1">
<summary>解答</summary>

$y$ 的标注中的 $x$ 指向外层绑定子 $\lambda(x : A)$，因为此时还没有进入内层的 $\lambda(x : \Sort{0})$。最内层的 $x$ 由内层绑定子绑定但从未被使用，而唯一的自由变量是 $A$。这个项会在[第 11 章](11-substitution-alpha.md)再次出现，在那里它让一个处理遮蔽不够小心的类型检查器出错。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 项有宇宙 $\Sort{u}$、变量、$\Pi$ 类型、$\lambda$ 抽象和应用五种，类型和项共用一套文法。
- $A \to B$ 是函数体不使用其变量的 $\Pi$ 类型的缩写。应用向左结合，`->` 向右结合，函数是柯里化的。
- 约束变量的名字可以任取，替换必须避免捕获，两者都在第 11 章处理。
- 在 Rust 中，`Term` 是每种形式对应一个变体的枚举，`spine`/`apps` 在嵌套应用与“头部加参数列表”之间来回转换。

</div>
