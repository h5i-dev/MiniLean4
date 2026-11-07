<div class="lead" markdown="1">

宇宙和 $\Pi$ 类型已经给出一种逻辑，但还没有可以计算并证明其性质的自然数。归纳类型提供自然数；我们给内核加入常量，声明自然数，并从递归子得到计算与归纳法。

</div>

## 常量与定义

首先需要一种给内核添加具名对象的方式。项新增**常量**（constant）$c$：

$$
t, A, B \;::=\; \cdots \;\mid\; c
$$

**签名**（signature）$\Sigma$ 列出所有常量，每个条目要么只*声明*一个常量及其类型，写作 $c : C$；要么还给出它的体，写作 $c : C \mathrel{:=} t$，带体的条目是**定义**。例如，下文的 $\Nat : \Sort{1}$ 是声明，而本章后面的 $\add$ 是定义。在添加一个条目之前，要先在空上下文中检查它的类型确实是类型；如果有体，还要对照该类型检查它的体，正如 Lean 对每个 `def` 所做的那样。

签名有两种用法。其一，常量的类型就是签名给它的类型：

$$
\dfrac{\ctxok{\Gamma} \qquad (c : C) \in \Sigma}{\Gamma \vdash c : C}\rulename{T-Const}
$$

其中 $(c : C) \in \Sigma$ 同时涵盖声明和定义。其二，定义可以被**展开**：用它的体替换该常量。这一计算步骤称为 **δ 归约**（delta-reduction）：

$$
c \;\deltared\; t \qquad \text{if } (c : C \mathrel{:=} t) \in \Sigma.
$$

例如 $\add\;2\;1 \deltared (\tLam{m}{\Nat}{\tLam{n}{\Nat}{\cdots}})\;2\;1$，之后 β 归约继续进行。没有体的已声明常量，例如 $\Nat$ 或 $\zero$，永远不会 δ 归约。与 β 一样，这一步可以应用于任何子项。

常量不是变量：它们从不被绑定，所以 $\FV(c) = \emptyset$，替换也保持它们不变。现在归约由 β、δ 以及下面引入的 ι 规则组成，而定义相等（[第 12 章](12-reduction-conversion.md)）是相对于这三者定义的。

<aside class="code" markdown="1">

签名是 `src/kernel.rs` 中 `Kernel` 的字段 `decls: HashMap<String, Decl>`。一个 `Decl` 把类型与一个 `DeclKind` 配对，后者记录该常量是 `Axiom`（已声明、无体）、`Definition(body)`，还是由归纳声明生成的三种之一（`Inductive`、`Constructor`、`Recursor`）。`Kernel::axiom` 和 `Kernel::define` 在完成上述检查后添加条目；`infer` 通过查找类型来处理 T-Const；`whnf` 通过展开 `Definition` 来处理 δ。

</aside>

## 自然数

在 Lean 中，自然数声明为

```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

这个声明说，每个自然数都以两种方式之一构造：它是 $\zero$，或者是 $\suc\;n$，即某个自然数 $n$ 的后继。例如，$2$ 是 $\suc\;(\suc\;\zero)$。在我们的内核中，这个声明添加三个没有体的常量：

$$
\Nat : \Sort{1}, \qquad \zero : \Nat, \qquad \suc : \Nat \to \Nat.
$$

$\zero$ 和 $\suc$ 称为**构造子**（constructor），它们构造值，但从不计算：$\suc\;(\suc\;\zero)$ 已经是范式，它*就是*数 $2$。我们用 $0, 1, 2, \ldots$ 表示 $\zero$、$\suc\;\zero$、$\suc\;(\suc\;\zero)$ 等等。

现在我们有了数，却还无法用它们计算：加法需要区分 $\zero$ 和 $\suc\;n$，而目前的项只能传递参数，无法检查它的结构。

## 计算：加法

加法应当如何定义？对第二个参数做递归：

$$
\add\;m\;\zero = m, \qquad \add\;m\;(\suc\;k) = \suc\;(\add\;m\;k).
$$

看看这个定义的形状。固定 $m$ 后，函数 $\add\;m$ 由两份数据决定：它在 $\zero$ 上的值，即 $m$；以及一种把它在 $k$ 上的值 $r$ 变成它在 $\suc\;k$ 上的值的方法，即 $\suc\;r$。每个用这种递归（称为**结构递归**，structural recursion）定义的函数 $f : \Nat \to C$ 都具有相同的形状：

$$
f\;\zero = z, \qquad f\;(\suc\;k) = s\;k\;(f\;k),
$$

其中 $z : C$，$s : \Nat \to C \to C$，步骤函数 $s$ 同时接收 $k$ 和递归调用的结果 $f\;k$。于是我们一劳永逸地添加一个常量，它从 $z$ 和 $s$ 构造出 $f$：

$$
\mathsf{rec}_C : C \to (\Nat \to C \to C) \to \Nat \to C,
$$

并配上两条计算规则，称为 **ι 规则**（iota-rules），它们就是上面的两个等式：

$$
\mathsf{rec}_C\;z\;s\;\zero \;\iotared\; z,
\qquad
\mathsf{rec}_C\;z\;s\;(\suc\;n) \;\iotared\; s\;n\;(\mathsf{rec}_C\;z\;s\;n).
$$

现在加法是一个普通的、非递归的定义：

$$
\add : \Nat \to \Nat \to \Nat \mathrel{:=} \tLam{m}{\Nat}{\tLam{n}{\Nat}{\mathsf{rec}_{\Nat}\;m\;s\;n}},
\qquad
s = \tLam{k}{\Nat}{\tLam{r}{\Nat}{\suc\;r}}.
$$

我们把 $\add\;m\;n$ 写作 $m + n$。内核只用 δ、β 和 ι 步骤就能算出 $2 + 1$，下面的浏览器就是内核在做这件事，一次一个头步骤，并已加载 $\add$ 的定义。

<div class="explorer" data-kind="reduce" data-term="add (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n</pre></div>

每一行是一个头步骤：高亮部分是可归约式（redex），下一行显示它变成了什么。改动数字，或者在上下文 `n : Nat` 下试试 `add Nat.zero n`，就能看到递归子卡住。

其他函数遵循同样的模式：满足 $\mathit{double}\;(\suc\;k) = \suc\;(\suc\;(\mathit{double}\;k))$ 的加倍函数是

$$
\mathit{double} \mathrel{:=} \tLam{n}{\Nat}{\mathsf{rec}_{\Nat}\;\zero\;(\tLam{k}{\Nat}{\tLam{r}{\Nat}{\suc\;(\suc\;r)}})\;n},
$$

并且 $\mathit{double}\;2 \to \suc\;(\suc\;(\mathit{double}\;1)) \to \suc^4\;(\mathit{double}\;0) \to \suc^4\;\zero = 4$。

不需要新的递归机制：归纳类型的常量，加上 $\mathsf{rec}_C$ 及其两条规则，足以表达 $\Nat$ 上所有的结构递归函数。而且与一般递归不同，这种递归总是终止：每一个 ι 步骤都从参数中去掉一个 $\suc$。

<aside class="intuition" markdown="1">

对程序员来说，$\mathsf{rec}_C$ 就是自然数上的 *fold*：正如列表的 `fold` 用一个值处理 `nil`、用一个函数处理 `cons`。fold 每次处理参数的一个构造子，因此不会无限循环。它不如 `while` 循环灵活，但能保证程序终止，而逻辑需要这一保证。

</aside>

## 证明：归纳

现在考虑证明。要证明性质 $P\;n$ 对每个 $n$ 成立，其中 $P : \Nat \to \Sort{0}$，数学上使用归纳法：证明**基础情形** $P\;\zero$，以及**归纳步骤** $\tPi{k}{\Nat}{P\;k \to P\;(\suc\;k)}$，后者的参数 $P\;k$ 就是**归纳假设**。

通过 Curry-Howard 对应，$\tPi{n}{\Nat}{P\;n}$ 的证明是一个函数 $f$，它接收 $n$ 并返回 $P\;n$ 的证明。如何从 $\mathit{base} : P\;\zero$ 和 $\mathit{step}$ 构造出这样的 $f$？对于 $3$，证明是 $\mathit{step}\;2\;(\mathit{step}\;1\;(\mathit{step}\;0\;\mathit{base}))$，一般地

$$
f\;\zero = \mathit{base}, \qquad f\;(\suc\;k) = \mathit{step}\;k\;(f\;k).
$$

这又是一个结构递归函数，形状与上面的 $\add$ 完全相同：$z = \mathit{base}$，$s = \mathit{step}$。**归纳就是返回证明的递归。**

区别在于结果类型：$\add$ 对每个 $n$ 都返回同一类型 $C$，而证明的类型依赖于 $n$，例如 $f\;\zero : P\;\zero$、$f\;1 : P\;1$。因此，类型中带有固定 $C$ 的 $\mathsf{rec}_C$ 还无法表达归纳。

## 一个递归子兼顾两者

把两种情形并排放在一起，就能看出该推广什么。

| | 递归 | 归纳 |
|---|---|---|
| $n$ 处的结果 | $C$ | $P\;n$ |
| $\zero$ 情形 | $z : C$ | $\mathit{base} : P\;\zero$ |
| $\suc$ 情形 | $s : \tPi{k}{\Nat}{C \to C}$ | $\mathit{step} : \tPi{k}{\Nat}{P\;k \to P\;(\suc\;k)}$ |
| 结果 | $\Nat \to C$ | $\tPi{n}{\Nat}{P\;n}$ |

左列是右列的特例，其中 $P\;n$ 对每个 $n$ 都是同一个类型 $C$。所以我们采用右列，并把 $P$ 换成任意函数 $M : \Nat \to \Sort{u}$，它给出每个 $n$ 处结果的类型，这个函数称为 **motive**。所得的就是图 7.1 中的**递归子**（recursor）$\NatRec{u}$，它的参数依次是 motive、每个构造子对应的一个**小前提**（minor premise），最后是要对其递归的数 $n$，称为**大前提**（major premise）。它的 ι 规则就是 $\mathsf{rec}_C$ 的那两条。与 Lean 一样（那里的递归子是 `Nat.rec.{u}`），每个宇宙层级有一个递归子；由于我们没有宇宙多态，层级写成下标。

<div class="rulebox" markdown="1">

<p class="caption">图 7.1. 自然数的常量与递归子的 ι 规则。</p>

$$
\begin{array}{lcll}
\Nat &:& \Sort{1} & \text{Lean: } \texttt{Nat} \\[2pt]
\zero &:& \Nat & \texttt{Nat.zero} \\[2pt]
\suc &:& \Nat \to \Nat & \texttt{Nat.succ} \\[2pt]
\NatRec{u} &:& \tPi{M}{\Nat \to \Sort{u}}{\;M\;\zero \to (\tPi{n}{\Nat}{M\;n \to M\;(\suc\;n)}) \to \tPi{n}{\Nat}{M\;n}} & \texttt{Nat.rec}
\end{array}
$$

$$
\begin{array}{rcl}
\NatRec{u}\;M\;z\;s\;\zero &\iotared& z \\[2pt]
\NatRec{u}\;M\;z\;s\;(\suc\;n) &\iotared& s\;n\;(\NatRec{u}\;M\;z\;s\;n)
\end{array}
$$

</div>

这一个递归子同时胜任两项工作，取决于 motive。

**递归。** 取层级 $1$ 处的常值 motive $\tLam{\_}{\Nat}{C}$，$\NatRec{1}\;(\tLam{\_}{\Nat}{C})$ 的类型与 $\mathsf{rec}_C$ 的类型可转换，所以 $\mathsf{rec}_C$ 不过就是 $\NatRec{1}\;(\tLam{\_}{\Nat}{C})$，从现在起

$$
\add \mathrel{:=} \tLam{m}{\Nat}{\tLam{n}{\Nat}{\NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;m\;(\tLam{k}{\Nat}{\tLam{r}{\Nat}{\suc\;r}})\;n}},
$$

这就是 `examples/zero-add.leanmini` 中的定义。

**归纳。** 取层级 $0$ 处的谓词 $M : \Nat \to \Sort{0}$，$\NatRec{0}$ 的类型就是归纳原理

$$
M\;\zero \to (\forall n.\; M\;n \to M\;(\suc\;n)) \to \forall n.\; M\;n.
$$

这里 T-Pi 中选用 $\imax$ 至关重要：结论 $\tPi{n}{\Nat}{M\;n}$ 的类型是 $\Sort{\imax(1, 0)} = \Sort{0}$，所以尽管 $\Nat$ 位于 $\Sort{1}$，“对每个 $n$ 都有 $M\;n$”仍是一个命题。若改用 $\max$，它就会位于 $\Sort{1}$，关于数的陈述就根本不是命题了。

$\NatRec{u}$ 的类型并不是随意给的：它可以从 $\Nat$ 的声明中直接读出。每个构造子对应一个小前提，它接收该构造子的参数，并为类型是 $\Nat$ 本身的每个参数（**递归**参数）额外接收一个归纳假设，然后返回 motive 作用于该构造子的结果。$\zero$ 没有参数，所以它的情形就是 $M\;\zero$；$\suc$ 有一个递归参数 $n$，所以它的情形是 $\tPi{n}{\Nat}{M\;n \to M\;(\suc\;n)}$。[第 8 章](08-inductive-recipe.md)把这套方法应用到越来越一般的声明上。

## 动手试试

内核启动时已经声明了 $\Nat$ 及其递归子（`src/kernel.rs` 中的 `Kernel::standard`）。下面的脚本定义加法，并请内核确认 $2 + 1$ 与 $3$ 定义相等，`rfl` 通过计算两边来完成这一点。试着把 `three` 改成 `Nat.succ three`，看看内核如何拒绝。

<div class="playground" data-file="add-two-one"><pre>def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def one : Nat := Nat.succ Nat.zero
def two : Nat := Nat.succ one
def three : Nat := Nat.succ two
# 两边都计算到 succ (succ (succ zero))，所以 refl 能证明它。
goal Eq Nat (add two one) three
rfl
qed</pre></div>

目标中的 `Eq` 是相等类型，将在[第 9 章](09-equality.md)声明。目前可以把 `Eq Nat a b` 读作“$a = b$”，把 `rfl` 读作“两边计算到同一个东西”。

<aside class="lean" markdown="1">

Lean 按本章所述从 `inductive` 声明生成 `Nat.rec`，其类型与图 7.1 一致，只差约束变量的名字和隐式参数。Lean 的编译器在执行时把递归子替换为高效的机器算术；它的繁饰器允许用户用模式匹配编写递归函数，并在幕后把它们编译成递归子，但内核看到的始终只有递归子。

</aside>

## 练习

<div class="exercise" markdown="1">

仿照上面 $\add$ 的风格，利用 $\add$，通过对 $n$ 递归定义乘法 $\mathit{mul}\;m\;n$。

<details markdown="1">
<summary>解答</summary>

$\mathit{mul}\;m\;\zero = \zero$ 且 $\mathit{mul}\;m\;(\suc\;k) = \add\;m\;(\mathit{mul}\;m\;k)$，所以
$\mathit{mul} \mathrel{:=} \tLam{m}{\Nat}{\tLam{n}{\Nat}{\NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;\zero\;(\tLam{k}{\Nat}{\tLam{r}{\Nat}{\add\;m\;r}})\;n}}$。

```leanmini
def mul : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) Nat.zero (fun (k : Nat) => fun (r : Nat) => add m r) n
```

</details>

</div>

<div class="exercise" markdown="1">

内核为什么不能接受一般的不动点组合子 $\mathsf{fix} : (C \to C) \to C$ 及其规则 $\mathsf{fix}\;g \to g\;(\mathsf{fix}\;g)$？有了它，每个递归函数都能定义出来。

<details markdown="1">
<summary>解答</summary>

取 $C = \tPi{P}{\Sort{0}}{P}$ 和 $g = \tLam{x}{C}{x}$，项 $\mathsf{fix}\;g$ 的类型将是 $\tPi{P}{\Sort{0}}{P}$，即一切命题的证明，系统因此不一致；它还会永远归约到自身，所以 $\IsDefEq$ 不会终止。结构递归避免了这两个问题，因为每个 ι 步骤都消耗一个构造子。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 常量来自签名 $\Sigma$；定义通过 δ 归约展开，声明永远不展开。
- 归纳类型添加一个类型构造器和若干构造子；构造子构造值，不做计算。
- $\Nat$ 上的结构递归由一个常量即递归子来刻画，每个构造子对应一条 ι 规则。
- 归纳就是同一个递归子配上依赖 motive $M : \Nat \to \Sort{0}$。递归和归纳是同一种操作。
- $\imax$ 规则使“对所有 $n$，$M\;n$”成为命题。

</div>
