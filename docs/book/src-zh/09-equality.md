<div class="lead" markdown="1">

要陈述关于数的事实，例如 $0 + n = n$，我们需要一种方式来表达两个东西相等。人们或许以为相等是内核的原语，带着自己的规则内置其中。并非如此。相等只是另一个归纳类型，由第 8 章的方法生成，而它的递归子正是把关于 $a$ 的事实转化为关于 $b$ 的事实的原理。本章声明这个类型，解释此时并存的两种相等概念，并证明本书第一个真正的定理。

</div>

## 声明

在 Lean 中，相等的声明是

```lean
inductive Eq {A : Sort u} (a : A) : A -> Prop where
  | refl : Eq a a
```

对 $a, b : A$，类型 $\Eq{u}\;A\;a\;b$ 是“$a$ 与 $b$ 相等”这一命题；当 $A$ 是 $\Nat$ 时我们把它写作 $a = b$。用第 8 章的术语说，$A$ 和 $a$ 是参数，$b$ 是索引：

$$
\Eq{u} : \tPi{A}{\Sort{u}}{A \to A \to \Sort{0}}, \qquad
\refl{u} : \tPi{A}{\Sort{u}}{\tPi{a}{A}{\Eq{u}\;A\;a\;a}}.
$$

唯一的构造子 $\refl{u}$ 没有字段，它的索引项是 $a$：它只能证明两边是*同一个* $a$ 的等式。所以 $\Eq{}$ 像 $\mathsf{Vec}$ 一样是归纳族，而不是单个类型。左边由参数固定；右边可变，而构造子把它钉在左边上。

<aside class="intuition" markdown="1">

为什么一个构造子就够了？因为这个声明并不*定义*两个东西何时相等；它说的是相等的证明可以如何*构造*，而唯一的方式就是观察到某物等于它自己。其余一切，如对称性、传递性和替换，都由递归子导出，递归子说的是一旦有了这样的证明，能用它做什么。

</aside>

## 递归子：传输

非形式地说，$\Eq{}$ 的递归子表示：*若 $a = b$，则凡对 $a$ 成立者对 $b$ 也成立。* 这是莱布尼茨原理，其最常见的形式是

$$
\EqRec{u,v} : \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{A \to \Sort{v}}{M\;a \to \tPi{b}{A}{\Eq{u}\;A\;a\;b \to M\;b}}}}.
$$

给定 $A$ 的元素的一个性质 $M$、证据 $m : M\;a$ 和 $a = b$ 的证明 $h$，它返回 $M\;b$ 的证据。我们说它沿着 $h$ **传输** $m$。它的计算规则说，沿着 $\refl{}$ 传输什么也不做：

$$
\EqRec{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A\;c) \;\to\; m.
$$

第 8 章的通用方法生成的版本略为一般，$\EqRec{}$ 是由它构造出的一个定义。

<details markdown="1">
<summary>由通用方法生成的完整依赖递归子</summary>

由于 $b$ 是索引，动机接受 $b$ *以及*证明 $h : \Eq{u}\;A\;a\;b$，并且只有一个小前提，对应 $\refl{u}$，没有字段也没有假设：

$$
\begin{array}{l}
\EqRecDep{u,v} : \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{(\tPi{b}{A}{\Eq{u}\;A\;a\;b \to \Sort{v}})}{{}}}} \\[2pt]
\qquad\qquad M\;a\;(\refl{u}\;A\;a) \to \tPi{b}{A}{\tPi{h}{\Eq{u}\;A\;a\;b}{M\;b\;h}} \\[8pt]
\EqRecDep{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A'\;c) \;\iotared\; m.
\end{array}
$$

$\Eq{}$ 是子单元（一个构造子，没有字段），所以 $v$ 是任意的：相等的证明可以用来构造数据，而不只是证明。非依赖的 $\EqRec{u,v}$ 是动机忽略证明的特例：

$$
\begin{array}{l}
\EqRec{u,v} \mathrel{:=} \tLam{A}{\Sort{u}}{\tLam{a}{A}{\tLam{M}{A \to \Sort{v}}{\tLam{m}{M\;a}{\tLam{b}{A}{\tLam{h}{\Eq{u}\;A\;a\;b}{{}}}}}}} \\[2pt]
\qquad\qquad \EqRecDep{u,v}\;A\;a\;(\tLam{b'}{A}{\tLam{\_}{\Eq{u}\;A\;a\;b'}{M\;b'}})\;m\;b\;h.
\end{array}
$$

在良类型的可归约式中 $b$ 和 $c$ 都可转换为 $a$，所以规则可以忽略它们。图 9.1 总结了这些常量。

<div class="rulebox" markdown="1">

<p class="caption">图 9.1。相等的常量及其计算规则。$\EqRec{u,v}$ 的规则由其定义经 δ、β 以及 $\EqRecDep{u,v}$ 的规则推出。</p>

$$
\begin{array}{lcll}
\Eq{u} &:& \tPi{A}{\Sort{u}}{A \to A \to \Sort{0}} & \text{Lean: } \texttt{Eq} \\[2pt]
\refl{u} &:& \tPi{A}{\Sort{u}}{\tPi{a}{A}{\Eq{u}\;A\;a\;a}} & \texttt{Eq.refl} \\[2pt]
\EqRecDep{u,v} &:& \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{(\tPi{b}{A}{\Eq{u}\;A\;a\;b \to \Sort{v}})}{M\;a\;(\refl{u}\;A\;a) \to \tPi{b}{A}{\tPi{h}{\Eq{u}\;A\;a\;b}{M\;b\;h}}}}} & \texttt{Eq.rec} \\[2pt]
\EqRec{u,v} &:& \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{A \to \Sort{v}}{M\;a \to \tPi{b}{A}{\Eq{u}\;A\;a\;b \to M\;b}}}} & \texttt{Eq.ndrec}\ \text{(definition)}
\end{array}
$$

$$
\begin{array}{rcl}
\EqRecDep{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A\;c) &\iotared& m \\[2pt]
\EqRec{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A\;c) &\to_{\delta\beta\iota}& m
\end{array}
$$

</div>

</details>

例如，设 $P : \Nat \to \Sort{0}$，$a, b : \Nat$，$h : a = b$，$\mathit{pa} : P\;a$。取动机 $M = P$，得到

$$
\EqRec{1,0}\;\Nat\;a\;P\;\mathit{pa}\;b\;h \;:\; P\;b.
$$

这一行就是*重写*的逻辑内容：关于 $a$ 的事实变成关于 $b$ 的事实。[第 10 章](10-tactics.md)的 `rw` 策略会自动构造这样的项。

<aside class="lean" markdown="1">

在 Lean 中，`Eq` 的类型参数是*隐式的*，在声明中写作 `{A}`，由繁释器填入，所以用户写 `Eq a b` 或 `a = b`。我们的内核只看到完全显式的项，因此我们写出每一个参数；填入它们是内核之上那一层的工作。在脚本语言中，这些常量是 `Eq`、`Eq.refl` 以及依赖递归子 `Eq.rec0` 和 `Eq.rec1`；非依赖的 $\EqRec{}$ 没有预先声明，但它只是一个两行的定义，见下面的演练场。由于没有宇宙多态，内核只在 $A : \Sort{1}$ 处声明一次 `Eq`，这覆盖了 $\Nat$ 和每个用户声明的数据类型；证明之间的相等则不可用。

</aside>

## 定义相等与命题相等

现在有了两种相等概念，区分它们是理解证明助手行为的关键。

- **定义相等** $\conv$ 由内核通过计算来判定。它是关于项的判断，不是类型；不涉及任何证明对象。
- **命题相等** $\Eq{}$ 是一个类型。它的证明是项，找到一个证明可能需要真正的推理，例如归纳。

构造子 $\refl{}$ 把二者联系起来：由 T-Conv，只要 $a \conv b$，就有 $\refl{u}\;A\;a : \Eq{u}\;A\;a\;b$。所以每个定义相等都免费给出一个命题相等。反之不成立，标准的例子是 $n + 0 = n$ 和 $0 + n = n$ 这两半。采用第 7 章 $\add$ 的定义，并记 $s$ 为它的步骤函数，

$$
n + 0 \;\to_{\delta\beta}\; \NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;n\;s\;\zero \;\iotared\; n,
$$

所以 $\refl{1}\;\Nat\;n : n + 0 = n$，Lean 用 `rfl` 证明它。相反，

$$
0 + n \;\to_{\delta\beta}\; \NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;0\;s\;n
$$

是**卡住的**：$n$ 是变量，而 ι 规则只在 $\zero$ 和 $\suc$ 上触发。所以 $0 + n = n$ 不能用 $\refl{}$ 证明，需要归纳。

归约浏览器展示了这两个计算，其中 $n$ 是上下文中的变量。第一个到达 $n$；第二个停在递归子处，等待一个永远不会到来的构造子。

<div class="explorer" data-kind="reduce" data-term="add n Nat.zero" data-ctx="n : Nat"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n</pre></div>

<div class="explorer" data-kind="reduce" data-term="add Nat.zero n" data-ctx="n : Nat"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n</pre></div>

<div class="playground" data-file="plus-zero"><pre>def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n

# n + 0 = n 由计算成立：递归子看到的是构造子 zero。
goal forall (n : Nat), Eq Nat (add n Nat.zero) n
intro n
rfl
qed

# 0 + n = n 则不然：递归子卡在变量 n 上。
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
rfl</pre></div>

<aside class="warning" markdown="1">

哪些等式由 `rfl` 成立，取决于函数是*如何*定义的，而不是它计算什么。对第二个参数递归的加法使 $n + 0 = n$ 成为定义相等、$0 + n = n$ 成为命题相等；对第一个参数递归则会把二者对调。Lean 用户经常遇到这种情况：`rfl` 能否关闭目标，取决于相关定义中递归的方向。

</aside>

## 示例：证明 0 + n = n

我们用归纳证明 $\tPi{n}{\Nat}{0 + n = n}$，使用 $\NatRec{0}$ 和动机 $M_0 = \tLam{n}{\Nat}{0 + n = n}$。

**基础情形。** 我们需要 $M_0\;0$，它可转换为 $0 + 0 = 0$。由于 $0 + 0$ 计算为 $0$，项 $\refl{1}\;\Nat\;0$ 即可。

**归纳步骤。** 给定 $k : \Nat$ 和 $\mathit{ih} : 0 + k = k$，我们需要 $M_0\;(\suc\;k)$，即 $0 + \suc\;k = \suc\;k$。由第二条 ι 规则，$0 + \suc\;k$ 计算为 $\suc\;(0 + k)$，所以只需证明 $\suc\;(0 + k) = \suc\;k$。我们从 $\refl{1}\;\Nat\;(\suc\;(0 + k))$ 出发，它是 $\suc\;(0+k) = \suc\;(0+k)$ 的证明，然后用动机 $N = \tLam{b}{\Nat}{\suc\;(0 + k) = \suc\;b}$ 沿着 $\mathit{ih}$ 传输它，这把*第二个* $0 + k$ 替换为 $k$：

$$
\mathit{step} = \tLam{k}{\Nat}{\tLam{\mathit{ih}}{0 + k = k}{
  \EqRec{1,0}\;\Nat\;(0 + k)\;N\;(\refl{1}\;\Nat\;(\suc\;(0 + k)))\;k\;\mathit{ih}}}.
$$

证明为

$$
\mathit{zero\_add} = \NatRec{0}\;M_0\;(\refl{1}\;\Nat\;0)\;\mathit{step} \;:\; \tPi{n}{\Nat}{0 + n = n}.
$$

内核用算法 5.1 检查它。每个参数都对照 $\NatRec{0}$ 的类型中以 $M_0$ 实例化后的相应部分进行检查，每次比较都在规范化之后成功。下面是完整的项，一次性提交给内核。非依赖递归子先定义，如图 9.1 所示。

<div class="playground" data-file="zero-add-term"><pre>def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n

# 层级 (1, 0) 的 Eq.ndrec：沿着 a = b 把 M a 的证明传输到 M b。
def ndrec : forall (A : Sort 1), forall (a : A), forall (M : A -> Sort 0), M a -> forall (b : A), Eq A a b -> M b := fun (A : Sort 1) => fun (a : A) => fun (M : A -> Sort 0) => fun (m : M a) => fun (b : A) => fun (h : Eq A a b) => Eq.rec0 A a (fun (b' : A) => fun (_h : Eq A a b') => M b') m b h

goal forall (n : Nat), Eq Nat (add Nat.zero n) n
exact Nat.rec0 (fun (n : Nat) => Eq Nat (add Nat.zero n) n) (Eq.refl Nat Nat.zero) (fun (k : Nat) => fun (ih : Eq Nat (add Nat.zero k) k) => ndrec Nat (add Nat.zero k) (fun (b : Nat) => Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ b)) (Eq.refl Nat (Nat.succ (add Nat.zero k))) k ih)
qed</pre></div>

手写这样的项很繁琐，而找到正确的动机才是难点：动机 $N$ 必须恰好在 $0 + k$ 出现的两处之一提及 $b$。策略（[第 10 章](10-tactics.md)）把记账工作和动机的选择都自动化了。

## 内核的变化

从命题逻辑走到带相等的算术，内核改动很少。$\Infer$ 增加了常量的情形，它在 $\Sigma$ 中查找类型（T-Const）。$\Check$ 没有变化。只有 $\Whnf$，以及经由它的 $\IsDefEq$，学会了新的 δ 步骤和 ι 步骤。[第 12 章](12-reduction-conversion.md)展示单个 $\Whnf$ 如何处理每一种归纳类型，[第 14 章](14-properties.md)讨论归纳类型给元理论带来的变化。

## 练习

<div class="exercise" markdown="1">

证明相等的对称性：用 $\EqRec{}$ 构造一个类型为 $\tPi{a}{\Nat}{\tPi{b}{\Nat}{a = b \to b = a}}$ 的项。

<details markdown="1">
<summary>解答</summary>

用动机 $\tLam{x}{\Nat}{x = a}$ 沿着 $h : a = b$ 传输证明 $\refl{}\;a : a = a$，这把 $a = a$ 变成 $b = a$：
$\tLam{a}{\Nat}{\tLam{b}{\Nat}{\tLam{h}{a = b}{\EqRec{1,0}\;\Nat\;a\;(\tLam{x}{\Nat}{x = a})\;(\refl{1}\;\Nat\;a)\;b\;h}}}$。

```leanmini
goal forall (a : Nat), forall (b : Nat), Eq Nat a b -> Eq Nat b a
exact fun (a : Nat) => fun (b : Nat) => fun (h : Eq Nat a b) => ndrec Nat a (fun (x : Nat) => Eq Nat x a) (Eq.refl Nat a) b h
qed
```

（其中 `ndrec` 的定义同上面的演练场。）

</details>

</div>

<div class="exercise" markdown="1">

解释为什么 $\Eq{}$ 虽是命题却能消去到每个宇宙，而有两个构造子的类型 `Or` 却不能。

<details markdown="1">
<summary>解答</summary>

$\Eq{}$ 是子单元：一个构造子，没有字段。由其递归子定义的函数无法区分 $a = b$ 的两个证明，因为构造任何这样的证明只有一种方式。`Or` 有两个构造子，所以它到 $\Nat$ 的递归子可以对两个注入返回不同的数，使程序的值依赖于提供的是哪个证明。第 8 章精确地给出了这条规则。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- $\Eq{}$ 是归纳族，参数为 $A$ 和 $a$，索引为 $b$，只有一个没有字段的构造子 $\refl{}$。
- 它的递归子沿着 $a = b$ 的证明把关于 $a$ 的事实传输为关于 $b$ 的事实，而在 $\refl{}$ 上什么也不做。这就是重写。
- 定义相等由计算判定；命题相等是一个类型，其证明可能需要归纳。$\refl{}$ 把前者变成后者。
- $n + 0 = n$ 是定义相等，$0 + n = n$ 不是，因为加法对第二个参数递归。

</div>
