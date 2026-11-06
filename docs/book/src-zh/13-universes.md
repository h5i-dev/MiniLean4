<div class="lead" markdown="1">

第 4 章说明了类型规则实现了一种逻辑，而只有当这个系统一致时它才可以接受。本章要回答一个从第 2 章起就一直搁置的问题：$\Sort{0}$ 的类型是什么？最简单的答案是一个包含自身的单一宇宙，它会使系统不一致。Lean 的答案是一个层级 $\Sort{0} : \Sort{1} : \Sort{2} : \cdots$，底层宇宙是非谓词的，这样就不会不一致。本章还会顺带解释 T-Pi 中唯一看起来古怪的部分：函数 $\imax$。

</div>

## Sort 0 的类型是什么？

命题变量在类型论中以假设 $P : \Sort{0}$ 的形式出现，它可以出现在两个地方：在上下文中，如下面左边的判断；或被 $\lambda$ 或 $\Pi$ 绑定，如右边的判断：

$$
P : \Sort{0} \vdash \tLam{h}{P}{h} : P \to P
\qquad\text{versus}\qquad
\vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{P \to P}.
$$

左边的判断对一个由外部提供的固定 $P$ 证明了 $P \to P$，而右边的是一个封闭项，它对*每一个* $P$ 都证明了这一点，并且之后可以应用到任何具体的命题上；图 4.1 中的 $\forall$ 各行需要的正是这个。

两种形式都要求 $\Sort{0}$ 是一个类型。把 $P : \Sort{0}$ 加入上下文的 C-Ext，以及绑定 $P : \Sort{0}$ 的 T-Lam 和 T-Pi，都对新变量的类型 $A$ 有前提 $\Gamma \vdash A : \Sort{u}$。当 $A = \Sort{0}$ 时，这个前提就是对某个 $u$ 有 $\Gamma \vdash \Sort{0} : \Sort{u}$：命题宇宙本身必须有一个类型。问题是，是哪一个。

## Type 不是 Type

假设我们把所有宇宙换成一个包含自身的单一宇宙 $\mathsf{Type}$：

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \mathsf{Type} : \mathsf{Type}}
\qquad
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \tPi{x}{A}{B} : \mathsf{Type}}
$$

把 $\forall P.\,\varphi$ 翻译为 $\tPi{P}{\mathsf{Type}}{\varphi^\ast}$。于是 $P$ 的取值范围是一个包含 $\mathsf{Type}$ 自身以及由它构造出的每个类型的集合体。这样的集合体是“所有集合的集合”在类型论中的对应物，而朴素集合论已经表明，这类集合体会导出矛盾。最著名的例子是**罗素悖论**（Russell's paradox）：令 $R = \{\, x \mid x \notin x \,\}$，则 $R \in R$ 和 $R \notin R$ 都导出矛盾。

类型论没有 $x \notin x$ 这样的成员关系测试，所以罗素的论证不能逐字搬过来。Girard 改而改编了一个相关的悖论，即 Burali-Forti 关于所有良序的集合体的悖论 [Girard 1972]，Hurkens 随后简化了由此得到的项 [Hurkens 1995]。结果是一个封闭项 $t_{\mathrm{H}}$，满足

$$
\vdash t_{\mathrm{H}} : \tPi{P}{\mathsf{Type}}{P},
$$

因此系统不一致：$\bot$ 没有证明，$\bot^\ast$ 却有一个项，于是建立在这些规则之上的内核会接受每个陈述的证明。关键的要素是一个类型 $U$，它对整个 $\mathsf{Type}$ 进行量化，同时又是 $\mathsf{Type}$ 的成员，这使得 $U$ 可以包含自身二重幂集的一个副本，而这是任何集合都做不到的。[附录 C](c-hurkens.md) 完整给出 $t_{\mathrm{H}}$，解释它的工作原理，并展示如何只改动内核的一行代码来重现这个结果。

损害同样波及算法：类型保持性仍然成立，所以如果 $t_{\mathrm{H}}$ 有范式，它就会是类型为 $\tPi{p}{\mathsf{Type}}{p}$ 的一个处于范式的封闭项。[附录 D](d-proof-consistency.md) 中一致性证明里分析范式项的那一部分不用强规范化，可以搬到 $\mathsf{Type} : \mathsf{Type}$ 上；它表明这样的范式项不存在。因此 $t_{\mathrm{H}}$ 没有范式，强规范化失效，$\Normalize$ 在它上面永远运行下去。带有 $\mathsf{Type} : \mathsf{Type}$ 的内核不仅不可靠，而且在某些输入上不终止。

<aside class="history" markdown="1">

Martin-Löf 1971 年的第一个类型论就有这条规则，第二年 Girard 悖论就针对它被发现了。此后的每一种依赖类型论都要么有一个宇宙层级，要么有某种别的装置来打破自指。这个悖论不是猎奇：自含的宇宙是*显而易见*的设计，而显而易见的设计是错的。

</aside>

## 底层非谓词的层级

第二种答案是：$\Sort{0}$ 住在一个更大的宇宙里，后者又住在一个更大的宇宙里：

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
\qquad\text{so}\qquad
\Sort{0} : \Sort{1} : \Sort{2} : \cdots.
$$

没有宇宙包含自身。$\Pi$ 类型从一个宇宙取参数，在另一个宇宙中返回类型，所以 T-Pi 还必须说明 $\Pi$ 类型本身属于哪个宇宙；Lean 的答案使用函数 $\imax$：

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash B : \Sort{v}}{\Gamma \vdash \tPi{x}{A}{B} : \Sort{\imax(u, v)}}\rulename{T-Pi}
\qquad
\imax(u, v) =
\begin{cases}
0 & \text{if } v = 0, \\
\max(u, v) & \text{otherwise.}
\end{cases}
$$

$\imax$ 中的分情形使得 $\Pi$ 类型在函数体是命题时是*非谓词的*（impredicative），否则是*谓词的*（predicative）。在下面选择 $A$ 和 $B$ 的宇宙，观察 $\Pi$ 类型落在哪里。

<div class="explorer" data-kind="universes"></div>

**命题是非谓词的。** 如果函数体 $B$ 是命题（$v = 0$），那么无论它对什么进行量化，整个 $\Pi$ 都是命题。特别地，$(\forall P.\,\varphi)^\ast = \tPi{P}{\Sort{0}}{\varphi^\ast}$ 属于 $\Sort{0}$，尽管它对整个 $\Sort{0}$ 进行量化。包含对自身进行量化的类型的宇宙称为**非谓词的**（impredicative）。因为每个翻译后的公式都在 $\Sort{0}$ 中，$\forall$-elim 的前提 $\psi^\ast : \Sort{0}$ 总是成立，所以全称陈述可以用任何命题实例化，甚至用它自己。例如，令 $\mathit{id} = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$，则

$$
\mathit{id} : \tPi{P}{\Sort{0}}{P \to P}
\qquad\text{and}\qquad
\tPi{P}{\Sort{0}}{P \to P} : \Sort{0},
$$

所以 $\mathit{id}\;(\tPi{P}{\Sort{0}}{P \to P})\;\mathit{id}$ 是良类型的，其类型为 $\tPi{P}{\Sort{0}}{P \to P}$。同一情形也使 $\forall n : \Nat,\, n + 0 = n$ 成为命题，尽管 $\Nat$ 住在 $\Sort{1}$ 中；[第 7 章](07-inductive-nat.md)的归纳正是依赖于此。

<div class="playground" data-file="impredicative"><pre># “每个命题都蕴涵自身”本身就是一个命题，
# 所以它可以用自己来实例化。
def id : forall (P : Sort 0), P -> P := fun (P : Sort 0) => fun (h : P) => h
def self : forall (P : Sort 0), P -> P := id (forall (P : Sort 0), P -> P) id

# 高一层的类似陈述却不是自己的实例：
# forall (A : Sort 1), A -> A 住在 Sort 2 中，而不是 Sort 1。
def idT : forall (A : Sort 1), A -> A := fun (A : Sort 1) => fun (a : A) => a
def selfT : forall (A : Sort 1), A -> A := idT (forall (A : Sort 1), A -> A) idT</pre></div>

**类型是谓词的。** 如果函数体不是命题（$v \ge 1$），$\Pi$ 就住在两个宇宙中较大的那个里。于是，对 $\Sort{u}$ 进行量化的类型住在 $\Sort{(\max(u+1, v))}$ 中，它永远不会是 $\Sort{u}$：

$$
\dfrac{
  \dfrac{}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
  \qquad
  \Gamma, x : \Sort{u} \vdash B : \Sort{v}
}{\Gamma \vdash \tPi{x}{\Sort{u}}{B} : \Sort{(\max(u+1, v))}}\rulename{T-Pi}
$$

这个性质称为**谓词性**（predicativity）。例如，类型上的恒等函数 $\tLam{A}{\Sort{1}}{\tLam{a}{A}{a}}$ 的类型是 $\tPi{A}{\Sort{1}}{A \to A}$，它住在 $\Sort{2}$ 中，所以不能应用到自己的类型上；而 $\Sort{2}$ 处的一个副本可以。每一层都容纳它下面的那一层；实践中几层就够了，更高的层级只在对大的集合体进行量化时出现，比如所有小范畴构成的范畴。

**为什么这是安全的。** 非谓词性看起来像上一节所警告的自指，但它被限制住了：$\Sort{0}$ 包含对 $\Sort{0}$ 进行量化的类型，但 $\Sort{0}$ 不是自身的成员。Coquand 证明了底层的一个非谓词宇宙是一致的 [Coquand 1988]，而一旦有*两*层是非谓词的，Girard 悖论就已经可以推导出来 [Hurkens 1995]。采用这些规则，系统是一致的且强规范化的（[第 14 章](14-properties.md)）。

<aside class="intuition" markdown="1">

为什么命题可以是非谓词的，而类型不可以？命题的证明不携带程序可提取的数据，第 8 章的消去限制也确保了这一点。对所有命题量化后定义一个命题，类似于用涉及所有集合的性质定义集合：如果结果也在量词的范围内，而且可以检查其内容，就会出问题；若只能把它当作假设使用，同样的问题便不会出现。悖论需要*检查*它构造出的对象，但命题的证明不允许这种操作。

</aside>

## 与 Lean 的比较

在 Lean [de Moura and Ullrich 2021] 中，$\Sort{0}$ 是 `Prop`，$\Sort{(u+1)}$ 是 `Type u`，$\Pi$ 类型的宇宙按上面的 $\imax$ 指派。还有两处差别。

第一，Lean 的 `Prop` 具有**定义性证明无关性**（definitional proof irrelevance）：同一个命题的任意两个证明在定义上相等。我们的转换不把证明视为相同；加上这一点会让转换依赖于类型，于是[第 12 章](12-reduction-conversion.md)那种简单的“规范化后比较”检查就不再够用。

第二，Lean 有**宇宙多态**（universe polymorphism），所以定义可以对所有层级 $u$ 一次性陈述，$\imax$ 此时也要对层级*变量*起作用，诸如 $\imax(u, v) \le w$ 这样的约束要符号化求解，而在我们的系统中，每个层级都是一个具体的数。

下表总结了设计空间。

| 设计 | 量化范围 | 缺点 |
|---|---|---|
| 没有宇宙 | 只有值 | 无法说“对每个命题” |
| $\mathsf{Type} : \mathsf{Type}$ | 一切 | 不一致 |
| 两个 sort $\ast : \square$ | 只有 $\ast$ | $\square$ 本身没有类型 |
| $\Sort{u} : \Sort{(u+1)}$ 配 $\max$ | 任意层级 | 对命题的 $\forall$ 不是命题 |
| $\Sort{u} : \Sort{(u+1)}$ 配 $\imax$（Lean） | 任意层级 | 规范化更难证明 |

<aside class="code" markdown="1">

本章的全部内容就是 `src/typecheck.rs` 中 `infer` 的两行：`Sort(u)` 情形返回 `Sort(u + 1)`；`Pi` 情形在函数体的层级为 `0` 时返回 `Sort(0)`，否则返回最大值。[附录 C](c-hurkens.md) 展示了把第一行改成返回 `Sort(u)` 后，内核就会接受 Hurkens 的项。

</aside>

## 练习

<div class="exercise" markdown="1">

计算 $\tPi{A}{\Sort{1}}{\tPi{P}{A \to \Sort{0}}{\tPi{a}{A}{P\;a}}}$ 的宇宙。这个陈述说的是“每个类型上的每个谓词处处成立”（它是假的，但是良构的）。

<details markdown="1">
<summary>解答</summary>

最内层：$P\;a : \Sort{0}$，所以 $\tPi{a}{A}{P\;a} : \Sort{\imax(1, 0)} = \Sort{0}$。接着，$A \to \Sort{0}$ 的宇宙是 $\imax(1, 1) = 1$（它的函数体 $\Sort{0}$ 的类型是 $\Sort{1}$），所以中间的 $\Pi$ 的宇宙是 $\imax(1, 0) = 0$。最后，$\Sort{1} : \Sort{2}$ 而函数体在 $\Sort{0}$ 中，得到 $\imax(2, 0) = 0$，整个陈述是一个命题；如果用 $\max$ 代替 $\imax$，它会落在 $\Sort{2}$ 中。

</details>

</div>

<div class="exercise" markdown="1">

说明演练场中的 `selfT` 定义为什么被拒绝，指出所涉及的规则和两个宇宙。

<details markdown="1">
<summary>解答</summary>

`idT` 期望一个参数 $A : \Sort{1}$，而实际提供的参数是 $\tPi{A}{\Sort{1}}{A \to A}$，按 T-Pi 它的宇宙是 $\max(2, 1) = 2$，于是 $\Check$ 比较 $\Sort{2}$ 与 $\Sort{1}$ 并失败：内核在该应用处报告类型不匹配。这就是谓词性：对 $\Sort{1}$ 进行量化的类型不在 $\Sort{1}$ 中。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- $\Sort{0}$ 需要一个类型，因为命题变量会被 $\lambda$ 和 $\Pi$ 绑定。
- 包含自身的宇宙是不一致的（Girard，Hurkens），并且破坏规范化。
- 层级 $\Sort{u} : \Sort{(u+1)}$ 避免了自含；$\imax$ 使命题成为非谓词的，其余一切成为谓词的。
- 底层的一个非谓词宇宙是安全的，两个则不然。Lean 在同样的设计之上又加了证明无关性和宇宙多态。

</div>
