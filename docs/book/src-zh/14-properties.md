<div class="lead" markdown="1">

前面各章对内核提出了两类断言：它的算法会终止；它永远不会接受 False 的证明。这两点都依赖于关于类型系统的定理，而这些定理远比内核本身所做的事情困难。本章陈述这些定理，说明每一条能带来什么，并概述一致性如何由它们导出。一致性的完整证明见附录 D。

</div>

## 核心系统

下面的定理针对的是*核心*系统：图 3.1 的规则，加上[第 13 章](13-universes.md)的宇宙，不含第二部分的常量。按 Barendregt 的说法，这是一个**纯类型系统**（Pure Type System）：构造演算（Calculus of Constructions）[Coquand 1988]，在其非谓词的 $\Sort{0}$ 之上加一层谓词宇宙的层级，接近 Luo 的扩展构造演算（Extended Calculus of Constructions）[Luo 1990]。前三条性质对每个函数式纯类型系统都成立 [Barendregt 1992]。在存在非谓词性的情况下，强规范化要困难得多，需要 Girard 的可归约性候选（reducibility candidates）方法 [Girard 1972; Coquand 1988; Luo 1990]。本章末尾说明加入归纳类型后会有什么变化。

## 四条性质

<div class="theorem" markdown="1">

**定理 14.1（类型唯一性）.** 若 $\Gamma \vdash t : A$ 且 $\Gamma \vdash t : B$，则 $A \conv B$。

</div>

一个项在转换意义下只有一个类型。$\Infer$ 依赖这一点：它要计算的答案只有一个，$\Check$ 可以放心地与之比较，不必担心另一棵推导会给出某个不可转换的不同类型。

<div class="theorem" markdown="1">

**定理 14.2（类型正确性）.** 若 $\Gamma \vdash t : A$，则或者对某个 $u$ 有 $A = \Sort{u}$，或者对某个 $u$ 有 $\Gamma \vdash A : \Sort{u}$。

</div>

良类型项的类型本身也是一个类型（或者是一个宇宙；宇宙按 T-Sort 也有类型，只是不必写成那种形式）。因此 $\Infer$ 的结果总能再交给 $\InferSort$，算法构造的上下文也始终保持良构。

<div class="theorem" markdown="1">

**定理 14.3（主体归约）.** 若 $\Gamma \vdash t : A$ 且 $t \betared t'$，则 $\Gamma \vdash t' : A$。

</div>

计算保持类型。正是它为 T-Conv 以及“通过规范化判定相等”这一整套策略提供了依据：归约一个项永远不会使它离开自己的类型，所以比较范式，比较的正是该比较的东西。

<div class="theorem" markdown="1">

**定理 14.4（强规范化）.** 若 $\Gamma \vdash t : A$，则从 $t$ 出发的每一个 β 归约序列都是有限的。

</div>

每个良类型项都能到达范式，无论按什么顺序归约。这是最深刻的一条。$\Whnf$、$\Normalize$，从而 $\IsDefEq$ 和 $\Infer$，在良类型输入上终止都是因为它；下一节还会说明，一致性同样建立在它之上。

四条性质按一种确定的模式支撑着两项保证，如下图所示：箭头读作“为……所需”。

<div class="rulebox" markdown="1">

<p class="caption">图 14.1. 元理论各部分如何衔接。</p>

<svg class="dep-diagram" viewBox="0 0 760 300" role="img" aria-label="Dependency diagram: uniqueness of types and type correctness support the algorithm; subject reduction and strong normalization support both decidability and consistency; the normal-form analysis joins strong normalization for consistency.">
<defs><marker id="arr" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0L10 5L0 10z" fill="currentColor"/></marker></defs>
<g class="dep-box"><rect x="20" y="20" width="160" height="54" rx="8"/><text x="100" y="42" text-anchor="middle">类型</text><text x="100" y="60" text-anchor="middle">唯一性 (14.1)</text></g>
<g class="dep-box"><rect x="200" y="20" width="160" height="54" rx="8"/><text x="280" y="42" text-anchor="middle">类型</text><text x="280" y="60" text-anchor="middle">正确性 (14.2)</text></g>
<g class="dep-box"><rect x="400" y="20" width="160" height="54" rx="8"/><text x="480" y="42" text-anchor="middle">主体</text><text x="480" y="60" text-anchor="middle">归约 (14.3)</text></g>
<g class="dep-box hot"><rect x="580" y="20" width="160" height="54" rx="8"/><text x="660" y="42" text-anchor="middle">强</text><text x="660" y="60" text-anchor="middle">规范化 (14.4)</text></g>
<g class="dep-box"><rect x="110" y="140" width="180" height="54" rx="8"/><text x="200" y="162" text-anchor="middle">Infer 与 Check</text><text x="200" y="180" text-anchor="middle">良定义（第 5 章）</text></g>
<g class="dep-box"><rect x="470" y="140" width="180" height="54" rx="8"/><text x="560" y="162" text-anchor="middle">范式</text><text x="560" y="180" text-anchor="middle">分析（附录 D）</text></g>
<g class="dep-box goal"><rect x="110" y="236" width="180" height="48" rx="8"/><text x="200" y="265" text-anchor="middle">可判定性</text></g>
<g class="dep-box goal"><rect x="470" y="236" width="180" height="48" rx="8"/><text x="560" y="265" text-anchor="middle">一致性 (14.5)</text></g>
<g class="dep-arrows">
<path d="M100 74 L170 140"/><path d="M280 74 L230 140"/>
<path d="M480 74 L300 150"/><path d="M660 74 L300 160"/>
<path d="M480 74 L540 140"/><path d="M660 74 L580 140"/>
<path d="M200 194 L200 236"/><path d="M560 194 L560 236"/>
<path d="M660 74 L620 236"/>
</g>
</svg>

</div>

这些性质合起来，给出了我们对一个内核所要求的两项保证。

- **可判定性.** 算法 5.1 在每个输入上都终止，所以一个证明是否正确总能被判定。
- **一致性.** 没有封闭项能证明 False。

<aside class="note" markdown="1">

强规范化只对良类型项成立。内核可能收到非良类型的项，而且在类型确立之前，推断过程中就会调用 $\Whnf$。这就是实现中设有步数预算的原因：对于定理未覆盖的输入，它是定理的工程替代品。

</aside>

## 一致性

<div class="theorem" markdown="1">

**定理 14.5（一致性）.** 不存在封闭项 $t$ 使得 $\cdot \vdash t : \tPi{P}{\Sort{0}}{P}$。

</div>

论证分两半，不看细节也能看出它的轮廓。

**归结到范式.** 由强规范化，这样的项 $t$ 会有范式 $n$；由主体归约，$n$ 的类型不变。因此只需证明：没有任何处于*范式*的封闭项具有类型 $\tPi{P}{\Sort{0}}{P}$。全部困难都在这一步，因为它用到了定理 14.4。

**分析范式.** 范式项要么是宇宙、$\Pi$、$\lambda$，要么是一个变量作用于若干参数（称为*中性*项，neutral term）。类型为 $\Pi$ 的封闭范式项必定是 $\lambda$：它不可能是中性项，因为作用域内没有任何变量；而宇宙和 $\Pi$ 类型的类型是宇宙，不是 $\Pi$。于是 $n = \tLam{P}{\Sort{0}}{s}$，其中 $P : \Sort{0} \vdash s : P$ 且 $s$ 是范式。现在问 $s$ 能是什么。宇宙、$\Pi$ 或 $\lambda$ 的类型会是宇宙或 $\Pi$，而不是变量 $P$。中性项必须以作用域内的某个变量开头，而作用域内只有 $P$ 本身，其类型是 $\Sort{0}$：这个类型不是 $P$，所以 $s$ 不能是 $P$；它也不是函数类型，所以 $P$ 不能作用于任何东西。每种情形都不可能。

[附录 D](d-proof-consistency.md) 严格地完成这一论证，包括上述情形分析默默用到的关于类型和转换的标准事实（生成引理、合流性、替换）。

<aside class="intuition" markdown="1">

用一句话说：要证明 $\tPi{P}{\Sort{0}}{P}$，你必须在除了名字 $P$ 之外一无所有的情况下，给出*任意*命题 $P$ 的证明。范式把“一无所有”变成了字面意义：范式证明无法藏起一段能凭空变出东西的计算，只能直接用作用域内的材料搭建，而作用域内没有任何东西的类型是 $P$。强规范化保证的正是：每个证明都*可以*化成这种老实的形式。

</aside>

## 加入归纳类型之后

第二部分的 ι 规则彼此不重叠，也不与 β 重叠，所以归约仍然合流。主体归约、强规范化和一致性对归纳构造演算（Calculus of Inductive Constructions）都是已知结果 [Werner 1994]，而我们带归纳类型的系统只是它的一个小片段。上面的简短一致性论证本身已不再够用，因为范式现在还包括卡住的递归子应用，例如 $n$ 为变量时的 $\NatRec{0}\;M\;z\;s\;n$；一致性仍由强规范化导出，但需要对范式做更细致的分析，其中中性项也可以以常量为头部。

[第 8 章](08-inductive-recipe.md)的每一条接受条件都对应这一分析可能失败的一种方式：没有正性，ι 归约可能循环，强规范化就丢失了；没有宇宙条件，一个类型可以包含自己所在的宇宙，第 13 章的悖论就会卷土重来；没有对命题的消去限制，证明无关性（Lean 假定它成立）就会被推翻。

Lean 的完整理论带有定义性证明无关性、宇宙多态、商类型以及一般的嵌套归纳类型和互归纳类型，其元理论更为微妙；Carneiro 的论文 [Carneiro 2019] 是这方面的参考文献。但核心结构是一样的：强规范化加上范式分析。

<aside class="lean" markdown="1">

Lean 的内核和我们的一样，并不*证明*这些结论，而是假定它们成立。这些定理是关于类型系统的，不是关于代码的；它们针对设计好的系统，在纸上一次性建立。代码要做的，是忠实地实现那个系统。本书这个紧凑的内核，以及图 3.1、第 8 章和算法 12.1 中对它更紧凑的描述，正是让人类读者能够核对“忠实”二字的东西。

</aside>

## 练习

<div class="exercise" markdown="1">

按第 13 章的说法，带有 $\mathsf{Type} : \mathsf{Type}$ 的内核会失去四条性质中的哪几条？

<details markdown="1">
<summary>解答</summary>

强规范化（Hurkens 的项没有范式）和一致性（它的类型是 $\tPi{P}{\mathsf{Type}}{P}$）。类型唯一性和主体归约仍然成立；它们是规则形状的性质，与宇宙结构无关。

</details>

</div>

<div class="exercise" markdown="1">

一致性论证说，类型为 $\Pi$ 的封闭范式项必定是 $\lambda$。加入常量后这一点为何不再成立？取而代之的是什么？

<details markdown="1">
<summary>解答</summary>

像 $\suc$ 或 $\NatRec{0}$ 这样的常量是封闭的，而且可以作为范式项的头部，所以类型为 $\Pi$ 的封闭范式项可以是 $\suc$ 本身，也可以是卡住的递归子应用。分析因此还要考虑以常量为头部的中性项，并利用模式赋予构造子和递归子的具体类型，证明它们都不能具有类型 $\tPi{P}{\Sort{0}}{P}$。Werner 的论文对归纳构造演算完成了这项工作。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 类型唯一性和类型正确性使 $\Infer$ 良定义；主体归约为通过规范化判定相等提供依据；强规范化使一切终止。
- 一致性由强规范化加上对范式的情形分析得出：作用域内没有任何东西能证明任意的 $P$。
- 只要接受条件成立，归纳类型保持全部四条性质；每条条件各自阻止一种特定的失败。
- 内核假定这些定理，而不证明它们。它的职责是忠实、清晰地实现这些定理所描述的系统。

</div>
