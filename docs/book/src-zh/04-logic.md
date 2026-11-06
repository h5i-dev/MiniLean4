<div class="lead" markdown="1">

第 3 章给出了八条类型规则，并承诺它们是逻辑规则。本章兑现这个承诺。它选定一种具体的逻辑，把其中的公式翻译成类型，并说明该逻辑中的每个证明都变成一个内核接受的项。随后它指出内核要想被信任，首先必须具备的性质：一致性。

</div>

## 用来对照的逻辑

这种逻辑的公式由命题变量 $P, Q, \ldots$ 经蕴含和对命题的量化构成：

$$
\varphi, \psi \;::=\; P \;\mid\; \varphi \to \psi \;\mid\; \forall P.\,\varphi
$$

这是**二阶命题逻辑**（second-order propositional logic）：之所以叫“二阶”，是因为 $\forall$ 的取值范围是命题而非个体。它很小，却远非平凡。合取、析取、否定和假都可以在其中定义，例如 $\bot = \forall P.\,P$ 和 $\varphi \wedge \psi = \forall R.\,(\varphi \to \psi \to R) \to R$。

这种逻辑中的证明是判断 $\Delta \vdash \varphi$ 的自然演绎推导，其中 $\Delta$ 是假设列表。规则就是下面图 4.1 左栏列出的那些：使用假设，引入和消去蕴含，引入和消去量词。

## 把公式翻译成类型

每个公式翻译成一个类型，写作 $\varphi^\ast$：

$$
P^\ast = P,
\qquad
(\varphi \to \psi)^\ast = \varphi^\ast \to \psi^\ast,
\qquad
(\forall P.\,\varphi)^\ast = \tPi{P}{\Sort{0}}{\varphi^\ast}.
$$

命题变量变成类型变量，蕴含变成函数类型，对命题的量化变成在 $\Sort{0}$ 上的 $\Pi$ 类型。

假设列表翻译成上下文。除了每条假设对应一条 $h_i : \varphi_i^\ast$ 之外，上下文还必须声明判断中任何位置出现的命题变量：

$$
(\varphi_1, \ldots, \varphi_n)^\ast
\;=\;
P_1 : \Sort{0}, \ldots, P_k : \Sort{0},\;
h_1 : \varphi_1^\ast, \ldots, h_n : \varphi_n^\ast,
$$

其中 $P_1, \ldots, P_k$ 是在被翻译的判断 $\Delta \vdash \varphi$ 中，于 $\Delta$ 或结论 $\varphi$ 里自由出现的命题变量，$h_1, \ldots, h_n$ 是新鲜的名字。结论必须计入，因为变量可能只出现在那里，比如 $\cdot \vdash P \to P$ 中的 $P$。

图 4.1 把每条逻辑规则与实现它的类型规则并排放置。仅用于检查类型良构的前提已省略。

<div class="rulebox" markdown="1">

<p class="caption">图 4.1. 自然演绎（中栏）与实现它的类型规则（右栏）。每一行中，$\Delta^\ast$ 是结论的上下文。</p>

$$
\begin{array}{lcc}
\text{Hypothesis} &
\dfrac{\varphi_i \in \Delta}{\Delta \vdash \varphi_i} &
\dfrac{(h_i : \varphi_i^\ast) \in \Delta^\ast}{\Delta^\ast \vdash h_i : \varphi_i^\ast}\rulename{T-Var}
\\[18pt]
\to\text{-intro} &
\dfrac{\Delta, \varphi \vdash \psi}{\Delta \vdash \varphi \to \psi} &
\dfrac{\Delta^\ast, h : \varphi^\ast \vdash t : \psi^\ast}{\Delta^\ast \vdash \tLam{h}{\varphi^\ast}{t} : \varphi^\ast \to \psi^\ast}\rulename{T-Lam}
\\[18pt]
\to\text{-elim} &
\dfrac{\Delta \vdash \varphi \to \psi \qquad \Delta \vdash \varphi}{\Delta \vdash \psi} &
\dfrac{\Delta^\ast \vdash f : \varphi^\ast \to \psi^\ast \qquad \Delta^\ast \vdash a : \varphi^\ast}{\Delta^\ast \vdash f\;a : \psi^\ast}\rulename{T-App}
\\[18pt]
\forall\text{-intro} &
\dfrac{\Delta \vdash \varphi \qquad P \notin \FV(\Delta)}{\Delta \vdash \forall P.\,\varphi} &
\dfrac{\Delta^\ast, P : \Sort{0} \vdash t : \varphi^\ast}{\Delta^\ast \vdash \tLam{P}{\Sort{0}}{t} : \tPi{P}{\Sort{0}}{\varphi^\ast}}\rulename{T-Lam}
\\[18pt]
\forall\text{-elim} &
\dfrac{\Delta \vdash \forall P.\,\varphi}{\Delta \vdash \subst{\varphi}{P}{\psi}} &
\dfrac{\Delta^\ast \vdash f : \tPi{P}{\Sort{0}}{\varphi^\ast} \qquad \Delta^\ast \vdash \psi^\ast : \Sort{0}}{\Delta^\ast \vdash f\;\psi^\ast : \subst{\varphi^\ast}{P}{\psi^\ast}}\rulename{T-App}
\end{array}
$$

</div>

把右栏中的项抹去，就恰好得到中栏。有两处细节值得说明。

在 $\forall$-intro 一行，逻辑的附加条件 $P \notin \FV(\Delta)$ 保证没有假设提到 $P$，所以类型规则可以把 $P : \Sort{0}$ 加在假设*之后*，而不破坏上下文的依赖顺序。

在 $\forall$-elim 一行，前提 $\psi^\ast : \Sort{0}$ 对*每个*公式 $\psi$ 都成立，哪怕是含有 $\forall$ 的公式，因为 T-Pi 把每个翻译后的公式都放进 $\Sort{0}$。（这归功于 T-Pi 中的 $\imax$：$\tPi{P}{\Sort{0}}{\varphi^\ast}$ 落在 $\Sort{\imax(1, 0)} = \Sort{0}$ 中。）所以全称陈述可以用任何公式实例化，正如在逻辑中一样。[第 13 章](13-universes.md)会回到这一点，它叫做非谓词性（impredicativity）。

## 证明即项

<div class="theorem" markdown="1">

**定理 4.1（证明即项）。**若 $\Delta \vdash \varphi$ 在逻辑中可证，则存在某个项 $t$ 使得 $\Delta^\ast \vdash t : \varphi^\ast$。

</div>

图 4.1 把逻辑证明的每一步变成类型推导的一步，于是对证明做归纳，每个证明都变成一个项。[附录 A](a-proof-pat.md)在明确命题变量作用域的前提下陈述该定理，并给出完整证明。

这条定理说明类型检查器能检查该逻辑的每个证明。要让内核*值得信任*，我们还需要反方向的保证：对于逻辑所否定的命题，它绝不能接受任何项。

## 一致性

定义 $\bot = \forall P.\,P$，即“一切都成立”。逻辑中不存在 $\bot$ 的证明：若把每个命题变量读作真或假，每条规则在任何读法下都保持真，而在使某个 $P$ 为假的读法下 $\forall P.\,P$ 为假。

类型论应当与此一致。也就是说，不应有任何闭项具有类型

$$
\bot^\ast \;=\; \tPi{P}{\Sort{0}}{P}.
$$

具有这个类型的闭项 $t$ 将是一场灾难：对每个命题 $C : \Sort{0}$，应用 $t\;C$ 都具有类型 $C$，于是每个命题都可证，内核就一文不值了。

<div class="definition" markdown="1">

**定义 4.2（一致性）。**一个类型系统是*一致的*，如果没有闭项具有类型 $\tPi{P}{\Sort{0}}{P}$。

</div>

一致性是本书中每个设计决策都必须保持的性质。特别地，一种宇宙设计只有在系统仍然一致时才可接受；[第 13 章](13-universes.md)展示一个看似自然却通不过这个检验的设计，[第 14 章](14-properties.md)则把我们系统的一致性陈述为定理 14.5。

<aside class="note" markdown="1">

人们或许期望定理 4.1 的完整逆命题：每个类型为 $\varphi^\ast$ 的项都来自 $\varphi$ 的某个证明。这个更强的性质叫做*保守性*（conservativity），在这里更难建立，因为 $\Sort{0}$ 还包含一些并非公式翻译的类型，比如 $\tPi{F}{\Sort{0} \to \Sort{0}}{F\;P \to F\;P}$，而一个项在通往 $\varphi^\ast$ 的途中可能经过它们。我们不需要保守性。没有一致性，内核的“是”毫无意义；有了它，这个“是”就足够了。

</aside>

<aside class="intuition" markdown="1">

为什么单单挑出 $\tPi{P}{\Sort{0}}{P}$，而不是比如 $0 = 1$？因为它是一张万能假钞：它的任何证明只需一次应用，就能换成其他任何命题的证明。如果别的某个荒谬陈述有证明，那个证明同样可以用来构造 $\tPi{P}{\Sort{0}}{P}$ 的证明，所以排除这一个类型就排除了全部。

</aside>

## 练习

<div class="exercise" markdown="1">

把公式 $\forall P.\,\forall Q.\,(P \to Q) \to P \to Q$ 翻译成类型，并写出图 4.1 为自然演绎证明“假设 $P \to Q$ 和 $P$；把前者应用于后者”所产生的证明项。

<details markdown="1">
<summary>解答</summary>

该类型是 $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{(P \to Q) \to P \to Q}}$。两次 $\forall$-intro 给出外层两个在 $\Sort{0}$ 上的 $\lambda$，两次 $\to$-intro 给出 $\lambda(f : P \to Q)$ 和 $\lambda(p : P)$，$\to$-elim 给出函数体 $f\;p$：
$\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{f}{P \to Q}{\tLam{p}{P}{f\;p}}}}$。

</details>

</div>

<div class="exercise" markdown="1">

证明：由 $t : \tPi{P}{\Sort{0}}{P}$ 可以构造出类型为 $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q}}$ 的项，即“每个命题都蕴含其他每个命题”。

<details markdown="1">
<summary>解答</summary>

$\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{t\;Q}}}$。假设 $p$ 被忽略，而由 T-App 得 $t\;Q : Q$。$\bot^\ast$ 的证明能证明一切，说的就是这个意思。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 二阶命题逻辑可以翻译进类型论：$\to$ 变成函数类型，$\forall P$ 变成 $\Pi(P : \Sort{0})$，假设变成上下文条目。
- 定理 4.1：逻辑中的每个证明都变成一个良类型的项。翻译是逐条规则进行的（图 4.1）。
- 内核只有在一致时才值得信任：不存在类型为 $\tPi{P}{\Sort{0}}{P}$ 的闭项。
- 借助 $\imax$ 实现的非谓词性，让全称陈述可以用任何公式实例化，包括它自身。

</div>