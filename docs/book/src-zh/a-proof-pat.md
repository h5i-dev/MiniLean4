<div class="lead" markdown="1">

[第 4 章](04-logic.md)断言，二阶命题逻辑中的每个证明都可以变成一个被内核接受的项（定理 4.1）。本附录把这一陈述精确化，并给出完整证明。一旦必要的簿记就位，证明并不长：它是对逻辑判断的推导做归纳，每种情形正好对应第 4 章表格中的一行，从左读到右。

</div>

## 思路

逻辑中的一棵推导是规则应用构成的树，而第 4 章的翻译把每条逻辑规则与一条类型规则配对，于是自然的计划是：从叶子向上遍历推导，在每个节点上构造配对的类型规则所给出的类型推导。假设变成变量查找，蕴涵引入变成 $\lambda$，蕴涵消去变成应用，两条量词规则则变成在 $\Sort{0}$ 上的 $\lambda$ 和对类型的应用。

有两处细节需要留意，都和上下文有关。

- 逻辑规则不说明哪些命题变量在作用域内，而类型这一侧需要知道，因为命题变量 $P$ 只有在假设 $P : \Sort{0}$ 进入上下文之后才能使用。因此精确陈述带有一个显式的命题变量列表 $\Theta$。
- 类型规则向右扩展上下文，而第 4 章的翻译 $\Delta^\ast$ 把所有命题变量放在所有假设之前。若允许任意交错，证明会更容易，所以我们对每个*表示*该逻辑判断的上下文证明定理，“表示”的含义见下文定义。

## 精确陈述

定理 4.1 没有明说哪些命题变量在作用域内；为了证明，我们把它们显式写出，记

$$
\Theta; \Delta \vdash \varphi,
$$

其中 $\Theta$ 是互不相同的命题变量的列表，并且在 $\Delta$ 或 $\varphi$ 中自由出现的每个命题变量都属于 $\Theta$。带上这套簿记，第 4 章的规则读作如下。

$$
\dfrac{\varphi \in \Delta}{\Theta; \Delta \vdash \varphi}\rulename{Hyp}
\qquad
\dfrac{\Theta; \Delta, \varphi \vdash \psi}{\Theta; \Delta \vdash \varphi \to \psi}\rulename{$\to$-intro}
\qquad
\dfrac{\Theta; \Delta \vdash \varphi \to \psi \qquad \Theta; \Delta \vdash \varphi}{\Theta; \Delta \vdash \psi}\rulename{$\to$-elim}
$$

$$
\dfrac{\Theta, P; \Delta \vdash \varphi \qquad P \notin \Theta}{\Theta; \Delta \vdash \forall P.\,\varphi}\rulename{$\forall$-intro}
\qquad
\dfrac{\Theta; \Delta \vdash \forall P.\,\varphi \qquad \FV(\psi) \subseteq \Theta}{\Theta; \Delta \vdash \subst{\varphi}{P}{\psi}}\rulename{$\forall$-elim}
$$

第 4 章的附加条件 $P \notin \FV(\Delta)$ 现在由 $P \notin \Theta$ 蕴涵：在 $\Delta$ 中自由出现的每个命题变量都在 $\Theta$ 中，而 $P$ 不在。公式在 $\alpha$ 等价意义下看待，所以约束的 $P$ 总可以改名以满足附加条件。与第 4 章一样，$\varphi^\ast \to \psi^\ast$ 表示 $\tPi{x}{\varphi^\ast}{\psi^\ast}$，其中 $x$ 是新鲜的。

第 4 章的上下文 $\Delta^\ast$ 先列出命题变量，再列出假设，但证明需要向右扩展上下文，所以允许任意顺序更为方便。

<div class="definition" markdown="1">

**定义 A.1（表示）.** 称上下文 $\Gamma$ *表示* $(\Theta; \Delta)$，如果 $\ctxok{\Gamma}$，且 $\Gamma$ 由以下假设按某种顺序组成：对每个 $P \in \Theta$ 有一个假设 $P : \Sort{0}$，对每个 $\chi \in \Delta$ 有一个假设 $h : \chi^\ast$。

</div>

<div class="theorem" markdown="1">

**定理 A.2（定理 4.1 的精确形式）.** 若 $\Theta; \Delta \vdash \varphi$ 且 $\Gamma$ 表示 $(\Theta; \Delta)$，则存在项 $t$ 使得 $\Gamma \vdash t : \varphi^\ast$。

</div>

定理 4.1 是 $\Gamma = \Delta^\ast$ 的特例。当 $\Theta$ 列出全部自由命题变量时，上下文 $\Delta^\ast$ 恰好包含所需的假设；由下面的引理 A.3 加上规则 C-Ext，它是良构的，因为一旦命题变量在作用域内，每个假设类型 $\chi^\ast$ 都是命题。

## 关于翻译的事实

翻译 $\varphi \mapsto \varphi^\ast$ 与替换可交换：

$$
(\subst{\varphi}{P}{\psi})^\ast = \subst{\varphi^\ast}{P}{\psi^\ast}.
$$

这是对 $\varphi$ 的例行归纳：两边都把 $P$ 的自由出现换成 $\psi^\ast$，而翻译对命题变量什么也不做，只保留它的名字。主证明的 $\forall$-elim 情形依赖这个等式。

下一条引理是[第 13 章](13-universes.md)的宇宙结构唯一介入的地方，它说每个翻译后的公式都是命题，也就是类型为 $\Sort{0}$。没有它，类型规则 T-Lam 就不能应用于假设，$\forall$-elim 情形也不能用任意公式实例化量词。

<div class="lemma" markdown="1">

**引理 A.3（公式是命题）.** 若 $\ctxok{\Gamma}$，且对每个 $P \in \FV(\varphi)$ 都有 $(P : \Sort{0}) \in \Gamma$，则 $\Gamma \vdash \varphi^\ast : \Sort{0}$。

</div>

<div class="proof" markdown="1">

对 $\varphi$ 归纳。

对命题变量 $P$，假设给出 $(P : \Sort{0}) \in \Gamma$，于是由 T-Var 得 $\Gamma \vdash P : \Sort{0}$。

对 $\varphi \to \psi$，归纳假设给出 $\Gamma \vdash \varphi^\ast : \Sort{0}$，于是对新鲜的 $x$，由 C-Ext 知 $\Gamma, x : \varphi^\ast$ 良构。在这个扩展后的上下文中对 $\psi$ 用归纳假设，得 $\Gamma, x : \varphi^\ast \vdash \psi^\ast : \Sort{0}$，再由 T-Pi 得 $\Gamma \vdash \tPi{x}{\varphi^\ast}{\psi^\ast} : \Sort{\imax(0, 0)} = \Sort{0}$。

对 $\forall Q.\,\chi$，把 $Q$ 改名使 $Q \notin \dom(\Gamma)$。T-Sort 给出 $\Gamma \vdash \Sort{0} : \Sort{1}$，于是由 C-Ext 知 $\Gamma, Q : \Sort{0}$ 良构。在该上下文中对 $\chi$ 用归纳假设，得 $\Gamma, Q : \Sort{0} \vdash \chi^\ast : \Sort{0}$，再由 T-Pi 得 $\Gamma \vdash \tPi{Q}{\Sort{0}}{\chi^\ast} : \Sort{\imax(1, 0)} = \Sort{0}$。

</div>

<aside class="note" markdown="1">

最后一种情形正是用到非谓词性的地方：定义域 $\Sort{0}$ 位于 $\Sort{1}$ 中，所以如果用 $\max$ 代替 $\imax$，类型 $(\forall Q.\,\chi)^\ast$ 会落在 $\Sort{1}$ 而不是 $\Sort{0}$。那样下面的 $\forall$-elim 情形就只对不含 $\forall$ 的公式 $\psi$ 成立，因为只有这些公式的类型是 $\Sort{0}$，才允许作为参数。第 13 章讨论了这一设计选择。

</aside>

## 证明

<div class="proof" markdown="1">

我们对 $\Theta; \Delta \vdash \varphi$ 的推导做归纳来证明定理 A.2，同时对所有表示它的上下文 $\Gamma$ 一并证明。每种情形构造的，都是第 4 章表格右栏所示的类型推导。

*假设.* 该规则由 $\varphi \in \Delta$ 得出 $\Theta; \Delta \vdash \varphi$。由于 $\Gamma$ 表示 $(\Theta; \Delta)$，它包含一个假设 $h : \varphi^\ast$，于是由 T-Var 得 $\Gamma \vdash h : \varphi^\ast$。

*$\to$-intro.* 前提是 $\Theta; \Delta, \varphi \vdash \psi$，结论是 $\Theta; \Delta \vdash \varphi \to \psi$。由引理 A.3，$\Gamma \vdash \varphi^\ast : \Sort{0}$。因此对新鲜的 $h$，上下文 $\Gamma, h : \varphi^\ast$ 由 C-Ext 良构，并且它表示 $(\Theta; \Delta, \varphi)$。把归纳假设用于该前提和这个上下文，得到对某个 $t$ 有 $\Gamma, h : \varphi^\ast \vdash t : \psi^\ast$，再由 T-Lam 得

$$
\Gamma \vdash \tLam{h}{\varphi^\ast}{t} : \tPi{h}{\varphi^\ast}{\psi^\ast}.
$$

这个类型就是 $\varphi^\ast \to \psi^\ast$：$\psi^\ast$ 的自由变量都是命题变量，$h$ 不在其中，所以 $h$ 不出现在 $\psi^\ast$ 里，这个 $\Pi$ 是非依赖的。

*$\to$-elim.* 前提是 $\Theta; \Delta \vdash \varphi \to \psi$ 和 $\Theta; \Delta \vdash \varphi$。两个归纳假设给出 $\Gamma \vdash f : \tPi{x}{\varphi^\ast}{\psi^\ast}$，其中 $x \notin \FV(\psi^\ast)$，以及 $\Gamma \vdash a : \varphi^\ast$。T-App 给出 $\Gamma \vdash f\;a : \subst{\psi^\ast}{x}{a}$；由于 $x$ 不出现在 $\psi^\ast$ 中，替换什么也不做：$\subst{\psi^\ast}{x}{a} = \psi^\ast$。

*$\forall$-intro.* 前提是 $\Theta, P; \Delta \vdash \varphi$，其中 $P \notin \Theta$；结论是 $\Theta; \Delta \vdash \forall P.\,\varphi$。必要时把 $P$ 改名，设 $P \notin \dom(\Gamma)$；一个例行归纳表明，把 $\Theta$ 中的变量改成新鲜变量保持推导不变。由 T-Sort 和 C-Ext，$\Gamma, P : \Sort{0}$ 良构，并且它表示 $(\Theta, P; \Delta)$。归纳假设给出 $\Gamma, P : \Sort{0} \vdash t : \varphi^\ast$，再由 T-Lam 得

$$
\Gamma \vdash \tLam{P}{\Sort{0}}{t} : \tPi{P}{\Sort{0}}{\varphi^\ast},
$$

这正是 $\forall P.\,\varphi$ 的翻译。

*$\forall$-elim.* 前提是 $\Theta; \Delta \vdash \forall P.\,\varphi$，其中 $\FV(\psi) \subseteq \Theta$；结论是 $\Theta; \Delta \vdash \subst{\varphi}{P}{\psi}$。归纳假设给出 $\Gamma \vdash f : \tPi{P}{\Sort{0}}{\varphi^\ast}$。由于 $\psi$ 的每个命题变量都在 $\Theta$ 中，从而在 $\Gamma$ 中有假设 $Q : \Sort{0}$，引理 A.3 给出 $\Gamma \vdash \psi^\ast : \Sort{0}$。T-App 给出

$$
\Gamma \vdash f\;\psi^\ast : \subst{\varphi^\ast}{P}{\psi^\ast} = (\subst{\varphi}{P}{\psi})^\ast,
$$

其中最后一步是上一节的替换等式。

逻辑的每条规则都已覆盖，所以定理对每棵推导成立。

</div>

证明从未用到 T-Conv：它构造的每棵类型推导都只在语法上比较类型，至多相差约束变量的名字；只有当逻辑扩展了计算，比如加入第二部分的归纳类型，转换才成为必需。

<aside class="history" markdown="1">

相反的方向，即类型为 $\varphi^\ast$ 的每个项都来自 $\varphi$ 的某个证明，称为*保守性*。正如第 4 章所指出的，它更难，因为 $\Sort{0}$ 中含有不是公式翻译的类型，一个项可能途经它们。本书不需要它：内核必须保证的是一致性，其证明见[附录 D](d-proof-consistency.md)。

</aside>

<div class="summary-box" markdown="1">

要点回顾

- 定理的精确形式带有一个显式的命题变量列表 $\Theta$，并对每个表示 $(\Theta; \Delta)$ 的上下文（顺序任意）证明结论。
- 每个翻译后的公式都位于 $\Sort{0}$ 中（引理 A.3）。这在 $\forall$ 情形用到非谓词性，也正是它让 $\forall$-elim 能用任意公式实例化量词。
- 证明是对推导的归纳；每条逻辑规则恰好对应一条类型规则：Hyp 对应 T-Var，两条引入规则对应 T-Lam，两条消去规则对应 T-App。
- 从未用到 T-Conv，因为这个逻辑没有计算。

</div>
