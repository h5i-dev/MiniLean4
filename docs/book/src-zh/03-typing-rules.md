<div class="lead" markdown="1">

内核的任务是判定“项 $t$ 具有类型 $A$”这一判断。本章用一小组推理规则定义这个判断：每种项一条规则，外加一条允许在类型内部进行计算的规则。自底向上地读每条规则，它就成了检查项的一套步骤，而这套步骤在第 5 章变成算法。

</div>

## 上下文与判断

像 $f\;p$ 这样的项无法孤立地检查：它的类型取决于 $f$ 和 $p$ 是什么。**上下文**（context）$\Gamma$ 记录这些信息，它是一个有序的假设列表

$$
\Gamma \;=\; x_1 : A_1,\; x_2 : A_2,\; \ldots,\; x_n : A_n,
$$

给出作用域内每个变量的类型，$\dom(\Gamma)$ 表示名字的集合 $\{x_1, \ldots, x_n\}$。空上下文写作 $\cdot$。

顺序很重要，因为靠后的类型可以提到靠前的变量，比如 $P : \Sort{0},\; h : P$：只有先知道 $P$ 是命题，假设 $h : P$ 才有意义。我们会要求上下文中的名字互不相同，这样上下文就能当作一个从名字到类型的字典来使用；不过这个字典的各条目按顺序相互依赖。

两个判断是一起定义的。

- $\ctxok{\Gamma}$ 表示上下文 $\Gamma$ 是*良构的*（well formed）：每条假设的类型在它之前的上下文中都是一个类型。
- $\Gamma \vdash t : A$ 表示在 $\Gamma$ 的假设之下，项 $t$ 具有类型 $A$。

透过 Curry-Howard 的视角，$\Gamma \vdash t : A$ 说的是：$t$ 是从假设 $\Gamma$ 出发对 $A$ 的证明。

## 规则

图 3.1 列出全部规则，每条规则横线上方是前提，下方是结论；只要所有前提成立，结论就成立。右侧的规则名在全书中通用。

<div class="rulebox" markdown="1">

<p class="caption">图 3.1. 良构上下文（第一行）与类型规则。</p>

$$
\dfrac{\phantom{\ctxok{\Gamma}}}{\ctxok{\cdot}}\rulename{C-Empty}
\qquad
\dfrac{\ctxok{\Gamma} \qquad \Gamma \vdash A : \Sort{u} \qquad x \notin \dom(\Gamma)}{\ctxok{\Gamma, x : A}}\rulename{C-Ext}
$$

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
\qquad
\dfrac{\ctxok{\Gamma} \qquad (x : A) \in \Gamma}{\Gamma \vdash x : A}\rulename{T-Var}
$$

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash B : \Sort{v}}{\Gamma \vdash \tPi{x}{A}{B} : \Sort{\imax(u, v)}}\rulename{T-Pi}
$$

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash t : B}{\Gamma \vdash \tLam{x}{A}{t} : \tPi{x}{A}{B}}\rulename{T-Lam}
$$

$$
\dfrac{\Gamma \vdash f : \tPi{x}{A}{B} \qquad \Gamma \vdash a : A}{\Gamma \vdash f\;a : \subst{B}{x}{a}}\rulename{T-App}
$$

$$
\dfrac{\Gamma \vdash t : A \qquad \Gamma \vdash B : \Sort{u} \qquad A \conv B}{\Gamma \vdash t : B}\rulename{T-Conv}
$$

</div>

有两条规则用到了项上的操作，接下来几章把它们当作黑箱处理。

**替换。**T-App 用 $\subst{B}{x}{a}$ 表示把 $B$ 中 $x$ 的每个自由出现替换为 $a$ 的结果。例如，$\subst{(P \to P)}{P}{Q} = Q \to Q$。在绑定子内部替换名字需要小心，[第 11 章](11-substitution-alpha.md)会解释；在那之前，直观含义就够用了。

**定义相等。**当 $A$ 和 $B$ 在某种内核可以机械判定的意义下是“同一个类型”时，T-Conv 写作 $A \conv B$。两类差异会被忽略。

- 约束变量的名字。$\tPi{P}{\Sort{0}}{P \to P}$ 和 $\tPi{Q}{\Sort{0}}{Q \to Q}$ 陈述的是同一个命题，仅有这种差异的项是 *α 等价*的，写作 $A \alphaeq B$。
- 计算。若 $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$，则 $\mathit{Id}\;P$ 把 $P$ 代入 $X$ 后计算得到 $P$，因此 $\mathit{Id}\;P$ 的证明应当算作 $P$ 的证明。计算步骤 $(\tLam{x}{A}{t})\;s \betared \subst{t}{x}{s}$ 称为 *β 归约*。

内核判定 $A \conv B$ 的方法是把两边尽可能地计算下去，再检查结果是否 α 等价。[第 12 章](12-reduction-conversion.md)给出精确定义。

## 解读规则

规则最好自底向上地读，当作一套步骤：要建立结论，就先建立前提。

**C-Empty 与 C-Ext。**上下文一次加入一条假设，每条新假设的类型本身必须是一个类型。附加条件 $x \notin \dom(\Gamma)$ 禁止两条假设同名，而由于约束变量的名字无关紧要，这个条件并不限制什么：会冲突的绑定子总可以先改名。[第 11 章](11-substitution-alpha.md#variable-capture-in-contexts)展示了跳过这个条件的内核会出什么问题。

**T-Sort。**每个宇宙都住在下一个宇宙里：$\Sort{0} : \Sort{1}$，$\Sort{1} : \Sort{2}$，依此类推。[第 13 章](13-universes.md)解释为什么宇宙不能是自己的类型。

**T-Var。**变量的类型就是上下文赋予它的类型。从逻辑上看：使用一条假设。

**T-Pi。**若 $A$ 是类型，且在假设 $x : A$ 之后 $B$ 是类型，则 $\tPi{x}{A}{B}$ 是类型。所得宇宙为 $\imax(u, v)$：当 $v = 0$ 时为 $0$，否则为 $\max(u, v)$。用文字说：只要函数体是命题，$\Pi$ 类型就是命题，无论它量化的是什么；否则它住在两个宇宙中较大的那个。从逻辑上看，这条规则规定了 $A \to B$ 和 $\forall x{:}A.\,B$ 何时是良构的陈述。

**T-Lam。**要构造从 $A$ 到 $B$ 的函数，先假设 $x : A$，再构造类型为 $B$ 的项 $t$。函数体的类型 $B$ 可以提到 $x$，并原样保留在所得的 $\Pi$ 类型中，依赖性正是从这里进入的。从逻辑上看，这是蕴含和全称量词的引入规则：要证明 $A \to B$，就假设 $A$ 并证明 $B$。

**T-App。**若 $f$ 把每个 $x : A$ 映射到 $B$ 的一个元素，且 $a : A$，则 $f\;a$ 的类型是把 $B$ 中的 $x$ 替换为 $a$ 的结果。当 $B$ 不提到 $x$ 时，这就是肯定前件（modus ponens）：由 $A \to B$ 和 $A$ 推出 $B$；反之，这是对全称陈述的实例化。例如，若 $f : \tPi{n}{\Nat}{n + 0 = n}$，则 $f\;3 : 3 + 0 = 3$（自然数在[第 7 章](07-inductive-nat.md)登场）。

**T-Conv。**在计算意义下相等的类型可以互换：由 $h : \mathit{Id}\;P$ 可以得出 $h : P$。前提 $\Gamma \vdash B : \Sort{u}$ 保证新类型本身是一个类型。这是唯一一条使用时机不由 $t$ 的形状决定的规则，这一点对[第 5 章](05-algorithm.md)的算法很重要。

<aside class="intuition" markdown="1">

每条规则都是关于函数的一点常识。T-Lam 说怎样构造函数；T-App 说怎样使用函数；T-Pi 说函数类型何时有意义；T-Var 和 T-Sort 说基本的东西是什么；T-Conv 说在类型内部计算不改变它的含义。规则里没有任何专门“逻辑”的成分，逻辑是透过 Curry-Howard 解读这些规则的结果，[第 4 章](04-logic.md)会把这一点讲精确。

</aside>

## 应用为何重要

构造项的 T-Lam 和 T-Pi 也许更引人注意，但若没有 T-App，证明只能原样返回假设，无法真正*使用*它。粗略地说，此时只能证明结论恰好是某条假设的命题，例如 $P \to Q \to P$。复合律

$$
(P \to Q) \to (Q \to R) \to P \to R,
$$

的证明是 $\tLam{f}{P \to Q}{\tLam{g}{Q \to R}{\tLam{p}{P}{g\,(f\,p)}}}$，它先应用 $f$ 再应用 $g$。凡是不止于复述假设的证明都要经过 T-App，而在依赖类型论中，T-App 也是替换发生的地方，因此大部分微妙之处都在这里。

## 第一个推导

推导是一棵由规则实例组成的树，树根是要建立的判断。下面是 $\tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ 证明 $\tPi{P}{\Sort{0}}{P \to P}$ 的推导。记 $\Gamma_1 = P : \Sort{0}$，$\Gamma_2 = \Gamma_1, h : P$，并省略例行的良构前提 $\ctxok{\Gamma}$。

$$
\dfrac{
  \dfrac{}{\cdot \vdash \Sort{0} : \Sort{1}}\rulename{T-Sort}
  \qquad
  \dfrac{
    \dfrac{}{\Gamma_1 \vdash P : \Sort{0}}\rulename{T-Var}
    \qquad
    \dfrac{}{\Gamma_2 \vdash h : P}\rulename{T-Var}
  }{\Gamma_1 \vdash \tLam{h}{P}{h} : \tPi{h}{P}{P}}\rulename{T-Lam}
}{\cdot \vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}}\rulename{T-Lam}
$$

内核构建的就是这棵树。下面每个节点是规则的一次应用，标有它建立的判断；切换到调用视图，可以自顶向下地把它读成生成这棵树的递归过程。换成你自己的项，看看哪些规则会被触发。

<div class="explorer" data-kind="derive" data-view="tree" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

两点观察。第一，树的形状跟随项的形状：根是一个 $\lambda$，其下又是一个 $\lambda$，叶子是变量。第二，根处的类型是 $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$，而所陈述的命题是 $\tPi{P}{\Sort{0}}{P \to P}$。两者只差一个约束变量的名字（$h$ 与箭头的匿名 `_`），所以它们是 α 等价的，由 T-Conv 弥合这一差距。[第 6 章](06-worked-examples.md)会用算法重新审视这个例子。

<aside class="code" markdown="1">

本章的规则由 `src/typecheck.rs` 中的 `Kernel::infer` 和 `Kernel::check` 实现，[第 5 章](05-algorithm.md)会逐行阅读它们。上下文是 `src/declaration.rs` 中的 Rust 类型 `Context = Vec<(String, Term)>`：一个由名字与类型配对组成的向量，从末尾开始查找，使得同名假设中最新的一条生效。

</aside>

## 练习

<div class="exercise" markdown="1">

自底向上地应用时，下列判断各由哪条规则处理，产生哪些前提？(a) $\Gamma \vdash \tLam{x}{A}{x} : A \to A$。(b) $\Gamma \vdash \Sort{2} : \Sort{3}$。(c) $\Gamma \vdash f\;a : B$，其中 $f : A \to B$。

<details markdown="1">
<summary>解答</summary>

(a) T-Lam，前提是对某个 $u$ 有 $\Gamma \vdash A : \Sort{u}$，以及 $\Gamma, x : A \vdash x : A$；后者由 T-Var 处理。所得类型是 $\tPi{x}{A}{A}$，在不计绑定子名字的意义下就是 $A \to A$。
(b) T-Sort，唯一的前提是 $\ctxok{\Gamma}$。
(c) T-App，前提是 $\Gamma \vdash f : \tPi{\_}{A}{B}$ 和 $\Gamma \vdash a : A$。结论是 $\subst{B}{\_}{a} = B$，因为 `_` 不出现在 $B$ 中。

</details>

</div>

<div class="exercise" markdown="1">

用 T-Pi 计算 $\tPi{P}{\Sort{0}}{P \to P}$ 和 $\tPi{A}{\Sort{1}}{A \to A}$ 的宇宙。

<details markdown="1">
<summary>解答</summary>

对前者，$\Sort{0} : \Sort{1}$，故 $u = 1$；又 $P \to P : \Sort{0}$（再次用 T-Pi，取 $u = v = 0$），故 $v = 0$。于是宇宙为 $\Sort{\imax(1, 0)} = \Sort{0}$：对所有命题量化的陈述本身仍是命题。
对后者，$u = 2$，且 $A \to A : \Sort{1}$，故 $v = 1$，得到 $\Sort{\imax(2,1)} = \Sort{2}$。[第 13 章](13-universes.md)解释这种不对称。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 上下文是互不重名的假设 $x : A$ 的有序列表；判断 $\Gamma \vdash t : A$ 表示在这些假设下 $t$ 具有类型 $A$。
- 每种项一条规则，外加 T-Conv，它把在计算和约束变量改名意义下相等的类型视为同一。
- T-App 是使用假设、发生替换的地方；T-Conv 是唯一不由项的形状触发的规则。
- 替换和定义相等在第三部分之前当作黑箱。

</div>
