<div class="lead" markdown="1">

本书用到的每个符号、判断和术语，以及引入它的章节。阅读时可把本附录当作参考，也可当作本书内容的清单。

</div>

## 记法

### 项

| 记法 | 含义 | 章节 |
|---|---|---|
| $\Sort{u}$ | 层级 $u$ 上的宇宙；$\Sort{0}$ 是命题的宇宙 | [2](02-syntax.md) |
| $x, y, z$ | 变量 | [2](02-syntax.md) |
| $c$ | 签名中的常量 | [7](07-inductive-nat.md) |
| $\tPi{x}{A}{B}$ | 依赖函数类型（$\Pi$ 类型） | [2](02-syntax.md) |
| $A \to B$ | 非依赖函数类型，即 $\tPi{\_}{A}{B}$ | [2](02-syntax.md) |
| $\tLam{x}{A}{t}$ | 函数（$\lambda$ 抽象） | [2](02-syntax.md) |
| $t\;s$ | 应用，左结合 | [2](02-syntax.md) |
| $h\;a_1 \cdots a_n$ | 脊：头部 $h$ 应用于一列参数 | [2](02-syntax.md) |
| $(\vec{x} : \vec{A})$, $\tPi{\vec{x}}{\vec{A}}{B}$ | 绑定的 telescope，以及其上的 $\Pi$ | [8](08-inductive-recipe.md) |
| $\FV(t)$ | $t$ 的自由变量 | [11](11-substitution-alpha.md) |
| $\subst{t}{x}{s}$ | 在 $t$ 中用 $s$ 替换 $x$ 的避免捕获的替换 | [11](11-substitution-alpha.md) |
| $\db{t}{E}$ | $t$ 在绑定子列表 $E$ 之下的无名（de Bruijn）形式 | [B](b-proof-alpha.md) |
| $\hole{m}$ | 部分证明项中的洞（元变量） | [10](10-tactics.md) |

### 判断与关系

| 记法 | 含义 | 章节 |
|---|---|---|
| $\Gamma$ | 上下文，即假设 $x : A$ 的有序列表 | [3](03-typing-rules.md) |
| $\cdot$ | 空上下文 | [3](03-typing-rules.md) |
| $\dom(\Gamma)$ | $\Gamma$ 中被假设的名字 | [3](03-typing-rules.md) |
| $\ctxok{\Gamma}$ | $\Gamma$ 是良构的 | [3](03-typing-rules.md) |
| $\Gamma \vdash t : A$ | 在 $\Gamma$ 中 $t$ 具有类型 $A$ | [3](03-typing-rules.md) |
| $\Sigma$ | 常量的签名 | [7](07-inductive-nat.md) |
| $c : C \mathrel{:=} t$ | 体为 $t$ 的定义 | [7](07-inductive-nat.md) |
| $\imax(u, v)$ | 若 $v = 0$ 则为 $0$，否则为 $\max(u, v)$ | [3](03-typing-rules.md)、[13](13-universes.md) |
| $s \alphaeq t$ | α 等价 | [11](11-substitution-alpha.md) |
| $E_1; E_2 \vdash s \alphaeq t$ | 绑定子列表 $E_1$、$E_2$ 之下的算法化 α 等价 | [11](11-substitution-alpha.md) |
| $\mathrm{idx}(E, x)$ | $E$ 中最后一个 $x$ 的位置，从右数起 | [11](11-substitution-alpha.md) |
| $t \betared t'$, $t \deltared t'$, $t \iotared t'$ | β 归约、δ 归约、ι 归约 | [3](03-typing-rules.md)、[7](07-inductive-nat.md) |
| $t \to t'$ | 任意一种归约的一步 | [12](12-reduction-conversion.md) |
| $s \conv t$ | 定义相等（转换） | [3](03-typing-rules.md)、[12](12-reduction-conversion.md) |
| $\Delta \vdash \varphi$ | 二阶命题逻辑中的可证性 | [4](04-logic.md) |
| $\varphi^\ast$, $\Delta^\ast$ | 公式的翻译、假设列表的翻译 | [4](04-logic.md) |
| $\goal{\Gamma}{\hole{m}}{T}$ | 目标：为洞 $m$ 在 $\Gamma$ 中找一个类型为 $T$ 的项 | [10](10-tactics.md) |

### 标准内核的常量

| 记法 | 类型 | leanmini 名字 | 章节 |
|---|---|---|---|
| $\Nat$ | $\Sort{1}$ | `Nat` | [7](07-inductive-nat.md) |
| $\zero$ | $\Nat$ | `Nat.zero` | [7](07-inductive-nat.md) |
| $\suc$ | $\Nat \to \Nat$ | `Nat.succ` | [7](07-inductive-nat.md) |
| $\NatRec{u}$ | 见图 7.1 | `Nat.rec0`, `Nat.rec1` | [7](07-inductive-nat.md) |
| $\Eq{u}$ | $\tPi{A}{\Sort{u}}{A \to A \to \Sort{0}}$ | `Eq` | [9](09-equality.md) |
| $\refl{u}$ | $\tPi{A}{\Sort{u}}{\tPi{a}{A}{\Eq{u}\;A\;a\;a}}$ | `Eq.refl` | [9](09-equality.md) |
| $\EqRecDep{u,v}$ | 依赖消去子，图 9.1 | `Eq.rec0`, `Eq.rec1` | [9](09-equality.md) |
| $\EqRec{u,v}$ | 非依赖消去子（一个定义） | 未预先声明 | [9](09-equality.md) |
| $\add$, $m + n$ | $\Nat \to \Nat \to \Nat$ | `add`（在脚本中定义） | [7](07-inductive-nat.md) |

### 算法

| 名称 | 作用 | Rust | 章节 |
|---|---|---|---|
| $\Infer(\Gamma, t)$ | 计算 $t$ 的类型 | `Kernel::infer` | [5](05-algorithm.md) |
| $\Check(\Gamma, t, T)$ | 验证 $t : T$ | `Kernel::check` | [5](05-algorithm.md) |
| $\InferSort(\Gamma, A)$ | 验证 $A$ 是类型，并返回其层级 | `Kernel::infer_sort` | [5](05-algorithm.md) |
| $\Freshen(\Gamma, x, b)$ | 重命名会遮蔽 $\Gamma$ 的绑定子 | `rename_binder_if_needed` | [5](05-algorithm.md) |
| $\Whnf(t)$ | 弱头范式 | `Kernel::whnf` | [12](12-reduction-conversion.md) |
| $\Normalize(t)$ | 完全范式 | `Kernel::normalize` | [12](12-reduction-conversion.md) |
| $\IsDefEq(s, t)$ | 判定 $s \conv t$ | `Kernel::is_def_eq` | [12](12-reduction-conversion.md) |

## 术语表

**α 等价（Alpha-equivalence）。** 项在约束变量重命名意义下的相等。判定方法：约束变量按绑定子位置比较，自由变量按名字比较。[第 11 章](11-substitution-alpha.md)。

**β 归约（Beta-reduction）。** 计算步骤 $(\tLam{x}{A}{t})\;s \to \subst{t}{x}{s}$。[第 3 章](03-typing-rules.md)和[第 12 章](12-reduction-conversion.md)。

**捕获（Capture）。** 把一个项替换到某个绑定子之下，而该绑定子恰好绑定了该项的某个自由变量，从而改变其含义的错误。通过重命名绑定子来避免。[第 11 章](11-substitution-alpha.md)。

**合流性（Confluence）。** 不同的归约顺序到达同一范式的性质。正是它使得转换可以通过规范化来判定。[第 12 章](12-reduction-conversion.md)。

**一致性（Consistency）。** 没有闭项具有类型 $\tPi{P}{\Sort{0}}{P}$。这个性质使内核的接受有意义。[第 4 章](04-logic.md)和[第 14 章](14-properties.md)。

**构造子（Constructor）。** 构造归纳类型的值的常量，如 $\zero$ 和 $\suc$。构造子从不归约。[第 7 章](07-inductive-nat.md)。

**上下文（Context）。** 类型假设的有序列表。[第 3 章](03-typing-rules.md)。

**转换（Conversion）。** 见定义相等。

**Curry-Howard 对应（Curry-Howard correspondence）。** 命题即类型，证明即项，证明检查即类型检查。[第 1 章](01-propositions-as-types.md)。

**de Bruijn 索引（De Bruijn index）。** 用约束变量的出现与其绑定子之间的绑定子个数来表示该变量，这使得 α 等价的项完全相同。[第 11 章](11-substitution-alpha.md)、[附录 B](b-proof-alpha.md)。

**定义相等（Definitional equality）。** 由归约和 α 等价生成的项上的等价关系；由内核判定。与命题相等相对。[第 9 章](09-equality.md)和[第 12 章](12-reduction-conversion.md)。

**δ 归约（Delta-reduction）。** 把已定义的常量展开为其体。[第 7 章](07-inductive-nat.md)。

**依赖函数类型（Dependent function type）。** 结果类型可以提到参数的 $\Pi$ 类型；全称命题的证明所具有的类型。[第 1 章](01-propositions-as-types.md)。

**大消去（Elimination, large）。** 用命题的递归子构造数据，仅对子单元允许。[第 8 章](08-inductive-recipe.md)。

**字段（Field）。** 构造子的一个参数，但不计归纳类型的参数（parameter）。[第 8 章](08-inductive-recipe.md)。

**目标（Goal）。** 一个上下文连同一个类型，其项尚待寻找。[第 10 章](10-tactics.md)。

**非谓词的（Impredicative）。** 包含对该宇宙本身量化的类型的宇宙。$\Sort{0}$ 是非谓词的；更高的宇宙不是。[第 13 章](13-universes.md)。

**索引（Index）。** 归纳类型构造器的参数中可在构造子之间变化的那种，如向量的长度或等式的右侧。[第 8 章](08-inductive-recipe.md)。

**归纳假设（Induction hypothesis）。** 小前提中“motive 对递归字段已经成立”这一假设。[第 7 章](07-inductive-nat.md)。

**归纳类型（Inductive type）。** 由其构造子指定的类型，内核由此生成递归子和 ι 规则。[第 7 章](07-inductive-nat.md)和[第 8 章](08-inductive-recipe.md)。

**ι 归约（Iota-reduction）。** 在构造子应用上运行递归子。[第 7 章](07-inductive-nat.md)和[第 12 章](12-reduction-conversion.md)。

**内核（Kernel）。** 判定 $\Gamma \vdash t : A$ 的可信组件。其他一切只是为它生产项。[第 1 章](01-propositions-as-types.md)。

**大前提（Major premise）。** 递归子的参数中，由其构造子决定使用哪条 ι 规则的那一个。[第 7 章](07-inductive-nat.md)。

**元变量（Metavariable）。** Lean 对部分项中的洞的称呼。[第 10 章](10-tactics.md)。

**小前提（Minor premise）。** 递归子的参数中，给出某一构造子对应情形的那一个。[第 7 章](07-inductive-nat.md)。

**motive。** 为每个元素给出递归子结果类型的函数 $M$；对归纳而言，它是一个谓词。[第 7 章](07-inductive-nat.md)。

**中性项（Neutral term）。** 以变量（或在有常量时，以卡住的常量）为头部的范式项。[第 14 章](14-properties.md)、[附录 D](d-proof-consistency.md)。

**范式（Normal form）。** 没有任何归约步骤可应用的项。[第 12 章](12-reduction-conversion.md)。

**参数（Parameter）。** 归纳类型构造器的参数中在每个构造子里都相同的那种，如列表的元素类型。[第 8 章](08-inductive-recipe.md)。

**严格正性（Positivity, strict）。** 递归字段只能把归纳类型用作函数的结果、绝不能用作函数参数的条件。终止性和一致性都需要它。[第 8 章](08-inductive-recipe.md)。

**谓词的（Predicative）。** 不包含对自身量化的类型的宇宙。$u \ge 1$ 时的 $\Sort{u}$。[第 13 章](13-universes.md)。

**证明无关性（Proof irrelevance）。** Lean 的规则：同一命题的任意两个证明定义相等。MiniLean4 未实现。[第 13 章](13-universes.md)。

**命题相等（Propositional equality）。** 归纳类型 $\Eq{}$。它的证明是项；与定义相等相对。[第 9 章](09-equality.md)。

**递归子（Recursor）。** 为归纳类型生成的常量，表达结构递归和归纳。[第 7 章](07-inductive-nat.md)。

**签名（Signature）。** 常量及其类型的表，定义还带有体。[第 7 章](07-inductive-nat.md)。

**脊（Spine）。** 把项看作头部应用于一列参数的视角。[第 2 章](02-syntax.md)。

**强规范化（Strong normalization）。** 从良类型项出发的每个归约序列都是有限的。[第 14 章](14-properties.md)。

**类型保持性（Subject reduction）。** 归约保持类型。[第 14 章](14-properties.md)。

**子单元（Subsingleton）。** 至多有一个构造子、且其字段全是证明或索引的命题；它可以消去到任何宇宙。[第 8 章](08-inductive-recipe.md)。

**语法制导（Syntax-directed）。** 项的形状决定可用规则的规则系统。除 T-Conv 之外的所有类型规则。[第 5 章](05-algorithm.md)。

**策略（Tactic）。** 内核之外的程序，为证明状态中的洞赋值项。[第 10 章](10-tactics.md)。

**Telescope。** 一列绑定，其中靠后的类型可以提到靠前的变量。[第 8 章](08-inductive-recipe.md)。

**传输（Transport）。** 沿着 $a = b$ 的证明，经由 $\Eq{}$ 的递归子，把关于 $a$ 的事实搬到关于 $b$ 的事实。[第 9 章](09-equality.md)。

**宇宙（Universe）。** 元素都是类型的类型：$\Sort{u}$。[第 2 章](02-syntax.md)和[第 13 章](13-universes.md)。

**弱头范式（Weak head normal form）。** 只在项的头部归约、直到最外层形状可见为止所得的结果。[第 12 章](12-reduction-conversion.md)。

<div class="summary-box" markdown="1">

要点回顾

- 项、判断和算法各有一套全书统一使用的固定记法；上面的表格把每一项对应到它的 Rust 实现。
- 两种相等（定义相等与命题相等）和两类宇宙（非谓词的与谓词的）是需要分清的区别。

</div>
