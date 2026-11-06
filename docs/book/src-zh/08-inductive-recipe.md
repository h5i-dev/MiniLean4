<div class="lead" markdown="1">

第 7 章手工构造了自然数的递归子。在 Lean 中，用户从不这样做：他们写下一个 `inductive` 声明，由内核检查它，并生成类型构造器、构造子、递归子及其计算规则。本章分三步建立这一过程，从更多的构造子，到参数，再到索引，最后给出一般性的表述。内核中对应的代码约有五百行。

</div>

## 更多构造子：树

$\Nat$ 有两个构造子，其中只有一个带递归参数。考虑一个有三个构造子的类型：

```lean
inductive Tree where
  | leaf   : Tree
  | node   : Tree -> Tree
  | branch : Tree -> Tree -> Tree
```

例如，$\mathsf{branch}\;(\mathsf{node}\;\mathsf{leaf})\;\mathsf{leaf}$ 是由四个构造子搭成的树。要对每棵树 $t$ 构造 $M\;t$，其中 $M : \mathsf{Tree} \to \Sort{v}$，第 7 章的方法要求每个构造子对应一个情形，而每个类型为 $\mathsf{Tree}$ 的参数各贡献一个归纳假设：

$$
\begin{array}{lcl}
m_{\mathsf{leaf}} &:& M\;\mathsf{leaf} \\[2pt]
m_{\mathsf{node}} &:& \tPi{t}{\mathsf{Tree}}{M\;t \to M\;(\mathsf{node}\;t)} \\[2pt]
m_{\mathsf{branch}} &:& \tPi{l}{\mathsf{Tree}}{\tPi{r}{\mathsf{Tree}}{M\;l \to M\;r \to M\;(\mathsf{branch}\;l\;r)}}
\end{array}
$$

递归子接受 motive、三个情形和一棵树：

$$
\mathsf{Tree.rec}_v : \tPi{M}{\mathsf{Tree} \to \Sort{v}}{\;
  M\;\mathsf{leaf} \to (\cdots_{\mathsf{node}}) \to (\cdots_{\mathsf{branch}}) \to \tPi{t}{\mathsf{Tree}}{M\;t}},
$$

其中省略号代表 $m_{\mathsf{node}}$ 和 $m_{\mathsf{branch}}$ 的类型。与 $\NatRec{v}$ 相比，变化的只有情形的个数和每个情形中假设的个数。记 $R$ 为部分应用 $\mathsf{Tree.rec}_v\;M\;m_{\mathsf{leaf}}\;m_{\mathsf{node}}\;m_{\mathsf{branch}}$，则 ι 规则为

$$
\begin{array}{rcl}
R\;\mathsf{leaf} &\iotared& m_{\mathsf{leaf}} \\[2pt]
R\;(\mathsf{node}\;t) &\iotared& m_{\mathsf{node}}\;t\;(R\;t) \\[2pt]
R\;(\mathsf{branch}\;l\;r) &\iotared& m_{\mathsf{branch}}\;l\;r\;(R\;l)\;(R\;r).
\end{array}
$$

每条规则按大前提头部的构造子选出对应的情形，并用对相应子树的递归调用填入每个假设。例如，取 $M = \tLam{\_}{\mathsf{Tree}}{\Nat}$ 以及情形

$$
m_{\mathsf{leaf}} = 1, \qquad
m_{\mathsf{node}} = \tLam{t}{\mathsf{Tree}}{\tLam{i}{\Nat}{1 + i}}, \qquad
m_{\mathsf{branch}} = \tLam{l}{\mathsf{Tree}}{\tLam{r}{\mathsf{Tree}}{\tLam{i}{\Nat}{\tLam{j}{\Nat}{1 + i + j}}}},
$$

则 $R$ 计算一棵树中构造子的个数：

$$
R\;(\mathsf{branch}\;(\mathsf{node}\;\mathsf{leaf})\;\mathsf{leaf})
\to 1 + R\;(\mathsf{node}\;\mathsf{leaf}) + R\;\mathsf{leaf}
\to 1 + (1 + R\;\mathsf{leaf}) + 1
\to 1 + (1 + 1) + 1 = 4.
$$

当 $M$ 是谓词（$v = 0$）时，同一个递归子就是树上的结构归纳。一般地，有 $n$ 个构造子的类型得到一个带 $n$ 个小前提 $m_1, \ldots, m_n$ 的递归子，而内核不需要任何针对该类型的专门代码：它只需知道，对每个构造子，该选哪个情形、该对哪些参数递归。

下面是内核眼中的这棵树。每个方框是一次构造子应用；递归字段挂在它下方，每个方框底部那一行是处理它的递归子情形，其中 $(R\;l)$ 和 $(R\;r)$ 是由递归调用算出的归纳假设。输入另一棵树即可查看它的各个情形。

<div class="explorer" data-kind="ctree" data-term="Tree.branch (Tree.node Tree.leaf) Tree.leaf"><pre class="prelude">inductive Tree : Sort 1 where
  | leaf
  | node (t : Tree)
  | branch (l : Tree) (r : Tree)</pre></div>

<div class="playground" data-file="tree-count"><pre>inductive Tree : Sort 1 where
  | leaf
  | node (t : Tree)
  | branch (l : Tree) (r : Tree)

def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def one : Nat := Nat.succ Nat.zero
def four : Nat := Nat.succ (Nat.succ (Nat.succ one))

# branch 的小前提先接受 l 和 r，再接受两个归纳假设。
def count : Tree -> Nat := fun (t : Tree) => Tree.rec1 (fun (_t : Tree) => Nat) one (fun (t : Tree) => fun (i : Nat) => Nat.succ i) (fun (l : Tree) => fun (r : Tree) => fun (i : Nat) => fun (j : Nat) => Nat.succ (add i j)) t

goal Eq Nat (count (Tree.branch (Tree.node Tree.leaf) Tree.leaf)) four
rfl
qed</pre></div>

## 参数：列表

一个数的列表要么为空，要么是一个数接在一个数的列表前面，因此我们可以声明类型 $\mathsf{ListNat}$，其构造子为 $\mathsf{nil}$ 和 $\mathsf{cons} : \Nat \to \mathsf{ListNat} \to \mathsf{ListNat}$。但这样一来，树的列表又需要另一个声明 $\mathsf{ListTree}$，带同样的构造子和一个单独的递归子，每种元素类型都要如此。更好的做法是让元素类型成为该类型本身的参数：

```lean
inductive List (A : Sort 1) where
  | nil  : List A
  | cons : A -> List A -> List A
```

现在 $\mathsf{List}\;\Nat$ 和 $\mathsf{List}\;\mathsf{Tree}$ 是同一个声明的两个实例。该声明添加

$$
\mathsf{List} : \Sort{1} \to \Sort{1}, \qquad
\mathsf{nil} : \tPi{A}{\Sort{1}}{\mathsf{List}\;A}, \qquad
\mathsf{cons} : \tPi{A}{\Sort{1}}{A \to \mathsf{List}\;A \to \mathsf{List}\;A}.
$$

构造子把 $A$ 作为显式的第一个参数。例如，单元素列表 $[5]$ 是 $\mathsf{cons}\;\Nat\;5\;(\mathsf{nil}\;\Nat)$。在同一个列表内，$A$ 从不改变：$\mathsf{cons}\;A\;a\;\mathit{as}$ 的尾部仍是一个 $\mathsf{List}\;A$。在每个构造子和每个递归参数中都保持不变的类型参数称为**参数**（parameter）。由于它从不改变，递归子可以在 motive 之前一次性接受它，并把它视为固定的：

$$
\begin{array}{l}
\mathsf{List.rec}_v : \tPi{A}{\Sort{1}}{\tPi{M}{\mathsf{List}\;A \to \Sort{v}}{\;M\;(\mathsf{nil}\;A) \to {}}} \\[2pt]
\qquad (\tPi{a}{A}{\tPi{\mathit{as}}{\mathsf{List}\;A}{M\;\mathit{as} \to M\;(\mathsf{cons}\;A\;a\;\mathit{as})}}) \to \tPi{x}{\mathsf{List}\;A}{M\;x} \\[8pt]
\mathsf{List.rec}_v\;A\;M\;m_1\;m_2\;(\mathsf{nil}\;A') \;\iotared\; m_1 \\[2pt]
\mathsf{List.rec}_v\;A\;M\;m_1\;m_2\;(\mathsf{cons}\;A'\;a\;\mathit{as}) \;\iotared\; m_2\;a\;\mathit{as}\;(\mathsf{List.rec}_v\;A\;M\;m_1\;m_2\;\mathit{as})
\end{array}
$$

除了开头的 $A$，这又是第 7 章的方法：$\mathsf{cons}$ 有两个参数，其中只有 $\mathit{as}$ 是递归的，所以它的情形得到一个归纳假设。规则忽略构造子中存储的参数 $A'$；在良类型的项里它可转换为 $A$。例如，列表的长度是

$$
\mathit{length} \mathrel{:=} \tLam{A}{\Sort{1}}{\tLam{x}{\mathsf{List}\;A}{
\mathsf{List.rec}_1\;A\;(\tLam{\_}{\mathsf{List}\;A}{\Nat})\;\zero\;(\tLam{a}{A}{\tLam{\mathit{as}}{\mathsf{List}\;A}{\tLam{r}{\Nat}{\suc\;r}}})\;x}}.
$$

列表值在每个构造子中都携带参数 $A$，下面的树把它显示在每个方框旁边：参数重复出现，字段各不相同。

<div class="explorer" data-kind="ctree" data-term="List.cons Nat (Nat.succ Nat.zero) (List.cons Nat Nat.zero (List.nil Nat))"><pre class="prelude">inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)</pre></div>

<div class="playground" data-file="examples/generic-list.leanmini"><pre>inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)

def length : forall (A : Sort 1), List A -> Nat := fun (A : Sort 1) => fun (xs : List A) => List.rec1 A (fun (_xs : List A) => Nat) Nat.zero (fun (head : A) => fun (tail : List A) => fun (r : Nat) => Nat.succ r) xs

# length [0, 0] = 2
goal Eq Nat (length Nat (List.cons Nat Nat.zero (List.cons Nat Nat.zero (List.nil Nat)))) (Nat.succ (Nat.succ Nat.zero))
rfl
qed</pre></div>

## 索引：向量

$\mathsf{List}\;\Nat$ 可以有任意长度。如果我们想把长度放进类型里，使 $\mathsf{Vec}\;\Nat\;0$ 和 $\mathsf{Vec}\;\Nat\;2$ 成为不同的类型，该怎么办？

```lean
inductive Vec (A : Sort 1) : Nat -> Sort 1 where
  | vnil  : Vec A 0
  | vcons : (n : Nat) -> A -> Vec A n -> Vec A (succ n)
```

元素类型 $A$ 仍然是参数。长度则不是：$\mathsf{vnil}$ 的长度为 $0$，而 $\mathsf{vcons}$ 接受一个长度为 $n$ 的向量，返回一个长度为 $\suc\;n$ 的向量。在不同构造子之间、以及构造子与其递归参数之间可以不同的类型参数称为**索引**（index）。构造子为

$$
\mathsf{vnil} : \tPi{A}{\Sort{1}}{\mathsf{Vec}\;A\;\zero}, \qquad
\mathsf{vcons} : \tPi{A}{\Sort{1}}{\tPi{n}{\Nat}{A \to \mathsf{Vec}\;A\;n \to \mathsf{Vec}\;A\;(\suc\;n)}}.
$$

由于索引会变化，递归子不能预先固定它。取而代之的是，motive 把它作为参数接受，$M : \tPi{n}{\Nat}{\mathsf{Vec}\;A\;n \to \Sort{v}}$，而 $\mathsf{vcons}$ 的情形是

$$
\tPi{n}{\Nat}{\tPi{a}{A}{\tPi{\mathit{xs}}{\mathsf{Vec}\;A\;n}{M\;n\;\mathit{xs} \to M\;(\suc\;n)\;(\mathsf{vcons}\;A\;n\;a\;\mathit{xs})}}}.
$$

归纳假设谈的是长度为 $n$ 的向量，这从递归参数的类型 $\mathsf{Vec}\;A\;n$ 读出；结论谈的是长度为 $\suc\;n$ 的向量，这从构造子的结果类型读出。脚本 `examples/generic-vec.leanmini`（[附录 E](e-leanmini-reference.md)）声明了这个类型，并检查了一个使用它的小项。

## 通用方法

本节给出处理带参数和索引的单个归纳类型的过程。Lean 还支持互归纳类型和嵌套归纳类型，它们不在本书范围之内。

这一过程还回答了 T-Const 留下的一个问题。没有体的常量是一条假设：T-Const 接受 $c : \tPi{P}{\Sort{0}}{P}$ 就像接受 $\zero : \Nat$ 一样轻易，而有了它，系统就不一致了。下面生成的常量不是任意的假设。它们是一个固定模式的实例，即归纳构造演算（Calculus of Inductive Constructions）的归纳类型，其一致性是已知的 [Werner 1994]。

**Telescope。** 我们用 $(\vec{x} : \vec{A})$ 表示一列绑定 $(x_1 : A_1) \cdots (x_k : A_k)$，其中每个 $A_i$ 可以提及 $x_1, \ldots, x_{i-1}$；用 $\tPi{\vec{x}}{\vec{A}}{B}$ 表示 $\tPi{x_1}{A_1}{\cdots\,\tPi{x_k}{A_k}{B}}$；用 $f\;\vec{x}$ 表示 $f\;x_1 \cdots x_k$。$\vec{x}$ 的长度记为 $|\vec{x}|$。在代码中，telescope 就是一个 `Context`，而 `src/term.rs` 中的 `telescope(binders, tail)` 构造嵌套的 $\Pi$。

**声明。** 一个声明引入类型构造器 $I$ 和构造子 $c_1, \ldots, c_n$：

$$
\begin{array}{rcll}
I &:& \tPi{\vec{p}}{\vec{P}}{\tPi{\vec{\imath}}{\vec{J}}{\Sort{u}}} & \\[2pt]
c_j &:& \tPi{\vec{p}}{\vec{P}}{\tPi{\vec{a}}{\vec{A}_j}{I\;\vec{p}\;\vec{t}_j}} & (j = 1, \ldots, n)
\end{array}
$$

**参数** $\vec{p}$ 由所有构造子共享，并在每个结果类型中原样出现。**索引** $\vec{\imath}$ 在不同构造子之间可以不同：索引项 $\vec{t}_j$ 可以提及 $\vec{p}$ 以及该构造子自己的参数 $\vec{a}$，后者称为它的**字段**。对于到目前为止的例子（构造子类型中省略了开头对参数的 $\Pi$）：

| 类型构造器 | 参数 | 索引 | 构造子 |
|---|---|---|---|
| $\Nat : \Sort{1}$ | 无 | 无 | $\zero : \Nat$, $\;\suc : \Nat \to \Nat$ |
| $\mathsf{Tree} : \Sort{1}$ | 无 | 无 | $\mathsf{leaf}$, $\mathsf{node}$, $\mathsf{branch}$ |
| $\mathsf{List} : \Sort{1} \to \Sort{1}$ | $(A : \Sort{1})$ | 无 | $\mathsf{nil} : \mathsf{List}\;A$, $\;\mathsf{cons} : A \to \mathsf{List}\;A \to \mathsf{List}\;A$ |
| $\mathsf{Vec} : \Sort{1} \to \Nat \to \Sort{1}$ | $(A : \Sort{1})$ | $(n : \Nat)$ | $\mathsf{vnil} : \mathsf{Vec}\;A\;\zero$, $\;\mathsf{vcons} : \tPi{n}{\Nat}{A \to \mathsf{Vec}\;A\;n \to \mathsf{Vec}\;A\;(\suc\;n)}$ |

**接受条件。** 只有当以下四个条件都成立时，内核才接受一个声明。

1. $I$ 的类型在当前签名中是一个类型。
2. 把 $I$ 加入签名后，每个构造子类型都是一个类型，并且以 $I\;\vec{p}\;\vec{t}_j$ 结尾，其中 $\vec{p}$ 恰好是按顺序排列的参数，且 $I$ 不出现在 $\vec{t}_j$ 中。
3. **严格正性。** 每个字段类型要么不提及 $I$，要么具有形式 $\tPi{\vec{y}}{\vec{B}}{I\;\vec{p}\;\vec{s}}$，其中 $I$ 既不出现在 $\vec{B}$ 中也不出现在 $\vec{s}$ 中。第二种形式的字段称为**递归的**。
4. **宇宙。** 若 $u \ge 1$，每个字段类型都位于某个 $\Sort{w}$ 中，且 $w \le u$。若 $u = 0$，则没有条件。

条件 2 让递归子可以统一地处理参数。条件 3 排除了诸如

```lean
inductive Bad where
  | mk : (Bad -> False) -> Bad
```

这样的声明，它的字段在箭头左侧提及了 `Bad`。对 `Bad` 做情形分析，就能定义 $f : \mathsf{Bad} \to \mathsf{False}$，令 $f\;(\mathsf{mk}\;g) = g\;(\mathsf{mk}\;g)$。于是 $f\;(\mathsf{mk}\;f)$ 是类型为 $\mathsf{False}$ 的闭项，并且它归约到自身，因此没有范式。对一个正在声明的类型 $\mathsf{Tree}$，一些字段类型及其状态如下：

| 字段类型 | 状态 | 原因 |
|---|---|---|
| $\Nat$ | 接受，非递归 | 不提及 $\mathsf{Tree}$ |
| $\mathsf{Tree}$ | 接受，递归 | 归纳假设 $M\;a_k$ |
| $\Nat \to \mathsf{Tree}$ | 接受，递归 | 产生树；假设为 $\tPi{n}{\Nat}{M\;(a_k\;n)}$ |
| $\mathsf{Tree} \to \Nat$ | 拒绝 | $\mathsf{Tree}$ 位于箭头左侧 |
| $\mathsf{List}\;\mathsf{Tree}$ | 在此拒绝 | 嵌套出现；Lean 接受它，但不在本书范围内 |

类型为 $\Nat \to \mathsf{Tree}$ 的字段是一棵有无穷多个孩子的树，每个数对应一个孩子；递归子仍然可以递归进入每个孩子 $a_k\;n$。类型为 $\mathsf{Tree} \to \Nat$ 的字段*消耗*树而不是包含树，正是这种形状使 `Bad` 导致悖论。

条件 4 防止一个类型包含更大的宇宙。没有它，带构造子 $\mathsf{mk} : \Sort{1} \to T$ 的声明 $T : \Sort{1}$ 就会把整个 $\Sort{1}$ 的一份副本放进 $\Sort{1}$ 里，这正是[第 13 章](13-universes.md)证明为不一致的自我包含。对 $u = 0$ 不需要条件，因为 $\Sort{0}$ 是非谓词的。

**递归子。** 对于被接受的声明，内核为每个可容许的层级 $v$（见下文）生成一个递归子 $I.\mathsf{rec}_v$：

$$
I.\mathsf{rec}_v :
\tPi{\vec{p}}{\vec{P}}{\;
\tPi{M}{(\tPi{\vec{\imath}}{\vec{J}}{I\;\vec{p}\;\vec{\imath} \to \Sort{v}})}{\;
\tPi{m_1}{C_1}{\cdots\,\tPi{m_n}{C_n}{\;
\tPi{\vec{\imath}}{\vec{J}}{\tPi{x}{I\;\vec{p}\;\vec{\imath}}{M\;\vec{\imath}\;x}}}}}}.
$$

参数在最前面并保持固定，如同列表的情形；motive 接受索引和元素，如同向量的情形。小前提 $C_j$ 要求构造子 $c_j$ 的情形：给定它的字段，以及每个递归字段的一个归纳假设，构造出 $c_j$ 应用于这些字段时的 $M$：

$$
\begin{array}{l}
C_j = \tPi{\vec{a}}{\vec{A}_j}{\;\tPi{\vec{h}}{\vec{H}_j}{\;M\;\vec{t}_j\;(c_j\;\vec{p}\;\vec{a})}}, \\[4pt]
H_{j,k} = \tPi{\vec{y}}{\vec{B}}{M\;\vec{s}\;(a_k\;\vec{y})}
\quad\text{for each recursive field } a_k : \tPi{\vec{y}}{\vec{B}}{I\;\vec{p}\;\vec{s}}.
\end{array}
$$

最后的参数是索引和元素 $x$ 本身，即大前提。

**规则。** 对每个构造子，内核生成一条 ι 规则，它把小前提应用于字段和归纳假设，后者由递归调用算出：

$$
I.\mathsf{rec}_v\;\vec{p}\;M\;\vec{m}\;\vec{\imath}\;(c_j\;\vec{p}\,'\;\vec{a}) \;\iotared\; m_j\;\vec{a}\;\vec{h},
\qquad
h_k = \tLam{\vec{y}}{\vec{B}}{I.\mathsf{rec}_v\;\vec{p}\;M\;\vec{m}\;\vec{s}\;(a_k\;\vec{y})}.
$$

大前提位于第 $|\vec{p}| + 1 + n + |\vec{\imath}|$ 个位置（从零数起），构造子有 $|\vec{p}|$ 个参数和 $|\vec{a}|$ 个字段，而在良类型的可归约式中 $\vec{p}\,'$ 可转换为 $\vec{p}$，所以规则忽略它，正如列表的规则忽略 $A'$。对 $\Nat$、$\mathsf{Tree}$、$\mathsf{List}$ 和 $\mathsf{Vec}$，这一过程恰好产生本章和上一章的递归子与规则，而且递归子的类型与 Lean 4 生成的一致，至多相差约束变量的名字和隐式参数。

**从命题消去。** 若 $u \ge 1$，则对每个层级 $v$ 都生成递归子。若 $u = 0$，即 $I$ 是命题，则只对 $v = 0$ 生成递归子，除非 $I$ 是**子单元**（subsingleton）：它至多有一个构造子，并且每个字段要么是证明（其类型位于 $\Sort{0}$ 中），要么出现在索引项 $\vec{t}_j$ 之中。这一限制使数据不会依赖于给出的是命题的*哪一个*证明。例如，$P \vee Q$ 有两个构造子，于是从 $P \vee Q$ 的证明到 $\Nat$ 的函数可以对其中一个返回 $0$、对另一个返回 $1$，证明便携带了计算信息。因此 Lean 的 `Or.rec` 和 `Exists.rec` 只消去到 `Prop`，而 `And.rec` 和 `Eq.rec` 可以消去到每个宇宙：`And` 只有一个构造子，其字段都是证明；`Eq`（[第 9 章](09-equality.md)）只有一个没有字段的构造子。

于是，签名不断增长而内核的规则保持不变：一个通用过程把每个声明变成签名条目，一个归约函数运行它们的规则（[第 12 章](12-reduction-conversion.md#computation-rules-as-data)）。

## 代码中

<aside class="code" markdown="1">

该过程位于 `src/inductive/` 中。输入是一个 `InductiveSpec`（`src/declaration.rs`）：名字、参数和索引的 telescope、宇宙层级 $u$，以及每个构造子对应的一个 `ConstructorSpec`，给出其字段和索引项 $\vec{t}_j$。脚本解析器从一个 `inductive` 块构造它。

- `src/inductive/mod.rs` 中的 `Kernel::add_inductive` 依次运行四个接受条件（`check_inductive_type` 是条件 1，`check_constructor_fields` 检查字段都是类型并执行条件 4，`check_constructor_result` 是条件 2），全部通过后注册类型构造器和构造子，并记录一个 `InductiveInfo`。失败时签名保持不变。
- `src/inductive/positivity.rs` 是条件 3。`check_recursive_field` 剥去字段类型开头的各个 $\Pi$，拒绝任何定义域提及 $I$ 的情况，并要求目标是 $I$ 恰好应用于参数变量，后跟不提及 $I$ 的索引项。它返回一个 `RecursiveFieldInfo`，记录 $\vec{y} : \vec{B}$ 和 $\vec{s}$，这正是递归子生成器所需的全部信息。
- `src/inductive/recursor.rs` 按上面的公式构造递归子类型。`recursor_type` 组装 telescope $\vec{p}$、motive、各小前提、索引和大前提；`minor_premise_type` 构造每个 $C_j$；`induction_hypothesis_type` 构造每个 $H_{j,k}$。生成的绑定子名字（`__motive`、`__minor_j`、`__ih_j_k`、`__major`）以两个下划线开头，用户声明不得使用这种名字，因此它们永远不会与字段冲突。
- `mod.rs` 中的 `allows_large_elimination` 实现子单元测试。`add_inductive` 总是注册 `I.rec0`，在允许大消去时还注册 `I.rec1`；`register_recursor` 按需生成更高的层级。

ι 规则不会生成为项。`whnf` 直接依据存储的 `InductiveInfo` 应用它们，[第 12 章](12-reduction-conversion.md)会解释这一点。

</aside>

生成器的核心短到可以通读。请把它与 $C_j$ 的公式对照。

```rust
/// C_j = Pi (as : As_j). Pi (hs : Hs_j). M ts_j (c_j ps as)
fn minor_premise_type(info: &InductiveInfo, j: usize, constructor: &ConstructorInfo) -> Term {
    // c_j ps as
    let constructor_application = apps(
        const_term(&constructor.name),
        info.params.iter().chain(constructor.fields.iter()).map(|(name, _)| var(name)),
    );
    // (as : As_j)，随后是 (hs : Hs_j)
    let mut minor_premise_binders = constructor.fields.clone();
    for (k, recursive_field) in constructor.recursive_fields.iter().enumerate() {
        minor_premise_binders.push((
            format!("{INDUCTION_HYPOTHESIS_PREFIX}{j}_{k}"),
            induction_hypothesis_type(constructor, recursive_field),
        ));
    }
    telescope(&minor_premise_binders, apply_motive(&constructor.result_indices, constructor_application))
}
```

内核从不对 $\Nat$ 做特殊处理。`src/kernel.rs` 中的 `Kernel::standard` 通过调用 `add_inductive` 来声明 $\Nat$ 和 $\mathsf{Eq}$，传入的 `InductiveSpec` 与用户脚本会产生的完全相同，所以图 7.1 是*生成*出来的，而不是硬编码的；`src/inductive/tests.rs` 中的测试检查生成的类型与手写的类型一致。

<aside class="warning" markdown="1">

正性检查是可靠性的要求，而不是为了方便。多年来 Lean、Coq 和 Agda 在内核的这一部分都出过错误，因为一般情形（嵌套和互归纳类型、宇宙约束、提及其他归纳类型的索引）十分复杂。我们受限的模式把检查控制在八十行以内。扩展它时，对每个新特性都要问同一个问题：该类型的值能否由一个消耗该类型的函数构造出来？

</aside>

## 练习

<div class="exercise" markdown="1">

为 `inductive Bool where | true | false` 写出递归子类型 $\mathsf{Bool.rec}_v$，并用它定义否定。

<details markdown="1">
<summary>解答</summary>

$\mathsf{Bool.rec}_v : \tPi{M}{\mathsf{Bool} \to \Sort{v}}{M\;\mathsf{true} \to M\;\mathsf{false} \to \tPi{b}{\mathsf{Bool}}{M\;b}}$，没有归纳假设，因为两个构造子都没有字段。否定是 $\tLam{b}{\mathsf{Bool}}{\mathsf{Bool.rec}_1\;(\tLam{\_}{\mathsf{Bool}}{\mathsf{Bool}})\;\mathsf{false}\;\mathsf{true}\;b}$。没有递归字段的类型，其递归子就是情形分析。

</details>

</div>

<div class="exercise" markdown="1">

以下各项分别被四个接受条件中的哪一个拒绝（如果有的话）？(a) `inductive T : Sort 1 where | mk (f : Sort 1)`。(b) `inductive T : Sort 1 where | mk (f : T -> T)`。(c) `inductive T : Sort 0 where | mk (f : Sort 1)`。

<details markdown="1">
<summary>解答</summary>

(a) 条件 4：字段 $\Sort{1}$ 的类型是 $\Sort{2}$，超过了 $u = 1$。(b) 条件 3：$T$ 出现在某个字段类型中箭头的左侧。(c) 接受：对 $u = 0$，条件 4 不施加任何要求，这个类型是一个把类型打包起来的命题；这是 $\Sort{0}$ 的非谓词性在起作用，而且它是无害的，因为 $T$ 只能消去到 $\Sort{0}$（它不是子单元，因为它的字段既不是证明也不是索引）。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 一个声明给出带参数和索引的类型构造器，以及带字段的构造子。参数自始至终固定；索引可变，并成为 motive 的参数。
- 递归子对每个构造子有一个小前提，其中每个递归字段对应一个归纳假设；每个构造子对应一条 ι 规则。
- 接受一个声明需要良构性、统一的参数、严格正性和宇宙上界。正性是保证递归终止、逻辑一致的关键。
- 命题只能消去到 $\Sort{0}$，除非它是子单元。
- 内核从数据生成这一切；它不含任何针对 $\Nat$ 的专门代码。

</div>
