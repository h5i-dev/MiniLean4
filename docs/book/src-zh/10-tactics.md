<div class="lead" markdown="1">

Lean 用户很少手写第 9 章末尾那样的项。他们写策略脚本，即一系列命令，逐步构造项，同时系统显示还剩下什么要证。本章展示常见的策略如何在我们的系统中构造项，以及为什么它们都不需要被信任。

</div>

在 Lean 中，第 9 章的定理是这样证明的：

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
```

每个策略都是一个小程序，构造证明项的一部分。策略在内核*之外*运行，它们的输出是普通的项，内核用算法 5.1 像检查其他任何项一样检查它。

## 目标与证明状态

**目标** $\goal{\Gamma}{\hole{m}}{T}$ 要求在上下文 $\Gamma$ 中给出一个类型为 $T$ 的项。**洞** $\hole{m}$ 代表尚待找到的项；Lean 称之为*元变量*。**证明状态**是一个目标列表，连同一个**部分证明项**，即可能含有洞的项。

要证明 $T$，我们从部分项 $\hole{0}$ 和唯一的目标 $\goal{\cdot}{\hole{0}}{T}$ 出发。策略作用于第一个目标 $\goal{\Gamma}{\hole{m}}{T}$，给 $\hole{m}$ **赋值**一个可能含有新鲜洞的项，并把该目标替换为每个新鲜洞对应的一个新目标。当没有目标剩下时，部分项不再含洞，内核对照 $T$ 检查它。洞可以位于绑定子之下，如 $\tLam{x}{A}{\hole{1}}$ 中的 $\hole{1}$，填入它的项可以使用那些约束变量，这就是每个目标都带有自己的上下文的原因。

每个策略都必须确保它的赋值在 $\Gamma$ 中具有类型 $T$，前提是每个新鲜洞随后都被填入其目标所述类型的项。我们写 $\goal{\Gamma}{\hole{m}}{T} \leadsto \text{new goals}$，后跟赋值。

### 第一个例子

脚本 `examples/identity.leanmini` 证明第 1 章开头的例子。下面的浏览器逐条命令运行它。

<div class="explorer" data-kind="proof" data-title="证明浏览器：恒等"><pre class="script">goal forall (P : Sort 0), P -> P
intro P
intro p
exact p
qed</pre></div>

用按钮或方向键逐步执行。中间面板是每条命令之后的目标列表，右侧面板是部分证明项，当前目标的洞高亮显示。三个面板始终一致：策略改变目标，*正是因为*它给某个洞赋了一个项。

单有目标列表是不够的：`intro p` 之后，目标 $P$ 不记得它的解必须包在两个 $\lambda$ 里面，而部分项记录了这一点。

## 基本策略

**`intro x`。** 若 $T$ 规范化为 $\Pi$ 类型，该策略把它的参数移入上下文：

$$
\goal{\Gamma}{\hole{m}}{\tPi{y}{A}{B}} \;\leadsto\; \goal{\Gamma, x : A}{\hole{1}}{\subst{B}{y}{x}},
\qquad
\hole{m} \mathrel{:=} \tLam{x}{A}{\hole{1}}.
$$

由 T-Lam，赋值具有正确的类型。名字 $x$ 不能在 $\dom(\Gamma)$ 中；否则新假设会遮蔽已有的假设，这会使内核不可靠（[第 11 章](11-substitution-alpha.md#variable-capture-in-contexts)）。我们的 `intro` 拒绝这样的名字，并给出消息“binder name already in context”；Lean 则会重命名它。

**`exact t`。** 该策略用给定的项关闭目标：

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \text{no goals},
\qquad
\hole{m} \mathrel{:=} t,
$$

在此之前它自己先运行 $\Check(\Gamma, t, T)$。类型不正确的 $t$ 反正最后会被内核拒绝；提前检查只是为了给出更好的错误信息。

**`apply f`。** 若 $f$ 的类型为 $A_1 \to \cdots \to A_n \to B$ 且 $B \conv T$，该策略把各参数留作新目标：

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{A_1}, \ldots, \goal{\Gamma}{\hole{n}}{A_n},
\qquad
\hole{m} \mathrel{:=} f\;\hole{1} \cdots \hole{n}.
$$

由 $n$ 次 T-App，赋值具有类型 $B$；再由 T-Conv，具有类型 $T$。当 $f$ 的类型是依赖的 $\Pi$ 时，后面的 $A_i$ 和 $B$ 会提及前面的参数，策略必须通过把 $B$ 与 $T$ 匹配来找出这些参数。Lean 用*合一*做到这一点，求解元变量，而我们的受限版本只处理非依赖的箭头，其他情况报告“dependent apply requires elaboration/unification”。（当 $n = 0$，即 $f$ 的类型已经可转换为 $T$ 时，`apply f` 的行为与 `exact f` 相同。）

例如，蕴涵的传递性，即第 6 章的第二个练习，从结论反向推进：

<div class="explorer" data-kind="proof" data-title="证明浏览器：用 apply 证明传递性"><pre class="script">goal forall (P : Sort 0), forall (Q : Sort 0), forall (R : Sort 0), (P -> Q) -> (Q -> R) -> P -> R
intro P
intro Q
intro R
intro f
intro g
intro p
apply g
apply f
exact p
qed</pre></div>

六个 `intro` 之后，目标是 $\goal{\Gamma}{\hole{6}}{R}$，其中 $\Gamma = P, Q, R : \Sort{0},\; f : P \to Q,\; g : Q \to R,\; p : P$。没有假设的类型是 $R$，所以 `exact` 关不掉它，但 $g$ *以 $R$ 结尾*：`apply g` 赋值 $\hole{6} \mathrel{:=} g\;\hole{7}$ 并留下 $\hole{7} : Q$。同样，`apply f` 赋值 $\hole{7} \mathrel{:=} f\;\hole{8}$ 并留下 $\hole{8} : P$，由 `exact p` 关闭。所得项的体是 $g\;(f\;p)$。注意两个策略的区别：`exact g` 失败，因为 $g$ 的类型是 $Q \to R$ 而不是 $R$，而 `apply g` 把 $g$ 缺少的参数变成新目标。

**`change T'`。** 该策略把目标替换为一个定义相等的目标：

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{T'},
\qquad
\hole{m} \mathrel{:=} \hole{1},
$$

前提是 $T'$ 是类型且 $T' \conv T$。它不向项添加任何东西；只改变目标的显示方式，T-Conv 为它提供依据。需要 `change` 是因为 `rw`（见下文）只在 α 等价的意义下查找子项：只有经过计算才出现的子项，必须先用 `change` 暴露出来，如本章末尾的例子所示。

**`rfl`。** 若 $T$ 规范化为 $\Eq{u}\;A\;a\;b$ 且 $a \conv b$，该策略关闭目标：

$$
\goal{\Gamma}{\hole{m}}{\Eq{u}\;A\;a\;b} \;\leadsto\; \text{no goals},
\qquad
\hole{m} \mathrel{:=} \refl{u}\;A\;a.
$$

赋值的类型是 $\Eq{u}\;A\;a\;a$，它可转换为目标。所以 `rfl` 恰好证明那些由定义相等成立的等式（[第 9 章](09-equality.md)）。

## 归纳

设 $n : \Nat$ 是 $\Gamma$ 中的变量，且 $\Gamma \vdash T : \Sort{u}$。策略 `induction n` 把目标中的 $n$ 抽象出来形成 motive，并为每个构造子产生一个目标：

$$
\begin{array}{l}
\goal{\Gamma}{\hole{m}}{T}
\;\leadsto\;
\goal{\Gamma}{\hole{z}}{\subst{T}{n}{\zero}},\;
\goal{\Gamma, k : \Nat, \mathit{ih} : \subst{T}{n}{k}}{\hole{s}}{\subst{T}{n}{\suc\;k}}, \\[4pt]
\hole{m} \mathrel{:=} \NatRec{u}\;(\tLam{z}{\Nat}{\subst{T}{n}{z}})\;\hole{z}\;(\tLam{k}{\Nat}{\tLam{\mathit{ih}}{\subst{T}{n}{k}}{\hole{s}}})\;n.
\end{array}
$$

取 motive $M = \tLam{z}{\Nat}{\subst{T}{n}{z}}$，$\NatRec{u}\;M$ 的类型要求 $M\;\zero$ 和 $\tPi{k}{\Nat}{M\;k \to M\;(\suc\;k)}$，结果的类型为 $M\;n$。由 β，它们分别可转换为两个目标的类型以及 $T$。这一构造只有在名字新鲜、层级 $u$ 正确、且没有其他假设提及 $n$ 时才正确。

- motive 绑定一个新鲜的名字 $z$ 而不是 $n$：由于 $n$ 已在 $\Gamma$ 中，写 $\tLam{n}{\Nat}{T}$ 会遮蔽它，这正是第 11 章的陷阱。同样，$k$ 和 $\mathit{ih}$ 也必须新鲜。（我们的实现把 motive 的变量命名为 `ind_x`，当 `n` 已被占用时把后继的字段命名为 `k`，把假设命名为 `ih`。）
- motive 的层级 $u$ 来自目标的类型，由 $\InferSort$ 求得；对命题它是 $0$，而 $\NatRec{0}$ 就是归纳。
- 如果另一个假设提及 $n$，例如 $h : n = 2$，新目标仍然含有关于原来那个 $n$ 的 $h$，而 $\mathit{ih}$ 对它一无所言。此时目标是正确的，但可能无法证明。Lean 的 `induction` 会先把这类假设移回目标（*回退*它们），使之成为 motive 的一部分，而我们的版本要求后面的假设都不提及 $n$，否则报告“induction: revert dependent hypotheses first”。

该实现并非专门针对 $\Nat$，而是适用于任何没有索引的归纳类型：它从签名读出递归子的类型，为每个构造子剥下一个小前提，并把每个小前提变成一个目标，其上下文包含该构造子的字段和归纳假设。脚本 `examples/generic-list.leanmini` 把它用于用户声明的列表类型。

## 重写

设 $h : \Eq{u}\;A\;a\;b$，并设目标 $T$ 是命题。策略 `rw h` 分三步把目标中的 $a$ 替换为 $b$。

1. **抽象。** 选一个新鲜的 $x$，令 $C$ 为把 $T$ 中每处 $a$ 替换为 $x$ 所得的结果。出现位置按 α 等价而非按转换来查找；位于某个绑定子之下、且该绑定子绑定了 $a$ 的自由变量的出现会被跳过，因为在那里它指的是别的东西。
2. **检查 motive。** 检查 $\Gamma, x : A \vdash C : \Sort{0}$。这一步可能失败，见下文。
3. **构造项。** 新目标是 $\subst{C}{x}{b}$，即把 $a$ 替换为 $b$ 后的目标：
   $$
   \goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{\subst{C}{x}{b}},
   \qquad
   \hole{m} \mathrel{:=} \EqRec{u,0}\;A\;a\;(\tLam{x}{A}{C \to T})\;(\tLam{p}{T}{p})\;b\;h\;\hole{1}.
   $$

要看出赋值具有类型 $T$，记 motive 为 $N = \tLam{x}{A}{C \to T}$。由于 $\subst{C}{x}{a} = T$，项 $N\;a$ 可转换为 $T \to T$，恒等函数 $\tLam{p}{T}{p}$ 居于其中。沿着 $h$ 传输则给出 $N\;b$，它可转换为 $\subst{C}{x}{b} \to T$，再把它应用于 $\hole{1}$ 便得到 $T$。Lean 基于同样的思想构造另一个项 `Eq.mpr (congrArg (fun x => C) h)`，并且还会尝试用 `rfl` 关闭新目标；我们的版本把这交给显式的 `rfl`，这样两个步骤在脚本中都看得见。

**motive 类型不正确时。** 抽象 $a$ 可能破坏目标。令 $\Gamma = n : \Nat,\; h : n = 2,\; q : n = 0$，假设我们对目标 $\Eq{0}\;(n = 0)\;q\;q$ 运行 `rw h`，这是一个关于证明 $q$ 的陈述。抽象 $n$ 得到 $C = \Eq{0}\;(x = 0)\;q\;q$，它的类型不正确：$q$ 的类型是 $n = 0$ 而不是 $x = 0$，而 $q$ 本身无法被抽象。第 2 步失败，Lean 对同样的情形报告“motive is not type correct”。没有第 2 步，策略会产生一个被内核拒绝的项，这对可靠性无害，但对用户没有帮助。

<aside class="code" markdown="1">

策略是 `src/proof.rs` 中 `ProofState` 的方法。部分证明项是一个 `Template`（`src/template.rs`），即带有 `Hole(i)` 节点的项；`materialize` 代入各个解，若有洞未解则失败。`ProofState::replace` 执行一次赋值：它记录当前目标的解，并把新目标拼接到最前面。`intro`、`exact`、`apply`、`change`、`rfl`、`induction` 和 `rw` 各自遵循上面的描述；`rw` 用 `replace_exact` 做第 1 步、用 `check_transport` 做第 2 步；`finish` 就是 `qed`：它实体化项，并对照原始目标调用 `Kernel::check`。

</aside>

## 示例：用策略证明 0 + n = n

在我们的系统中，第 9 章的证明变成下面的脚本，它是 `examples/zero-add.leanmini` 加上 $\add$ 的定义（脚本把 $0 + n$ 写作 `add Nat.zero n`）。

<div class="explorer" data-kind="proof" data-title="证明浏览器：0 + n = n"><pre class="script">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
induction n
rfl
change Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ k)
rw ih
rfl
qed</pre></div>

观察部分项如何增长：`induction n` 插入带两个洞的 $\NatRec{0}$，`rfl` 填上第一个，`change` 不动项、只改写目标，`rw ih` 插入传输，留下一个洞给最后的 `rfl`。删掉 `change` 那一行再运行脚本，就能看到 `rw` 找不到它的左边。

<div class="playground" data-file="examples/zero-add.leanmini"><pre># 对第二个参数递归的加法：
#   add m zero     = m
#   add m (succ k) = succ (add m k)
def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n

# add zero n = n 不是定义相等，所以需要对 n 归纳。
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
induction n
# 基础情形：add zero zero 归约为 zero。
rfl
# 归纳步骤：把 add zero (succ k) 展开为 succ (add zero k)，然后使用 ih。
change Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ k)
rw ih
rfl
qed</pre></div>

这个项与第 9 章手写的项有两处不同：由于 `intro`，它以 $\tLam{n}{\Nat}{\ldots\;n}$ 开头；它的归纳步骤使用 `rw` 构造的 motive。两者都是同一命题的证明，内核不在乎收到的是哪一个。试着在演练场中删掉 `change` 那一行，读一读 `rw` 给出的错误。

## 为什么策略不需要被信任

内核检查最终的项，所以策略不必正确，系统也能保持可靠。有错误的策略可能失败，也可能产生类型不正确的项，后者会被内核拒绝；它不可能让内核接受一个假定理。策略自己执行的检查，如 `exact` 中的 $\Check$ 或 `rw` 中的 motive 检查，只是为了尽早、清楚地报告错误。

因此系统的可信部分很小：算法 5.1、第三部分的归约与比较函数，以及第 8 章构造签名的过程，而 `src/proof.rs` 和 `src/syntax.rs` 中的一切都在它之外。

Lean 的策略框架比这里勾勒的丰富得多：它有通过合一求解的元变量，有填入隐式参数并展开 `0 + n` 这类记法的繁饰器，有能回退依赖假设并处理带索引的族的 `induction`，还有 `simp` 这样的自动化。所有这些都在不可信的一侧：Lean 的内核和我们的一样，只会看到完整的项 [de Moura and Ullrich 2021]。

## 练习

<div class="exercise" markdown="1">

用策略通过归纳证明 $\tPi{n}{\Nat}{n = n}$，并解释为什么 `rfl` 能关闭两个情形。

<details markdown="1">
<summary>解答</summary>

这就是 `examples/nat-reflexivity.leanmini`：`intro n`、`induction n`、`rfl`、`rfl`、`qed`。基础目标是 $0 = 0$，归纳步骤的目标是 $\suc\;k = \suc\;k$；两边在语法上完全相同，所以定义相等平凡地成立。这里的归纳其实没有必要（`intro n` 之后一个 `rfl` 就够了），但它展示了目标的形状。

</details>

</div>

<div class="exercise" markdown="1">

写出当目标为 $\Eq{}\;\Nat\;a\;c$、假设为 $h : a = b$、上下文为 $a, b, c : \Nat$ 时 `rw` 产生的项。

<details markdown="1">
<summary>解答</summary>

抽象 $a$ 得到 $C = (x = c)$ 和新目标 $b = c$。赋值为
$\EqRec{1,0}\;\Nat\;a\;(\tLam{x}{\Nat}{(x = c) \to (a = c)})\;(\tLam{p}{a = c}{p})\;b\;h\;\hole{1}$，其中 $\hole{1} : b = c$。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 证明状态是一个目标列表加上一个带洞的部分项。策略给第一个洞赋值一个项，并为每个新鲜洞开一个新目标。
- `intro` 构造 $\lambda$，`exact` 填入一个项，`apply` 构造一个以洞为参数的应用，`change` 使用 T-Conv，`rfl` 使用 $\refl{}$。
- `induction` 把变量抽象成 motive 并应用递归子；`rw` 把左边抽象成 motive 并应用传输。
- 内核重新检查完整的项，所以策略在可信基之外。

</div>
