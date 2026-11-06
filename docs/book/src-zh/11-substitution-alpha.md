<div class="lead" markdown="1">

前几章把项上的三种操作当作黑盒：替换（substitution），T-App、Freshen 和每一步计算都要用它；弱头规范化（weak head normalization），用来把 $\Pi$ 或宇宙暴露出来；定义相等（definitional equality），Check 要用它。这三种操作都属于可信内核，而内核的多数 bug 就藏在其中，因为它们必须正确处理约束变量的名字。本章打开第一个黑盒，即替换，接着展示同样的命名问题如何出现在上下文里，最后定义两个项何时在约束变量的名字意义下相等。

</div>

## 自由变量与替换

$\Pi$ 和 $\lambda$ 会*绑定*它们的变量：在 $\tLam{x}{A}{t}$ 中，$t$ 内部出现的 $x$ 指的是参数。绑定子的作用域只有函数体；$x$ 在标注 $A$ 中并不受绑定。一个变量出现若不被任何外层的 $\Pi$ 或 $\lambda$ 绑定，就是*自由的*。

<div class="definition" markdown="1">

**定义 11.1（自由变量）。**

$$
\begin{array}{rclcrcl}
\FV(\Sort{u}) &=& \emptyset &\qquad& \FV(\tPi{x}{A}{B}) &=& \FV(A) \cup (\FV(B) \setminus \{x\}) \\[2pt]
\FV(x) &=& \{x\} && \FV(\tLam{x}{A}{t}) &=& \FV(A) \cup (\FV(t) \setminus \{x\}) \\[2pt]
\FV(t\;s) &=& \FV(t) \cup \FV(s) && \FV(c) &=& \emptyset
\end{array}
$$

</div>

例如，$\FV(\tLam{x}{P}{f\;x\;y}) = \{P, f, y\}$，而 $\FV(\tPi{P}{\Sort{0}}{P \to P}) = \emptyset$，所以后者是一个*封闭*项。常量永远不会被绑定，因此不贡献任何自由变量。

下面的浏览器（explorer）把每个约束变量涂成与其绑定子相同的颜色，并给自由变量加下划线；把鼠标悬停在变量上可以看到它的绑定子。试试带遮蔽的项，例如 `fun (x : A) => fun (x : A) => x`。

<div class="explorer" data-kind="scope" data-term="fun (x : P) => f x y"></div>

我们用 $\subst{t}{x}{s}$ 表示把 $t$ 中自由出现的 $x$ 替换为 $s$ 的结果。唯一微妙的情形是遇到绑定子。考虑 $\subst{(\tLam{y}{A}{x})}{x}{y}$。函数体的意思是“忽略参数，返回外层的 $x$”。若直接把 $x$ 换成 $y$，得到 $\tLam{y}{A}{y}$，即恒等函数，含义完全不同：自由的 $y$ 被绑定子**捕获**了。替换必须先给绑定子改名，以避免这种情况。

<div class="definition" markdown="1">

**定义 11.2（避免捕获的替换）。** 对 $\square \in \{\Pi, \lambda\}$：

$$
\begin{array}{rcll}
\subst{x}{x}{s} &=& s \\[2pt]
\subst{y}{x}{s} &=& y & (y \neq x) \\[2pt]
\subst{\Sort{u}}{x}{s} &=& \Sort{u} \\[2pt]
\subst{c}{x}{s} &=& c \\[2pt]
\subst{(t_1\;t_2)}{x}{s} &=& \subst{t_1}{x}{s}\;\;\subst{t_2}{x}{s} \\[2pt]
\subst{(\square(x{:}A).\,B)}{x}{s} &=& \square(x{:}\subst{A}{x}{s}).\,B & \text{($x$ is shadowed)} \\[2pt]
\subst{(\square(y{:}A).\,B)}{x}{s} &=& \square(y{:}\subst{A}{x}{s}).\,\subst{B}{x}{s} & (y \neq x,\; y \notin \FV(s)) \\[2pt]
\subst{(\square(y{:}A).\,B)}{x}{s} &=& \square(z{:}\subst{A}{x}{s}).\,\subst{(\subst{B}{y}{z})}{x}{s} & (y \neq x,\; y \in \FV(s),\; z \text{ fresh})
\end{array}
$$

这里“$z$ fresh”（新鲜）的意思是 $z \notin \FV(s) \cup \FV(B) \cup \{x\}$。

</div>

下面的例子逐一覆盖绑定子的各种情形。

| 替换 | 结果 | 原因 |
|---|---|---|
| $\subst{(\tPi{h}{P}{P})}{P}{Q}$ | $\tPi{h}{Q}{Q}$ | 不可能发生捕获；这是第 6 章的 T-App 步骤 |
| $\subst{(\tLam{x}{A}{x})}{x}{s}$ | $\tLam{x}{A}{x}$ | $x$ 被遮蔽；函数体保持不动 |
| $\subst{(\tLam{y}{x}{y})}{x}{s}$ | $\tLam{y}{s}{y}$ | 标注在 $y$ 的作用域之外 |
| $\subst{(\tLam{y}{A}{x\;y})}{x}{f\;y}$ | $\tLam{z}{A}{f\;y\;z}$ | $y \in \FV(f\;y)$，所以绑定子被改名为 $z$ |

在最后一个例子里，替换项中的自由 $y$ 仍然指向外层的 $y$，而约束变量（现在叫 $z$）仍然指向参数。若不改名，结果会是 $\tLam{y}{A}{f\;y\;y}$，它把参数传了两次。下面的浏览器并排执行这两种替换；颜色显示结果中的 $y$ 究竟是替换项里的自由变量，还是被绑定子捕获的那个。

<div class="explorer" data-kind="subst" data-term="fun (y : A) => x y" data-var="x" data-with="f y"></div>

<aside class="code" markdown="1">

定义 11.1 和 11.2 对应 `src/substitution.rs` 中的 `fv` 和 `subst`。下面是 `subst` 的绑定子情形。与定义相比，它多了一条捷径：如果 $x$ 在函数体中完全没有自由出现，就原样返回函数体，省掉一次遍历，且不会改变结果。

```rust
Term::Pi(y, domain, body) | Term::Lam(y, domain, body) => {
    let substituted_domain = subst(domain, x, replacement);
    let (renamed_binder, substituted_body) = if y == x || !fv(body).contains(x) {
        (y.clone(), (**body).clone())                       // shadowed, or nothing to do
    } else if !fv(replacement).contains(y) {
        (y.clone(), subst(body, x, replacement))            // no capture possible
    } else {
        let mut avoid = all_names(body);                    // capture: rename y to a fresh z
        avoid.extend(all_names(domain));
        avoid.extend(all_names(replacement));
        avoid.insert(x.to_string());
        let z = fresh(y, &avoid);
        let body_with_z = subst(body, y, &var(&z));
        (z, subst(&body_with_z, x, replacement))
    };
    // ... 用 renamed_binder、substituted_domain、substituted_body 重建 Pi 或 Lam
}
```

`fresh` 函数不断在提示名后面追加撇号，直到得到一个未被使用的名字。避让集合由 `all_names` 给出，它收集相关各项中的所有名字，而不只是自由名字。这比定义所要求的更多，但能让输出更易读。

</aside>

## 上下文中的变量捕获

人们很容易想去掉 C-Ext 的附加条件 $x \notin \dom(\Gamma)$，让新假设直接遮蔽旧假设，就像大多数编程语言那样。这样做会使内核不可靠。考虑

$$
t = \tLam{x}{\Sort{0}}{\tLam{y}{x}{\tLam{x}{\Sort{0}}{y}}}.
$$

变量 $y$ 的类型是*外层*的 $x$，而最内层的 $\lambda$ 忽略自己的参数。所以 $t$ 的正确类型是

$$
\tPi{x}{\Sort{0}}{\tPi{y}{x}{\tPi{x'}{\Sort{0}}{x}}}.
$$

一个没有 $\Freshen$ 的检查器会在上下文 $x : \Sort{0},\; y : x,\; x : \Sort{0}$ 中查找 $y$，并返回它的类型，也就是光秃秃的名字 $x$。此时 $x$ 指的是内层绑定子，于是检查器返回

$$
\tPi{x}{\Sort{0}}{\tPi{y}{x}{\tPi{x}{\Sort{0}}{x}}},
$$

它的意思是“从任意类型的任意元素出发，可以造出每一个类型的元素”。给定 $A : \Sort{0}$ 和 $a : A$，项 $t\;A\;a$ 的类型就是 $\tPi{B}{\Sort{0}}{B}$，即 False 的一个证明。而这样的 $A$ 和 $a$ 在空上下文中就已存在：$A = \tPi{P}{\Sort{0}}{P \to P}$ 本身就是一个命题，恒等函数 $a = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ 证明了它。

有了 $\Freshen$，最内层的绑定子在进入上下文之前会被改名为 $x'$，上下文因此变成 $x : \Sort{0},\; y : x,\; x' : \Sort{0}$。查找 $y$ 返回 $x$，它仍然指向外层绑定子，于是 $\Infer$ 返回上面那个正确的类型。推导浏览器会展示这次改名：最内层 T-Lam 节点上的注记报告了它，叶子节点的上下文中也出现了 $x'$。

<div class="explorer" data-kind="derive" data-term="fun (x : Sort 0) => fun (y : x) => fun (x : Sort 0) => y"></div>

<div class="playground" data-file="capture"><pre># 内核把内层的 x 改名为 x'，并推断出正确的类型。
# 如果内核允许内层的 x 遮蔽外层的 x，它就会接受这个项
# 作为第二个陈述的证明，而第二个陈述是假的。
goal forall (x : Sort 0), forall (y : x), forall (x' : Sort 0), x
exact fun (x : Sort 0) => fun (y : x) => fun (x : Sort 0) => y
qed
goal forall (x : Sort 0), forall (y : x), forall (x' : Sort 0), x'
exact fun (x : Sort 0) => fun (y : x) => fun (x : Sort 0) => y
qed</pre></div>

这个问题和替换中的问题是同一个：一个名字被移进了另一个作用域，而它在那里的含义变了。任何按名字识别变量的表示方式都会受影响，无论上下文是列表还是哈希表。常见的补救办法有三种。

1. 直接拒绝遮蔽。这是最简单的做法，但 $A \to B$ 使用的保留名 `_` 必须例外，且永远不加入上下文。
2. 进入时改名，也就是 $\Freshen$ 的做法。这是我们的选择。
3. 用位置表示约束变量（**de Bruijn 索引** [de Bruijn 1972]），或采用*局部无名*（locally nameless）风格：约束变量用索引，自由变量带唯一标识符。Lean 4 采用后一种方式。

测试套件应当包含上面的 $t$，并检查内核要么拒绝它，要么给它赋予正确的类型。

<aside class="warning" markdown="1">

这个 bug 容易写出来，却很难被发现，因为所有普通的证明照样能通过检查。只有刻意在嵌套绑定子中重用名字的项才会暴露它。内核的测试套件需要对抗性的项，而不只是正确的证明。

</aside>

## α 等价

约束变量的名字不携带任何含义。$\tLam{x}{A}{x}$ 和 $\tLam{y}{A}{y}$ 是同一个函数，$\tPi{P}{\Sort{0}}{P \to P}$ 和 $\tPi{Q}{\Sort{0}}{Q \to Q}$ 是同一个命题。只在约束变量名字上有差别的项称为 **α 等价**（alpha-equivalent）的。内核不能用单纯的语法相等来比较类型，否则第二对项就会被拒绝。

<div class="definition" markdown="1">

**定义 11.3（α 等价）。** $\alphaeq$ 是项上最小的合同关系，使得对 $\square \in \{\Pi, \lambda\}$，

$$
\square(x{:}A).\,B \;\alphaeq\; \square(y{:}A).\,\subst{B}{x}{y}
\qquad \text{whenever } y \notin \FV(B).
$$

</div>

（*合同关系*（congruence）是指被每个项构造器保持的等价关系：各部分相关，则整体相关。）这个定义容易陈述，却不能直接执行，因为它没有说该选哪些名字。实现的做法是同步遍历两个项，并为每一侧记住到目前为止经过的绑定子列表。这样，约束变量就由它指向*哪一个*绑定子来识别，而不是由名字。

为了描述这个遍历过程，我们使用形如 $E_1; E_2 \vdash s \alphaeq t$ 的判断，其中 $E_1$ 和 $E_2$ 是名字列表。$E_1$ 记录包围 $s$ 的绑定子，从最外层到最内层；$E_2$ 记录包围 $t$ 的绑定子。这个判断读作：“放在绑定子 $E_1$ 之内的 $s$ 与放在绑定子 $E_2$ 之内的 $t$，在约束变量名字的意义下是同一个项”。之所以需要两个列表，是因为两个项对应的绑定子可能使用不同的名字。例如，比较 $\tLam{x}{A}{\tLam{y}{B}{x}}$ 与 $\tLam{a}{A}{\tLam{b}{B}{a}}$ 时，两侧各经过两个绑定子，到达

$$
x, y;\; a, b \vdash x \alphaeq a,
$$

它成立，因为 $x$ 和 $a$ 都指向两个绑定子中外层的那个。比较两个完整的项时从空列表出发：$\cdot\,;\cdot \vdash s \alphaeq t$。

为了把“同一个绑定子”说精确，令 $\mathrm{idx}(E, x)$ 为 $x$ 在 $E$ 中*最后一次*出现的位置，从右边开始、自 $0$ 起计数；若 $x \notin E$ 则无定义。在上面的例子中，$\mathrm{idx}((x, y), x) = \mathrm{idx}((a, b), a) = 1$。取最后一次出现是为了处理遮蔽：在 $\tLam{x}{A}{\tLam{x}{B}{x}}$ 中，函数体指的是内层的 $x$。

<div class="rulebox" markdown="1">

<p class="caption">图 11.1。算法化的 α 等价。由定理 11.4，两个项 $s$ 和 $t$ α 等价当且仅当 $\cdot\,;\cdot \vdash s \alphaeq t$。</p>

$$
\dfrac{}{E_1; E_2 \vdash \Sort{u} \alphaeq \Sort{u}}\rulename{$\alpha$-Sort}
\qquad
\dfrac{}{E_1; E_2 \vdash c \alphaeq c}\rulename{$\alpha$-Const}
$$

$$
\dfrac{\mathrm{idx}(E_1, x) = \mathrm{idx}(E_2, y) = i}{E_1; E_2 \vdash x \alphaeq y}\rulename{$\alpha$-Bound}
\qquad
\dfrac{x \notin E_1 \qquad x \notin E_2}{E_1; E_2 \vdash x \alphaeq x}\rulename{$\alpha$-Free}
$$

$$
\dfrac{E_1; E_2 \vdash A \alphaeq A' \qquad E_1, x;\; E_2, y \vdash B \alphaeq B'}{E_1; E_2 \vdash \tPi{x}{A}{B} \alphaeq \tPi{y}{A'}{B'}}\rulename{$\alpha$-Pi}
$$

$$
\dfrac{E_1; E_2 \vdash A \alphaeq A' \qquad E_1, x;\; E_2, y \vdash t \alphaeq t'}{E_1; E_2 \vdash \tLam{x}{A}{t} \alphaeq \tLam{y}{A'}{t'}}\rulename{$\alpha$-Lam}
\qquad
\dfrac{E_1; E_2 \vdash t_1 \alphaeq t_1' \qquad E_1; E_2 \vdash t_2 \alphaeq t_2'}{E_1; E_2 \vdash t_1\;t_2 \alphaeq t_1'\;t_2'}\rulename{$\alpha$-App}
$$

</div>

自由变量按名字比较（$\alpha$-Free），约束变量按位置比较（$\alpha$-Bound），常量按名字比较（$\alpha$-Const）。一侧受绑定、另一侧自由的变量不与任何东西相等，所以这种情形没有规则。由于两侧总是一起穿过绑定子，$E_1$ 和 $E_2$ 的长度始终相同。因此，从右数位置与从左数位置是一回事，实现可以把每个列表存成从名字到绑定深度的映射，只要离开绑定子时恢复先前的条目即可。如果*处处*都用位置代替名字，就得到 **de Bruijn 表示**：在这种表示下，α 等价的项在语法上完全相同。

### 示例

第 6 章的第一个例子最后比较了推断出的类型与声明的类型，其中 $P \to P$ 是 $\tPi{\_}{P}{P}$ 的缩写：

<ul class="trace">
<li>$\cdot\,;\cdot \vdash \tPi{P}{\Sort{0}}{\tPi{h}{P}{P}} \alphaeq \tPi{P}{\Sort{0}}{\tPi{\_}{P}{P}}$ <span class="rule">$\alpha$-Pi</span>
  <ul>
  <li>$\cdot\,;\cdot \vdash \Sort{0} \alphaeq \Sort{0}$：成立 <span class="rule">$\alpha$-Sort</span></li>
  <li>$P;\, P \vdash \tPi{h}{P}{P} \alphaeq \tPi{\_}{P}{P}$ <span class="rule">$\alpha$-Pi</span>
    <ul>
    <li>$P;\, P \vdash P \alphaeq P$：成立，两侧的索引都是 $0$ <span class="rule">$\alpha$-Bound</span></li>
    <li>$P, h;\; P, \_ \vdash P \alphaeq P$：成立，两侧的索引都是 $1$ <span class="rule">$\alpha$-Bound</span></li>
    </ul>
  </li>
  </ul>
</li>
</ul>

名字 $h$ 和 $\_$ 不同，但两者都从未被查找，所以无关紧要。第 6 章的那个错误证明则在最后一步失败：

<ul class="trace">
<li>$\cdot\,;\cdot \vdash \tPi{P}{\Sort{0}}{\tPi{h}{P}{\Sort{0}}} \alphaeq \tPi{P}{\Sort{0}}{\tPi{\_}{P}{P}}$ <span class="rule">$\alpha$-Pi</span>
  <ul>
  <li>$\cdot\,;\cdot \vdash \Sort{0} \alphaeq \Sort{0}$：成立 <span class="rule">$\alpha$-Sort</span></li>
  <li>$P;\, P \vdash \tPi{h}{P}{\Sort{0}} \alphaeq \tPi{\_}{P}{P}$ <span class="rule">$\alpha$-Pi</span>
    <ul>
    <li>$P;\, P \vdash P \alphaeq P$：成立 <span class="rule">$\alpha$-Bound</span></li>
    <li class="fail">$P, h;\; P, \_ \vdash \Sort{0} \alphaeq P$：没有规则适用</li>
    </ul>
  </li>
  </ul>
</li>
</ul>

位置还能区分那些粗心地按名字比较时会混淆的项。$\tLam{x}{A}{\tLam{y}{A}{x}}$ 和 $\tLam{a}{A}{\tLam{b}{A}{b}}$ *不是* α 等价的：两个函数体到达 $x, y;\, a, b \vdash x \alphaeq b$，而 $\mathrm{idx}$ 给 $x$ 的值是 $1$，给 $b$ 的值却是 $0$。反过来，$\tLam{x}{A}{\tLam{x}{A}{x}}$ 和 $\tLam{a}{A}{\tLam{b}{A}{b}}$ *是* α 等价的，因为 $x$ 在 $(x, x)$ 中最后一次出现的索引是 $0$，与 $b$ 在 $(a, b)$ 中的索引相同。

图 11.1 的规则与定义 11.3 是两个不同的定义，所以我们必须检查它们一致。

<div class="theorem" markdown="1">

**定理 11.4（算法化 α 等价的正确性）。** 对所有项 $s$ 和 $t$，$s \alphaeq t$ 在定义 11.3 的意义下成立，当且仅当 $\cdot\,;\cdot \vdash s \alphaeq t$ 可由图 11.1 的规则推导出来。

</div>

证明的思路是，两边说的是同一件事：$s$ 和 $t$ 有相同的 de Bruijn 表示。对算法而言这几乎是显然的，因为它的规则比较位置的方式正是 de Bruijn 索引的方式。对定义 11.3 而言，关键事实是给约束变量改名不改变 de Bruijn 表示。[附录 B](b-proof-alpha.md) 给出完整证明。

<aside class="code" markdown="1">

图 11.1 对应 `src/substitution.rs` 中的函数 `alpha`。两个绑定子列表是两个 `Vec<String>`，在对函数体递归调用的前后分别压入和弹出；`binder_distance` 就是 $\mathrm{idx}$：它从列表末尾开始搜索，所以最先找到的是距离最近的同名外层绑定子。

```rust
(Term::Var(x), Term::Var(y)) => {
    match (binder_distance(bound_a, x), binder_distance(bound_b, y)) {
        (Some(i), Some(j)) => i == j,     // alpha-Bound
        (None, None) => x == y,           // alpha-Free
        _ => false,                       // bound on one side only
    }
}
```

</aside>

## 练习

<div class="exercise" markdown="1">

逐步计算 $\subst{(\tLam{y}{A}{\tLam{x}{B}{x\;y}})}{x}{y}$。

<details markdown="1">
<summary>解答</summary>

外层绑定子是 $y$，它在替换项 $y$ 中自由出现，所以适用捕获情形：把 $y$ 改名为新鲜的 $z$，得到函数体 $\tLam{x}{B}{x\;z}$，然后再替换。内层绑定子是 $x$，正是被替换的变量，所以内层函数体保持不动。结果：$\tLam{z}{A}{\tLam{x}{B}{x\;z}}$。注意内层的 $x$ 从来不是自由出现，所以实际上什么都没被替换；唯一的效果是避免捕获所强制的改名。

</details>

</div>

<div class="exercise" markdown="1">

运行图 11.1 的规则，判断 $\tLam{x}{A}{\tLam{y}{A}{y\;x}}$ 与 $\tLam{y}{A}{\tLam{x}{A}{x\;y}}$ 是否 α 等价。

<details markdown="1">
<summary>解答</summary>

是。经过两步 $\alpha$-Lam 之后，列表分别是 $x, y$ 和 $y, x$，函数体分别是 $y\;x$ 和 $x\;y$。$\alpha$-App 先比较 $y$ 与 $x$：索引为 $0$ 和 $0$。再比较 $x$ 与 $y$：索引为 $1$ 和 $1$。两者都成立。名字互换了，位置却一致。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 替换只替换自由出现；当替换项提到绑定子的名字时（捕获），必须给绑定子改名。
- 同样的捕获问题也出现在上下文中。允许绑定子遮蔽上下文条目的内核可以证明 False；Freshen 防止了这一点。
- α 等价按绑定子的位置比较约束变量，按名字比较自由变量。图 11.1 是算法；定理 11.4 说明它与定义一致。
- 这三者都在 `src/substitution.rs` 中：`subst`、`fv` 和 `alpha`。

</div>
