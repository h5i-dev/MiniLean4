<div class="lead" markdown="1">

本章在几个小项上手工运行算法 5.1，并把每一次运行与类型规则对应起来。所选的例子覆盖了算法的各项工作：构造推导、抓出错误的证明、使用假设、实例化全称命题，以及在类型内部进行计算。下面的每一条追踪都可以在演练场中用内核复现。

</div>

要验证 $t$ 是定理 $T$ 的证明，内核调用 $\Check(\cdot, t, T)$；它调用 $\Infer(\cdot, t)$，再把结果与 $T$ 作比较。追踪展示了 $\Infer$ 发出的递归调用，以及每次调用所对应的类型规则。展开或折叠各节点即可跟随递归过程。

## 恒等证明

令 $\Gamma_1 = P : \Sort{0}$，$\Gamma_2 = \Gamma_1, h : P$。[第 1 章](01-propositions-as-types.md)开篇例子的推导，略去良构性前提后，是

$$
\dfrac{
  \dfrac{}{\cdot \vdash \Sort{0} : \Sort{1}}\rulename{T-Sort}
  \qquad
  \dfrac{
    \dfrac{}{\Gamma_1 \vdash P : \Sort{0}}\rulename{T-Var}
    \qquad
    \dfrac{}{\Gamma_2 \vdash h : P}\rulename{T-Var}
  }{\Gamma_1 \vdash \tLam{h}{P}{h} : P \to P}\rulename{T-Lam}
}{\cdot \vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{P \to P}}\rulename{T-Lam}
$$

算法自下而上构造出同一棵推导。调用 $\Infer(\cdot, \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}})$ 的过程如下。

<ul class="trace">
<li>$\Infer(\cdot,\; \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}})$ <span class="rule">T-Lam</span>
  <ul>
  <li>$\InferSort(\cdot,\; \Sort{0})$：$\Infer$ 返回 $\Sort{1}$，所以标注是一个类型 <span class="rule">T-Sort</span></li>
  <li>$\Freshen$ 保持 $P$ 不变，因为上下文为空</li>
  <li>$\Infer(\Gamma_1,\; \tLam{h}{P}{h})$ <span class="rule">T-Lam</span>
    <ul>
    <li>$\InferSort(\Gamma_1,\; P)$：$\Infer$ 查找 $P$ 并返回 $\Sort{0}$ <span class="rule">T-Var</span></li>
    <li>$\Freshen$ 保持 $h$ 不变</li>
    <li>$\Infer(\Gamma_2,\; h)$ 查找 $h$ 并返回 $P$ <span class="rule">T-Var</span></li>
    <li class="result">返回 $\tPi{h}{P}{P}$</li>
    </ul>
  </li>
  <li class="result">返回 $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$</li>
  </ul>
</li>
</ul>

每一次返回类型的调用都对应推导树的一个节点，而且没有任何调用用到计算。最后，$\Check$ 把结果与所声明的类型 $\tPi{P}{\Sort{0}}{P \to P}$ 作比较。两者只差一个约束变量的名字，因为 $P \to P$ 是 $\tPi{\_}{P}{P}$ 的缩写，而 $h$ 和 $\_$ 都不出现在体中。于是 $\IsDefEq$ 成功，证明被接受。

下面是由内核自己记录的同一次运行。调用视图与上面的列表一致；证明树视图与推导一致。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

<div class="playground" data-file="examples/identity.leanmini"><pre># 同一个证明，以完整的项给出。内核推断它的类型，
# 再与目标作比较。
goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : P) => h
qed</pre></div>

## 一个错误的证明

假设用户声称 $t = \tLam{P}{\Sort{0}}{\tLam{h}{P}{P}}$ 证明了 $\tPi{P}{\Sort{0}}{P \to P}$。它的体返回的是命题 $P$，而不是证明 $h$。内核调用 $\Check(\cdot, t, \tPi{P}{\Sort{0}}{P \to P})$，后者先调用 $\Infer$。各次调用与上面相同，只是最后一次 $\Infer(\Gamma_2, P)$ 返回 $\Sort{0}$。于是 $\Infer$ *成功*，结果为

$$
\Infer(\cdot, t) \;=\; \tPi{P}{\Sort{0}}{\tPi{h}{P}{\Sort{0}}}.
$$

项 $t$ 是良类型的，却不能证明所声称的命题。$\Check$ 比较这两个类型时，发现两边都无法继续归约，重命名约束变量也不能使它们相等：最内层的体一边是 $\Sort{0}$，另一边是 $P$。因此 $\IsDefEq$ 失败，$\Check$ 报告类型不匹配。（[第 11 章](11-substitution-alpha.md#alpha-equivalence)用 $\IsDefEq$ 的算法逐步重演这次比较。）

这个错误之所以能被发现，只是因为用户*声明*了要证明的命题。一个只运行 $\Infer$ 的内核会接受 $t$，并悄悄给它分配一个不同的类型。这就是为什么每个脚本都以 `goal` 开头，也是为什么 `qed` 要对照它来检查。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : P) => P"></div>

<div class="playground" data-file="wrong-proof"><pre>goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : P) => P
qed</pre></div>

<aside class="warning" markdown="1">

项是良类型的，并不表示它证明了所声称的定理。每个通过 $\Infer$ 的闭项都有一个推断出的类型；内核还须确认它与定理所声称的类型一致。策略（[第 10 章](10-tactics.md)）会在构造项之前固定要证明的命题。

</aside>

## 使用假设：肯定前件

到目前为止的例子从未应用过函数。考虑检查

$$
t = \tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{f}{P \to Q}{\tLam{p}{P}{f\;p}}}}
\quad\text{against}\quad
\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{(P \to Q) \to P \to Q}},
$$

它说的是“如果 $P$ 蕴涵 $Q$ 且 $P$ 成立，那么 $Q$ 成立”。四个 $\lambda$ 像之前一样把上下文扩展为 $\Gamma = P : \Sort{0},\; Q : \Sort{0},\; f : P \to Q,\; p : P$。体 $f\;p$ 进入 $\Infer$ 的应用分支：

<ul class="trace">
<li>$\Infer(\Gamma,\; f\;p)$ <span class="rule">T-App</span>
  <ul>
  <li>$\Infer(\Gamma,\; f)$ 返回 $P \to Q$，即 $\tPi{\_}{P}{Q}$。$\Whnf$ 保持它不变，它是一个 $\Pi$ <span class="rule">T-Var</span></li>
  <li>$\Check(\Gamma,\; p,\; P)$ 成功，因为 $p : P$ 在 $\Gamma$ 中 <span class="rule">T-Var, T-Conv</span></li>
  <li class="result">返回 $\subst{Q}{\_}{p} = Q$。名字 $\_$ 不出现在 $Q$ 中，所以替换什么也不做</li>
  </ul>
</li>
</ul>

如果用户写的是 $f\;f$，第二步就会调用 $\Check(\Gamma, f, P)$，它会失败，因为 $P \to Q$ 不是 $P$：在这里函数不能喂给它自己。试一试：把下面的 `f p` 改成 `f f`。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (Q : Sort 0) => fun (f : P -> Q) => fun (p : P) => f p"></div>

<div class="playground" data-file="modus-ponens"><pre>goal forall (P : Sort 0), forall (Q : Sort 0), (P -> Q) -> P -> Q
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (f : P -> Q) => fun (p : P) => f p
qed</pre></div>

## 实例化全称命题

在*依赖*应用中，T-App 里的替换会做实际的工作。令 $\mathit{id} = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ 为第一个例子中的证明，并令 $\Gamma = Q : \Sort{0}$。那么 $\Infer(\Gamma, \mathit{id}\;Q)$：

<ul class="trace">
<li>$\Infer(\Gamma,\; \mathit{id}\;Q)$ <span class="rule">T-App</span>
  <ul>
  <li>$\Infer(\Gamma,\; \mathit{id})$ 返回 $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$，已经是一个 $\Pi$ <span class="rule">T-Lam</span></li>
  <li>$\Check(\Gamma,\; Q,\; \Sort{0})$ 成功 <span class="rule">T-Var</span></li>
  <li class="result">返回 $\subst{(\tPi{h}{P}{P})}{P}{Q} = \tPi{h}{Q}{Q}$，即 $Q \to Q$</li>
  </ul>
</li>
</ul>

从逻辑上看，这是 $\forall$ 消去：从“每个命题都蕴涵自身”得到“$Q$ 蕴涵 $Q$”。结果的类型取决于参数 $Q$ 的*值*，这正是依赖 $\Pi$ 类型所表达的东西，也是 T-App 要做替换的原因。在浏览器中，$\mathit{id}$ 是一个已定义的常量，$Q$ 来自上下文；T-App 节点上的注释记录了这次替换。

<div class="explorer" data-kind="derive" data-term="id Q" data-ctx="Q : Sort 0"><pre class="prelude">def id : forall (P : Sort 0), P -> P := fun (P : Sort 0) => fun (h : P) => h</pre></div>

## 转换

回忆[第 3 章](03-typing-rules.md)中的 $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$。核心系统没有定义，所以 $\mathit{Id}\;P$ 是项 $(\tLam{X}{\Sort{0}}{X})\;P$ 的简写。考虑检查

$$
t = \tLam{P}{\Sort{0}}{\tLam{h}{\mathit{Id}\;P}{h}}
\quad\text{against}\quad
\tPi{P}{\Sort{0}}{P \to P}.
$$

$\Infer$ 首先检查标注 $\mathit{Id}\;P$ 是一个类型。$\InferSort(\Gamma_1, \mathit{Id}\;P)$ 进入 $\Infer$ 的应用分支：函数 $\tLam{X}{\Sort{0}}{X}$ 的类型是 $\tPi{X}{\Sort{0}}{\Sort{0}}$，参数 $P$ 通过 $\Check(\Gamma_1, P, \Sort{0})$，结果是 $\subst{\Sort{0}}{X}{P} = \Sort{0}$。所以 $\mathit{Id}\;P$ 是一个类型，而且是一个命题。接着体 $h$ 的类型是 $\mathit{Id}\;P$，于是

$$
\Infer(\cdot, t) \;=\; \tPi{P}{\Sort{0}}{\tPi{h}{\mathit{Id}\;P}{\mathit{Id}\;P}}.
$$

仅靠给约束变量改名，无法把它变成 $\tPi{P}{\Sort{0}}{P \to P}$。但 $\IsDefEq$ 在比较之前会先计算两边，而 $\mathit{Id}\;P \betared P$，所以推断出的类型变为 $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$，比较像第一个例子一样成功。在类型规则中，这一步是在推导根部使用一次 T-Conv：

$$
\dfrac{
  \cdot \vdash t : \tPi{P}{\Sort{0}}{\mathit{Id}\;P \to \mathit{Id}\;P}
  \qquad
  \cdot \vdash \tPi{P}{\Sort{0}}{P \to P} : \Sort{0}
  \qquad
  \tPi{P}{\Sort{0}}{\mathit{Id}\;P \to \mathit{Id}\;P} \conv \tPi{P}{\Sort{0}}{P \to P}
}{\cdot \vdash t : \tPi{P}{\Sort{0}}{P \to P}}\rulename{T-Conv}
$$

算法从不决定*在哪里*应用 T-Conv。正如[第 5 章](05-algorithm.md)所述，转换隐藏在对 $\IsDefEq$ 的调用中，而它只在比较两个类型的地方运行。

实时推导显示了计算发生的位置：标注 $\mathit{Id}\;P$ 由 T-App 检查，推断出的类型一直含有 $\mathit{Id}\;P$，直到 $\Check$ 把它与目标作比较。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : (fun (X : Sort 0) => X) P) => h"></div>

<div class="playground" data-file="conversion"><pre># h 的标注是 (fun (X : Sort 0) => X) P，它计算到 P。
goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : (fun (X : Sort 0) => X) P) => h
qed</pre></div>

## 练习

像上面的例子那样，手工对这些项运行 $\Infer$，是检验自己是否理解该算法的好办法。每一题也都可以在演练场中尝试。

<div class="exercise" markdown="1">

证明 $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q \to P}}$。

<details markdown="1">
<summary>解答</summary>

一个答案是 $\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{\tLam{q}{Q}{p}}}}$。这个证明从不使用 $q$：系统允许假设不被使用。

</details>

</div>

<div class="exercise" markdown="1">

证明蕴涵是传递的：
$\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{\tPi{R}{\Sort{0}}{(P \to Q) \to (Q \to R) \to P \to R}}}$。

<details markdown="1">
<summary>解答</summary>

一个答案以 $\tLam{f}{P \to Q}{\tLam{g}{Q \to R}{\tLam{p}{P}{g\;(f\;p)}}}$ 结尾；它两次用到应用分支，先是 $f\;p : Q$，然后是 $g\;(f\;p) : R$。

```leanmini
goal forall (P : Sort 0), forall (Q : Sort 0), forall (R : Sort 0), (P -> Q) -> (Q -> R) -> P -> R
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (R : Sort 0) => fun (f : P -> Q) => fun (g : Q -> R) => fun (p : P) => g (f p)
qed
```

</details>

</div>

<div class="exercise" markdown="1">

解释为什么 $\tLam{P}{\Sort{0}}{\tLam{h}{P}{h\;h}}$ 会被拒绝，以及在算法 5.1 的哪一行被拒绝。

<details markdown="1">
<summary>解答</summary>

在上下文 $P : \Sort{0}, h : P$ 中，体 $h\;h$ 进入应用分支。$\Infer$ 对函数 $h$ 返回 $P$，而 $\Whnf(P) = P$ 是一个变量，不是 $\Pi$。算法在 `else fail "not a function"` 这一行失败：$P$ 的证明不是可以被应用的东西。在 Rust 中，错误信息是 `application of non-function`。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 一次 $\Infer$ 的运行对应一棵推导树；每一次返回的调用就是一个节点。
- $\Infer$ 可以在一个并未证明所声明定理的项上成功。对照所声明的类型运行 $\Check$ 才能抓出这种情况。
- T-App 是使用假设（肯定前件）的地方，也是实例化全称命题（替换进 $\Pi$ 的体）的地方。
- 类型内部的计算完全由 $\IsDefEq$ 处理；算法从不选择在哪里应用 T-Conv。

</div>
