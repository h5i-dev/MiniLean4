<div class="lead" markdown="1">

解决变量命名问题后，就可以实现计算。我们定义三种归约，再用它们实现弱头规范化、完全规范化和定义相等。归纳类型的计算规则作为数据存放在签名中，因此一个归约函数就能处理所有已声明的归纳类型。

</div>

## 归约

把 $\lambda$ 抽象应用到参数上，其计算方式是把参数替换进约束变量：

$$
(\tLam{x}{A}{t})\;s \;\betared\; \subst{t}{x}{s}.
$$

这一步是 **β 归约**（beta-reduction），形如 $(\tLam{x}{A}{t})\;s$ 的子项是 **β 可归约式**（beta-redex）。第二部分又加入了两种步骤：**δ 归约**（delta-reduction），展开一个定义（[第 7 章](07-inductive-nat.md)）；**ι 归约**（iota-reduction），在构造子上运行递归子（图 7.1、图 9.1，以及[第 8 章](08-inductive-recipe.md)的通用规则）。每种步骤都允许在项内部的任何位置进行，我们用 $\to$ 表示任意一种的单步归约。没有任何步骤可以应用的项处于**范式**（normal form）。例如，令 $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$，则

$$
\tLam{h}{\mathit{Id}\;P}{(\tLam{y}{P}{y})\;h} \;\betared\; \tLam{h}{P}{(\tLam{y}{P}{y})\;h} \;\betared\; \tLam{h}{P}{h},
$$

最后一个项处于范式，而先归约内层的可归约式也会得到同样的结果。

## 转换

**定义相等**（definitional equality），又称**转换**（conversion），把计算结果相同的项视为同一个，差别只允许出现在约束变量的名字上。

<div class="definition" markdown="1">

**定义 12.1（转换）。** $s \conv t$ 是包含 $\alphaeq$ 和 $\to$、且在所有项构造器下封闭的最小等价关系。

</div>

要判定 $s \conv t$，内核把两个项都规范化，然后用 $\alphaeq$ 比较结果。这一做法依赖两个事实。

- 归约是**合流的**（confluent）：不同的归约顺序不会得到不同的范式。所以 $s \conv t$ 成立，恰当 $s$ 和 $t$ 的范式 α 等价；不需要去寻找某个巧妙的步骤序列。
- 每个良类型的项都**有**范式，所以规范化会终止。这对我们的系统成立，但它是一个深刻的定理（强规范化，[第 14 章](14-properties.md)）[Barendregt 1992]。

实用的内核还会限制归约步数，以免某个 bug 让它无限循环；我们的实现在 20,000 步后停下，并报错“reduction fuel exhausted”。

<aside class="intuition" markdown="1">

为什么用规范化来判定相等，而不是去搜索一条步骤链？因为合流性把一个存在性问题（“有没有某种办法让这两个项相等？”）变成了一个标准形问题（“它们的范式是否相同？”），而后者有直接的算法。代价是规范化可能很昂贵：一个展开后变成大项的定义会被完全展开，哪怕两边在第一个符号上就已不同。生产级内核用惰性比较来避免这一点，本章末尾会讨论。

</aside>

## 作为数据的计算规则

图 7.1 和图 9.1 把每条 ι 规则写成单独的等式，这似乎暗示每个新的归纳类型都需要在内核里添加新的归约代码。其实不然：内核把 ι 规则作为数据存放在签名中，紧挨着递归子，由一段代码统一地为所有归纳类型应用它们。

每个递归子条目记录了它的**大前提**（major premise）的位置，也就是由其构造子决定适用哪条规则的那个参数，以及它所属归纳类型的各个构造子。对每个构造子，内核知道开头有多少个参数是**参数**（parameter，规则忽略它们），有多少个是**字段**（field，规则把它们传下去），以及哪些字段是递归的。对我们的三个递归子，这些数据及其产生的右侧如下；$\lambda$ 上的类型标注已省略。

$$
\begin{array}{llcll}
\textbf{Recursor} & \textbf{Major} & \textbf{Constructor} & \textbf{Params, fields} & \textbf{Right-hand side} \\[2pt]
\NatRec{u} & \text{4th} & \zero & 0,\;0 & \lambda M\,z\,s.\; z \\[2pt]
& & \suc & 0,\;1 & \lambda M\,z\,s\,n.\; s\;n\;(\NatRec{u}\;M\;z\;s\;n) \\[2pt]
\EqRecDep{u,v} & \text{6th} & \refl{u} & 2,\;0 & \lambda A\,a\,M\,m\,b.\; m \\[2pt]
\mathsf{Tree.rec}_v & \text{5th} & \mathsf{leaf} & 0,\;0 & \lambda M\,m_1\,m_2\,m_3.\; m_1 \\[2pt]
& & \mathsf{node} & 0,\;1 & \lambda M\,m_1\,m_2\,m_3\,t.\; m_2\;t\;(\mathsf{Tree.rec}_v\;M\,m_1\,m_2\,m_3\;t) \\[2pt]
& & \mathsf{branch} & 0,\;2 & \lambda M\,m_1\,m_2\,m_3\,l\,r.\; m_3\;l\;r\;(\mathsf{Tree.rec}_v\;M\,m_1\,m_2\,m_3\;l)\;(\cdots\;r)
\end{array}
$$

右侧先接收大前提之前的那些参数，再接收构造子的字段。例如，$\NatRec{u}\;M\;z\;s\;(\suc\;n)$ 选中第二条规则，变成

$$
(\lambda M\,z\,s\,n.\; s\;n\;(\NatRec{u}\;M\;z\;s\;n))\;M\;z\;s\;n,
$$

它经过 β 归约后就是图 7.1 第二个等式的右侧。类似地，$\EqRecDep{u,v}$ 唯一的规则在 $\EqRecDep{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A'\;c)$ 上触发。构造子 $\refl{u}$ 有两个参数 $A'$ 和 $c$，没有字段，所以右侧只接收 $A\;a\;M\;m\;b$，并返回 $m$。

## 弱头范式与规范化

算法 12.1 定义了算法 5.1 留下未定的三个函数。$\Whnf$ 和 $\Normalize$ 都把项看成一条**脊**（spine）$h\;a_1 \cdots a_n$：一个不是应用的头部 $h$，施加于 $n \ge 0$ 个参数（[第 2 章](02-syntax.md)），而每个项恰有一种这样的分解。

<div class="rulebox" markdown="1">

<p class="caption">算法 12.1。带 β、δ、ι 的弱头规范化；完全规范化；以及定义相等。</p>

```text
Whnf(t):
  loop:
    write t as a spine h a_1 ... a_n
    if h = λ(x : A). b and n ≥ 1:                               -- beta
        t ← (b[x ↦ a_1]) a_2 ... a_n
    else if h = c and (c : C := d) ∈ Σ:                         -- delta
        t ← d a_1 ... a_n
    else if h = c is a recursor with major position p ≤ n:      -- iota
        k b_1 ... b_j ← Whnf(a_p)
        if k is a constructor of c's inductive type with q parameters:
            t ← rhs_k a_1 ... a_{p-1} b_{q+1} ... b_j a_{p+1} ... a_n
        else return t                                           -- stuck, e.g. on a variable
    else return t

Normalize(t):
  t ← Whnf(t)
  if t = Π(x : A). B:  return Π(x : Normalize(A)). Normalize(B)
  if t = λ(x : A). b:  return λ(x : Normalize(A)). Normalize(b)
  else write t as a spine h a_1 ... a_n and return h Normalize(a_1) ... Normalize(a_n)

IsDefEq(s, t):
  return  · ; · ⊢ Normalize(s) =α Normalize(t)                  -- Figure 11.1
```

</div>

$\Whnf$ 只在项的头部归约，直到那里没有规则可用为止；结果就是**弱头范式**（weak head normal form）。它从不深入 $\lambda$、$\Pi$ 的内部，也不深入卡住的头部的参数。当调用者只需要类型的最外层形状时（例如 $\Infer$ 的应用情形需要一个 $\Pi$），这就足够了，而且比完全规范化便宜。$\Normalize$ 先计算弱头范式，然后规范化每一个直接子项。例如，令 $t = \tLam{h}{\mathit{Id}\;P}{h}$，$\mathit{Id}$ 同上，则

$$
\Whnf(t) = t, \qquad \Normalize(t) = \tLam{h}{P}{h},
$$

因为 $t$ 的头部是一个不带参数的 $\lambda$，而 $\Normalize$ 会继续进入标注 $\mathit{Id}\;P$。类似地，$\Whnf(\mathit{Id}\;(\mathit{Id}\;P \to P)) = \mathit{Id}\;P \to P$，它已经显露出一个 $\Pi$，尽管其定义域还不是范式。下面可以同时看到这两点：头部没有任何步骤可用，范式却不同。

<div class="explorer" data-kind="reduce" data-term="fun (h : (fun (X : Sort 0) => X) P) => h" data-ctx="P : Sort 0"></div>

$\Whnf$ 的三种情形有如下性质。

- ι 情形完全不提及 $\Nat$、$\Eq{}$ 或 $\mathsf{Tree}$，而是从签名中读取大前提的位置和构造子数据。这段代码只写一次；此后每个新的归纳类型增加的是数据行，而不是代码。
- 大前提在查询规则*之前*先被化为弱头范式，因为它可能要经过计算才会变成构造子。对第 7 章的 $2 + 1$，大前提是数字 $1 = \suc\;\zero$，已经是构造子；对 $\mathit{double}\;(1 + 1)$，大前提是 $1 + 1$，$\Whnf$ 先把它变成 $\suc\;(1 + 0)$。
- 如果大前提没有变成构造子，比如它是一个变量，那么这个项就是**卡住的**（stuck），保持原样；这就是 $0 + n$ 不归约的原因（[第 9 章](09-equality.md)）。

下面是 $\Whnf$ 处理 $\mathit{double}\;(1 + 1)$ 的实时演算，$\mathit{double}$ 的定义同第 7 章。归约只发生在头部，但归约大前提会迫使一次内层计算。

<div class="explorer" data-kind="reduce" data-term="double (add (Nat.succ Nat.zero) (Nat.succ Nat.zero))"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def double : Nat -> Nat := fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) Nat.zero (fun (k : Nat) => fun (r : Nat) => Nat.succ (Nat.succ r)) n</pre></div>

标为 *whnf* 的那一步就是内层计算：递归子需要它的大前提是构造子，所以 $1 + 1$ 先在头部被归约。最终的弱头范式里仍含有一个卡住的内层递归子；它下方的范式则是 $\Normalize$ 继续向内归约得到的结果。

为简化实现，本书的 $\IsDefEq$ 会将两边完全规范化，而实用的内核则采用惰性比较：先把两边化为弱头范式并比较头部，只在必要时才检查参数，从而避免对头部已经不同的大项做完整规范化。强规范化保证这三个函数在良类型项上都会终止。

## 代码中

<aside class="code" markdown="1">

算法 12.1 对应 `src/reduction.rs`。`whnf`、`normalize` 和 `is_def_eq` 是薄薄的包装：它们分配燃料预算（`REDUCTION_FUEL = 20000`），然后调用 `whnf_with_fuel`、`normalize_with_fuel` 和 `is_def_eq_with_fuel`。`whnf_with_fuel` 中的循环是算法的直接转写：

```rust
let (head, args) = spine(&t);
let reduced = match head {
    // beta: (fun x. b) a_1 a_2 ... a_n  ~>  b[x := a_1] a_2 ... a_n
    Term::Lam(x, _, body) if !args.is_empty() => Some(apps(
        subst(&body, &x, &args[0]),
        args[1..].iter().cloned(),
    )),
    Term::Const(c) => match self.decls.get(&c) {
        // delta: c as  ~>  d as   其中 (c := d) 属于 Sigma
        Some(Decl { kind: DeclKind::Definition(body), .. }) => Some(apps(body.clone(), args)),
        // iota: I.rec ps M ms is (c_j ps' as)  ~>  m_j as hs
        Some(Decl { kind: DeclKind::Recursor(recursor), .. }) => {
            self.iota_reduce(&c, recursor, &args, fuel)?
        }
        _ => None,
    },
    _ => None,
};
match reduced {
    Some(next) => t = next,
    None => return Ok(t),
}
```

`iota_reduce` 在 `recursor.major_argument_index` 处找到大前提，把它化为弱头范式，检查其头部是所属归纳类型的构造子并且已施加了全部参数和字段，检查构造子的参数与递归子的参数可转换（良类型的可归约式保证了这一点，但内核选择验证而不是假设），然后构造 $m_j\;\vec{a}\;\vec{h}$，并在后面接上多余的参数。归纳假设 $\vec{h}$ 由 `induction_hypothesis` 构造：它用实际的参数和字段值实例化每个递归字段存储的 $\vec{y} : \vec{B}$ 和 $\vec{s}$，并把递归调用包进相应的 $\lambda$ 中。

实现并不像上表那样为每条规则存储一个右侧*项*，而是每次从 `InductiveInfo` 计算出右侧。两种做法等价；即时计算避免了维护构造子数据的第二份副本并保持同步。

</aside>

`normalize_with_fuel` 中有一处细节值得一提。在规范化应用的函数部分和参数部分之后，它会对重建后的项再调用一次 `whnf`，因为规范化参数可能在头部暴露出新的可归约式：对于一个卡住的递归子应用，如果它的大前提要等自身的参数规范化之后才*变成*构造子，那么头部必须再归约一次。少了这次复查，`is_def_eq` 会漏掉某些相等关系；`src/proof.rs` 中的测试 `conversion_renormalizes_exposed_redex` 守护着这一点。

## 练习

<div class="exercise" markdown="1">

给出 $(\tLam{f}{\Nat \to \Nat}{f})\;(\tLam{x}{\Nat}{x})\;\zero$ 的弱头范式和范式。

<details markdown="1">
<summary>解答</summary>

这条脊的头部是 $\tLam{f}{\Nat \to \Nat}{f}$，带两个参数。对第一个参数做 β 归约得到 $(\tLam{x}{\Nat}{x})\;\zero$，它的头部又是一个 β 可归约式，归约为 $\zero$。所以弱头范式和范式都是 $\zero$。（这正是测试 `conversion_renormalizes_exposed_redex` 中的项。）

</details>

</div>

<div class="exercise" markdown="1">

为什么 $\Whnf$ 不在 $\lambda$ 之下归约？如果 $\Whnf$ 返回的 $\tLam{x}{A}{b}$ 中 $b$ 已经规范化，$\Infer$ 会出什么问题？

<details markdown="1">
<summary>解答</summary>

不会出任何*错误*：结果仍然可转换为输入，但这是浪费工作。$\Infer$ 调用 $\Whnf$ 只是为了知道最外层的形状，而头部一旦是 $\lambda$，形状就已经可见。向内归约可能代价任意大，比如在一个从不与任何东西比较的标注里。让 $\Whnf$ 保持浅层，才能让大项上的类型推断保持廉价。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- 三种归约步骤：β（应用 $\lambda$）、δ（展开定义）、ι（在构造子上运行递归子）。转换是它们与 α 等价一起生成的等价关系。
- 转换的判定方法是把两边规范化，再在 α 等价意义下比较；其正确性来自合流性，其终止性来自强规范化。
- ι 规则是数据：大前提的位置加上构造子的元数据。一个 `whnf` 服务于所有归纳类型。
- Whnf 只在头部归约，是 Infer 所需要的；Normalize 深入每个角落，是 IsDefEq 所使用的。步数预算防范 bug。

</div>
