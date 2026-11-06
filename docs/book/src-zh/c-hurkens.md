<div class="lead" markdown="1">

[第 13 章](13-universes.md)断言：若一个宇宙包含自身，类型理论就会变得不一致，也就是存在一个类型为 $\tPi{p}{\mathsf{Type}}{p}$ 的闭项，它是对一切命题的证明。本附录完整给出这个项，解释其背后的思想，并精确指出规则 $\mathsf{Type} : \mathsf{Type}$ 用在哪里，让你看清宇宙层级为何能挡住它。

</div>

## 设定

在整个附录中，内核的宇宙被替换为单一宇宙 $\mathsf{Type}$，并以下面两条规则

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \mathsf{Type} : \mathsf{Type}}
\qquad
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \tPi{x}{A}{B} : \mathsf{Type}}
$$

取代 T-Sort 与 T-Pi。其余一切，包括 T-Lam、T-App、T-Conv、替换和 $\beta$ 归约，都保持不变。目标是构造一个闭项 $t_{\mathrm{H}}$，使得

$$
\vdash t_{\mathrm{H}} : \bot, \qquad \bot = \tPi{p}{\mathsf{Type}}{p}.
$$

这样的项能证明任意命题 $C$，因为 $t_{\mathrm{H}}\;C : C$。

这一构造源于 Girard，他把集合论中的 Burali-Forti 悖论移植到了带有 $\mathsf{Type} : \mathsf{Type}$ 的类型理论 [Girard 1972]。下面的项是 Hurkens 的简化版本 [Hurkens 1995]，一页纸即可写下，并且只用到 $\Pi$、$\lambda$ 和应用。

## 类型理论中的幂集

把函数 $p : S \to \mathsf{Type}$ 读作 $S$ 上的一个*谓词*（predicate），或等价地读作 $S$ 的一个*子集*：使 $p\;x$ 有证明的那些元素 $x$ 就是它的成员。所有这类谓词构成的类型就是 $S$ 的*幂集*（power set）：

$$
\wp S \;=\; S \to \mathsf{Type}.
$$

套用两次，$\wp\wp S = (S \to \mathsf{Type}) \to \mathsf{Type}$ 就是“$S$ 的子集族”的类型。

在集合论中，康托尔（Cantor）定理说，没有任何集合包含自身幂集的副本，更不用说二重幂集了：$\wp S$ 总是严格大于 $S$。这个悖论建立在一个违反该定理的类型 $U$ 之上，它包含 $\wp\wp U$ 的一个副本：函数 $\tau : \wp\wp U \to U$ 把 $U$ 的一个子集族打包成 $U$ 的单个元素，函数 $\sigma : U \to \wp\wp U$ 再把它解包。类型

$$
U \;=\; \tPi{X}{\mathsf{Type}}{\bigl((\wp\wp X \to X) \to \wp\wp X\bigr)}
$$

通过对*整个* $\mathsf{Type}$ 量化做到了这一点。$U$ 一边对 $\mathsf{Type}$ 量化，一边又是 $\mathsf{Type}$ 的成员，这正是 $\mathsf{Type} : \mathsf{Type}$ 所允许、而[第 13 章](13-universes.md)的层级所禁止的。

## 该项

下列缩写都在原处展开；内核看到的只有 $\Pi$、$\lambda$、变量和应用。我们用 $\neg\varphi$ 表示 $\varphi \to \bot$。

$$
\begin{array}{rcl}
\bot &=& \tPi{p}{\mathsf{Type}}{p} \\[4pt]
\wp S &=& S \to \mathsf{Type} \\[4pt]
U &=& \tPi{X}{\mathsf{Type}}{((\wp\wp X \to X) \to \wp\wp X)} \\[4pt]
\tau &=& \tLam{t}{\wp\wp U}{\tLam{X}{\mathsf{Type}}{\tLam{f}{\wp\wp X \to X}{\tLam{p}{\wp X}{t\;(\tLam{x}{U}{p\;(f\;(x\;X\;f))})}}}} \\[4pt]
\sigma &=& \tLam{s}{U}{s\;U\;\tau} \\[4pt]
\Delta &=& \tLam{y}{U}{\neg\,(\tPi{p}{\wp U}{\sigma\;y\;p \to p\;(\tau\;(\sigma\;y))})} \\[4pt]
\Omega &=& \tau\;(\tLam{p}{\wp U}{\tPi{x}{U}{\sigma\;x\;p \to p\;x}})
\end{array}
$$

借助这些缩写，类型为 $\bot$ 的项是

$$
\begin{array}{rcl}
t_{\mathrm{H}} &=& (\lambda (h_0 : \tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;\Omega}).\; \\
&& \qquad h_0\;\Delta\;(\tLam{x}{U}{\tLam{h_2}{\sigma\;x\;\Delta}{\tLam{h_3}{\tPi{p}{\wp U}{\sigma\;x\;p \to p\;(\tau\;(\sigma\;x))}}{
     h_3\;\Delta\;h_2\;(\tLam{p}{\wp U}{h_3\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})})}}}) \\
&& \qquad\phantom{h_0\;\Delta\;}(\tLam{p}{\wp U}{h_0\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})})) \\
&& (\tLam{p}{\wp U}{\tLam{h_1}{\tPi{x}{U}{\sigma\;x\;p \to p\;x}}{h_1\;\Omega\;(\tLam{x}{U}{h_1\;(\tau\;(\sigma\;x))})}})
\end{array}
$$

它的外形是一个应用：一个绑定 $h_0$ 的 $\lambda$，作用于（最后一行的）一个参数，该参数的类型正是 $h_0$ 所要求的。在内部，$h_0$ 作用于两个参数，即 $\Delta$ 和一个关于 $\Delta$ 的证明，所得结果再作用于另一个参数。下面逐一解释。

## 该项如何运作

**打包与解包。** 两个函数 $\tau : \wp\wp U \to U$ 和 $\sigma : U \to \wp\wp U$ 互逆的程度足以支撑整个论证。展开定义并做 $\beta$ 归约，对每个 $t : \wp\wp U$ 和 $p : \wp U$ 都有

$$
\sigma\;(\tau\;t)\;p \;\conv\; t\;(\tLam{x}{U}{p\;(\tau\;(\sigma\;x))}).
$$

内核在 $t_{\mathrm{H}}$ 中的多处通过 T-Conv 使用这个等式；它是一次计算，而不是一条公理。

**$U$ 上的一种序。** 把 $\sigma\;x\;p$ 读作“谓词 $p$ 对 $x$ 以下的一切都成立”，这给了 $U$ 某种类似序的结构，并让我们能对谓词和元素各说一件事。

- 谓词 $p : \wp U$ 是*归纳的*（inductive），如果只要它对 $x$ 以下的一切成立，就对 $x$ 成立：即 $\tPi{x}{U}{\sigma\;x\;p \to p\;x}$。
- 元素 $x : U$ 是*良基的*（well-founded），如果每个归纳谓词都对 $x$ 成立：即 $\tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;x}$。

元素 $\Omega$ 被构造出来扮演“全体良基元素的汇集”这一角色：它打包了由全部归纳谓词组成的族。在 Burali-Forti 悖论中，这对应于全体序数的集合，它本身是一个序数，因此是自身的成员，因此不是良基的，尽管所有序数都是良基的。

**三个要素。** 自下而上地读 $t_{\mathrm{H}}$：

1. 最后一行 $\tLam{p}{\wp U}{\tLam{h_1}{\cdots}{h_1\;\Omega\;(\tLam{x}{U}{h_1\;(\tau\;(\sigma\;x))})}}$ 证明 $\Omega$ 是良基的，它的类型是 $\tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;\Omega}$，也就是 $h_0$ 的类型，所以 $h_0$ 代表“$\Omega$ 是良基的”。
2. 谓词 $\Delta\;y$ 说的是“$y$ 不在自身之下”（严格地说，它谈论的是 $\tau\;(\sigma\;y)$，由上面的等式，它的行为与 $y$ 相同）。$h_0$ 的第二个参数，即以 $\tLam{x}{U}{\tLam{h_2}{\cdots}{\cdots}}$ 开头的那个长 $\lambda$，证明 $\Delta$ 是归纳的。于是 $h_0\;\Delta\;(\cdots) : \Delta\;\Omega$，也就是说，$\Omega$ 不在自身之下。
3. 余下的参数 $\tLam{p}{\wp U}{h_0\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})}$ 证明 $\Omega$ *确实*在自身之下：把 $\Omega$ 的良基性应用于一个经打包等式变换过的谓词即可。

由于 $\Delta\;\Omega$ 是“$\Omega$ 在自身之下”的否定，把第 2 步的结果应用于第 3 步的结果，就得到一个类型为 $\bot$ 的项。

<aside class="intuition" markdown="1">

这个论证就是乔装后的 Burali-Forti 悖论。序数都是良基的；全体序数的汇集 $\Omega$ 本身是一个序数，因此是自身的成员；但良基的东西都不是自身的成员。集合论的出路是拒绝让全体序数的汇集成为集合，而带 $\mathsf{Type} : \mathsf{Type}$ 的类型理论没有这种拒绝，因为 $U$ 可以对一切量化，包括它自己。

</aside>

## Type : Type 用在何处

$t_{\mathrm{H}}$ 中的每一步定型都很平常，只有一处例外：在 $\sigma = \tLam{s}{U}{s\;U\;\tau}$ 中，变量 $s : U$ 被应用于类型 $U$ 自身，而 $s$ 的类型以 $\tPi{X}{\mathsf{Type}}{\cdots}$ 开头，所以 T-App 要求 $U : \mathsf{Type}$。但 $U$ 是一个对 $\mathsf{Type}$ 量化的 $\Pi$ 类型，而在带宇宙层级的系统里，这样的类型位于它所量化的宇宙之*上*一层：

$$
\dfrac{\Gamma \vdash \Sort{u} : \Sort{(u+1)} \qquad \Gamma, X : \Sort{u} \vdash B : \Sort{v}}{\Gamma \vdash \tPi{X}{\Sort{u}}{B} : \Sort{\max(u+1, v)}}
$$

按[第 13 章](13-universes.md)的 T-Pi 规则，$U$ 至多在 $\Sort{(u+1)}$ 中，绝不会在 $\Sort{u}$ 中，于是 $s\;U$ 类型不正确，$\sigma$ 根本写不出来。整个构造在这一个应用处崩塌。$\Sort{0}$ 的非谓词性也不会重新打开这扇门：$U$ 的体是 $(\wp\wp X \to X) \to \wp\wp X$，其结果 $\wp\wp X$ 是一个以宇宙为值域的函数类型，因而不是命题，所以 $\mathrm{imax}$ 不会把 $U$ 放进 $\Sort{0}$。Coquand 证明了底层只有一个非谓词宇宙时系统是一致的 [Coquand 1988]；Hurkens 的项则表明，两个非谓词层级已经太多 [Hurkens 1995]。

## 用内核重现它

你可以亲眼看到内核接受和拒绝这个项。唯一要改的规则是 T-Sort，它由 `src/typecheck.rs` 中 `infer` 的 `Term::Sort(u)` 分支实现：

```rust
// T-Sort，发布版本：每个宇宙都位于下一个宇宙之中。
Term::Sort(u) => Ok(Term::Sort(u.checked_add(1).ok_or("universe overflow")?)),
```

把右侧换成 `Ok(Term::Sort(*u))`，使得 $\Sort{0} : \Sort{0}$，并在全文中以 $\Sort{0}$ 充当 $\mathsf{Type}$。其他什么都不用改：当每个类型都在 $\Sort{0}$ 中时，带 $\mathrm{imax}$ 的 T-Pi 规则已经把 $\Sort{0}$ 赋给每个 $\Pi$ 类型，这正是本附录的第二条规则。只改这一行后，`infer` 对 $t_{\mathrm{H}}$ 恰好返回 $\tPi{p}{\Sort{0}}{p}$。未修改的内核则如上文所料，在 $\sigma$ 内部的应用 $s\;U$ 处以类型不匹配拒绝该项。

<aside class="warning" markdown="1">

不要把这个修改留在代码里，它除了让内核不一致，还破坏了终止性：如[第 13 章](13-universes.md)所述，$t_{\mathrm{H}}$ 没有范式，所以让修改后的内核去规范化它，会一直跑到[第 12 章](12-reduction-conversion.md)的归约燃料耗尽为止。

</aside>

## 为什么没有范式

[第 14 章](14-properties.md)证明真实系统的一致性，方法是证明没有*范式*闭项具有类型 $\tPi{P}{\Sort{0}}{P}$。该证明中分析范式形状的那部分不使用强规范化，对 $\mathsf{Type} : \mathsf{Type}$ 照样成立。所以，如果 $t_{\mathrm{H}}$ 有范式，这个范式将是一个类型为 $\bot$ 的闭范式项，而这样的项不可能存在。类型保持性依然成立，所以归约也无法逃离类型 $\bot$。唯一剩下的可能是 $t_{\mathrm{H}}$ 永远归约下去：强规范化失效，类型检查器的终止性随之失效。因此，Girard 悖论不仅是逻辑上的缺陷，也是计算上的缺陷；这也是[第 13 章](13-universes.md)的宇宙设计对算法和对逻辑同样重要的原因。

<div class="summary-box" markdown="1">

要点回顾

- 在 $\mathsf{Type} : \mathsf{Type}$ 之下，类型 $U$ 对所有类型量化，同时自己也是其中之一，于是它包含自身二重幂集的副本，而没有任何集合能做到这一点。
- Hurkens 的项 $t_{\mathrm{H}}$ 把这一点变成 Burali-Forti 悖论：$\Omega$，即全部归纳谓词打包而成的族，既是良基的，又在自身之下。
- 规则 $\mathsf{Type} : \mathsf{Type}$ 只用在一处，即 $\sigma$ 中的应用 $s\;U$；宇宙层级使该应用类型不正确。
- 该项没有范式，所以这个悖论除一致性外也破坏了内核的终止性。

</div>
