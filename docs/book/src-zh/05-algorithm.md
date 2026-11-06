<div class="lead" markdown="1">

类型规则说明哪些判断成立，却没有给出判定方法。本章把工作分给两个相互递归的函数，将规则变成算法：一个计算项的类型，另一个借助定义相等，把算出的类型与期望的类型作比较。最终的 Rust 实现只有几十行。

</div>

## 从规则到算法

图 3.1 的八条规则中有七条是*语法制导*（syntax-directed）的：看一眼项，就知道该用哪条规则。宇宙对应 T-Sort，变量对应 T-Var，$\Pi$ 对应 T-Pi，$\lambda$ 对应 T-Lam，应用对应 T-App。T-Conv 是例外：它可以在任何时刻应用于任何项，程序无法从项本身判断何时该用它，而朴素地搜索推导就只能靠猜。

标准解法 [Barendregt 1992] 是把类型检查拆成两个函数：

- $\Infer(\Gamma, t)$ 按语法制导的规则计算 $t$ 在 $\Gamma$ 中的*那个*类型，或者失败。
- $\Check(\Gamma, t, T)$ 验证 $t$ 具有期望的类型 $T$：先推断出一个类型，再用定义相等把它与 $T$ 作比较。

T-Conv 只在一处使用，即 $\Check$ 内部。另有两处要求类型具有特定形状：T-App 要求一个 $\Pi$，T-Pi 和 T-Lam 的前提要求一个宇宙。在这些地方，算法把推断出的类型计算到刚好能看清最外层形状为止。

算法用到两个作用于项的函数，其定义推迟到[第 12 章](12-reduction-conversion.md)：

- $\Whnf(T)$ 计算 $T$，直到它的最外层形状可见为止。例如 $\Whnf(\mathit{Id}\;(P \to P)) = P \to P$，这是一个 $\Pi$。
- $\IsDefEq(A, B)$ 判定 $A \conv B$。

## 算法

算法 5.1 用贴近 Rust 的伪代码写出，$\Infer$ 的每个分支都标注了它所实现的规则。

<div class="rulebox" markdown="1">

<p class="caption">算法 5.1. 类型推断与类型检查。</p>

```text
Infer(Γ, t):
  if t = Sort u:                                        -- T-Sort
      return Sort (u + 1)
  if t = x:                                             -- T-Var
      if (x : A) ∈ Γ: return A  else fail "unbound variable"
  if t = Π(x : A). B:                                   -- T-Pi
      u ← InferSort(Γ, A)
      (x', B') ← Freshen(Γ, x, B)
      v ← InferSort((Γ, x' : A), B')
      return Sort (imax(u, v))
  if t = λ(x : A). s:                                   -- T-Lam
      InferSort(Γ, A)
      (x', s') ← Freshen(Γ, x, s)
      B ← Infer((Γ, x' : A), s')
      return Π(x' : A). B
  if t = f a:                                           -- T-App
      T ← Whnf(Infer(Γ, f))
      if T = Π(x : A). B:
          Check(Γ, a, A)
          return B[x ↦ a]
      else fail "not a function"

Check(Γ, t, T):                                         -- T-Conv
  T' ← Infer(Γ, t)
  if IsDefEq(T', T): return  else fail "type mismatch"

InferSort(Γ, A):
  T ← Whnf(Infer(Γ, A))
  if T = Sort u: return u  else fail "expected a type"

Freshen(Γ, x, b):
  if x ∈ dom(Γ):
      choose x' ∉ dom(Γ) ∪ FV(b)
      return (x', b[x ↦ x'])
  else return (x, b)
```

</div>

这个算法有以下性质。

- **语法制导。** $\Infer$ 的每个分支恰好对应图 3.1 的一条规则。找出一个证明可能很难，但检查一个给定的证明是机械的：从不需要作选择。
- **T-Conv 从不单独应用。** 它只发生在 $\Check$ 内部，这是推断出的类型与期望类型相遇的唯一地方。
- **$\InferSort$ 是内核判定一个项是否为类型的方式。** 项 $A$ 是类型，当且仅当它的类型计算到一个宇宙。例如，$\lambda$ 抽象永远不是类型，因为它推断出的类型总是一个 $\Pi$。
- **$\Freshen$ 实现了 C-Ext 的附加条件。** 它给名字已在上下文中出现的绑定子改名。[第 11 章](11-substitution-alpha.md#variable-capture-in-contexts)给出了一个项，若没有这一步，内核就会不可靠。
- **上下文始终良构。** 从空上下文出发，算法构造的每个上下文都是良构的，因为只有在 $\InferSort$ 对假设的类型成功之后，才会把该假设加入。若调用者从非空上下文开始，则必须另行检查该上下文。
- **终止性**取决于 $\Whnf$ 和 $\IsDefEq$ 是否终止；对良类型的项，强规范化（[第 14 章](14-properties.md)）保证了这一点。

<aside class="intuition" markdown="1">

将工作分为 $\Infer$ 和 $\Check$，有时称为*双向*（bidirectional）类型检查，因为类型信息沿两个方向流动。推断从叶子*向上*进行：变量已有类型，应用则从其组成部分算出类型；检查则从用户给出的期望类型*向下*进行，在根部将它与推断结果比较。我们的内核可以推断每个项的类型，因此检查只需再做一次比较；在更丰富的系统中，有些项必须有期望类型才能检查。

</aside>

## 代码中

<aside class="code" markdown="1">

算法 5.1 对应 `src/typecheck.rs` 中的 `Kernel::infer`、`Kernel::check` 和 `Kernel::infer_sort`；`Freshen` 对应同一文件中的辅助函数 `rename_binder_if_needed`。下面给出完整的 `infer`，其中包含第二部分才引入的常量分支；想逐行对照时可以展开。

</aside>

<details class="code-details" markdown="1">
<summary>完整的 infer 函数（约五十行）</summary>

```rust
pub fn infer(&self, ctx: &Context, t: &Term) -> Result<Term> {
    match t {
        // T-Sort
        Term::Sort(u) => Ok(Term::Sort(u.checked_add(1).ok_or("universe overflow")?)),
        // T-Var
        Term::Var(x) => ctx
            .iter()
            .rev()
            .find(|(name, _)| name == x)
            .map(|(_, ty)| ty.clone())
            .ok_or_else(|| format!("unbound local: {x}")),
        // T-Const（第 7 章）
        Term::Const(c) => self
            .decls
            .get(c)
            .map(|decl| decl.ty.clone())
            .ok_or_else(|| format!("unknown constant: {c}")),
        // T-Pi：Sort 0 是非谓词的。
        Term::Pi(x, domain, body) => {
            let domain_level = self.infer_sort(ctx, domain)?;
            let (x, body) = rename_binder_if_needed(ctx, x, body);
            let mut extended = ctx.clone();
            extended.push((x, (**domain).clone()));
            let body_level = self.infer_sort(&extended, &body)?;
            Ok(Term::Sort(if body_level == 0 {
                0
            } else {
                domain_level.max(body_level)
            }))
        }
        // T-Lam
        Term::Lam(x, domain, body) => {
            self.infer_sort(ctx, domain)?;
            let (x, body) = rename_binder_if_needed(ctx, x, body);
            let mut extended = ctx.clone();
            extended.push((x.clone(), (**domain).clone()));
            let body_type = self.infer(&extended, &body)?;
            Ok(Term::Pi(x, domain.clone(), Box::new(body_type)))
        }
        // T-App
        Term::App(f, a) => match self.whnf(&self.infer(ctx, f)?)? {
            Term::Pi(x, domain, codomain) => {
                self.check(ctx, a, &domain)?;
                Ok(subst(&codomain, &x, a))
            }
            ty => Err(format!("application of non-function: {ty:?}")),
        },
    }
}
```

</details>

有几处细节与伪代码不同。

- 变量分支的上下文查找是从末尾开始的（`.rev()`），由于 `rename_binder_if_needed` 保证名字互不相同，匹配项永远不会多于一个；但如果调用者传入了含重复名字的上下文，从末尾查找才是正确的行为。
- T-Pi 中的 $\imax$ 就是 `if body_level == 0` 这个表达式：体是命题的 $\Pi$ 本身是命题，否则它位于两个层级中较大的那一个。
- 宇宙层级是 `u64`，`checked_add` 防止溢出。没有哪个真实证明会接近层级 $2^{64}$，但内核对任何输入都不应有未定义行为。
- 应用分支在对 `f` 的推断类型作匹配之前先调用 `whnf`，与伪代码一致；没有这一步，类型写成 $\mathit{Id}\;(A \to B)$ 的函数就无法被应用。

剩下的两个函数都很短。

```rust
/// Gamma |- t : expected，用 T-Conv 比较推断出的类型。
pub fn check(&self, ctx: &Context, t: &Term, expected: &Term) -> Result<()> {
    self.infer_sort(ctx, expected)?;
    let actual = self.infer(ctx, t)?;
    if self.is_def_eq(&actual, expected)? {
        Ok(())
    } else {
        Err(format!("type mismatch: actual {actual:?}, expected {expected:?}"))
    }
}

/// 推断 t 的类型，并要求它是一个宇宙 Sort u。返回 u。
pub fn infer_sort(&self, ctx: &Context, t: &Term) -> Result<u64> {
    match self.whnf(&self.infer(ctx, t)?)? {
        Term::Sort(u) => Ok(u),
        other => Err(format!("expected a type, got {other:?}")),
    }
}
```

`check` 以 `infer_sort(ctx, expected)` 开头，这对应 T-Conv 的前提 $\Gamma \vdash B : \Sort{u}$：期望的类型本身必须是类型。伪代码省略了它，因为算法内部的调用者传入的总是已经检查过的类型；但公开的 `check` 也会被用户提供的命题调用，所以 Rust 版本要验证这一点。

最后是 `Freshen`：

```rust
fn rename_binder_if_needed(ctx: &Context, x: &str, body: &Term) -> (String, Term) {
    if !ctx.iter().any(|(name, _)| name == x) {
        return (x.into(), body.clone());
    }
    let mut used = all_names(body);
    for (name, ty) in ctx {
        used.insert(name.clone());
        used.extend(all_names(ty));
    }
    let renamed = fresh(x, &used);
    let renamed_body = subst(body, x, &var(&renamed));
    (renamed, renamed_body)
}
```

要避开的名字集合比伪代码中的 $\dom(\Gamma) \cup \FV(b)$ 更大：它包含体中以及上下文各类型中出现的所有名字，无论约束还是自由。多避开一些名字总是安全的，而且能让改名后的项保持可读。`fresh` 不断追加撇号直到名字未被使用，所以 `x` 冲突时会得到 `x'`。

## 观察 Infer 的运行

下面的浏览器（explorer）在一个项上运行该算法，并记录每一次递归调用：进入了 $\Infer$ 的哪个分支、在哪个上下文中、返回了什么。注释报告隐藏的工作，例如 $\Whnf$ 暴露出一个 $\Pi$，或 $\Freshen$ 给某个绑定子改名。上下文栏接受形如 `Q : Sort 0; q : Q` 的假设，用分号分隔。

<div class="explorer" data-kind="derive" data-term="fun (f : P -> Q) => fun (p : P) => f p" data-ctx="P : Sort 0; Q : Sort 0"></div>

## 证明是如何被检查的

要验证项 $t$ 证明了定理 $T$，内核在空上下文中运行 $\Check(\cdot, t, T)$。在脚本语言里，这正是 `qed` 所做的事：[第 10 章](10-tactics.md)的策略组装出一个项，`qed` 把它连同 `goal` 给出的命题一起交给 `check`。两者之间的一切都是不可信的。

下一章将在若干项上手工运行 $\Infer$ 和 $\Check$，其中包括一个良类型但并未证明其所声称命题的项。

## 练习

<div class="exercise" markdown="1">

追踪 $\Infer(\cdot, \tLam{A}{\Sort{1}}{\tLam{a}{A}{a}})$，给出结果及其所在宇宙。

<details markdown="1">
<summary>解答</summary>

$\InferSort(\cdot, \Sort{1})$ 返回 $2$，上下文变为 $A : \Sort{1}$。对于内层 $\lambda$，$\InferSort(A : \Sort{1}, A)$ 返回 $1$，上下文变为 $A : \Sort{1}, a : A$，$\Infer$ 对体返回 $A$。于是内层结果是 $\tPi{a}{A}{A}$，外层结果是 $\tPi{A}{\Sort{1}}{\tPi{a}{A}{A}}$。对这个类型运行 $\InferSort$ 得到 $\imax(2, \imax(1, 1)) = 2$，所以该类型位于 $\Sort{2}$。

</details>

</div>

<div class="exercise" markdown="1">

$\Pi$ 类型“只是一个类型”，为什么 $\Infer$ 的 $\Pi$ 分支仍要调用 $\Freshen$？给出一个项，使得跳过这一步会改变结果。

<details markdown="1">
<summary>解答</summary>

$\Pi$ 的体是在扩展后的上下文中检查的，所以会出现与 $\lambda$ 相同的遮蔽问题。取 $\Gamma = x : \Sort{0}, y : x$，类型 $\tPi{x}{\Sort{1}}{y}$ 应当失败，因为 $y : x$ 中的 $x$ 是外层的命题，而命题不是宇宙。若不改名，反向查找会先找到内层的 $x : \Sort{1}$，使 $y$ 的类型看起来取值于 $\Sort{1}$，结果就错了。改名后内层绑定子变为 $x'$，体仍然指向外层的 $x$。

</details>

</div>

<div class="summary-box" markdown="1">

要点回顾

- $\Infer$ 跟随项的形状；$\Check$ 先推断，再用 $\IsDefEq$ 比较，T-Conv 只存在于 $\Check$ 内部。
- 在需要 $\Pi$ 或宇宙的地方，$\Whnf$ 暴露出类型的最外层形状。
- $\InferSort$ 就是“这个项是类型吗”这一测试：它的类型必须计算到一个宇宙。
- $\Freshen$ 给会遮蔽上下文条目的绑定子改名，这是正确性的要求，而不是为了方便。
- `src/typecheck.rs` 是算法的直接转写，约一百行。

</div>
