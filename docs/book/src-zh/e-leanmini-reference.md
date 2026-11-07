<div class="lead" markdown="1">

本书的脚本使用 leanmini，由 `src/syntax.rs` 解析，再交给 `src/main.rs` 运行。每个绑定子都有显式类型，每个参数都要写出。这份参考说明语言的规则，并收录仓库中可运行的示例脚本。

</div>

## 运行脚本

运行器是由 `src/main.rs` 构建的二进制程序 `mini-lean`。

```text
cargo run -- examples/identity.leanmini    # run a script file
cargo run                                  # interactive session on stdin
cargo test                                 # the kernel's own test suite
```

脚本是一系列行，运行器自上而下处理它们，遇到第一个错误即停止，打印消息并以状态 1 退出。空行和以 `#` 开头的行是注释，会被跳过。

```leanmini
# 这是一行注释。
goal forall (P : Sort 0), P -> P
```

不带文件参数时，运行器先打印一份可用命令的提示，然后从标准输入逐行读取同样的命令。错误以前缀 `error:` 报告，会话继续。命令 `quit`（或 `exit`）结束会话。两种模式有一处命令上的差别：在文件中，`inductive` 块是首行加上随后的各 `|` 行；在交互模式下，该块以只含 `end` 的一行结束。

<aside class="note" markdown="1">

命令行运行器用 Rust 的 `Debug` 格式打印项，例如 `App(Const("Nat.succ"), Const("Nat.zero"))`，因为内核没有美化打印器。本书的演练场运行的是同一个内核编译成 WebAssembly 的版本，外加一个小型美化打印器，把项写回 leanmini 语法；它们还会在每条命令的输出之前回显该命令，使记录可以独立阅读。

</aside>

## 项

项按下列形式之一书写。`A`、`B`、`t` 代表项，`x` 代表名字。

| 语法 | 含义 | 书中记法 |
|---|---|---|
| `Sort 0`、`Sort 1`、... | 宇宙；数字是必需的 | $\Sort{u}$ |
| `x` | 变量或常量，取决于作用域 | $x$ 或 $c$ |
| `forall (x : A), B` | 依赖函数类型 | $\tPi{x}{A}{B}$ |
| `A -> B` | 非依赖函数类型 | $A \to B$ |
| `fun (x : A) => t` | 函数 | $\tLam{x}{A}{t}$ |
| `f a` | 应用 | $f\;a$ |
| `(t)` | 分组 | |

应用左结合且结合最紧：`f a b` 即 `(f a) b`。箭头右结合：`A -> B -> C` 即 `A -> (B -> C)`。`forall` 或 `fun` 向右延伸到尽可能远，箭头的右侧也是如此，所以 `A -> forall (x : B), C` 无需括号。作为*参数*使用的 `forall` 或 `fun` 必须加括号，如 `Nat.rec1 (fun (_n : Nat) => Nat) m`。箭头 `A -> B` 读作 `forall (_ : A), B`；名字 `_` 为此保留，不能在归纳声明中用作绑定子。

词法分析器按空白以及字符 `(`、`)`、`,`、`:` 和双字符符号 `->`、`=>` 切分。名字是由字母、数字、`_`、`'` 和 `.` 组成的连续序列，所以 `Nat.succ`、`List.rec1` 和 `x'` 都是单个名字。三个 Unicode 字符被接受为别名：`→` 对应 `->`，`λ` 对应 `fun`，`∀` 对应 `forall`。其他任何字符都会以 `unexpected character: ...` 拒绝。

名字在项被解析时就解析完毕，而不是之后。

- 由外层 `fun` 或 `forall` 绑定的名字，或出现在当前目标上下文中的名字，是**局部变量**。
- 否则，在内核中声明过的名字（通过 `inductive`、`def`、`axiom`、`recursor`，或内建）是**常量**。
- 否则解析失败，报 `unknown identifier: x`。拼错构造子名字，或使用尚未引入的假设，得到的也是这个错误。

局部变量遮蔽同名常量。解析器从不猜测类型：`Sort` 后面必须跟数字，绑定子必须写成带类型的 `(x : A)`。

## 声明

### 归纳类型

```leanmini
inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)
```

首行的形式是 `inductive Name (p : P) ... (index i : J) ... : Sort u where`。每个带括号的绑定子是一个**参数**；若以单词 `index` 开头，则是一个**索引**。参数必须在索引之前（`parameters must precede indices`）。冒号之后的宇宙必须是字面量 `Sort u`（`inductive result must be Sort u`），且该行必须以 `where` 结尾。

随后的每一行以 `|` 开头，声明一个构造子：`| ctor (field : T) ... [: Name params indices]`。字段类型可以提到参数、先前的字段和 `Name` 本身。可选冒号之后的结果类型必须是 `Name` 依次、原样应用于各参数（`constructor parameters must be uniform`），再跟上每个索引对应的一个索引项。若类型有索引，每个构造子都必须给出结果类型（`indexed constructor requires explicit result type`）；若没有索引，结果类型可以省略。构造子字段上不允许使用 `index` 关键字。

```leanmini
inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where
  | nil : Vec A Nat.zero
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)
```

构造子以限定名注册：上面的声明添加 `Vec.nil` 和 `Vec.cons`，而 `List` 的构造子是 `List.nil` 和 `List.cons`；脚本必须使用限定形式。

接受声明时会运行[第 8 章](08-inductive-recipe.md)的四个条件：`Name` 的类型是一个类型，每个构造子类型都是以 `Name` 应用于参数结尾的类型，每个提到 `Name` 的字段都严格正，并且当 `u` 至少为 1 时，没有字段位于 `Sort u` 之上的宇宙。失败时的消息包括 `non-strictly-positive / unsupported recursive field`、`field f lives in Sort w, exceeding inductive universe Sort u` 和 `inductive occurrence inside result index`。以 `_` 或 `__` 开头的绑定子名字会被拒绝（`reserved binder name`），因为内核用这类名字命名它自己生成的绑定子。

成功时运行器打印 `inductive Name registered`，内核添加类型构造器、各构造子、递归子 `Name.rec0`，以及在允许大消去时的 `Name.rec1`。命题（`Sort 0`）只有在是子单元时才获得 `Name.rec1`，如[第 8 章](08-inductive-recipe.md)所述。

<aside class="warning" markdown="1">

在脚本文件中，`inductive` 块的构造子行必须紧跟首行，中间不能夹注释行。运行器收集以 `|` 开头的行和空行；一个 `#` 行会提前结束该块，之后的第一个构造子行就会被报为 `start with 'goal <type>'`（若有证明正在进行，则是 `unknown command: ...`）。

</aside>

### 定义与公理

```leanmini
def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
axiom em : forall (P : Sort 0), P -> P
```

`def name : T := t` 检查 `T` 是一个类型，并在空上下文中检查 `t : T`，然后添加带有体 `t` 的 `name`；内核在归约时展开它（$\delta$ 归约，[第 12 章](12-reduction-conversion.md)）。运行器打印 `defined name`。定义必须写在一行内，第一个 `:=` 分隔类型和体。

`axiom name : T` 在检查 `T` 是一个类型之后，添加没有体的 `name : T`。它打印 `added axiom name`。公理从不展开。没有什么能阻止你用这种方式假设一个假命题；内核检查的是类型良构，而不是它为真。

名字必须是新的：重复声明会以 `duplicate declaration: name` 失败，并且不能在已有归纳类型的命名空间 `Name.rec...` 之内声明任何东西。

### 额外的递归子

```leanmini
recursor Nat 2
```

`recursor I v` 为消去宇宙 `v` 生成 `I.recv`（若尚不存在），并打印 `generated I.recv`。层级 0 和 1 由 `inductive` 自动生成；当 motive 需要返回 `Sort 2` 或更高宇宙中的类型时使用此命令。对不允许大消去的命题，它会失败（`I is not a subsingleton proposition; cannot eliminate into Sort v`）。

## 标准内核

每个会话开始时 `Nat` 和 `Eq` 都已声明，就像运行过下列声明一样。生成的绑定子名字以 `__` 开头；为便于阅读，这里写作 `M` 和 `m`，而重命名约束变量不改变类型。

```leanmini
Nat      : Sort 1
Nat.zero : Nat
Nat.succ : Nat -> Nat
Nat.rec0 : forall (M : Nat -> Sort 0), M Nat.zero -> (forall (n : Nat), M n -> M (Nat.succ n)) -> forall (x : Nat), M x
Nat.rec1 : forall (M : Nat -> Sort 1), M Nat.zero -> (forall (n : Nat), M n -> M (Nat.succ n)) -> forall (x : Nat), M x

Eq       : forall (A : Sort 1), A -> A -> Sort 0
Eq.refl  : forall (A : Sort 1), forall (a : A), Eq A a a
Eq.rec0  : forall (A : Sort 1), forall (a : A), forall (M : forall (b : A), Eq A a b -> Sort 0), M a (Eq.refl A a) -> forall (b : A), forall (h : Eq A a b), M b h
Eq.rec1  : forall (A : Sort 1), forall (a : A), forall (M : forall (b : A), Eq A a b -> Sort 1), M a (Eq.refl A a) -> forall (b : A), forall (h : Eq A a b), M b h
```

`Nat.rec1` 是进入类型的递归，`Nat.rec0` 是进入命题的归纳（[第 7 章](07-inductive-nat.md)）。`Eq` 显式接受类型参数 `A`，所以 $\Nat$ 中的等式 $a = b$ 写作 `Eq Nat a b`，其自反性证明是 `Eq.refl Nat a`（[第 9 章](09-equality.md)）。由于 `Eq` 以 `A : Sort 1` 声明，相等只对 `Sort 1` 中的类型可用，如 `Nat` 和 `List Nat`，对命题不可用。

一般地，归纳类型 `I` 进入 `Sort v` 的递归子名为 `I.recv`：`List.rec0`、`List.rec1`、`Vec.rec1` 等等。其参数顺序为：参数、motive、每个构造子（按声明顺序）各一个小前提、索引，最后是大前提（[第 8 章](08-inductive-recipe.md)）。

## 证明

### 开始一个目标

```leanmini
goal forall (n : Nat), Eq Nat n n
```

`goal T` 检查 `T` 在空上下文中是一个类型，并以单个目标 `?0 : T` 开始一个证明。在命令行运行器中它不打印任何东西（演练场会打印目标）。在 `goal` 之前给出的任何策略都会以 `start with 'goal <type>'` 失败。开始新的 `goal` 会放弃未完成的证明。

每条策略之后，运行器打印剩余的目标，每个目标依次是编号、假设，以及推导符号之后的目标类型：

```text
?3:
  n : Nat
  k : Nat
  ih : Eq Nat (add Nat.zero k) k
  ⊢ Eq Nat (add Nat.zero (Nat.succ k)) (Nat.succ k)
```

没有目标剩余时，它打印 `No goals. Run 'qed' to kernel-check.`。命令 `show` 打印目标而不做任何改动。

策略总是作用于第一个目标，交给策略的项在该目标的上下文中解析，所以假设的名字在作用域内。[第 10 章](10-tactics.md)解释每条策略对部分证明项做了什么；本节只陈述接口。

### 策略

**`intro x`** 要求目标归约到 `forall` 或箭头，然后把 `x : A` 加入上下文，其中 `A` 是定义域，并把体设为新目标。名字不能已在上下文中（`binder name already in context`）；其他情况下的消息是 `intro expects a Pi/arrow goal`。

**`exact t`** 先把 `t` 对照目标检查，再用 `t` 关闭目标。不匹配时由内核报告 `type mismatch: actual ..., expected ...`。

**`apply f`** 推断 `f` 的类型，并逐层剥去非依赖箭头，直到结果与目标定义相等；每个剥下的定义域依次成为一个新目标。若 `f` 的类型已与目标匹配，`apply f` 的行为与 `exact f` 相同。依赖绑定子会被拒绝，报 `dependent apply requires elaboration/unification`；结果始终不匹配则报 `apply result does not match the goal`。

**`change T`** 把目标替换为 `T`，`T` 必须是与之定义相等的类型（`change expects definitionally equal target`）。它用于在 `rw` 之前暴露出只有经过计算才出现的子项。

**`rfl`** 要求目标归约到 `Eq A a b`（`rfl expects Eq A lhs rhs`），且 `a` 与 `b` 定义相等（`rfl: sides are not definitionally equal`），然后用 `Eq.refl A a` 关闭它。

**`rw h`** 要求 `h` 的类型归约到 `Eq A a b`（`rw expects proof of equality`），然后把目标中 `a` 的每一次出现替换为 `b`，并把重写后的目标作为新目标。出现是按语法查找的，只容许约束变量名不同；仅在计算之后才相等的项找不到，此时报 `rw: no syntactic occurrence of lhs in goal; use change first`。与 Lean 的 `rw` 不同，它之后不会尝试 `rfl`，所以形如 `Eq A x x` 的目标仍须显式关闭。若抽象 `a` 产生类型不正确的 motive，内核的类型错误会在证明状态改变之前报告。

**`induction x`** 要求 `x` 是一个假设，其类型归约到无索引的归纳类型，并且之后的假设都不能提到 `x`（`induction: revert dependent hypotheses first`），然后按声明顺序为每个构造子创建一个目标，每个目标的上下文获得该构造子的各字段（使用其声明的名字），以及每个递归字段对应的一个归纳假设，名为 `ih`（若 `ih` 已被占用则追加撇号）。当 `n` 已在使用中时，`Nat.succ` 中名为 `n` 的字段会被重命名为 `k`，这就是下面示例的目标里出现 `k` 和 `ih` 的原因。所用的递归子是 `I.recv`，其中 `v` 是目标的宇宙；若该递归子不存在，消息是 `no elimination recursor at target universe`。不支持索引族（`indexed induction requires motive/index elaboration (not implemented)`）。

**`qed`** 在仍有目标时失败（`N goals remain`）；否则，它从各策略步骤组装出证明项，交给内核对照原始目标检查，打印 `QED. Kernel checked proof:` 和该项，然后结束证明。系统的可靠性只取决于这最后一次检查。

其他任何行都会得到 `unknown command: ...`。

### 来自内核的错误

有些消息来自内核而非策略层，可能在任何命令下出现。

| 消息 | 含义 |
|---|---|
| `unbound local: x` | 变量在其绑定子之外被使用；解析器不会产生这种情况，只有错误构造的项才会。 |
| `unknown constant: c` | 常量被移除或从未声明。 |
| `application of non-function: ...` | 应用的函数位置没有 `forall` 类型。 |
| `expected a type, got ...` | 绑定子注解、目标或声明的类型不是一个类型。 |
| `type mismatch: actual ..., expected ...` | 推断出的类型与所需类型不定义相等。 |
| `universe overflow` | 宇宙层级超出 64 位。 |
| `reduction fuel exhausted` | 单次归约超过 20,000 步；在很大的计算中会发生，例如大数相加。 |

## 示例脚本

`examples/` 目录中的每个脚本都在下面以演练场形式给出。每个脚本都经内核检查通过；修改它并按下运行，看看会有什么变化。

### identity.leanmini

<div class="playground" data-file="examples/identity.leanmini"><pre># 命题上的多态恒等函数：对每个 P，P -&gt; P。
goal forall (P : Sort 0), P -&gt; P
intro P
intro p
exact p
qed</pre></div>

### nat-reflexivity.leanmini

<div class="playground" data-file="examples/nat-reflexivity.leanmini"><pre># 每个自然数都等于自身，对 Nat 归纳证明。
# 每种情形都由 rfl 关闭，因为两边在语法上相同。
goal forall (n : Nat), Eq Nat n n
intro n
induction n
rfl
rfl
qed</pre></div>

### zero-add.leanmini

<div class="playground" data-file="examples/zero-add.leanmini"><pre># 通过对第二个参数递归定义加法：
#   add m zero     = m
#   add m (succ k) = succ (add m k)
def add : Nat -&gt; Nat -&gt; Nat := fun (m : Nat) =&gt; fun (n : Nat) =&gt; Nat.rec1 (fun (_n : Nat) =&gt; Nat) m (fun (k : Nat) =&gt; fun (r : Nat) =&gt; Nat.succ r) n

# add zero n = n 不是定义相等，所以需要对 n 归纳。
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
induction n
# 基础情形：add zero zero 归约到 zero。
rfl
# 归纳步骤：把 add zero (succ k) 展开为 succ (add zero k)，然后使用 ih。
change Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ k)
rw ih
rfl
qed</pre></div>

### generic-list.leanmini

<div class="playground" data-file="examples/generic-list.leanmini"><pre># 用户声明的多态列表。声明它会生成 List.rec0、List.rec1 等。
inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)

# induction 对任何无索引的归纳类型都有效，不只是 Nat。
goal forall (xs : List Nat), Eq (List Nat) xs xs
intro xs
induction xs
rfl
rfl
qed</pre></div>

### generic-vec.leanmini

<div class="playground" data-file="examples/generic-vec.leanmini"><pre># 以长度为索引的向量。索引 n 在构造子之间变化，
# 所以在首行用 `index` 关键字声明它。
inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where
  | nil : Vec A Nat.zero
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

# 构造子显式接受参数 A。
def one : Vec Nat (Nat.succ Nat.zero) := Vec.cons Nat Nat.zero Nat.zero (Vec.nil Nat)

# 策略 `induction` 尚不支持索引族，
# 但内核仍然检查直接使用 Vec 的项。
goal Eq (Vec Nat (Nat.succ Nat.zero)) one (Vec.cons Nat Nat.zero Nat.zero (Vec.nil Nat))
rfl
qed</pre></div>

## 与 Lean 4 相比缺少什么

leanmini 是理解内核的工具，不是证明助手。下表列出 Lean 前端替你做、而这门语言不做的事。

| Lean 4 | leanmini |
|---|---|
| 隐式参数，由繁饰器填入 | 每个参数都显式；写 `Eq Nat a b`，而非 `a = b` |
| 用合一求解元变量 | 没有；策略只在项已完全确定时才有效 |
| 宇宙多态（带层级变量的 `Sort u`） | 每个层级都是数字；每个层级一个递归子 |
| 互归纳与嵌套归纳类型 | 一次只有一个归纳类型；作为字段的 `List Tree` 会被拒绝 |
| 定义性的证明无关性 | 命题的证明和其他项一样比较 |
| 对索引族的 `induction`，带回退（revert） | 仅限无索引类型；依赖假设必须手工回退（而没有任何策略能做这件事） |
| 带依赖参数的 `apply` | 仅限非依赖箭头 |
| 容许实例的 `rw`，之后自动 `rfl` | 仅按语法匹配；没有自动 `rfl` |
| `simp`、`omega` 和其他自动化 | 没有 |
| 记法、数字字面量，以及带命名结果的 `theorem` | `Nat.succ (Nat.succ Nat.zero)`；完成的证明不会以名字保存 |

最后一行有一个实际后果：`qed` 打印证明项，然后丢弃它。要复用一个结果，把它写成项展开后的 `def`，或者写成 `axiom`。

<aside class="lean" markdown="1">

右列的一切都是 Lean 的繁饰器和策略框架在项到达内核之前完成的工作，而 Lean 的内核和我们的一样，只会看到完整的项。上述限制是本仓库前端的限制，而不是类型理论的限制。

</aside>

<div class="summary-box" markdown="1">

要点回顾

- leanmini 脚本是一列命令：`inductive`、`def`、`axiom`、`recursor`、`goal`，以及策略 `intro`、`exact`、`apply`、`change`、`rw`、`rfl`、`induction`，最后以 `qed` 收尾。
- 项完全显式：`Sort u`、`forall (x : A), B`、`fun (x : A) => t`、`A -> B`，以及左结合的应用。
- 构造子和递归子使用限定名：`List.cons`、`List.rec1`。`Nat` 和 `Eq` 是预先声明的。
- 前端刻意做到最小；只有最后由内核执行的 `qed` 检查才与可靠性有关。

</div>
