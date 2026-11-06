<header class="hero" markdown="1">
<div class="hero-head" markdown="1">

<h1 class="logo">MiniLean4</h1>

</div>
<div class="hero-text" markdown="1">

<p class="hero-title">从零实现交互式定理证明器</p>

<p class="byline">Hideaki Takahashi</p>

<div class="lead" markdown="1">

一个 Lean 4 风格的证明内核，从零开始构建。起点只有五种项和八条类型规则；到最后加入归纳类型、策略语言，以及维系整个系统一致性的宇宙层级。每一部分都对应一段小巧的 Rust 实现，一个下午就能读完。

</div>

<p class="punch">证明即程序。内核负责检查。其余皆不可信。</p>

</div>
<div class="hero-term" markdown="1">
<div class="playground" data-file="examples/identity.leanmini"><pre># 命题上的多态恒等函数：对每个 P，都有 P -> P。
goal forall (P : Sort 0), P -> P
intro P
intro p
exact p
qed</pre></div>
<p class="hero-caption">这是真正的内核，编译成 WebAssembly，正在检查本书的第一个定理。修改脚本，再运行一次。</p>
</div>
</header>

## 本书是什么

Lean、Coq、Agda 这类交互式定理证明器（interactive theorem prover）都建立在一个很小的核心之上：一个*内核*（kernel），用来判定某个项是否具有给定的类型。其余一切，包括策略、记法和自动化，都只是脚手架，负责生成交给内核检查的项。只要内核是对的，别处的错误至多让系统证不出某个定理，却绝不会让它接受一个错误的定理。

本书的目标是把这个内核讲具体。每一章先在纸上引入一个想法，给出精确的陈述，再展示实现它的 Rust 代码。整个实现，包括内核、策略和解析器，不到三千行，没有任何依赖，本书会全部讲到。

本书自成一体，读者只需能读懂递归函数，并了解一点集合记法。不要求事先接触过类型论或 Lean，不过熟悉 Lean 的读者会发现许多似曾相识的内容。

## 如何阅读

<p>CONTENTS_GO_HERE</p>

**第一部分**为一个依赖类型论构建类型检查器，并说明它就是某种逻辑的证明检查器。**第二部分**加入归纳类型（自然数、树、列表、向量和相等），以及替你写出证明项的策略语言。**第三部分**打开前两部分一直依赖的黑箱：替换、α 等价和归约，内核的错误往往藏在这里。**第四部分**解释宇宙为何如此构造，并陈述元理论。附录包含完整的证明、为宇宙设计提供依据的悖论，以及脚本语言的参考手册。

全书中你会遇到四种交互元素。

- **演练场**运行内核：编辑脚本，按下运行，然后阅读输出记录。
- **浏览器**（explorer）展示内核眼中的项：语法树、逐条规则的类型推导、逐步进行的归约、每个变量属于哪个绑定子，以及每条策略之后的证明状态。每个浏览器都是实时的：改动项，内核就会重新计算。
- **步进器**逐步执行一个算法，展示每一步之后的状态。
- **调用树**展示类型检查器在某个项上发起的递归调用的精确序列，并标出每次调用对应的类型规则。

标有*代码中*的提示框指向实现刚才所定义内容的 Rust 函数。练习附有解答，默认折叠，需要时再展开。

## 自己运行代码

代码仓库包含内核、一个命令行运行器，以及本书用到的示例脚本。

```text
cargo run -- examples/identity.leanmini
cargo run -- examples/nat-reflexivity.leanmini
cargo run -- examples/zero-add.leanmini
cargo run -- examples/generic-list.leanmini
cargo run -- examples/generic-vec.leanmini
cargo test
```

不带参数运行 `cargo run` 会启动一个交互式会话，逐行接受同样的命令，这门语言由[附录 E](e-leanmini-reference.md) 描述。

源码的组织顺序与本书一致。

| 文件 | 内容 | 章节 |
|---|---|---|
| `src/term.rs` | 项的表示 | 2 |
| `src/typecheck.rs` | 类型推断与类型检查 | 5、6 |
| `src/substitution.rs` | 自由变量、替换、α 等价 | 11 |
| `src/reduction.rs` | 弱头范式、规范化、定义相等 | 12 |
| `src/declaration.rs` | 签名：常量、定义、归纳类型元数据 | 7、8 |
| `src/inductive/` | 检查归纳声明并生成递归子 | 8 |
| `src/proof.rs` | 目标、证明状态与策略 | 10 |
| `src/syntax.rs` | 脚本语言的解析器 | 附录 E |
| `src/main.rs` | 命令行运行器 | 附录 E |
