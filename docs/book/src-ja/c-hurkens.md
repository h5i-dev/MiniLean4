<div class="lead" markdown="1">

規則 $\mathsf{Type} : \mathsf{Type}$ を認めると、型 $\tPi{p}{\mathsf{Type}}{p}$ を持つ閉じた項が作れてしまい、どんな命題でも証明できるようになります。この付録では、[第 13 章](13-universes.md)の主張を裏づけるその項を具体的に示し、自分自身を含む宇宙がどこで使われているかを突き止めます。

</div>

## 前提となる体系

この付録では、カーネルの宇宙を単一の宇宙 $\mathsf{Type}$ に置き換え、T-Sort と T-Pi の代わりに次の二つの規則を使います。

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \mathsf{Type} : \mathsf{Type}}
\qquad
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \tPi{x}{A}{B} : \mathsf{Type}}
$$

ほかはすべて変わらず、T-Lam、T-App、T-Conv、代入、$\beta$ 簡約もそのままです。目標は、次を満たす閉じた項 $t_{\mathrm{H}}$ を作ることです。

$$
\vdash t_{\mathrm{H}} : \bot, \qquad \bot = \tPi{p}{\mathsf{Type}}{p}.
$$

$t_{\mathrm{H}}\;C : C$ となるので、このような項があればどんな命題 $C$ でも証明できます。

この構成は Girard によるもので、集合論の Burali-Forti のパラドックスを、$\mathsf{Type} : \mathsf{Type}$ をもつ型理論に移し替えたものです [Girard 1972]。以下に示す項は Hurkens による簡略版 [Hurkens 1995] で、1 ページに収まり、$\Pi$、$\lambda$、適用しか使いません。

## 型理論における冪集合

関数 $p : S \to \mathsf{Type}$ は $S$ 上の*述語*、言い換えれば $S$ の*部分集合*として読めます。$p\;x$ に証明がある要素 $x$ が、その部分集合の元です。こうした述語全体の型が $S$ の*冪集合*（power set）です。

$$
\wp S \;=\; S \to \mathsf{Type}.
$$

冪集合を 2 回とった $\wp\wp S = (S \to \mathsf{Type}) \to \mathsf{Type}$ は、$S$ の部分集合の族の型になります。

集合論では、Cantor の定理により $\wp S$ はつねに $S$ より真に大きいので、どんな集合も自分の冪集合の複製を含められず、二重冪集合ならなおさら無理です。パラドックスは、この常識に反して $\wp\wp U$ の複製を含む型 $U$ を土台に組み立てられます。具体的には、$U$ の部分集合の族を $U$ の一つの要素に詰め込む関数 $\tau : \wp\wp U \to U$ と、それを取り出す関数 $\sigma : U \to \wp\wp U$ を用意します。型

$$
U \;=\; \tPi{X}{\mathsf{Type}}{\bigl((\wp\wp X \to X) \to \wp\wp X\bigr)}
$$

は、$\mathsf{Type}$ *全体*にわたって量化することで、これを実現しています。$\mathsf{Type}$ にわたって量化しておきながら、$U$ 自身も $\mathsf{Type}$ の元になっている。$\mathsf{Type} : \mathsf{Type}$ が許してしまい、[第 13 章](13-universes.md) の階層が禁じているのは、まさにこの点です。

## 項

以下の略記はその場で展開されるので、カーネルが目にするのは $\Pi$、$\lambda$、変数、適用だけです。また、$\varphi \to \bot$ を $\neg\varphi$ と書きます。

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

これらの略記を使うと、型 $\bot$ を持つ項は次のように書けます。

$$
\begin{array}{rcl}
t_{\mathrm{H}} &=& (\lambda (h_0 : \tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;\Omega}).\; \\
&& \qquad h_0\;\Delta\;(\tLam{x}{U}{\tLam{h_2}{\sigma\;x\;\Delta}{\tLam{h_3}{\tPi{p}{\wp U}{\sigma\;x\;p \to p\;(\tau\;(\sigma\;x))}}{
     h_3\;\Delta\;h_2\;(\tLam{p}{\wp U}{h_3\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})})}}}) \\
&& \qquad\phantom{h_0\;\Delta\;}(\tLam{p}{\wp U}{h_0\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})})) \\
&& (\tLam{p}{\wp U}{\tLam{h_1}{\tPi{x}{U}{\sigma\;x\;p \to p\;x}}{h_1\;\Omega\;(\tLam{x}{U}{h_1\;(\tau\;(\sigma\;x))})}})
\end{array}
$$

全体は一つの適用で、$h_0$ を束縛する $\lambda$ が、$h_0$ の期待する型を持つ引数（最後の行）に適用されています。その内側では、$h_0$ が二つの引数（$\Delta$ と、$\Delta$ についての証明）に適用され、その結果がさらにもう一つの引数に適用されます。それぞれの意味は以下で説明します。

## 項の仕組み

**詰め込みと取り出し。** 二つの関数 $\tau : \wp\wp U \to U$ と $\sigma : U \to \wp\wp U$ は、この議論に必要な程度には互いに逆になっています。定義を展開して $\beta$ 簡約すると、任意の $t : \wp\wp U$ と $p : \wp U$ について次の等式が得られます。

$$
\sigma\;(\tau\;t)\;p \;\conv\; t\;(\tLam{x}{U}{p\;(\tau\;(\sigma\;x))}).
$$

この等式は公理として置いたものではなく計算の結果で、$t_{\mathrm{H}}$ のいくつかの箇所でカーネルが T-Conv を通して使います。

**$U$ 上の順序。** $\sigma\;x\;p$ を「述語 $p$ は $x$ より下のすべての要素について成り立つ」と読むと、$U$ に順序のようなものが入り、述語と要素について次の二つの概念が定義できます。

- 述語 $p : \wp U$ が*帰納的*であるとは、$x$ より下のすべてについて成り立つなら $x$ についても成り立つこと、すなわち $\tPi{x}{U}{\sigma\;x\;p \to p\;x}$ です。
- 要素 $x : U$ が*整礎*（well-founded）であるとは、すべての帰納的述語が $x$ について成り立つこと、すなわち $\tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;x}$ です。

要素 $\Omega$ は、すべての帰納的述語からなる族を詰め込んだもので、「すべての整礎な要素の集まり」の役を果たすように作られています。Burali-Forti のパラドックスでいえば、すべての順序数の集合にあたります。この集合はそれ自身が順序数なので自分自身の元になり、すべての順序数は整礎であるはずなのに、この集合だけは整礎になりません。

**三つの材料。** $t_{\mathrm{H}}$ を下から上へ読んでいきます。

1. 最後の行 $\tLam{p}{\wp U}{\tLam{h_1}{\cdots}{h_1\;\Omega\;(\tLam{x}{U}{h_1\;(\tau\;(\sigma\;x))})}}$ は、$\Omega$ が整礎であることの証明です。その型 $\tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;\Omega}$ は $h_0$ の型と同じなので、$h_0$ は「$\Omega$ は整礎である」という仮定を表しています。
2. 述語 $\Delta\;y$ は「$y$ は自分自身より下にない」という意味です（厳密には $\tau\;(\sigma\;y)$ について述べていますが、上の等式によりこれは $y$ と同じように振る舞います）。$h_0$ の第二引数、つまり $\tLam{x}{U}{\tLam{h_2}{\cdots}{\cdots}}$ で始まる長い $\lambda$ は、$\Delta$ が帰納的であることを証明しています。そのため $h_0\;\Delta\;(\cdots) : \Delta\;\Omega$ となり、$\Omega$ は自分自身より下にないことがわかります。
3. 残りの引数 $\tLam{p}{\wp U}{h_0\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})}$ は、$\Omega$ の整礎性を、詰め込みの等式で書き換えた述語に適用したものです。これにより、$\Omega$ が自分自身より下に*ある*ことが証明されます。

$\Delta\;\Omega$ は「$\Omega$ は自分自身より下にある」の否定なので、ステップ 2 の結果をステップ 3 の結果に適用すれば、型 $\bot$ の項が得られます。

<aside class="intuition" markdown="1">

この議論の正体は、姿を変えた Burali-Forti のパラドックスです。順序数は整礎であり、すべての順序数の集まり $\Omega$ もまた順序数なので、自分自身の元になります。しかし整礎なものは自分自身の元にはなれません。集合論は、すべての順序数の集まりを集合として認めないことでこの矛盾を避けています。ところが $\mathsf{Type} : \mathsf{Type}$ をもつ型理論では、$U$ が自分自身を含むすべての型にわたって量化できるので、そうした歯止めがありません。

</aside>

## Type : Type が使われる箇所

$t_{\mathrm{H}}$ の型付けは、一か所を除いてどのステップもごく普通のものです。その一か所が $\sigma = \tLam{s}{U}{s\;U\;\tau}$ で、ここでは変数 $s : U$ が型 $U$ 自身に適用されています。$s$ の型は $\tPi{X}{\mathsf{Type}}{\cdots}$ で始まるので、T-App は $U : \mathsf{Type}$ を要求します。ところが $U$ は $\mathsf{Type}$ にわたって量化する $\Pi$ 型であり、宇宙の階層をもつ体系では、このような型は量化する宇宙より一つ*上*のレベルに属します。

$$
\dfrac{\Gamma \vdash \Sort{u} : \Sort{(u+1)} \qquad \Gamma, X : \Sort{u} \vdash B : \Sort{v}}{\Gamma \vdash \tPi{X}{\Sort{u}}{B} : \Sort{\max(u+1, v)}}
$$

[第 13 章](13-universes.md) の T-Pi 規則のもとでは、$U$ はせいぜい $\Sort{(u+1)}$ に属し、$\Sort{u}$ に属することはありません。そのため $s\;U$ には型が付かず、$\sigma$ が書けず、構成全体がこの一つの適用で崩れます。$U$ の本体は $(\wp\wp X \to X) \to \wp\wp X$ で、その結果の $\wp\wp X$ は宇宙への関数型であって命題ではありません。したがって $\mathrm{imax}$ が $U$ を $\Sort{0}$ に落とすことはなく、$\Sort{0}$ の非述語性が抜け道になることもありません。Coquand は、最下層に非述語的な宇宙が一つあるだけなら整合的であることを示しました [Coquand 1988]。一方 Hurkens の項は、非述語的なレベルが二つあればもう多すぎることを示しています [Hurkens 1995]。

## カーネルで再現してみる

カーネルがこの項を受理する様子も、拒否する様子も、自分で確かめられます。変更すべき規則は T-Sort だけで、`src/typecheck.rs` の `infer` にある `Term::Sort(u)` の場合分けがこれを実装しています。

```rust
// T-Sort、出荷時の形: どの宇宙も一つ上の宇宙に属する。
Term::Sort(u) => Ok(Term::Sort(u.checked_add(1).ok_or("universe overflow")?)),
```

右辺を `Ok(Term::Sort(*u))` に置き換えると $\Sort{0} : \Sort{0}$ となるので、全体を通して $\Sort{0}$ を $\mathsf{Type}$ として使います。ほかの変更は要りません。すべての型が $\Sort{0}$ にあれば、$\mathrm{imax}$ 付きの T-Pi 規則はもともとあらゆる $\Pi$ 型に $\Sort{0}$ を割り当てるので、これがそのままこの付録の第二の規則になるからです。この 1 行の変更だけで、`infer` は $t_{\mathrm{H}}$ に対してちょうど $\tPi{p}{\Sort{0}}{p}$ を返します。変更前のカーネルは、予告したとおり $\sigma$ の中の適用 $s\;U$ で型の不一致を報告し、この項を拒否します。

<aside class="warning" markdown="1">

この変更は必ず元に戻してください。カーネルが整合的でなくなるうえに、停止性も壊れます。[第 13 章](13-universes.md) で説明するとおり $t_{\mathrm{H}}$ には正規形がないので、変更後のカーネルに正規化させると、[第 12 章](12-reduction-conversion.md) の簡約の燃料が尽きるまで走り続けます。

</aside>

## 正規形が存在しない理由

[第 14 章](14-properties.md) は、型 $\tPi{P}{\Sort{0}}{P}$ を持つ*正規な*閉じた項が存在しないことを示して、本来の体系の整合性を証明します。その証明のうち、正規項の形を分析する部分は強正規化を使わないので、$\mathsf{Type} : \mathsf{Type}$ のもとでもそのまま通用します。したがって、もし $t_{\mathrm{H}}$ に正規形があれば、それは型 $\bot$ を持つ閉じた正規項になるはずですが、そのような項は存在しえません。型保存性も成り立つので、簡約によって型 $\bot$ から抜け出すこともできません。残る可能性は、$t_{\mathrm{H}}$ がいつまでも簡約され続けることだけです。こうして強正規化が破れ、型検査器の停止性も失われます。Girard のパラドックスは論理の欠陥であると同時に計算の欠陥でもあり、[第 13 章](13-universes.md) の宇宙の設計が論理にとってもアルゴリズムにとっても重要なのはそのためです。

<div class="summary-box" markdown="1">

覚えておくこと

- $\mathsf{Type} : \mathsf{Type}$ のもとでは、型 $U$ は自分自身もその一つであるすべての型にわたって量化するので、自分自身の二重冪集合の複製を含めます。集合にはこれができません。
- Hurkens の項 $t_{\mathrm{H}}$ はこれを Burali-Forti のパラドックスに仕立てたもので、すべての帰納的述語の族を詰め込んだ $\Omega$ は、整礎でありながら自分自身より下にあります。
- 規則 $\mathsf{Type} : \mathsf{Type}$ が使われるのは $\sigma$ の中の適用 $s\;U$ のただ一か所で、宇宙の階層はこの適用に型が付かないようにしています。
- この項には正規形がないので、パラドックスは整合性に加えてカーネルの停止性も壊します。

</div>
