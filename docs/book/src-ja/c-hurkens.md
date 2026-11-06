<div class="lead" markdown="1">

[第 13 章](13-universes.md) は、自分自身を含む単一の宇宙があると型理論が整合的でなくなると述べたのは、型 $\tPi{p}{\mathsf{Type}}{p}$ をもつ閉じた項、つまりあらゆる命題の証明が存在するからである。この付録ではその項を完全な形で与え、背後にある考え方を説明し、規則 $\mathsf{Type} : \mathsf{Type}$ がどこで使われるかを正確に示すので、宇宙の階層がなぜこの構成を阻むのかが見えるはずである。

</div>

## 設定

この付録を通して、カーネルの宇宙は単一の宇宙 $\mathsf{Type}$ に置き換え、T-Sort と T-Pi の代わりに次の二つの規則を使う。

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \mathsf{Type} : \mathsf{Type}}
\qquad
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \tPi{x}{A}{B} : \mathsf{Type}}
$$

それ以外はすべて変わらず、T-Lam、T-App、T-Conv、代入、$\beta$ 簡約はそのままである。目標は次を満たす閉じた項 $t_{\mathrm{H}}$ である。

$$
\vdash t_{\mathrm{H}} : \bot, \qquad \bot = \tPi{p}{\mathsf{Type}}{p}.
$$

このような項は、$t_{\mathrm{H}}\;C : C$ なので、あらゆる命題 $C$ を証明する。

この構成は Girard によるもので、集合論の Burali-Forti のパラドックスを $\mathsf{Type} : \mathsf{Type}$ をもつ型理論に移植したものである [Girard 1972]。以下に示す項は Hurkens による簡略版 [Hurkens 1995] で、1 ページに収まり、$\Pi$、$\lambda$、適用以外は何も使わない。

## 型理論における冪集合

関数 $p : S \to \mathsf{Type}$ は $S$ 上の*述語*、言い換えれば $S$ の*部分集合*と読み、$p\;x$ に証明がある要素 $x$ がその元である。そのような述語すべての型が $S$ の*冪集合*（power set）である。

$$
\wp S \;=\; S \to \mathsf{Type}.
$$

これを 2 回適用した $\wp\wp S = (S \to \mathsf{Type}) \to \mathsf{Type}$ は、$S$ の部分集合の族の型である。

集合論では、Cantor の定理により $\wp S$ は常に $S$ より真に大きいので、どんな集合も自分の冪集合の複製を含まず、二重冪集合ならなおさらである。パラドックスは、これに反して $\wp\wp U$ の複製を含む型 $U$ の上に組み立てられる。すなわち、$U$ の部分集合の族を $U$ の一つの要素に詰め込む関数 $\tau : \wp\wp U \to U$ と、それを再び取り出す関数 $\sigma : U \to \wp\wp U$ がある。型

$$
U \;=\; \tPi{X}{\mathsf{Type}}{\bigl((\wp\wp X \to X) \to \wp\wp X\bigr)}
$$

は、$\mathsf{Type}$ *全体*にわたって量化することでこれを実現する。$\mathsf{Type}$ にわたって量化しながら $U$ 自身が $\mathsf{Type}$ の元であることこそ、$\mathsf{Type} : \mathsf{Type}$ が許し、[第 13 章](13-universes.md) の階層が禁じるものである。

## 項

以下の略記はその場で展開され、カーネルが見るのは $\Pi$、$\lambda$、変数、適用だけである。$\varphi \to \bot$ を $\neg\varphi$ と書く。

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

これらの略記を使うと、型 $\bot$ をもつ項は次のようになる。

$$
\begin{array}{rcl}
t_{\mathrm{H}} &=& (\lambda (h_0 : \tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;\Omega}).\; \\
&& \qquad h_0\;\Delta\;(\tLam{x}{U}{\tLam{h_2}{\sigma\;x\;\Delta}{\tLam{h_3}{\tPi{p}{\wp U}{\sigma\;x\;p \to p\;(\tau\;(\sigma\;x))}}{
     h_3\;\Delta\;h_2\;(\tLam{p}{\wp U}{h_3\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})})}}}) \\
&& \qquad\phantom{h_0\;\Delta\;}(\tLam{p}{\wp U}{h_0\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})})) \\
&& (\tLam{p}{\wp U}{\tLam{h_1}{\tPi{x}{U}{\sigma\;x\;p \to p\;x}}{h_1\;\Omega\;(\tLam{x}{U}{h_1\;(\tau\;(\sigma\;x))})}})
\end{array}
$$

形は適用であり、$h_0$ を束縛する $\lambda$ が、（最後の行で）$h_0$ の期待する型の引数に適用されている。内部では $h_0$ が二つの引数、$\Delta$ と $\Delta$ についての証明に適用され、その結果がさらにもう一つの引数に適用される。すべて以下で説明する。

## 項の仕組み

**詰め込みと取り出し。** 二つの関数 $\tau : \wp\wp U \to U$ と $\sigma : U \to \wp\wp U$ は、この議論に必要な程度には互いに逆である。定義を展開して $\beta$ 簡約すると、任意の $t : \wp\wp U$ と $p : \wp U$ について次が得られる。

$$
\sigma\;(\tau\;t)\;p \;\conv\; t\;(\tLam{x}{U}{p\;(\tau\;(\sigma\;x))}).
$$

この等式は公理ではなく計算であり、$t_{\mathrm{H}}$ のいくつかの箇所で T-Conv を通してカーネルに使われる。

**$U$ 上の順序。** $\sigma\;x\;p$ を「述語 $p$ は $x$ より下のすべてについて成り立つ」と読むと、$U$ に順序のようなものが入り、述語と要素について二つのことが言える。

- 述語 $p : \wp U$ が*帰納的*であるとは、$x$ より下のすべてについて成り立つなら $x$ についても成り立つこと、すなわち $\tPi{x}{U}{\sigma\;x\;p \to p\;x}$ である。
- 要素 $x : U$ が*整礎*（well-founded）であるとは、すべての帰納的述語が $x$ について成り立つこと、すなわち $\tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;x}$ である。

要素 $\Omega$ は、すべての帰納的述語からなる族を詰め込んだもので、「すべての整礎な要素の集まり」の役を演じるように作られている。Burali-Forti のパラドックスでは、これはすべての順序数の集合にあたり、それ自身が順序数であり、したがって自分自身の元であり、したがってすべての順序数が整礎であるにもかかわらず整礎でない。

**三つの材料。** $t_{\mathrm{H}}$ を下から上へ読む。

1. 最後の行 $\tLam{p}{\wp U}{\tLam{h_1}{\cdots}{h_1\;\Omega\;(\tLam{x}{U}{h_1\;(\tau\;(\sigma\;x))})}}$ は、$\Omega$ が整礎であることを証明する。その型は $\tPi{p}{\wp U}{(\tPi{x}{U}{\sigma\;x\;p \to p\;x}) \to p\;\Omega}$ で、これは $h_0$ の型なので、$h_0$ は「$\Omega$ は整礎である」を表す。
2. 述語 $\Delta\;y$ は「$y$ は自分自身より下にない」と言っている（厳密には $\tau\;(\sigma\;y)$ について述べているが、上の等式によりこれは $y$ と同じように振る舞う）。$h_0$ の第二引数、$\tLam{x}{U}{\tLam{h_2}{\cdots}{\cdots}}$ で始まる長い $\lambda$ は、$\Delta$ が帰納的であることを証明するので、$h_0\;\Delta\;(\cdots) : \Delta\;\Omega$、つまり $\Omega$ は自分自身より下にない。
3. 残りの引数 $\tLam{p}{\wp U}{h_0\;(\tLam{y}{U}{p\;(\tau\;(\sigma\;y))})}$ は、$\Omega$ が自分自身より下に*ある*ことを、$\Omega$ の整礎性を詰め込みの等式で変換した述語に適用することで証明する。

$\Delta\;\Omega$ は「$\Omega$ は自分自身より下にある」の否定なので、ステップ 2 の結果をステップ 3 の結果に適用すると型 $\bot$ の項が得られる。

<aside class="intuition" markdown="1">

この議論は Burali-Forti のパラドックスの変装である。順序数は整礎であり、すべての順序数の集まり $\Omega$ は順序数なので、自分自身の元である。しかし整礎なものは自分自身の元にはなれない。集合論は、すべての順序数の集まりを集合と認めないことで逃れるが、$\mathsf{Type} : \mathsf{Type}$ をもつ型理論には、$U$ が自分自身を含むすべてにわたって量化できるので、そのような拒否がない。

</aside>

## Type : Type が使われる場所

$t_{\mathrm{H}}$ の型付けの各ステップは、一つを除いてすべて普通のものである。$\sigma = \tLam{s}{U}{s\;U\;\tau}$ では、変数 $s : U$ が型 $U$ 自身に適用され、$s$ の型は $\tPi{X}{\mathsf{Type}}{\cdots}$ で始まるので、T-App は $U : \mathsf{Type}$ を要求する。ところが $U$ は $\mathsf{Type}$ にわたって量化する $\Pi$ 型であり、宇宙の階層をもつ体系では、そのような型は量化対象の宇宙より一つ*上*のレベルに属する。

$$
\dfrac{\Gamma \vdash \Sort{u} : \Sort{(u+1)} \qquad \Gamma, X : \Sort{u} \vdash B : \Sort{v}}{\Gamma \vdash \tPi{X}{\Sort{u}}{B} : \Sort{\max(u+1, v)}}
$$

[第 13 章](13-universes.md) の T-Pi 規則のもとでは、$U$ はよくても $\Sort{(u+1)}$ に属し、決して $\Sort{u}$ には属さない。したがって $s\;U$ には型が付かず、$\sigma$ は書けず、構成全体がこの一つの適用で崩れる。$U$ の本体は $(\wp\wp X \to X) \to \wp\wp X$ で、その結果 $\wp\wp X$ は宇宙への関数型であって命題ではないため、$\mathrm{imax}$ は $U$ を $\Sort{0}$ に置かず、$\Sort{0}$ の非述語性が扉を開け直すこともない。Coquand は、最下層に非述語的な宇宙が一つあるだけなら整合的であることを示した [Coquand 1988] が、Hurkens の項は、非述語的なレベルが二つあればもう多すぎることを示している [Hurkens 1995]。

## カーネルで再現する

カーネルがこの項を受理し、また拒否する様子を自分で確かめられる。変更すべき規則は T-Sort だけで、これは `src/typecheck.rs` の `infer` にある `Term::Sort(u)` の場合分けで実装されている。

```rust
// T-Sort、出荷時の形: どの宇宙も一つ上の宇宙に属する。
Term::Sort(u) => Ok(Term::Sort(u.checked_add(1).ok_or("universe overflow")?)),
```

右辺を `Ok(Term::Sort(*u))` に置き換えて $\Sort{0} : \Sort{0}$ とし、全体を通して $\Sort{0}$ を $\mathsf{Type}$ として使う。ほかに変更は要らず、すべての型が $\Sort{0}$ にあれば、$\mathrm{imax}$ 付きの T-Pi 規則はすでにあらゆる $\Pi$ 型に $\Sort{0}$ を割り当てており、これがこの付録の第二の規則にほかならない。この 1 行の変更で、`infer` は $t_{\mathrm{H}}$ に対してちょうど $\tPi{p}{\Sort{0}}{p}$ を返す。変更前のカーネルは、上で予告したとおり、$\sigma$ の中の適用 $s\;U$ で型の不一致を報告してこの項を拒否する。

<aside class="warning" markdown="1">

この変更を残したままにしてはいけない。カーネルが整合的でなくなるだけでなく、停止性も壊れる。[第 13 章](13-universes.md) で説明するように $t_{\mathrm{H}}$ には正規形がないので、変更後のカーネルに正規化を頼むと、[第 12 章](12-reduction-conversion.md) の簡約の燃料が尽きるまで走り続ける。

</aside>

## 正規形が存在しない理由

[第 14 章](14-properties.md) は、型 $\tPi{P}{\Sort{0}}{P}$ をもつ*正規な*閉じた項が存在しないことを示して、本来の体系の整合性を証明する。その証明のうち正規項の形を分析する部分は強正規化を使わず、$\mathsf{Type} : \mathsf{Type}$ のもとでもそのまま通る。したがって、もし $t_{\mathrm{H}}$ に正規形があれば、それは型 $\bot$ をもつ閉じた正規項になるが、そのようなものは存在しえない。型保存性も成り立つので、簡約によって型 $\bot$ から逃れることもできない。残る可能性はただ一つ、$t_{\mathrm{H}}$ が永遠に簡約され続けることであり、強正規化が破れ、それとともに型検査器の停止性も失われる。Girard のパラドックスは論理上の欠陥であるだけでなく計算上の欠陥でもあり、[第 13 章](13-universes.md) の宇宙の設計が、論理と同じくらいアルゴリズムにとっても重要である理由はここにある。

<div class="summary-box" markdown="1">

覚えておくこと

- $\mathsf{Type} : \mathsf{Type}$ のもとでは、型 $U$ は自分もその一つでありながらすべての型にわたって量化するので、自分自身の二重冪集合の複製を含むが、集合にはそれができない。
- Hurkens の項 $t_{\mathrm{H}}$ はこれを Burali-Forti のパラドックスに仕立て、すべての帰納的述語の族を詰め込んだ $\Omega$ は、整礎でありながら自分自身より下にある。
- 規則 $\mathsf{Type} : \mathsf{Type}$ が使われるのはただ一か所、$\sigma$ の中の適用 $s\;U$ であり、宇宙の階層はこの適用に型が付かないようにする。
- この項には正規形がないので、パラドックスは整合性だけでなくカーネルの停止性も壊す。

</div>
