<div class="lead" markdown="1">

カーネルの仕事は、判断「項 $t$ は型 $A$ を持つ」を判定することである。本章ではこの判断を少数の推論規則、すなわち項の種類ごとに一つと、型の内部で計算を許すための追加の一つで定義する。各規則を下から上へ読めば項を検査する手順になり、その手順が第 5 章のアルゴリズムになる。

</div>

## 文脈と判断

$f\;p$ のような項は単独では検査できず、その型は $f$ と $p$ が何であるかに依存する。**文脈**（context）$\Gamma$ がその情報を記録する。文脈は仮定の順序付きリスト

$$
\Gamma \;=\; x_1 : A_1,\; x_2 : A_2,\; \ldots,\; x_n : A_n,
$$

であり、スコープ内の各変数の型を与える。$\dom(\Gamma)$ は名前の集合 $\{x_1, \ldots, x_n\}$ を表し、空の文脈は $\cdot$ と書く。

順序は重要であり、$P : \Sort{0},\; h : P$ のように、後の型が前の変数に言及してよい。仮定 $h : P$ は、$P$ が命題だとわかってはじめて意味を持つ。文脈の中の名前は互いに異なることを要求するので、文脈は名前から型への辞書のように使えるが、その項目が順に互いへ依存する辞書である。

二つの判断を同時に定義する。

- $\ctxok{\Gamma}$ は文脈 $\Gamma$ が*整形式*（well formed）であること、すなわち仮定された各型がその手前の文脈において型であることを意味する。
- $\Gamma \vdash t : A$ は、$\Gamma$ の仮定のもとで項 $t$ が型 $A$ を持つことを意味する。

Curry-Howard の目で見れば、$\Gamma \vdash t : A$ は、$t$ が仮定 $\Gamma$ からの $A$ の証明であると言っている。

## 規則

図 3.1 にすべての規則を挙げる。各規則は線の上に前提、下に結論を持ち、前提がすべて成り立てば結論が成り立つ。右側の規則名は本書全体で使う。

<div class="rulebox" markdown="1">

<p class="caption">図 3.1. 整形式の文脈（上段）と型付け規則。</p>

$$
\dfrac{\phantom{\ctxok{\Gamma}}}{\ctxok{\cdot}}\rulename{C-Empty}
\qquad
\dfrac{\ctxok{\Gamma} \qquad \Gamma \vdash A : \Sort{u} \qquad x \notin \dom(\Gamma)}{\ctxok{\Gamma, x : A}}\rulename{C-Ext}
$$

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
\qquad
\dfrac{\ctxok{\Gamma} \qquad (x : A) \in \Gamma}{\Gamma \vdash x : A}\rulename{T-Var}
$$

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash B : \Sort{v}}{\Gamma \vdash \tPi{x}{A}{B} : \Sort{\imax(u, v)}}\rulename{T-Pi}
$$

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash t : B}{\Gamma \vdash \tLam{x}{A}{t} : \tPi{x}{A}{B}}\rulename{T-Lam}
$$

$$
\dfrac{\Gamma \vdash f : \tPi{x}{A}{B} \qquad \Gamma \vdash a : A}{\Gamma \vdash f\;a : \subst{B}{x}{a}}\rulename{T-App}
$$

$$
\dfrac{\Gamma \vdash t : A \qquad \Gamma \vdash B : \Sort{u} \qquad A \conv B}{\Gamma \vdash t : B}\rulename{T-Conv}
$$

</div>

規則のうち二つは項に対する操作を使っているが、続く数章ではそれをブラックボックスとして扱う。

**代入。** T-App は、$B$ の中の $x$ の自由な出現をすべて $a$ で置き換えた結果を $\subst{B}{x}{a}$ と書く。たとえば $\subst{(P \to P)}{P}{Q} = Q \to Q$ である。束縛子の内側で名前を置き換えるには注意が要り、それは[第 11 章](11-substitution-alpha.md)で説明するが、それまでは直観的な意味で十分である。

**定義的等価。** T-Conv は、$A$ と $B$ がカーネルに機械的に判定できる意味で「同じ型」であるとき、$A \conv B$ と書く。二種類の違いが無視される。

- 束縛変数の名前。$\tPi{P}{\Sort{0}}{P \to P}$ と $\tPi{Q}{\Sort{0}}{Q \to Q}$ は同じ命題を述べている。この点だけが異なる項を *α 同値*と呼び、$A \alphaeq B$ と書く。
- 計算。$\mathit{Id} = \tLam{X}{\Sort{0}}{X}$ とすると、$\mathit{Id}\;P$ は $X$ に $P$ を代入して $P$ に計算されるので、$\mathit{Id}\;P$ の証明は $P$ の証明として数えられるべきである。計算の一歩 $(\tLam{x}{A}{t})\;s \betared \subst{t}{x}{s}$ を *β 簡約*（beta-reduction）と呼ぶ。

カーネルは $A \conv B$ を、両辺を可能な限り計算してから結果が α 同値かどうかを調べることで判定する。[第 12 章](12-reduction-conversion.md)でこれを正確に定義する。

## 規則の読み方

規則は下から上へ、結論を立てるには前提を立てよという手順として読むのがよい。

**C-Empty と C-Ext。** 文脈は仮定を一つずつ加えて作り、新しい仮定の型はそれ自体が型でなければならない。側条件 $x \notin \dom(\Gamma)$ は同じ名前の仮定が二つあることを禁じるが、束縛変数の名前は重要でないので、これは何も制限していない。衝突しそうな束縛子は、先に名前を付け替えればよい。この条件を省いたカーネルで何が起きるかは[第 11 章](11-substitution-alpha.md#variable-capture-in-contexts)で示す。

**T-Sort。** どの宇宙も次の宇宙に住み、$\Sort{0} : \Sort{1}$、$\Sort{1} : \Sort{2}$、以下同様である。宇宙が自分自身の型にはなれない理由は[第 13 章](13-universes.md)で説明する。

**T-Var。** 変数は文脈が割り当てる型を持ち、論理的には仮定を使うことにあたる。

**T-Pi。** $A$ が型で、$x : A$ を仮定したうえで $B$ が型なら、$\tPi{x}{A}{B}$ は型である。結果の宇宙は $\imax(u, v)$ で、$v = 0$ なら $0$、そうでなければ $\max(u, v)$ である。言葉にすると、$\Pi$ 型は本体が命題でありさえすれば何の上で量化していようと命題であり、そうでなければ二つの宇宙の大きい方に住む。論理的には、この規則は $A \to B$ と $\forall x{:}A.\,B$ がいつ整形式の主張であるかを言っている。

**T-Lam。** $A$ から $B$ への関数を作るには、$x : A$ を仮定して型 $B$ の項 $t$ を作る。本体の型 $B$ は $x$ に言及してよく、結果の $\Pi$ 型にそのまま残る。依存性が入り込むのはここである。論理的には、これは含意と全称量化子の導入規則であり、$A \to B$ を証明するには $A$ を仮定して $B$ を証明する。

**T-App。** $f$ が各 $x : A$ を $B$ の要素に写し、$a : A$ なら、$f\;a$ は $B$ の $x$ を $a$ で置き換えた型を持つ。$B$ が $x$ に言及しないなら、これは $A \to B$ と $A$ から $B$ を結論するモーダスポネンスであり、言及するなら全称命題の具体化である。たとえば $f : \tPi{n}{\Nat}{n + 0 = n}$ なら $f\;3 : 3 + 0 = 3$ である（自然数は[第 7 章](07-inductive-nat.md)で登場する）。

**T-Conv。** 計算を除いて等しい型は交換可能であり、$h : \mathit{Id}\;P$ から $h : P$ を結論してよい。前提 $\Gamma \vdash B : \Sort{u}$ は、新しい型がそれ自体型であることを保証する。これは、使うかどうかが $t$ の形から決まらない唯一の規則であり、この事実は[第 5 章](05-algorithm.md)のアルゴリズムで効いてくる。

<aside class="intuition" markdown="1">

どの規則も、関数についての小さな常識である。T-Lam は関数の作り方、T-App は使い方、T-Pi は関数型がいつ意味を持つか、T-Var と T-Sort は基本的なものが何であるか、T-Conv は型の内部で計算しても意味は変わらないことを言う。規則の中にとくに「論理的」なものは何もなく、論理は規則を Curry-Howard を通して読んだ帰結であり、それを[第 4 章](04-logic.md)で正確にする。

</aside>

## 適用が重要な理由

何かを組み立てる T-Lam や T-Pi のほうが重要に見えるかもしれないが、T-App がなければ、証明は仮定を返せても*使う*ことはできない。おおまかに言えば、証明できるのは $P \to Q \to P$ のように、結論が仮定の一つそのものである命題だけになる。合成

$$
(P \to Q) \to (Q \to R) \to P \to R,
$$

の証明は $\tLam{f}{P \to Q}{\tLam{g}{Q \to R}{\tLam{p}{P}{g\,(f\,p)}}}$ で、$f$ を適用してから $g$ を適用する。仮定を言い直す以上のことをする証明はすべて T-App を通る。そして依存型理論では、T-App は代入が起きる場所でもあり、したがって微妙な点の大半が潜む場所でもある。

## はじめての導出

導出とは、規則の実例からなる木で、その根が立証したい判断であるものをいう。$\tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ が $\tPi{P}{\Sort{0}}{P \to P}$ を証明する導出を示す。$\Gamma_1 = P : \Sort{0}$、$\Gamma_2 = \Gamma_1, h : P$ と書き、整形式性の前提 $\ctxok{\Gamma}$ は定型なので省く。

$$
\dfrac{
  \dfrac{}{\cdot \vdash \Sort{0} : \Sort{1}}\rulename{T-Sort}
  \qquad
  \dfrac{
    \dfrac{}{\Gamma_1 \vdash P : \Sort{0}}\rulename{T-Var}
    \qquad
    \dfrac{}{\Gamma_2 \vdash h : P}\rulename{T-Var}
  }{\Gamma_1 \vdash \tLam{h}{P}{h} : \tPi{h}{P}{P}}\rulename{T-Lam}
}{\cdot \vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}}\rulename{T-Lam}
$$

カーネルが組み立てるのはこの木であり、下の表示では各節点が規則の一回の適用で、それが立証する判断を伴う。呼び出しビューに切り替えると、この木を生み出す再帰として上から下へ読める。項を自分のものに置き換えて、どの規則が発火するか見てみてほしい。

<div class="explorer" data-kind="derive" data-view="tree" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

二つ観察しておく。第一に、木の形は項の形に従い、根に $\lambda$、その下に $\lambda$、葉に変数である。第二に、根の型は $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$ だが、述べた命題は $\tPi{P}{\Sort{0}}{P \to P}$ だった。両者は束縛変数の名前（$h$ か、矢印の無名の `_` か）だけが異なるので α 同値であり、T-Conv がその隙間を埋める。[第 6 章](06-worked-examples.md)でこの例をアルゴリズムで再訪する。

<aside class="code" markdown="1">

本章の規則は `src/typecheck.rs` の `Kernel::infer` と `Kernel::check` が実装しており、[第 5 章](05-algorithm.md)で一行ずつ読む。文脈は `src/declaration.rs` の Rust 型 `Context = Vec<(String, Term)>`、すなわち名前と型の対のベクトルで、末尾から探索するので、同じ名前についてはもっとも新しい仮定が勝つ。

</aside>

## 演習

<div class="exercise" markdown="1">

次の各判断を下から上へ処理するのはどの規則で、どんな前提を生むか。(a) $\Gamma \vdash \tLam{x}{A}{x} : A \to A$。(b) $\Gamma \vdash \Sort{2} : \Sort{3}$。(c) $f : A \to B$ のときの $\Gamma \vdash f\;a : B$。

<details markdown="1">
<summary>解答</summary>

(a) T-Lam で、前提はある $u$ について $\Gamma \vdash A : \Sort{u}$ と $\Gamma, x : A \vdash x : A$ であり、後者は T-Var による。結果の型は $\tPi{x}{A}{A}$ で、束縛子の名前を除けば $A \to A$ である。
(b) T-Sort で、前提は $\ctxok{\Gamma}$ のみ。
(c) T-App で、前提は $\Gamma \vdash f : \tPi{\_}{A}{B}$ と $\Gamma \vdash a : A$ である。`_` は $B$ に現れないので、結論は $\subst{B}{\_}{a} = B$ となる。

</details>

</div>

<div class="exercise" markdown="1">

T-Pi を使って、$\tPi{P}{\Sort{0}}{P \to P}$ と $\tPi{A}{\Sort{1}}{A \to A}$ の宇宙を計算せよ。

<details markdown="1">
<summary>解答</summary>

前者では、$\Sort{0} : \Sort{1}$ なので $u = 1$ であり、$P \to P : \Sort{0}$（再び T-Pi により、$u = v = 0$）なので $v = 0$ である。よって宇宙は $\Sort{\imax(1, 0)} = \Sort{0}$ となり、すべての命題の上で量化する主張はそれ自体が命題である。
後者では $u = 2$ で、$A \to A : \Sort{1}$ なので $v = 1$ であり、$\Sort{\imax(2,1)} = \Sort{2}$ を得る。この非対称性は[第 13 章](13-universes.md)で説明する。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 文脈は互いに異なる仮定 $x : A$ の順序付きリストであり、判断 $\Gamma \vdash t : A$ は、その仮定のもとで $t$ が型 $A$ を持つことを言う。
- 規則は項の種類ごとに一つと、それに計算と束縛変数の付け替えを除いて型を同一視する T-Conv がある。
- T-App は仮定を使う場所であり、代入が起きる場所でもある一方、T-Conv は項の形から引き起こされない唯一の規則である。
- 代入と定義的等価は第 III 部までブラックボックスとして扱う。

</div>
