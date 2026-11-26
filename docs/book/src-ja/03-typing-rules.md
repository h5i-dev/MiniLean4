<div class="lead" markdown="1">

「項 $t$ は型 $A$ を持つ」という判断は、項の種類ごとに用意された規則と、型の中で計算してよいとする規則によって決まります。これらの規則を下から上へ読むと、第 5 章で実装する検査の手順が見えてきます。

</div>

## 文脈と判断

$f\;p$ のような項は、それだけを見ても検査できません。型は $f$ と $p$ が何であるかによって決まるからです。その情報を記録するのが**文脈**（context）$\Gamma$ です。文脈は仮定の順序付きリスト

$$
\Gamma \;=\; x_1 : A_1,\; x_2 : A_2,\; \ldots,\; x_n : A_n,
$$

で、スコープ内の各変数の型を与えます。$\dom(\Gamma)$ は名前の集合 $\{x_1, \ldots, x_n\}$ を表し、空の文脈は $\cdot$ と書きます。

順序には意味があり、$P : \Sort{0},\; h : P$ のように、後ろの型が前の変数に言及してもかまいません。仮定 $h : P$ は、$P$ が命題だとわかってはじめて意味を持ちます。文脈の中の名前は互いに異なるものとするので、文脈は名前から型を引く辞書のように使えます。ただし、項目どうしが前から順に依存し合う辞書です。

二つの判断を同時に定義します。

- $\ctxok{\Gamma}$ は、文脈 $\Gamma$ が*整形式*（well formed）であること、つまり仮定した各型がそれより手前の文脈で型になっていることを表します。
- $\Gamma \vdash t : A$ は、$\Gamma$ の仮定のもとで項 $t$ が型 $A$ を持つことを表します。

Curry-Howard の見方では、$\Gamma \vdash t : A$ は「$t$ は仮定 $\Gamma$ から $A$ を導く証明である」と読めます。

## 規則

図 3.1 にすべての規則を挙げます。各規則は横線の上に前提、下に結論を書いたもので、前提がすべて成り立てば結論も成り立ちます。右側の規則名は本書全体で使います。

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

規則のうち二つは項に対する操作を使っていますが、続く数章ではその中身には立ち入らず、ブラックボックスとして扱います。

**代入。** T-App に出てくる $\subst{B}{x}{a}$ は、$B$ の中の $x$ の自由な出現をすべて $a$ で置き換えた結果を表します。たとえば $\subst{(P \to P)}{P}{Q} = Q \to Q$ です。束縛子の内側で名前を置き換えるときには注意が必要で、その点は[第 11 章](11-substitution-alpha.md)で説明しますが、それまでは直観的な理解で十分です。

**定義的等価。** T-Conv に出てくる $A \conv B$ は、$A$ と $B$ が、カーネルが機械的に判定できる意味で「同じ型」であることを表します。この判定では、次の二種類の違いを無視します。

- 束縛変数の名前。$\tPi{P}{\Sort{0}}{P \to P}$ と $\tPi{Q}{\Sort{0}}{Q \to Q}$ は同じ命題です。名前だけが異なる項を *α 同値*であるといい、$A \alphaeq B$ と書きます。
- 計算。$\mathit{Id} = \tLam{X}{\Sort{0}}{X}$ とすると、$\mathit{Id}\;P$ は $X$ に $P$ を代入して $P$ に計算されるので、$\mathit{Id}\;P$ の証明は $P$ の証明として扱えるべきです。この計算の一歩 $(\tLam{x}{A}{t})\;s \betared \subst{t}{x}{s}$ を *β 簡約*（beta-reduction）と呼びます。

カーネルは、両辺をできるかぎり計算してから結果が α 同値かどうかを調べることで、$A \conv B$ を判定します。正確な定義は[第 12 章](12-reduction-conversion.md)で与えます。

## 規則の読み方

規則は下から上へ、「結論を得たければ、まず前提を示せ」という手順として読むとわかりやすくなります。

**C-Empty と C-Ext。** 文脈は仮定を一つずつ加えて作ります。新しく加える仮定の型は、それ自体が型でなければなりません。側条件 $x \notin \dom(\Gamma)$ は同じ名前の仮定が二つ並ぶことを禁じていますが、束縛変数の名前に意味はないので、実質的な制限にはなりません。衝突しそうな束縛子は、先に名前を付け替えれば済みます。この条件を省いたカーネルで何が起きるかは[第 11 章](11-substitution-alpha.md#variable-capture-in-contexts)で示します。

**T-Sort。** どの宇宙も一つ上の宇宙に住みます。$\Sort{0} : \Sort{1}$、$\Sort{1} : \Sort{2}$、以下同様です。宇宙が自分自身の型になれない理由は[第 13 章](13-universes.md)で説明します。

**T-Var。** 変数は文脈が割り当てた型を持ちます。論理的には、仮定を使うことにあたります。

**T-Pi。** $A$ が型で、$x : A$ を仮定したもとで $B$ が型なら、$\tPi{x}{A}{B}$ も型です。結果の宇宙は $\imax(u, v)$ で、$v = 0$ なら $0$、そうでなければ $\max(u, v)$ になります。言い換えると、$\Pi$ 型は本体が命題でありさえすれば、何について量化していても命題になり、そうでなければ二つの宇宙のうち大きい方に住みます。論理的には、この規則は $A \to B$ や $\forall x{:}A.\,B$ がどんなときに整形式の主張になるかを定めています。

**T-Lam。** $A$ から $B$ への関数を作るには、$x : A$ を仮定して型 $B$ の項 $t$ を作ります。本体の型 $B$ は $x$ に言及してよく、その言及は結果の $\Pi$ 型にそのまま残ります。依存性が入り込むのはここです。論理的には含意と全称量化子の導入規則にあたり、$A \to B$ を証明するには $A$ を仮定して $B$ を証明すればよい、ということを表しています。

**T-App。** $f$ が各 $x : A$ を $B$ の要素に写し、$a : A$ であれば、$f\;a$ は $B$ の $x$ を $a$ で置き換えた型を持ちます。$B$ が $x$ に言及しない場合は、$A \to B$ と $A$ から $B$ を導くモーダスポネンスに、言及する場合は全称命題の具体化にあたります。たとえば $f : \tPi{n}{\Nat}{n + 0 = n}$ なら $f\;3 : 3 + 0 = 3$ です（自然数は[第 7 章](07-inductive-nat.md)で登場します）。

**T-Conv。** 計算を除いて等しい型は入れ替えてよく、$h : \mathit{Id}\;P$ から $h : P$ を結論できます。前提 $\Gamma \vdash B : \Sort{u}$ は、置き換え先の型もきちんと型であることを保証します。T-Conv は、使うかどうかが $t$ の形からは決まらない唯一の規則で、この事実は[第 5 章](05-algorithm.md)のアルゴリズムで効いてきます。

<aside class="intuition" markdown="1">

どの規則も、関数についての小さな常識を述べているにすぎません。T-Lam は関数の作り方、T-App は使い方、T-Pi は関数型がどんなときに意味を持つか、T-Var と T-Sort は基本となるものが何か、T-Conv は型の中で計算しても意味が変わらないことを言っています。規則そのものにとりたてて「論理的」なものはありません。論理は、規則を Curry-Howard の見方で読んだ結果として現れるもので、その対応は[第 4 章](04-logic.md)で正確に述べます。

</aside>

## 適用が重要な理由

何かを組み立てる T-Lam や T-Pi のほうが重要に見えるかもしれません。しかし T-App がなければ、証明は仮定を返せても、仮定を*使う*ことはできません。おおまかに言えば、証明できるのは $P \to Q \to P$ のように、結論が仮定の一つそのものである命題だけになってしまいます。合成

$$
(P \to Q) \to (Q \to R) \to P \to R,
$$

の証明は $\tLam{f}{P \to Q}{\tLam{g}{Q \to R}{\tLam{p}{P}{g\,(f\,p)}}}$ で、$f$ を適用してから $g$ を適用します。仮定を言い直す以上のことをする証明は、必ず T-App を通ります。さらに依存型理論では、T-App は代入が起きる場所でもあり、微妙な問題の大半はここに潜んでいます。

## はじめての導出

導出とは、規則の実例を積み上げた木で、根が示したい判断になっているものをいいます。ここでは、$\tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ が $\tPi{P}{\Sort{0}}{P \to P}$ を証明することの導出を示します。$\Gamma_1 = P : \Sort{0}$、$\Gamma_2 = \Gamma_1, h : P$ と書き、整形式性の前提 $\ctxok{\Gamma}$ は決まりきっているので省きます。

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

カーネルが組み立てるのはこの木です。下の表示では、各節点が規則の一回の適用を表し、その適用で示される判断が添えられています。呼び出しビューに切り替えると、同じ木を、それを生み出す再帰呼び出しとして上から下へ読めます。項を自分で書き換えて、どの規則が使われるかを確かめてみてください。

<div class="explorer" data-kind="derive" data-view="tree" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

ここで二つのことに注目してください。第一に、木の形は項の形をそのままなぞっていて、根に $\lambda$、その下に $\lambda$、葉に変数があります。第二に、根の型は $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$ ですが、示したかった命題は $\tPi{P}{\Sort{0}}{P \to P}$ でした。両者の違いは束縛変数の名前（$h$ か、矢印の無名の `_` か）だけなので α 同値であり、その差は T-Conv が埋めます。[第 6 章](06-worked-examples.md)では、この例をアルゴリズムの側からもう一度たどります。

<aside class="code" markdown="1">

本章の規則は `src/typecheck.rs` の `Kernel::infer` と `Kernel::check` が実装しており、[第 5 章](05-algorithm.md)で一行ずつ読んでいきます。文脈は `src/declaration.rs` の Rust 型 `Context = Vec<(String, Term)>`、つまり名前と型の組のベクトルです。末尾から探索するので、同じ名前があればいちばん新しい仮定が優先されます。

</aside>

## 演習

<div class="exercise" markdown="1">

次の各判断を下から上へ処理するとき、使われるのはどの規則で、どんな前提が生じるでしょうか。(a) $\Gamma \vdash \tLam{x}{A}{x} : A \to A$。(b) $\Gamma \vdash \Sort{2} : \Sort{3}$。(c) $f : A \to B$ のときの $\Gamma \vdash f\;a : B$。

<details markdown="1">
<summary>解答</summary>

(a) T-Lam です。前提は、ある $u$ についての $\Gamma \vdash A : \Sort{u}$ と、$\Gamma, x : A \vdash x : A$ で、後者は T-Var で示せます。結果の型は $\tPi{x}{A}{A}$ で、束縛子の名前を除けば $A \to A$ と同じです。
(b) T-Sort です。前提は $\ctxok{\Gamma}$ だけです。
(c) T-App です。前提は $\Gamma \vdash f : \tPi{\_}{A}{B}$ と $\Gamma \vdash a : A$ で、`_` は $B$ に現れないので、結論は $\subst{B}{\_}{a} = B$ になります。

</details>

</div>

<div class="exercise" markdown="1">

T-Pi を使って、$\tPi{P}{\Sort{0}}{P \to P}$ と $\tPi{A}{\Sort{1}}{A \to A}$ の宇宙を計算してください。

<details markdown="1">
<summary>解答</summary>

前者では、$\Sort{0} : \Sort{1}$ なので $u = 1$、$P \to P : \Sort{0}$（再び T-Pi により、$u = v = 0$）なので $v = 0$ です。よって宇宙は $\Sort{\imax(1, 0)} = \Sort{0}$ となり、すべての命題について量化する主張も、それ自体が命題になります。
後者では $u = 2$、$A \to A : \Sort{1}$ なので $v = 1$ となり、$\Sort{\imax(2,1)} = \Sort{2}$ が得られます。この非対称性の理由は[第 13 章](13-universes.md)で説明します。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 文脈は、名前の重ならない仮定 $x : A$ の順序付きリストです。判断 $\Gamma \vdash t : A$ は、その仮定のもとで $t$ が型 $A$ を持つことを表します。
- 規則は、項の種類ごとに一つずつと、計算と束縛変数の付け替えを除いて型を同一視する T-Conv からなります。
- T-App は仮定を使う場所であり、代入が起きる場所でもあります。一方 T-Conv は、項の形によらずに適用される唯一の規則です。
- 代入と定義的等価は第 III 部までブラックボックスとして扱います。

</div>
