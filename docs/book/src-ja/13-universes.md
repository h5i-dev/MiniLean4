<div class="lead" markdown="1">

$\Sort{0}$ の型は何か。宇宙が自分自身を含むと体系は不整合になる。Lean は最下層を非述語的にした階層 $\Sort{0} : \Sort{1} : \Sort{2} : \cdots$ を使う。この選択は T-Pi 規則に現れる $\imax$ の形も説明する。

</div>

## Sort 0 の型は何か

命題変数は、型理論では仮定 $P : \Sort{0}$ として現れるが、その場所は二つあり、下の左の判断のように文脈の中か、右の判断のように $\lambda$ や $\Pi$ に束縛されてかである。

$$
P : \Sort{0} \vdash \tLam{h}{P}{h} : P \to P
\qquad\text{versus}\qquad
\vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{P \to P}.
$$

左の判断は、外から与えられた一つの固定された $P$ について $P \to P$ を証明するのに対し、右の判断は一つの閉じた項であり、*すべての* $P$ についてそれを証明するので、後から任意の特定の命題に適用できる。図 4.1 の $\forall$ の行が必要とするのはこちらである。

どちらの形も $\Sort{0}$ が型であることを要求する。文脈に $P : \Sort{0}$ を加える C-Ext も、$P : \Sort{0}$ を束縛する T-Lam と T-Pi も、新しい変数の型 $A$ について前提 $\Gamma \vdash A : \Sort{u}$ を持つ。$A = \Sort{0}$ とすると、この前提は、ある $u$ について $\Gamma \vdash \Sort{0} : \Sort{u}$ となるので、命題の宇宙はそれ自身が型を持たなければならない。問題はどの型か、である。

## Type は型ではない

すべての宇宙を、自分自身を含む単一の宇宙 $\mathsf{Type}$ で置き換えたとしよう。

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \mathsf{Type} : \mathsf{Type}}
\qquad
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \tPi{x}{A}{B} : \mathsf{Type}}
$$

$\forall P.\,\varphi$ を $\tPi{P}{\mathsf{Type}}{\varphi^\ast}$ と翻訳すると、$P$ は、$\mathsf{Type}$ 自身とそこから作られるあらゆる型を含む集まりを動く。このような集まりは、型理論における「すべての集合の集合」にあたり、素朴集合論ではこうした集まりが矛盾を導くことが知られている。最もよく知られた例が**ラッセルのパラドックス**であり、$R = \{\, x \mid x \notin x \,\}$ とすると、$R \in R$ も $R \notin R$ も矛盾を導く。

型理論には $x \notin x$ のような所属判定がないので、ラッセルの議論はそのままでは移らない。Girard は代わりに、すべての整列順序の集まりに関する Burali-Forti の関連するパラドックスを翻案し [Girard 1972]、Hurkens が得られた項を簡略化した [Hurkens 1995]。結果は

$$
\vdash t_{\mathrm{H}} : \tPi{P}{\mathsf{Type}}{P},
$$

を満たす閉じた項 $t_{\mathrm{H}}$ であり、体系は不整合である。$\bot$ には証明がないのに $\bot^\ast$ には項があり、これらの規則の上に作られたカーネルはあらゆる文の証明を受け入れてしまう。本質的な材料は、$\mathsf{Type}$ 全体を量化しながら $\mathsf{Type}$ の要素でもある型 $U$ であり、これにより $U$ は自身の二重冪集合の複製を含むことができる。集合には決してできないことである。[付録 C](c-hurkens.md) では $t_{\mathrm{H}}$ を完全な形で示し、その仕組みを説明し、カーネルの一行を変えるだけでこの結果を再現する方法を示す。

被害はアルゴリズムにも及ぶ。型保存性は依然として成り立つので、もし $t_{\mathrm{H}}$ に正規形があれば、それは型 $\tPi{p}{\mathsf{Type}}{p}$ の正規な閉じた項になる。[付録 D](d-proof-consistency.md) の整合性の証明のうち正規な項を分析する部分は強正規化を使っておらず、$\mathsf{Type} : \mathsf{Type}$ にもそのまま移り、そのような正規な項が存在しないことを示す。したがって $t_{\mathrm{H}}$ には正規形がなく、強正規化は破れ、$\Normalize$ はこの項に対して永遠に走り続ける。$\mathsf{Type} : \mathsf{Type}$ を持つカーネルは不健全であるだけでなく、入力によっては停止しない。

<aside class="history" markdown="1">

Martin-Löf の 1971 年の最初の型理論はこの規則を持っており、翌年、それに対して Girard のパラドックスが発見された。それ以来、すべての依存型理論は、宇宙の階層か、自己言及を断ち切る何らかの別の仕掛けを備えている。このパラドックスは珍奇な話ではなく、自分自身を含む宇宙は*自明な*設計であり、その自明な設計が間違っているのである。

</aside>

## 最下層が非述語的な階層

第二の答えは、$\Sort{0}$ はより大きな宇宙に住み、その宇宙はさらに大きな宇宙に住む、というものである。

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
\qquad\text{so}\qquad
\Sort{0} : \Sort{1} : \Sort{2} : \cdots.
$$

自分自身を含む宇宙はない。$\Pi$ 型はある宇宙から引数を取り、別の宇宙の型を返すので、T-Pi は $\Pi$ 型それ自身がどの宇宙に属するかも言わなければならず、Lean の答えは関数 $\imax$ を使う。

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash B : \Sort{v}}{\Gamma \vdash \tPi{x}{A}{B} : \Sort{\imax(u, v)}}\rulename{T-Pi}
\qquad
\imax(u, v) =
\begin{cases}
0 & \text{if } v = 0, \\
\max(u, v) & \text{otherwise.}
\end{cases}
$$

$\imax$ の場合分けにより、$\Pi$ 型は本体が命題のとき*非述語的*になり、それ以外のとき*述語的*になる。下で $A$ と $B$ の宇宙を選び、$\Pi$ 型がどこに落ち着くかを見てほしい。

<div class="explorer" data-kind="universes"></div>

**命題は非述語的である。** 本体 $B$ が命題なら（$v = 0$）、何を量化していようと $\Pi$ 全体が命題になり、特に $(\forall P.\,\varphi)^\ast = \tPi{P}{\Sort{0}}{\varphi^\ast}$ は、$\Sort{0}$ 全体を量化しているにもかかわらず $\Sort{0}$ に属する。自分自身を量化する型を含む宇宙を**非述語的**（impredicative）と呼ぶ。翻訳された式はすべて $\Sort{0}$ に属するので、$\forall$ 除去の前提 $\psi^\ast : \Sort{0}$ は常に成り立ち、全称文は任意の命題で、自分自身でさえも、具体化できる。たとえば $\mathit{id} = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ とすると、

$$
\mathit{id} : \tPi{P}{\Sort{0}}{P \to P}
\qquad\text{and}\qquad
\tPi{P}{\Sort{0}}{P \to P} : \Sort{0},
$$

なので、$\mathit{id}\;(\tPi{P}{\Sort{0}}{P \to P})\;\mathit{id}$ は型が付き、その型は $\tPi{P}{\Sort{0}}{P \to P}$ である。同じ場合分けにより、$\Nat$ が $\Sort{1}$ に属するにもかかわらず $\forall n : \Nat,\, n + 0 = n$ は命題になり、[第 7 章](07-inductive-nat.md) の帰納法はこれに依存していた。

<div class="playground" data-file="impredicative"><pre># 「すべての命題は自分自身を含意する」はそれ自身が命題なので、
# 自分自身で具体化できる。
def id : forall (P : Sort 0), P -> P := fun (P : Sort 0) => fun (h : P) => h
def self : forall (P : Sort 0), P -> P := id (forall (P : Sort 0), P -> P) id

# 一つ上のレベルの同様の文は、自分自身の実例では「ない」。
# forall (A : Sort 1), A -> A は Sort 1 ではなく Sort 2 に属する。
def idT : forall (A : Sort 1), A -> A := fun (A : Sort 1) => fun (a : A) => a
def selfT : forall (A : Sort 1), A -> A := idT (forall (A : Sort 1), A -> A) idT</pre></div>

**型は述語的である。** 本体が命題でなければ（$v \ge 1$）、$\Pi$ は二つの宇宙のうち大きいほうに属するので、$\Sort{u}$ を量化する型は $\Sort{(\max(u+1, v))}$ に属し、これは決して $\Sort{u}$ にはならない。

$$
\dfrac{
  \dfrac{}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
  \qquad
  \Gamma, x : \Sort{u} \vdash B : \Sort{v}
}{\Gamma \vdash \tPi{x}{\Sort{u}}{B} : \Sort{(\max(u+1, v))}}\rulename{T-Pi}
$$

この性質を**述語性**（predicativity）と呼ぶ。たとえば型上の恒等関数 $\tLam{A}{\Sort{1}}{\tLam{a}{A}{a}}$ の型は $\tPi{A}{\Sort{1}}{A \to A}$ で、これは $\Sort{2}$ に属するので、自分自身の型には適用できないが、$\Sort{2}$ での複製なら適用できる。各レベルはその下のレベルを含み、実際には数レベルあれば足り、より高いレベルが現れるのは、すべての小さい圏の圏のような、大きな集まりを量化するときである。

**なぜ安全なのか。** 非述語性は前節が警告した自己言及に似ているが、閉じ込められており、$\Sort{0}$ は $\Sort{0}$ を量化する型を含むが、$\Sort{0}$ は自分自身の要素ではない。Coquand は、最下層に非述語的な宇宙が一つあっても整合的であることを示した [Coquand 1988] が、*二つ*のレベルが非述語的になると、すでに Girard のパラドックスが導出できる [Hurkens 1995]。これらの規則のもとで体系は整合的かつ強正規化的である（[第 14 章](14-properties.md)）。

<aside class="intuition" markdown="1">

なぜ命題は非述語的でよく、型はそうではないのか。命題の証明にはプログラムが取り出せるデータがなく、第 8 章の消去制限もその性質を守っている。すべての命題を量化して命題を定義するのは、すべての集合に言及する性質で集合を定義するのに似ている。作ったものが量化の対象に含まれ、しかも中身を調べられるなら危険だが、仮定として使うことしかできなければ同じ問題は起きない。パラドックスには作ったものを*調べる*操作が必要であり、命題の証明ではそれができない。

</aside>

## Lean との比較

Lean [de Moura and Ullrich 2021] では、$\Sort{0}$ が `Prop`、$\Sort{(u+1)}$ が `Type u` であり、$\Pi$ 型には上と同じく $\imax$ で宇宙が割り当てられる。違いは二つ残る。

第一に、Lean の `Prop` には**定義的証明無関係性**（definitional proof irrelevance）があり、同じ命題の任意の二つの証明は定義的に等しい。本書の変換は証明を同一視しないが、これを加えると変換が型に依存するようになり、[第 12 章](12-reduction-conversion.md) の単純な「正規化して比較する」検査では足りなくなる。

第二に、Lean には**宇宙多相**（universe polymorphism）があり、定義をすべてのレベル $u$ について一度に述べられるので、$\imax$ はレベル*変数*に対しても重要になり、$\imax(u, v) \le w$ のような制約が記号的に解かれる。本書の体系では、すべてのレベルは具体的な数である。

次の表に設計の選択肢をまとめる。

| 設計 | 量化できる範囲 | 欠点 |
|---|---|---|
| 宇宙なし | 値のみ | 「すべての命題について」と言えない |
| $\mathsf{Type} : \mathsf{Type}$ | すべて | 不整合 |
| 二つのソート $\ast : \square$ | $\ast$ のみ | $\square$ 自身に型がない |
| $\max$ を使う $\Sort{u} : \Sort{(u+1)}$ | 任意のレベル | 命題を量化する $\forall$ が命題にならない |
| $\imax$ を使う $\Sort{u} : \Sort{(u+1)}$（Lean） | 任意のレベル | 正規化の証明が難しくなる |

<aside class="code" markdown="1">

本章の内容はすべて、`src/typecheck.rs` の `infer` の二行に収まる。`Sort(u)` の場合は `Sort(u + 1)` を返し、`Pi` の場合は本体のレベルが `0` なら `Sort(0)` を、そうでなければ最大値を返す。[付録 C](c-hurkens.md) は、最初の行を `Sort(u)` を返すように変えるとカーネルが Hurkens の項を受け入れるようになることを示す。

</aside>

## 演習

<div class="exercise" markdown="1">

$\tPi{A}{\Sort{1}}{\tPi{P}{A \to \Sort{0}}{\tPi{a}{A}{P\;a}}}$ の宇宙を計算せよ。これは「すべての型の上のすべての述語がいたるところで成り立つ」という文である（偽だが整形式である）。

<details markdown="1">
<summary>解答</summary>

最も内側から。$P\;a : \Sort{0}$ なので $\tPi{a}{A}{P\;a} : \Sort{\imax(1, 0)} = \Sort{0}$ である。次に $A \to \Sort{0}$ の宇宙は $\imax(1, 1) = 1$（本体 $\Sort{0}$ の型は $\Sort{1}$）なので、真ん中の $\Pi$ の宇宙は $\imax(1, 0) = 0$ である。最後に $\Sort{1} : \Sort{2}$ で本体は $\Sort{0}$ にあるので、$\imax(2, 0) = 0$ を得るので、文全体は命題である。$\imax$ の代わりに $\max$ なら $\Sort{2}$ に落ち着く。

</details>

</div>

<div class="exercise" markdown="1">

プレイグラウンドの `selfT` の定義が拒否される理由を、関係する規則と二つの宇宙を挙げて説明せよ。

<details markdown="1">
<summary>解答</summary>

`idT` は引数 $A : \Sort{1}$ を期待するが、与えられた引数は $\tPi{A}{\Sort{1}}{A \to A}$ で、T-Pi によるその宇宙は $\max(2, 1) = 2$ なので、$\Check$ は $\Sort{2}$ と $\Sort{1}$ を比較して失敗し、カーネルはその適用で型の不一致を報告する。これが述語性であり、$\Sort{1}$ を量化する型は $\Sort{1}$ に属さない。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 命題変数が $\lambda$ と $\Pi$ に束縛されるので、$\Sort{0}$ には型が必要である。
- 自分自身を含む宇宙は不整合であり（Girard、Hurkens）、正規化も壊す。
- 階層 $\Sort{u} : \Sort{(u+1)}$ は自己包含を避け、$\imax$ は命題を非述語的に、それ以外をすべて述語的にする。
- 最下層に非述語的な宇宙が一つなら安全で、二つなら安全でない。Lean は同じ設計の上に証明無関係性と宇宙多相を加えている。

</div>
