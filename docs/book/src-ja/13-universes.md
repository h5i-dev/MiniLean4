<div class="lead" markdown="1">

$\Sort{0}$ の型は何でしょうか。宇宙が自分自身を含むと、体系は不整合になります。そこで Lean は、最下層だけを非述語的にした階層 $\Sort{0} : \Sort{1} : \Sort{2} : \cdots$ を使います。T-Pi 規則に現れる $\imax$ の形も、この選択から説明できます。

</div>

## Sort 0 の型は何か

型理論では、命題変数は仮定 $P : \Sort{0}$ として現れます。現れる場所は二つあり、下の左の判断のように文脈に置かれるか、右の判断のように $\lambda$ や $\Pi$ で束縛されるかです。

$$
P : \Sort{0} \vdash \tLam{h}{P}{h} : P \to P
\qquad\text{versus}\qquad
\vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{P \to P}.
$$

左の判断は、外から与えられた一つの固定された $P$ について $P \to P$ を証明しています。一方、右の判断は一つの閉じた項で、*すべての* $P$ についてそれを証明しているので、後から任意の命題に適用できます。図 4.1 の $\forall$ の行で必要なのはこちらです。

どちらの形でも、$\Sort{0}$ が型である必要があります。文脈に $P : \Sort{0}$ を加える C-Ext も、$P : \Sort{0}$ を束縛する T-Lam と T-Pi も、新しい変数の型 $A$ について前提 $\Gamma \vdash A : \Sort{u}$ をもちます。$A = \Sort{0}$ とするとこの前提は、ある $u$ について $\Gamma \vdash \Sort{0} : \Sort{u}$ となります。つまり命題の宇宙そのものが型をもたなければなりません。問題は、それがどの型か、です。

## Type を型にすると矛盾する

まず、すべての宇宙を、自分自身を含む単一の宇宙 $\mathsf{Type}$ で置き換えてみましょう。

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \mathsf{Type} : \mathsf{Type}}
\qquad
\dfrac{\Gamma \vdash A : \mathsf{Type} \qquad \Gamma, x : A \vdash B : \mathsf{Type}}{\Gamma \vdash \tPi{x}{A}{B} : \mathsf{Type}}
$$

$\forall P.\,\varphi$ を $\tPi{P}{\mathsf{Type}}{\varphi^\ast}$ と翻訳すると、$P$ は $\mathsf{Type}$ 自身とそこから作られるあらゆる型を含む集まりを動きます。これは型理論版の「すべての集合の集合」であり、素朴集合論ではこの種の集まりが矛盾を導くことが知られています。最も有名なのが**ラッセルのパラドックス**で、$R = \{\, x \mid x \notin x \,\}$ とおくと、$R \in R$ と $R \notin R$ のどちらを仮定しても矛盾が出ます。

型理論には $x \notin x$ のような所属判定がないので、ラッセルの議論はそのままでは使えません。そこで Girard は、すべての整列順序の集まりにまつわる Burali-Forti のパラドックスを型理論に持ち込み [Girard 1972]、Hurkens がその項を簡略化しました [Hurkens 1995]。得られるのは

$$
\vdash t_{\mathrm{H}} : \tPi{P}{\mathsf{Type}}{P},
$$

を満たす閉じた項 $t_{\mathrm{H}}$ で、体系は不整合になります。$\bot$ には証明がないはずなのに $\bot^\ast$ には項があるので、これらの規則の上に作ったカーネルはどんな文の証明でも受け入れてしまいます。鍵になるのは、$\mathsf{Type}$ 全体を量化しながら、それ自身も $\mathsf{Type}$ の要素である型 $U$ です。このおかげで $U$ は自身の二重冪集合の複製を含めますが、集合では決してこうはなりません。[付録 C](c-hurkens.md) では $t_{\mathrm{H}}$ の全体を示して仕組みを説明し、カーネルを一行変えるだけでこの結果を再現する方法も紹介します。

被害はアルゴリズムにも及びます。型保存性は依然として成り立つので、もし $t_{\mathrm{H}}$ に正規形があれば、それは型 $\tPi{p}{\mathsf{Type}}{p}$ をもつ正規な閉じた項になります。ところが [付録 D](d-proof-consistency.md) の整合性の証明のうち、正規な項を分析する部分は強正規化を使っていないので $\mathsf{Type} : \mathsf{Type}$ にもそのまま当てはまり、そのような正規な項は存在しないことがわかります。したがって $t_{\mathrm{H}}$ には正規形がなく、強正規化は破れ、$\Normalize$ はこの項に対して永遠に走り続けます。$\mathsf{Type} : \mathsf{Type}$ をもつカーネルは不健全なうえに、入力によっては停止すらしません。

<aside class="history" markdown="1">

Martin-Löf が 1971 年に発表した最初の型理論はこの規則をもっており、翌年、Girard がそこにパラドックスを見つけました。それ以来、どの依存型理論も、宇宙の階層か、自己言及を断ち切る別の仕掛けを備えています。これは珍しい落とし穴の話ではありません。自分自身を含む宇宙は誰もが最初に思いつく*自明な*設計であり、その自明な設計が間違っているのです。

</aside>

## 最下層が非述語的な階層

もう一つの答えは、$\Sort{0}$ をより大きな宇宙に住まわせ、その宇宙をさらに大きな宇宙に住まわせる、というものです。

$$
\dfrac{\ctxok{\Gamma}}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
\qquad\text{so}\qquad
\Sort{0} : \Sort{1} : \Sort{2} : \cdots.
$$

こうすれば、自分自身を含む宇宙はなくなります。ただし $\Pi$ 型はある宇宙から引数を取って別の宇宙の型を返すので、T-Pi では $\Pi$ 型自身がどの宇宙に属するかも決めなければなりません。Lean はこれを関数 $\imax$ で決めます。

$$
\dfrac{\Gamma \vdash A : \Sort{u} \qquad \Gamma, x : A \vdash B : \Sort{v}}{\Gamma \vdash \tPi{x}{A}{B} : \Sort{\imax(u, v)}}\rulename{T-Pi}
\qquad
\imax(u, v) =
\begin{cases}
0 & \text{if } v = 0, \\
\max(u, v) & \text{otherwise.}
\end{cases}
$$

$\imax$ の場合分けによって、$\Pi$ 型は本体が命題のときに*非述語的*に、それ以外のときに*述語的*になります。下で $A$ と $B$ の宇宙を選び、$\Pi$ 型がどの宇宙に入るかを確かめてください。

<div class="explorer" data-kind="universes"></div>

**命題は非述語的である。** 本体 $B$ が命題なら（$v = 0$）、何を量化していても $\Pi$ 全体が命題になります。特に $(\forall P.\,\varphi)^\ast = \tPi{P}{\Sort{0}}{\varphi^\ast}$ は、$\Sort{0}$ 全体を量化しているにもかかわらず $\Sort{0}$ に属します。自分自身を量化する型を含む宇宙を**非述語的**（impredicative）と呼びます。翻訳された式はすべて $\Sort{0}$ に属するので、$\forall$ 除去の前提 $\psi^\ast : \Sort{0}$ は常に成り立ち、全称文はどんな命題でも、自分自身でさえも、具体化できます。たとえば $\mathit{id} = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ とすると、

$$
\mathit{id} : \tPi{P}{\Sort{0}}{P \to P}
\qquad\text{and}\qquad
\tPi{P}{\Sort{0}}{P \to P} : \Sort{0},
$$

なので、$\mathit{id}\;(\tPi{P}{\Sort{0}}{P \to P})\;\mathit{id}$ には型が付き、その型は $\tPi{P}{\Sort{0}}{P \to P}$ です。$\Nat$ が $\Sort{1}$ に属するのに $\forall n : \Nat,\, n + 0 = n$ が命題になるのも同じ場合分けのおかげで、[第 7 章](07-inductive-nat.md) の帰納法はこの性質に頼っていました。

<div class="playground" data-file="impredicative"><pre># 「すべての命題は自分自身を含意する」はそれ自身が命題なので、
# 自分自身で具体化できる。
def id : forall (P : Sort 0), P -> P := fun (P : Sort 0) => fun (h : P) => h
def self : forall (P : Sort 0), P -> P := id (forall (P : Sort 0), P -> P) id

# 一つ上のレベルの同様の文は、自分自身の実例では「ない」。
# forall (A : Sort 1), A -> A は Sort 1 ではなく Sort 2 に属する。
def idT : forall (A : Sort 1), A -> A := fun (A : Sort 1) => fun (a : A) => a
def selfT : forall (A : Sort 1), A -> A := idT (forall (A : Sort 1), A -> A) idT</pre></div>

**型は述語的である。** 本体が命題でなければ（$v \ge 1$）、$\Pi$ は二つの宇宙のうち大きいほうに属します。したがって $\Sort{u}$ を量化する型は $\Sort{(\max(u+1, v))}$ に属し、$\Sort{u}$ に入ることは決してありません。

$$
\dfrac{
  \dfrac{}{\Gamma \vdash \Sort{u} : \Sort{(u+1)}}\rulename{T-Sort}
  \qquad
  \Gamma, x : \Sort{u} \vdash B : \Sort{v}
}{\Gamma \vdash \tPi{x}{\Sort{u}}{B} : \Sort{(\max(u+1, v))}}\rulename{T-Pi}
$$

この性質を**述語性**（predicativity）と呼びます。たとえば型上の恒等関数 $\tLam{A}{\Sort{1}}{\tLam{a}{A}{a}}$ の型は $\tPi{A}{\Sort{1}}{A \to A}$ で、これは $\Sort{2}$ に属します。そのため恒等関数を自分自身の型に適用できませんが、$\Sort{2}$ 版の恒等関数なら適用できます。各レベルはその下のレベルを含みます。実際には数レベルあれば足り、それより高いレベルが必要になるのは、すべての小さい圏の圏のような大きな集まりを量化するときくらいです。

**なぜ安全なのでしょうか。** 非述語性は前節で警告した自己言及に似ていますが、範囲が閉じ込められています。$\Sort{0}$ は $\Sort{0}$ を量化する型を含みますが、$\Sort{0}$ 自身はその要素ではありません。Coquand は、最下層に非述語的な宇宙が一つあっても整合的であることを示しました [Coquand 1988]。ところが非述語的なレベルが*二つ*になると、それだけで Girard のパラドックスが導出できます [Hurkens 1995]。本章の規則のもとでは、体系は整合的かつ強正規化的です（[第 14 章](14-properties.md)）。

<aside class="intuition" markdown="1">

なぜ命題は非述語的でよく、型はだめなのでしょうか。命題の証明には、プログラムが取り出せるデータがありません。第 8 章の消去制限も、この性質を守るためのものです。すべての命題を量化して命題を定義するのは、すべての集合に言及する性質で集合を定義するのに似ています。作ったものが量化の対象に含まれ、しかも中身を調べられるなら危険ですが、仮定として使うことしかできなければ同じ問題は起きません。パラドックスを起こすには作ったものを*調べる*操作が必要で、命題の証明ではそれができないのです。

</aside>

## Lean との比較

Lean [de Moura and Ullrich 2021] では $\Sort{0}$ が `Prop`、$\Sort{(u+1)}$ が `Type u` にあたり、$\Pi$ 型の宇宙は本章と同じく $\imax$ で決まります。違いは二つあります。

第一に、Lean の `Prop` には**定義的証明無関係性**（definitional proof irrelevance）があり、同じ命題の証明はどの二つも定義的に等しいとみなされます。本書の変換は証明を同一視しません。これを加えると変換が型に依存するようになり、[第 12 章](12-reduction-conversion.md) の「正規化して比較する」という単純な検査では足りなくなります。

第二に、Lean には**宇宙多相**（universe polymorphism）があり、定義をすべてのレベル $u$ についてまとめて書けます。そのため $\imax$ はレベル*変数*に対しても意味をもち、$\imax(u, v) \le w$ のような制約を記号的に解く必要が出てきます。本書の体系では、レベルはすべて具体的な数です。

設計の選択肢を次の表にまとめます。

| 設計 | 量化できる範囲 | 欠点 |
|---|---|---|
| 宇宙なし | 値のみ | 「すべての命題について」と言えない |
| $\mathsf{Type} : \mathsf{Type}$ | すべて | 不整合 |
| 二つのソート $\ast : \square$ | $\ast$ のみ | $\square$ 自身に型がない |
| $\max$ を使う $\Sort{u} : \Sort{(u+1)}$ | 任意のレベル | 命題を量化する $\forall$ が命題にならない |
| $\imax$ を使う $\Sort{u} : \Sort{(u+1)}$（Lean） | 任意のレベル | 正規化の証明が難しくなる |

<aside class="code" markdown="1">

本章の内容は、`src/typecheck.rs` の `infer` のわずか二行に収まっています。`Sort(u)` に対しては `Sort(u + 1)` を返し、`Pi` に対しては本体のレベルが `0` なら `Sort(0)` を、そうでなければ最大値を返します。[付録 C](c-hurkens.md) では、最初の行を `Sort(u)` を返すように書き換えると、カーネルが Hurkens の項を受け入れてしまうことを確かめます。

</aside>

## 演習

<div class="exercise" markdown="1">

$\tPi{A}{\Sort{1}}{\tPi{P}{A \to \Sort{0}}{\tPi{a}{A}{P\;a}}}$ の宇宙を計算してください。これは「どの型の上のどの述語も、いたるところで成り立つ」という文です（偽ですが、整形式です）。

<details markdown="1">
<summary>解答</summary>

内側から順に計算します。$P\;a : \Sort{0}$ なので $\tPi{a}{A}{P\;a} : \Sort{\imax(1, 0)} = \Sort{0}$ です。次に $A \to \Sort{0}$ の宇宙は $\imax(1, 1) = 1$（本体 $\Sort{0}$ の型は $\Sort{1}$）なので、真ん中の $\Pi$ の宇宙は $\imax(1, 0) = 0$ です。最後に、$\Sort{1} : \Sort{2}$ で本体が $\Sort{0}$ にあるので $\imax(2, 0) = 0$ となり、文全体は命題です。$\imax$ の代わりに $\max$ を使うと、$\Sort{2}$ に入ります。

</details>

</div>

<div class="exercise" markdown="1">

プレイグラウンドの `selfT` の定義が拒否される理由を、関係する規則と二つの宇宙を挙げて説明してください。

<details markdown="1">
<summary>解答</summary>

`idT` は引数として $A : \Sort{1}$ を期待しますが、渡された引数は $\tPi{A}{\Sort{1}}{A \to A}$ で、T-Pi によるその宇宙は $\max(2, 1) = 2$ です。そのため $\Check$ は $\Sort{2}$ と $\Sort{1}$ を比較して失敗し、カーネルはこの適用で型の不一致を報告します。これが述語性で、$\Sort{1}$ を量化する型は $\Sort{1}$ に属しません。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 命題変数は $\lambda$ や $\Pi$ で束縛されるので、$\Sort{0}$ にも型が必要です。
- 自分自身を含む宇宙は体系を不整合にし（Girard、Hurkens）、正規化も壊します。
- 階層 $\Sort{u} : \Sort{(u+1)}$ で自己包含を避け、$\imax$ によって命題だけを非述語的に、それ以外はすべて述語的にします。
- 最下層の非述語的な宇宙は一つなら安全ですが、二つになると安全ではありません。Lean は同じ設計の上に証明無関係性と宇宙多相を加えています。

</div>
