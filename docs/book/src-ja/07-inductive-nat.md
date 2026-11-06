<div class="lead" markdown="1">

ここまでに扱った型は宇宙と $\Pi$ 型だけであり、命題論理には足りても、数学に必要な数や等しさを表す手段はまだない。Lean はその両方を帰納型で提供する。本章ではカーネルに定数を加えて自然数を宣言し、同じ仕組みで数の計算と証明を扱えることを示す。

</div>

## 定数と定義

まず、名前のついた対象をカーネルに追加する手段が要るので、項に**定数**（constant）$c$ を加える。

$$
t, A, B \;::=\; \cdots \;\mid\; c
$$

**シグネチャ**（signature）$\Sigma$ は定数を列挙する。各項目は、定数をその型とともに*宣言*する（$c : C$ と書く）か、さらに本体も与える（$c : C \mathrel{:=} t$ と書く）かのどちらかである。本体をもつ項目を**定義**（definition）と呼ぶ。たとえば、下の $\Nat : \Sort{1}$ は宣言で、本章の後半に出てくる $\add$ は定義である。項目を追加する前に、その型が空の文脈で型であることを検査し、本体があればそれをその型に対して検査する。Lean が各 `def` に対して行うのと同じである。

シグネチャは二通りに使われる。第一に、定数はシグネチャが与える型をもつ。

$$
\dfrac{\ctxok{\Gamma} \qquad (c : C) \in \Sigma}{\Gamma \vdash c : C}\rulename{T-Const}
$$

ここで $(c : C) \in \Sigma$ は宣言と定義の両方を含む。第二に、定義は**展開**（unfold）でき、定数をその本体で置き換えるこの計算ステップを **δ 簡約**（delta-reduction）と呼ぶ。

$$
c \;\deltared\; t \qquad \text{if } (c : C \mathrel{:=} t) \in \Sigma.
$$

たとえば $\add\;2\;1 \deltared (\tLam{m}{\Nat}{\tLam{n}{\Nat}{\cdots}})\;2\;1$ であり、その後は β 簡約が続く。$\Nat$ や $\zero$ のような本体のない宣言された定数は、決して δ 簡約されない。β と同様に、このステップはどの部分項にも適用できる。

定数は変数ではなく、決して束縛されないので、$\FV(c) = \emptyset$ であり、代入は定数を変えない。簡約はここから β、δ、そして以下で導入する ι 規則からなり、定義的等価（[第 12 章](12-reduction-conversion.md)）はこの三つすべてに関して定められる。

<aside class="code" markdown="1">

シグネチャは `src/kernel.rs` の `Kernel` のフィールド `decls: HashMap<String, Decl>` である。`Decl` は型と `DeclKind` の組で、`DeclKind` はその定数が `Axiom`（宣言のみ、本体なし）か、`Definition(body)` か、帰納的宣言から生成される三種類（`Inductive`、`Constructor`、`Recursor`）のいずれかを記録する。`Kernel::axiom` と `Kernel::define` は、上で述べた検査の後に項目を追加する。`infer` は型を引くことで T-Const を扱い、`whnf` は `Definition` を展開することで δ を扱う。

</aside>

## 自然数

Lean では、自然数は次のように宣言される。

```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

この宣言によれば、自然数は $\zero$ か、ある自然数 $n$ の後続数 $\suc\;n$ として作られる。たとえば $2$ は $\suc\;(\suc\;\zero)$ である。私たちのカーネルでは、この宣言によって本体のない三つの定数が追加される。

$$
\Nat : \Sort{1}, \qquad \zero : \Nat, \qquad \suc : \Nat \to \Nat.
$$

$\zero$ と $\suc$ を**構成子**（constructor）と呼ぶ。構成子は値を作るが決して計算しないので、$\suc\;(\suc\;\zero)$ はすでに正規形であり、それ自体が数 $2$ *である*。以下では $\zero$、$\suc\;\zero$、$\suc\;(\suc\;\zero)$ などを $0, 1, 2, \ldots$ と書く。

これで数は手に入ったが、まだ計算には使えない。加法には $\zero$ と $\suc\;n$ を区別する手段が必要なのに、今の項は引数を受け渡すだけで、その中身を調べられないからである。

## 計算: 加法

加法はどう定義すべきか。第二引数に関する再帰で定義する。

$$
\add\;m\;\zero = m, \qquad \add\;m\;(\suc\;k) = \suc\;(\add\;m\;k).
$$

この定義の形に注目してほしい。$m$ を固定すると、関数 $\add\;m$ は二つのデータ、すなわち $\zero$ での値（これは $m$）と、$k$ での値 $r$ を $\suc\;k$ での値に変える方法（これは $\suc\;r$）で決まる。この種の再帰を**構造的再帰**（structural recursion）と呼び、構造的再帰で定義される関数 $f : \Nat \to C$ はどれも同じ形をしている。

$$
f\;\zero = z, \qquad f\;(\suc\;k) = s\;k\;(f\;k),
$$

ここで $z : C$、$s : \Nat \to C \to C$ である。ステップ関数 $s$ は、$k$ と再帰呼び出しの結果 $f\;k$ の両方を受け取る。そこで、$z$ と $s$ から $f$ を組み立てる定数を一つ、一度だけ追加する。

$$
\mathsf{rec}_C : C \to (\Nat \to C \to C) \to \Nat \to C,
$$

これに二つの計算規則を添える。**ι 規則**（iota-rule）と呼ばれるもので、上の等式そのものである。

$$
\mathsf{rec}_C\;z\;s\;\zero \;\iotared\; z,
\qquad
\mathsf{rec}_C\;z\;s\;(\suc\;n) \;\iotared\; s\;n\;(\mathsf{rec}_C\;z\;s\;n).
$$

加法はこれで、再帰を含まないふつうの定義になる。

$$
\add : \Nat \to \Nat \to \Nat \mathrel{:=} \tLam{m}{\Nat}{\tLam{n}{\Nat}{\mathsf{rec}_{\Nat}\;m\;s\;n}},
\qquad
s = \tLam{k}{\Nat}{\tLam{r}{\Nat}{\suc\;r}}.
$$

$\add\;m\;n$ を $m + n$ と書くと、カーネルは $2 + 1$ を δ、β、ι のステップだけで計算する。下のエクスプローラは、$\add$ の定義を読み込んだカーネルが、頭部ステップを一度に一つずつ実行しているところである。

<div class="explorer" data-kind="reduce" data-term="add (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n</pre></div>

各行が一つの頭部ステップであり、強調された部分が簡約基（redex）で、次の行にその結果が示される。数字を変えてみるか、文脈 `n : Nat` で `add Nat.zero n` を試して、再帰子が行き詰まるところを見てほしい。

ほかの関数も同じパターンに従う。$\mathit{double}\;(\suc\;k) = \suc\;(\suc\;(\mathit{double}\;k))$ となる二倍は、

$$
\mathit{double} \mathrel{:=} \tLam{n}{\Nat}{\mathsf{rec}_{\Nat}\;\zero\;(\tLam{k}{\Nat}{\tLam{r}{\Nat}{\suc\;(\suc\;r)}})\;n},
$$

であり、$\mathit{double}\;2 \to \suc\;(\suc\;(\mathit{double}\;1)) \to \suc^4\;(\mathit{double}\;0) \to \suc^4\;\zero = 4$ となる。

帰納型の定数と、$\mathsf{rec}_C$ およびその二つの規則だけで $\Nat$ 上の構造的再帰関数はすべて表せるので、新しい再帰の仕組みは要らない。しかも一般の再帰と違って、各 ι ステップが引数から $\suc$ を一つ取り除くので、この再帰は必ず停止する。

<aside class="intuition" markdown="1">

プログラマにとって、$\mathsf{rec}_C$ は自然数上の *fold*（畳み込み）であり、リストの `fold` が `nil` を値で、`cons` を関数で置き換えるのと同じである。fold は引数の構成子を一つずつ処理するため、無限ループしない。`while` ループほど自由には書けないが、どのプログラムも停止する。論理にはこの性質が必要である。

</aside>

## 証明: 帰納法

次に証明を考える。$P : \Nat \to \Sort{0}$ について、性質 $P\;n$ がすべての $n$ で成り立つことを示すには、数学では帰納法を使い、**基底ケース**（base case）$P\;\zero$ と、**帰納ステップ**（step）$\tPi{k}{\Nat}{P\;k \to P\;(\suc\;k)}$ を証明する。帰納ステップの引数 $P\;k$ が**帰納法の仮定**（induction hypothesis）である。

Curry-Howard を通して見ると、$\tPi{n}{\Nat}{P\;n}$ の証明とは、$n$ を受け取って $P\;n$ の証明を返す関数 $f$ である。$\mathit{base} : P\;\zero$ と $\mathit{step}$ から、そのような $f$ をどう作るか。$3$ に対する証明は $\mathit{step}\;2\;(\mathit{step}\;1\;(\mathit{step}\;0\;\mathit{base}))$ であり、一般には

$$
f\;\zero = \mathit{base}, \qquad f\;(\suc\;k) = \mathit{step}\;k\;(f\;k).
$$

となる。これもまた構造的再帰関数であり、上の $\add$ とまったく同じ形をしており、$z = \mathit{base}$、$s = \mathit{step}$ である。**帰納法とは、証明を返す再帰である。**

違いは結果の型にあり、$\add$ ではどの $n$ に対しても同じ型 $C$ だったが、証明では $f\;\zero : P\;\zero$、$f\;1 : P\;1$ のように $n$ に依存する。$\mathsf{rec}_C$ の型には固定された $C$ が現れるため、このままでは帰納法を表せない。

## 両方をこなす一つの再帰子

二つの場合を並べてみると、何を一般化すべきかが見えてくる。

| | 再帰 | 帰納法 |
|---|---|---|
| $n$ に対する結果 | $C$ | $P\;n$ |
| $\zero$ の場合 | $z : C$ | $\mathit{base} : P\;\zero$ |
| $\suc$ の場合 | $s : \tPi{k}{\Nat}{C \to C}$ | $\mathit{step} : \tPi{k}{\Nat}{P\;k \to P\;(\suc\;k)}$ |
| 結果 | $\Nat \to C$ | $\tPi{n}{\Nat}{P\;n}$ |

左の列は、右の列で $P\;n$ がどの $n$ に対しても同じ型 $C$ になる特殊な場合である。そこで $P$ を、各 $n$ に対する結果の型を与える任意の関数 $M : \Nat \to \Sort{u}$ に置き換える。この関数を **motive** と呼び、そこから図 7.1 の**再帰子**（recursor）$\NatRec{u}$ が得られる。再帰子は、motive、構成子ごとに一つの**小前提**（minor premise）、最後に再帰の対象となる数 $n$ を受け取り、この最後の引数が**大前提**（major premise）である。ι 規則は $\mathsf{rec}_C$ のものと同じである。Lean の再帰子 `Nat.rec.{u}` と同様、宇宙レベルごとに一つずつ用意するが、本書の体系には宇宙多相がないため、レベルは添字で表す。

<div class="rulebox" markdown="1">

<p class="caption">図 7.1. 自然数の定数と、再帰子の ι 規則。</p>

$$
\begin{array}{lcll}
\Nat &:& \Sort{1} & \text{Lean: } \texttt{Nat} \\[2pt]
\zero &:& \Nat & \texttt{Nat.zero} \\[2pt]
\suc &:& \Nat \to \Nat & \texttt{Nat.succ} \\[2pt]
\NatRec{u} &:& \tPi{M}{\Nat \to \Sort{u}}{\;M\;\zero \to (\tPi{n}{\Nat}{M\;n \to M\;(\suc\;n)}) \to \tPi{n}{\Nat}{M\;n}} & \texttt{Nat.rec}
\end{array}
$$

$$
\begin{array}{rcl}
\NatRec{u}\;M\;z\;s\;\zero &\iotared& z \\[2pt]
\NatRec{u}\;M\;z\;s\;(\suc\;n) &\iotared& s\;n\;(\NatRec{u}\;M\;z\;s\;n)
\end{array}
$$

</div>

この一つの再帰子が、motive に応じて両方の仕事をこなす。

**再帰。** レベル $1$ の定数 motive $\tLam{\_}{\Nat}{C}$ を与えると、$\NatRec{1}\;(\tLam{\_}{\Nat}{C})$ の型は $\mathsf{rec}_C$ の型と変換可能である。つまり $\mathsf{rec}_C$ は $\NatRec{1}\;(\tLam{\_}{\Nat}{C})$ にほかならず、以後は

$$
\add \mathrel{:=} \tLam{m}{\Nat}{\tLam{n}{\Nat}{\NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;m\;(\tLam{k}{\Nat}{\tLam{r}{\Nat}{\suc\;r}})\;n}},
$$

とする。これが `examples/zero-add.leanmini` にある定義である。

**帰納法。** レベル $0$ の述語 $M : \Nat \to \Sort{0}$ を与えると、$\NatRec{0}$ の型は帰納法の原理

$$
M\;\zero \to (\forall n.\; M\;n \to M\;(\suc\;n)) \to \forall n.\; M\;n.
$$

になる。ここで T-Pi に $\imax$ を選んだことが効いてくる。結論 $\tPi{n}{\Nat}{M\;n}$ の型は $\Sort{\imax(1, 0)} = \Sort{0}$ なので、$\Nat$ が $\Sort{1}$ に属していても、「すべての $n$ について $M\;n$」は命題である。代わりに $\max$ を使えばこれは $\Sort{1}$ に属し、数についての主張はまったく命題にならない。

$\NatRec{u}$ の型は恣意的なものではなく、$\Nat$ の宣言から読み取れる。小前提は構成子ごとに一つあり、各小前提は、構成子の引数を受け取り、さらに型が $\Nat$ 自身である引数（**再帰的**（recursive）引数）ごとに帰納法の仮定を一つ受け取って、構成子に motive を適用したものを返す。$\zero$ には引数がないので、その場合はただの $M\;\zero$ であり、$\suc$ には再帰的引数 $n$ が一つあるので、その場合は $\tPi{n}{\Nat}{M\;n \to M\;(\suc\;n)}$ になる。[第 8 章](08-inductive-recipe.md) では、この手順をより一般的な宣言へと順に適用していく。

## 試してみる

カーネルは、$\Nat$ とその再帰子をあらかじめ宣言した状態で始まる（`src/kernel.rs` の `Kernel::standard`）。下のスクリプトは加法を定義し、$2 + 1$ と $3$ が定義的に等しいことをカーネルに確かめさせ、`rfl` は両辺を計算してこれを行う。`three` を `Nat.succ three` に変えて、カーネルが拒否するのを見てほしい。

<div class="playground" data-file="add-two-one"><pre>def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def one : Nat := Nat.succ Nat.zero
def two : Nat := Nat.succ one
def three : Nat := Nat.succ two
# 両辺とも succ (succ (succ zero)) に計算されるので、refl でこれを証明できる。
goal Eq Nat (add two one) three
rfl
qed</pre></div>

ゴールの `Eq` は等式型であり、[第 9 章](09-equality.md) で宣言する。今のところは、`Eq Nat a b` を「$a = b$」、`rfl` を「両辺は同じものに計算される」と読んでおけばよい。

<aside class="lean" markdown="1">

Lean は、ここで述べたとおりに `inductive` 宣言から `Nat.rec` を生成し、その型は、束縛変数の名前と暗黙の引数を除けば図 7.1 と一致する。Lean のコンパイラは、実行時には再帰子を効率的な機械の算術で置き換える。エラボレータは、利用者がパターンマッチで再帰関数を書くことを許し、裏でそれを再帰子にコンパイルするが、カーネルが目にするのは再帰子だけである。

</aside>

## 演習

<div class="exercise" markdown="1">

上の $\add$ の流儀で、$\add$ を使って、乗法 $\mathit{mul}\;m\;n$ を $n$ に関する再帰で定義せよ。

<details markdown="1">
<summary>解答</summary>

$\mathit{mul}\;m\;\zero = \zero$ かつ $\mathit{mul}\;m\;(\suc\;k) = \add\;m\;(\mathit{mul}\;m\;k)$ なので、
$\mathit{mul} \mathrel{:=} \tLam{m}{\Nat}{\tLam{n}{\Nat}{\NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;\zero\;(\tLam{k}{\Nat}{\tLam{r}{\Nat}{\add\;m\;r}})\;n}}$ となる。

```leanmini
def mul : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) Nat.zero (fun (k : Nat) => fun (r : Nat) => add m r) n
```

</details>

</div>

<div class="exercise" markdown="1">

規則 $\mathsf{fix}\;g \to g\;(\mathsf{fix}\;g)$ をもつ一般の不動点コンビネータ $\mathsf{fix} : (C \to C) \to C$ があれば、どんな再帰関数も定義できる。カーネルがこれを受け入れられないのはなぜか。

<details markdown="1">
<summary>解答</summary>

$C = \tPi{P}{\Sort{0}}{P}$、$g = \tLam{x}{C}{x}$ とすると、項 $\mathsf{fix}\;g$ は型 $\tPi{P}{\Sort{0}}{P}$ をもつことになり、これはあらゆる命題の証明であって、体系は整合性を失う。さらにこの項は自分自身へ際限なく簡約されるので、$\IsDefEq$ が停止しない。構造的再帰は、各 ι ステップが構成子を一つ消費するので、どちらの問題も起こさない。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 定数はシグネチャ $\Sigma$ に由来し、定義は δ 簡約で展開され、宣言は決して展開されない。
- 帰納型は型構成子と構成子を追加し、構成子は値を作るが計算はしない。
- $\Nat$ 上の構造的再帰は、再帰子という一つの定数に集約され、ι 規則は構成子ごとに一つである。
- 帰納法は、依存的な motive $M : \Nat \to \Sort{0}$ を与えた同じ再帰子である。再帰と帰納法は一つの操作である。
- $\imax$ の規則があるからこそ、「すべての $n$ について $M\;n$」は命題になる。

</div>
