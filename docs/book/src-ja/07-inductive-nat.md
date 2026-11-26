<div class="lead" markdown="1">

宇宙と $\Pi$ 型があれば論理は表せますが、計算したり証明したりする対象となる自然数はまだありません。本章では帰納型を使ってカーネルに自然数を加え、その再帰子から計算と帰納法の両方を引き出します。

</div>

## 定数と定義

まず、名前のついた対象をカーネルに追加できるようにする必要があります。そこで項に**定数**（constant）$c$ を加えます。

$$
t, A, B \;::=\; \cdots \;\mid\; c
$$

**シグネチャ**（signature）$\Sigma$ は定数の一覧です。各項目では、定数を型とともに*宣言*する（$c : C$ と書きます）か、本体も合わせて与えます（$c : C \mathrel{:=} t$ と書きます）。本体をもつ項目を**定義**（definition）と呼びます。たとえば下の $\Nat : \Sort{1}$ は宣言で、本章の後半に出てくる $\add$ は定義です。項目を追加する前には、その型が空の文脈で型になっていることを検査し、本体があれば本体がその型をもつことも検査します。Lean が `def` のたびに行う処理と同じです。

シグネチャの使い道は二つあります。一つ目に、定数はシグネチャに書かれた型をもちます。

$$
\dfrac{\ctxok{\Gamma} \qquad (c : C) \in \Sigma}{\Gamma \vdash c : C}\rulename{T-Const}
$$

ここで $(c : C) \in \Sigma$ には宣言も定義も含まれます。二つ目に、定義は**展開**（unfold）できます。定数をその本体で置き換えるこの計算ステップを **δ 簡約**（delta-reduction）と呼びます。

$$
c \;\deltared\; t \qquad \text{if } (c : C \mathrel{:=} t) \in \Sigma.
$$

たとえば $\add\;2\;1 \deltared (\tLam{m}{\Nat}{\tLam{n}{\Nat}{\cdots}})\;2\;1$ となり、そのあとに β 簡約が続きます。$\Nat$ や $\zero$ のように本体のない宣言済みの定数が δ 簡約されることはありません。β と同じく、このステップはどの部分項に対しても行えます。

定数は変数ではなく、束縛されることもないので、$\FV(c) = \emptyset$ であり、代入しても定数は変わりません。これ以降、簡約は β、δ と、後で導入する ι の三種類からなり、定義的等価（[第 12 章](12-reduction-conversion.md)）もこの三つすべてを考慮して定めます。

<aside class="code" markdown="1">

シグネチャの実体は、`src/kernel.rs` にある `Kernel` のフィールド `decls: HashMap<String, Decl>` です。`Decl` は型と `DeclKind` の組です。`DeclKind` には、その定数が `Axiom`（宣言のみで本体なし）なのか、`Definition(body)` なのか、帰納的宣言から生成される三種類（`Inductive`、`Constructor`、`Recursor`）のどれなのかを記録します。`Kernel::axiom` と `Kernel::define` は、上で述べた検査をしてから項目を追加します。`infer` は型を引いて T-Const を処理し、`whnf` は `Definition` を展開して δ を処理します。

</aside>

## 自然数

Lean では、自然数は次のように宣言されます。

```lean
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

この宣言は、自然数が $\zero$ か、ある自然数 $n$ の後続数 $\suc\;n$ のどちらかとして作られることを表しています。たとえば $2$ は $\suc\;(\suc\;\zero)$ です。私たちのカーネルでは、この宣言によって本体のない定数が三つ追加されます。

$$
\Nat : \Sort{1}, \qquad \zero : \Nat, \qquad \suc : \Nat \to \Nat.
$$

$\zero$ と $\suc$ を**構成子**（constructor）と呼びます。構成子は値を作るだけで計算はしないので、$\suc\;(\suc\;\zero)$ はすでに正規形であり、これがそのまま数 $2$ *です*。以下では $\zero$、$\suc\;\zero$、$\suc\;(\suc\;\zero)$ などを $0, 1, 2, \ldots$ と書きます。

これで数は手に入りましたが、まだ計算には使えません。加法を定義するには $\zero$ と $\suc\;n$ を見分ける必要があるのに、今の項にできるのは引数を受け渡すことだけで、中身を調べられないからです。

## 計算: 加法

加法はどう定義すればよいでしょうか。第二引数についての再帰を使います。

$$
\add\;m\;\zero = m, \qquad \add\;m\;(\suc\;k) = \suc\;(\add\;m\;k).
$$

この定義の形に注目してください。$m$ を固定すると、関数 $\add\;m$ は二つのデータで決まります。$\zero$ での値（ここでは $m$）と、$k$ での値 $r$ から $\suc\;k$ での値を作る方法（ここでは $\suc\;r$）です。この種の再帰を**構造的再帰**（structural recursion）と呼びます。構造的再帰で定義される関数 $f : \Nat \to C$ は、どれも次の形をしています。

$$
f\;\zero = z, \qquad f\;(\suc\;k) = s\;k\;(f\;k),
$$

ここで $z : C$、$s : \Nat \to C \to C$ です。ステップ関数 $s$ は、$k$ と再帰呼び出しの結果 $f\;k$ の両方を受け取ります。そこで、$z$ と $s$ から $f$ を組み立てる定数を一つだけ用意し、最初に追加しておきます。

$$
\mathsf{rec}_C : C \to (\Nat \to C \to C) \to \Nat \to C,
$$

この定数には二つの計算規則を添えます。これを **ι 規則**（iota-rule）と呼び、中身は上の等式そのものです。

$$
\mathsf{rec}_C\;z\;s\;\zero \;\iotared\; z,
\qquad
\mathsf{rec}_C\;z\;s\;(\suc\;n) \;\iotared\; s\;n\;(\mathsf{rec}_C\;z\;s\;n).
$$

これで加法は、再帰を含まない普通の定義として書けます。

$$
\add : \Nat \to \Nat \to \Nat \mathrel{:=} \tLam{m}{\Nat}{\tLam{n}{\Nat}{\mathsf{rec}_{\Nat}\;m\;s\;n}},
\qquad
s = \tLam{k}{\Nat}{\tLam{r}{\Nat}{\suc\;r}}.
$$

$\add\;m\;n$ を $m + n$ と書くことにすると、カーネルは $2 + 1$ を δ、β、ι のステップだけで計算できます。下のエクスプローラでは、$\add$ の定義を読み込んだカーネルが頭部ステップを一つずつ実行していきます。

<div class="explorer" data-kind="reduce" data-term="add (Nat.succ (Nat.succ Nat.zero)) (Nat.succ Nat.zero)"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n</pre></div>

各行が一つの頭部ステップに対応し、強調された部分が簡約基（redex）、次の行がその簡約結果です。数字を変えてみたり、文脈 `n : Nat` のもとで `add Nat.zero n` を試して再帰子が行き詰まる様子を確かめたりしてください。

ほかの関数も同じパターンで定義できます。たとえば $\mathit{double}\;(\suc\;k) = \suc\;(\suc\;(\mathit{double}\;k))$ を満たす二倍関数は、

$$
\mathit{double} \mathrel{:=} \tLam{n}{\Nat}{\mathsf{rec}_{\Nat}\;\zero\;(\tLam{k}{\Nat}{\tLam{r}{\Nat}{\suc\;(\suc\;r)}})\;n},
$$

であり、$\mathit{double}\;2 \to \suc\;(\suc\;(\mathit{double}\;1)) \to \suc^4\;(\mathit{double}\;0) \to \suc^4\;\zero = 4$ となります。

帰納型の定数に $\mathsf{rec}_C$ とその二つの規則を加えるだけで $\Nat$ 上の構造的再帰関数はすべて表せるので、新しい再帰の仕組みは必要ありません。しかも一般の再帰と違い、ι ステップのたびに引数から $\suc$ が一つ外れるので、この再帰は必ず停止します。

<aside class="intuition" markdown="1">

プログラマの目から見ると、$\mathsf{rec}_C$ は自然数上の *fold*（畳み込み）です。リストの `fold` が `nil` を値に、`cons` を関数に置き換えるのと同じことをしています。fold は引数の構成子を一つずつ処理するので、無限ループに陥りません。`while` ループほど自由には書けない代わりに、どのプログラムも必ず停止します。論理にはこの性質が欠かせません。

</aside>

## 証明: 帰納法

次は証明です。$P : \Nat \to \Sort{0}$ について、性質 $P\;n$ がすべての $n$ で成り立つことを示すとき、数学では帰納法を使います。つまり**基底ケース**（base case）$P\;\zero$ と**帰納ステップ**（step）$\tPi{k}{\Nat}{P\;k \to P\;(\suc\;k)}$ を証明します。帰納ステップの引数 $P\;k$ が**帰納法の仮定**（induction hypothesis）です。

Curry-Howard の見方では、$\tPi{n}{\Nat}{P\;n}$ の証明とは、$n$ を受け取って $P\;n$ の証明を返す関数 $f$ のことです。では、$\mathit{base} : P\;\zero$ と $\mathit{step}$ からこの $f$ をどう作ればよいでしょうか。$3$ に対する証明は $\mathit{step}\;2\;(\mathit{step}\;1\;(\mathit{step}\;0\;\mathit{base}))$ であり、一般には

$$
f\;\zero = \mathit{base}, \qquad f\;(\suc\;k) = \mathit{step}\;k\;(f\;k).
$$

となります。これも構造的再帰関数で、上の $\add$ とまったく同じ形をしており、$z = \mathit{base}$、$s = \mathit{step}$ に当たります。**帰納法とは、証明を返す再帰のことです。**

違いは結果の型にあります。$\add$ では $n$ によらず結果の型は同じ $C$ でしたが、証明では $f\;\zero : P\;\zero$、$f\;1 : P\;1$ のように型が $n$ に依存します。$\mathsf{rec}_C$ の型には固定された $C$ が現れるので、このままでは帰納法を表せません。

## 再帰も帰納法も一つの再帰子で

二つの場合を並べてみると、何を一般化すればよいかが見えてきます。

| | 再帰 | 帰納法 |
|---|---|---|
| $n$ に対する結果 | $C$ | $P\;n$ |
| $\zero$ の場合 | $z : C$ | $\mathit{base} : P\;\zero$ |
| $\suc$ の場合 | $s : \tPi{k}{\Nat}{C \to C}$ | $\mathit{step} : \tPi{k}{\Nat}{P\;k \to P\;(\suc\;k)}$ |
| 結果 | $\Nat \to C$ | $\tPi{n}{\Nat}{P\;n}$ |

左の列は、右の列で $P\;n$ が $n$ によらず同じ型 $C$ になる特殊な場合です。そこで $P$ を、$n$ ごとに結果の型を与える任意の関数 $M : \Nat \to \Sort{u}$ に置き換えます。この関数を **motive** と呼び、こうして図 7.1 の**再帰子**（recursor）$\NatRec{u}$ が得られます。再帰子が受け取るのは、motive、構成子ごとに一つの**小前提**（minor premise）、そして最後に再帰の対象となる数 $n$ で、この最後の引数を**大前提**（major premise）と呼びます。ι 規則は $\mathsf{rec}_C$ のものと変わりません。Lean の再帰子 `Nat.rec.{u}` と同じく宇宙レベルごとに一つずつ用意しますが、本書の体系には宇宙多相がないので、レベルは添字で表します。

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

この一つの再帰子が、motive の選び方しだいで両方の役目を果たします。

**再帰。** レベル $1$ の定数 motive $\tLam{\_}{\Nat}{C}$ を与えると、$\NatRec{1}\;(\tLam{\_}{\Nat}{C})$ の型は $\mathsf{rec}_C$ の型と変換可能になります。つまり $\mathsf{rec}_C$ は $\NatRec{1}\;(\tLam{\_}{\Nat}{C})$ そのものなので、以後は

$$
\add \mathrel{:=} \tLam{m}{\Nat}{\tLam{n}{\Nat}{\NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;m\;(\tLam{k}{\Nat}{\tLam{r}{\Nat}{\suc\;r}})\;n}},
$$

と定義します。これが `examples/zero-add.leanmini` にある定義です。

**帰納法。** レベル $0$ の述語 $M : \Nat \to \Sort{0}$ を与えると、$\NatRec{0}$ の型は帰納法の原理

$$
M\;\zero \to (\forall n.\; M\;n \to M\;(\suc\;n)) \to \forall n.\; M\;n.
$$

になります。ここで、T-Pi に $\imax$ を選んだことが効いてきます。結論 $\tPi{n}{\Nat}{M\;n}$ の型は $\Sort{\imax(1, 0)} = \Sort{0}$ なので、$\Nat$ が $\Sort{1}$ に属していても「すべての $n$ について $M\;n$」は命題になります。もし $\max$ を使っていたら、これは $\Sort{1}$ に属してしまい、数についての主張は一つも命題になりません。

$\NatRec{u}$ の型は勝手に決めたものではなく、$\Nat$ の宣言から読み取れます。小前提は構成子ごとに一つあります。各小前提は構成子の引数を受け取り、さらに型が $\Nat$ 自身である引数（**再帰的**（recursive）引数）ごとに帰納法の仮定を一つずつ受け取って、構成子に motive を適用したものを返します。$\zero$ には引数がないので、小前提はただの $M\;\zero$ です。$\suc$ には再帰的引数 $n$ が一つあるので、小前提は $\tPi{n}{\Nat}{M\;n \to M\;(\suc\;n)}$ になります。[第 8 章](08-inductive-recipe.md) では、この手順をより一般的な宣言へと段階的に広げていきます。

## 試してみる

カーネルは、$\Nat$ とその再帰子が宣言済みの状態で起動します（`src/kernel.rs` の `Kernel::standard`）。下のスクリプトでは加法を定義し、$2 + 1$ と $3$ が定義的に等しいことをカーネルに確かめさせます。`rfl` は両辺を計算して、この等しさを確かめます。`three` を `Nat.succ three` に書き換えて、カーネルが拒否するところを見てください。

<div class="playground" data-file="add-two-one"><pre>def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def one : Nat := Nat.succ Nat.zero
def two : Nat := Nat.succ one
def three : Nat := Nat.succ two
# 両辺とも succ (succ (succ zero)) に計算されるので、refl でこれを証明できる。
goal Eq Nat (add two one) three
rfl
qed</pre></div>

ゴールにある `Eq` は等式型で、[第 9 章](09-equality.md) で宣言します。今のところは、`Eq Nat a b` を「$a = b$」、`rfl` を「両辺は同じものに計算される」と読んでおけば十分です。

<aside class="lean" markdown="1">

Lean は、ここで説明したとおりに `inductive` 宣言から `Nat.rec` を生成します。その型は、束縛変数の名前と暗黙の引数を除けば図 7.1 と一致します。実行時には、Lean のコンパイラが再帰子を効率のよい機械の算術に置き換えます。利用者はパターンマッチで再帰関数を書けますが、エラボレータが裏でそれを再帰子にコンパイルするので、カーネルが目にするのは再帰子だけです。

</aside>

## 演習

<div class="exercise" markdown="1">

上の $\add$ と同じやり方で、$\add$ を使って乗法 $\mathit{mul}\;m\;n$ を $n$ についての再帰で定義してください。

<details markdown="1">
<summary>解答</summary>

$\mathit{mul}\;m\;\zero = \zero$、$\mathit{mul}\;m\;(\suc\;k) = \add\;m\;(\mathit{mul}\;m\;k)$ なので、
$\mathit{mul} \mathrel{:=} \tLam{m}{\Nat}{\tLam{n}{\Nat}{\NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;\zero\;(\tLam{k}{\Nat}{\tLam{r}{\Nat}{\add\;m\;r}})\;n}}$ となります。

```leanmini
def mul : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) Nat.zero (fun (k : Nat) => fun (r : Nat) => add m r) n
```

</details>

</div>

<div class="exercise" markdown="1">

規則 $\mathsf{fix}\;g \to g\;(\mathsf{fix}\;g)$ をもつ一般の不動点コンビネータ $\mathsf{fix} : (C \to C) \to C$ があれば、どんな再帰関数でも定義できます。カーネルがこれを受け入れられないのはなぜでしょうか。

<details markdown="1">
<summary>解答</summary>

$C = \tPi{P}{\Sort{0}}{P}$、$g = \tLam{x}{C}{x}$ とすると、項 $\mathsf{fix}\;g$ は型 $\tPi{P}{\Sort{0}}{P}$ をもちます。これはあらゆる命題の証明になってしまうので、体系は整合性を失います。さらにこの項は自分自身へいつまでも簡約され続けるので、$\IsDefEq$ が停止しません。構造的再帰では ι ステップのたびに構成子が一つ消費されるので、どちらの問題も起きません。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 定数はシグネチャ $\Sigma$ に登録されます。定義は δ 簡約で展開されますが、宣言は展開されません。
- 帰納型を宣言すると、型構成子と構成子が追加されます。構成子は値を作るだけで、計算はしません。
- $\Nat$ 上の構造的再帰は再帰子という一つの定数にまとまり、ι 規則は構成子ごとに一つあります。
- 帰納法は、依存的な motive $M : \Nat \to \Sort{0}$ を与えた同じ再帰子です。再帰と帰納法は同じ一つの操作です。
- $\imax$ の規則があるおかげで、「すべての $n$ について $M\;n$」は命題になります。

</div>
