<div class="lead" markdown="1">

$0 + n = n$ を述べるには、等しさを命題として表す必要があります。等式は第 8 章の手順で帰納型として生成できるので、カーネルに専用の型付け規則を加える必要はありません。その再帰子を使うと、$a$ についての事実を $b$ についての事実へ移せます。本章では定義的等価との違いを確かめたうえで、ゼロ加算の定理を証明します。

</div>

## 宣言

Lean では、等式は次のように宣言されています。

```lean
inductive Eq {A : Sort u} (a : A) : A -> Prop where
  | refl : Eq a a
```

$a, b : A$ に対して、型 $\Eq{u}\;A\;a\;b$ は「$a$ と $b$ が等しい」という命題を表します。$A$ が $\Nat$ のときは $a = b$ と書きます。第 8 章の用語でいえば、$A$ と $a$ がパラメータ、$b$ が添字です。

$$
\Eq{u} : \tPi{A}{\Sort{u}}{A \to A \to \Sort{0}}, \qquad
\refl{u} : \tPi{A}{\Sort{u}}{\tPi{a}{A}{\Eq{u}\;A\;a\;a}}.
$$

唯一の構成子 $\refl{u}$ はフィールドを持たず、添字の位置には $a$ が入るので、証明できるのは両辺が*同じ* $a$ である等式だけです。つまり $\Eq{}$ は一つの型ではなく、$\mathsf{Vec}$ と同じく帰納族です。左辺はパラメータとして固定され、右辺は変わりえますが、構成子が右辺を左辺に縛りつけています。

<aside class="intuition" markdown="1">

構成子が一つで足りるのはなぜでしょうか。この宣言は、二つのものがいつ等しいかを*定義*しているわけではありません。述べているのは等式の証明をどう*組み立てる*かであり、その方法は「あるものはそれ自身に等しい」と認めることただ一つです。対称性、推移性、代入といったほかの性質はすべて再帰子から導けます。再帰子は、そうした証明を手にしたときに何ができるかを述べています。

</aside>

## 再帰子: 輸送

くだけた言い方をすると、$\Eq{}$ の再帰子が述べているのは次のことです。*$a = b$ ならば、$a$ について成り立つことは何であれ $b$ についても成り立つ。* これはライプニッツの原理であり、最もよく使われる形で書くと次のようになります。

$$
\EqRec{u,v} : \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{A \to \Sort{v}}{M\;a \to \tPi{b}{A}{\Eq{u}\;A\;a\;b \to M\;b}}}}.
$$

$A$ の要素についての性質 $M$、証拠 $m : M\;a$、そして $a = b$ の証明 $h$ を与えると、$M\;b$ の証拠が返ってきます。これを、$m$ を $h$ に沿って**輸送**（transport）するといいます。計算規則は、$\refl{}$ に沿って輸送しても何も変わらない、というものです。

$$
\EqRec{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A\;c) \;\to\; m.
$$

第 8 章の一般的な手順が実際に生成するのはこれより少し一般的な再帰子で、$\EqRec{}$ はそこから組み立てた定義です。

<details markdown="1">
<summary>手順が生成する完全な依存再帰子</summary>

$b$ は添字なので、motive は $b$ *と*証明 $h : \Eq{u}\;A\;a\;b$ の両方を受け取ります。小前提は $\refl{u}$ に対応する一つだけで、フィールドも仮定もありません。

$$
\begin{array}{l}
\EqRecDep{u,v} : \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{(\tPi{b}{A}{\Eq{u}\;A\;a\;b \to \Sort{v}})}{{}}}} \\[2pt]
\qquad\qquad M\;a\;(\refl{u}\;A\;a) \to \tPi{b}{A}{\tPi{h}{\Eq{u}\;A\;a\;b}{M\;b\;h}} \\[8pt]
\EqRecDep{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A'\;c) \;\iotared\; m.
\end{array}
$$

$\Eq{}$ は部分単集合（構成子が一つでフィールドなし）なので $v$ は任意に選べます。そのため等式の証明は、証明だけでなくデータを組み立てるのにも使えます。非依存の $\EqRec{u,v}$ は、motive が証明を無視する特殊な場合です。

$$
\begin{array}{l}
\EqRec{u,v} \mathrel{:=} \tLam{A}{\Sort{u}}{\tLam{a}{A}{\tLam{M}{A \to \Sort{v}}{\tLam{m}{M\;a}{\tLam{b}{A}{\tLam{h}{\Eq{u}\;A\;a\;b}{{}}}}}}} \\[2pt]
\qquad\qquad \EqRecDep{u,v}\;A\;a\;(\tLam{b'}{A}{\tLam{\_}{\Eq{u}\;A\;a\;b'}{M\;b'}})\;m\;b\;h.
\end{array}
$$

型の付いた簡約基では $b$ も $c$ も $a$ と変換可能なので、規則はそれらを無視して構いません。これらの定数を図 9.1 にまとめます。

<div class="rulebox" markdown="1">

<p class="caption">図 9.1. 等式のための定数とその計算規則。$\EqRec{u,v}$ の規則は、その定義に δ、β と $\EqRecDep{u,v}$ の規則を適用すると得られます。</p>

$$
\begin{array}{lcll}
\Eq{u} &:& \tPi{A}{\Sort{u}}{A \to A \to \Sort{0}} & \text{Lean: } \texttt{Eq} \\[2pt]
\refl{u} &:& \tPi{A}{\Sort{u}}{\tPi{a}{A}{\Eq{u}\;A\;a\;a}} & \texttt{Eq.refl} \\[2pt]
\EqRecDep{u,v} &:& \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{(\tPi{b}{A}{\Eq{u}\;A\;a\;b \to \Sort{v}})}{M\;a\;(\refl{u}\;A\;a) \to \tPi{b}{A}{\tPi{h}{\Eq{u}\;A\;a\;b}{M\;b\;h}}}}} & \texttt{Eq.rec} \\[2pt]
\EqRec{u,v} &:& \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{A \to \Sort{v}}{M\;a \to \tPi{b}{A}{\Eq{u}\;A\;a\;b \to M\;b}}}} & \texttt{Eq.ndrec}\ \text{(definition)}
\end{array}
$$

$$
\begin{array}{rcl}
\EqRecDep{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A\;c) &\iotared& m \\[2pt]
\EqRec{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A\;c) &\to_{\delta\beta\iota}& m
\end{array}
$$

</div>

</details>

たとえば $P : \Nat \to \Sort{0}$、$a, b : \Nat$、$h : a = b$、$\mathit{pa} : P\;a$ とします。motive に $M = P$ を選ぶと、

$$
\EqRec{1,0}\;\Nat\;a\;P\;\mathit{pa}\;b\;h \;:\; P\;b.
$$

この一行が*書き換え*の論理的な中身で、$a$ についての事実が $b$ についての事実に変わります。[第 10 章](10-tactics.md)の `rw` タクティクは、このような項を自動で組み立てます。

<aside class="lean" markdown="1">

Lean では `Eq` の型引数は*暗黙*の引数で、宣言では `{A}` と書き、エラボレータが補います。そのためユーザーは `Eq a b` や `a = b` と書けますが、本書のカーネルが扱う項は完全に明示的なので、引数をすべて書かなければなりません。引数を補うのはカーネルより上の層の仕事です。スクリプト言語には `Eq` と `Eq.refl`、依存再帰子 `Eq.rec0` と `Eq.rec1` が用意されています。非依存の $\EqRec{}$ は宣言されていませんが、下のプレイグラウンドのように二行で定義できます。また、宇宙多相がないため、カーネルは `Eq` を $A : \Sort{1}$ について一度だけ宣言します。これで $\Nat$ やユーザーが宣言するデータ型はすべて扱えますが、証明どうしの等式は表せません。

</aside>

## 定義的等価と命題的等価の違い

これで等しさの概念が二つそろいました。この二つを区別することは、証明支援系の振る舞いを理解するうえで欠かせません。

- **定義的等価** $\conv$ は、カーネルが計算によって判定します。型ではなく項についての判断であり、証明オブジェクトは関わりません。
- **命題的等価** $\Eq{}$ は型です。その証明は項であり、見つけるには帰納法のような本格的な推論が必要になることがあります。

二つをつなぐのが構成子 $\refl{}$ です。T-Conv により、$a \conv b$ ならいつでも $\refl{u}\;A\;a : \Eq{u}\;A\;a\;b$ となるので、定義的等価が成り立てば命題的等価はただで手に入ります。しかし逆は成り立ちません。典型的な例が $n + 0 = n$ と $0 + n = n$ です。第 7 章の $\add$ の定義を使い、そのステップ関数を $s$ とすると、

$$
n + 0 \;\to_{\delta\beta}\; \NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;n\;s\;\zero \;\iotared\; n,
$$

となるので $\refl{1}\;\Nat\;n : n + 0 = n$ であり、Lean ではこれを `rfl` で証明します。一方、

$$
0 + n \;\to_{\delta\beta}\; \NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;0\;s\;n
$$

はそこで**行き詰まります**（stuck）。$n$ は変数で、ι 規則は $\zero$ と $\suc$ に対してしか発火しないからです。そのため $0 + n = n$ は $\refl{}$ では証明できず、帰納法が必要になります。

簡約エクスプローラで、文脈に変数 $n$ を置いて両方の計算を見てみましょう。前者は $n$ にたどり着きますが、後者は、来るはずのない構成子を再帰子が待ったまま止まってしまいます。

<div class="explorer" data-kind="reduce" data-term="add n Nat.zero" data-ctx="n : Nat"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n</pre></div>

<div class="explorer" data-kind="reduce" data-term="add Nat.zero n" data-ctx="n : Nat"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n</pre></div>

<div class="playground" data-file="plus-zero"><pre>def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n

# n + 0 = n は計算で成り立つ: 再帰子は構成子 zero を見る。
goal forall (n : Nat), Eq Nat (add n Nat.zero) n
intro n
rfl
qed

# 0 + n = n はそうならない: 再帰子は変数 n で行き詰まる。
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
rfl</pre></div>

<aside class="warning" markdown="1">

ある等式が `rfl` で成り立つかどうかは、関数が何を計算するかではなく、関数を*どう*定義したかで決まります。加法を第二引数についての再帰で定義すると $n + 0 = n$ は定義的に、$0 + n = n$ は命題的に成り立ちますが、第一引数についての再帰で定義すると両者が入れ替わります。Lean のユーザーはこの現象にしょっちゅう出会います。`rfl` でゴールが閉じるかどうかは、関係する定義がどちら向きに再帰しているか次第です。

</aside>

## 例: 0 + n = n の証明

$\tPi{n}{\Nat}{0 + n = n}$ を帰納法で証明するには、$\NatRec{0}$ を motive $M_0 = \tLam{n}{\Nat}{0 + n = n}$ とともに使います。

**基底。** 必要なのは $M_0\;0$ です。これは $0 + 0 = 0$ と変換可能で、$0 + 0$ は $0$ に計算されるので、項 $\refl{1}\;\Nat\;0$ で足ります。

**ステップ。** $k : \Nat$ と $\mathit{ih} : 0 + k = k$ が与えられたとき、必要なのは $M_0\;(\suc\;k)$、つまり $0 + \suc\;k = \suc\;k$ です。第二の ι 規則により $0 + \suc\;k$ は $\suc\;(0 + k)$ に計算されるので、$\suc\;(0 + k) = \suc\;k$ を示せば十分です。$\suc\;(0+k) = \suc\;(0+k)$ の証明 $\refl{1}\;\Nat\;(\suc\;(0 + k))$ から出発し、motive $N = \tLam{b}{\Nat}{\suc\;(0 + k) = \suc\;b}$ を使って $\mathit{ih}$ に沿って輸送します。この motive によって、*二つ目*の $0 + k$ だけが $k$ に置き換わります。

$$
\mathit{step} = \tLam{k}{\Nat}{\tLam{\mathit{ih}}{0 + k = k}{
  \EqRec{1,0}\;\Nat\;(0 + k)\;N\;(\refl{1}\;\Nat\;(\suc\;(0 + k)))\;k\;\mathit{ih}}}.
$$

証明は次のようになります。

$$
\mathit{zero\_add} = \NatRec{0}\;M_0\;(\refl{1}\;\Nat\;0)\;\mathit{step} \;:\; \tPi{n}{\Nat}{0 + n = n}.
$$

カーネルはこれをアルゴリズム 5.1 で検査します。各引数は、$M_0$ で具体化した $\NatRec{0}$ の型の対応する部分に対して検査され、どの比較も正規化のあとで成功します。カーネルに一度に渡せる形で完全な項を示します。非依存の再帰子は、図 9.1 のとおり先に定義しておきます。

<div class="playground" data-file="zero-add-term"><pre>def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n

# レベル (1, 0) の Eq.ndrec: M a の証明を a = b に沿って M b へ輸送する。
def ndrec : forall (A : Sort 1), forall (a : A), forall (M : A -> Sort 0), M a -> forall (b : A), Eq A a b -> M b := fun (A : Sort 1) => fun (a : A) => fun (M : A -> Sort 0) => fun (m : M a) => fun (b : A) => fun (h : Eq A a b) => Eq.rec0 A a (fun (b' : A) => fun (_h : Eq A a b') => M b') m b h

goal forall (n : Nat), Eq Nat (add Nat.zero n) n
exact Nat.rec0 (fun (n : Nat) => Eq Nat (add Nat.zero n) n) (Eq.refl Nat Nat.zero) (fun (k : Nat) => fun (ih : Eq Nat (add Nat.zero k) k) => ndrec Nat (add Nat.zero k) (fun (b : Nat) => Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ b)) (Eq.refl Nat (Nat.succ (add Nat.zero k))) k ih)
qed</pre></div>

こうした項を手で書くのは手間がかかり、特に正しい motive を見つけるのが大変です。motive $N$ では、$0 + k$ が現れる二箇所のうち、ちょうど片方だけを $b$ にしておく必要がありました。タクティク（[第 10 章](10-tactics.md)）を使えば、項の組み立ても motive の選択も自動化できます。

## カーネルに加えた変更

命題論理から等式付きの算術へ進むのに必要な変更は、わずかなものでした。$\Infer$ には定数の場合が加わり、$\Sigma$ から型を引くようになりました（T-Const）が、$\Check$ は変わっていません。新しく δ ステップと ι ステップを覚えたのは $\Whnf$ だけで、それを通じて $\IsDefEq$ も変わりました。[第 12 章](12-reduction-conversion.md)では一つの $\Whnf$ ですべての帰納型を扱う仕組みを示し、[第 14 章](14-properties.md)では帰納型によってメタ理論がどう変わるかを論じます。

## 演習

<div class="exercise" markdown="1">

等式の対称性を証明してください。$\EqRec{}$ を使って、型 $\tPi{a}{\Nat}{\tPi{b}{\Nat}{a = b \to b = a}}$ をもつ項を組み立ててください。

<details markdown="1">
<summary>解答</summary>

証明 $\refl{}\;a : a = a$ を、motive $\tLam{x}{\Nat}{x = a}$ を使って $h : a = b$ に沿って輸送すると、$a = a$ が $b = a$ に変わります。
$\tLam{a}{\Nat}{\tLam{b}{\Nat}{\tLam{h}{a = b}{\EqRec{1,0}\;\Nat\;a\;(\tLam{x}{\Nat}{x = a})\;(\refl{1}\;\Nat\;a)\;b\;h}}}$。

```leanmini
goal forall (a : Nat), forall (b : Nat), Eq Nat a b -> Eq Nat b a
exact fun (a : Nat) => fun (b : Nat) => fun (h : Eq Nat a b) => ndrec Nat a (fun (x : Nat) => Eq Nat x a) (Eq.refl Nat a) b h
qed
```

（`ndrec` は上のプレイグラウンドと同じように定義しておきます。）

</details>

</div>

<div class="exercise" markdown="1">

$\Eq{}$ は命題なのにすべての宇宙へ消去できますが、構成子を二つもつ型 `Or` はそうではありません。その理由を説明してください。

<details markdown="1">
<summary>解答</summary>

$\Eq{}$ は部分単集合で、構成子は一つ、フィールドはありません。この種の証明は組み立て方が一通りしかないので、その再帰子で定義した関数には $a = b$ の二つの証明を区別する手段がありません。一方 `Or` には構成子が二つあるので、$\Nat$ への再帰子を使えば二つの注入に対して異なる数を返せてしまい、プログラムの値が、どちらの証明を与えたかに左右されることになります。この規則の正確な形は第 8 章にあります。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- $\Eq{}$ は、パラメータ $A$ と $a$、添字 $b$、そしてフィールドを持たない唯一の構成子 $\refl{}$ からなる帰納族です。
- その再帰子は、$a = b$ の証明に沿って $a$ についての事実を $b$ についての事実へ輸送します。$\refl{}$ に対しては何もしません。これが書き換えの正体です。
- 定義的等価は計算で判定されるのに対し、命題的等価は型であり、その証明には帰納法が必要になることがあります。$\refl{}$ を使えば前者から後者が得られます。
- 加法は第二引数について再帰するので、$n + 0 = n$ は定義的に成り立ちますが、$0 + n = n$ はそうではありません。

</div>
