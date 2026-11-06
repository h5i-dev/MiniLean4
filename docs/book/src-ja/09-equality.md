<div class="lead" markdown="1">

$0 + n = n$ のような数に関する事実を述べるには、等しさを表す手段が要る。専用の規則がカーネルに組み込まれているように思えるかもしれないが、等式も第 8 章の手順で生成される帰納型の一つである。その再帰子を使えば、$a$ についての事実を $b$ についての事実へ移せる。本章ではこの型を宣言し、定義的等価との違いを説明してから、本書で最初の本格的な定理を証明する。

</div>

## 宣言

Lean では、等式は次のように宣言されている。

```lean
inductive Eq {A : Sort u} (a : A) : A -> Prop where
  | refl : Eq a a
```

$a, b : A$ に対して、型 $\Eq{u}\;A\;a\;b$ は $a$ と $b$ が等しいという命題である。$A$ が $\Nat$ のときは $a = b$ と書く。第 8 章の言葉でいえば、$A$ と $a$ がパラメータで $b$ が添字である。

$$
\Eq{u} : \tPi{A}{\Sort{u}}{A \to A \to \Sort{0}}, \qquad
\refl{u} : \tPi{A}{\Sort{u}}{\tPi{a}{A}{\Eq{u}\;A\;a\;a}}.
$$

唯一の構成子 $\refl{u}$ はフィールドを持たず、その添字項は $a$ である。つまり、両辺が*同じ* $a$ である等式しか証明できない。したがって $\Eq{}$ は単一の型ではなく、$\mathsf{Vec}$ と同じ帰納族である。左辺はパラメータで固定され、右辺は変化するが、構成子がそれを左辺に釘付けにする。

<aside class="intuition" markdown="1">

なぜ構成子が一つで足りるのか。この宣言は、二つのものがいつ等しいかを*定義*しているのではない。等式の証明がどう*組み立てられる*かを述べているのであり、その唯一の方法が「あるものはそれ自身に等しい」と認めることである。対称性、推移性、代入といった残りはすべて再帰子から導かれる。再帰子は、そうした証明を手にしたとき何ができるかを述べる。

</aside>

## 再帰子: 輸送

くだけて言えば、$\Eq{}$ の再帰子はこう述べている。*$a = b$ ならば、$a$ について成り立つことは何であれ $b$ についても成り立つ。* これはライプニッツの原理であり、最もよく使われる形では次のように読める。

$$
\EqRec{u,v} : \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{A \to \Sort{v}}{M\;a \to \tPi{b}{A}{\Eq{u}\;A\;a\;b \to M\;b}}}}.
$$

$A$ の要素についての性質 $M$、証拠 $m : M\;a$、そして $a = b$ の証明 $h$ が与えられると、$M\;b$ の証拠を返す。$m$ を $h$ に沿って**輸送**（transport）する、という。その計算規則は、$\refl{}$ に沿った輸送は何もしない、というものである。

$$
\EqRec{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A\;c) \;\to\; m.
$$

第 8 章の一般的な手順が生成するものはこれより少し一般的で、$\EqRec{}$ はそれから組み立てた定義である。

<details markdown="1">
<summary>手順が生成する完全な依存再帰子</summary>

$b$ は添字なので、motive は $b$ *と*証明 $h : \Eq{u}\;A\;a\;b$ を受け取る。小前提は $\refl{u}$ のための一つだけで、フィールドも仮定もない。

$$
\begin{array}{l}
\EqRecDep{u,v} : \tPi{A}{\Sort{u}}{\tPi{a}{A}{\tPi{M}{(\tPi{b}{A}{\Eq{u}\;A\;a\;b \to \Sort{v}})}{{}}}} \\[2pt]
\qquad\qquad M\;a\;(\refl{u}\;A\;a) \to \tPi{b}{A}{\tPi{h}{\Eq{u}\;A\;a\;b}{M\;b\;h}} \\[8pt]
\EqRecDep{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A'\;c) \;\iotared\; m.
\end{array}
$$

$\Eq{}$ は部分単集合（構成子が一つでフィールドなし）なので、$v$ は任意でよい。等式の証明は、証明だけでなくデータを組み立てるのにも使える。非依存の $\EqRec{u,v}$ は、motive が証明を無視する特殊な場合である。

$$
\begin{array}{l}
\EqRec{u,v} \mathrel{:=} \tLam{A}{\Sort{u}}{\tLam{a}{A}{\tLam{M}{A \to \Sort{v}}{\tLam{m}{M\;a}{\tLam{b}{A}{\tLam{h}{\Eq{u}\;A\;a\;b}{{}}}}}}} \\[2pt]
\qquad\qquad \EqRecDep{u,v}\;A\;a\;(\tLam{b'}{A}{\tLam{\_}{\Eq{u}\;A\;a\;b'}{M\;b'}})\;m\;b\;h.
\end{array}
$$

型の付いた簡約基では $b$ も $c$ も $a$ と変換可能なので、規則はそれらを無視してよい。図 9.1 にこれらの定数をまとめる。

<div class="rulebox" markdown="1">

<p class="caption">図 9.1. 等式のための定数とその計算規則。$\EqRec{u,v}$ の規則は、その定義から δ、β、および $\EqRecDep{u,v}$ の規則によって従う。</p>

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

たとえば $P : \Nat \to \Sort{0}$、$a, b : \Nat$、$h : a = b$、$\mathit{pa} : P\;a$ とする。motive $M = P$ を選ぶと

$$
\EqRec{1,0}\;\Nat\;a\;P\;\mathit{pa}\;b\;h \;:\; P\;b.
$$

この一行が*書き換え*の論理的な中身である。$a$ についての事実が $b$ についての事実になる。[第 10 章](10-tactics.md)の `rw` タクティクは、このような項を自動で組み立てる。

<aside class="lean" markdown="1">

Lean では `Eq` の型引数は*暗黙*で、宣言では `{A}` と書き、エラボレータが補う。そのためユーザーは `Eq a b` や `a = b` と書けるが、本書のカーネルが扱う項は完全に明示的であり、引数をすべて書く必要がある。引数の補完はカーネルより上の層の仕事である。スクリプト言語には `Eq` と `Eq.refl`、依存再帰子 `Eq.rec0` と `Eq.rec1` がある。非依存の $\EqRec{}$ はあらかじめ宣言されていないが、下のプレイグラウンドに示すように二行で定義できる。また、宇宙多相がないため、カーネルは `Eq` を $A : \Sort{1}$ で一度だけ宣言する。これで $\Nat$ とユーザーが宣言するすべてのデータ型を扱えるが、証明どうしの等式は使えない。

</aside>

## 定義的等価と命題的等価

いまや等しさの概念が二つある。この二つを区別することが、証明支援系の振る舞いを理解するうえで欠かせない。

- **定義的等価** $\conv$ は、カーネルが計算によって決定する。項についての判断であって型ではなく、証明オブジェクトは関与しない。
- **命題的等価** $\Eq{}$ は型である。その証明は項であり、見つけるには帰納法のような本物の推論が要ることがある。

構成子 $\refl{}$ が両者をつなぐ。T-Conv により、$a \conv b$ であれば常に $\refl{u}\;A\;a : \Eq{u}\;A\;a\;b$ となる。したがって、定義的等価からは命題的等価がただで得られる。逆は成り立たない。標準的な例が $n + 0 = n$ と $0 + n = n$ の二つである。第 7 章の $\add$ の定義を使い、その段階関数を $s$ とすると、

$$
n + 0 \;\to_{\delta\beta}\; \NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;n\;s\;\zero \;\iotared\; n,
$$

なので $\refl{1}\;\Nat\;n : n + 0 = n$ であり、Lean はこれを `rfl` で証明する。対照的に、

$$
0 + n \;\to_{\delta\beta}\; \NatRec{1}\;(\tLam{\_}{\Nat}{\Nat})\;0\;s\;n
$$

は**行き詰まる**（stuck）。$n$ は変数であり、ι 規則は $\zero$ と $\suc$ に対してしか発火しない。したがって $0 + n = n$ は $\refl{}$ では証明できず、帰納法が要る。

簡約エクスプローラは、文脈に変数 $n$ を置いて両方の計算を示す。前者は $n$ に到達する。後者は、来るはずのない構成子を再帰子が待ったまま止まる。

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

どの等式が `rfl` で成り立つかは、関数が何を計算するかではなく、*どう*定義されたかで決まる。第二引数に関する再帰で加法を定義すると $n + 0 = n$ が定義的で $0 + n = n$ が命題的になる。第一引数に関する再帰なら両者は入れ替わる。Lean のユーザーはこれに絶えず出会う。`rfl` でゴールが閉じるかどうかは、関係する定義の再帰の向き次第である。

</aside>

## 例: 0 + n = n の証明

$\tPi{n}{\Nat}{0 + n = n}$ を帰納法で証明する。$\NatRec{0}$ を motive $M_0 = \tLam{n}{\Nat}{0 + n = n}$ で使う。

**基底。** 必要なのは $M_0\;0$ で、これは $0 + 0 = 0$ と変換可能である。$0 + 0$ は $0$ に計算されるので、項 $\refl{1}\;\Nat\;0$ で済む。

**ステップ。** $k : \Nat$ と $\mathit{ih} : 0 + k = k$ が与えられたとき、必要なのは $M_0\;(\suc\;k)$、すなわち $0 + \suc\;k = \suc\;k$ である。第二の ι 規則により $0 + \suc\;k$ は $\suc\;(0 + k)$ に計算されるので、$\suc\;(0 + k) = \suc\;k$ を証明すれば足りる。$\suc\;(0+k) = \suc\;(0+k)$ の証明 $\refl{1}\;\Nat\;(\suc\;(0 + k))$ から出発し、motive $N = \tLam{b}{\Nat}{\suc\;(0 + k) = \suc\;b}$ で $\mathit{ih}$ に沿って輸送する。この motive は*二つ目*の $0 + k$ を $k$ に置き換える。

$$
\mathit{step} = \tLam{k}{\Nat}{\tLam{\mathit{ih}}{0 + k = k}{
  \EqRec{1,0}\;\Nat\;(0 + k)\;N\;(\refl{1}\;\Nat\;(\suc\;(0 + k)))\;k\;\mathit{ih}}}.
$$

証明は次のとおりである。

$$
\mathit{zero\_add} = \NatRec{0}\;M_0\;(\refl{1}\;\Nat\;0)\;\mathit{step} \;:\; \tPi{n}{\Nat}{0 + n = n}.
$$

カーネルはこれをアルゴリズム 5.1 で検査する。各引数は、$M_0$ でインスタンス化した $\NatRec{0}$ の型の対応する部分に対して検査され、どの比較も正規化のあとで成功する。完全な項を、カーネルに一度に提出する形で示す。非依存再帰子は図 9.1 のとおり先に定義しておく。

<div class="playground" data-file="zero-add-term"><pre>def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n

# レベル (1, 0) の Eq.ndrec: M a の証明を a = b に沿って M b へ輸送する。
def ndrec : forall (A : Sort 1), forall (a : A), forall (M : A -> Sort 0), M a -> forall (b : A), Eq A a b -> M b := fun (A : Sort 1) => fun (a : A) => fun (M : A -> Sort 0) => fun (m : M a) => fun (b : A) => fun (h : Eq A a b) => Eq.rec0 A a (fun (b' : A) => fun (_h : Eq A a b') => M b') m b h

goal forall (n : Nat), Eq Nat (add Nat.zero n) n
exact Nat.rec0 (fun (n : Nat) => Eq Nat (add Nat.zero n) n) (Eq.refl Nat Nat.zero) (fun (k : Nat) => fun (ih : Eq Nat (add Nat.zero k) k) => ndrec Nat (add Nat.zero k) (fun (b : Nat) => Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ b)) (Eq.refl Nat (Nat.succ (add Nat.zero k))) k ih)
qed</pre></div>

こうした項を手で書くのは手間がかかり、とくに正しい motive を見つけるのが難しい。motive $N$ は、$0 + k$ が現れる二箇所のうち、ちょうど一方だけで $b$ に言及しなければならなかった。タクティク（[第 10 章](10-tactics.md)）は、項の組み立てと motive の選択を自動化する。

## カーネルへの変更

命題論理から等式付きの算術に進むのに、変更はわずかで済んだ。$\Infer$ には定数のケースが加わり、$\Sigma$ から型を引く（T-Const）。$\Check$ は変わらない。新しい δ ステップと ι ステップを覚えたのは $\Whnf$ だけで、それを通して $\IsDefEq$ も変わった。[第 12 章](12-reduction-conversion.md)では一つの $\Whnf$ がすべての帰納型を扱う仕組みを示し、[第 14 章](14-properties.md)では帰納型がメタ理論にもたらす変化を論じる。

## 演習

<div class="exercise" markdown="1">

等式の対称性を証明せよ。$\EqRec{}$ を使って型 $\tPi{a}{\Nat}{\tPi{b}{\Nat}{a = b \to b = a}}$ の項を組み立てよ。

<details markdown="1">
<summary>解答</summary>

証明 $\refl{}\;a : a = a$ を、motive $\tLam{x}{\Nat}{x = a}$ で $h : a = b$ に沿って輸送する。これにより $a = a$ が $b = a$ に変わる。
$\tLam{a}{\Nat}{\tLam{b}{\Nat}{\tLam{h}{a = b}{\EqRec{1,0}\;\Nat\;a\;(\tLam{x}{\Nat}{x = a})\;(\refl{1}\;\Nat\;a)\;b\;h}}}$。

```leanmini
goal forall (a : Nat), forall (b : Nat), Eq Nat a b -> Eq Nat b a
exact fun (a : Nat) => fun (b : Nat) => fun (h : Eq Nat a b) => ndrec Nat a (fun (x : Nat) => Eq Nat x a) (Eq.refl Nat a) b h
qed
```

（`ndrec` は上のプレイグラウンドのとおり定義しておく。）

</details>

</div>

<div class="exercise" markdown="1">

$\Eq{}$ は命題であるのにすべての宇宙へ消去できる。一方、構成子が二つある型 `Or` はそうではない。理由を説明せよ。

<details markdown="1">
<summary>解答</summary>

$\Eq{}$ は部分単集合である。構成子は一つで、フィールドはない。その再帰子で定義した関数は $a = b$ の二つの証明を区別できない。そのような証明の組み立て方が一通りしかないからである。`Or` には構成子が二つあるので、$\Nat$ への再帰子は二つの注入に対して異なる数を返せてしまい、プログラムの値がどちらの証明が与えられたかに依存することになる。第 8 章にこの規則の正確な形がある。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- $\Eq{}$ は、パラメータ $A$ と $a$、添字 $b$、フィールドを持たない唯一の構成子 $\refl{}$ からなる帰納族である。
- その再帰子は、$a = b$ の証明に沿って $a$ についての事実を $b$ についての事実へ輸送し、$\refl{}$ に対しては何もしない。これが書き換えである。
- 定義的等価は計算で決定される。命題的等価は型であり、その証明には帰納法が要ることがある。$\refl{}$ が前者を後者に変える。
- $n + 0 = n$ は定義的で $0 + n = n$ はそうでない。加法が第二引数で再帰するからである。

</div>
