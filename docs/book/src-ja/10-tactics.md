<div class="lead" markdown="1">

第 9 章末尾の証明項を手で書くのは骨が折れます。タクティクを使えば、残っているゴールを確かめながら項を組み立てられます。本章では、よく使うタクティクがどの項を作るかを追い、完成した項をカーネルが検査する仕組みを見ていきます。

</div>

Lean では、第 9 章の定理を次のように証明します。

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
```

各タクティクは証明項の一部を組み立てる小さなプログラムで、カーネルの*外側*で動きます。出力はふつうの項なので、カーネルは他の項と同じようにアルゴリズム 5.1 で検査します。

## ゴールと証明状態

**ゴール**（goal）$\goal{\Gamma}{\hole{m}}{T}$ は、文脈 $\Gamma$ のもとで型 $T$ を持つ項を求めるものです。**ホール**（hole）$\hole{m}$ はまだ見つかっていない項を表し、Lean ではこれを*メタ変数*と呼びます。**証明状態**（proof state）は、ゴールのリストと、ホールを含んでいてもよい項である**部分的な証明項**を合わせたものです。

$T$ を証明するには、部分項 $\hole{0}$ と唯一のゴール $\goal{\cdot}{\hole{0}}{T}$ から始めます。タクティクは最初のゴール $\goal{\Gamma}{\hole{m}}{T}$ に作用し、新鮮なホールを含んでいてもよい項を $\hole{m}$ に**割り当て**ます。そしてそのゴールを、新鮮なホール一つにつき一つの新しいゴールで置き換えます。ゴールが残っていなければ部分項にホールはなく、カーネルがそれを $T$ に対して検査します。ホールは束縛子の下に置かれることもあります。$\tLam{x}{A}{\hole{1}}$ の $\hole{1}$ がその例で、ここを埋める項はその束縛変数を使えます。ゴールがそれぞれ自分の文脈を持つのはそのためです。

各タクティクは、新しく作ったホールがあとでそれぞれのゴールが求める型の項で埋められるものと仮定して、自分の割り当てが $\Gamma$ のもとで型 $T$ を持つよう保証しなければなりません。以下ではこれを $\goal{\Gamma}{\hole{m}}{T} \leadsto \text{new goals}$ と書き、その後ろに割り当てを添えます。

### 最初の例

スクリプト `examples/identity.leanmini` は第 1 章冒頭の例を証明するもので、下のエクスプローラではそれを 1 コマンドずつ実行できます。

<div class="explorer" data-kind="proof" data-title="証明エクスプローラ: identity"><pre class="script">goal forall (P : Sort 0), P -> P
intro P
intro p
exact p
qed</pre></div>

ボタンか矢印キーで一歩ずつ進めてみてください。中央のパネルは各コマンドの後のゴールのリスト、右のパネルは部分的な証明項で、現在のゴールに対応するホールが強調されています。三つのパネルの内容は常に整合しています。ゴールが変わるのは、タクティクがホールに項を割り当てる*からこそ*です。

ただし、ゴールのリストだけでは情報が足りません。`intro p` のあとのゴール $P$ は、その解を二つの $\lambda$ で包む必要があることを覚えておらず、それを記録しているのは部分項です。

## 基本的なタクティク

**`intro x`。** $T$ が $\Pi$ 型に正規化されるとき、このタクティクはその引数を文脈に移します。

$$
\goal{\Gamma}{\hole{m}}{\tPi{y}{A}{B}} \;\leadsto\; \goal{\Gamma, x : A}{\hole{1}}{\subst{B}{y}{x}},
\qquad
\hole{m} \mathrel{:=} \tLam{x}{A}{\hole{1}}.
$$

割り当てが正しく型付けされることは T-Lam から従います。名前 $x$ は $\dom(\Gamma)$ に含まれていてはいけません。含まれていると新しい仮定が既存の仮定をシャドーイングし、カーネルが不健全になります（[第 11 章](11-substitution-alpha.md#variable-capture-in-contexts)）。本書の `intro` はそのような名前を「binder name already in context」というメッセージで拒否しますが、Lean は名前を付け替えます。

**`exact t`。** このタクティクは、与えられた項でゴールを閉じます。

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \text{no goals},
\qquad
\hole{m} \mathrel{:=} t,
$$

閉じる前に、タクティク自身が $\Check(\Gamma, t, T)$ を実行します。型の正しくない $t$ はどのみち最後にカーネルが拒否するので、この早めの検査はエラーメッセージを分かりやすくするためのものにすぎません。

**`apply f`。** $f$ が型 $A_1 \to \cdots \to A_n \to B$ を持ち $B \conv T$ であるとき、このタクティクは引数を新しいゴールとして残します。

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{A_1}, \ldots, \goal{\Gamma}{\hole{n}}{A_n},
\qquad
\hole{m} \mathrel{:=} f\;\hole{1} \cdots \hole{n}.
$$

T-App を $n$ 回使えば割り当ての型は $B$ になり、T-Conv によって型 $T$ も持ちます。$f$ の型が依存 $\Pi$ のときは、後ろの $A_i$ と $B$ が前の引数を含むので、タクティクは $B$ を $T$ と照合してそれらの引数を見つけなければなりません。Lean は*単一化*でメタ変数を解いてこれを行いますが、本書の制限版は非依存の矢印しか扱わず、それ以外は「dependent apply requires elaboration/unification」と報告します。（$n = 0$ のとき、つまり $f$ の型がすでに $T$ と変換可能なら、`apply f` は `exact f` と同じに振る舞います。）

たとえば第 6 章の二つ目の演習で扱った含意の推移性は、結論から逆向きに証明できます。

<div class="explorer" data-kind="proof" data-title="証明エクスプローラ: apply による推移性"><pre class="script">goal forall (P : Sort 0), forall (Q : Sort 0), forall (R : Sort 0), (P -> Q) -> (Q -> R) -> P -> R
intro P
intro Q
intro R
intro f
intro g
intro p
apply g
apply f
exact p
qed</pre></div>

六回の `intro` のあと、ゴールは $\goal{\Gamma}{\hole{6}}{R}$ で、$\Gamma = P, Q, R : \Sort{0},\; f : P \to Q,\; g : Q \to R,\; p : P$ です。型 $R$ の仮定はないので `exact` では閉じられませんが、$g$ の型は $R$ で*終わって*います。`apply g` は $\hole{6} \mathrel{:=} g\;\hole{7}$ を割り当て、$\hole{7} : Q$ を残します。同様に `apply f` は $\hole{7} \mathrel{:=} f\;\hole{8}$ を割り当てて $\hole{8} : P$ を残し、これを `exact p` が閉じます。得られる項の本体は $g\;(f\;p)$ です。二つのタクティクの違いに注意してください。$g$ の型は $R$ ではなく $Q \to R$ なので `exact g` は失敗しますが、`apply g` なら $g$ に足りない引数を新しいゴールにしてくれます。

**`change T'`。** このタクティクは、ゴールを定義的に等しいものに置き換えます。

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{T'},
\qquad
\hole{m} \mathrel{:=} \hole{1},
$$

ただし $T'$ は型で、$T' \conv T$ でなければなりません。項には何も加えず、ゴールの見せ方を変えるだけで、その正当性は T-Conv が保証します。`change` が必要になるのは、`rw`（後述）が部分項を α 同値の範囲でしか探さないからです。計算してはじめて現れる部分項は、まず `change` で表に出しておく必要があります。本章末尾の例がちょうどそうです。

**`rfl`。** $T$ が $\Eq{u}\;A\;a\;b$ に正規化され $a \conv b$ であるとき、このタクティクはゴールを閉じます。

$$
\goal{\Gamma}{\hole{m}}{\Eq{u}\;A\;a\;b} \;\leadsto\; \text{no goals},
\qquad
\hole{m} \mathrel{:=} \refl{u}\;A\;a.
$$

割り当ての型は $\Eq{u}\;A\;a\;a$ で、ゴールと変換可能です。つまり `rfl` で証明できるのは、ちょうど定義的等価によって成り立つ等式です（[第 9 章](09-equality.md)）。

## 帰納法

$n : \Nat$ を $\Gamma$ の変数とし、$\Gamma \vdash T : \Sort{u}$ とします。タクティク `induction n` は、ゴールの中の $n$ を抽象化して motive を作り、構成子ごとに一つのゴールを生成します。

$$
\begin{array}{l}
\goal{\Gamma}{\hole{m}}{T}
\;\leadsto\;
\goal{\Gamma}{\hole{z}}{\subst{T}{n}{\zero}},\;
\goal{\Gamma, k : \Nat, \mathit{ih} : \subst{T}{n}{k}}{\hole{s}}{\subst{T}{n}{\suc\;k}}, \\[4pt]
\hole{m} \mathrel{:=} \NatRec{u}\;(\tLam{z}{\Nat}{\subst{T}{n}{z}})\;\hole{z}\;(\tLam{k}{\Nat}{\tLam{\mathit{ih}}{\subst{T}{n}{k}}{\hole{s}}})\;n.
\end{array}
$$

motive を $M = \tLam{z}{\Nat}{\subst{T}{n}{z}}$ とすると、$\NatRec{u}\;M$ の型は $M\;\zero$ と $\tPi{k}{\Nat}{M\;k \to M\;(\suc\;k)}$ の項を引数に求め、結果の型は $M\;n$ です。これらは β 簡約により、それぞれ二つのゴールの型および $T$ と変換可能です。この構成が正しいのは、名前が新鮮で、レベル $u$ が正しく、他のどの仮定にも $n$ が現れないときに限ります。

- motive が $n$ ではなく新鮮な名前 $z$ を束縛するのは、$n$ がすでに $\Gamma$ にあり、$\tLam{n}{\Nat}{T}$ と書くとそれをシャドーイングしてしまい、第 11 章の落とし穴にはまるからです。同様に $k$ と $\mathit{ih}$ も新鮮でなければなりません。（本書の実装では、motive の変数を `ind_x`、後者の構成子のフィールドを（`n` が使用済みなら）`k`、仮定を `ih` と名付けます。）
- motive のレベル $u$ はゴールの型から来るもので、$\InferSort$ で求めます。命題なら $0$ で、$\NatRec{0}$ がそのまま帰納法になります。
- 他の仮定に $n$ が現れるとき、たとえば $h : n = 2$ があると、新しいゴールには元の $n$ についての $h$ が残ったままになり、$\mathit{ih}$ はそれについて何も教えてくれません。そのため、ゴール自体は正しくても証明できなくなることがあります。Lean の `induction` はそのような仮定をまずゴールの中に戻し（*リバート*し）、motive の一部にしますが、本書の実装では、後ろの仮定に $n$ が現れないことを要求し、そうでなければ「induction: revert dependent hypotheses first」と報告します。

この実装は $\Nat$ 専用ではなく、添字を持たない任意の帰納型で動きます。シグネチャから再帰子の型を読み取り、構成子ごとに小前提を一つずつ取り出して、それぞれを、構成子のフィールドと帰納法の仮定を文脈に持つゴールに変えます。スクリプト `examples/generic-list.leanmini` は、ユーザーが宣言したリスト型に対してこれを使います。

## 書き換え

$h : \Eq{u}\;A\;a\;b$ とし、ゴール $T$ を命題とします。タクティク `rw h` は、ゴールの中の $a$ を $b$ に三段階で置き換えます。

1. **抽象化。** 新鮮な $x$ を選び、$T$ の中の $a$ のすべての出現を $x$ で置き換えたものを $C$ とします。出現は変換可能性ではなく α 同値で照合します。$a$ の自由変数を束縛する束縛子の下にある出現は、そこでは別のものを指しているので対象外です。
2. **motive の検査。** $\Gamma, x : A \vdash C : \Sort{0}$ を検査します。これは後述のとおり失敗することがあります。
3. **項の構築。** 新しいゴールは $\subst{C}{x}{b}$、つまり $a$ を $b$ に置き換えたゴールです。
   $$
   \goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{\subst{C}{x}{b}},
   \qquad
   \hole{m} \mathrel{:=} \EqRec{u,0}\;A\;a\;(\tLam{x}{A}{C \to T})\;(\tLam{p}{T}{p})\;b\;h\;\hole{1}.
   $$

この割り当てが型 $T$ を持つことを確かめましょう。motive を $N = \tLam{x}{A}{C \to T}$ と書きます。$\subst{C}{x}{a} = T$ なので、項 $N\;a$ は $T \to T$ と変換可能で、恒等関数 $\tLam{p}{T}{p}$ がその型を持ちます。$h$ に沿って輸送すると $N\;b$ が得られます。これは $\subst{C}{x}{b} \to T$ と変換可能なので、$\hole{1}$ に適用すれば型 $T$ の項になります。Lean は同じ発想から `Eq.mpr (congrArg (fun x => C) h)` という別の項を組み立て、新しいゴールを `rfl` で閉じることまで試みます。本書の実装ではそれを明示的な `rfl` に任せ、二つの段階をスクリプト上で見えるようにしました。

**motive の型が正しくないとき。** $a$ を抽象化するとゴールが壊れることがあります。$\Gamma = n : \Nat,\; h : n = 2,\; q : n = 0$ とし、証明 $q$ についての主張であるゴール $\Eq{0}\;(n = 0)\;q\;q$ に `rw h` を実行したとしましょう。$n$ を抽象化すると $C = \Eq{0}\;(x = 0)\;q\;q$ となります。ところが $q$ の型は $x = 0$ ではなく $n = 0$ で、$q$ 自身は抽象化できないので、この式は型が正しくありません。段階 2 が失敗し、Lean も同じ状況を「motive is not type correct」と報告します。段階 2 がなければ、タクティクはカーネルに拒否される項を生成してしまいます。健全性は損なわれませんが、ユーザーにとっては不親切です。

<aside class="code" markdown="1">

タクティクは `src/proof.rs` にある `ProofState` のメソッドとして実装されています。部分的な証明項は `Template`（`src/template.rs`）で、`Hole(i)` ノードを持つ項です。`materialize` は解を代入し、未解決のホールがあれば失敗します。`ProofState::replace` が割り当てを行い、現在のゴールの解を記録して、新しいゴールを先頭に継ぎ足します。`intro`、`exact`、`apply`、`change`、`rfl`、`induction`、`rw` はそれぞれ上の説明のとおりに動きます。`rw` は段階 1 に `replace_exact` を、段階 2 に `check_transport` を使います。`qed` に対応するのは `finish` で、項を具体化して元のゴールに対して `Kernel::check` を呼びます。

</aside>

## 例: タクティクによる 0 + n = n

本書の体系では、第 9 章の証明は次のスクリプトになります。`examples/zero-add.leanmini` に $\add$ の定義を加えたものです（スクリプトでは $0 + n$ を `add Nat.zero n` と書きます）。

<div class="explorer" data-kind="proof" data-title="証明エクスプローラ: 0 + n = n"><pre class="script">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
induction n
rfl
change Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ k)
rw ih
rfl
qed</pre></div>

部分項が育っていく様子を見てください。`induction n` が二つのホールを持つ $\NatRec{0}$ を挿入し、`rfl` が最初のホールを埋め、`change` は項には触れずゴールだけを書き換え、`rw ih` が輸送を挿入して最後の `rfl` のためのホールを一つ残します。`change` の行を消してスクリプトを適用すると、`rw` が左辺を見つけられずに失敗するのが分かります。

<div class="playground" data-file="examples/zero-add.leanmini"><pre># 第二引数に関する再帰による加法:
#   add m zero     = m
#   add m (succ k) = succ (add m k)
def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n

# add zero n = n は定義的ではないので、n に関する帰納法が要る。
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
induction n
# 基底ケース: add zero zero は zero に簡約される。
rfl
# ステップケース: add zero (succ k) を succ (add zero k) に展開し、ih を使う。
change Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ k)
rw ih
rfl
qed</pre></div>

できあがる項は、第 9 章で手書きしたものと二箇所で異なります。`intro` を使ったので $\tLam{n}{\Nat}{\ldots\;n}$ で始まる点と、ステップケースで `rw` が組み立てた motive を使う点です。どちらも同じ命題の証明で、カーネルはどちらでも受け入れます。プレイグラウンドで `change` の行を消し、`rw` が出すエラーを読んでみてください。

## なぜタクティクを信頼する必要がないのか

最終的な項はカーネルが検査するので、タクティクが正しくなくても体系の健全性は保たれます。バグのあるタクティクは、失敗するか、型の正しくない項を生成してカーネルに拒否されるかのどちらかであり、偽の定理をカーネルに受理させることはできません。`exact` の $\Check$ や `rw` の motive の検査など、タクティク自身が行う検査は、エラーを早く分かりやすく報告するためにあるにすぎません。

したがって、体系のうち信頼しなければならない部分は小さく、アルゴリズム 5.1、第 III 部の簡約関数と比較関数、第 8 章のシグネチャ構築手続きだけです。`src/proof.rs` と `src/syntax.rs` の中身はすべてその外側にあります。

Lean のタクティク基盤は、ここで素描したものよりはるかに豊富です。単一化で解かれるメタ変数、暗黙の引数を補い `0 + n` のような記法を展開するエラボレータ、依存する仮定をリバートし添字付きの族も扱う `induction`、`simp` のような自動化などが揃っています。これらはすべて信頼されない側にあり、Lean のカーネルも本書のものと同じく、完成した項しか見ません [de Moura and Ullrich 2021]。

## 演習

<div class="exercise" markdown="1">

$\tPi{n}{\Nat}{n = n}$ を、帰納法を使ってタクティクで証明し、なぜ両方のケースが `rfl` で閉じるのかを説明してください。

<details markdown="1">
<summary>解答</summary>

これは `examples/nat-reflexivity.leanmini` です。`intro n`、`induction n`、`rfl`、`rfl`、`qed`。基底のゴールは $0 = 0$、ステップのゴールは $\suc\;k = \suc\;k$ で、どちらも両辺が構文的に同一なので、定義的等価は自明に成り立ちます。ここで帰納法は不要ですが（`intro n` のあと `rfl` 一つで済みます）、ゴールの形を見るには役に立ちます。

</details>

</div>

<div class="exercise" markdown="1">

ゴールが $\Eq{}\;\Nat\;a\;c$、仮定が $h : a = b$、文脈が $a, b, c : \Nat$ のとき、`rw` が生成する項を書いてください。

<details markdown="1">
<summary>解答</summary>

$a$ を抽象化すると $C = (x = c)$ となり、新しいゴールは $b = c$ です。割り当ては
$\EqRec{1,0}\;\Nat\;a\;(\tLam{x}{\Nat}{(x = c) \to (a = c)})\;(\tLam{p}{a = c}{p})\;b\;h\;\hole{1}$ で、$\hole{1} : b = c$ です。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 証明状態はゴールのリストとホールを持つ部分項の組です。タクティクは最初のホールに項を割り当て、新鮮なホールごとに新しいゴールを一つ開きます。
- `intro` は $\lambda$ を組み立て、`exact` は項を差し込み、`apply` は引数の位置にホールを持つ適用を組み立て、`change` は T-Conv を使い、`rfl` は $\refl{}$ を使います。
- `induction` は変数を motive へ抽象化して再帰子を適用し、`rw` は左辺を motive へ抽象化して輸送を適用します。
- カーネルは完成した項を検査し直すので、タクティクは信頼基盤の外側にあります。

</div>
