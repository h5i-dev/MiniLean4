<div class="lead" markdown="1">

Lean のユーザーが、第 9 章の末尾にあるような項を手で書くことはめったにない。書くのはタクティクスクリプトである。これはコマンドの列で、残っている証明すべきものをシステムが表示しながら、項を一歩ずつ組み立てていく。本章では、よく使われるタクティクが本書の体系でどのように項を構築するか、そしてなぜそのどれも信頼する必要がないかを示す。

</div>

Lean では、第 9 章の定理は次のように証明される。

```lean
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]
```

各タクティクは、証明項の一部を組み立てる小さなプログラムである。タクティクはカーネルの*外側*で動く。その出力はふつうの項であり、カーネルは他の項と同じようにアルゴリズム 5.1 でそれを検査する。

## ゴールと証明状態

**ゴール**（goal）$\goal{\Gamma}{\hole{m}}{T}$ は、文脈 $\Gamma$ における型 $T$ の項を求める。**ホール**（hole）$\hole{m}$ はまだ見つかっていない項を表す。Lean ではこれを*メタ変数*と呼ぶ。**証明状態**（proof state）は、ゴールのリストと、ホールを含みうる項である**部分的な証明項**を合わせたものである。

$T$ を証明するには、部分項 $\hole{0}$ と唯一のゴール $\goal{\cdot}{\hole{0}}{T}$ から始める。タクティクは最初のゴール $\goal{\Gamma}{\hole{m}}{T}$ に対して働く。$\hole{m}$ に、新鮮なホールを含みうる項を**割り当て**、そのゴールを新鮮なホールごとに一つの新しいゴールで置き換える。ゴールが残っていなければ部分項にホールはなく、カーネルがそれを $T$ に対して検査する。ホールは束縛子の下に置かれることがある。$\tLam{x}{A}{\hole{1}}$ の $\hole{1}$ がそうで、それを埋める項はその束縛変数を使ってよい。ゴールがそれぞれ自分の文脈を持つのはそのためである。

各タクティクは、新鮮な各ホールがのちにそのゴールの述べる型の項で埋められると仮定したうえで、自分の割り当てが $\Gamma$ において型 $T$ を持つことを保証しなければならない。これを $\goal{\Gamma}{\hole{m}}{T} \leadsto \text{new goals}$ と書き、続けて割り当てを書く。

### 最初の例

スクリプト `examples/identity.leanmini` は第 1 章の冒頭の例を証明する。下のエクスプローラはそれを一コマンドずつ実行する。

<div class="explorer" data-kind="proof" data-title="証明エクスプローラ: identity"><pre class="script">goal forall (P : Sort 0), P -> P
intro P
intro p
exact p
qed</pre></div>

ボタンか矢印キーで一歩ずつ進めてほしい。中央のパネルは各コマンドの後のゴールのリスト、右のパネルは部分的な証明項で、現在のゴールに対応するホールが強調されている。三つのパネルは常に一致する。タクティクがホールに項を割り当てる*からこそ*、ゴールが変わる。

ゴールのリストだけでは足りない。`intro p` のあと、ゴール $P$ は、その解が二つの $\lambda$ で包まれなければならないことを覚えていない。部分項がそれを記録する。

## 基本的なタクティク

**`intro x`。** $T$ が $\Pi$ 型に正規化されるとき、このタクティクはその引数を文脈に移す。

$$
\goal{\Gamma}{\hole{m}}{\tPi{y}{A}{B}} \;\leadsto\; \goal{\Gamma, x : A}{\hole{1}}{\subst{B}{y}{x}},
\qquad
\hole{m} \mathrel{:=} \tLam{x}{A}{\hole{1}}.
$$

割り当てが正しい型を持つことは T-Lam による。名前 $x$ は $\dom(\Gamma)$ に含まれていてはならない。さもないと新しい仮定が既存の仮定をシャドーイングし、カーネルが不健全になる（[第 11 章](11-substitution-alpha.md#variable-capture-in-contexts)）。本書の `intro` はそのような名前を「binder name already in context」というメッセージで拒否する。Lean は名前を付け替える。

**`exact t`。** このタクティクは、与えられた項でゴールを閉じる。

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \text{no goals},
\qquad
\hole{m} \mathrel{:=} t,
$$

その前に自分で $\Check(\Gamma, t, T)$ を実行する。型の正しくない $t$ はどのみち最後にカーネルが拒否する。早めに検査するのは、よりよいエラーメッセージのためでしかない。

**`apply f`。** $f$ が型 $A_1 \to \cdots \to A_n \to B$ を持ち $B \conv T$ であるとき、このタクティクは引数を新しいゴールとして残す。

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{A_1}, \ldots, \goal{\Gamma}{\hole{n}}{A_n},
\qquad
\hole{m} \mathrel{:=} f\;\hole{1} \cdots \hole{n}.
$$

割り当ては T-App を $n$ 回使って型 $B$ を持ち、T-Conv により型 $T$ を持つ。$f$ の型が依存 $\Pi$ のときは、後ろの $A_i$ と $B$ が前の引数に言及するので、タクティクは $B$ を $T$ と照合してそれらの引数を見つけなければならない。Lean はこれを*単一化*で行い、メタ変数について解く。本書の制限版は非依存の矢印しか扱わず、それ以外は「dependent apply requires elaboration/unification」と報告する。（$n = 0$ のとき、つまり $f$ の型がすでに $T$ と変換可能なら、`apply f` は `exact f` と同じに振る舞う。）

たとえば、第 6 章の二つ目の演習だった含意の推移性は、結論から逆向きに進められる。

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

六回の `intro` のあと、ゴールは $\goal{\Gamma}{\hole{6}}{R}$ で、$\Gamma = P, Q, R : \Sort{0},\; f : P \to Q,\; g : Q \to R,\; p : P$ である。型 $R$ の仮定はないので `exact` では閉じられないが、$g$ は $R$ で*終わる*。`apply g` は $\hole{6} \mathrel{:=} g\;\hole{7}$ を割り当て、$\hole{7} : Q$ を残す。同様に `apply f` は $\hole{7} \mathrel{:=} f\;\hole{8}$ を割り当てて $\hole{8} : P$ を残し、これを `exact p` が閉じる。得られる項の本体は $g\;(f\;p)$ である。二つのタクティクの違いに注意してほしい。`exact g` は失敗する。$g$ の型は $Q \to R$ であって $R$ ではないからである。一方 `apply g` は、$g$ に足りない引数を新しいゴールに変える。

**`change T'`。** このタクティクは、ゴールを定義的に等しいものに置き換える。

$$
\goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{T'},
\qquad
\hole{m} \mathrel{:=} \hole{1},
$$

ただし $T'$ は型で、$T' \conv T$ でなければならない。項には何も加えない。ゴールの表示の仕方を変えるだけであり、それを正当化するのは T-Conv である。`change` が必要なのは、`rw`（後述）が部分項を α 同値までしか探さないからである。計算してはじめて現れる部分項は、まず `change` で露出させなければならない。本章末尾の例がそうである。

**`rfl`。** $T$ が $\Eq{u}\;A\;a\;b$ に正規化され $a \conv b$ であるとき、このタクティクはゴールを閉じる。

$$
\goal{\Gamma}{\hole{m}}{\Eq{u}\;A\;a\;b} \;\leadsto\; \text{no goals},
\qquad
\hole{m} \mathrel{:=} \refl{u}\;A\;a.
$$

割り当ての型は $\Eq{u}\;A\;a\;a$ で、これはゴールと変換可能である。つまり `rfl` が証明するのは、定義的等価で成り立つ等式そのものである（[第 9 章](09-equality.md)）。

## 帰納法

$n : \Nat$ を $\Gamma$ の変数とし、$\Gamma \vdash T : \Sort{u}$ とする。タクティク `induction n` は、ゴールの中の $n$ を抽象化して motive を作り、構成子ごとに一つのゴールを生成する。

$$
\begin{array}{l}
\goal{\Gamma}{\hole{m}}{T}
\;\leadsto\;
\goal{\Gamma}{\hole{z}}{\subst{T}{n}{\zero}},\;
\goal{\Gamma, k : \Nat, \mathit{ih} : \subst{T}{n}{k}}{\hole{s}}{\subst{T}{n}{\suc\;k}}, \\[4pt]
\hole{m} \mathrel{:=} \NatRec{u}\;(\tLam{z}{\Nat}{\subst{T}{n}{z}})\;\hole{z}\;(\tLam{k}{\Nat}{\tLam{\mathit{ih}}{\subst{T}{n}{k}}{\hole{s}}})\;n.
\end{array}
$$

motive を $M = \tLam{z}{\Nat}{\subst{T}{n}{z}}$ とすると、$\NatRec{u}\;M$ の型は $M\;\zero$ と $\tPi{k}{\Nat}{M\;k \to M\;(\suc\;k)}$ を求め、結果の型は $M\;n$ である。これらは β により、二つのゴールの型および $T$ と変換可能である。この構成が正しいのは、名前が新鮮で、レベル $u$ が正しく、他のどの仮定も $n$ に言及しないときに限る。

- motive は $n$ ではなく新鮮な名前 $z$ を束縛する。$n$ はすでに $\Gamma$ にあるので、$\tLam{n}{\Nat}{T}$ と書くとそれをシャドーイングしてしまい、第 11 章の落とし穴にはまる。同様に $k$ と $\mathit{ih}$ も新鮮でなければならない。（本書の実装では、motive の変数を `ind_x`、`n` が使われているときの後者の構成子のフィールドを `k`、仮定を `ih` と名付ける。）
- motive のレベル $u$ はゴールの型から来るもので、$\InferSort$ で求める。命題なら $0$ であり、$\NatRec{0}$ が帰納法である。
- 他の仮定が $n$ に言及しているとき、たとえば $h : n = 2$ があるとき、新しいゴールには元の $n$ についての $h$ が残ったままで、$\mathit{ih}$ はそれについて何も言わない。ゴールは正しいが、証明できないかもしれない。Lean の `induction` はそのような仮定をまずゴールの中に戻し（*リバート*し）、motive の一部にする。本書の実装では、後続の仮定が $n$ に言及しないことを要求し、そうでなければ「induction: revert dependent hypotheses first」と報告する。

この実装は $\Nat$ に固有のものではない。添字を持たない任意の帰納型で動く。シグネチャから再帰子の型を読み、構成子ごとに小前提を一つずつ剥がし、それぞれを、構成子のフィールドと帰納法の仮定を文脈に持つゴールに変える。スクリプト `examples/generic-list.leanmini` は、ユーザーが宣言したリスト型に対してこれを使う。

## 書き換え

$h : \Eq{u}\;A\;a\;b$ とし、ゴール $T$ を命題とする。タクティク `rw h` は、ゴールの中の $a$ を $b$ に三段階で置き換える。

1. **抽象化。** 新鮮な $x$ を選び、$T$ の中の $a$ のすべての出現を $x$ で置き換えたものを $C$ とする。出現は変換ではなく α 同値までで探す。$a$ の自由変数を束縛する束縛子の下にある出現は、そこでは別のものを指すので飛ばす。
2. **motive の検査。** $\Gamma, x : A \vdash C : \Sort{0}$ を検査する。これは失敗しうる。後述する。
3. **項の構築。** 新しいゴールは $\subst{C}{x}{b}$、つまり $a$ を $b$ に置き換えたゴールである。
   $$
   \goal{\Gamma}{\hole{m}}{T} \;\leadsto\; \goal{\Gamma}{\hole{1}}{\subst{C}{x}{b}},
   \qquad
   \hole{m} \mathrel{:=} \EqRec{u,0}\;A\;a\;(\tLam{x}{A}{C \to T})\;(\tLam{p}{T}{p})\;b\;h\;\hole{1}.
   $$

この割り当てが型 $T$ を持つことを見るために、motive を $N = \tLam{x}{A}{C \to T}$ と書く。$\subst{C}{x}{a} = T$ なので、項 $N\;a$ は $T \to T$ と変換可能で、恒等関数 $\tLam{p}{T}{p}$ がその型を持つ。$h$ に沿って輸送すると $N\;b$ が得られ、これは $\subst{C}{x}{b} \to T$ と変換可能である。それを $\hole{1}$ に適用すれば $T$ になる。Lean は同じ発想から `Eq.mpr (congrArg (fun x => C) h)` という別の項を組み立て、さらに新しいゴールを `rfl` で閉じることも試みる。本書の実装ではそれを明示的な `rfl` に任せ、二つの段階がスクリプト上で見えるようにしている。

**motive の型が正しくないとき。** $a$ を抽象化するとゴールが壊れることがある。$\Gamma = n : \Nat,\; h : n = 2,\; q : n = 0$ とし、証明 $q$ についての主張であるゴール $\Eq{0}\;(n = 0)\;q\;q$ に `rw h` を実行したとしよう。$n$ を抽象化すると $C = \Eq{0}\;(x = 0)\;q\;q$ となるが、これは型が正しくない。$q$ の型は $n = 0$ であって $x = 0$ ではなく、$q$ 自身は抽象化できない。段階 2 が失敗し、Lean も同じ状況を「motive is not type correct」と報告する。段階 2 がなければ、タクティクはカーネルに拒否される項を生成する。健全性には無害だが、ユーザーの役には立たない。

<aside class="code" markdown="1">

タクティクは `src/proof.rs` の `ProofState` のメソッドである。部分的な証明項は `Template`（`src/template.rs`）で、`Hole(i)` ノードを持つ項である。`materialize` は解を代入し、未解決のホールがあれば失敗する。`ProofState::replace` が割り当てを行う。現在のゴールの解を記録し、新しいゴールを先頭に継ぎ足す。`intro`、`exact`、`apply`、`change`、`rfl`、`induction`、`rw` はそれぞれ上の説明のとおりに動く。`rw` は段階 1 に `replace_exact` を、段階 2 に `check_transport` を使う。`finish` が `qed` であり、項を具体化して元のゴールに対して `Kernel::check` を呼ぶ。

</aside>

## 例: タクティクによる 0 + n = n

本書の体系では、第 9 章の証明は次のスクリプトになる。これは `examples/zero-add.leanmini` に $\add$ の定義を含めたものである（スクリプトでは $0 + n$ を `add Nat.zero n` と書く）。

<div class="explorer" data-kind="proof" data-title="証明エクスプローラ: 0 + n = n"><pre class="script">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
induction n
rfl
change Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ k)
rw ih
rfl
qed</pre></div>

部分項が育っていく様子を見てほしい。`induction n` が二つのホールを持つ $\NatRec{0}$ を挿入し、`rfl` が最初のホールを埋め、`change` は項には触れずゴールだけを書き換え、`rw ih` が輸送を挿入して最後の `rfl` のためのホールを一つ残す。`change` の行を消してスクリプトを適用すると、`rw` が左辺を見つけられずに失敗するのが分かる。

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

この項は、第 9 章で手書きしたものと二箇所で異なる。`intro` のために $\tLam{n}{\Nat}{\ldots\;n}$ で始まることと、ステップが `rw` の組み立てた motive を使うことである。どちらも同じ命題の証明であり、カーネルはどちらを受け取っても構わない。プレイグラウンドで `change` の行を消し、`rw` が出すエラーを読んでみてほしい。

## なぜタクティクを信頼する必要がないのか

カーネルが最終的な項を検査するので、体系が健全であるためにタクティクが正しい必要はない。バグのあるタクティクは、失敗するか、型の正しくない項を生成してカーネルに拒否されるかのどちらかである。偽の定理をカーネルに受理させることはできない。`exact` の $\Check$ や `rw` の motive の検査など、タクティク自身が行う検査は、エラーを早く分かりやすく報告するためにあるにすぎない。

したがって体系の信頼すべき部分は小さい。アルゴリズム 5.1、第 III 部の簡約関数と比較関数、そして第 8 章のシグネチャ構築手続きである。`src/proof.rs` と `src/syntax.rs` の中身はすべてその外側にある。

Lean のタクティク基盤は、ここで素描したものよりはるかに豊かである。単一化で解かれるメタ変数、暗黙の引数を補い `0 + n` のような記法を展開するエラボレータ、依存する仮定をリバートし添字付きの族も扱う `induction`、そして `simp` のような自動化がある。これらはすべて信頼されない側にある。Lean のカーネルも本書のものと同じく、完成した項しか見ない [de Moura and Ullrich 2021]。

## 演習

<div class="exercise" markdown="1">

$\tPi{n}{\Nat}{n = n}$ をタクティクで、帰納法を使って証明し、なぜ両方のケースが `rfl` で閉じるのかを説明せよ。

<details markdown="1">
<summary>解答</summary>

これは `examples/nat-reflexivity.leanmini` である。`intro n`、`induction n`、`rfl`、`rfl`、`qed`。基底のゴールは $0 = 0$、ステップのゴールは $\suc\;k = \suc\;k$ で、どちらも両辺が構文的に同一なので、定義的等価は自明に成り立つ。ここで帰納法は不要だが（`intro n` のあと `rfl` 一つで済む）、ゴールの形を見るには役に立つ。

</details>

</div>

<div class="exercise" markdown="1">

ゴールが $\Eq{}\;\Nat\;a\;c$、仮定が $h : a = b$、文脈が $a, b, c : \Nat$ のとき、`rw` が生成する項を書け。

<details markdown="1">
<summary>解答</summary>

$a$ を抽象化すると $C = (x = c)$ となり、新しいゴールは $b = c$ である。割り当ては
$\EqRec{1,0}\;\Nat\;a\;(\tLam{x}{\Nat}{(x = c) \to (a = c)})\;(\tLam{p}{a = c}{p})\;b\;h\;\hole{1}$ で、$\hole{1} : b = c$ である。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 証明状態は、ゴールのリストと、ホールを持つ部分項である。タクティクは最初のホールに項を割り当て、新鮮なホールごとに新しいゴールを一つ開く。
- `intro` は $\lambda$ を組み立て、`exact` は項を差し込み、`apply` は引数の位置にホールを持つ適用を組み立て、`change` は T-Conv を使い、`rfl` は $\refl{}$ を使う。
- `induction` は変数を motive へ抽象化して再帰子を適用し、`rw` は左辺を motive へ抽象化して輸送を適用する。
- カーネルは完成した項を検査し直すので、タクティクは信頼基盤の外側にある。

</div>
