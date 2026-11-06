<div class="lead" markdown="1">

本章では、いくつかの小さな項に対してアルゴリズム 5.1 を手で実行し、各実行を型付け規則に対応づける。例は、アルゴリズムの仕事を一つずつ見せるように選んである。導出を組み立てること、誤った証明を捕まえること、仮定を使うこと、全称命題を具体化すること、型の内部で計算することである。以下のトレースはどれも、プレイグラウンドでカーネル上に再現できる。

</div>

定理 $T$ の証明 $t$ を検証するために、カーネルは $\Check(\cdot, t, T)$ を呼ぶ。これは $\Infer(\cdot, t)$ を呼び、その結果を $T$ と比較する。トレースには、$\Infer$ が行う再帰呼び出しと、各呼び出しが対応する型付け規則を示す。ノードを開いたり閉じたりして、再帰を追ってほしい。

## 恒等証明

$\Gamma_1 = P : \Sort{0}$、$\Gamma_2 = \Gamma_1, h : P$ とおく。[第 1 章](01-propositions-as-types.md) の冒頭の例の導出は、整形式性の前提を省くと次のようになる。

$$
\dfrac{
  \dfrac{}{\cdot \vdash \Sort{0} : \Sort{1}}\rulename{T-Sort}
  \qquad
  \dfrac{
    \dfrac{}{\Gamma_1 \vdash P : \Sort{0}}\rulename{T-Var}
    \qquad
    \dfrac{}{\Gamma_2 \vdash h : P}\rulename{T-Var}
  }{\Gamma_1 \vdash \tLam{h}{P}{h} : P \to P}\rulename{T-Lam}
}{\cdot \vdash \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}} : \tPi{P}{\Sort{0}}{P \to P}}\rulename{T-Lam}
$$

アルゴリズムは、同じ導出を下から上へ組み立てる。呼び出し $\Infer(\cdot, \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}})$ は次のように進む。

<ul class="trace">
<li>$\Infer(\cdot,\; \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}})$ <span class="rule">T-Lam</span>
  <ul>
  <li>$\InferSort(\cdot,\; \Sort{0})$: $\Infer$ が $\Sort{1}$ を返すので、注釈は型である <span class="rule">T-Sort</span></li>
  <li>文脈が空なので、$\Freshen$ は $P$ をそのままにする</li>
  <li>$\Infer(\Gamma_1,\; \tLam{h}{P}{h})$ <span class="rule">T-Lam</span>
    <ul>
    <li>$\InferSort(\Gamma_1,\; P)$: $\Infer$ が $P$ を引いて $\Sort{0}$ を返す <span class="rule">T-Var</span></li>
    <li>$\Freshen$ は $h$ をそのままにする</li>
    <li>$\Infer(\Gamma_2,\; h)$ は $h$ を引いて $P$ を返す <span class="rule">T-Var</span></li>
    <li class="result">$\tPi{h}{P}{P}$ を返す</li>
    </ul>
  </li>
  <li class="result">$\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$ を返す</li>
  </ul>
</li>
</ul>

型を返す各呼び出しは、導出木の一つのノードに対応する。計算を使う呼び出しは一つもない。最後に $\Check$ が、結果を宣言された型 $\tPi{P}{\Sort{0}}{P \to P}$ と比較する。両者の違いは束縛変数一つの名前だけである。$P \to P$ は $\tPi{\_}{P}{P}$ の略記であり、$h$ も $\_$ も本体には現れないからである。したがって $\IsDefEq$ は成功し、証明は受理される。

同じ実行を、カーネル自身に記録させたものが次である。呼び出しビューは上のリストと、証明木ビューは導出と一致する。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

<div class="playground" data-file="examples/identity.leanmini"><pre># 同じ証明を、完全な項として与える。カーネルはその型を推論し、
# ゴールと比較する。
goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : P) => h
qed</pre></div>

## 誤った証明

利用者が、$t = \tLam{P}{\Sort{0}}{\tLam{h}{P}{P}}$ は $\tPi{P}{\Sort{0}}{P \to P}$ を証明すると主張したとしよう。本体は証明 $h$ ではなく命題 $P$ を返している。カーネルは $\Check(\cdot, t, \tPi{P}{\Sort{0}}{P \to P})$ を呼び、まず $\Infer$ が走る。呼び出しは上と同じだが、最後の $\Infer(\Gamma_2, P)$ だけが $\Sort{0}$ を返す。つまり $\Infer$ は*成功し*、結果は

$$
\Infer(\cdot, t) \;=\; \tPi{P}{\Sort{0}}{\tPi{h}{P}{\Sort{0}}}.
$$

となる。項 $t$ は正しく型付けされるが、主張された命題の証明にはなっていない。$\Check$ が二つの型を比較しても、どちらもこれ以上計算できず、束縛変数を改名しても一致しない。いちばん内側の本体が片方では $\Sort{0}$、もう片方では $P$ だからである。そのため $\IsDefEq$ は失敗し、$\Check$ は型の不一致を報告する。（[第 11 章](11-substitution-alpha.md#alpha-equivalence) では、$\IsDefEq$ が使うアルゴリズムでこの比較を一歩ずつ再現する。）

この誤りが見つかったのは、利用者が証明すべき命題を*宣言した*からにほかならない。$\Infer$ だけを走らせるカーネルなら、$t$ を受理し、黙って別の型を割り当てていただろう。どのスクリプトでも `goal` が先頭に来るのはこのためであり、`qed` がそれと照合するのもこのためである。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : P) => P"></div>

<div class="playground" data-file="wrong-proof"><pre>goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : P) => P
qed</pre></div>

<aside class="warning" markdown="1">

項が正しく型付けされていても、主張された定理を証明したことにはならない。$\Infer$ を通る閉じた項には型を推論できるが、カーネルはそれが定理に対して主張された型と一致するかも確かめなければならない。タクティク（[第 10 章](10-tactics.md)）は、項を組み立てる前にその主張を固定するよう設計されている。

</aside>

## 仮定を使う: モーダス・ポネンス

ここまでの例では、関数を一度も適用していない。次の検査を考えよう。

$$
t = \tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{f}{P \to Q}{\tLam{p}{P}{f\;p}}}}
\quad\text{against}\quad
\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{(P \to Q) \to P \to Q}},
$$

この型は「$P$ ならば $Q$ であり、$P$ が成り立つなら、$Q$ が成り立つ」と述べている。四つの $\lambda$ が、これまでと同じように文脈を $\Gamma = P : \Sort{0},\; Q : \Sort{0},\; f : P \to Q,\; p : P$ まで拡張する。本体 $f\;p$ は $\Infer$ の適用のケースに達する。

<ul class="trace">
<li>$\Infer(\Gamma,\; f\;p)$ <span class="rule">T-App</span>
  <ul>
  <li>$\Infer(\Gamma,\; f)$ は $P \to Q$、すなわち $\tPi{\_}{P}{Q}$ を返す。$\Whnf$ はこれを変えず、これは $\Pi$ である <span class="rule">T-Var</span></li>
  <li>$\Check(\Gamma,\; p,\; P)$ は成功する。$p : P$ が $\Gamma$ にあるからである <span class="rule">T-Var, T-Conv</span></li>
  <li class="result">$\subst{Q}{\_}{p} = Q$ を返す。名前 $\_$ は $Q$ に現れないので、代入は何もしない</li>
  </ul>
</li>
</ul>

利用者が代わりに $f\;f$ と書いていたら、二つ目のステップで $\Check(\Gamma, f, P)$ が呼ばれ、$P \to Q$ は $P$ ではないので失敗する。ここでは関数を自分自身に食わせることはできない。下で `f p` を `f f` に変えて試してほしい。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (Q : Sort 0) => fun (f : P -> Q) => fun (p : P) => f p"></div>

<div class="playground" data-file="modus-ponens"><pre>goal forall (P : Sort 0), forall (Q : Sort 0), (P -> Q) -> P -> Q
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (f : P -> Q) => fun (p : P) => f p
qed</pre></div>

## 全称命題の具体化

*依存的な*適用では、T-App の代入が実質的な仕事をする。最初の例の証明を $\mathit{id} = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ とし、$\Gamma = Q : \Sort{0}$ とする。このとき $\Infer(\Gamma, \mathit{id}\;Q)$ は次のようになる。

<ul class="trace">
<li>$\Infer(\Gamma,\; \mathit{id}\;Q)$ <span class="rule">T-App</span>
  <ul>
  <li>$\Infer(\Gamma,\; \mathit{id})$ は $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$ を返す。すでに $\Pi$ である <span class="rule">T-Lam</span></li>
  <li>$\Check(\Gamma,\; Q,\; \Sort{0})$ は成功する <span class="rule">T-Var</span></li>
  <li class="result">$\subst{(\tPi{h}{P}{P})}{P}{Q} = \tPi{h}{Q}{Q}$、すなわち $Q \to Q$ を返す</li>
  </ul>
</li>
</ul>

論理的には、これは $\forall$ 除去である。「どの命題も自分自身を含意する」から「$Q$ は $Q$ を含意する」を得ている。結果の型は引数 $Q$ の*値*に依存する。依存 $\Pi$ 型が表しているのはまさにこのことであり、T-App が代入を行う理由でもある。エクスプローラでは、$\mathit{id}$ は定義された定数で、$Q$ は文脈から来る。T-App ノードの注記に代入が記録される。

<div class="explorer" data-kind="derive" data-term="id Q" data-ctx="Q : Sort 0"><pre class="prelude">def id : forall (P : Sort 0), P -> P := fun (P : Sort 0) => fun (h : P) => h</pre></div>

## 変換

[第 3 章](03-typing-rules.md) の $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$ を思い出そう。核となる体系には定義がないので、$\mathit{Id}\;P$ は項 $(\tLam{X}{\Sort{0}}{X})\;P$ の略記である。次の検査を考える。

$$
t = \tLam{P}{\Sort{0}}{\tLam{h}{\mathit{Id}\;P}{h}}
\quad\text{against}\quad
\tPi{P}{\Sort{0}}{P \to P}.
$$

$\Infer$ はまず、注釈 $\mathit{Id}\;P$ が型であることを確かめる。$\InferSort(\Gamma_1, \mathit{Id}\;P)$ は $\Infer$ の適用のケースに達する。関数 $\tLam{X}{\Sort{0}}{X}$ の型は $\tPi{X}{\Sort{0}}{\Sort{0}}$ で、引数 $P$ は $\Check(\Gamma_1, P, \Sort{0})$ を通り、結果は $\subst{\Sort{0}}{X}{P} = \Sort{0}$ である。したがって $\mathit{Id}\;P$ は型であり、しかも命題である。本体 $h$ の型は $\mathit{Id}\;P$ なので、

$$
\Infer(\cdot, t) \;=\; \tPi{P}{\Sort{0}}{\tPi{h}{\mathit{Id}\;P}{\mathit{Id}\;P}}.
$$

となる。束縛変数を改名するだけでは、これは $\tPi{P}{\Sort{0}}{P \to P}$ にならない。しかし $\IsDefEq$ は比較の前に両辺を計算する。$\mathit{Id}\;P \betared P$ なので、推論された型は $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$ になり、最初の例と同じく比較は成功する。型付け規則で言えば、このステップは導出の根における T-Conv の一回の使用である。

$$
\dfrac{
  \cdot \vdash t : \tPi{P}{\Sort{0}}{\mathit{Id}\;P \to \mathit{Id}\;P}
  \qquad
  \cdot \vdash \tPi{P}{\Sort{0}}{P \to P} : \Sort{0}
  \qquad
  \tPi{P}{\Sort{0}}{\mathit{Id}\;P \to \mathit{Id}\;P} \conv \tPi{P}{\Sort{0}}{P \to P}
}{\cdot \vdash t : \tPi{P}{\Sort{0}}{P \to P}}\rulename{T-Conv}
$$

アルゴリズムは、T-Conv を*どこで*適用するかを決して決めない。[第 5 章](05-algorithm.md) で述べたとおり、変換は $\IsDefEq$ の呼び出しの中に隠れており、二つの型が比較される場所でしか走らない。

ライブの導出を見ると、計算がどこで起きるかが分かる。注釈 $\mathit{Id}\;P$ は T-App で検査され、推論された型には、$\Check$ がゴールと比較するまで $\mathit{Id}\;P$ が残ったままである。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : (fun (X : Sort 0) => X) P) => h"></div>

<div class="playground" data-file="conversion"><pre># h の注釈は (fun (X : Sort 0) => X) P であり、P に計算される。
goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : (fun (X : Sort 0) => X) P) => h
qed</pre></div>

## 演習

上の例のように $\Infer$ を手で走らせてみると、アルゴリズムの理解を確かめるよい練習になる。どれもプレイグラウンドで試せる。

<div class="exercise" markdown="1">

$\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q \to P}}$ を証明せよ。

<details markdown="1">
<summary>解答</summary>

一つの答えは $\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{\tLam{q}{Q}{p}}}}$ である。この証明は $q$ を一度も使わない。体系は、仮定を使わずに済ませることを許している。

</details>

</div>

<div class="exercise" markdown="1">

含意が推移的であることを証明せよ:
$\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{\tPi{R}{\Sort{0}}{(P \to Q) \to (Q \to R) \to P \to R}}}$。

<details markdown="1">
<summary>解答</summary>

一つの答えは $\tLam{f}{P \to Q}{\tLam{g}{Q \to R}{\tLam{p}{P}{g\;(f\;p)}}}$ で終わる。適用のケースを二回使う。まず $f\;p : Q$、次に $g\;(f\;p) : R$ である。

```leanmini
goal forall (P : Sort 0), forall (Q : Sort 0), forall (R : Sort 0), (P -> Q) -> (Q -> R) -> P -> R
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (R : Sort 0) => fun (f : P -> Q) => fun (g : Q -> R) => fun (p : P) => g (f p)
qed
```

</details>

</div>

<div class="exercise" markdown="1">

$\tLam{P}{\Sort{0}}{\tLam{h}{P}{h\;h}}$ が拒否される理由と、アルゴリズム 5.1 のどの行で拒否されるかを説明せよ。

<details markdown="1">
<summary>解答</summary>

文脈 $P : \Sort{0}, h : P$ において、本体 $h\;h$ は適用のケースに達する。$\Infer$ は関数 $h$ に対して $P$ を返すが、$\Whnf(P) = P$ は変数であって $\Pi$ ではない。アルゴリズムは `else fail "not a function"` の行で失敗する。$P$ の証明は適用できるものではない。Rust でのメッセージは `application of non-function` である。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- $\Infer$ の実行は導出木を映す。値を返す各呼び出しが一つのノードである。
- $\Infer$ は、宣言された定理を証明していない項に対しても成功しうる。それを捕まえるのは、宣言された型に対する $\Check$ である。
- T-App は、仮定が使われる場所（モーダス・ポネンス）であり、全称命題が具体化される場所（$\Pi$ の本体への代入）でもある。
- 型の内部の計算はすべて $\IsDefEq$ が扱う。アルゴリズムは T-Conv をどこで適用するかを決して選ばない。

</div>
