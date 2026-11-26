<div class="lead" markdown="1">

この章では、アルゴリズム 5.1 の再帰呼び出しを具体的な項で追いかけます。取り上げるのは、正しい導出、誤った証明の拒否、仮定の利用、全称命題の具体化、型の内部での計算の五つです。どのトレースもプレイグラウンドで再現できます。

</div>

定理 $T$ の証明 $t$ を検証するとき、カーネルは $\Check(\cdot, t, T)$ を呼びます。その中で $\Infer(\cdot, t)$ を呼び、得られた型を $T$ と比較します。以下のトレースには、$\Infer$ の再帰呼び出しと、それぞれに対応する型付け規則を示しました。ノードを開閉しながら再帰の流れを追ってください。

## 恒等関数による証明

$\Gamma_1 = P : \Sort{0}$、$\Gamma_2 = \Gamma_1, h : P$ とおきます。[第 1 章](01-propositions-as-types.md) の冒頭の例の導出は、整形式性の前提を省くと次のようになります。

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

アルゴリズムはこの導出を下から上へ組み立てます。呼び出し $\Infer(\cdot, \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}})$ は次のように進みます。

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

型を返す呼び出しはそれぞれ導出木の一つのノードに対応し、計算を必要とする呼び出しは一つもありません。最後に $\Check$ が、結果を宣言された型 $\tPi{P}{\Sort{0}}{P \to P}$ と比較します。$P \to P$ は $\tPi{\_}{P}{P}$ の略記で、$h$ も $\_$ も本体には現れないので、両者の違いは束縛変数の名前一つだけです。したがって $\IsDefEq$ は成功し、証明は受理されます。

次のエクスプローラは、同じ実行をカーネル自身に記録させたものです。呼び出しビューは上のリストと、証明木ビューは導出と一致します。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : P) => h"></div>

<div class="playground" data-file="examples/identity.leanmini"><pre># 同じ証明を、完全な項として与える。カーネルはその型を推論し、
# ゴールと比較する。
goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : P) => h
qed</pre></div>

## 誤った証明の拒否

利用者が、$t = \tLam{P}{\Sort{0}}{\tLam{h}{P}{P}}$ は $\tPi{P}{\Sort{0}}{P \to P}$ の証明だと主張したとしましょう。この項の本体は、証明 $h$ ではなく命題 $P$ を返しています。カーネルは $\Check(\cdot, t, \tPi{P}{\Sort{0}}{P \to P})$ を呼び、まず $\Infer$ が走ります。呼び出しの流れは上と同じで、最後の $\Infer(\Gamma_2, P)$ だけが $\Sort{0}$ を返します。つまり $\Infer$ は*成功し*、結果は

$$
\Infer(\cdot, t) \;=\; \tPi{P}{\Sort{0}}{\tPi{h}{P}{\Sort{0}}}.
$$

となります。項 $t$ には正しく型が付きますが、主張された命題の証明にはなっていません。$\Check$ が二つの型を比較すると、どちらもこれ以上計算できず、いちばん内側の本体が片方は $\Sort{0}$、もう片方は $P$ なので、束縛変数を改名しても一致しません。そのため $\IsDefEq$ は失敗し、$\Check$ は型の不一致を報告します。（[第 11 章](11-substitution-alpha.md#alpha-equivalence) では、$\IsDefEq$ が使うアルゴリズムでこの比較を一歩ずつ再現します。）

この誤りを見つけられたのは、利用者が証明すべき命題を*宣言した*からです。$\Infer$ しか走らせないカーネルなら、$t$ を受理し、黙って別の型を割り当てていたでしょう。どのスクリプトも `goal` で始まり、`qed` がそれと照合するのはこのためです。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : P) => P"></div>

<div class="playground" data-file="wrong-proof"><pre>goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : P) => P
qed</pre></div>

<aside class="warning" markdown="1">

項に正しく型が付いても、それだけでは主張された定理を証明したことになりません。$\Infer$ を通る閉じた項には型が推論できますが、カーネルはその型が定理として主張された型と一致するかどうかも確かめる必要があります。タクティク（[第 10 章](10-tactics.md)）は、項を組み立てる前に主張を固定するように設計されています。

</aside>

## 仮定を使う: モーダス・ポネンス

ここまでの例では関数を一度も適用していません。そこで次の検査を考えましょう。

$$
t = \tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{f}{P \to Q}{\tLam{p}{P}{f\;p}}}}
\quad\text{against}\quad
\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{(P \to Q) \to P \to Q}},
$$

この型は「$P$ ならば $Q$ であり、かつ $P$ が成り立つなら、$Q$ が成り立つ」と述べています。四つの $\lambda$ がこれまでと同じように文脈を $\Gamma = P : \Sort{0},\; Q : \Sort{0},\; f : P \to Q,\; p : P$ まで広げ、本体 $f\;p$ で $\Infer$ は適用のケースに入ります。

<ul class="trace">
<li>$\Infer(\Gamma,\; f\;p)$ <span class="rule">T-App</span>
  <ul>
  <li>$\Infer(\Gamma,\; f)$ は $P \to Q$、すなわち $\tPi{\_}{P}{Q}$ を返す。$\Whnf$ を通しても変わらず、すでに $\Pi$ の形 <span class="rule">T-Var</span></li>
  <li>$\Check(\Gamma,\; p,\; P)$ は成功する。$p : P$ が $\Gamma$ にあるため <span class="rule">T-Var, T-Conv</span></li>
  <li class="result">$\subst{Q}{\_}{p} = Q$ を返す。名前 $\_$ は $Q$ に現れないので、代入しても何も変わらない</li>
  </ul>
</li>
</ul>

代わりに $f\;f$ と書いていたら、二つ目のステップで $\Check(\Gamma, f, P)$ が呼ばれ、$P \to Q$ は $P$ ではないので失敗します。この体系では、関数を自分自身に渡せません。下で `f p` を `f f` に書き換えて試してください。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (Q : Sort 0) => fun (f : P -> Q) => fun (p : P) => f p"></div>

<div class="playground" data-file="modus-ponens"><pre>goal forall (P : Sort 0), forall (Q : Sort 0), (P -> Q) -> P -> Q
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (f : P -> Q) => fun (p : P) => f p
qed</pre></div>

## 全称命題の具体化

*依存的な*適用では、T-App の代入が本当に働きます。最初の例の証明を $\mathit{id} = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ とし、$\Gamma = Q : \Sort{0}$ とします。このとき $\Infer(\Gamma, \mathit{id}\;Q)$ は次のように進みます。

<ul class="trace">
<li>$\Infer(\Gamma,\; \mathit{id}\;Q)$ <span class="rule">T-App</span>
  <ul>
  <li>$\Infer(\Gamma,\; \mathit{id})$ は $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$ を返す。すでに $\Pi$ の形 <span class="rule">T-Lam</span></li>
  <li>$\Check(\Gamma,\; Q,\; \Sort{0})$ は成功する <span class="rule">T-Var</span></li>
  <li class="result">$\subst{(\tPi{h}{P}{P})}{P}{Q} = \tPi{h}{Q}{Q}$、すなわち $Q \to Q$ を返す</li>
  </ul>
</li>
</ul>

論理的には、これは $\forall$ 除去です。「どの命題も自分自身を含意する」から「$Q$ は $Q$ を含意する」を導いています。結果の型が引数 $Q$ の*値*に依存することこそ依存 $\Pi$ 型が表すものであり、T-App が代入を行う理由でもあります。エクスプローラでは $\mathit{id}$ を定義済みの定数として扱い、$Q$ は文脈から取ります。代入の内容は T-App ノードの注記に表示されます。

<div class="explorer" data-kind="derive" data-term="id Q" data-ctx="Q : Sort 0"><pre class="prelude">def id : forall (P : Sort 0), P -> P := fun (P : Sort 0) => fun (h : P) => h</pre></div>

## 型の中での計算（変換）

[第 3 章](03-typing-rules.md) の $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$ を思い出してください。核となる体系には定義がないので、$\mathit{Id}\;P$ は項 $(\tLam{X}{\Sort{0}}{X})\;P$ の略記です。次の検査を考えます。

$$
t = \tLam{P}{\Sort{0}}{\tLam{h}{\mathit{Id}\;P}{h}}
\quad\text{against}\quad
\tPi{P}{\Sort{0}}{P \to P}.
$$

$\Infer$ はまず、注釈 $\mathit{Id}\;P$ が型であることを確かめます。このとき $\InferSort(\Gamma_1, \mathit{Id}\;P)$ は $\Infer$ の適用のケースに入ります。関数 $\tLam{X}{\Sort{0}}{X}$ の型は $\tPi{X}{\Sort{0}}{\Sort{0}}$ で、引数 $P$ は $\Check(\Gamma_1, P, \Sort{0})$ を通過し、結果は $\subst{\Sort{0}}{X}{P} = \Sort{0}$ です。したがって $\mathit{Id}\;P$ は型であり、しかも命題です。本体 $h$ の型は $\mathit{Id}\;P$ なので、

$$
\Infer(\cdot, t) \;=\; \tPi{P}{\Sort{0}}{\tPi{h}{\mathit{Id}\;P}{\mathit{Id}\;P}}.
$$

となります。束縛変数を改名するだけでは $\tPi{P}{\Sort{0}}{P \to P}$ と一致しませんが、$\IsDefEq$ は比較の前に両辺を計算します。$\mathit{Id}\;P \betared P$ なので、推論された型は $\tPi{P}{\Sort{0}}{\tPi{h}{P}{P}}$ になり、最初の例と同じく比較は成功します。型付け規則の言葉で言えば、このステップは導出の根で T-Conv を一回使ったことにあたります。

$$
\dfrac{
  \cdot \vdash t : \tPi{P}{\Sort{0}}{\mathit{Id}\;P \to \mathit{Id}\;P}
  \qquad
  \cdot \vdash \tPi{P}{\Sort{0}}{P \to P} : \Sort{0}
  \qquad
  \tPi{P}{\Sort{0}}{\mathit{Id}\;P \to \mathit{Id}\;P} \conv \tPi{P}{\Sort{0}}{P \to P}
}{\cdot \vdash t : \tPi{P}{\Sort{0}}{P \to P}}\rulename{T-Conv}
$$

アルゴリズムが T-Conv を*どこで*使うかを自分で決めることはありません。[第 5 章](05-algorithm.md) で述べたとおり、変換は $\IsDefEq$ の呼び出しの中に隠れていて、二つの型を比較する場所でしか走りません。

ライブの導出を見ると、計算がどこで起きるかが分かります。注釈 $\mathit{Id}\;P$ は T-App で検査され、推論された型の中では、$\Check$ がゴールと比較するまで $\mathit{Id}\;P$ がそのまま残ります。

<div class="explorer" data-kind="derive" data-term="fun (P : Sort 0) => fun (h : (fun (X : Sort 0) => X) P) => h"></div>

<div class="playground" data-file="conversion"><pre># h の注釈は (fun (X : Sort 0) => X) P であり、P に計算される。
goal forall (P : Sort 0), P -> P
exact fun (P : Sort 0) => fun (h : (fun (X : Sort 0) => X) P) => h
qed</pre></div>

## 演習

上の例のように $\Infer$ を手で走らせると、アルゴリズムを理解できているかを確かめるよい練習になります。どの演習もプレイグラウンドで試せます。

<div class="exercise" markdown="1">

$\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q \to P}}$ を証明してください。

<details markdown="1">
<summary>解答</summary>

答えの一つは $\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{\tLam{q}{Q}{p}}}}$ です。この証明は $q$ を一度も使いませんが、仮定を使わずに済ませることは体系上まったく問題ありません。

</details>

</div>

<div class="exercise" markdown="1">

含意が推移的であることを証明してください:
$\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{\tPi{R}{\Sort{0}}{(P \to Q) \to (Q \to R) \to P \to R}}}$。

<details markdown="1">
<summary>解答</summary>

答えの一つは $\tLam{f}{P \to Q}{\tLam{g}{Q \to R}{\tLam{p}{P}{g\;(f\;p)}}}$ で終わる項で、適用のケースを二回使います。まず $f\;p : Q$、次に $g\;(f\;p) : R$ です。

```leanmini
goal forall (P : Sort 0), forall (Q : Sort 0), forall (R : Sort 0), (P -> Q) -> (Q -> R) -> P -> R
exact fun (P : Sort 0) => fun (Q : Sort 0) => fun (R : Sort 0) => fun (f : P -> Q) => fun (g : Q -> R) => fun (p : P) => g (f p)
qed
```

</details>

</div>

<div class="exercise" markdown="1">

$\tLam{P}{\Sort{0}}{\tLam{h}{P}{h\;h}}$ が拒否される理由と、アルゴリズム 5.1 のどの行で拒否されるかを説明してください。

<details markdown="1">
<summary>解答</summary>

文脈 $P : \Sort{0}, h : P$ のもとで、本体 $h\;h$ は適用のケースに入ります。$\Infer$ は関数 $h$ に対して $P$ を返しますが、$\Whnf(P) = P$ は変数であって $\Pi$ ではないので、アルゴリズムは `else fail "not a function"` の行で失敗します。$P$ の証明は適用できるものではないからです。Rust 版のエラーメッセージは `application of non-function` です。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- $\Infer$ の実行は導出木をなぞり、値を返す呼び出しの一つひとつがノードになります。
- $\Infer$ は、宣言された定理を証明していない項に対しても成功することがあります。それを捕まえるのは、宣言された型に対する $\Check$ です。
- T-App は、仮定が使われる場所（モーダス・ポネンス）であり、全称命題が具体化される場所（$\Pi$ の本体への代入）でもあります。
- 型の内部の計算はすべて $\IsDefEq$ が引き受けるので、アルゴリズムが T-Conv を使う場所を選ぶことはありません。

</div>
