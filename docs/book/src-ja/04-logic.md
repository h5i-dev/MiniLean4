<div class="lead" markdown="1">

第 3 章の型付け規則は、本当に論理の規則として働くのでしょうか。この章では、二階命題論理の論理式を型に、導出を項に翻訳して確かめます。ただし、どんな命題でも証明できてしまう体系では検査に意味がないので、整合性も必要になります。

</div>

## 比較対象となる論理

この論理の論理式は、命題変数 $P, Q, \ldots$ から、含意と命題についての量化によって作られます。

$$
\varphi, \psi \;::=\; P \;\mid\; \varphi \to \psi \;\mid\; \forall P.\,\varphi
$$

これは**二階命題論理**（second-order propositional logic）と呼ばれる論理です。「二階」と呼ぶのは、$\forall$ が個体ではなく命題を動くからです。小さな論理ですが決して自明ではなく、連言、選言、否定、矛盾はすべてこの中で定義できます。たとえば $\bot = \forall P.\,P$、$\varphi \wedge \psi = \forall R.\,(\varphi \to \psi \to R) \to R$ と定義します。

この論理の証明は、判断 $\Delta \vdash \varphi$ を自然演繹で導出したもので、$\Delta$ は仮定のリストです。規則は下の図 4.1 の左列にあるもの、すなわち仮定の使用、含意の導入と除去、量化子の導入と除去です。

## 論理式を型へ翻訳する

各論理式を型に翻訳したものを $\varphi^\ast$ と書きます。

$$
P^\ast = P,
\qquad
(\varphi \to \psi)^\ast = \varphi^\ast \to \psi^\ast,
\qquad
(\forall P.\,\varphi)^\ast = \tPi{P}{\Sort{0}}{\varphi^\ast}.
$$

命題変数は型変数に、含意は関数型に、命題についての量化は $\Sort{0}$ 上の $\Pi$ 型に移ります。

仮定のリストは文脈に翻訳します。ただし文脈には、仮定ごとの $h_i : \varphi_i^\ast$ に加えて、判断のどこかに現れる命題変数の宣言も必要です。

$$
(\varphi_1, \ldots, \varphi_n)^\ast
\;=\;
P_1 : \Sort{0}, \ldots, P_k : \Sort{0},\;
h_1 : \varphi_1^\ast, \ldots, h_n : \varphi_n^\ast,
$$

ここで $P_1, \ldots, P_k$ は、翻訳する判断 $\Delta \vdash \varphi$ の $\Delta$ または結論 $\varphi$ に自由に現れる命題変数で、$h_1, \ldots, h_n$ は新鮮な名前です。結論に現れる変数まで含めるのは、$\cdot \vdash P \to P$ の $P$ のように、結論にしか現れない変数があるからです。

図 4.1 では、各論理規則の隣に、それを実装する型付け規則を並べました。型が整形式であることを確かめるだけの前提は省いています。

<div class="rulebox" markdown="1">

<p class="caption">図 4.1. 自然演繹（中央列）とそれを実装する型付け規則（右列）。各行で $\Delta^\ast$ は結論に対する文脈です。</p>

$$
\begin{array}{lcc}
\text{Hypothesis} &
\dfrac{\varphi_i \in \Delta}{\Delta \vdash \varphi_i} &
\dfrac{(h_i : \varphi_i^\ast) \in \Delta^\ast}{\Delta^\ast \vdash h_i : \varphi_i^\ast}\rulename{T-Var}
\\[18pt]
\to\text{-intro} &
\dfrac{\Delta, \varphi \vdash \psi}{\Delta \vdash \varphi \to \psi} &
\dfrac{\Delta^\ast, h : \varphi^\ast \vdash t : \psi^\ast}{\Delta^\ast \vdash \tLam{h}{\varphi^\ast}{t} : \varphi^\ast \to \psi^\ast}\rulename{T-Lam}
\\[18pt]
\to\text{-elim} &
\dfrac{\Delta \vdash \varphi \to \psi \qquad \Delta \vdash \varphi}{\Delta \vdash \psi} &
\dfrac{\Delta^\ast \vdash f : \varphi^\ast \to \psi^\ast \qquad \Delta^\ast \vdash a : \varphi^\ast}{\Delta^\ast \vdash f\;a : \psi^\ast}\rulename{T-App}
\\[18pt]
\forall\text{-intro} &
\dfrac{\Delta \vdash \varphi \qquad P \notin \FV(\Delta)}{\Delta \vdash \forall P.\,\varphi} &
\dfrac{\Delta^\ast, P : \Sort{0} \vdash t : \varphi^\ast}{\Delta^\ast \vdash \tLam{P}{\Sort{0}}{t} : \tPi{P}{\Sort{0}}{\varphi^\ast}}\rulename{T-Lam}
\\[18pt]
\forall\text{-elim} &
\dfrac{\Delta \vdash \forall P.\,\varphi}{\Delta \vdash \subst{\varphi}{P}{\psi}} &
\dfrac{\Delta^\ast \vdash f : \tPi{P}{\Sort{0}}{\varphi^\ast} \qquad \Delta^\ast \vdash \psi^\ast : \Sort{0}}{\Delta^\ast \vdash f\;\psi^\ast : \subst{\varphi^\ast}{P}{\psi^\ast}}\rulename{T-App}
\end{array}
$$

</div>

右列から項を消すと、ちょうど中央列になります。細かい点を二つ補足しておきます。

$\forall$-intro の行では、論理側の側条件 $P \notin \FV(\Delta)$ により、どの仮定も $P$ に言及しないことが保証されます。そのため型付け規則は、文脈の依存順序を壊さずに、仮定の*後に* $P : \Sort{0}$ を加えられます。

$\forall$-elim の行では、T-Pi によって翻訳後の論理式はどれも $\Sort{0}$ に入るので、前提 $\psi^\ast : \Sort{0}$ は、$\forall$ を含むものも含めて*すべての*論理式 $\psi$ について成り立ちます。（理由は T-Pi の $\imax$ にあり、$\tPi{P}{\Sort{0}}{\varphi^\ast}$ は $\Sort{\imax(1, 0)} = \Sort{0}$ に落ち着きます。）したがって全称命題は、論理の場合と同じく、任意の論理式で具体化できます。この性質は非述語性（impredicativity）と呼ばれ、[第 13 章](13-universes.md)で再び取り上げます。

## 証明は項である

<div class="theorem" markdown="1">

**定理 4.1（証明は項である）。** $\Delta \vdash \varphi$ が論理で証明可能なら、ある項 $t$ について $\Delta^\ast \vdash t : \varphi^\ast$ が成り立ちます。

</div>

図 4.1 は論理の証明の各ステップを型付け導出のステップに置き換えるので、証明に関する帰納法により、どの証明も項になります。[付録 A](a-proof-pat.md)では、命題変数のスコープを明示した形で定理を述べ、完全な証明を与えます。

この定理は、型検査器が論理のすべての証明を検査できることを述べています。しかしカーネルを*信頼する*には逆向きの保証も必要で、論理が反駁する命題の項を受理してはなりません。

## 整合性

$\bot = \forall P.\,P$、すなわち「すべてが成り立つ」と定義します。論理には $\bot$ の証明がありません。各命題変数を真か偽のどちらかと読むと、どの読み方でもすべての規則は真を保ちますが、$\forall P.\,P$ は $P$ を偽とする読み方のもとで偽になるからです。

型理論もこれに合わせるべきで、次の型を持つ閉じた項があってはなりません。

$$
\bot^\ast \;=\; \tPi{P}{\Sort{0}}{P}.
$$

この型の閉じた項 $t$ があれば大惨事です。すべての命題 $C : \Sort{0}$ について適用 $t\;C$ が型 $C$ を持ち、あらゆる命題が証明できてしまうので、カーネルは役に立たなくなります。

<div class="definition" markdown="1">

**定義 4.2（整合性）。** 型システムが*整合的*（consistent）であるとは、型 $\tPi{P}{\Sort{0}}{P}$ を持つ閉じた項が存在しないことをいいます。

</div>

整合性は、本書のあらゆる設計判断が守らなければならない性質です。とくに宇宙の設計は、システムの整合性を保てる場合にしか採用できません。[第 13 章](13-universes.md)ではこの試験に落ちる一見自然な設計を示し、[第 14 章](14-properties.md)では本書のシステムの整合性を定理 14.5 として述べます。

<aside class="note" markdown="1">

定理 4.1 の完全な逆、つまり型 $\varphi^\ast$ の項はどれも $\varphi$ の証明から来る、という性質も期待したくなるかもしれません。この強い性質は*保存性*（conservativity）と呼ばれ、ここで確立するのは困難です。$\Sort{0}$ には $\tPi{F}{\Sort{0} \to \Sort{0}}{F\;P \to F\;P}$ のように論理式の翻訳ではない型も含まれていて、項が $\varphi^\ast$ に至る途中でそれらを経由することがあるからです。とはいえ、保存性は必要ありません。整合性がなければカーネルの「はい」には何の意味もありませんが、整合性さえあれば、その「はい」で十分です。

</aside>

<aside class="intuition" markdown="1">

なぜ、たとえば $0 = 1$ ではなく $\tPi{P}{\Sort{0}}{P}$ を特別扱いするのでしょうか。この型は万能の偽造品で、その証明は一回の適用でほかのどんな命題の証明にも変えられるからです。また、別の不合理な主張に証明があれば、そこから $\tPi{P}{\Sort{0}}{P}$ の証明も組み立てられます。つまり、この一つの型を排除すれば、すべてを排除したことになります。

</aside>

## 演習

<div class="exercise" markdown="1">

論理式 $\forall P.\,\forall Q.\,(P \to Q) \to P \to Q$ を型に翻訳し、自然演繹の証明「$P \to Q$ と $P$ を仮定し、前者を後者に適用する」から図 4.1 が生み出す証明項を書いてください。

<details markdown="1">
<summary>解答</summary>

型は $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{(P \to Q) \to P \to Q}}$ です。二回の $\forall$-intro が $\Sort{0}$ 上の外側の $\lambda$ を二つ、二回の $\to$-intro が $\lambda(f : P \to Q)$ と $\lambda(p : P)$ を与え、$\to$-elim が本体 $f\;p$ を与えます。
$\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{f}{P \to Q}{\tLam{p}{P}{f\;p}}}}$。

</details>

</div>

<div class="exercise" markdown="1">

$t : \tPi{P}{\Sort{0}}{P}$ があれば、型 $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q}}$、つまり「すべての命題はほかのすべての命題を含意する」の項を組み立てられることを示してください。

<details markdown="1">
<summary>解答</summary>

$\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{t\;Q}}}$ です。仮定 $p$ は使わず、T-App により $t\;Q : Q$ となります。$\bot^\ast$ の証明があらゆるものを証明するというのは、この意味です。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 二階命題論理は型理論に翻訳できます。$\to$ は関数型に、$\forall P$ は $\Pi(P : \Sort{0})$ に、仮定は文脈の項目になります。
- 定理 4.1: 論理のすべての証明は、型の付く項になります。翻訳は規則ごとに対応しています（図 4.1）。
- カーネルを信頼できるのは、システムが整合的な場合、つまり型 $\tPi{P}{\Sort{0}}{P}$ の閉じた項が存在しない場合だけです。
- 全称命題を任意の論理式で、それ自身でさえ具体化できるのは、$\imax$ による非述語性のおかげです。

</div>
