<div class="lead" markdown="1">

第 3 章の型付け規則は、本当に論理の規則として働くのか。二階命題論理の論理式を型に、導出を項に翻訳して確かめる。ただし、どんな命題も証明できる体系では検査に意味がないため、整合性も必要になる。

</div>

## 比較対象となる論理

この論理の論理式は、命題変数 $P, Q, \ldots$ から含意と命題の上の量化によって作られる。

$$
\varphi, \psi \;::=\; P \;\mid\; \varphi \to \psi \;\mid\; \forall P.\,\varphi
$$

これは**二階命題論理**（second-order propositional logic）であり、「二階」というのは $\forall$ が個体ではなく命題の上を動くからである。小さいが決して自明ではなく、連言、選言、否定、矛盾はすべてこの中で定義できる。たとえば $\bot = \forall P.\,P$ や $\varphi \wedge \psi = \forall R.\,(\varphi \to \psi \to R) \to R$ である。

この論理の証明は、判断 $\Delta \vdash \varphi$ の自然演繹による導出であり、ここで $\Delta$ は仮定のリストである。規則は下の図 4.1 の左列にあるもの、すなわち仮定を使う、含意の導入と除去、量化子の導入と除去である。

## 論理式を型へ翻訳する

各論理式は型へ翻訳され、それを $\varphi^\ast$ と書く。

$$
P^\ast = P,
\qquad
(\varphi \to \psi)^\ast = \varphi^\ast \to \psi^\ast,
\qquad
(\forall P.\,\varphi)^\ast = \tPi{P}{\Sort{0}}{\varphi^\ast}.
$$

命題変数は型変数に、含意は関数型に、命題の上の量化は $\Sort{0}$ の上の $\Pi$ 型になる。

仮定のリストは文脈へ翻訳されるが、仮定ごとの仮定 $h_i : \varphi_i^\ast$ に加えて、文脈は判断のどこかに現れる命題変数を宣言しなければならない。

$$
(\varphi_1, \ldots, \varphi_n)^\ast
\;=\;
P_1 : \Sort{0}, \ldots, P_k : \Sort{0},\;
h_1 : \varphi_1^\ast, \ldots, h_n : \varphi_n^\ast,
$$

ここで $P_1, \ldots, P_k$ は、翻訳する判断 $\Delta \vdash \varphi$ の $\Delta$ または結論 $\varphi$ に自由に現れる命題変数であり、$h_1, \ldots, h_n$ は新鮮な名前である。結論を含めなければならないのは、$\cdot \vdash P \to P$ における $P$ のように、変数が結論だけに現れることがあるからである。

図 4.1 では、各論理規則の隣に、それを実装する型付け規則を並べるが、型が整形式であることを確かめるだけの前提は省いてある。

<div class="rulebox" markdown="1">

<p class="caption">図 4.1. 自然演繹（中央列）とそれを実装する型付け規則（右列）。各行で $\Delta^\ast$ は結論に対する文脈である。</p>

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

右列から項を消すと、ちょうど中央列になる。二つの細部に注釈が要る。

$\forall$-intro の行では、論理側の側条件 $P \notin \FV(\Delta)$ が、どの仮定も $P$ に言及しないことを保証するので、型付け規則は、文脈の依存順序を壊すことなく、仮定の*後に* $P : \Sort{0}$ を加えてよい。

$\forall$-elim の行では、T-Pi が翻訳されたどの論理式も $\Sort{0}$ に置くので、前提 $\psi^\ast : \Sort{0}$ は、$\forall$ を含むものも含めて*すべての*論理式 $\psi$ について成り立つ。（T-Pi の $\imax$ がその理由であり、$\tPi{P}{\Sort{0}}{\varphi^\ast}$ は $\Sort{\imax(1, 0)} = \Sort{0}$ に落ち着く。）したがって全称命題は、論理の場合と同じく任意の論理式で具体化できる。この点は非述語性（impredicativity）と呼ばれ、[第 13 章](13-universes.md)で再び取り上げる。

## 証明は項である

<div class="theorem" markdown="1">

**定理 4.1（証明は項である）。** $\Delta \vdash \varphi$ が論理で証明可能なら、ある項 $t$ について $\Delta^\ast \vdash t : \varphi^\ast$ が成り立つ。

</div>

図 4.1 は論理の証明の各ステップを型付け導出のステップに変えるので、証明に関する帰納法により、すべての証明が項になる。[付録 A](a-proof-pat.md)では命題変数のスコープを明示した形で定理を述べ、完全な証明を与える。

この定理は型検査器が論理のすべての証明を検査できると言っているが、カーネルが*信頼に値する*ためには逆向きの保証も要り、論理が反駁する命題に対する項を受理してはならない。

## 整合性

$\bot = \forall P.\,P$、「すべてが成り立つ」と定義する。論理には $\bot$ の証明が存在しない。各命題変数を真か偽と読むと、どの読み方のもとでもすべての規則は真を保つが、$\forall P.\,P$ はある $P$ を偽にする読み方のもとで偽になるからである。

型理論もこれに合致すべきで、次の型を持つ閉じた項があってはならない。

$$
\bot^\ast \;=\; \tPi{P}{\Sort{0}}{P}.
$$

この型の閉じた項 $t$ があれば大惨事で、すべての命題 $C : \Sort{0}$ について適用 $t\;C$ が型 $C$ を持つことになり、あらゆる命題が証明可能になって、カーネルは無価値になる。

<div class="definition" markdown="1">

**定義 4.2（整合性）。** 型システムが*整合的*（consistent）であるとは、型 $\tPi{P}{\Sort{0}}{P}$ を持つ閉じた項が存在しないことをいう。

</div>

整合性は、本書のあらゆる設計判断が保たなければならない性質である。とくに宇宙の設計は、システムが整合的であり続ける場合にのみ受け入れられる。[第 13 章](13-universes.md)ではこの試験に落ちる、一見自然な設計を示し、[第 14 章](14-properties.md)では本書のシステムの整合性を定理 14.5 として述べる。

<aside class="note" markdown="1">

定理 4.1 の完全な逆、すなわち型 $\varphi^\ast$ のすべての項が $\varphi$ の証明から来ることを期待したくなるかもしれない。この強い性質は*保存性*（conservativity）と呼ばれ、ここで確立するのは難しい。$\Sort{0}$ には $\tPi{F}{\Sort{0} \to \Sort{0}}{F\;P \to F\;P}$ のように論理式の翻訳ではない型も含まれており、項が $\varphi^\ast$ に至る途中でそれらを経由することがあるからである。保存性は必要なく、整合性がなければカーネルの「はい」は何も意味しないが、整合性があればその「はい」で十分である。

</aside>

<aside class="intuition" markdown="1">

なぜ、たとえば $0 = 1$ ではなく $\tPi{P}{\Sort{0}}{P}$ を特別扱いするのか。それが万能の偽造品であり、その証明は一回の適用で他のどんなものの証明にも変えられるからである。もし別の不合理な主張に証明があれば、その証明から $\tPi{P}{\Sort{0}}{P}$ の証明も組み立てられるので、この一つの型を排除すればすべてを排除したことになる。

</aside>

## 演習

<div class="exercise" markdown="1">

論理式 $\forall P.\,\forall Q.\,(P \to Q) \to P \to Q$ を型へ翻訳し、自然演繹の証明「$P \to Q$ と $P$ を仮定し、前者を後者に適用する」に対して図 4.1 が生む証明項を書け。

<details markdown="1">
<summary>解答</summary>

型は $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{(P \to Q) \to P \to Q}}$ である。二回の $\forall$-intro が $\Sort{0}$ 上の外側の $\lambda$ を二つ、二回の $\to$-intro が $\lambda(f : P \to Q)$ と $\lambda(p : P)$ を与え、$\to$-elim が本体 $f\;p$ を与える。
$\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{f}{P \to Q}{\tLam{p}{P}{f\;p}}}}$。

</details>

</div>

<div class="exercise" markdown="1">

$t : \tPi{P}{\Sort{0}}{P}$ から、型 $\tPi{P}{\Sort{0}}{\tPi{Q}{\Sort{0}}{P \to Q}}$、「すべての命題は他のすべての命題を含意する」の項を組み立てられることを示せ。

<details markdown="1">
<summary>解答</summary>

$\tLam{P}{\Sort{0}}{\tLam{Q}{\Sort{0}}{\tLam{p}{P}{t\;Q}}}$ である。仮定 $p$ は無視され、T-App により $t\;Q : Q$ である。$\bot^\ast$ の証明があらゆるものを証明するというのは、この意味においてである。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 二階命題論理は型理論へ翻訳される。$\to$ は関数型に、$\forall P$ は $\Pi(P : \Sort{0})$ に、仮定は文脈の項目になる。
- 定理 4.1: 論理のすべての証明は、型の付く項になる。翻訳は規則ごとに対応する（図 4.1）。
- カーネルが信頼に値するのは整合的である場合、つまり型 $\tPi{P}{\Sort{0}}{P}$ の閉じた項が存在しない場合だけである。
- 全称命題を任意の論理式で、それ自身によってさえ、具体化できるのは $\imax$ による非述語性のおかげである。

</div>
