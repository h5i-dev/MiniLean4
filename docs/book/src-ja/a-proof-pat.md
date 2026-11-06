<div class="lead" markdown="1">

[第 4 章](04-logic.md)では、二階命題論理のあらゆる証明が、カーネルの受理する項に変換できると主張した（定理 4.1）。本付録ではその主張を精密に述べ、完全に証明する。変数と仮定の扱いを明確にすれば、証明は短い。論理の判断の導出に関する帰納法であり、各ケースは第 4 章の表の一行を左から右へ読んだものにあたる。

</div>

## 考え方

論理における導出は、規則適用の木である。第 4 章の変換は、各論理規則を一つの型付け規則と対にした。したがって自然な方針は、導出を葉から上へたどり、各節点で、対になる型付け規則が与える型付け導出を組み立てることである。仮定は変数の参照になり、含意の導入は $\lambda$ に、含意の除去は適用になる。二つの量化子規則は、$\Sort{0}$ 上の $\lambda$ と、型への適用になる。

注意を要する細部が二つあり、どちらも文脈に関わる。

- 論理の規則は、どの命題変数がスコープ内にあるかを述べない。型付けの側はそれを知る必要がある。命題変数 $P$ は、仮定 $P : \Sort{0}$ が文脈に入ってはじめて使えるからである。そこで精密な主張は、命題変数の明示的なリスト $\Theta$ を携える。
- 型付け規則は文脈を右側に拡張するが、第 4 章の変換 $\Delta^\ast$ は、すべての命題変数をすべての仮定の前に置く。任意の並び順を許したほうが証明は楽なので、以下で定義する意味で論理の判断を*表現する*あらゆる文脈について定理を証明する。

## 精密な主張

定理 4.1 では、どの命題変数がスコープ内にあるかが暗黙になっていた。証明のためにこれを明示し、

$$
\Theta; \Delta \vdash \varphi,
$$

と書く。ここで $\Theta$ は相異なる命題変数のリストであり、$\Delta$ または $\varphi$ に自由に現れる命題変数はすべて $\Theta$ に属する。命題変数を明示すると、第 4 章の規則は次のようになる。

$$
\dfrac{\varphi \in \Delta}{\Theta; \Delta \vdash \varphi}\rulename{Hyp}
\qquad
\dfrac{\Theta; \Delta, \varphi \vdash \psi}{\Theta; \Delta \vdash \varphi \to \psi}\rulename{$\to$-intro}
\qquad
\dfrac{\Theta; \Delta \vdash \varphi \to \psi \qquad \Theta; \Delta \vdash \varphi}{\Theta; \Delta \vdash \psi}\rulename{$\to$-elim}
$$

$$
\dfrac{\Theta, P; \Delta \vdash \varphi \qquad P \notin \Theta}{\Theta; \Delta \vdash \forall P.\,\varphi}\rulename{$\forall$-intro}
\qquad
\dfrac{\Theta; \Delta \vdash \forall P.\,\varphi \qquad \FV(\psi) \subseteq \Theta}{\Theta; \Delta \vdash \subst{\varphi}{P}{\psi}}\rulename{$\forall$-elim}
$$

第 4 章の側条件 $P \notin \FV(\Delta)$ は、いまや $P \notin \Theta$ から従う。$\Delta$ に自由に現れる命題変数はすべて $\Theta$ にあり、$P$ はそこにないからである。論理式は $\alpha$ 同値を除いて扱うので、束縛された $P$ はつねに側条件を満たすように改名できる。第 4 章と同じく、$\varphi^\ast \to \psi^\ast$ は、$x$ を新鮮な変数として $\tPi{x}{\varphi^\ast}{\psi^\ast}$ を表す。

第 4 章の文脈 $\Delta^\ast$ は、命題変数を先に並べ、仮定をその後に並べる。証明では文脈を右側に拡張する必要があるので、任意の順序を許すのが都合がよい。

<div class="definition" markdown="1">

**定義 A.1（表現）.** 文脈 $\Gamma$ が $(\Theta; \Delta)$ を*表現する*とは、$\ctxok{\Gamma}$ であり、$\Gamma$ が各 $P \in \Theta$ に対する仮定 $P : \Sort{0}$ を一つずつと、各 $\chi \in \Delta$ に対する仮定 $h : \chi^\ast$ を一つずつ、何らかの順序で並べたものからなることをいう。

</div>

<div class="theorem" markdown="1">

**定理 A.2（定理 4.1 の精密な形）.** $\Theta; \Delta \vdash \varphi$ であり、$\Gamma$ が $(\Theta; \Delta)$ を表現するならば、ある項 $t$ について $\Gamma \vdash t : \varphi^\ast$ が成り立つ。

</div>

定理 4.1 は $\Gamma = \Delta^\ast$ という特別な場合である。$\Theta$ が自由な命題変数を列挙するとき、文脈 $\Delta^\ast$ はちょうど必要な仮定を含む。それが整形式であることは、後述の補題 A.3 と規則 C-Ext から従う。命題変数がスコープに入れば、各仮定の型 $\chi^\ast$ は命題だからである。

## 変換についての事実

変換 $\varphi \mapsto \varphi^\ast$ は代入と可換である。

$$
(\subst{\varphi}{P}{\psi})^\ast = \subst{\varphi^\ast}{P}{\psi^\ast}.
$$

これは $\varphi$ に関する定型的な帰納法で示せる。両辺とも $P$ の自由な出現を $\psi^\ast$ で置き換えるのであり、変換は命題変数に対して、その名前を保つ以外に何もしない。主証明の $\forall$-elim のケースはこの等式に依存する。

次の補題は、[第 13 章](13-universes.md)の宇宙構造が入ってくる唯一の箇所である。変換されたすべての論理式が命題である、すなわち型 $\Sort{0}$ を持つことを述べる。これがなければ、型付け規則 T-Lam を仮定に適用できず、$\forall$-elim のケースで量化子を任意の論理式で具体化できない。

<div class="lemma" markdown="1">

**補題 A.3（論理式は命題である）.** $\ctxok{\Gamma}$ であり、すべての $P \in \FV(\varphi)$ について $(P : \Sort{0}) \in \Gamma$ ならば、$\Gamma \vdash \varphi^\ast : \Sort{0}$ である。

</div>

<div class="proof" markdown="1">

$\varphi$ に関する帰納法による。

命題変数 $P$ の場合、仮定から $(P : \Sort{0}) \in \Gamma$ なので、T-Var により $\Gamma \vdash P : \Sort{0}$ である。

$\varphi \to \psi$ の場合、帰納法の仮定から $\Gamma \vdash \varphi^\ast : \Sort{0}$ なので、新鮮な $x$ について $\Gamma, x : \varphi^\ast$ は C-Ext により整形式である。この拡張した文脈で $\psi$ に帰納法の仮定を適用すると $\Gamma, x : \varphi^\ast \vdash \psi^\ast : \Sort{0}$ が得られ、T-Pi により $\Gamma \vdash \tPi{x}{\varphi^\ast}{\psi^\ast} : \Sort{\imax(0, 0)} = \Sort{0}$ となる。

$\forall Q.\,\chi$ の場合、$Q \notin \dom(\Gamma)$ となるように $Q$ を改名する。T-Sort により $\Gamma \vdash \Sort{0} : \Sort{1}$ なので、$\Gamma, Q : \Sort{0}$ は C-Ext により整形式である。この文脈で $\chi$ に帰納法の仮定を適用すると $\Gamma, Q : \Sort{0} \vdash \chi^\ast : \Sort{0}$ が得られ、T-Pi により $\Gamma \vdash \tPi{Q}{\Sort{0}}{\chi^\ast} : \Sort{\imax(1, 0)} = \Sort{0}$ となる。

</div>

<aside class="note" markdown="1">

最後のケースが非述語性を使う箇所である。定義域 $\Sort{0}$ は $\Sort{1}$ に住むので、$\imax$ の代わりに $\max$ を使うと、型 $(\forall Q.\,\chi)^\ast$ は $\Sort{0}$ ではなく $\Sort{1}$ に落ちてしまう。すると後述の $\forall$-elim のケースは、$\forall$ を含まない論理式 $\psi$ についてしか成り立たなくなる。型 $\Sort{0}$ を持ち、引数として許されるのは、そうした論理式だけだからである。この設計上の選択は第 13 章で論じている。

</aside>

## 証明

<div class="proof" markdown="1">

定理 A.2 を、$\Theta; \Delta \vdash \varphi$ の導出に関する帰納法で、表現するすべての文脈 $\Gamma$ について同時に証明する。各ケースは、第 4 章の表の右列に示した型付け導出を組み立てる。

*仮定（Hyp）.* この規則は $\varphi \in \Delta$ から $\Theta; \Delta \vdash \varphi$ を結論する。$\Gamma$ は $(\Theta; \Delta)$ を表現するので仮定 $h : \varphi^\ast$ を含み、T-Var により $\Gamma \vdash h : \varphi^\ast$ である。

*$\to$-intro.* 前提は $\Theta; \Delta, \varphi \vdash \psi$、結論は $\Theta; \Delta \vdash \varphi \to \psi$ である。補題 A.3 により $\Gamma \vdash \varphi^\ast : \Sort{0}$ である。したがって新鮮な $h$ について、文脈 $\Gamma, h : \varphi^\ast$ は C-Ext により整形式であり、$(\Theta; \Delta, \varphi)$ を表現する。前提とこの文脈に帰納法の仮定を適用すると、ある $t$ について $\Gamma, h : \varphi^\ast \vdash t : \psi^\ast$ が得られ、T-Lam により

$$
\Gamma \vdash \tLam{h}{\varphi^\ast}{t} : \tPi{h}{\varphi^\ast}{\psi^\ast}.
$$

となる。この型は $\varphi^\ast \to \psi^\ast$ である。$\psi^\ast$ の自由変数は命題変数であり、$h$ はそのどれでもないので、$h$ は $\psi^\ast$ に現れず、この $\Pi$ は非依存的である。

*$\to$-elim.* 前提は $\Theta; \Delta \vdash \varphi \to \psi$ と $\Theta; \Delta \vdash \varphi$ である。帰納法の仮定から、$x \notin \FV(\psi^\ast)$ となる $\Gamma \vdash f : \tPi{x}{\varphi^\ast}{\psi^\ast}$ と、$\Gamma \vdash a : \varphi^\ast$ が得られる。T-App により $\Gamma \vdash f\;a : \subst{\psi^\ast}{x}{a}$ であり、$x$ は $\psi^\ast$ に現れないので代入は何もしない。すなわち $\subst{\psi^\ast}{x}{a} = \psi^\ast$ である。

*$\forall$-intro.* 前提は $P \notin \Theta$ を満たす $\Theta, P; \Delta \vdash \varphi$、結論は $\Theta; \Delta \vdash \forall P.\,\varphi$ である。必要なら $P$ を改名して、$P \notin \dom(\Gamma)$ と仮定する。$\Theta$ の変数を新鮮な変数に改名しても導出が保たれることは、定型的な帰納法で示せる。T-Sort と C-Ext により $\Gamma, P : \Sort{0}$ は整形式であり、$(\Theta, P; \Delta)$ を表現する。帰納法の仮定から $\Gamma, P : \Sort{0} \vdash t : \varphi^\ast$ が得られ、T-Lam により

$$
\Gamma \vdash \tLam{P}{\Sort{0}}{t} : \tPi{P}{\Sort{0}}{\varphi^\ast},
$$

となる。これは $\forall P.\,\varphi$ の変換である。

*$\forall$-elim.* 前提は $\FV(\psi) \subseteq \Theta$ を満たす $\Theta; \Delta \vdash \forall P.\,\varphi$、結論は $\Theta; \Delta \vdash \subst{\varphi}{P}{\psi}$ である。帰納法の仮定から $\Gamma \vdash f : \tPi{P}{\Sort{0}}{\varphi^\ast}$ が得られる。$\psi$ の命題変数はすべて $\Theta$ にあり、したがって $\Gamma$ に仮定 $Q : \Sort{0}$ を持つので、補題 A.3 により $\Gamma \vdash \psi^\ast : \Sort{0}$ である。T-App により

$$
\Gamma \vdash f\;\psi^\ast : \subst{\varphi^\ast}{P}{\psi^\ast} = (\subst{\varphi}{P}{\psi})^\ast,
$$

となる。最後のステップは前節の代入の等式である。

論理のすべての規則を扱ったので、定理はあらゆる導出について成り立つ。

</div>

この証明は T-Conv を一度も必要としない。組み立てるすべての型付け導出は、束縛変数の名前を除いて、型を構文的にのみ比較する。変換が必要になるのは、第 II 部の帰納型のように、論理に計算を加えたときだけである。

<aside class="history" markdown="1">

逆方向、すなわち型 $\varphi^\ast$ を持つすべての項が $\varphi$ の証明から来るという主張は、*保存性*と呼ばれる。第 4 章で触れたように、こちらのほうが難しい。$\Sort{0}$ には論理式の変換ではない型が含まれ、項がそれらを経由しうるからである。本書はこれを必要としない。カーネルが保証しなければならないのは整合性であり、それは[付録 D](d-proof-consistency.md)で証明する。

</aside>

<div class="summary-box" markdown="1">

覚えておくこと

- 定理の精密な形は命題変数の明示的なリスト $\Theta$ を携え、$(\Theta; \Delta)$ を任意の順序で表現するあらゆる文脈について主張を証明する。
- 変換されたすべての論理式は $\Sort{0}$ に住む（補題 A.3）。これは $\forall$ のケースで非述語性を使っており、$\forall$-elim が量化子を任意の論理式で具体化できるのはそのおかげである。
- 証明は導出に関する帰納法であり、各論理規則はちょうど一つの型付け規則に対応する。Hyp は T-Var に、二つの導入は T-Lam に、二つの除去は T-App に対応する。
- 論理には計算がないので、T-Conv は一度も使われない。

</div>
