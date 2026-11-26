<div class="lead" markdown="1">

定理 4.1 は、二階命題論理のどの導出からも、カーネルが受理する項を作れることを主張しています。この付録では、導出に関する帰納法でこれを証明します。各ケースは、[第 4 章](04-logic.md)の翻訳表の一行に対応します。

</div>

## 考え方

論理における導出は、規則を適用してできる木です。第 4 章の変換では各論理規則を一つの型付け規則と対にしたので、自然な方針は、導出を葉から根へとたどり、各節点で対応する型付け規則を使って型付け導出を組み立てることです。仮定は変数の参照に、含意の導入は $\lambda$ に、含意の除去は適用になります。二つの量化子規則は、それぞれ $\Sort{0}$ 上の $\lambda$ と、型への適用になります。

注意の要る細部が二つあり、どちらも文脈にかかわります。

- 論理の規則は、どの命題変数がスコープ内にあるかを述べません。しかし命題変数 $P$ は、仮定 $P : \Sort{0}$ が文脈に入ってはじめて使えるので、型付けの側ではそれを知っておく必要があります。そこで精密な主張では、命題変数の明示的なリスト $\Theta$ を持ち回ります。
- 型付け規則は文脈を右側に拡張しますが、第 4 章の変換 $\Delta^\ast$ は、すべての命題変数をすべての仮定より前に置きます。並び順は任意にしておいたほうが証明が楽なので、以下で定義する意味で論理の判断を*表現する*文脈であれば、どれについても定理が成り立つことを証明します。

## 精密な主張

定理 4.1 では、どの命題変数がスコープ内にあるかを暗黙にしていました。証明のためにこれを明示して、

$$
\Theta; \Delta \vdash \varphi,
$$

と書きます。ここで $\Theta$ は相異なる命題変数のリストで、$\Delta$ または $\varphi$ に自由に現れる命題変数はすべて $\Theta$ に属するものとします。命題変数を明示すると、第 4 章の規則は次のようになります。

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

$\Delta$ に自由に現れる命題変数はすべて $\Theta$ にあり、$P$ はそこに含まれないので、第 4 章の側条件 $P \notin \FV(\Delta)$ は、$P \notin \Theta$ から従うようになります。論理式は $\alpha$ 同値を除いて扱うので、束縛された $P$ は、側条件を満たすようにいつでも改名できます。第 4 章と同じく、$\varphi^\ast \to \psi^\ast$ は、$x$ を新鮮な変数として $\tPi{x}{\varphi^\ast}{\psi^\ast}$ を表します。

第 4 章の文脈 $\Delta^\ast$ では命題変数を先に、仮定を後に並べました。しかし証明の途中では文脈を右側に拡張する必要があるので、並び順は任意にしておくほうが好都合です。

<div class="definition" markdown="1">

**定義 A.1（表現）.** 文脈 $\Gamma$ が $(\Theta; \Delta)$ を*表現する*とは、$\ctxok{\Gamma}$ であり、$\Gamma$ が各 $P \in \Theta$ に対する仮定 $P : \Sort{0}$ を一つずつと、各 $\chi \in \Delta$ に対する仮定 $h : \chi^\ast$ を一つずつ、何らかの順序で並べたものからなることをいいます。

</div>

<div class="theorem" markdown="1">

**定理 A.2（定理 4.1 の精密な形）.** $\Theta; \Delta \vdash \varphi$ であり、$\Gamma$ が $(\Theta; \Delta)$ を表現するならば、ある項 $t$ について $\Gamma \vdash t : \varphi^\ast$ が成り立ちます。

</div>

定理 4.1 は $\Gamma = \Delta^\ast$ という特別な場合です。$\Theta$ に自由な命題変数を列挙すれば、文脈 $\Delta^\ast$ はちょうど必要な仮定を含みます。命題変数がスコープに入れば各仮定の型 $\chi^\ast$ は命題になるので、この文脈が整形式であることは、後述の補題 A.3 と規則 C-Ext から従います。

## 変換についての事実

変換 $\varphi \mapsto \varphi^\ast$ は代入と可換です。

$$
(\subst{\varphi}{P}{\psi})^\ast = \subst{\varphi^\ast}{P}{\psi^\ast}.
$$

両辺とも $P$ の自由な出現を $\psi^\ast$ で置き換えたものであり、変換は命題変数の名前をそのまま保つだけなので、この等式は $\varphi$ に関する定型的な帰納法で示せます。主証明の $\forall$-elim のケースは、この等式を使います。

次の補題は、[第 13 章](13-universes.md)の宇宙の構造が効いてくる唯一の箇所です。変換したどの論理式も命題である、すなわち型 $\Sort{0}$ を持つことを述べています。この補題がなければ、仮定に型付け規則 T-Lam を適用できず、$\forall$-elim のケースで量化子を任意の論理式で具体化することもできません。

<div class="lemma" markdown="1">

**補題 A.3（論理式は命題である）.** $\ctxok{\Gamma}$ であり、すべての $P \in \FV(\varphi)$ について $(P : \Sort{0}) \in \Gamma$ ならば、$\Gamma \vdash \varphi^\ast : \Sort{0}$ です。

</div>

<div class="proof" markdown="1">

$\varphi$ に関する帰納法によります。

命題変数 $P$ の場合、仮定から $(P : \Sort{0}) \in \Gamma$ なので、T-Var により $\Gamma \vdash P : \Sort{0}$ です。

$\varphi \to \psi$ の場合、帰納法の仮定から $\Gamma \vdash \varphi^\ast : \Sort{0}$ なので、新鮮な $x$ について $\Gamma, x : \varphi^\ast$ は C-Ext により整形式です。この拡張した文脈で $\psi$ に帰納法の仮定を適用すると $\Gamma, x : \varphi^\ast \vdash \psi^\ast : \Sort{0}$ が得られ、T-Pi により $\Gamma \vdash \tPi{x}{\varphi^\ast}{\psi^\ast} : \Sort{\imax(0, 0)} = \Sort{0}$ となります。

$\forall Q.\,\chi$ の場合、$Q \notin \dom(\Gamma)$ となるように $Q$ を改名します。T-Sort により $\Gamma \vdash \Sort{0} : \Sort{1}$ なので、$\Gamma, Q : \Sort{0}$ は C-Ext により整形式です。この文脈で $\chi$ に帰納法の仮定を適用すると $\Gamma, Q : \Sort{0} \vdash \chi^\ast : \Sort{0}$ が得られ、T-Pi により $\Gamma \vdash \tPi{Q}{\Sort{0}}{\chi^\ast} : \Sort{\imax(1, 0)} = \Sort{0}$ となります。

</div>

<aside class="note" markdown="1">

非述語性を使うのは最後のケースです。定義域 $\Sort{0}$ は $\Sort{1}$ に住むので、$\imax$ の代わりに $\max$ を使うと、型 $(\forall Q.\,\chi)^\ast$ は $\Sort{0}$ ではなく $\Sort{1}$ に入ってしまいます。そうなると、型 $\Sort{0}$ を持ち、引数として渡せるのは $\forall$ を含まない論理式だけになり、後述の $\forall$-elim のケースはそうした論理式 $\psi$ についてしか成り立たなくなります。この設計上の選択については第 13 章で論じています。

</aside>

## 証明

<div class="proof" markdown="1">

定理 A.2 を、$\Theta; \Delta \vdash \varphi$ の導出に関する帰納法で、それを表現するすべての文脈 $\Gamma$ について同時に証明します。各ケースでは、第 4 章の表の右列に示した型付け導出を組み立てます。

*仮定（Hyp）.* この規則は $\varphi \in \Delta$ から $\Theta; \Delta \vdash \varphi$ を結論します。$\Gamma$ は $(\Theta; \Delta)$ を表現するので仮定 $h : \varphi^\ast$ を含み、T-Var により $\Gamma \vdash h : \varphi^\ast$ です。

*$\to$-intro.* 前提は $\Theta; \Delta, \varphi \vdash \psi$、結論は $\Theta; \Delta \vdash \varphi \to \psi$ です。補題 A.3 により $\Gamma \vdash \varphi^\ast : \Sort{0}$ なので、新鮮な $h$ について、文脈 $\Gamma, h : \varphi^\ast$ は C-Ext により整形式で、$(\Theta; \Delta, \varphi)$ を表現します。前提とこの文脈に帰納法の仮定を適用すると、ある $t$ について $\Gamma, h : \varphi^\ast \vdash t : \psi^\ast$ が得られ、T-Lam により

$$
\Gamma \vdash \tLam{h}{\varphi^\ast}{t} : \tPi{h}{\varphi^\ast}{\psi^\ast}.
$$

となります。$\psi^\ast$ の自由変数は命題変数だけで、$h$ はそのどれでもないので、$h$ は $\psi^\ast$ に現れません。したがってこの $\Pi$ は非依存的であり、この型は $\varphi^\ast \to \psi^\ast$ です。

*$\to$-elim.* 前提は $\Theta; \Delta \vdash \varphi \to \psi$ と $\Theta; \Delta \vdash \varphi$ です。帰納法の仮定から、$x \notin \FV(\psi^\ast)$ を満たす $\Gamma \vdash f : \tPi{x}{\varphi^\ast}{\psi^\ast}$ と、$\Gamma \vdash a : \varphi^\ast$ が得られます。T-App により $\Gamma \vdash f\;a : \subst{\psi^\ast}{x}{a}$ となりますが、$x$ は $\psi^\ast$ に現れないので代入は何も変えず、$\subst{\psi^\ast}{x}{a} = \psi^\ast$ です。

*$\forall$-intro.* 前提は $P \notin \Theta$ を満たす $\Theta, P; \Delta \vdash \varphi$、結論は $\Theta; \Delta \vdash \forall P.\,\varphi$ です。$\Theta$ の変数を新鮮な変数に改名しても導出が保たれることは定型的な帰納法で示せるので、必要なら $P$ を改名して、$P \notin \dom(\Gamma)$ と仮定します。T-Sort と C-Ext により $\Gamma, P : \Sort{0}$ は整形式で、$(\Theta, P; \Delta)$ を表現します。帰納法の仮定から $\Gamma, P : \Sort{0} \vdash t : \varphi^\ast$ が得られ、T-Lam により

$$
\Gamma \vdash \tLam{P}{\Sort{0}}{t} : \tPi{P}{\Sort{0}}{\varphi^\ast},
$$

となり、これは $\forall P.\,\varphi$ の変換です。

*$\forall$-elim.* 前提は $\FV(\psi) \subseteq \Theta$ を満たす $\Theta; \Delta \vdash \forall P.\,\varphi$、結論は $\Theta; \Delta \vdash \subst{\varphi}{P}{\psi}$ です。帰納法の仮定から $\Gamma \vdash f : \tPi{P}{\Sort{0}}{\varphi^\ast}$ が得られます。$\psi$ の命題変数はすべて $\Theta$ にあるので、$\Gamma$ はそれぞれに対する仮定 $Q : \Sort{0}$ を含み、補題 A.3 により $\Gamma \vdash \psi^\ast : \Sort{0}$ です。T-App により

$$
\Gamma \vdash f\;\psi^\ast : \subst{\varphi^\ast}{P}{\psi^\ast} = (\subst{\varphi}{P}{\psi})^\ast,
$$

となります。最後のステップでは、前節の代入の等式を使いました。

論理のすべての規則を扱ったので、定理はどの導出についても成り立ちます。

</div>

ここで組み立てた型付け導出はどれも、束縛変数の名前を除いて型を構文的に比べるだけなので、この証明では T-Conv を一度も使いません。変換が必要になるのは、第 II 部の帰納型のように、論理に計算を加えたときだけです。

<aside class="history" markdown="1">

逆方向の主張、つまり型 $\varphi^\ast$ を持つ項はどれも $\varphi$ の証明から来るという主張は、*保存性*と呼ばれます。第 4 章で触れたとおり、$\Sort{0}$ には論理式の変換ではない型も含まれ、項がそれらを経由することがあるので、こちらのほうが難しい問題です。本書では保存性は必要ありません。カーネルが保証しなければならないのは整合性であり、これは[付録 D](d-proof-consistency.md)で証明します。

</aside>

<div class="summary-box" markdown="1">

覚えておくこと

- 定理の精密な形では命題変数の明示的なリスト $\Theta$ を持ち回り、$(\Theta; \Delta)$ を任意の順序で表現するどの文脈についても主張を証明します。
- 変換したどの論理式も $\Sort{0}$ に住みます（補題 A.3）。$\forall$ のケースでは非述語性を使っており、$\forall$-elim で量化子を任意の論理式で具体化できるのはそのおかげです。
- 証明は導出に関する帰納法で、各論理規則はちょうど一つの型付け規則に対応します。Hyp は T-Var に、二つの導入は T-Lam に、二つの除去は T-App に対応します。
- 論理には計算がないので、T-Conv は一度も使われません。

</div>
