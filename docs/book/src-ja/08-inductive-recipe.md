<div class="lead" markdown="1">

第 7 章では、自然数の再帰子を手で組み立てました。Lean では、カーネルが `inductive` 宣言を検査し、再帰子と計算規則を自動で生成します。この章では、構成子を増やし、パラメータと添字を加えながら、この生成手順を導きます。対応するカーネルのコードは約五百行です。

</div>

## 構成子を増やす: 木

$\Nat$ の構成子は二つで、そのうち再帰的引数を持つのは一つだけでした。今度は構成子が三つある型を考えてみましょう。

```lean
inductive Tree where
  | leaf   : Tree
  | node   : Tree -> Tree
  | branch : Tree -> Tree -> Tree
```

たとえば $\mathsf{branch}\;(\mathsf{node}\;\mathsf{leaf})\;\mathsf{leaf}$ は、四つの構成子から組み立てた木です。$M : \mathsf{Tree} \to \Sort{v}$ として、すべての木 $t$ について $M\;t$ を組み立てたいとします。第 7 章の手順に従うと、構成子ごとにケースが一つずつ必要になり、型 $\mathsf{Tree}$ の引数が一つあるごとに帰納法の仮定が一つ加わります。

$$
\begin{array}{lcl}
m_{\mathsf{leaf}} &:& M\;\mathsf{leaf} \\[2pt]
m_{\mathsf{node}} &:& \tPi{t}{\mathsf{Tree}}{M\;t \to M\;(\mathsf{node}\;t)} \\[2pt]
m_{\mathsf{branch}} &:& \tPi{l}{\mathsf{Tree}}{\tPi{r}{\mathsf{Tree}}{M\;l \to M\;r \to M\;(\mathsf{branch}\;l\;r)}}
\end{array}
$$

再帰子は、motive、三つのケース、そして木を受け取ります。

$$
\mathsf{Tree.rec}_v : \tPi{M}{\mathsf{Tree} \to \Sort{v}}{\;
  M\;\mathsf{leaf} \to (\cdots_{\mathsf{node}}) \to (\cdots_{\mathsf{branch}}) \to \tPi{t}{\mathsf{Tree}}{M\;t}},
$$

ここで点々は $m_{\mathsf{node}}$ と $m_{\mathsf{branch}}$ の型を表します。$\NatRec{v}$ と比べて変わったのは、ケースの数と、ケースごとの仮定の数だけです。部分適用 $\mathsf{Tree.rec}_v\;M\;m_{\mathsf{leaf}}\;m_{\mathsf{node}}\;m_{\mathsf{branch}}$ を $R$ と書くと、ι 規則は次のようになります。

$$
\begin{array}{rcl}
R\;\mathsf{leaf} &\iotared& m_{\mathsf{leaf}} \\[2pt]
R\;(\mathsf{node}\;t) &\iotared& m_{\mathsf{node}}\;t\;(R\;t) \\[2pt]
R\;(\mathsf{branch}\;l\;r) &\iotared& m_{\mathsf{branch}}\;l\;r\;(R\;l)\;(R\;r).
\end{array}
$$

どの規則も、大前提の頭部にある構成子に対応するケースを選び、各仮定には対応する部分木への再帰呼び出しを入れます。たとえば $M = \tLam{\_}{\mathsf{Tree}}{\Nat}$ とし、ケースを

$$
m_{\mathsf{leaf}} = 1, \qquad
m_{\mathsf{node}} = \tLam{t}{\mathsf{Tree}}{\tLam{i}{\Nat}{1 + i}}, \qquad
m_{\mathsf{branch}} = \tLam{l}{\mathsf{Tree}}{\tLam{r}{\mathsf{Tree}}{\tLam{i}{\Nat}{\tLam{j}{\Nat}{1 + i + j}}}},
$$

とすると、$R$ は木に含まれる構成子の数を数えます。

$$
R\;(\mathsf{branch}\;(\mathsf{node}\;\mathsf{leaf})\;\mathsf{leaf})
\to 1 + R\;(\mathsf{node}\;\mathsf{leaf}) + R\;\mathsf{leaf}
\to 1 + (1 + R\;\mathsf{leaf}) + 1
\to 1 + (1 + 1) + 1 = 4.
$$

$M$ を述語にすれば（$v = 0$）、同じ再帰子が木に関する構造的帰納法になります。一般に、構成子が $n$ 個ある型には、$n$ 個の小前提 $m_1, \ldots, m_n$ を持つ再帰子が付きます。カーネルにはその型専用のコードは要らず、構成子ごとに、どのケースを選び、どの引数で再帰するかさえ分かれば十分です。

下の図は、この木をカーネルから見たものです。各ボックスが構成子の適用を表し、再帰的フィールドはその下にぶら下がります。各ボックスの最下行は、そのボックスを処理する再帰子のケースです。$(R\;l)$ と $(R\;r)$ は、再帰呼び出しで計算される帰納法の仮定にあたります。別の木を入力すると、そのケースが表示されます。

<div class="explorer" data-kind="ctree" data-term="Tree.branch (Tree.node Tree.leaf) Tree.leaf"><pre class="prelude">inductive Tree : Sort 1 where
  | leaf
  | node (t : Tree)
  | branch (l : Tree) (r : Tree)</pre></div>

<div class="playground" data-file="tree-count"><pre>inductive Tree : Sort 1 where
  | leaf
  | node (t : Tree)
  | branch (l : Tree) (r : Tree)

def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def one : Nat := Nat.succ Nat.zero
def four : Nat := Nat.succ (Nat.succ (Nat.succ one))

# branch の小前提は l と r を受け取り、続いて二つの帰納法の仮定を受け取る。
def count : Tree -> Nat := fun (t : Tree) => Tree.rec1 (fun (_t : Tree) => Nat) one (fun (t : Tree) => fun (i : Nat) => Nat.succ i) (fun (l : Tree) => fun (r : Tree) => fun (i : Nat) => fun (j : Nat) => Nat.succ (add i j)) t

goal Eq Nat (count (Tree.branch (Tree.node Tree.leaf) Tree.leaf)) four
rfl
qed</pre></div>

## パラメータ: リスト

数のリストは、空であるか、数のリストの先頭に数を一つ付け加えたものです。そこで、構成子 $\mathsf{nil}$ と $\mathsf{cons} : \Nat \to \mathsf{ListNat} \to \mathsf{ListNat}$ を持つ型 $\mathsf{ListNat}$ を宣言することもできます。しかしこの方法だと、木のリストを扱うには構成子は同じで再帰子だけが違う別の宣言 $\mathsf{ListTree}$ が必要になり、要素の型ごとに同じ宣言を繰り返すはめになります。要素の型は、型そのものの引数にしたほうがよいでしょう。

```lean
inductive List (A : Sort 1) where
  | nil  : List A
  | cons : A -> List A -> List A
```

これで $\mathsf{List}\;\Nat$ と $\mathsf{List}\;\mathsf{Tree}$ は、一つの宣言から得られる二つのインスタンスになります。この宣言によって、次の定数が追加されます。

$$
\mathsf{List} : \Sort{1} \to \Sort{1}, \qquad
\mathsf{nil} : \tPi{A}{\Sort{1}}{\mathsf{List}\;A}, \qquad
\mathsf{cons} : \tPi{A}{\Sort{1}}{A \to \mathsf{List}\;A \to \mathsf{List}\;A}.
$$

構成子は $A$ を明示的な第一引数として受け取ります。たとえば一要素のリスト $[5]$ は $\mathsf{cons}\;\Nat\;5\;(\mathsf{nil}\;\Nat)$ です。一つのリストの中で $A$ が変わることはなく、$\mathsf{cons}\;A\;a\;\mathit{as}$ の尾部もやはり $\mathsf{List}\;A$ です。このように、すべての構成子とすべての再帰的引数で変わらない型の引数を**パラメータ**（parameter）と呼びます。パラメータは変わらないので、再帰子はそれを motive より前に一度だけ受け取り、固定したものとして扱えます。

$$
\begin{array}{l}
\mathsf{List.rec}_v : \tPi{A}{\Sort{1}}{\tPi{M}{\mathsf{List}\;A \to \Sort{v}}{\;M\;(\mathsf{nil}\;A) \to {}}} \\[2pt]
\qquad (\tPi{a}{A}{\tPi{\mathit{as}}{\mathsf{List}\;A}{M\;\mathit{as} \to M\;(\mathsf{cons}\;A\;a\;\mathit{as})}}) \to \tPi{x}{\mathsf{List}\;A}{M\;x} \\[8pt]
\mathsf{List.rec}_v\;A\;M\;m_1\;m_2\;(\mathsf{nil}\;A') \;\iotared\; m_1 \\[2pt]
\mathsf{List.rec}_v\;A\;M\;m_1\;m_2\;(\mathsf{cons}\;A'\;a\;\mathit{as}) \;\iotared\; m_2\;a\;\mathit{as}\;(\mathsf{List.rec}_v\;A\;M\;m_1\;m_2\;\mathit{as})
\end{array}
$$

先頭の $A$ を除けば、これも第 7 章の手順そのものです。$\mathsf{cons}$ の引数は二つで、再帰的なのは $\mathit{as}$ だけなので、そのケースには帰納法の仮定が一つ付きます。型の付いた項では、構成子に格納されたパラメータ $A'$ は $A$ と変換可能なので、規則はこれを無視します。たとえばリストの長さは次のように書けます。

$$
\mathit{length} \mathrel{:=} \tLam{A}{\Sort{1}}{\tLam{x}{\mathsf{List}\;A}{
\mathsf{List.rec}_1\;A\;(\tLam{\_}{\mathsf{List}\;A}{\Nat})\;\zero\;(\tLam{a}{A}{\tLam{\mathit{as}}{\mathsf{List}\;A}{\tLam{r}{\Nat}{\suc\;r}}})\;x}}.
$$

リストの値はすべての構成子にパラメータ $A$ を持ち運んでおり、下の木では各ボックスの横にそれが表示されます。パラメータはどのボックスでも同じで、フィールドだけが異なります。

<div class="explorer" data-kind="ctree" data-term="List.cons Nat (Nat.succ Nat.zero) (List.cons Nat Nat.zero (List.nil Nat))"><pre class="prelude">inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)</pre></div>

<div class="playground" data-file="examples/generic-list.leanmini"><pre>inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)

def length : forall (A : Sort 1), List A -> Nat := fun (A : Sort 1) => fun (xs : List A) => List.rec1 A (fun (_xs : List A) => Nat) Nat.zero (fun (head : A) => fun (tail : List A) => fun (r : Nat) => Nat.succ r) xs

# length [0, 0] = 2
goal Eq Nat (length Nat (List.cons Nat Nat.zero (List.cons Nat Nat.zero (List.nil Nat)))) (Nat.succ (Nat.succ Nat.zero))
rfl
qed</pre></div>

## 添字: ベクトル

$\mathsf{List}\;\Nat$ の長さは任意です。では、長さを型の一部にして、$\mathsf{Vec}\;\Nat\;0$ と $\mathsf{Vec}\;\Nat\;2$ を別々の型にしたい場合はどうなるでしょうか。

```lean
inductive Vec (A : Sort 1) : Nat -> Sort 1 where
  | vnil  : Vec A 0
  | vcons : (n : Nat) -> A -> Vec A n -> Vec A (succ n)
```

要素の型 $A$ は相変わらずパラメータですが、長さはそうではありません。$\mathsf{vnil}$ の長さは $0$ で、$\mathsf{vcons}$ は長さ $n$ のベクトルを受け取って長さ $\suc\;n$ のベクトルを返します。構成子ごとに、また構成子とその再帰的引数とのあいだで異なってよい型の引数を**添字**（index）と呼びます。構成子は次のとおりです。

$$
\mathsf{vnil} : \tPi{A}{\Sort{1}}{\mathsf{Vec}\;A\;\zero}, \qquad
\mathsf{vcons} : \tPi{A}{\Sort{1}}{\tPi{n}{\Nat}{A \to \mathsf{Vec}\;A\;n \to \mathsf{Vec}\;A\;(\suc\;n)}}.
$$

添字は変化するので、再帰子はそれを前もって固定できません。代わりに motive が添字を引数として受け取ります。$M : \tPi{n}{\Nat}{\mathsf{Vec}\;A\;n \to \Sort{v}}$ であり、$\mathsf{vcons}$ のケースは

$$
\tPi{n}{\Nat}{\tPi{a}{A}{\tPi{\mathit{xs}}{\mathsf{Vec}\;A\;n}{M\;n\;\mathit{xs} \to M\;(\suc\;n)\;(\mathsf{vcons}\;A\;n\;a\;\mathit{xs})}}}.
$$

となります。帰納法の仮定は長さ $n$ のベクトルについての主張で、その長さは再帰的引数の型 $\mathsf{Vec}\;A\;n$ から読み取ります。一方、結論は長さ $\suc\;n$ のベクトルについての主張で、こちらは構成子の結果型から読み取ります。スクリプト `examples/generic-vec.leanmini`（[付録 E](e-leanmini-reference.md)）では、この型を宣言し、それを使う小さな項を検査しています。

## 一般的な手順

この節では、パラメータと添字を持つ単一の帰納型について手続きを述べます。Lean が対応している相互帰納型と入れ子帰納型は範囲外とします。

この手続きは、T-Const が未解決のまま残した問いにも答えを与えます。本体のない定数は仮定にあたり、T-Const は $\zero : \Nat$ を受け入れるのとまったく同じように $c : \tPi{P}{\Sort{0}}{P}$ も受け入れてしまいます。そして後者があると、体系は非整合になります。以下で生成する定数は恣意的な仮定ではなく、固定されたスキーマのインスタンス、つまり Calculus of Inductive Constructions の帰納型であり、その整合性は知られています [Werner 1994]。

**テレスコープ。** 束縛の列 $(x_1 : A_1) \cdots (x_k : A_k)$ のうち、各 $A_i$ が $x_1, \ldots, x_{i-1}$ に言及してよいものを $(\vec{x} : \vec{A})$ と書きます。また $\tPi{x_1}{A_1}{\cdots\,\tPi{x_k}{A_k}{B}}$ を $\tPi{\vec{x}}{\vec{A}}{B}$ と、$f\;x_1 \cdots x_k$ を $f\;\vec{x}$ と略記し、$\vec{x}$ の長さを $|\vec{x}|$ で表します。コードではテレスコープは `Context` で表され、`src/term.rs` の `telescope(binders, tail)` が入れ子の $\Pi$ を組み立てます。

**宣言。** 宣言は、型構成子 $I$ と構成子 $c_1, \ldots, c_n$ を導入します。

$$
\begin{array}{rcll}
I &:& \tPi{\vec{p}}{\vec{P}}{\tPi{\vec{\imath}}{\vec{J}}{\Sort{u}}} & \\[2pt]
c_j &:& \tPi{\vec{p}}{\vec{P}}{\tPi{\vec{a}}{\vec{A}_j}{I\;\vec{p}\;\vec{t}_j}} & (j = 1, \ldots, n)
\end{array}
$$

**パラメータ** $\vec{p}$ はすべての構成子に共通で、どの結果型にも同じ形で現れます。**添字** $\vec{\imath}$ は構成子ごとに異なってよく、添字項 $\vec{t}_j$ は $\vec{p}$ と、構成子自身の引数 $\vec{a}$ に言及できます。この引数を**フィールド**（field）と呼びます。これまでの例を、構成子の型からパラメータの先頭の $\Pi$ を省いて示すと、次のようになります。

| 型構成子 | パラメータ | 添字 | 構成子 |
|---|---|---|---|
| $\Nat : \Sort{1}$ | なし | なし | $\zero : \Nat$, $\;\suc : \Nat \to \Nat$ |
| $\mathsf{Tree} : \Sort{1}$ | なし | なし | $\mathsf{leaf}$, $\mathsf{node}$, $\mathsf{branch}$ |
| $\mathsf{List} : \Sort{1} \to \Sort{1}$ | $(A : \Sort{1})$ | なし | $\mathsf{nil} : \mathsf{List}\;A$, $\;\mathsf{cons} : A \to \mathsf{List}\;A \to \mathsf{List}\;A$ |
| $\mathsf{Vec} : \Sort{1} \to \Nat \to \Sort{1}$ | $(A : \Sort{1})$ | $(n : \Nat)$ | $\mathsf{vnil} : \mathsf{Vec}\;A\;\zero$, $\;\mathsf{vcons} : \tPi{n}{\Nat}{A \to \mathsf{Vec}\;A\;n \to \mathsf{Vec}\;A\;(\suc\;n)}$ |

**受理。** カーネルが宣言を受理するのは、次の四つの条件がすべて成り立つときに限ります。

1. $I$ の型が、現在のシグネチャのもとで型になっていること。
2. $I$ をシグネチャに加えたうえで、各構成子の型が型になっていて、その末尾が $I\;\vec{p}\;\vec{t}_j$ の形をしていること。ここで $\vec{p}$ はパラメータをちょうどその順に並べたもので、$I$ は $\vec{t}_j$ に現れません。
3. **正格な正値性。** 各フィールドの型は、$I$ に言及しないか、$I$ が $\vec{B}$ にも $\vec{s}$ にも現れない $\tPi{\vec{y}}{\vec{B}}{I\;\vec{p}\;\vec{s}}$ の形をしているかのどちらかであること。後者の形のフィールドを**再帰的**（recursive）と呼びます。
4. **宇宙。** $u \ge 1$ なら、各フィールドの型はある $\Sort{w}$（$w \le u$）に属すること。$u = 0$ なら条件はありません。

条件 2 のおかげで、再帰子はパラメータを一様に扱えます。条件 3 は、たとえば次のような宣言を排除します。

```lean
inductive Bad where
  | mk : (Bad -> False) -> Bad
```

このフィールドは矢印の左側で `Bad` に言及しています。`Bad` に対する場合分けを許すと、$f\;(\mathsf{mk}\;g) = g\;(\mathsf{mk}\;g)$ によって $f : \mathsf{Bad} \to \mathsf{False}$ が定義できてしまいます。すると $f\;(\mathsf{mk}\;f)$ は型 $\mathsf{False}$ の閉じた項になり、しかも自分自身に簡約されるので正規形を持ちません。宣言中の型 $\mathsf{Tree}$ を例に、フィールドの型とその扱いをいくつか示します。

| フィールドの型 | 扱い | 理由 |
|---|---|---|
| $\Nat$ | 受理、非再帰的 | $\mathsf{Tree}$ に言及しない |
| $\mathsf{Tree}$ | 受理、再帰的 | 帰納法の仮定は $M\;a_k$ |
| $\Nat \to \mathsf{Tree}$ | 受理、再帰的 | 木を生み出す。仮定は $\tPi{n}{\Nat}{M\;(a_k\;n)}$ |
| $\mathsf{Tree} \to \Nat$ | 拒否 | $\mathsf{Tree}$ が矢印の左側にある |
| $\mathsf{List}\;\mathsf{Tree}$ | ここでは拒否 | 入れ子の出現。Lean は受理するが範囲外 |

型 $\Nat \to \mathsf{Tree}$ のフィールドは、数ごとに一つずつ、無限個の子を持つ木を表しますが、それでも再帰子は各子 $a_k\;n$ へ再帰できます。一方、型 $\mathsf{Tree} \to \Nat$ のフィールドは木を含むのではなく木を*消費*するもので、`Bad` をパラドックスにしていたのもこの形です。

条件 4 は、型がより大きな宇宙を含むのを防ぎます。この条件がないと、構成子 $\mathsf{mk} : \Sort{1} \to T$ を持つ宣言 $T : \Sort{1}$ によって $\Sort{1}$ 全体の複製が $\Sort{1}$ の内側に置かれてしまいます。[第 13 章](13-universes.md)で非整合だと示す自己包含が、まさにこれです。$u = 0$ のときは $\Sort{0}$ が非述語的なので、この条件は要りません。

**再帰子。** 受理された宣言について、カーネルは許容される各レベル $v$（後述）ごとに再帰子 $I.\mathsf{rec}_v$ を生成します。

$$
I.\mathsf{rec}_v :
\tPi{\vec{p}}{\vec{P}}{\;
\tPi{M}{(\tPi{\vec{\imath}}{\vec{J}}{I\;\vec{p}\;\vec{\imath} \to \Sort{v}})}{\;
\tPi{m_1}{C_1}{\cdots\,\tPi{m_n}{C_n}{\;
\tPi{\vec{\imath}}{\vec{J}}{\tPi{x}{I\;\vec{p}\;\vec{\imath}}{M\;\vec{\imath}\;x}}}}}}.
$$

パラメータが先頭に来て固定される点はリストと同じで、motive が添字と要素を受け取る点はベクトルと同じです。小前提 $C_j$ は、構成子 $c_j$ のケースを要求します。つまり、フィールドと、再帰的フィールドごとの帰納法の仮定が与えられたとき、$c_j$ をそれらのフィールドに適用したものについて $M$ を組み立てることを求めます。

$$
\begin{array}{l}
C_j = \tPi{\vec{a}}{\vec{A}_j}{\;\tPi{\vec{h}}{\vec{H}_j}{\;M\;\vec{t}_j\;(c_j\;\vec{p}\;\vec{a})}}, \\[4pt]
H_{j,k} = \tPi{\vec{y}}{\vec{B}}{M\;\vec{s}\;(a_k\;\vec{y})}
\quad\text{for each recursive field } a_k : \tPi{\vec{y}}{\vec{B}}{I\;\vec{p}\;\vec{s}}.
\end{array}
$$

最後の引数は、添字と要素 $x$ 自身、すなわち大前提です。

**規則。** カーネルは構成子ごとに ι 規則を一つ生成します。この規則は、小前提をフィールドと、再帰呼び出しで計算した帰納法の仮定とに適用します。

$$
I.\mathsf{rec}_v\;\vec{p}\;M\;\vec{m}\;\vec{\imath}\;(c_j\;\vec{p}\,'\;\vec{a}) \;\iotared\; m_j\;\vec{a}\;\vec{h},
\qquad
h_k = \tLam{\vec{y}}{\vec{B}}{I.\mathsf{rec}_v\;\vec{p}\;M\;\vec{m}\;\vec{s}\;(a_k\;\vec{y})}.
$$

大前提の位置は（ゼロから数えて）$|\vec{p}| + 1 + n + |\vec{\imath}|$ で、構成子は $|\vec{p}|$ 個のパラメータと $|\vec{a}|$ 個のフィールドを持ちます。型の付いた簡約基では $\vec{p}\,'$ は $\vec{p}$ と変換可能なので、リストの規則で $A'$ を無視したのと同じく、規則はこれを無視します。$\Nat$、$\mathsf{Tree}$、$\mathsf{List}$、$\mathsf{Vec}$ について、この手続きは本章と前章の再帰子と規則をそのまま生成します。生成される再帰子の型は、束縛変数の名前と暗黙の引数を除けば、Lean 4 が生成するものと一致します。

**命題からの消去。** $u \ge 1$ なら再帰子はすべてのレベル $v$ について生成されますが、$u = 0$、つまり $I$ が命題の場合は、$v = 0$ についてしか生成されません。ただし $I$ が**部分単集合**（subsingleton）なら話は別です。部分単集合とは、構成子が高々一つで、各フィールドが証明である（型が $\Sort{0}$ に属する）か、添字項 $\vec{t}_j$ の中に現れるかのどちらかである型をいいます。この制限は、命題の*どの*証明が与えられたかにデータが左右されるのを防ぐためのものです。たとえば $P \vee Q$ には構成子が二つあるので、制限がなければ $P \vee Q$ の証明から $\Nat$ への関数が一方の証明には $0$ を、他方には $1$ を返せてしまい、証明が計算上の情報を運んでしまいます。そのため Lean の `Or.rec` と `Exists.rec` は `Prop` へしか消去できず、`And.rec` と `Eq.rec` はどの宇宙へも消去できます。`And` の構成子は一つでフィールドはすべて証明であり、`Eq`（[第 9 章](09-equality.md)）の構成子は一つでフィールドを持たないからです。

こうして、シグネチャが大きくなってもカーネルの規則は変わりません。一つの汎用の手続きが各宣言をシグネチャの項目に変え、一つの簡約関数がそれらの規則を実行します（[第 12 章](12-reduction-conversion.md#computation-rules-as-data)）。

## コードでは

<aside class="code" markdown="1">

この手続きは `src/inductive/` にあります。入力は `InductiveSpec`（`src/declaration.rs`）で、名前、パラメータと添字のテレスコープ、宇宙レベル $u$、そして構成子ごとにフィールドと添字項 $\vec{t}_j$ を与える `ConstructorSpec` からなります。スクリプトのパーサは、`inductive` ブロックからこれを組み立てます。

- `src/inductive/mod.rs` の `Kernel::add_inductive` は、四つの受理条件を順に検査します（`check_inductive_type` が条件 1、フィールドが型であることを確かめる `check_constructor_fields` が条件 4、`check_constructor_result` が条件 2 を担当します）。すべて通れば型構成子と構成子を登録し、`InductiveInfo` を記録します。どこかで失敗した場合、シグネチャは変更されません。
- 条件 3 は `src/inductive/positivity.rs` が担当します。`check_recursive_field` はフィールドの型の先頭の $\Pi$ を剥がしていき、定義域が $I$ に言及していれば拒否します。さらに標的が、$I$ をちょうどパラメータ変数に適用し、その後に $I$ に言及しない添字項を続けた形であることを要求します。戻り値は $\vec{y} : \vec{B}$ と $\vec{s}$ を記録した `RecursiveFieldInfo` で、再帰子の生成器が必要とする情報はこれだけです。
- `src/inductive/recursor.rs` は、上の式に従って再帰子の型を組み立てます。`recursor_type` がテレスコープ $\vec{p}$、motive、小前提、添字、大前提をまとめ、`minor_premise_type` が各 $C_j$ を、`induction_hypothesis_type` が各 $H_{j,k}$ を組み立てます。生成される束縛子の名前（`__motive`、`__minor_j`、`__ih_j_k`、`__major`）は下線二つで始まり、ユーザーの宣言ではこの形の名前を使えないので、フィールドと衝突することはありません。
- 部分単集合の判定は `mod.rs` の `allows_large_elimination` が実装しています。`add_inductive` は `I.rec0` を常に登録し、大消去が許されるなら `I.rec1` も登録します。それより高いレベルの再帰子は、`register_recursor` が必要に応じて生成します。

ι 規則は項としては生成されません。`whnf` が、格納された `InductiveInfo` から直接適用します。詳しくは[第 12 章](12-reduction-conversion.md)で説明します。

</aside>

生成器の中心部は全文を読めるほど短いので、$C_j$ の式と見比べてみてください。

```rust
/// C_j = Pi (as : As_j). Pi (hs : Hs_j). M ts_j (c_j ps as)
fn minor_premise_type(info: &InductiveInfo, j: usize, constructor: &ConstructorInfo) -> Term {
    // c_j ps as
    let constructor_application = apps(
        const_term(&constructor.name),
        info.params.iter().chain(constructor.fields.iter()).map(|(name, _)| var(name)),
    );
    // (as : As_j) の後に (hs : Hs_j)
    let mut minor_premise_binders = constructor.fields.clone();
    for (k, recursive_field) in constructor.recursive_fields.iter().enumerate() {
        minor_premise_binders.push((
            format!("{INDUCTION_HYPOTHESIS_PREFIX}{j}_{k}"),
            induction_hypothesis_type(constructor, recursive_field),
        ));
    }
    telescope(&minor_premise_binders, apply_motive(&constructor.result_indices, constructor_application))
}
```

カーネルは $\Nat$ を特別扱いしません。`src/kernel.rs` の `Kernel::standard` は、ユーザーのスクリプトが生成するのと同じ `InductiveSpec` を使って `add_inductive` を呼び、$\Nat$ と $\mathsf{Eq}$ を宣言しています。つまり図 7.1 はハードコードされたものではなく*生成された*もので、`src/inductive/tests.rs` のテストでは、生成された型が手書きのものと一致することを確かめています。

<aside class="warning" markdown="1">

正値性の検査は、便宜のためではなく健全性のために欠かせない要件です。一般の場合（入れ子帰納型と相互帰納型、宇宙制約、ほかの帰納型に言及する添字）は複雑なので、Lean、Coq、Agda のいずれも、カーネルのこの部分で長年にわたってバグを出してきました。本書の制限されたスキーマなら検査は八十行に収まりますが、拡張する際には、新機能を加えるたびに一つのことを問う必要があります。その型を消費する関数から、その型の値を組み立てられてしまわないか、という問いです。

</aside>

## 演習

<div class="exercise" markdown="1">

`inductive Bool where | true | false` に対する再帰子の型 $\mathsf{Bool.rec}_v$ を書き、それを使って否定を定義してください。

<details markdown="1">
<summary>解答</summary>

$\mathsf{Bool.rec}_v : \tPi{M}{\mathsf{Bool} \to \Sort{v}}{M\;\mathsf{true} \to M\;\mathsf{false} \to \tPi{b}{\mathsf{Bool}}{M\;b}}$ です。どちらの構成子もフィールドを持たないので、帰納法の仮定はありません。否定は $\tLam{b}{\mathsf{Bool}}{\mathsf{Bool.rec}_1\;(\tLam{\_}{\mathsf{Bool}}{\mathsf{Bool}})\;\mathsf{false}\;\mathsf{true}\;b}$ と書けます。再帰的フィールドを持たない型の再帰子は、単なる場合分けになるわけです。

</details>

</div>

<div class="exercise" markdown="1">

次の宣言は、それぞれ四つの受理条件のどれによって拒否されるでしょうか。拒否されないものはあるでしょうか。(a) `inductive T : Sort 1 where | mk (f : Sort 1)`。(b) `inductive T : Sort 1 where | mk (f : T -> T)`。(c) `inductive T : Sort 0 where | mk (f : Sort 1)`。

<details markdown="1">
<summary>解答</summary>

(a) 条件 4。フィールド $\Sort{1}$ の型は $\Sort{2}$ で、$u = 1$ を超えます。(b) 条件 3。フィールドの型の中で、$T$ が矢印の左側に現れています。(c) 受理されます。$u = 0$ では条件 4 は何も課さず、この型は型を一つ包み込んだ命題になります。これは $\Sort{0}$ の非述語性の現れですが、$T$ は $\Sort{0}$ へしか消去できない（フィールドが証明でも添字でもないので部分単集合ではない）ため、害はありません。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 宣言は、パラメータと添字を持つ型構成子と、フィールドを持つ構成子を与えます。パラメータは全体を通して固定され、添字は変化して motive の引数になります。
- 再帰子は構成子ごとに小前提を一つ持ち、各小前提は再帰的フィールドごとに帰納法の仮定を一つ持ちます。ι 規則は構成子ごとに一つです。
- 宣言の受理には、整形式性、一様なパラメータ、正格な正値性、宇宙の上限が必要です。このうち再帰を停止させ、論理を整合的に保つのは正値性です。
- 命題は、部分単集合でない限り $\Sort{0}$ へしか消去できません。
- カーネルはこれらをすべてデータから生成し、$\Nat$ 専用のコードは含みません。

</div>
