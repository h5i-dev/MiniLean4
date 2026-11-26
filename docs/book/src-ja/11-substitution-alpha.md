<div class="lead" markdown="1">

代入は変数を項で置き換える操作ですが、うかつに置き換えると、自由変数が束縛子に捕らえられてしまいます。名前をめぐる同じ問題は、文脈や α 同値にも現れます。この章では代入を正確に定義し、続いて「束縛変数の名前を除いて等しい」とはどういうことかを定めます。$\Pi$ 型や宇宙を露わにする弱頭正規化と、定義的等価は第 12 章で扱います。

</div>

## 自由変数と代入

$\Pi$ と $\lambda$ は変数を*束縛*します。$\tLam{x}{A}{t}$ では、$t$ の中に現れる $x$ が引数を指します。束縛子のスコープは本体だけで、注釈 $A$ の中の $x$ は束縛されていません。外側のどの $\Pi$ や $\lambda$ にも束縛されていない変数の出現を、*自由*な出現と呼びます。

<div class="definition" markdown="1">

**定義 11.1（自由変数）.**

$$
\begin{array}{rclcrcl}
\FV(\Sort{u}) &=& \emptyset &\qquad& \FV(\tPi{x}{A}{B}) &=& \FV(A) \cup (\FV(B) \setminus \{x\}) \\[2pt]
\FV(x) &=& \{x\} && \FV(\tLam{x}{A}{t}) &=& \FV(A) \cup (\FV(t) \setminus \{x\}) \\[2pt]
\FV(t\;s) &=& \FV(t) \cup \FV(s) && \FV(c) &=& \emptyset
\end{array}
$$

</div>

たとえば $\FV(\tLam{x}{P}{f\;x\;y}) = \{P, f, y\}$ であり、$\FV(\tPi{P}{\Sort{0}}{P \to P}) = \emptyset$ です。後者のように自由変数を持たない項を*閉じた*項（closed term）といいます。定数は束縛されることがないので、自由変数には何も加えません。

エクスプローラでは、束縛変数がその束縛子と同じ色で塗られ、自由変数には下線が引かれます。変数にカーソルを合わせると、どの束縛子に属するかが分かります。`fun (x : A) => fun (x : A) => x` のように名前がシャドーイングされる項も試してみてください。

<div class="explorer" data-kind="scope" data-term="fun (x : P) => f x y"></div>

$t$ の中の $x$ の自由な出現をすべて $s$ で置き換えた結果を $\subst{t}{x}{s}$ と書きます。ただし、束縛子があると話は単純ではありません。たとえば $\subst{(\tLam{y}{A}{x})}{x}{y}$ の本体は「引数を無視して外側の $x$ を返す」という意味です。ここで $x$ を素朴に $y$ へ置き換えると、自由だった $y$ が束縛子に**捕獲**され、恒等関数 $\tLam{y}{A}{y}$ に変わってしまいます。意味を保つには、置き換える前に束縛子の名前を変えておく必要があります。

<div class="definition" markdown="1">

**定義 11.2（捕獲回避代入）.** $\square \in \{\Pi, \lambda\}$ とします。

$$
\begin{array}{rcll}
\subst{x}{x}{s} &=& s \\[2pt]
\subst{y}{x}{s} &=& y & (y \neq x) \\[2pt]
\subst{\Sort{u}}{x}{s} &=& \Sort{u} \\[2pt]
\subst{c}{x}{s} &=& c \\[2pt]
\subst{(t_1\;t_2)}{x}{s} &=& \subst{t_1}{x}{s}\;\;\subst{t_2}{x}{s} \\[2pt]
\subst{(\square(x{:}A).\,B)}{x}{s} &=& \square(x{:}\subst{A}{x}{s}).\,B & \text{($x$ is shadowed)} \\[2pt]
\subst{(\square(y{:}A).\,B)}{x}{s} &=& \square(y{:}\subst{A}{x}{s}).\,\subst{B}{x}{s} & (y \neq x,\; y \notin \FV(s)) \\[2pt]
\subst{(\square(y{:}A).\,B)}{x}{s} &=& \square(z{:}\subst{A}{x}{s}).\,\subst{(\subst{B}{y}{z})}{x}{s} & (y \neq x,\; y \in \FV(s),\; z \text{ fresh})
\end{array}
$$

ここで「$z$ が新鮮（fresh）」とは $z \notin \FV(s) \cup \FV(B) \cup \{x\}$ を意味します。

</div>

次の例で、束縛子の各場合を一つずつ確かめます。

| 代入 | 結果 | 理由 |
|---|---|---|
| $\subst{(\tPi{h}{P}{P})}{P}{Q}$ | $\tPi{h}{Q}{Q}$ | 捕獲は起こりえません。第 6 章の T-App のステップです |
| $\subst{(\tLam{x}{A}{x})}{x}{s}$ | $\tLam{x}{A}{x}$ | $x$ はシャドーイングされており、本体はそのままです |
| $\subst{(\tLam{y}{x}{y})}{x}{s}$ | $\tLam{y}{s}{y}$ | 注釈は $y$ のスコープの外にあります |
| $\subst{(\tLam{y}{A}{x\;y})}{x}{f\;y}$ | $\tLam{z}{A}{f\;y\;z}$ | $y \in \FV(f\;y)$ なので束縛子を $z$ に改名します |

最後の例では、置き換え項に含まれる自由な $y$ は外側の $y$ を指したままで、束縛変数（いまは $z$）も引数を指したままです。改名しなければ結果は $\tLam{y}{A}{f\;y\;y}$ となり、引数を二度渡す関数になってしまいます。エクスプローラは二通りの代入を並べて実行します。結果に現れる $y$ が置き換え項から来た自由なものなのか、束縛子に捕獲されたものなのかは、色で見分けられます。

<div class="explorer" data-kind="subst" data-term="fun (y : A) => x y" data-var="x" data-with="f y"></div>

<aside class="code" markdown="1">

定義 11.1 と 11.2 は、`src/substitution.rs` の `fv` と `subst` にあたります。以下は `subst` のうち束縛子を扱う部分です。定義にはない近道が一つあり、$x$ が本体に自由に現れなければ本体をそのまま返します。走査が一回省けるうえ、結果は変わりません。

```rust
Term::Pi(y, domain, body) | Term::Lam(y, domain, body) => {
    let substituted_domain = subst(domain, x, replacement);
    let (renamed_binder, substituted_body) = if y == x || !fv(body).contains(x) {
        (y.clone(), (**body).clone())                       // shadowed, or nothing to do
    } else if !fv(replacement).contains(y) {
        (y.clone(), subst(body, x, replacement))            // no capture possible
    } else {
        let mut avoid = all_names(body);                    // capture: rename y to a fresh z
        avoid.extend(all_names(domain));
        avoid.extend(all_names(replacement));
        avoid.insert(x.to_string());
        let z = fresh(y, &avoid);
        let body_with_z = subst(body, y, &var(&z));
        (z, subst(&body_with_z, x, replacement))
    };
    // ... renamed_binder、substituted_domain、substituted_body から Pi または Lam を組み立て直す
}
```

`fresh` 関数は、使われていない名前になるまで、候補の名前にプライムを付け足していきます。避けるべき名前の集合には、自由な名前だけでなく、関係する項に出てくるすべての名前（`all_names`）を使います。定義が求める以上に避けていますが、そのほうが出力が読みやすくなります。

</aside>

## 文脈における変数の捕獲

多くのプログラミング言語と同じように、C-Ext の側条件 $x \notin \dom(\Gamma)$ を外して、新しい仮定が古い仮定を単にシャドーイングするようにしたくなるかもしれません。しかし、そうするとカーネルは健全でなくなります。次の項を考えてみましょう。

$$
t = \tLam{x}{\Sort{0}}{\tLam{y}{x}{\tLam{x}{\Sort{0}}{y}}}.
$$

変数 $y$ の型は*外側の* $x$ で、最も内側の $\lambda$ は引数を使いません。したがって、$t$ の正しい型は次のようになります。

$$
\tPi{x}{\Sort{0}}{\tPi{y}{x}{\tPi{x'}{\Sort{0}}{x}}}.
$$

$\Freshen$ を持たない型検査器は、文脈 $x : \Sort{0},\; y : x,\; x : \Sort{0}$ から $y$ を引き、その型として裸の名前 $x$ を返します。ところがこの時点の $x$ は内側の束縛子を指しているので、型検査器が返す型は

$$
\tPi{x}{\Sort{0}}{\tPi{y}{x}{\tPi{x}{\Sort{0}}{x}}},
$$

となります。これは「どんな型のどんな要素からでも、あらゆる型の要素が作れる」という主張です。$A : \Sort{0}$ と $a : A$ があれば、項 $t\;A\;a$ の型は $\tPi{B}{\Sort{0}}{B}$、つまり False の証明になります。しかも、そのような $A$ と $a$ は空の文脈でも手に入ります。$A = \tPi{P}{\Sort{0}}{P \to P}$ はそれ自体が命題であり、恒等関数 $a = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ がその証明になるからです。

$\Freshen$ があれば、最も内側の束縛子は文脈に入る前に $x'$ へ改名されます。文脈は $x : \Sort{0},\; y : x,\; x' : \Sort{0}$ となり、$y$ を引いて返ってくる $x$ は外側の束縛子を指したままなので、$\Infer$ は上の正しい型を返します。改名が起きる様子は導出エクスプローラで確認できます。最も内側の T-Lam ノードの注記に改名が表示され、葉の文脈には $x'$ が入っています。

<div class="explorer" data-kind="derive" data-term="fun (x : Sort 0) => fun (y : x) => fun (x : Sort 0) => y"></div>

<div class="playground" data-file="capture"><pre># カーネルは内側の x を x' に改名し、正しい型を推論する。
# 内側の x が外側の x をシャドーイングすることを許すカーネルは、
# この項を二つ目の文の証明として受け入れてしまう。二つ目の文は偽である。
goal forall (x : Sort 0), forall (y : x), forall (x' : Sort 0), x
exact fun (x : Sort 0) => fun (y : x) => fun (x : Sort 0) => y
qed
goal forall (x : Sort 0), forall (y : x), forall (x' : Sort 0), x'
exact fun (x : Sort 0) => fun (y : x) => fun (x : Sort 0) => y
qed</pre></div>

代入のときと同じく、問題の根は、名前が別の意味を持つスコープへ持ち込まれることにあります。文脈をリストで持つかハッシュマップで持つかに関係なく、変数を名前で識別する表現はどれもこの問題を抱えます。よく使われる対処法は三つあります。

1. シャドーイングを一切禁止します。最も単純な方法ですが、$A \to B$ が使う予約名 `_` だけは例外とし、文脈には決して加えないようにする必要があります。
2. 文脈に入るときに改名します。$\Freshen$ がこの方法で、本書もこれを採用しています。
3. 束縛変数を位置で表す（**de Bruijn インデックス** [de Bruijn 1972]）か、*locally nameless* 方式を使います。locally nameless 方式では、束縛変数をインデックスで表し、自由変数には一意な識別子を持たせます。Lean 4 が採用しているのはこちらです。

テストスイートには上の $t$ を入れ、カーネルがこれを拒否するか、正しい型を付けるかを確認しておくべきです。

<aside class="warning" markdown="1">

このバグは作り込みやすいうえに、普通の証明はどれも問題なく通るので、なかなか気づけません。入れ子の束縛子でわざと名前を使い回す項を与えて、初めて表に出てきます。カーネルのテストスイートには、正しい証明だけでなく、意地の悪い項（adversarial terms）も必要です。

</aside>

## α 同値

束縛変数の名前そのものに意味はありません。$\tLam{x}{A}{x}$ と $\tLam{y}{A}{y}$ は同じ関数ですし、$\tPi{P}{\Sort{0}}{P \to P}$ と $\tPi{Q}{\Sort{0}}{Q \to Q}$ は同じ命題です。束縛変数の名前だけが異なる項どうしを **α 同値**（alpha-equivalent）といいます。カーネルが型を単なる構文的な一致で比べると、後者の組が拒否されてしまうので、それでは困ります。

<div class="definition" markdown="1">

**定義 11.3（α 同値）.** $\alphaeq$ は、$\square \in \{\Pi, \lambda\}$ について次を含む最小の合同関係です。

$$
\square(x{:}A).\,B \;\alphaeq\; \square(y{:}A).\,\subst{B}{x}{y}
\qquad \text{whenever } y \notin \FV(B).
$$

</div>

（*合同関係*（congruence）とは、すべての項構成子で保たれる同値関係のことで、部分どうしが関係にあれば全体どうしも関係にあります。）この定義は簡潔ですが、どの名前を選べばよいかを教えてくれないので、そのままでは実行できません。そこで実装では、二つの項を並行してたどりながら、それぞれの側でここまでに通過した束縛子のリストを覚えておきます。こうすると束縛変数を、名前ではなく*どの*束縛子を指しているかで識別できます。

この走査を記述するために、$E_1; E_2 \vdash s \alphaeq t$ という形の判断を使います。$E_1$ と $E_2$ は名前のリストで、$E_1$ には $s$ を囲む束縛子が外側から内側の順に、$E_2$ には $t$ を囲む束縛子が記録されます。この判断は「束縛子 $E_1$ の内側にある $s$ と、束縛子 $E_2$ の内側にある $t$ は、束縛変数の名前を除いて同じ項である」と読みます。リストを二つ用意するのは、対応する束縛子に二つの項が別々の名前を付けているかもしれないからです。たとえば $\tLam{x}{A}{\tLam{y}{B}{x}}$ と $\tLam{a}{A}{\tLam{b}{B}{a}}$ を比べると、両側で束縛子を二つずつ通過して

$$
x, y;\; a, b \vdash x \alphaeq a,
$$

に行き着きます。$x$ と $a$ はどちらも二つの束縛子のうち外側を指しているので、これは成り立ちます。項全体を比べるときは、空のリストから $\cdot\,;\cdot \vdash s \alphaeq t$ として始めます。

「同じ束縛子」を正確に表すために、$E$ の中で $x$ が*最後に*現れる位置を右から $0$ 始まりで数えたものを $\mathrm{idx}(E, x)$ とし、$x \notin E$ のときは未定義とします。上の例では $\mathrm{idx}((x, y), x) = \mathrm{idx}((a, b), a) = 1$ です。最後の出現を取ればシャドーイングも正しく扱え、$\tLam{x}{A}{\tLam{x}{B}{x}}$ の本体は内側の $x$ を指します。

<div class="rulebox" markdown="1">

<p class="caption">図 11.1. アルゴリズム的 α 同値。定理 11.4 により、二つの項 $s$ と $t$ が α 同値であることと $\cdot\,;\cdot \vdash s \alphaeq t$ とは同値です。</p>

$$
\dfrac{}{E_1; E_2 \vdash \Sort{u} \alphaeq \Sort{u}}\rulename{$\alpha$-Sort}
\qquad
\dfrac{}{E_1; E_2 \vdash c \alphaeq c}\rulename{$\alpha$-Const}
$$

$$
\dfrac{\mathrm{idx}(E_1, x) = \mathrm{idx}(E_2, y) = i}{E_1; E_2 \vdash x \alphaeq y}\rulename{$\alpha$-Bound}
\qquad
\dfrac{x \notin E_1 \qquad x \notin E_2}{E_1; E_2 \vdash x \alphaeq x}\rulename{$\alpha$-Free}
$$

$$
\dfrac{E_1; E_2 \vdash A \alphaeq A' \qquad E_1, x;\; E_2, y \vdash B \alphaeq B'}{E_1; E_2 \vdash \tPi{x}{A}{B} \alphaeq \tPi{y}{A'}{B'}}\rulename{$\alpha$-Pi}
$$

$$
\dfrac{E_1; E_2 \vdash A \alphaeq A' \qquad E_1, x;\; E_2, y \vdash t \alphaeq t'}{E_1; E_2 \vdash \tLam{x}{A}{t} \alphaeq \tLam{y}{A'}{t'}}\rulename{$\alpha$-Lam}
\qquad
\dfrac{E_1; E_2 \vdash t_1 \alphaeq t_1' \qquad E_1; E_2 \vdash t_2 \alphaeq t_2'}{E_1; E_2 \vdash t_1\;t_2 \alphaeq t_1'\;t_2'}\rulename{$\alpha$-App}
$$

</div>

自由変数は名前で（$\alpha$-Free）、束縛変数は位置で（$\alpha$-Bound）、定数は名前で（$\alpha$-Const）比べます。片側では束縛され、もう片側では自由な変数は何とも等しくならないので、その場合の規則はありません。両側は束縛子をいっしょに下っていくため、$E_1$ と $E_2$ の長さは常に同じです。したがって右から数えた位置を比べても左から数えた位置を比べても結果は同じで、実装では各リストを名前から束縛の深さへの写像として持っても構いません。ただし、束縛子を抜けるときには以前の値を元に戻す必要があります。名前の代わりに*すべての場所で*位置を使うのが **de Bruijn 表現**で、この表現では α 同値な項が構文的にも同一になります。

### 例

第 6 章の最初の例は、推論した型と宣言した型の比較で終わっていました。ここで $P \to P$ は $\tPi{\_}{P}{P}$ の略記です。

<ul class="trace">
<li>$\cdot\,;\cdot \vdash \tPi{P}{\Sort{0}}{\tPi{h}{P}{P}} \alphaeq \tPi{P}{\Sort{0}}{\tPi{\_}{P}{P}}$ <span class="rule">$\alpha$-Pi</span>
  <ul>
  <li>$\cdot\,;\cdot \vdash \Sort{0} \alphaeq \Sort{0}$：成立 <span class="rule">$\alpha$-Sort</span></li>
  <li>$P;\, P \vdash \tPi{h}{P}{P} \alphaeq \tPi{\_}{P}{P}$ <span class="rule">$\alpha$-Pi</span>
    <ul>
    <li>$P;\, P \vdash P \alphaeq P$：成立。どちらもインデックスは $0$ <span class="rule">$\alpha$-Bound</span></li>
    <li>$P, h;\; P, \_ \vdash P \alphaeq P$：成立。どちらもインデックスは $1$ <span class="rule">$\alpha$-Bound</span></li>
    </ul>
  </li>
  </ul>
</li>
</ul>

名前 $h$ と $\_$ は異なりますが、どちらも一度も引かれないので関係ありません。一方、第 6 章の誤った証明は最後のステップで失敗します。

<ul class="trace">
<li>$\cdot\,;\cdot \vdash \tPi{P}{\Sort{0}}{\tPi{h}{P}{\Sort{0}}} \alphaeq \tPi{P}{\Sort{0}}{\tPi{\_}{P}{P}}$ <span class="rule">$\alpha$-Pi</span>
  <ul>
  <li>$\cdot\,;\cdot \vdash \Sort{0} \alphaeq \Sort{0}$：成立 <span class="rule">$\alpha$-Sort</span></li>
  <li>$P;\, P \vdash \tPi{h}{P}{\Sort{0}} \alphaeq \tPi{\_}{P}{P}$ <span class="rule">$\alpha$-Pi</span>
    <ul>
    <li>$P;\, P \vdash P \alphaeq P$：成立 <span class="rule">$\alpha$-Bound</span></li>
    <li class="fail">$P, h;\; P, \_ \vdash \Sort{0} \alphaeq P$：適用できる規則がない</li>
    </ul>
  </li>
  </ul>
</li>
</ul>

位置で比べれば、名前を不用意に比べると取り違えてしまう項も区別できます。$\tLam{x}{A}{\tLam{y}{A}{x}}$ と $\tLam{a}{A}{\tLam{b}{A}{b}}$ は α 同値では*ありません*。本体の比較は $x, y;\, a, b \vdash x \alphaeq b$ に行き着き、$\mathrm{idx}$ は $x$ に $1$、$b$ に $0$ を返すからです。逆に $\tLam{x}{A}{\tLam{x}{A}{x}}$ と $\tLam{a}{A}{\tLam{b}{A}{b}}$ は α 同値*です*。$(x, x)$ の中で最後に現れる $x$ のインデックスは $0$ で、$(a, b)$ の中の $b$ と一致します。

図 11.1 の規則は定義 11.3 とは別の定義なので、両者が一致することを確かめておく必要があります。

<div class="theorem" markdown="1">

**定理 11.4（アルゴリズム的 α 同値の正しさ）.** すべての項 $s$ と $t$ について、定義 11.3 の意味で $s \alphaeq t$ であることと、$\cdot\,;\cdot \vdash s \alphaeq t$ が図 11.1 の規則で導出できることとは同値です。

</div>

証明の要点は、どちらの定義も「$s$ と $t$ の de Bruijn 表現が同じ」と言い換えられることです。アルゴリズムの規則は de Bruijn インデックスとまったく同じやり方で位置を比べているので、アルゴリズムの側はほぼそのままです。定義 11.3 の側では、束縛変数を改名しても de Bruijn 表現が変わらないことが鍵になります。完全な証明は[付録 B](b-proof-alpha.md) にあります。

<aside class="code" markdown="1">

図 11.1 は `src/substitution.rs` の関数 `alpha` にあたります。二つの束縛子リストは `Vec<String>` で、本体を再帰的に比べる前に push し、比べ終えたら pop します。`binder_distance` が $\mathrm{idx}$ の役目を果たし、リストを末尾から探すので、その名前を持つ最も内側の束縛子が最初に見つかります。

```rust
(Term::Var(x), Term::Var(y)) => {
    match (binder_distance(bound_a, x), binder_distance(bound_b, y)) {
        (Some(i), Some(j)) => i == j,     // alpha-Bound
        (None, None) => x == y,           // alpha-Free
        _ => false,                       // bound on one side only
    }
}
```

</aside>

## 演習

<div class="exercise" markdown="1">

$\subst{(\tLam{y}{A}{\tLam{x}{B}{x\;y}})}{x}{y}$ を一歩ずつ計算してください。

<details markdown="1">
<summary>解答</summary>

外側の束縛子 $y$ は置き換え項 $y$ に自由に現れるので、捕獲の場合にあたります。そこで $y$ を新しい名前 $z$ に改名して本体 $\tLam{x}{B}{x\;z}$ を得てから代入します。内側の束縛子は置き換え対象の変数 $x$ そのものなので、内側の本体には手を付けません。結果は $\tLam{z}{A}{\tLam{x}{B}{x\;z}}$ です。内側の $x$ はもともと自由な出現ではないので、実際には何も置き換わっていません。起きたのは、捕獲を避けるための改名だけです。

</details>

</div>

<div class="exercise" markdown="1">

$\tLam{x}{A}{\tLam{y}{A}{y\;x}}$ と $\tLam{y}{A}{\tLam{x}{A}{x\;y}}$ が α 同値かどうかを、図 11.1 を実行して判定してください。

<details markdown="1">
<summary>解答</summary>

α 同値です。$\alpha$-Lam を二回適用すると、束縛子のリストは $x, y$ と $y, x$、本体は $y\;x$ と $x\;y$ になります。$\alpha$-App で $y$ と $x$ を比べるとインデックスは $0$ と $0$、続いて $x$ と $y$ を比べると $1$ と $1$ です。名前は入れ替わっていても、位置は一致しています。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 代入が置き換えるのは自由な出現だけです。置き換え項に束縛子の名前が含まれるとき（捕獲）は、束縛子を改名しなければなりません。
- 同じ捕獲の問題は文脈でも起こります。束縛子が文脈の項目をシャドーイングできるカーネルでは False が証明できてしまいますが、Freshen がこれを防ぎます。
- α 同値では、束縛変数をその束縛子の位置で、自由変数を名前で比べます。図 11.1 がそのアルゴリズムで、定理 11.4 はそれが定義と一致することを保証します。
- 三つとも `src/substitution.rs` にあります（`subst`、`fv`、`alpha`）。

</div>
