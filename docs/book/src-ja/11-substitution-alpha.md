<div class="lead" markdown="1">

代入は変数を項で置き換える操作だが、不用意に行うと自由変数が束縛されてしまう。同じ名前の問題は文脈と α 同値にも及ぶ。ここでは代入を正確に定義し、束縛変数の改名を除いて二つの項が等しいとはどういうことかを定める。$\Pi$ 型や宇宙を露わにする弱頭正規化と定義的等価は第 12 章で扱う。

</div>

## 自由変数と代入

$\Pi$ と $\lambda$ は変数を*束縛*し、$\tLam{x}{A}{t}$ において、$t$ の中に現れる $x$ は引数を指す。束縛子のスコープは本体だけであり、注釈 $A$ の中では $x$ は束縛されない。外側の $\Pi$ や $\lambda$ に束縛されていない変数の出現を*自由*な出現と呼ぶ。

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

たとえば $\FV(\tLam{x}{P}{f\;x\;y}) = \{P, f, y\}$ であり、$\FV(\tPi{P}{\Sort{0}}{P \to P}) = \emptyset$ である。後者は*閉じた*項（closed term）である。定数は決して束縛されないので、自由変数には何も寄与しない。

エクスプローラは各束縛変数をその束縛子と同じ色で塗り、自由変数には下線を引き、変数にカーソルを合わせると束縛子が分かる。`fun (x : A) => fun (x : A) => x` のようなシャドーイングを含む項も試してみてほしい。

<div class="explorer" data-kind="scope" data-term="fun (x : P) => f x y"></div>

$t$ の中の $x$ の自由な出現を $s$ で置き換えた結果を $\subst{t}{x}{s}$ と書くが、束縛子があるときには注意が要る。たとえば $\subst{(\tLam{y}{A}{x})}{x}{y}$ の本体は、「引数を無視して外側の $x$ を返す」という意味である。ところが単純に $x$ を $y$ で置き換えると、自由だった $y$ が束縛子に**捕獲**され、恒等関数 $\tLam{y}{A}{y}$ になってしまう。意味を保つには、代入する前に束縛子を改名しなければならない。

<div class="definition" markdown="1">

**定義 11.2（捕獲回避代入）.** $\square \in \{\Pi, \lambda\}$ とする。

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

ここで「$z$ が新鮮（fresh）」とは $z \notin \FV(s) \cup \FV(B) \cup \{x\}$ を意味する。

</div>

次の例は束縛子の各場合を一つずつ試すものである。

| 代入 | 結果 | 理由 |
|---|---|---|
| $\subst{(\tPi{h}{P}{P})}{P}{Q}$ | $\tPi{h}{Q}{Q}$ | 捕獲は起こりえない。第 6 章の T-App のステップ |
| $\subst{(\tLam{x}{A}{x})}{x}{s}$ | $\tLam{x}{A}{x}$ | $x$ はシャドーイングされており、本体はそのまま |
| $\subst{(\tLam{y}{x}{y})}{x}{s}$ | $\tLam{y}{s}{y}$ | 注釈は $y$ のスコープの外にある |
| $\subst{(\tLam{y}{A}{x\;y})}{x}{f\;y}$ | $\tLam{z}{A}{f\;y\;z}$ | $y \in \FV(f\;y)$ なので束縛子を $z$ に改名する |

最後の例では、置き換え項に含まれる自由な $y$ は依然として外側の $y$ を指し、束縛変数（今は $z$）は依然として引数を指す。改名しなければ結果は $\tLam{y}{A}{f\;y\;y}$ となり、引数を二度渡す関数になってしまう。エクスプローラは二通りの代入を並べて実行し、結果に現れる $y$ が、置き換え項由来の自由なものなのか、束縛子に捕獲されたものなのかは、色で区別できる。

<div class="explorer" data-kind="subst" data-term="fun (y : A) => x y" data-var="x" data-with="f y"></div>

<aside class="code" markdown="1">

定義 11.1 と 11.2 は `src/substitution.rs` の `fv` と `subst` である。`subst` の束縛子の場合を以下に示す。定義と比べて近道が一つ加わっており、$x$ が本体に自由に出現しなければ本体をそのまま返す。これで走査を一回省けるし、結果は変わらない。

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

`fresh` 関数は、名前が未使用になるまでヒントにプライムを付け加える。回避集合は `all_names`、すなわち自由な名前だけでなく関係する項に含まれるすべての名前であり、定義が要求する以上の範囲だが、そのほうが出力が読みやすい。

</aside>

## 文脈における変数の捕獲

C-Ext の側条件 $x \notin \dom(\Gamma)$ を落とし、多くのプログラミング言語と同じように、新しい仮定が古い仮定を単にシャドーイングするようにしたくなるかもしれないが、そうするとカーネルは不健全になる。次の項を考えよう。

$$
t = \tLam{x}{\Sort{0}}{\tLam{y}{x}{\tLam{x}{\Sort{0}}{y}}}.
$$

変数 $y$ の型は*外側の* $x$ であり、最も内側の $\lambda$ は引数を無視するので、$t$ の正しい型は次である。

$$
\tPi{x}{\Sort{0}}{\tPi{y}{x}{\tPi{x'}{\Sort{0}}{x}}}.
$$

$\Freshen$ のない型検査器は、文脈 $x : \Sort{0},\; y : x,\; x : \Sort{0}$ の中で $y$ を引き、その型である裸の名前 $x$ を返すが、この時点で $x$ は内側の束縛子を指しているため、型検査器が返すのは

$$
\tPi{x}{\Sort{0}}{\tPi{y}{x}{\tPi{x}{\Sort{0}}{x}}},
$$

となり、これは「任意の型の任意の要素から、あらゆる型の要素を作れる」と言っている。$A : \Sort{0}$ と $a : A$ が与えられれば、項 $t\;A\;a$ の型は $\tPi{B}{\Sort{0}}{B}$、つまり False の証明になる。そのような $A$ と $a$ は空の文脈にも存在する。$A = \tPi{P}{\Sort{0}}{P \to P}$ はそれ自身が命題であり、恒等関数 $a = \tLam{P}{\Sort{0}}{\tLam{h}{P}{h}}$ がそれを証明するからだ。

$\Freshen$ があれば、最も内側の束縛子は文脈に入る前に $x'$ に改名される。文脈は $x : \Sort{0},\; y : x,\; x' : \Sort{0}$ となり、$y$ を引くと返ってくる $x$ は依然として外側の束縛子を指し、$\Infer$ は上に示した正しい型を返す。導出エクスプローラでこの改名の様子を確認でき、最も内側の T-Lam ノードの注記が改名を報告し、葉の文脈には $x'$ が含まれている。

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

問題は代入の場合と同じで、名前が、別の意味を持つスコープへ移動してしまう。文脈がリストであれハッシュマップであれ、変数を名前で識別する表現はすべてこの影響を受ける。よく使われる対処法は三つある。

1. シャドーイングを一律に拒否するのが最も単純な選択肢だが、$A \to B$ が使う予約名 `_` は例外にして、決して文脈に加えないようにしなければならない。
2. 文脈に入るときに改名する。$\Freshen$ がこれであり、本書の選択でもある。
3. 束縛変数を位置で表す（**de Bruijn インデックス** [de Bruijn 1972]）か、*locally nameless* 方式を使う。後者では束縛変数はインデックスで表し、自由変数は一意な識別子を持ち、Lean 4 は後者の方式を採る。

テストスイートには上の $t$ を含め、カーネルがそれを拒否するか、正しい型を割り当てるかを確認すべきである。

<aside class="warning" markdown="1">

このバグは書いてしまいやすく、普通の証明はすべて通ってしまうので気づきにくい。入れ子の束縛子で意図的に名前を使い回す項だけがこのバグを露わにする。カーネルのテストスイートには、正しい証明だけでなく、敵対的な項（adversarial terms）も必要である。

</aside>

## α 同値

束縛変数の名前には意味がなく、$\tLam{x}{A}{x}$ と $\tLam{y}{A}{y}$ は同じ関数であり、$\tPi{P}{\Sort{0}}{P \to P}$ と $\tPi{Q}{\Sort{0}}{Q \to Q}$ は同じ命題である。束縛変数の名前だけが異なる項を **α 同値**（alpha-equivalent）であるという。カーネルは型を単なる構文的な等しさで比較するわけにはいかず、それでは後者の組が拒否されてしまう。

<div class="definition" markdown="1">

**定義 11.3（α 同値）.** $\alphaeq$ は、$\square \in \{\Pi, \lambda\}$ について次を含む最小の合同関係である。

$$
\square(x{:}A).\,B \;\alphaeq\; \square(y{:}A).\,\subst{B}{x}{y}
\qquad \text{whenever } y \notin \FV(B).
$$

</div>

（*合同関係*（congruence）とは、すべての項構成子で保たれる同値関係である。部分どうしが関係にあれば、全体どうしも関係にある。）この定義は述べるのは簡単だが、どの名前を選ぶべきかを言っていないので、そのままでは実行できない。実装は代わりに両方の項を足並みをそろえてたどり、それぞれの側で、ここまでに通過した束縛子のリストを覚えておく。束縛変数はこうして、名前ではなく*どの*束縛子を指しているかで識別される。

この走査を記述するために、$E_1; E_2 \vdash s \alphaeq t$ という形の判断を使う。$E_1$ と $E_2$ は名前のリストで、$E_1$ は $s$ を囲む束縛子を外側から内側の順に記録し、$E_2$ は $t$ を囲む束縛子を記録する。この判断は「束縛子 $E_1$ の内側に置かれた $s$ と、束縛子 $E_2$ の内側に置かれた $t$ は、束縛変数の名前を除いて同じ項である」と読む。リストが二つ必要なのは、対応する束縛子に二つの項が異なる名前を使うかもしれないからだ。たとえば $\tLam{x}{A}{\tLam{y}{B}{x}}$ と $\tLam{a}{A}{\tLam{b}{B}{a}}$ の比較では、各側で二つの束縛子を通過して

$$
x, y;\; a, b \vdash x \alphaeq a,
$$

に到達し、$x$ と $a$ はどちらも二つの束縛子のうち外側を指すので、これは成り立つ。二つの項全体の比較は、空のリスト $\cdot\,;\cdot \vdash s \alphaeq t$ から始まる。

「同じ束縛子」を正確に言うために、$\mathrm{idx}(E, x)$ を、$E$ における $x$ の*最後の*出現の位置を右から $0$ 始まりで数えたものとし、$x \notin E$ なら未定義とする。上の例では $\mathrm{idx}((x, y), x) = \mathrm{idx}((a, b), a) = 1$ である。最後の出現を取ることでシャドーイングが扱え、$\tLam{x}{A}{\tLam{x}{B}{x}}$ の本体は内側の $x$ を指す。

<div class="rulebox" markdown="1">

<p class="caption">図 11.1. アルゴリズム的 α 同値。定理 11.4 により、二つの項 $s$ と $t$ が α 同値であることと $\cdot\,;\cdot \vdash s \alphaeq t$ とは同値である。</p>

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

自由変数は名前で比較し（$\alpha$-Free）、束縛変数は位置で比較し（$\alpha$-Bound）、定数は名前で比較する（$\alpha$-Const）。一方で束縛され他方で自由な変数は何とも等しくならないので、その場合の規則はない。両側は束縛子を一緒に下っていくので、$E_1$ と $E_2$ の長さは常に等しいので、右から数えた位置の比較は左から数えた位置の比較と同じであり、実装は各リストを名前から束縛の深さへの写像として保持してもよい。ただし束縛子を抜けるときには以前の項目を復元する必要がある。名前の代わりに位置を*あらゆる場所で*使うと **de Bruijn 表現**になり、そこでは α 同値な項は構文的に同一である。

### 例

第 6 章の最初の例は、推論した型と宣言された型の比較で終わった。ここで $P \to P$ は $\tPi{\_}{P}{P}$ の略記である。

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

名前 $h$ と $\_$ は異なるが、どちらも一度も引かれないので問題にならない。第 6 章の誤った証明は、代わりに最後のステップで失敗する。

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

位置は、名前の不注意な比較では混同してしまう項も区別する。$\tLam{x}{A}{\tLam{y}{A}{x}}$ と $\tLam{a}{A}{\tLam{b}{A}{b}}$ は α 同値では*なく*、本体の比較は $x, y;\, a, b \vdash x \alphaeq b$ に到達して、$\mathrm{idx}$ は $x$ に $1$、$b$ に $0$ を与える。逆に $\tLam{x}{A}{\tLam{x}{A}{x}}$ と $\tLam{a}{A}{\tLam{b}{A}{b}}$ は α 同値で*あり*、$(x, x)$ における $x$ の最後の出現のインデックスは $0$ で、$(a, b)$ における $b$ と同じである。

図 11.1 の規則は定義 11.3 とは別の定義なので、両者が一致することを確かめなければならない。

<div class="theorem" markdown="1">

**定理 11.4（アルゴリズム的 α 同値の正しさ）.** すべての項 $s$ と $t$ について、定義 11.3 の意味で $s \alphaeq t$ であることと、$\cdot\,;\cdot \vdash s \alphaeq t$ が図 11.1 の規則で導出できることとは同値である。

</div>

証明の要点は、どちらの定義も「$s$ と $t$ が同じ de Bruijn 表現を持つ」と言い換えられることである。アルゴリズムの規則は de Bruijn インデックスと同じ方法で位置を比較しているので、この言い換えはほぼ直接に分かる。一方、定義 11.3 については、束縛変数を改名しても de Bruijn 表現が変わらないことを示す必要がある。完全な証明は [付録 B](b-proof-alpha.md) にある。

<aside class="code" markdown="1">

図 11.1 は `src/substitution.rs` の関数 `alpha` である。二つの束縛子リストは `Vec<String>` で、本体への再帰呼び出しの前後で push と pop を行う。`binder_distance` が $\mathrm{idx}$ にあたり、リストを末尾から探索するので、その名前を持つ最も近い外側の束縛子までの距離が最初に見つかる。

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

$\subst{(\tLam{y}{A}{\tLam{x}{B}{x\;y}})}{x}{y}$ を一歩ずつ計算せよ。

<details markdown="1">
<summary>解答</summary>

外側の束縛子は $y$ で、これは置き換え項 $y$ に自由に現れるので、捕獲の場合にあたる。$y$ を新鮮な $z$ に改名して本体 $\tLam{x}{B}{x\;z}$ を得てから代入する。内側の束縛子は置き換え対象の変数 $x$ なので、内側の本体には手を付けない。結果は $\tLam{z}{A}{\tLam{x}{B}{x\;z}}$ である。内側の $x$ はもともと自由な出現ではなかったので、実際には何も置き換わっておらず、唯一の効果は、捕獲回避が強いた改名である。

</details>

</div>

<div class="exercise" markdown="1">

$\tLam{x}{A}{\tLam{y}{A}{y\;x}}$ と $\tLam{y}{A}{\tLam{x}{A}{x\;y}}$ が α 同値かどうかを、図 11.1 を実行して判定せよ。

<details markdown="1">
<summary>解答</summary>

同値である。$\alpha$-Lam を二回適用すると、束縛子のリストは $x, y$ と $y, x$、本体は $y\;x$ と $x\;y$ になる。$\alpha$-App で $y$ と $x$ を比べるとインデックスは $0$ と $0$、続いて $x$ と $y$ を比べると $1$ と $1$ になる。名前は入れ替わっていても、位置が一致するので同値である。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 代入は自由な出現だけを置き換え、置き換え項が束縛子の名前を含むとき（捕獲）は、束縛子を改名しなければならない。
- 同じ捕獲の問題は文脈でも起こり、束縛子が文脈の項目をシャドーイングすることを許すカーネルは False を証明できてしまうが、Freshen がこれを防ぐ。
- α 同値は、束縛変数をその束縛子の位置で、自由変数を名前で比較する。図 11.1 がそのアルゴリズムであり、定理 11.4 はそれが定義と一致することを述べる。
- 三つとも `src/substitution.rs` にあり、`subst`、`fv`、`alpha` である。

</div>
