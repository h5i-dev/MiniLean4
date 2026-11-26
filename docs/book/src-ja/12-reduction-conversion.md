<div class="lead" markdown="1">

変数名の問題が片づいたので、次は計算を実装します。三種類の簡約を定義し、それを使って弱頭正規化、正規化、定義的等価の判定を行います。帰納型の計算規則はシグネチャにデータとして保存しておくので、一つの簡約関数で宣言済みのどの帰納型も扱えます。

</div>

## 簡約

$\lambda$ 抽象を引数に適用したときは、束縛変数に引数を代入して結果を計算します。

$$
(\tLam{x}{A}{t})\;s \;\betared\; \subst{t}{x}{s}.
$$

このステップを **β 簡約**と呼び、$(\tLam{x}{A}{t})\;s$ の形の部分項を **β 簡約基**（beta-redex）と呼びます。第 II 部では、さらに二種類のステップを加えました。定義を展開する **δ 簡約**（[第 7 章](07-inductive-nat.md)）と、構成子に対して再帰子を走らせる **ι 簡約**（図 7.1 と 9.1、および [第 8 章](08-inductive-recipe.md) の一般規則）です。どのステップも項の内部のどこで行ってもよいことにし、いずれかの種類のステップ一回を $\to$ と書きます。どのステップも適用できない項は**正規形**にあるといいます。たとえば $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$ とすると、

$$
\tLam{h}{\mathit{Id}\;P}{(\tLam{y}{P}{y})\;h} \;\betared\; \tLam{h}{P}{(\tLam{y}{P}{y})\;h} \;\betared\; \tLam{h}{P}{h},
$$

となり、最後の項は正規形です。内側の簡約基から先に簡約しても、結果は同じになります。

## 変換

**定義的等価**は**変換**（conversion）とも呼ばれ、束縛変数の名前を除いて同じ結果に計算される項どうしを同じものとみなします。

<div class="definition" markdown="1">

**定義 12.1（変換）.** $s \conv t$ は、$\alphaeq$ と $\to$ を含み、すべての項構成子について閉じた最小の同値関係です。

</div>

$s \conv t$ を判定するとき、カーネルは両方の項を正規化し、結果を $\alphaeq$ で比較します。この手続きは次の二つの事実に支えられています。

- 簡約は**合流的**です。簡約の順序が違っても、異なる正規形にたどり着くことはありません。したがって $s \conv t$ が成り立つのは $s$ と $t$ の正規形が α 同値であるときであり、そのときに限られるので、うまいステップ列を探し回る必要はありません。
- 型の付く項はどれも正規形を**持つ**ので、正規化は停止します。本書の体系ではこれが成り立ちますが、決して自明ではない定理です（強正規化、[第 14 章](14-properties.md)）[Barendregt 1992]。

実用的なカーネルでは簡約のステップ数にも上限を設けて、バグがあっても無限ループに陥らないようにしています。本書の実装は 20,000 ステップで止まり、「reduction fuel exhausted」というエラーを出します。

<aside class="intuition" markdown="1">

等しさを判定するのに、ステップの連鎖を探すのではなく正規化を使うのはなぜでしょうか。合流性があれば、「これらを等しくする方法が何かあるか」という存在の問いが、「同じ正規形を持つか」という標準形の問いに置き換わり、後者は素直なアルゴリズムで答えられるからです。代わりに正規化は高くつくことがあります。大きな項に展開される定義は、両辺の最初の記号がすでに違っていても、最後まで展開されてしまいます。本番のカーネルは、章末で説明する遅延比較でこれを避けています。

</aside>

## 計算規則をデータとして持つ

図 7.1 と 9.1 では ι 規則を一本ずつ別の等式として書いたので、新しい帰納型を加えるたびにカーネルに新しい簡約コードが要るように見えるかもしれません。実際にはそうではありません。カーネルは ι 規則をデータとして再帰子と並べてシグネチャに保存し、一つのコードがすべての帰納型に対してその規則を適用します。

再帰子の各項目には、**大前提**の位置（どの規則を適用するかを、そこにある構成子が決める引数の位置）と、その帰納型の構成子を記録します。カーネルは各構成子について、先頭の引数のうちいくつが**パラメータ**（規則はこれを無視します）で、いくつが**フィールド**（規則はこれを受け渡します）か、そしてどのフィールドが再帰的かを把握しています。本書の再帰子のうち三つについて、そのデータと、そこから得られる右辺を次に示します（$\lambda$ の型注釈は省略します）。

$$
\begin{array}{llcll}
\textbf{Recursor} & \textbf{Major} & \textbf{Constructor} & \textbf{Params, fields} & \textbf{Right-hand side} \\[2pt]
\NatRec{u} & \text{4th} & \zero & 0,\;0 & \lambda M\,z\,s.\; z \\[2pt]
& & \suc & 0,\;1 & \lambda M\,z\,s\,n.\; s\;n\;(\NatRec{u}\;M\;z\;s\;n) \\[2pt]
\EqRecDep{u,v} & \text{6th} & \refl{u} & 2,\;0 & \lambda A\,a\,M\,m\,b.\; m \\[2pt]
\mathsf{Tree.rec}_v & \text{5th} & \mathsf{leaf} & 0,\;0 & \lambda M\,m_1\,m_2\,m_3.\; m_1 \\[2pt]
& & \mathsf{node} & 0,\;1 & \lambda M\,m_1\,m_2\,m_3\,t.\; m_2\;t\;(\mathsf{Tree.rec}_v\;M\,m_1\,m_2\,m_3\;t) \\[2pt]
& & \mathsf{branch} & 0,\;2 & \lambda M\,m_1\,m_2\,m_3\,l\,r.\; m_3\;l\;r\;(\mathsf{Tree.rec}_v\;M\,m_1\,m_2\,m_3\;l)\;(\cdots\;r)
\end{array}
$$

右辺は、まず大前提より前の引数を受け取り、続いて構成子のフィールドを受け取ります。たとえば $\NatRec{u}\;M\;z\;s\;(\suc\;n)$ では二番目の規則が選ばれ、

$$
(\lambda M\,z\,s\,n.\; s\;n\;(\NatRec{u}\;M\;z\;s\;n))\;M\;z\;s\;n,
$$

となります。これを β 簡約すると、図 7.1 の二番目の等式の右辺が得られます。同様に、$\EqRecDep{u,v}$ のただ一つの規則は $\EqRecDep{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A'\;c)$ に対して発火します。構成子 $\refl{u}$ にはパラメータが二つ（$A'$ と $c$）あり、フィールドはないので、右辺は $A\;a\;M\;m\;b$ だけを受け取って $m$ を返します。

## 弱頭正規形と正規化

アルゴリズム 12.1 では、アルゴリズム 5.1 で未定義のまま残した三つの関数を定義します。$\Whnf$ と $\Normalize$ はどちらも、項を**背骨**（spine）$h\;a_1 \cdots a_n$ として、つまり適用ではない頭部 $h$ に $n \ge 0$ 個の引数を適用したものとして扱います（[第 2 章](02-syntax.md)）。どの項もこの形にちょうど一通りに分解できます。

<div class="rulebox" markdown="1">

<p class="caption">アルゴリズム 12.1. β、δ、ι による弱頭正規化。完全正規化。定義的等価。</p>

```text
Whnf(t):
  loop:
    write t as a spine h a_1 ... a_n
    if h = λ(x : A). b and n ≥ 1:                               -- beta
        t ← (b[x ↦ a_1]) a_2 ... a_n
    else if h = c and (c : C := d) ∈ Σ:                         -- delta
        t ← d a_1 ... a_n
    else if h = c is a recursor with major position p ≤ n:      -- iota
        k b_1 ... b_j ← Whnf(a_p)
        if k is a constructor of c's inductive type with q parameters:
            t ← rhs_k a_1 ... a_{p-1} b_{q+1} ... b_j a_{p+1} ... a_n
        else return t                                           -- stuck, e.g. on a variable
    else return t

Normalize(t):
  t ← Whnf(t)
  if t = Π(x : A). B:  return Π(x : Normalize(A)). Normalize(B)
  if t = λ(x : A). b:  return λ(x : Normalize(A)). Normalize(b)
  else write t as a spine h a_1 ... a_n and return h Normalize(a_1) ... Normalize(a_n)

IsDefEq(s, t):
  return  · ; · ⊢ Normalize(s) =α Normalize(t)                  -- Figure 11.1
```

</div>

$\Whnf$ は項の頭部だけを簡約し、頭部に適用できる規則がなくなるまで続けます。こうして得られるのが**弱頭正規形**です。$\lambda$ や $\Pi$ の内側や、行き詰まった頭部の引数の中には立ち入りません。呼び出し側が型の一番外側の形だけを知りたいとき、たとえば $\Infer$ の適用の場合で $\Pi$ が必要なときにはこれで十分であり、完全な正規化より安く済みます。$\Normalize$ はまず弱頭正規形を求め、次にその直下の部分項をすべて正規化します。たとえば $\mathit{Id}$ を上のとおりとし、$t = \tLam{h}{\mathit{Id}\;P}{h}$ とすると、

$$
\Whnf(t) = t, \qquad \Normalize(t) = \tLam{h}{P}{h},
$$

となります。$t$ の頭部は引数のない $\lambda$ なので弱頭正規化では何も変わりませんが、$\Normalize$ は注釈 $\mathit{Id}\;P$ の中まで進むからです。同様に $\Whnf(\mathit{Id}\;(\mathit{Id}\;P \to P)) = \mathit{Id}\;P \to P$ であり、定義域はまだ正規形ではないものの、$\Pi$ の形はもう見えています。下のエクスプローラで両方を確かめられます。頭部に適用できるステップはないのに、正規形は元の項と異なります。

<div class="explorer" data-kind="reduce" data-term="fun (h : (fun (X : Sort 0) => X) P) => h" data-ctx="P : Sort 0"></div>

$\Whnf$ の三つの場合には、次のような性質があります。

- ι の場合は $\Nat$、$\Eq{}$、$\mathsf{Tree}$ にまったく言及せず、大前提の位置と構成子のデータをシグネチャから読み取ります。このコードは一度書けば済み、新しい帰納型が増えても、加わるのはデータの行であってコードではありません。
- 大前提は計算してはじめて構成子になることがあるので、規則を調べる*前に*弱頭正規形にしておきます。第 7 章の $2 + 1$ では大前提が数字 $1 = \suc\;\zero$ で最初から構成子ですが、$\mathit{double}\;(1 + 1)$ では大前提が $1 + 1$ なので、$\Whnf$ がまずこれを $\suc\;(1 + 0)$ に簡約します。
- 大前提が構成子にならない場合、たとえば変数の場合には、項は**行き詰まり**（stuck）、そのままの形で止まります。$0 + n$ が簡約されないのはこのためです（[第 9 章](09-equality.md)）。

$\mathit{double}$ を第 7 章のとおりに定義し、$\mathit{double}\;(1 + 1)$ に $\Whnf$ を適用した様子をその場で計算して示します。簡約されるのは常に頭部だけですが、大前提を簡約するために内側の計算が必要になります。

<div class="explorer" data-kind="reduce" data-term="double (add (Nat.succ Nat.zero) (Nat.succ Nat.zero))"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def double : Nat -> Nat := fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) Nat.zero (fun (k : Nat) => fun (r : Nat) => Nat.succ (Nat.succ r)) n</pre></div>

*whnf* と記されたステップが内側の計算です。再帰子は大前提が構成子であることを求めるので、まず $1 + 1$ を頭部で簡約します。最終的な弱頭正規形にはまだ行き詰まった内側の再帰子が残っていて、その下に示した正規形は、$\Normalize$ が内側へ進み続けて得たものです。

本書の $\IsDefEq$ は、実装を単純にするため両辺を完全に正規化します。実用的なカーネルでは、両辺を弱頭正規形にして頭部を比べ、必要なときだけ引数を調べます。この遅延比較なら、頭部の時点で違いがわかる大きな項を最後まで正規化せずに済みます。型の付く項に対して三つの関数がどれも停止することは、強正規化によって保証されています。

## コードでは

<aside class="code" markdown="1">

アルゴリズム 12.1 の実装は `src/reduction.rs` にあります。`whnf`、`normalize`、`is_def_eq` は薄いラッパーで、燃料の予算（`REDUCTION_FUEL = 20000`）を確保してから `whnf_with_fuel`、`normalize_with_fuel`、`is_def_eq_with_fuel` を呼びます。`whnf_with_fuel` のループは、アルゴリズムをほぼそのままコードにしたものです。

```rust
let (head, args) = spine(&t);
let reduced = match head {
    // beta: (fun x. b) a_1 a_2 ... a_n  ~>  b[x := a_1] a_2 ... a_n
    Term::Lam(x, _, body) if !args.is_empty() => Some(apps(
        subst(&body, &x, &args[0]),
        args[1..].iter().cloned(),
    )),
    Term::Const(c) => match self.decls.get(&c) {
        // delta: c as  ~>  d as   where (c := d) in Sigma
        Some(Decl { kind: DeclKind::Definition(body), .. }) => Some(apps(body.clone(), args)),
        // iota: I.rec ps M ms is (c_j ps' as)  ~>  m_j as hs
        Some(Decl { kind: DeclKind::Recursor(recursor), .. }) => {
            self.iota_reduce(&c, recursor, &args, fuel)?
        }
        _ => None,
    },
    _ => None,
};
match reduced {
    Some(next) => t = next,
    None => return Ok(t),
}
```

`iota_reduce` は次の手順で動きます。`recursor.major_argument_index` にある大前提を見つけて弱頭正規形にし、その頭部が正しい帰納型の構成子であり、パラメータとフィールドがすべてそろっていることを確かめます。さらに、構成子のパラメータが再帰子のパラメータと変換可能であることも確かめます（型の付く簡約基ならこれは保証されていますが、カーネルは仮定に頼らず検証します）。そのうえで $m_j\;\vec{a}\;\vec{h}$ に残りの引数を続けた項を組み立てます。帰納法の仮定 $\vec{h}$ を作るのは `induction_hypothesis` で、再帰的フィールドごとに、保存してある $\vec{y} : \vec{B}$ と $\vec{s}$ を実際のパラメータとフィールドの値で具体化し、再帰呼び出しを対応する $\lambda$ で包みます。

実装では、上の表のように規則ごとに右辺の*項*を保存するのではなく、そのつど `InductiveInfo` から右辺を計算しています。どちらでも結果は同じですが、その場で計算すれば、構成子データの複製をもう一つ持って同期させ続ける必要がありません。

</aside>

`normalize_with_fuel` には、触れておくべき細かい点が一つあります。引数を正規化すると頭部に新しい簡約基が現れることがあるので、適用の関数部と引数を正規化したあと、組み立て直した項に対してもう一度 `whnf` を呼びます。行き詰まった再帰子の適用で、大前提が自分の引数を正規化してはじめて構成子に*なる*場合には、頭部をもう一度簡約しなければなりません。この再確認がないと `is_def_eq` が一部の等しさを見逃してしまいます。`src/proof.rs` のテスト `conversion_renormalizes_exposed_redex` がこの点を検査しています。

## 演習

<div class="exercise" markdown="1">

$(\tLam{f}{\Nat \to \Nat}{f})\;(\tLam{x}{\Nat}{x})\;\zero$ の弱頭正規形と正規形を求めてください。

<details markdown="1">
<summary>解答</summary>

背骨の頭部は $\tLam{f}{\Nat \to \Nat}{f}$ で、引数は二つです。最初の引数で β 簡約すると $(\tLam{x}{\Nat}{x})\;\zero$ になります。これも頭部が β 簡約基なので、さらに $\zero$ に簡約されます。したがって弱頭正規形も正規形も $\zero$ です。（これはテスト `conversion_renormalizes_exposed_redex` で使っている項です。）

</details>

</div>

<div class="exercise" markdown="1">

$\Whnf$ が $\lambda$ の下を簡約しないのはなぜでしょうか。仮に $\Whnf$ が $b$ を正規化した $\tLam{x}{A}{b}$ を返したとすると、$\Infer$ で何か困ることはあるでしょうか。

<details markdown="1">
<summary>解答</summary>

*困る*ことは何もありません。結果は入力と変換可能なままですが、無駄な仕事が増えます。$\Infer$ が $\Whnf$ を呼ぶのは一番外側の形を知るためだけで、頭部が $\lambda$ になった時点でそれはもうわかっています。内側の簡約は、たとえば何とも比較されない注釈の中などで、いくらでも高くつくことがあります。$\Whnf$ を浅く保っておけば、大きな項でも型推論を安く済ませられます。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 簡約ステップは三つ。β（$\lambda$ を適用する）、δ（定義を展開する）、ι（構成子に対して再帰子を走らせる）。変換は、これらと α 同値から生成される同値関係です。
- 変換は、両辺を正規化して α 同値で比べることで判定します。合流性によってこの判定は正しく、強正規化によって必ず停止します。
- ι 規則は大前提の位置と構成子のメタデータというデータとして保存されるので、一つの `whnf` がすべての帰納型に対して働きます。
- Whnf は頭部だけを簡約し、Infer が必要とするのはこれで十分です。Normalize はあらゆる場所へ進み、IsDefEq はこちらを使います。ステップ数の予算はバグへの備えです。

</div>
