<div class="lead" markdown="1">

第 11 章では名前を扱ったのに対し、本章では計算を扱う。三種類の簡約ステップ、定義的等価の定義、そしてアルゴリズム 5.1 が未定義のまま残した Whnf、Normalize、IsDefEq のアルゴリズムである。設計上の要点は、帰納型の計算規則をシグネチャにデータとして保存することにあり、これにより、一つの簡約関数が、これまでに宣言されたあらゆる帰納型に対して働く。

</div>

## 簡約

$\lambda$ 抽象を引数に適用した結果は、束縛変数に引数を代入して計算する。

$$
(\tLam{x}{A}{t})\;s \;\betared\; \subst{t}{x}{s}.
$$

このステップを **β 簡約**と呼び、$(\tLam{x}{A}{t})\;s$ の形の部分項を **β 簡約基**（beta-redex）と呼ぶ。第 II 部ではさらに二種類のステップを加えた。定義を展開する **δ 簡約**（[第 7 章](07-inductive-nat.md)）と、構成子に対して再帰子を走らせる **ι 簡約**（図 7.1 と 9.1、および [第 8 章](08-inductive-recipe.md) の一般規則）である。各ステップは項の内部のどこで行ってもよいものとし、いずれかの種類の一回のステップを $\to$ と書く。どのステップも適用できない項は**正規形**にある。たとえば $\mathit{Id} = \tLam{X}{\Sort{0}}{X}$ とすると、

$$
\tLam{h}{\mathit{Id}\;P}{(\tLam{y}{P}{y})\;h} \;\betared\; \tLam{h}{P}{(\tLam{y}{P}{y})\;h} \;\betared\; \tLam{h}{P}{h},
$$

であり、最後の項は正規形である。内側の簡約基を先に簡約しても同じ結果に至る。

## 変換

**定義的等価**は**変換**（conversion）とも呼ばれ、束縛変数の名前を除いて同じ結果に計算される項どうしを同一視する。

<div class="definition" markdown="1">

**定義 12.1（変換）.** $s \conv t$ は、$\alphaeq$ と $\to$ を含み、すべての項構成子について閉じた最小の同値関係である。

</div>

$s \conv t$ を判定するために、カーネルは両方の項を正規化し、結果を $\alphaeq$ で比較する。この手続きは二つの事実に依拠している。

- 簡約は**合流的**であり、簡約の順序が違っても、異なる正規形に至ることはない。したがって $s \conv t$ が成り立つのは、$s$ と $t$ の正規形が α 同値であるとき、かつそのときに限り、巧妙なステップ列を探し回る必要はない。
- 型の付くすべての項は正規形を**持つ**ので、正規化は停止する。これは本書の体系で成り立つが、深い定理である（強正規化、[第 14 章](14-properties.md)）[Barendregt 1992]。

実用的なカーネルは簡約ステップ数にも上限を設け、バグがあっても無限ループに陥らないようにする。本書の実装は 20,000 ステップで停止し、「reduction fuel exhausted」というエラーを出す。

<aside class="intuition" markdown="1">

なぜステップの連鎖を探すのではなく、正規化して等しさを判定するのか。合流性があれば、存在の問い（「これらを等しくする何らかの方法があるか」）が標準形の問い（「同じ正規形を持つか」）に変わり、後者には直接的なアルゴリズムがあるからだ。代償として、正規化は高くつくことがあり、大きな項に展開される定義は、両辺が最初の記号から異なっていても完全に展開される。本番のカーネルは、章末で述べる遅延比較でこれを避ける。

</aside>

## データとしての計算規則

図 7.1 と 9.1 では ι 規則を一本ずつ別々の等式として書いており、これを見ると、新しい帰納型ごとにカーネルに新しい簡約コードが要るように思えるが、そうではない。カーネルは ι 規則を再帰子の隣にデータとしてシグネチャに保存し、一つのコードがすべての帰納型に対してそれを適用する。

各再帰子の項目は、**大前提**の位置、つまりどの規則を適用するかをその構成子が決める引数の位置と、その帰納型の構成子を記録する。各構成子について、カーネルは先頭の引数のうちいくつが**パラメータ**（規則はこれを無視する）で、いくつが**フィールド**（規則はこれを引き渡す）か、そしてどのフィールドが再帰的かを知っている。本書の再帰子のうち三つについて、そのデータと、結果として得られる右辺を次に示し、$\lambda$ の型注釈は省略する。

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

右辺は、大前提より前の引数を取り、次に構成子のフィールドを取る。たとえば $\NatRec{u}\;M\;z\;s\;(\suc\;n)$ は二番目の規則を選び、

$$
(\lambda M\,z\,s\,n.\; s\;n\;(\NatRec{u}\;M\;z\;s\;n))\;M\;z\;s\;n,
$$

となり、これを β 簡約すると図 7.1 の二番目の等式の右辺になる。同様に、$\EqRecDep{u,v}$ の唯一の規則は $\EqRecDep{u,v}\;A\;a\;M\;m\;b\;(\refl{u}\;A'\;c)$ に対して発火する。構成子 $\refl{u}$ は二つのパラメータ $A'$ と $c$ を持ち、フィールドを持たないので、右辺は $A\;a\;M\;m\;b$ だけを受け取って $m$ を返す。

## 弱頭正規形と正規化

アルゴリズム 12.1 は、アルゴリズム 5.1 が未定義のまま残した三つの関数を定義する。$\Whnf$ と $\Normalize$ はどちらも項を**背骨**（spine）$h\;a_1 \cdots a_n$、つまり適用ではない頭部 $h$ に $n \ge 0$ 個の引数を適用したものとして見る（[第 2 章](02-syntax.md)）。どの項もこの分解をちょうど一つ持つ。

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

$\Whnf$ は項の頭部でのみ簡約し、そこに適用できる規則がなくなるまで続け、結果が**弱頭正規形**である。$\lambda$ や $\Pi$ の内側、行き詰まった頭部の引数の中は決して見ない。呼び出し側が型の最も外側の形だけを必要とするとき、たとえば $\Infer$ の適用の場合で $\Pi$ が欲しいときには、これで十分であり、完全な正規化より安くつく。$\Normalize$ はまず弱頭正規形を計算し、次に直下の部分項をすべて正規化する。たとえば $t = \tLam{h}{\mathit{Id}\;P}{h}$ とし、$\mathit{Id}$ を上のとおりとすると、

$$
\Whnf(t) = t, \qquad \Normalize(t) = \tLam{h}{P}{h},
$$

である。$t$ の頭部は引数のない $\lambda$ なのに対し、$\Normalize$ は注釈 $\mathit{Id}\;P$ の中まで進むからだ。同様に $\Whnf(\mathit{Id}\;(\mathit{Id}\;P \to P)) = \mathit{Id}\;P \to P$ であり、定義域はまだ正規形でないものの、すでに $\Pi$ の形が見えている。どちらも下で確認でき、頭部に適用できるステップはないのに、正規形は異なる。

<div class="explorer" data-kind="reduce" data-term="fun (h : (fun (X : Sort 0) => X) P) => h" data-ctx="P : Sort 0"></div>

$\Whnf$ の三つの場合には次の性質がある。

- ι の場合は $\Nat$、$\Eq{}$、$\mathsf{Tree}$ への言及を一切含まず、大前提の位置と構成子のデータをシグネチャから読む。これは一度書けば終わりで、以後、新しい帰納型が加えるのはデータの行であってコードではない。
- 大前提は、計算の後で初めて構成子になることがあるので、規則を参照する*前に*弱頭正規形にする。第 7 章の $2 + 1$ では、大前提は数字 $1 = \suc\;\zero$ で、すでに構成子であるが、$\mathit{double}\;(1 + 1)$ では大前提は $1 + 1$ であり、$\Whnf$ がまずこれを $\suc\;(1 + 0)$ にする。
- 大前提が構成子にならなければ、たとえば変数であれば、項は**行き詰まり**（stuck）、そのままの形にとどまる。$0 + n$ が簡約されないのはこのためである（[第 9 章](09-equality.md)）。

$\mathit{double}$ を第 7 章のとおりとして、$\mathit{double}\;(1 + 1)$ に対する $\Whnf$ の動作をその場で計算した結果を示す。簡約されるのは常に頭部だけだが、大前提の簡約が内側の計算を強いる。

<div class="explorer" data-kind="reduce" data-term="double (add (Nat.succ Nat.zero) (Nat.succ Nat.zero))"><pre class="prelude">def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
def double : Nat -> Nat := fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) Nat.zero (fun (k : Nat) => fun (r : Nat) => Nat.succ (Nat.succ r)) n</pre></div>

*whnf* と記されたステップが内側の計算であり、再帰子は大前提が構成子であることを要求するので、まず $1 + 1$ を頭部で簡約する。最終的な弱頭正規形には、行き詰まった内側の再帰子がまだ残っており、その下に示す正規形は、$\Normalize$ が内側へ進み続けて得るものである。

本書の $\IsDefEq$ は、実装を単純にするため両辺を完全に正規化するが、実用的なカーネルは代わりに、両辺を弱頭正規形にして頭部を比較し、必要なときだけ引数を調べる。この遅延比較なら、頭部がすでに異なる大きな項を最後まで正規化せずに済む。型の付く項に対して三つの関数がすべて停止することは、強正規化によって保証される。

## コードでは

<aside class="code" markdown="1">

アルゴリズム 12.1 は `src/reduction.rs` である。`whnf`、`normalize`、`is_def_eq` は薄いラッパーで、燃料の予算（`REDUCTION_FUEL = 20000`）を確保して `whnf_with_fuel`、`normalize_with_fuel`、`is_def_eq_with_fuel` を呼ぶ。`whnf_with_fuel` のループは直訳である。

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

`iota_reduce` は `recursor.major_argument_index` にある大前提を見つけて弱頭正規形にし、その頭部が正しい帰納型の構成子で、パラメータとフィールドがすべて与えられていることを確かめ、構成子のパラメータが再帰子のパラメータと変換可能であることを確かめ（型の付く簡約基ならこれは保証されるが、カーネルは仮定せず検証する）、それから $m_j\;\vec{a}\;\vec{h}$ に残りの引数を続けたものを組み立てる。帰納法の仮定 $\vec{h}$ は `induction_hypothesis` が作るもので、各再帰的フィールドについて保存されている $\vec{y} : \vec{B}$ と $\vec{s}$ を実際のパラメータとフィールドの値で具体化し、再帰呼び出しを対応する $\lambda$ で包む。

上の表のように規則ごとに右辺の*項*を保存する代わりに、実装は毎回 `InductiveInfo` から右辺を計算する。両者は等価であり、その場で計算すれば、構成子データの二つ目の複製を同期し続ける必要がない。

</aside>

`normalize_with_fuel` には触れておくべき細かい点が一つある。引数の正規化が頭部に新しい簡約基を露わにすることがあるので、適用の関数部と引数を正規化した後、組み立て直した項に対してもう一度 `whnf` を呼ぶ。行き詰まった再帰子の適用で、大前提が自身の引数を正規化して初めて構成子に*なる*場合、頭部をもう一度簡約しなければならない。この再検査がなければ `is_def_eq` はいくつかの等しさを見逃し、`src/proof.rs` のテスト `conversion_renormalizes_exposed_redex` がこれを守っている。

## 演習

<div class="exercise" markdown="1">

$(\tLam{f}{\Nat \to \Nat}{f})\;(\tLam{x}{\Nat}{x})\;\zero$ の弱頭正規形と正規形を求めよ。

<details markdown="1">
<summary>解答</summary>

背骨の頭部は $\tLam{f}{\Nat \to \Nat}{f}$ で、引数は二つある。最初の引数で β 簡約すると $(\tLam{x}{\Nat}{x})\;\zero$ になり、これは再び頭部で β 簡約基なので $\zero$ に簡約される。したがって弱頭正規形も正規形も $\zero$ である。（これはテスト `conversion_renormalizes_exposed_redex` の項である。）

</details>

</div>

<div class="exercise" markdown="1">

$\Whnf$ はなぜ $\lambda$ の下で簡約しないのか。$\Whnf$ が $b$ を正規化した $\tLam{x}{A}{b}$ を返したとしたら、$\Infer$ で何がまずくなるか。

<details markdown="1">
<summary>解答</summary>

*まずい*ことは何も起こらず、結果は依然として入力と変換可能であるが、無駄な仕事になる。$\Infer$ が $\Whnf$ を呼ぶのは最も外側の形を知るためだけであり、頭部が $\lambda$ になった時点でそれはもう見えている。内側の簡約は、たとえば何とも比較されない注釈の中など、いくらでも高くつきうる。$\Whnf$ を浅く保つことで、大きな項に対する型推論が安く保たれる。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- 三つの簡約ステップ。β（$\lambda$ を適用する）、δ（定義を展開する）、ι（構成子に対して再帰子を走らせる）。変換は、これらと α 同値が生成する同値関係である。
- 変換は、両辺を正規化して α 同値まで比較することで判定する。合流性によりこれは正しく、強正規化により停止する。
- ι 規則はデータ、つまり大前提の位置と構成子のメタデータであり、一つの `whnf` がすべての帰納型に対して働く。
- Whnf は頭部でのみ簡約し、Infer が必要とするのはこれである一方、Normalize はあらゆる場所へ進み、IsDefEq が使うのはこれである。ステップの予算がバグに備える。

</div>
