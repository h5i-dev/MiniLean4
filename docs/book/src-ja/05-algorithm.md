<div class="lead" markdown="1">

型付け規則は、どの判断が成り立つかを述べるが、その確かめ方までは教えてくれない。本章では、仕事を相互再帰する二つの関数に分けて規則をアルゴリズムに変え、一方が項の型を計算し、もう一方が定義的等価を使ってその型を期待される型と比較する。できあがるのは、数十行の Rust である。

</div>

## 規則からアルゴリズムへ

図 3.1 の八つの規則のうち七つは*構文主導*（syntax-directed）であり、項を見ればどの規則が当てはまるか分かる。宇宙なら T-Sort、変数なら T-Var、$\Pi$ なら T-Pi、$\lambda$ なら T-Lam、適用なら T-App が適用される。例外は T-Conv であり、この規則はどの項にもどの時点でも適用できるため、項を見ただけではいつ使うべきか分からない。導出を素朴に探索しようとすれば、当て推量に頼ることになる。

標準的な解決策 [Barendregt 1992] は、型検査を二つの関数に分けることである。

- $\Infer(\Gamma, t)$ は、構文主導の規則に従って $\Gamma$ における $t$ の型を*一つ*計算し、計算できなければ失敗する。
- $\Check(\Gamma, t, T)$ は、$t$ が期待される型 $T$ をもつことを確かめる関数で、型を推論してそれを定義的等価で $T$ と比較する。

T-Conv が適用されるのは、$\Check$ の内部のただ一箇所である。このほかに、型が特定の形をしていなければならない場所が二つあり、T-App における $\Pi$ と、T-Pi および T-Lam の前提における宇宙である。そこでアルゴリズムは、推論した型を、いちばん外側の形が見える程度まで計算する。

アルゴリズムは項に対する二つの関数を使うが、その定義は [第 12 章](12-reduction-conversion.md) に先送りする。

- $\Whnf(T)$ は、いちばん外側の形が見えるまで $T$ を計算する。たとえば $\Whnf(\mathit{Id}\;(P \to P)) = P \to P$ であり、これは $\Pi$ である。
- $\IsDefEq(A, B)$ は $A \conv B$ を決定する。

## アルゴリズム

アルゴリズム 5.1 は、Rust に近い擬似コードで書かれている。$\Infer$ の各ケースには、それが実装する規則を注記してある。

<div class="rulebox" markdown="1">

<p class="caption">アルゴリズム 5.1. 型推論と型検査。</p>

```text
Infer(Γ, t):
  if t = Sort u:                                        -- T-Sort
      return Sort (u + 1)
  if t = x:                                             -- T-Var
      if (x : A) ∈ Γ: return A  else fail "unbound variable"
  if t = Π(x : A). B:                                   -- T-Pi
      u ← InferSort(Γ, A)
      (x', B') ← Freshen(Γ, x, B)
      v ← InferSort((Γ, x' : A), B')
      return Sort (imax(u, v))
  if t = λ(x : A). s:                                   -- T-Lam
      InferSort(Γ, A)
      (x', s') ← Freshen(Γ, x, s)
      B ← Infer((Γ, x' : A), s')
      return Π(x' : A). B
  if t = f a:                                           -- T-App
      T ← Whnf(Infer(Γ, f))
      if T = Π(x : A). B:
          Check(Γ, a, A)
          return B[x ↦ a]
      else fail "not a function"

Check(Γ, t, T):                                         -- T-Conv
  T' ← Infer(Γ, t)
  if IsDefEq(T', T): return  else fail "type mismatch"

InferSort(Γ, A):
  T ← Whnf(Infer(Γ, A))
  if T = Sort u: return u  else fail "expected a type"

Freshen(Γ, x, b):
  if x ∈ dom(Γ):
      choose x' ∉ dom(Γ) ∪ FV(b)
      return (x', b[x ↦ x'])
  else return (x, b)
```

</div>

このアルゴリズムには次の性質がある。

- **構文主導である。** $\Infer$ の各ケースは、図 3.1 の規則のちょうど一つに対応する。証明を見つけるのは難しくても、与えられた証明を検査するのは機械的な作業であり、選択を迫られる場面は一度もない。
- **T-Conv が単独で適用されることはない。** 適用されるのは $\Check$ の内部だけであり、推論した型と期待される型が出会う場所はそこしかない。
- **$\InferSort$ は、カーネルがある項を型とみなすかどうかを決める手段である。** 項 $A$ が型であるのは、その型が宇宙に計算されるとき、そのときに限る。たとえば $\lambda$ 抽象は、推論される型が必ず $\Pi$ になるので、決して型にならない。
- **$\Freshen$ は C-Ext の付帯条件を実装する。** 文脈にすでにある名前をもつ束縛子を改名する。[第 11 章](11-substitution-alpha.md#variable-capture-in-contexts) では、この段階を省くとカーネルが不健全になる項を示す。
- **文脈は整形式のままである。** 仮定が追加されるのはその型に対する $\InferSort$ が成功した後に限られるので、空の文脈から始めると、アルゴリズムが作る文脈はすべて整形式になる。空でない文脈から始める呼び出し側は、その文脈を別途検査しなければならない。
- **停止性**は $\Whnf$ と $\IsDefEq$ が停止することに依存するが、正しく型付けされた項については、強正規化（[第 14 章](14-properties.md)）によってこれが成り立つ。

<aside class="intuition" markdown="1">

$\Infer$ と $\Check$ への分割は、情報が二つの向きに流れることから、*双方向*（bidirectional）型検査と呼ばれることがある。推論は葉から*上へ*進み、変数の型や適用を構成する部分から、項全体の型を求める。一方、検査では利用者が与えた期待される型を*下へ*伝え、根で推論した型と比較する。私たちのカーネルではどの項も型を推論できるので、検査は推論に一回の比較を加えるだけでよいが、より豊かな体系には、期待される型があれば検査できても、型を推論できない項もある。

</aside>

## コードでは

<aside class="code" markdown="1">

アルゴリズム 5.1 は `src/typecheck.rs` の `Kernel::infer`、`Kernel::check`、`Kernel::infer_sort` である。`Freshen` は同じファイルの補助関数 `rename_binder_if_needed` にあたる。`infer` の全体を、第 II 部で加わる定数のケースも含めて以下に示すので、一行ずつ比べたいときに開いてほしい。

</aside>

<details class="code-details" markdown="1">
<summary>infer 関数の全体（約 50 行）</summary>

```rust
pub fn infer(&self, ctx: &Context, t: &Term) -> Result<Term> {
    match t {
        // T-Sort
        Term::Sort(u) => Ok(Term::Sort(u.checked_add(1).ok_or("universe overflow")?)),
        // T-Var
        Term::Var(x) => ctx
            .iter()
            .rev()
            .find(|(name, _)| name == x)
            .map(|(_, ty)| ty.clone())
            .ok_or_else(|| format!("unbound local: {x}")),
        // T-Const（第 7 章）
        Term::Const(c) => self
            .decls
            .get(c)
            .map(|decl| decl.ty.clone())
            .ok_or_else(|| format!("unknown constant: {c}")),
        // T-Pi: Sort 0 は非述語的である。
        Term::Pi(x, domain, body) => {
            let domain_level = self.infer_sort(ctx, domain)?;
            let (x, body) = rename_binder_if_needed(ctx, x, body);
            let mut extended = ctx.clone();
            extended.push((x, (**domain).clone()));
            let body_level = self.infer_sort(&extended, &body)?;
            Ok(Term::Sort(if body_level == 0 {
                0
            } else {
                domain_level.max(body_level)
            }))
        }
        // T-Lam
        Term::Lam(x, domain, body) => {
            self.infer_sort(ctx, domain)?;
            let (x, body) = rename_binder_if_needed(ctx, x, body);
            let mut extended = ctx.clone();
            extended.push((x.clone(), (**domain).clone()));
            let body_type = self.infer(&extended, &body)?;
            Ok(Term::Pi(x, domain.clone(), Box::new(body_type)))
        }
        // T-App
        Term::App(f, a) => match self.whnf(&self.infer(ctx, f)?)? {
            Term::Pi(x, domain, codomain) => {
                self.check(ctx, a, &domain)?;
                Ok(subst(&codomain, &x, a))
            }
            ty => Err(format!("application of non-function: {ty:?}")),
        },
    }
}
```

</details>

擬似コードと異なる点がいくつかある。

- 変数のケースの文脈探索は、末尾から（`.rev()`）探す。`rename_binder_if_needed` が名前の重複を防ぐので一致する項目が二つ以上あることはないが、呼び出し側が重複した名前を含む文脈を渡した場合には、末尾から探すのが正しい振る舞いである。
- T-Pi の $\imax$ は `if body_level == 0` の式であり、本体が命題であるような $\Pi$ は命題、そうでなければ二つのレベルの大きいほうに属する。
- 宇宙レベルは `u64` で、`checked_add` がオーバーフローを防ぐ。レベル $2^{64}$ に近づく証明は現実には存在しないが、カーネルはどんな入力に対しても未定義動作を起こしてはならない。
- 適用のケースは、擬似コードと同じく、`f` の推論された型にマッチする前に `whnf` を呼ぶが、これがなければ、型が $\mathit{Id}\;(A \to B)$ と書かれた関数を適用できない。

残りの二つの関数は短い。

```rust
/// Gamma |- t : expected。T-Conv を使って推論した型を比較する。
pub fn check(&self, ctx: &Context, t: &Term, expected: &Term) -> Result<()> {
    self.infer_sort(ctx, expected)?;
    let actual = self.infer(ctx, t)?;
    if self.is_def_eq(&actual, expected)? {
        Ok(())
    } else {
        Err(format!("type mismatch: actual {actual:?}, expected {expected:?}"))
    }
}

/// t の型を推論し、それが宇宙 Sort u であることを要求する。u を返す。
pub fn infer_sort(&self, ctx: &Context, t: &Term) -> Result<u64> {
    match self.whnf(&self.infer(ctx, t)?)? {
        Term::Sort(u) => Ok(u),
        other => Err(format!("expected a type, got {other:?}")),
    }
}
```

`check` は、期待される型そのものが型であることを確認するため、`infer_sort(ctx, expected)` から始まり、これは T-Conv の前提 $\Gamma \vdash B : \Sort{u}$ にあたる。アルゴリズム内部では検査済みの型しか渡さないため、擬似コードではこの処理を省いたが、公開された `check` は利用者が書いた主張も受け取るので、Rust 版では検査している。

最後に `Freshen` である。

```rust
fn rename_binder_if_needed(ctx: &Context, x: &str, body: &Term) -> (String, Term) {
    if !ctx.iter().any(|(name, _)| name == x) {
        return (x.into(), body.clone());
    }
    let mut used = all_names(body);
    for (name, ty) in ctx {
        used.insert(name.clone());
        used.extend(all_names(ty));
    }
    let renamed = fresh(x, &used);
    let renamed_body = subst(body, x, &var(&renamed));
    (renamed, renamed_body)
}
```

避けるべき名前の集合は、擬似コードの $\dom(\Gamma) \cup \FV(b)$ より大きく、本体と文脈中の型に現れる名前を、束縛か自由かを問わずすべて含む。必要以上に多くの名前を避けても害はなく、改名後の項が読みやすく保たれる。`fresh` は未使用になるまでプライム記号を付け足すので、`x` が衝突すれば `x'` になる。

## Infer の実行を見る

下のエクスプローラは、項に対してアルゴリズムを走らせ、再帰呼び出しをすべて記録するので、$\Infer$ のどのケースに入ったか、どの文脈で、何を返したかが分かる。注記には、$\Whnf$ が $\Pi$ を露わにしたり、$\Freshen$ が束縛子を改名したりといった、表に出ない仕事が記される。文脈欄には `Q : Sort 0; q : Q` のように、セミコロンで区切って仮定を書ける。

<div class="explorer" data-kind="derive" data-term="fun (f : P -> Q) => fun (p : P) => f p" data-ctx="P : Sort 0; Q : Sort 0"></div>

## 証明はどう検査されるか

項 $t$ が定理 $T$ を証明することを確かめるには、カーネルは空の文脈で $\Check(\cdot, t, T)$ を実行する。スクリプト言語ではこれが `qed` の仕事であり、[第 10 章](10-tactics.md) のタクティクが項を組み立て、`qed` がそれを `goal` で与えられた主張とともに `check` に渡す。その間にあるものはすべて信頼されていない。

次の章では、いくつかの項に対して $\Infer$ と $\Check$ を手で実行するが、そのなかには、正しく型付けされているが、主張したものを証明していない項も含まれる。

## 演習

<div class="exercise" markdown="1">

$\Infer(\cdot, \tLam{A}{\Sort{1}}{\tLam{a}{A}{a}})$ をトレースし、結果とその宇宙を答えよ。

<details markdown="1">
<summary>解答</summary>

$\InferSort(\cdot, \Sort{1})$ は $2$ を返し、文脈は $A : \Sort{1}$ になる。内側の $\lambda$ では、$\InferSort(A : \Sort{1}, A)$ が $1$ を返し、文脈は $A : \Sort{1}, a : A$ になり、$\Infer$ は本体に対して $A$ を返す。したがって内側の結果は $\tPi{a}{A}{A}$、外側の結果は $\tPi{A}{\Sort{1}}{\tPi{a}{A}{A}}$ である。この型に $\InferSort$ を走らせると $\imax(2, \imax(1, 1)) = 2$ となるので、この型は $\Sort{2}$ に属する。

</details>

</div>

<div class="exercise" markdown="1">

$\Pi$ 型は「ただの型」なのに、なぜ $\Infer$ の $\Pi$ のケースは $\Freshen$ を呼ぶのか。これを省くと結果が変わる項を挙げよ。

<details markdown="1">
<summary>解答</summary>

$\Pi$ の本体は拡張された文脈で検査されるので、$\lambda$ と同じシャドーイングの問題が起きる。$\Gamma = x : \Sort{0}, y : x$ のとき、型 $\tPi{x}{\Sort{1}}{y}$ は失敗すべきである。$y : x$ の $x$ は外側の命題であり、命題は宇宙ではないからである。改名しなければ、末尾からの探索で内側の $x : \Sort{1}$ が先に見つかり、$y$ の型が $\Sort{1}$ に値をもつかのように見えて、結果が誤る。改名すれば内側の束縛子は $x'$ になり、本体は依然として外側の $x$ を指す。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- $\Infer$ は項の形に従い、$\Check$ は推論してから $\IsDefEq$ で比較する。T-Conv が現れるのは $\Check$ の内部だけである。
- $\Whnf$ は、$\Pi$ や宇宙が要求される場所で、型のいちばん外側の形を露わにする。
- $\InferSort$ は「この項は型か」という検査であり、その型が宇宙に計算されなければならない。
- $\Freshen$ は、文脈の項目をシャドーイングしてしまう束縛子を改名し、これは便宜ではなく、正しさのための要件である。
- `src/typecheck.rs` はアルゴリズムの直訳であり、約 100 行である。

</div>
