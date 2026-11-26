<div class="lead" markdown="1">

この章では、型付け規則を実際に判定できる手順に書き直します。互いに呼び合う二つの関数のうち、`infer` が項の型を求め、`check` がそれを定義的等価で期待される型と比べます。Rust で実装しても数十行です。

</div>

## 規則からアルゴリズムへ

図 3.1 の八つの規則のうち七つは*構文主導*（syntax-directed）で、項を見ればどの規則を使うかが決まります。宇宙なら T-Sort、変数なら T-Var、$\Pi$ なら T-Pi、$\lambda$ なら T-Lam、適用なら T-App です。例外は T-Conv で、この規則はどの項にもいつでも適用できるので、項を見ただけではいつ使えばよいか分かりません。導出を素朴に探索すると、当て推量に頼るしかなくなります。

標準的な解決策は、型検査を二つの関数に分けることです [Barendregt 1992]。

- $\Infer(\Gamma, t)$ は、構文主導の規則に従って $\Gamma$ における $t$ の型を*一つ*計算し、計算できなければ失敗します。
- $\Check(\Gamma, t, T)$ は、$t$ が期待される型 $T$ をもつことを確かめます。具体的には型を推論し、それを定義的等価で $T$ と比較します。

T-Conv を使うのは $\Check$ の内部の一箇所だけです。これとは別に、型が特定の形をしていなければならない場所が二つあります。T-App では $\Pi$ が、T-Pi と T-Lam の前提では宇宙が必要です。そこでアルゴリズムは、推論した型をいちばん外側の形が見えるところまで計算します。

アルゴリズムは項に対する次の二つの関数を使います。定義は [第 12 章](12-reduction-conversion.md) で与えます。

- $\Whnf(T)$ は、いちばん外側の形が見えるまで $T$ を計算します。たとえば $\Whnf(\mathit{Id}\;(P \to P)) = P \to P$ で、結果は $\Pi$ です。
- $\IsDefEq(A, B)$ は $A \conv B$ を決定します。

## 型検査アルゴリズム

アルゴリズム 5.1 に、Rust に近い擬似コードで全体を示します。$\Infer$ の各ケースには、対応する規則を注記しました。

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

このアルゴリズムには次の性質があります。

- **構文主導です。** $\Infer$ の各ケースは、図 3.1 の規則のちょうど一つに対応します。証明を見つけるのは難しくても、与えられた証明の検査は機械的な作業で、どこにも選択の余地はありません。
- **T-Conv が単独で使われることはありません。** 使うのは $\Check$ の内部だけで、推論した型と期待される型が出会うのはそこしかないからです。
- **ある項を型とみなすかどうかは $\InferSort$ が決めます。** 項 $A$ が型であるのは、その型が宇宙に計算されるとき、かつそのときに限ります。たとえば $\lambda$ 抽象は、推論される型が必ず $\Pi$ になるので、決して型にはなりません。
- **$\Freshen$ は C-Ext の付帯条件を実装します。** 文脈にすでにある名前を束縛子が使っていれば、その束縛子を改名します。[第 11 章](11-substitution-alpha.md#variable-capture-in-contexts) では、この手順を省くとカーネルが不健全になる例を示します。
- **文脈は整形式に保たれます。** 仮定を文脈に追加するのは、その型に対する $\InferSort$ が成功した後だけです。そのため空の文脈から始めれば、アルゴリズムが作る文脈はすべて整形式になります。空でない文脈から呼び出す場合は、呼び出し側がその文脈を別途検査しなければなりません。
- **停止性**は $\Whnf$ と $\IsDefEq$ の停止に依存します。正しく型付けされた項については、強正規化（[第 14 章](14-properties.md)）によってこれが保証されます。

<aside class="intuition" markdown="1">

$\Infer$ と $\Check$ への分割は、情報が二つの向きに流れることから、*双方向*（bidirectional）型検査と呼ばれることがあります。推論では情報が葉から*上へ*流れ、変数の型や適用の各部分から項全体の型を組み立てます。一方、検査では利用者が与えた期待される型を*下へ*伝え、根で推論した型と比較します。私たちのカーネルではどの項の型も推論できるので、検査は推論に比較を一回足すだけで済みます。ただ、より豊かな体系には、期待される型があれば検査はできるのに、型を推論できない項もあります。

</aside>

## コードでは

<aside class="code" markdown="1">

アルゴリズム 5.1 に対応するのは、`src/typecheck.rs` の `Kernel::infer`、`Kernel::check`、`Kernel::infer_sort` です。`Freshen` は同じファイルの補助関数 `rename_binder_if_needed` にあたります。以下に `infer` の全体を、第 II 部で加わる定数のケースも含めて載せておくので、擬似コードと一行ずつ見比べたいときに開いてください。

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

擬似コードとの違いがいくつかあります。

- 変数のケースでは、文脈を末尾から（`.rev()`）探します。`rename_binder_if_needed` が名前の重複を防ぐので、一致する項目が二つ以上見つかることはありません。それでも呼び出し側が重複した名前を含む文脈を渡した場合には、末尾から探すのが正しい振る舞いです。
- T-Pi の $\imax$ は `if body_level == 0` の式で実現しています。本体が命題なら $\Pi$ も命題になり、そうでなければ二つのレベルの大きいほうに属します。
- 宇宙レベルは `u64` で表し、`checked_add` でオーバーフローを防いでいます。レベルが $2^{64}$ に近づく証明は現実にはありえませんが、カーネルはどんな入力に対しても未定義動作を起こしてはいけません。
- 適用のケースでは、擬似コードと同じく、`f` の推論された型をマッチする前に `whnf` を呼びます。これがないと、型が $\mathit{Id}\;(A \to B)$ と書かれた関数を適用できません。

残りの二つの関数は短く済みます。

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

`check` は最初に `infer_sort(ctx, expected)` を呼び、期待される型そのものが型であることを確かめます。これは T-Conv の前提 $\Gamma \vdash B : \Sort{u}$ にあたります。アルゴリズムの内部では検査済みの型しか渡さないので擬似コードでは省きましたが、公開された `check` は利用者が書いた主張も受け取るため、Rust 版では検査しています。

最後は `Freshen` です。

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

避ける名前の集合は擬似コードの $\dom(\Gamma) \cup \FV(b)$ より大きく、本体と文脈中の型に現れる名前を、束縛されているか自由かを問わずすべて含みます。必要以上に多くの名前を避けても害はなく、むしろ改名後の項が読みやすくなります。`fresh` は未使用の名前になるまでプライム記号を付け足すので、`x` が衝突すれば `x'` になります。

## Infer の実行を見る

下のエクスプローラは、項に対してアルゴリズムを走らせ、再帰呼び出しをすべて記録します。$\Infer$ のどのケースに、どの文脈で入り、何を返したかを追えます。注記には、$\Whnf$ が $\Pi$ を露わにする、$\Freshen$ が束縛子を改名する、といった表に出ない処理が表示されます。文脈欄には、`Q : Sort 0; q : Q` のようにセミコロン区切りで仮定を書けます。

<div class="explorer" data-kind="derive" data-term="fun (f : P -> Q) => fun (p : P) => f p" data-ctx="P : Sort 0; Q : Sort 0"></div>

## 証明はどう検査されるか

項 $t$ が定理 $T$ の証明になっているかを確かめるには、カーネルは空の文脈で $\Check(\cdot, t, T)$ を実行します。スクリプト言語でこれを担うのが `qed` です。[第 10 章](10-tactics.md) のタクティクが項を組み立て、`qed` がその項を `goal` で与えた主張と一緒に `check` に渡します。その途中にあるものは、どれも信頼する必要がありません。

次の章では、いくつかの項に対して $\Infer$ と $\Check$ を手で実行します。そのなかには、型は正しく付くのに、主張したものを証明していない項も含まれます。

## 演習

<div class="exercise" markdown="1">

$\Infer(\cdot, \tLam{A}{\Sort{1}}{\tLam{a}{A}{a}})$ をトレースし、結果とその宇宙を答えてください。

<details markdown="1">
<summary>解答</summary>

$\InferSort(\cdot, \Sort{1})$ が $2$ を返し、文脈は $A : \Sort{1}$ になります。内側の $\lambda$ では、$\InferSort(A : \Sort{1}, A)$ が $1$ を返して文脈が $A : \Sort{1}, a : A$ になり、$\Infer$ は本体に対して $A$ を返します。したがって内側の結果は $\tPi{a}{A}{A}$、外側の結果は $\tPi{A}{\Sort{1}}{\tPi{a}{A}{A}}$ です。この型に $\InferSort$ を走らせると $\imax(2, \imax(1, 1)) = 2$ となるので、この型は $\Sort{2}$ に属します。

</details>

</div>

<div class="exercise" markdown="1">

$\Pi$ 型は「ただの型」なのに、$\Infer$ の $\Pi$ のケースではなぜ $\Freshen$ を呼ぶのでしょうか。これを省くと結果が変わってしまう項を挙げてください。

<details markdown="1">
<summary>解答</summary>

$\Pi$ の本体も拡張された文脈で検査されるので、$\lambda$ と同じシャドーイングの問題が起きます。$\Gamma = x : \Sort{0}, y : x$ のとき、型 $\tPi{x}{\Sort{1}}{y}$ の検査は失敗すべきです。$y : x$ の $x$ は外側の命題で、命題は宇宙ではないからです。ところが改名しないと、末尾からの探索で内側の $x : \Sort{1}$ が先に見つかり、$y$ の型が $\Sort{1}$ の要素であるかのように扱われて、誤った結果になります。改名すれば内側の束縛子は $x'$ になり、本体は外側の $x$ を指したままです。

</details>

</div>

<div class="summary-box" markdown="1">

覚えておくこと

- $\Infer$ は項の形に従い、$\Check$ は推論してから $\IsDefEq$ で比較します。T-Conv が現れるのは $\Check$ の内部だけです。
- $\Whnf$ は、$\Pi$ や宇宙が要求される場所で、型のいちばん外側の形を露わにします。
- $\InferSort$ は「この項は型か」を判定します。型であるためには、その型が宇宙に計算されなければなりません。
- $\Freshen$ は、文脈の項目をシャドーイングしてしまう束縛子を改名します。これは便宜のためではなく、正しさのために必要です。
- `src/typecheck.rs` はアルゴリズムをほぼそのまま書き写したもので、約 100 行です。

</div>
