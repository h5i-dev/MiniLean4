<div class="lead" markdown="1">

本書のスクリプトは leanmini という言語で書かれており、`src/syntax.rs` が構文解析し、`src/main.rs` が実行します。束縛子にはすべて型を付け、引数もすべて省略せずに書きます。このリファレンスでは言語の仕様を説明し、リポジトリにある例題スクリプトをその場で実行できる形で収めます。

</div>

## スクリプトの実行

スクリプトを実行するランナーは、`src/main.rs` からビルドされるバイナリ `mini-lean` です。

```text
cargo run -- examples/identity.leanmini    # run a script file
cargo run                                  # interactive session on stdin
cargo test                                 # the kernel's own test suite
```

スクリプトは行の並びです。ランナーは上から順に一行ずつ処理し、エラーが出るとそこで止まり、メッセージを表示してステータス 1 で終了します。空行と `#` で始まる行はコメントとして読み飛ばされます。

```leanmini
# これはコメントである。
goal forall (P : Sort 0), P -> P
```

ファイルを指定しないと、ランナーは使えるコマンドの一覧を表示したあと、同じコマンドを標準入力から一行ずつ読み込みます。エラーは `error:` を頭に付けて報告され、セッションはそのまま続きます。終了するにはコマンド `quit`（または `exit`）を入力します。二つのモードで扱いが違うのは `inductive` ブロックだけです。ファイルではヘッダ行とそれに続く `|` 行がブロックになりますが、対話モードでは `end` だけの行でブロックを閉じます。

<aside class="note" markdown="1">

カーネルにはプリティプリンタがないので、コマンドラインのランナーは項を Rust の `Debug` 形式で表示します。たとえば `App(Const("Nat.succ"), Const("Nat.zero"))` のような出力になります。本書のプレイグラウンドは同じカーネルを WebAssembly にコンパイルして動かしており、項を leanmini の構文に戻して表示する小さなプリティプリンタを上に載せています。また、各コマンドを出力の前に表示し直すので、出力だけを読んでも何が起きたかが分かります。

</aside>

## 項

項は次のいずれかの形で書きます。`A`、`B`、`t` は項を、`x` は名前を表します。

| 構文 | 意味 | 本書での記法 |
|---|---|---|
| `Sort 0`、`Sort 1`、... | 宇宙。数字は必須 | $\Sort{u}$ |
| `x` | 変数または定数。スコープで決まる | $x$ または $c$ |
| `forall (x : A), B` | 依存関数型 | $\tPi{x}{A}{B}$ |
| `A -> B` | 非依存の関数型 | $A \to B$ |
| `fun (x : A) => t` | 関数 | $\tLam{x}{A}{t}$ |
| `f a` | 適用 | $f\;a$ |
| `(t)` | グループ化 | |

適用は左結合で、ほかのどの構文よりも強く結び付きます。`f a b` は `(f a) b` の意味です。矢印は右結合で、`A -> B -> C` は `A -> (B -> C)` を表します。`forall` や `fun` はできるだけ右まで続き、矢印の右辺も同様なので、`A -> forall (x : B), C` には括弧が要りません。一方、`forall` や `fun` を*引数*として渡すときは、`Nat.rec1 (fun (_n : Nat) => Nat) m` のように括弧で囲む必要があります。矢印 `A -> B` は `forall (_ : A), B` として読み込まれます。名前 `_` はこのために予約されているので、帰納型の宣言で束縛子の名前には使えません。

トークナイザは、空白と文字 `(`、`)`、`,`、`:`、および 2 文字の記号 `->` と `=>` の位置で入力を区切ります。名前は英字、数字、`_`、`'`、`.` の並びなので、`Nat.succ`、`List.rec1`、`x'` はどれも一つの名前です。Unicode 文字は三つだけ別名として使えます。`->` の代わりの `→`、`fun` の代わりの `λ`、`forall` の代わりの `∀` です。それ以外の文字は `unexpected character: ...` で拒否されます。

名前は、あとからではなく、項を構文解析した時点で解決されます。

- 外側の `fun` や `forall` で束縛された名前と、現在のゴールの文脈にある名前は**局所変数**になります。
- それ以外で、カーネルに宣言済みの名前（`inductive`、`def`、`axiom`、`recursor` で宣言したもの、または組み込みのもの）は**定数**になります。
- どちらにも当たらなければ、構文解析は `unknown identifier: x` で失敗します。構成子の綴りを間違えたときや、まだ導入していない仮定を使ったときにも、このエラーが出ます。

局所変数は同じ名前の定数より優先されます。パーサは型を推測しないので、`Sort` の後には必ず数字を書き、束縛子は `(x : A)` のように型を付けて書く必要があります。

## 宣言

### 帰納型

```leanmini
inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)
```

ヘッダは `inductive Name (p : P) ... (index i : J) ... : Sort u where` という形をしています。括弧で囲んだ束縛子は**パラメータ**で、`index` という語で始まるものは**添字**です。パラメータは添字より前に置く必要があります（`parameters must precede indices`）。コロンの後の宇宙は `Sort u` の形で直接書かなければならず（`inductive result must be Sort u`）、行末は `where` で終えます。

続く各行は `|` で始まり、構成子を一つずつ宣言します。形は `| ctor (field : T) ... [: Name params indices]` です。フィールドの型には、パラメータ、それより前のフィールド、`Name` 自身が出てきても構いません。省略できるコロンの後の結果型は、`Name` にパラメータを順番どおり変えずに適用し（`constructor parameters must be uniform`）、添字ごとに項を一つずつ続けたものでなければなりません。添字のある型では、すべての構成子に結果型を明示する必要があります（`indexed constructor requires explicit result type`）。添字がなければ結果型は省略できます。構成子のフィールドには `index` キーワードを付けられません。

```leanmini
inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where
  | nil : Vec A Nat.zero
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)
```

構成子は型の名前で修飾した名前で登録されます。上の宣言で追加されるのは `Vec.nil` と `Vec.cons` で、`List` の構成子は `List.nil` と `List.cons` です。スクリプトの中でも、この修飾した名前で書く必要があります。

宣言を受け付けるときには、[第 8 章](08-inductive-recipe.md) の四つの条件を検査します。`Name` の型が型であること、各構成子の型が型であり、末尾が `Name` にパラメータを適用した形になっていること、`Name` を含むフィールドがすべて正格に正であること、`u` が 1 以上のとき `Sort u` より上の宇宙に属するフィールドがないこと、の四つです。失敗したときのメッセージには、`non-strictly-positive / unsupported recursive field`、`field f lives in Sort w, exceeding inductive universe Sort u`、`inductive occurrence inside result index` などがあります。また、`_` や `__` で始まる束縛子名は拒否されます（`reserved binder name`）。カーネルが自分で生成する束縛子にこうした名前を使うからです。

宣言に成功すると、ランナーは `inductive Name registered` と表示し、カーネルは型構成子、構成子、再帰子 `Name.rec0` を追加します。大消去が許される場合は `Name.rec1` も加わります。命題（`Sort 0`）が `Name.rec1` を持てるのは、[第 8 章](08-inductive-recipe.md) で説明するように、部分単集合である場合だけです。

<aside class="warning" markdown="1">

スクリプトファイルでは、`inductive` ブロックの構成子行をヘッダのすぐ後に書き、間にコメント行を挟まないでください。ランナーは `|` で始まる行と空行をブロックとして集めるため、`#` の行があるとそこでブロックが終わってしまいます。その後の最初の構成子行は `start with 'goal <type>'`（証明の途中なら `unknown command: ...`）というエラーになります。

</aside>

### 定義と公理

```leanmini
def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
axiom em : forall (P : Sort 0), P -> P
```

`def name : T := t` は、`T` が型であること、空の文脈で `t : T` が成り立つことを検査したうえで、本体 `t` を持つ `name` を追加します。カーネルは簡約の途中でこの定義を展開します（$\delta$ 簡約、[第 12 章](12-reduction-conversion.md)）。ランナーの表示は `defined name` です。定義は 1 行に収める必要があり、最初に現れる `:=` が型と本体の区切りになります。

`axiom name : T` は、`T` が型であることを検査したうえで、本体を持たない `name : T` を追加し、`added axiom name` と表示します。公理が展開されることはありません。カーネルが検査するのは型が正しく作られているかどうかであって、その型が真かどうかではありません。そのため、この方法で偽の命題を仮定しても、止めるものは何もありません。

名前は未使用のものに限ります。同じ名前を宣言し直すと `duplicate declaration: name` で失敗し、既存の帰納型の名前空間 `Name.rec...` の中にも何も宣言できません。

### 追加の再帰子

```leanmini
recursor Nat 2
```

`recursor I v` は、消去先の宇宙 `v` に対応する `I.recv` がまだなければ生成し、`generated I.recv` と表示します。レベル 0 と 1 の再帰子は `inductive` が自動で生成するので、このコマンドが必要になるのは、motive が `Sort 2` 以上の型を返すときです。大消去を許さない命題に対しては失敗します（`I is not a subsingleton proposition; cannot eliminate into Sort v`）。

## 標準カーネル

どのセッションも、`Nat` と `Eq` が宣言済みの状態で始まります。次の宣言をあらかじめ実行したのと同じです。実際に生成される束縛子名は `__` で始まりますが、束縛変数の名前を変えても型は変わらないので、ここでは読みやすさを優先して `M` と `m` と書いています。

```leanmini
Nat      : Sort 1
Nat.zero : Nat
Nat.succ : Nat -> Nat
Nat.rec0 : forall (M : Nat -> Sort 0), M Nat.zero -> (forall (n : Nat), M n -> M (Nat.succ n)) -> forall (x : Nat), M x
Nat.rec1 : forall (M : Nat -> Sort 1), M Nat.zero -> (forall (n : Nat), M n -> M (Nat.succ n)) -> forall (x : Nat), M x

Eq       : forall (A : Sort 1), A -> A -> Sort 0
Eq.refl  : forall (A : Sort 1), forall (a : A), Eq A a a
Eq.rec0  : forall (A : Sort 1), forall (a : A), forall (M : forall (b : A), Eq A a b -> Sort 0), M a (Eq.refl A a) -> forall (b : A), forall (h : Eq A a b), M b h
Eq.rec1  : forall (A : Sort 1), forall (a : A), forall (M : forall (b : A), Eq A a b -> Sort 1), M a (Eq.refl A a) -> forall (b : A), forall (h : Eq A a b), M b h
```

`Nat.rec1` は型への再帰、`Nat.rec0` は命題への帰納法を表します（[第 7 章](07-inductive-nat.md)）。`Eq` は型引数 `A` を明示的に受け取るので、$\Nat$ 上の等式 $a = b$ は `Eq Nat a b` と書き、反射性による証明は `Eq.refl Nat a` となります（[第 9 章](09-equality.md)）。`Eq` は `A : Sort 1` として宣言されているので、等式を使えるのは `Nat` や `List Nat` のような `Sort 1` の型だけで、命題どうしの等式は書けません。

一般に、帰納型 `I` の `Sort v` への再帰子は `I.recv` という名前になります。`List.rec0`、`List.rec1`、`Vec.rec1` などがその例です。引数は、パラメータ、motive、構成子ごとの小前提（宣言順）、添字、最後に大前提の順に並びます（[第 8 章](08-inductive-recipe.md)）。

## 証明

### ゴールを始める

```leanmini
goal forall (n : Nat), Eq Nat n n
```

`goal T` は、`T` が空の文脈で型であることを検査し、ゴールが `?0 : T` 一つだけの証明を始めます。コマンドラインのランナーでは何も表示されません（プレイグラウンドではゴールが表示されます）。`goal` より前にタクティクを書くと `start with 'goal <type>'` で失敗します。新しく `goal` を始めると、終わっていない証明は破棄されます。

タクティクを一つ実行するたびに、ランナーは残っているゴールを表示します。各ゴールは、番号、仮定、そしてターンスタイルの後に続くターゲットからなります。

```text
?3:
  n : Nat
  k : Nat
  ih : Eq Nat (add Nat.zero k) k
  ⊢ Eq Nat (add Nat.zero (Nat.succ k)) (Nat.succ k)
```

ゴールがなくなると `No goals. Run 'qed' to kernel-check.` と表示されます。コマンド `show` を使うと、何も変えずにゴールを表示できます。

タクティクは常に最初のゴールに作用します。タクティクに渡す項はそのゴールの文脈で構文解析されるので、仮定の名前をそのまま使えます。各タクティクが部分的な証明項をどう変えるかは [第 10 章](10-tactics.md) で説明しているので、この節では使い方だけを述べます。

### タクティク

**`intro x`** を使うには、ターゲットが `forall` か矢印に簡約される必要があります。定義域を `A` とすると、`x : A` を文脈に加え、本体を新しいターゲットにします。名前が文脈にすでにあるとエラーになり（`binder name already in context`）、ターゲットの形が合わないときのメッセージは `intro expects a Pi/arrow goal` です。

**`exact t`** は、`t` がターゲットの型を持つことを検査してから、`t` でゴールを閉じます。型が合わなければ、カーネルが `type mismatch: actual ..., expected ...` と報告します。

**`apply f`** は `f` の型を推論し、結果がターゲットと定義的に等しくなるまで非依存の矢印を一つずつ外していきます。外した定義域は、それぞれ順に新しいゴールになります。`f` の型が最初からターゲットと一致していれば、`apply f` は `exact f` と同じ動きをします。依存束縛子があると `dependent apply requires elaboration/unification` で拒否され、いくら外しても一致しなければ `apply result does not match the goal` となります。

**`change T`** はターゲットを `T` に置き換えます。ただし `T` はターゲットと定義的に等しい型でなければなりません（`change expects definitionally equal target`）。計算しないと現れない部分項を、`rw` の前に表に出しておくときに使います。

**`rfl`** を使うには、ターゲットが `Eq A a b` に簡約され（`rfl expects Eq A lhs rhs`）、`a` と `b` が定義的に等しい（`rfl: sides are not definitionally equal`）必要があります。条件を満たせば、`Eq.refl A a` でゴールを閉じます。

**`rw h`** を使うには、`h` の型が `Eq A a b` に簡約される必要があります（`rw expects proof of equality`）。ターゲットに現れる `a` をすべて `b` に置き換え、書き換えたターゲットを新しいゴールとして残します。出現は、束縛変数の名前の違いを無視したうえで構文的に探します。そのため、計算して初めて等しくなる項は見つからず、`rw: no syntactic occurrence of lhs in goal; use change first` となります。Lean の `rw` と違って最後に `rfl` を試さないので、`Eq A x x` の形のゴールが残ったら自分で閉じる必要があります。`a` を抽象化してできる motive に型が付かない場合は、証明状態が変わる前にカーネルの型エラーが報告されます。

**`induction x`** を使うには、`x` が仮定であり、その型が添字のない帰納型に簡約される必要があります。また、`x` より後の仮定が `x` を含んでいてはいけません（`induction: revert dependent hypotheses first`）。構成子ごとにゴールを一つずつ、宣言順に作ります。各ゴールの文脈には、構成子のフィールドが宣言どおりの名前で加わり、再帰的なフィールドごとに `ih` という名前の帰納法の仮定が一つ加わります（`ih` がすでに使われていればプライムを付け足します）。`Nat.succ` のフィールド `n` は、`n` という名前がすでに使われていると `k` に改名されます。下の例のゴールに `k` と `ih` が出てくるのはこのためです。使う再帰子は `I.recv` で、`v` はターゲットの宇宙です。その再帰子がなければ、メッセージは `no elimination recursor at target universe` となります。添字付きの族にはまだ対応していません（`indexed induction requires motive/index elaboration (not implemented)`）。

**`qed`** は、ゴールが残っていれば失敗します（`N goals remain`）。残っていなければ、タクティクの各ステップから証明項を組み立て、元のゴールに対してカーネルに検査させ、`QED. Kernel checked proof:` に続けて項を表示して証明を終えます。体系の健全性が依存しているのは、この最後の検査だけです。

これ以外の行はすべて `unknown command: ...` になります。

### カーネルからのエラー

タクティク層ではなくカーネルから出るメッセージもあり、どのコマンドを実行しているときにも出る可能性があります。

| メッセージ | 意味 |
|---|---|
| `unbound local: x` | 変数が束縛子の外で使われています。パーサが作る項では起こらず、誤って組み立てた項でだけ起こります。 |
| `unknown constant: c` | 定数が削除されたか、宣言されていません。 |
| `application of non-function: ...` | 適用の関数の位置にある項が `forall` 型を持っていません。 |
| `expected a type, got ...` | 束縛子の注釈、ゴール、または宣言した型が型になっていません。 |
| `type mismatch: actual ..., expected ...` | 推論した型が、求められている型と定義的に等しくありません。 |
| `universe overflow` | 宇宙レベルが 64 ビットに収まりません。 |
| `reduction fuel exhausted` | 一回の簡約が 20,000 ステップを超えました。大きな数どうしの加算のような、非常に重い計算で起こります。 |

## 例題スクリプト

`examples/` ディレクトリにあるスクリプトを、すべてプレイグラウンドとして以下に載せます。どれもカーネルで検査済みです。書き換えて実行ボタンを押し、結果がどう変わるかを見てみてください。

### identity.leanmini

<div class="playground" data-file="examples/identity.leanmini"><pre># 命題上の多相的な恒等関数。すべての P について P -&gt; P が成り立つ。
goal forall (P : Sort 0), P -&gt; P
intro P
intro p
exact p
qed</pre></div>

### nat-reflexivity.leanmini

<div class="playground" data-file="examples/nat-reflexivity.leanmini"><pre># すべての自然数は自分自身と等しい。Nat についての帰納法で証明する。
# 両辺が構文的に同じなので、各ケースは rfl で閉じる。
goal forall (n : Nat), Eq Nat n n
intro n
induction n
rfl
rfl
qed</pre></div>

### zero-add.leanmini

<div class="playground" data-file="examples/zero-add.leanmini"><pre># 第二引数についての再帰による加算:
#   add m zero     = m
#   add m (succ k) = succ (add m k)
def add : Nat -&gt; Nat -&gt; Nat := fun (m : Nat) =&gt; fun (n : Nat) =&gt; Nat.rec1 (fun (_n : Nat) =&gt; Nat) m (fun (k : Nat) =&gt; fun (r : Nat) =&gt; Nat.succ r) n

# add zero n = n は定義的には成り立たないので、n についての帰納法が要る。
goal forall (n : Nat), Eq Nat (add Nat.zero n) n
intro n
induction n
# 基底ケース: add zero zero は zero に簡約される。
rfl
# 帰納ステップ: add zero (succ k) を succ (add zero k) に展開し、ih を使う。
change Eq Nat (Nat.succ (add Nat.zero k)) (Nat.succ k)
rw ih
rfl
qed</pre></div>

### generic-list.leanmini

<div class="playground" data-file="examples/generic-list.leanmini"><pre># ユーザが宣言する多相的なリスト。宣言すると List.rec0、List.rec1、... が生成される。
inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)

# induction は Nat に限らず、添字のない帰納型ならどれにでも使える。
goal forall (xs : List Nat), Eq (List Nat) xs xs
intro xs
induction xs
rfl
rfl
qed</pre></div>

### generic-vec.leanmini

<div class="playground" data-file="examples/generic-vec.leanmini"><pre># 長さで添字付けられたベクトル。添字 n は構成子ごとに変わるので、
# ヘッダで `index` キーワードを使って宣言する。
inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where
  | nil : Vec A Nat.zero
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

# 構成子はパラメータ A を明示的にとる。
def one : Vec Nat (Nat.succ Nat.zero) := Vec.cons Nat Nat.zero Nat.zero (Vec.nil Nat)

# タクティク `induction` はまだ添字付きの族に対応していないが、
# カーネルは Vec を直接使う項をそのまま検査できる。
goal Eq (Vec Nat (Nat.succ Nat.zero)) one (Vec.cons Nat Nat.zero Nat.zero (Vec.nil Nat))
rfl
qed</pre></div>

## Lean 4 と比べて欠けているもの

leanmini はカーネルを理解するための道具で、証明支援系として使うものではありません。次の表に、Lean のフロントエンドなら代わりにやってくれるのに、この言語にはない機能をまとめます。

| Lean 4 | leanmini |
|---|---|
| 暗黙の引数。エラボレータが補う | すべての引数が明示的。`a = b` ではなく `Eq Nat a b` |
| メタ変数を解く単一化 | なし。項がすべてを確定させるときにだけタクティクが働く |
| 宇宙多相（レベル変数をもつ `Sort u`） | すべてのレベルが数字。レベルごとに一つの再帰子 |
| 相互帰納型と入れ子帰納型 | 一度に一つの帰納型。フィールドとしての `List Tree` は拒否される |
| 定義的な証明無関係性 | 命題の証明もほかの項と同様に比較される |
| 添字付きの族に対する `induction`、仮定の revert 付き | 添字のない型のみ。依存する仮定は手で revert しなければならない（それを行うタクティクはない） |
| 依存引数をもつ `apply` | 非依存の矢印のみ |
| インスタンスを考慮した `rw`、その後の `rfl` | 構文的な一致のみ。自動の `rfl` はない |
| `simp`、`omega`、その他の自動化 | なし |
| 記法、数値リテラル、名前付きの結果をもつ `theorem` | `Nat.succ (Nat.succ Nat.zero)`。完成した証明は名前で保存されない |

最後の行は実用上の影響があります。`qed` は証明項を表示したあと捨ててしまうので、示した結果を再利用したいときは、項を書き下した `def` として、あるいは `axiom` として、改めて宣言してください。

<aside class="lean" markdown="1">

右の列にある機能はどれも、項がカーネルに届く前に Lean のエラボレータとタクティクの仕組みが担っている仕事です。Lean のカーネルも本書のカーネルと同じく、完全な項しか受け取りません。上に挙げた制限はこのリポジトリのフロントエンドの制限であって、型理論そのものの制限ではありません。

</aside>

<div class="summary-box" markdown="1">

覚えておくこと

- leanmini のスクリプトはコマンドの並びです。コマンドには `inductive`、`def`、`axiom`、`recursor`、`goal` と、タクティク `intro`、`exact`、`apply`、`change`、`rw`、`rfl`、`induction` があり、最後を `qed` で閉じます。
- 項はすべて明示的に書きます。使える形は `Sort u`、`forall (x : A), B`、`fun (x : A) => t`、`A -> B`、そして左結合の適用です。
- 構成子と再帰子は `List.cons`、`List.rec1` のように修飾した名前で呼びます。`Nat` と `Eq` は最初から宣言されています。
- フロントエンドはあえて最小限にしてあります。健全性にとって重要なのは、カーネルが行う最後の `qed` の検査だけです。

</div>
