<div class="lead" markdown="1">

本書のスクリプトは leanmini という小さな言語で書かれている。`src/syntax.rs` のパーサと `src/main.rs` のコマンドループが読む言語である。意図的に明示的な言語で、すべての束縛子は型を伴い、すべての引数は書き下され、何も推論されない。この付録はコードから一行ずつ導いた完全なリファレンスであり、リポジトリのすべての例題スクリプトを実行可能な形で収録している。

</div>

## スクリプトの実行

ランナーは `src/main.rs` からビルドされるバイナリ `mini-lean` である。

```text
cargo run -- examples/identity.leanmini    # run a script file
cargo run                                  # interactive session on stdin
cargo test                                 # the kernel's own test suite
```

スクリプトは行の並びである。ランナーは上から下へ処理し、最初のエラーで止まって、メッセージを表示し、ステータス 1 で終了する。空行と `#` で始まる行はコメントで、読み飛ばされる。

```leanmini
# これはコメントである。
goal forall (P : Sort 0), P -> P
```

ファイル引数がなければ、ランナーは利用できるコマンドの一覧を表示したあと、同じコマンドを標準入力から 1 行ずつ読む。エラーは接頭辞 `error:` 付きで報告され、セッションは続く。コマンド `quit`（または `exit`）で終了する。二つのモードで異なるコマンドが一つある。ファイルでは `inductive` ブロックはヘッダ行とそれに続く `|` 行からなるが、対話モードでは `end` だけの行でブロックを閉じる。

<aside class="note" markdown="1">

コマンドラインのランナーは項を Rust の `Debug` 形式で表示する。たとえば `App(Const("Nat.succ"), Const("Nat.zero"))` のようになる。カーネルにプリティプリンタがないからである。本書のプレイグラウンドは同じカーネルを WebAssembly にコンパイルして動かし、その上に項を leanmini の構文で書き戻す小さなプリティプリンタを載せている。また各コマンドを出力の前にエコーするので、記録だけを読んでも内容がわかる。

</aside>

## 項

項は次のいずれかの形で書く。`A`、`B`、`t` は項を、`x` は名前を表す。

| 構文 | 意味 | 本書での記法 |
|---|---|---|
| `Sort 0`、`Sort 1`、... | 宇宙。数字は必須 | $\Sort{u}$ |
| `x` | 変数または定数。スコープで決まる | $x$ または $c$ |
| `forall (x : A), B` | 依存関数型 | $\tPi{x}{A}{B}$ |
| `A -> B` | 非依存の関数型 | $A \to B$ |
| `fun (x : A) => t` | 関数 | $\tLam{x}{A}{t}$ |
| `f a` | 適用 | $f\;a$ |
| `(t)` | グループ化 | |

適用は左結合で、最も強く結合する。`f a b` は `(f a) b` である。矢印は右結合で、`A -> B -> C` は `A -> (B -> C)` である。`forall` や `fun` は可能な限り右まで伸び、矢印の右辺も同様なので、`A -> forall (x : B), C` に括弧は要らない。*引数*として使う `forall` や `fun` は括弧で囲まなければならない。`Nat.rec1 (fun (_n : Nat) => Nat) m` のようにである。矢印 `A -> B` は `forall (_ : A), B` と読まれる。名前 `_` はこの用途のために予約されており、帰納型の宣言で束縛子として使うことはできない。

トークナイザは空白と、文字 `(`、`)`、`,`、`:`、および 2 文字の記号 `->` と `=>` で分割する。名前は英字、数字、`_`、`'`、`.` の並びなので、`Nat.succ`、`List.rec1`、`x'` はそれぞれ一つの名前である。Unicode 文字が三つ、別名として受け付けられる。`->` の代わりの `→`、`fun` の代わりの `λ`、`forall` の代わりの `∀` である。それ以外の文字は `unexpected character: ...` で拒否される。

名前は項の構文解析時に解決され、それより後ではない。

- 外側の `fun` や `forall` で束縛された名前、または現在のゴールの文脈にある名前は**局所変数**である。
- そうでなければ、カーネルに宣言された名前（`inductive`、`def`、`axiom`、`recursor` によるもの、または組み込み）は**定数**である。
- どちらでもなければ構文解析は `unknown identifier: x` で失敗する。構成子の綴りを間違えたときや、まだ導入していない仮定を使ったときにもこのエラーが出る。

局所変数は同名の定数をシャドーイングする。パーサは型を推測しない。`Sort` の後には必ず数字が続き、束縛子は型付きで `(x : A)` と書かなければならない。

## 宣言

### 帰納型

```leanmini
inductive List (A : Sort 1) : Sort 1 where
  | nil
  | cons (head : A) (tail : List A)
```

ヘッダは `inductive Name (p : P) ... (index i : J) ... : Sort u where` の形をとる。括弧で囲まれた各束縛子は**パラメータ**であり、`index` という語で始まるものは**添字**である。パラメータは添字より前になければならない（`parameters must precede indices`）。コロンの後の宇宙はリテラルの `Sort u` でなければならず（`inductive result must be Sort u`）、行は `where` で終わらなければならない。

続く各行は `|` で始まり、構成子を一つ宣言する。`| ctor (field : T) ... [: Name params indices]` の形である。フィールドの型はパラメータ、先行するフィールド、そして `Name` 自身に言及してよい。省略可能なコロンの後の結果型は、`Name` にパラメータを順序どおり変更なしに適用し（`constructor parameters must be uniform`）、その後に添字ごとに一つの添字項を続けたものでなければならない。型に添字があれば、すべての構成子が結果型を明示しなければならない（`indexed constructor requires explicit result type`）。添字がなければ結果型は省略できる。構成子のフィールドに `index` キーワードは使えない。

```leanmini
inductive Vec (A : Sort 1) (index n : Nat) : Sort 1 where
  | nil : Vec A Nat.zero
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)
```

構成子は修飾名で登録される。上の宣言は `Vec.nil` と `Vec.cons` を追加し、`List` の構成子は `List.nil` と `List.cons` である。スクリプトでは修飾形を使わなければならない。

宣言を受理する際には [第 8 章](08-inductive-recipe.md) の四つの条件が検査される。`Name` の型が型であること、各構成子の型が型であって `Name` にパラメータを適用したもので終わること、`Name` に言及するすべてのフィールドが正格な正値性を満たすこと、そして `u` が 1 以上のとき `Sort u` より上の宇宙に属するフィールドがないことである。失敗時のメッセージには `non-strictly-positive / unsupported recursive field`、`field f lives in Sort w, exceeding inductive universe Sort u`、`inductive occurrence inside result index` がある。`_` や `__` で始まる束縛子名は拒否される（`reserved binder name`）。カーネルが自分の生成する束縛子にそのような名前を使うからである。

成功するとランナーは `inductive Name registered` と表示し、カーネルは型構成子、構成子、再帰子 `Name.rec0`、そして大消去が許される場合は `Name.rec1` を追加する。命題（`Sort 0`）が `Name.rec1` を得るのは、[第 8 章](08-inductive-recipe.md) で説明するように部分単集合である場合に限る。

<aside class="warning" markdown="1">

スクリプトファイルでは、`inductive` ブロックの構成子行はヘッダの直後に、間にコメント行を挟まずに続けなければならない。ランナーは `|` で始まる行と空行を集めるので、`#` の行があるとブロックはそこで閉じてしまい、その後の最初の構成子行は `start with 'goal <type>'`（証明の途中なら `unknown command: ...`）として報告される。

</aside>

### 定義と公理

```leanmini
def add : Nat -> Nat -> Nat := fun (m : Nat) => fun (n : Nat) => Nat.rec1 (fun (_n : Nat) => Nat) m (fun (k : Nat) => fun (r : Nat) => Nat.succ r) n
axiom em : forall (P : Sort 0), P -> P
```

`def name : T := t` は、`T` が型であることと、空の文脈で `t : T` であることを検査し、`name` を本体 `t` 付きで追加する。カーネルは簡約の際にこれを展開する（$\delta$ 簡約、[第 12 章](12-reduction-conversion.md)）。ランナーは `defined name` と表示する。定義は 1 行に収めなければならず、最初の `:=` が型と本体を分ける。

`axiom name : T` は、`T` が型であることを検査したうえで、本体なしの `name : T` を追加する。`added axiom name` と表示する。公理は決して展開されない。この方法で偽の命題を仮定することを妨げるものは何もない。カーネルが検査するのは型が整形式であることであって、それが真であることではない。

名前は新しいものでなければならない。再宣言は `duplicate declaration: name` で失敗し、既存の帰納型の名前空間 `Name.rec...` の中には何も宣言できない。

### 追加の再帰子

```leanmini
recursor Nat 2
```

`recursor I v` は、消去宇宙 `v` 向けの `I.recv` がまだなければ生成し、`generated I.recv` と表示する。レベル 0 と 1 は `inductive` が自動的に生成する。動機が `Sort 2` 以上の型を返す必要があるときにこのコマンドを使う。大消去を許さない命題に対しては失敗する（`I is not a subsingleton proposition; cannot eliminate into Sort v`）。

## 標準カーネル

すべてのセッションは `Nat` と `Eq` が宣言済みの状態で始まる。次の宣言を実行したのと同じである。生成される束縛子名は `__` で始まるが、ここでは読みやすさのために `M` と `m` で示す。束縛変数の名前を変えても型は変わらない。

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

`Nat.rec1` は型への再帰、`Nat.rec0` は命題への帰納法である（[第 7 章](07-inductive-nat.md)）。`Eq` は型引数 `A` を明示的にとるので、$\Nat$ における等式 $a = b$ は `Eq Nat a b` と書き、反射性によるその証明は `Eq.refl Nat a` である（[第 9 章](09-equality.md)）。`Eq` は `A : Sort 1` で宣言されているので、等式が使えるのは `Nat` や `List Nat` のような `Sort 1` の型に対してであり、命題に対しては使えない。

一般に、帰納型 `I` の `Sort v` への再帰子は `I.recv` という名前をもつ。`List.rec0`、`List.rec1`、`Vec.rec1` などである。引数の順序は、パラメータ、動機、構成子ごとに一つの小前提（宣言順）、添字、最後に大前提である（[第 8 章](08-inductive-recipe.md)）。

## 証明

### ゴールを始める

```leanmini
goal forall (n : Nat), Eq Nat n n
```

`goal T` は `T` が空の文脈で型であることを検査し、唯一のゴール `?0 : T` をもつ証明を始める。コマンドラインのランナーでは何も表示しない（プレイグラウンドはゴールを表示する）。`goal` より前に与えたタクティクは `start with 'goal <type>'` で失敗する。新しい `goal` を始めると、未完の証明は破棄される。

タクティクを実行するたびに、ランナーは残っているゴールを表示する。各ゴールは、番号、仮定、そしてターンスタイルの後のターゲットからなる。

```text
?3:
  n : Nat
  k : Nat
  ih : Eq Nat (add Nat.zero k) k
  ⊢ Eq Nat (add Nat.zero (Nat.succ k)) (Nat.succ k)
```

ゴールがなくなると `No goals. Run 'qed' to kernel-check.` と表示する。コマンド `show` は何も変えずにゴールを表示する。

タクティクは常に最初のゴールに作用する。タクティクに与える項はそのゴールの文脈で構文解析されるので、仮定の名前がスコープに入っている。各タクティクが部分的な証明項に何をするかは [第 10 章](10-tactics.md) で説明する。この節はインターフェースを述べる。

### タクティク

**`intro x`** は、ターゲットが `forall` または矢印に簡約されることを要求する。`A` を定義域として `x : A` を文脈に加え、本体を新しいターゲットにする。名前は文脈にまだないものでなければならない（`binder name already in context`）。ターゲットの形が合わなければメッセージは `intro expects a Pi/arrow goal` である。

**`exact t`** は、`t` をターゲットに対して検査したうえで、`t` でゴールを閉じる。不一致はカーネルが `type mismatch: actual ..., expected ...` として報告する。

**`apply f`** は `f` の型を推論し、結果がターゲットと定義的に等しくなるまで非依存の矢印を剥がしていく。剥がした各定義域が順に新しいゴールになる。`f` の型が最初からターゲットに一致すれば、`apply f` は `exact f` と同じように振る舞う。依存束縛子は `dependent apply requires elaboration/unification` で拒否され、結果がどこまで剥がしても一致しなければ `apply result does not match the goal` となる。

**`change T`** はターゲットを `T` に置き換える。`T` はターゲットと定義的に等しい型でなければならない（`change expects definitionally equal target`）。計算の後にしか現れない部分項を `rw` の前に露出させるために使う。

**`rfl`** は、ターゲットが `Eq A a b` に簡約され（`rfl expects Eq A lhs rhs`）、`a` と `b` が定義的に等しいこと（`rfl: sides are not definitionally equal`）を要求し、`Eq.refl A a` でゴールを閉じる。

**`rw h`** は、`h` の型が `Eq A a b` に簡約されることを要求する（`rw expects proof of equality`）。ターゲット中の `a` の出現をすべて `b` に置き換え、書き換えたターゲットを新しいゴールとして残す。出現は束縛変数の名前の違いを除いて構文的に探される。計算した後でなければ等しくならない項は見つからず、`rw: no syntactic occurrence of lhs in goal; use change first` となる。Lean の `rw` と違い、その後に `rfl` を試さないので、`Eq A x x` の形のゴールは明示的に閉じなければならない。`a` を抽象化した結果が型の付かない動機になる場合は、証明状態が変わる前にカーネルの型エラーが報告される。

**`induction x`** は、`x` が添字のない帰納型に簡約される型をもつ仮定であること、そして `x` より後の仮定が `x` に言及しないこと（`induction: revert dependent hypotheses first`）を要求する。構成子ごとに一つのゴールを宣言順に作る。各ゴールの文脈には、構成子のフィールドが宣言された名前で加わり、再帰的フィールドごとに `ih` という名前の帰納法の仮定が一つ加わる（`ih` が使用済みならプライムを付け足す）。`Nat.succ` のフィールド `n` は、`n` がすでに使われていれば `k` に改名される。下の例のゴールに `k` と `ih` が現れるのはそのためである。使われる再帰子は `I.recv` で、`v` はターゲットの宇宙である。その再帰子が存在しなければメッセージは `no elimination recursor at target universe` となる。添字付きの族には対応していない（`indexed induction requires motive/index elaboration (not implemented)`）。

**`qed`** はゴールが残っていれば失敗する（`N goals remain`）。そうでなければタクティクのステップから証明項を組み立て、元のゴールに対して検査するためカーネルに送り、`QED. Kernel checked proof:` に続けて項を表示し、証明を終える。この最後の検査が、体系の健全性が依存する唯一のステップである。

それ以外の行は `unknown command: ...` となる。

### カーネルからのエラー

タクティク層ではなくカーネルから来るメッセージもあり、どのコマンドの下でも現れうる。

| メッセージ | 意味 |
|---|---|
| `unbound local: x` | 変数が束縛子の外で使われた。パーサからは生じず、誤って組み立てた項からのみ生じる。 |
| `unknown constant: c` | 定数が削除されたか、宣言されていない。 |
| `application of non-function: ...` | 適用の関数位置が `forall` 型をもたない。 |
| `expected a type, got ...` | 束縛子の注釈、ゴール、または宣言された型が型でない。 |
| `type mismatch: actual ..., expected ...` | 推論された型が要求された型と定義的に等しくない。 |
| `universe overflow` | 宇宙レベルが 64 ビットに収まらない。 |
| `reduction fuel exhausted` | 一回の簡約が 20,000 ステップを超えた。大きな数の加算のような非常に大きな計算で起こる。 |

## 例題スクリプト

`examples/` ディレクトリのすべてのスクリプトをプレイグラウンドとして以下に示す。どれもカーネルで検査済みである。編集して実行を押し、何が変わるかを見てほしい。

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

leanmini はカーネルを理解するための道具であって、証明支援系ではない。次の表は、Lean のフロントエンドがやってくれるがこの言語にはないものを並べたものである。

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

最後の行には実際的な帰結がある。`qed` は証明項を表示して捨てる。結果を再利用するには、項を書き下した `def` として、あるいは `axiom` として述べ直す。

<aside class="lean" markdown="1">

右の列にあるものはすべて、項がカーネルに届く前に Lean のエラボレータとタクティクの枠組みが行う仕事である。Lean のカーネルも我々のものと同じく、完全な項しか見ない。上の制限はこのリポジトリのフロントエンドの制限であって、型理論の制限ではない。

</aside>

<div class="summary-box" markdown="1">

覚えておくこと

- leanmini スクリプトはコマンドの列である。`inductive`、`def`、`axiom`、`recursor`、`goal`、そしてタクティク `intro`、`exact`、`apply`、`change`、`rw`、`rfl`、`induction` があり、`qed` で閉じる。
- 項は完全に明示的である。`Sort u`、`forall (x : A), B`、`fun (x : A) => t`、`A -> B`、そして左結合の適用。
- 構成子と再帰子は修飾名をもつ。`List.cons`、`List.rec1`。`Nat` と `Eq` は宣言済みである。
- フロントエンドは意図的に最小限である。健全性にとって重要なのは、カーネルが行う最後の `qed` の検査だけである。

</div>
