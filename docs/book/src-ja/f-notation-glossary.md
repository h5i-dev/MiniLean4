<div class="lead" markdown="1">

本書の記号、判断、専門用語を引くための一覧である。各項目に、それを導入する章を示す。

</div>

## 記法

### 項

| 記法 | 意味 | 章 |
|---|---|---|
| $\Sort{u}$ | レベル $u$ の宇宙。$\Sort{0}$ は命題の宇宙 | [2](02-syntax.md) |
| $x, y, z$ | 変数 | [2](02-syntax.md) |
| $c$ | シグネチャの定数 | [7](07-inductive-nat.md) |
| $\tPi{x}{A}{B}$ | 依存関数型（$\Pi$ 型） | [2](02-syntax.md) |
| $A \to B$ | 非依存の関数型、$\tPi{\_}{A}{B}$ | [2](02-syntax.md) |
| $\tLam{x}{A}{t}$ | 関数（$\lambda$ 抽象） | [2](02-syntax.md) |
| $t\;s$ | 適用。左結合 | [2](02-syntax.md) |
| $h\;a_1 \cdots a_n$ | 背骨。頭部 $h$ を引数に適用したもの | [2](02-syntax.md) |
| $(\vec{x} : \vec{A})$, $\tPi{\vec{x}}{\vec{A}}{B}$ | 束縛のテレスコープと、その上の $\Pi$ | [8](08-inductive-recipe.md) |
| $\FV(t)$ | $t$ の自由変数 | [11](11-substitution-alpha.md) |
| $\subst{t}{x}{s}$ | $t$ の中の $x$ に $s$ を入れる捕獲回避代入 | [11](11-substitution-alpha.md) |
| $\db{t}{E}$ | 束縛子列 $E$ のもとでの $t$ の無名（de Bruijn）形 | [B](b-proof-alpha.md) |
| $\hole{m}$ | 部分的な証明項の中のホール（メタ変数） | [10](10-tactics.md) |

### 判断と関係

| 記法 | 意味 | 章 |
|---|---|---|
| $\Gamma$ | 文脈。仮定 $x : A$ の順序付きリスト | [3](03-typing-rules.md) |
| $\cdot$ | 空の文脈 | [3](03-typing-rules.md) |
| $\dom(\Gamma)$ | $\Gamma$ で仮定されている名前 | [3](03-typing-rules.md) |
| $\ctxok{\Gamma}$ | $\Gamma$ は整形式である | [3](03-typing-rules.md) |
| $\Gamma \vdash t : A$ | $\Gamma$ のもとで $t$ は型 $A$ をもつ | [3](03-typing-rules.md) |
| $\Sigma$ | 定数のシグネチャ | [7](07-inductive-nat.md) |
| $c : C \mathrel{:=} t$ | 本体 $t$ をもつ定義 | [7](07-inductive-nat.md) |
| $\imax(u, v)$ | $v = 0$ なら $0$、そうでなければ $\max(u, v)$ | [3](03-typing-rules.md), [13](13-universes.md) |
| $s \alphaeq t$ | α 同値 | [11](11-substitution-alpha.md) |
| $E_1; E_2 \vdash s \alphaeq t$ | 束縛子リスト $E_1$、$E_2$ のもとでのアルゴリズム的 α 同値 | [11](11-substitution-alpha.md) |
| $\mathrm{idx}(E, x)$ | $E$ における最後の $x$ の位置。右から数える | [11](11-substitution-alpha.md) |
| $t \betared t'$, $t \deltared t'$, $t \iotared t'$ | β 簡約、δ 簡約、ι 簡約 | [3](03-typing-rules.md), [7](07-inductive-nat.md) |
| $t \to t'$ | 任意の種類の簡約 1 ステップ | [12](12-reduction-conversion.md) |
| $s \conv t$ | 定義的等価（変換） | [3](03-typing-rules.md), [12](12-reduction-conversion.md) |
| $\Delta \vdash \varphi$ | 二階命題論理における証明可能性 | [4](04-logic.md) |
| $\varphi^\ast$, $\Delta^\ast$ | 論理式の翻訳、仮定リストの翻訳 | [4](04-logic.md) |
| $\goal{\Gamma}{\hole{m}}{T}$ | ゴール。ホール $m$ のために $\Gamma$ のもとで型 $T$ の項を見つける | [10](10-tactics.md) |

### 標準カーネルの定数

| 記法 | 型 | leanmini での名前 | 章 |
|---|---|---|---|
| $\Nat$ | $\Sort{1}$ | `Nat` | [7](07-inductive-nat.md) |
| $\zero$ | $\Nat$ | `Nat.zero` | [7](07-inductive-nat.md) |
| $\suc$ | $\Nat \to \Nat$ | `Nat.succ` | [7](07-inductive-nat.md) |
| $\NatRec{u}$ | 図 7.1 を参照 | `Nat.rec0`, `Nat.rec1` | [7](07-inductive-nat.md) |
| $\Eq{u}$ | $\tPi{A}{\Sort{u}}{A \to A \to \Sort{0}}$ | `Eq` | [9](09-equality.md) |
| $\refl{u}$ | $\tPi{A}{\Sort{u}}{\tPi{a}{A}{\Eq{u}\;A\;a\;a}}$ | `Eq.refl` | [9](09-equality.md) |
| $\EqRecDep{u,v}$ | 依存除去子。図 9.1 | `Eq.rec0`, `Eq.rec1` | [9](09-equality.md) |
| $\EqRec{u,v}$ | 非依存除去子（定義として与える） | 宣言済みではない | [9](09-equality.md) |
| $\add$, $m + n$ | $\Nat \to \Nat \to \Nat$ | `add`（スクリプト内で定義） | [7](07-inductive-nat.md) |

### アルゴリズム

| 名前 | 役割 | Rust | 章 |
|---|---|---|---|
| $\Infer(\Gamma, t)$ | $t$ の型を計算する | `Kernel::infer` | [5](05-algorithm.md) |
| $\Check(\Gamma, t, T)$ | $t : T$ を検証する | `Kernel::check` | [5](05-algorithm.md) |
| $\InferSort(\Gamma, A)$ | $A$ が型であることを検証し、そのレベルを返す | `Kernel::infer_sort` | [5](05-algorithm.md) |
| $\Freshen(\Gamma, x, b)$ | $\Gamma$ をシャドーイングしてしまう束縛子を改名する | `rename_binder_if_needed` | [5](05-algorithm.md) |
| $\Whnf(t)$ | 弱頭正規形 | `Kernel::whnf` | [12](12-reduction-conversion.md) |
| $\Normalize(t)$ | 完全な正規形 | `Kernel::normalize` | [12](12-reduction-conversion.md) |
| $\IsDefEq(s, t)$ | $s \conv t$ を決定する | `Kernel::is_def_eq` | [12](12-reduction-conversion.md) |

## 用語集

**α 同値（alpha-equivalence）.** 束縛変数の改名を除いた項の等しさで、束縛変数は束縛子の位置で、自由変数は名前で比較して決定する。[第 11 章](11-substitution-alpha.md)。

**β 簡約（beta-reduction）.** 計算ステップ $(\tLam{x}{A}{t})\;s \to \subst{t}{x}{s}$。[第 3 章](03-typing-rules.md) と [第 12 章](12-reduction-conversion.md)。

**捕獲（capture）.** 項の自由変数を束縛する束縛子の下にその項を代入してしまい、意味を変えてしまう誤り。束縛子を改名して回避する。[第 11 章](11-substitution-alpha.md)。

**合流性（confluence）.** 簡約の順序が異なっても同じ正規形に到達するという性質で、正規化によって変換を決定できるのはこの性質のおかげである。[第 12 章](12-reduction-conversion.md)。

**整合性（consistency）.** 型 $\tPi{P}{\Sort{0}}{P}$ をもつ閉じた項が存在しないことで、カーネルの受理に意味を与える性質。[第 4 章](04-logic.md) と [第 14 章](14-properties.md)。

**構成子（constructor）.** $\zero$ や $\suc$ のように、帰納型の値を作る定数で、決して簡約されない。[第 7 章](07-inductive-nat.md)。

**文脈（context）.** 型付けの仮定の順序付きリスト。[第 3 章](03-typing-rules.md)。

**変換（conversion）.** 定義的等価を参照。

**Curry-Howard 対応.** 命題は型であり、証明は項であり、証明の検査は型検査である。[第 1 章](01-propositions-as-types.md)。

**de Bruijn インデックス.** 束縛変数を、その出現と束縛子の間にある束縛子の数で表す表現で、α 同値な項が同一になる。[第 11 章](11-substitution-alpha.md)、[付録 B](b-proof-alpha.md)。

**定義的等価（definitional equality）.** 簡約と α 同値から生成される項の同値関係で、カーネルが決定する。命題的等価と対比される。[第 9 章](09-equality.md) と [第 12 章](12-reduction-conversion.md)。

**δ 簡約（delta-reduction）.** 定義された定数をその本体に展開すること。[第 7 章](07-inductive-nat.md)。

**依存関数型（dependent function type）.** 結果の型が引数に言及してよい $\Pi$ 型で、全称命題の証明の型。[第 1 章](01-propositions-as-types.md)。

**大消去（large elimination）.** 命題の再帰子を使ってデータを作ることで、部分単集合に対してのみ許される。[第 8 章](08-inductive-recipe.md)。

**フィールド（field）.** パラメータ以外の構成子の引数。[第 8 章](08-inductive-recipe.md)。

**ゴール（goal）.** 文脈と、まだ項が見つかっていない型の組。[第 10 章](10-tactics.md)。

**非述語的（impredicative）.** その宇宙自身にわたって量化する型を含む宇宙。$\Sort{0}$ は非述語的で、それより上の宇宙はそうではない。[第 13 章](13-universes.md)。

**添字（index）.** 帰納型の型構成子の引数のうち、構成子ごとに異なってよいもの。ベクトルの長さや等式の右辺など。[第 8 章](08-inductive-recipe.md)。

**帰納法の仮定（induction hypothesis）.** 小前提の中で、再帰的フィールドについて motive がすでに成り立つとする仮定。[第 7 章](07-inductive-nat.md)。

**帰納型（inductive type）.** 構成子によって指定される型で、カーネルはそこから再帰子と ι 規則を生成する。[第 7 章](07-inductive-nat.md) と [第 8 章](08-inductive-recipe.md)。

**ι 簡約（iota-reduction）.** 構成子の適用に対して再帰子を走らせること。[第 7 章](07-inductive-nat.md) と [第 12 章](12-reduction-conversion.md)。

**カーネル（kernel）.** $\Gamma \vdash t : A$ を決定する信頼された部品で、それ以外はすべて、カーネルに渡す項を作るだけである。[第 1 章](01-propositions-as-types.md)。

**大前提（major premise）.** 再帰子の引数のうち、その構成子が ι 規則を選ぶもの。[第 7 章](07-inductive-nat.md)。

**メタ変数（metavariable）.** 部分的な項の中のホールを指す Lean の用語。[第 10 章](10-tactics.md)。

**小前提（minor premise）.** 再帰子の引数のうち、一つの構成子に対する場合を与えるもの。[第 7 章](07-inductive-nat.md)。

**motive.** 各要素に対する再帰子の結果の型を与える関数 $M$。帰納法では述語にあたる。[第 7 章](07-inductive-nat.md)。

**中立項（neutral term）.** 変数を頭部とする正規項（定数があるときは、行き詰まった定数を頭部とするものも含む）。[第 14 章](14-properties.md)、[付録 D](d-proof-consistency.md)。

**正規形（normal form）.** どの簡約ステップも適用できない項。[第 12 章](12-reduction-conversion.md)。

**パラメータ（parameter）.** 帰納型の型構成子の引数のうち、すべての構成子で同じもの。リストの要素の型など。[第 8 章](08-inductive-recipe.md)。

**正格な正値性（strict positivity）.** 再帰的フィールドが帰納型に言及するのは関数の結果としてだけであり、引数としては決して言及しないという条件で、停止性と整合性のために必要である。[第 8 章](08-inductive-recipe.md)。

**述語的（predicative）.** その宇宙にわたって量化する型を含まない宇宙。$u \ge 1$ の $\Sort{u}$。[第 13 章](13-universes.md)。

**証明無関係性（proof irrelevance）.** 一つの命題の任意の二つの証明は定義的に等しいという Lean の規則で、MiniLean4 には実装されていない。[第 13 章](13-universes.md)。

**命題的等価（propositional equality）.** 帰納型 $\Eq{}$ で、その証明は項である。定義的等価と対比される。[第 9 章](09-equality.md)。

**再帰子（recursor）.** 帰納型に対して生成される定数で、構造的再帰と帰納法を表す。[第 7 章](07-inductive-nat.md)。

**シグネチャ（signature）.** 定数とその型の表で、定義については本体も含む。[第 7 章](07-inductive-nat.md)。

**背骨（spine）.** 項を、頭部を引数のリストに適用したものとして見る見方。[第 2 章](02-syntax.md)。

**強正規化（strong normalization）.** 正しく型付けされた項から始まる簡約列はすべて有限である。[第 14 章](14-properties.md)。

**型保存性（subject reduction）.** 簡約は型を保つ。[第 14 章](14-properties.md)。

**部分単集合（subsingleton）.** 構成子が高々一つで、そのフィールドがすべて証明または添字である命題で、任意の宇宙へ消去できる。[第 8 章](08-inductive-recipe.md)。

**構文主導（syntax-directed）.** 項の形が適用すべき規則を決める規則体系。T-Conv を除くすべての型付け規則。[第 5 章](05-algorithm.md)。

**タクティク（tactic）.** カーネルの外にあるプログラムで、証明状態のホールに項を割り当てる。[第 10 章](10-tactics.md)。

**テレスコープ（telescope）.** 後の型が前の変数に言及してよい束縛の列。[第 8 章](08-inductive-recipe.md)。

**輸送（transport）.** $a = b$ の証明に沿って、$a$ についての事実を $b$ についての事実に移すことで、$\Eq{}$ の再帰子で行う。[第 9 章](09-equality.md)。

**宇宙（universe）.** 要素が型であるような型。$\Sort{u}$。[第 2 章](02-syntax.md) と [第 13 章](13-universes.md)。

**弱頭正規形（weak head normal form）.** 項の頭部だけを、最も外側の形が見えるまで簡約した結果。[第 12 章](12-reduction-conversion.md)。

<div class="summary-box" markdown="1">

覚えておくこと

- 項、判断、アルゴリズムにはそれぞれ決まった記法があり、本書を通して一貫して使われる。上の表はそれぞれを Rust 側の対応物に対応づける。
- 二つの等価（定義的と命題的）と二種類の宇宙（非述語的と述語的）は、混同してはならない区別である。

</div>
