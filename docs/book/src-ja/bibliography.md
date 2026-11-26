<div class="lead" markdown="1">

本書で使った文献を、その結果を参照する箇所とともに挙げます。

</div>

- **[Barendregt 1992]** H. P. Barendregt. Lambda calculi with types. In *Handbook of Logic in Computer Science*, volume 2, Oxford University Press, 1992. 純粋型システムの標準的な参照文献です。型検査を推論と検査に分ける双方向の手法（[第 5 章](05-algorithm.md)）と、[第 14 章](14-properties.md)および[付録 D](d-proof-consistency.md)で用いる型の一意性、生成、合流性、型保存性といったメタ理論は、この文献に拠っています。

- **[Carneiro 2019]** M. Carneiro. *The Type Theory of Lean*. Master's thesis, Carnegie Mellon University, 2019. 定義的な証明無関係性とそれに伴う微妙な点も含めて、Lean の実際の型理論を精密に記述しています。Lean の完全なシステムが本書のシステムを超える点について、[第 13 章](13-universes.md)と[第 14 章](14-properties.md)で引用します。

- **[Coquand and Huet 1988]** T. Coquand and G. Huet. The calculus of constructions. *Information and Computation*, 76(2-3):95-120, 1988. 本書の中核をなすシステムで、命題の非述語的な宇宙を備えた依存型の体系です。その整合性の結果が、[第 13 章](13-universes.md)の宇宙の設計の根拠になっています。

- **[de Bruijn 1972]** N. G. de Bruijn. Lambda calculus notation with nameless dummies, a tool for automatic formula manipulation, with application to the Church-Rosser theorem. *Indagationes Mathematicae*, 34(5):381-392, 1972. 束縛変数を名前なしで表す方法を導入しました。[第 11 章](11-substitution-alpha.md)で扱う、変数の捕獲への三つの対処法の一つであり、[付録 B](b-proof-alpha.md)では α 同値の二つの定義をつなぐ橋になります。

- **[Girard 1972]** J.-Y. Girard. *Interpretation fonctionnelle et elimination des coupures de l'arithmetique d'ordre superieur*. PhD thesis, Universite Paris VII, 1972. 非述語的なシステムの強正規化を支える方法である可約性候補（reducibility candidates）を導入し（[第 14 章](14-properties.md)）、自分自身を含む宇宙が矛盾することを示すパラドックスを与えました（[第 13 章](13-universes.md)）。

- **[Hurkens 1995]** A. J. C. Hurkens. A simplification of Girard's paradox. In *Typed Lambda Calculi and Applications (TLCA)*, LNCS 902, pages 266-278, Springer, 1995. $\mathsf{Type} : \mathsf{Type}$ のもとで型 False を持つ短い閉じた項を与えました。この項は[付録 C](c-hurkens.md)で紹介し、改変したカーネルに受理させます。

- **[Luo 1990]** Z. Luo. *An Extended Calculus of Constructions*. PhD thesis, University of Edinburgh, 1990. 非述語的な宇宙の上に述語的な宇宙の階層を重ねた、Calculus of Constructions の拡張です。公刊されたシステムの中では、本書の核に最も近いものです（[第 14 章](14-properties.md)）。

- **[de Moura and Ullrich 2021]** L. de Moura and S. Ullrich. The Lean 4 theorem prover and programming language. In *Automated Deduction (CADE 28)*, LNCS 12699, pages 625-635, Springer, 2021. 本書が手本にしたシステムです。宇宙、帰納型と再帰子の扱い、そしてタクティクを信頼せずカーネルだけが項を検査するアーキテクチャは、ここから採っています（[第 10 章](10-tactics.md)、[第 13 章](13-universes.md)）。

- **[Werner 1994]** B. Werner. *Une theorie des constructions inductives*. PhD thesis, Universite Paris VII, 1994. Calculus of Inductive Constructions のメタ理論、すなわち帰納型がある場合の強正規化と整合性を扱っています。[第 8 章](08-inductive-recipe.md)の一般的な手順はこれに依拠しています（[第 14 章](14-properties.md)）。
