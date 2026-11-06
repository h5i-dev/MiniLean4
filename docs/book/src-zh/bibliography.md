<div class="lead" markdown="1">

本书引用的文献不多。下面每一条都说明该著作的贡献，以及本书在何处依赖它。

</div>

- **[Barendregt 1992]** H. P. Barendregt. Lambda calculi with types. In *Handbook of Logic in Computer Science*, volume 2, Oxford University Press, 1992. 纯类型系统的标准参考文献：把类型检查双向拆分为推断与检查（[第 5 章](05-algorithm.md)），以及[第 14 章](14-properties.md)和[附录 D](d-proof-consistency.md)用到的元理论，即类型唯一性、生成引理、合流性和主体归约。

- **[Carneiro 2019]** M. Carneiro. *The Type Theory of Lean*. Master's thesis, Carnegie Mellon University, 2019. 对 Lean 实际类型理论的精确刻画，包括定义性证明无关性及其带来的微妙之处；[第 13 章](13-universes.md)和[第 14 章](14-properties.md)在说明 Lean 的完整系统超出本书系统之处时引用了它。

- **[Coquand and Huet 1988]** T. Coquand and G. Huet. The calculus of constructions. *Information and Computation*, 76(2-3):95-120, 1988. 本书核心所在的系统：带有一个非谓词命题宇宙的依赖类型。它的一致性结果为[第 13 章](13-universes.md)的宇宙设计提供了依据。

- **[de Bruijn 1972]** N. G. de Bruijn. Lambda calculus notation with nameless dummies, a tool for automatic formula manipulation, with application to the Church-Rosser theorem. *Indagationes Mathematicae*, 34(5):381-392, 1972. 约束变量的无名表示。它是[第 11 章](11-substitution-alpha.md)中应对变量捕获的三种办法之一，也是[附录 B](b-proof-alpha.md)中连接 α 等价两种定义的桥梁。

- **[Girard 1972]** J.-Y. Girard. *Interpretation fonctionnelle et elimination des coupures de l'arithmetique d'ordre superieur*. PhD thesis, Universite Paris VII, 1972. 引入可归约性候选，即非谓词系统强规范化背后的方法（[第 14 章](14-properties.md)），以及表明包含自身的宇宙不一致的悖论（[第 13 章](13-universes.md)）。

- **[Hurkens 1995]** A. J. C. Hurkens. A simplification of Girard's paradox. In *Typed Lambda Calculi and Applications (TLCA)*, LNCS 902, pages 266-278, Springer, 1995. 在 $\mathsf{Type} : \mathsf{Type}$ 之下类型为 False 的那个简短封闭项；[附录 C](c-hurkens.md) 展示了它，经修改的内核会接受它。

- **[Luo 1990]** Z. Luo. *An Extended Calculus of Constructions*. PhD thesis, University of Edinburgh, 1990. 在非谓词宇宙之上扩展了一层谓词宇宙层级的构造演算，是已发表的系统中最接近本书核心的一个（[第 14 章](14-properties.md)）。

- **[de Moura and Ullrich 2021]** L. de Moura and S. Ullrich. The Lean 4 theorem prover and programming language. In *Automated Deduction (CADE 28)*, LNCS 12699, pages 625-635, Springer, 2021. 本书所模仿的系统：它的宇宙、它对归纳类型和递归子的处理，以及策略不可信、只有内核检查项的架构（[第 10 章](10-tactics.md)、[第 13 章](13-universes.md)）。

- **[Werner 1994]** B. Werner. *Une theorie des constructions inductives*. PhD thesis, Universite Paris VII, 1994. 归纳构造演算的元理论：存在归纳类型时的强规范化和一致性，[第 8 章](08-inductive-recipe.md)的通用方法正建立在它之上（[第 14 章](14-properties.md)）。
