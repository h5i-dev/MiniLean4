<div class="lead" markdown="1">

These are the sources used in the book, with notes on the results cited from each one.

</div>

- **[Barendregt 1992]** H. P. Barendregt. Lambda calculi with types. In *Handbook of Logic in Computer Science*, volume 2, Oxford University Press, 1992. The standard reference for Pure Type Systems: the bidirectional split of type checking into inference and checking ([Chapter 5](05-algorithm.md)), and the metatheory of uniqueness of types, generation, confluence, and subject reduction used in [Chapter 14](14-properties.md) and [Appendix D](d-proof-consistency.md).

- **[Carneiro 2019]** M. Carneiro. *The Type Theory of Lean*. Master's thesis, Carnegie Mellon University, 2019. A precise account of Lean's actual type theory, including definitional proof irrelevance and the subtleties it introduces; cited in [Chapter 13](13-universes.md) and [Chapter 14](14-properties.md) for where Lean's full system goes beyond ours.

- **[Coquand and Huet 1988]** T. Coquand and G. Huet. The calculus of constructions. *Information and Computation*, 76(2-3):95-120, 1988. The system at the heart of this book: dependent types with an impredicative universe of propositions. Its consistency result is what justifies the universe design of [Chapter 13](13-universes.md).

- **[de Bruijn 1972]** N. G. de Bruijn. Lambda calculus notation with nameless dummies, a tool for automatic formula manipulation, with application to the Church-Rosser theorem. *Indagationes Mathematicae*, 34(5):381-392, 1972. The nameless representation of bound variables. It is one of the three remedies for variable capture in [Chapter 11](11-substitution-alpha.md), and the bridge between the two definitions of alpha-equivalence in [Appendix B](b-proof-alpha.md).

- **[Girard 1972]** J.-Y. Girard. *Interpretation fonctionnelle et elimination des coupures de l'arithmetique d'ordre superieur*. PhD thesis, Universite Paris VII, 1972. Introduces reducibility candidates, the method behind strong normalization for impredicative systems ([Chapter 14](14-properties.md)), and the paradox showing that a universe containing itself is inconsistent ([Chapter 13](13-universes.md)).

- **[Hurkens 1995]** A. J. C. Hurkens. A simplification of Girard's paradox. In *Typed Lambda Calculi and Applications (TLCA)*, LNCS 902, pages 266-278, Springer, 1995. The short closed term of type False under $\mathsf{Type} : \mathsf{Type}$ that [Appendix C](c-hurkens.md) presents and that the modified kernel accepts.

- **[Luo 1990]** Z. Luo. *An Extended Calculus of Constructions*. PhD thesis, University of Edinburgh, 1990. The Calculus of Constructions extended with a predicative hierarchy of universes above the impredicative one, which is the closest published system to the core of this book ([Chapter 14](14-properties.md)).

- **[de Moura and Ullrich 2021]** L. de Moura and S. Ullrich. The Lean 4 theorem prover and programming language. In *Automated Deduction (CADE 28)*, LNCS 12699, pages 625-635, Springer, 2021. The system this book imitates: its universes, its treatment of inductive types and recursors, and its architecture in which tactics are untrusted and only the kernel checks terms ([Chapter 10](10-tactics.md), [Chapter 13](13-universes.md)).

- **[Werner 1994]** B. Werner. *Une theorie des constructions inductives*. PhD thesis, Universite Paris VII, 1994. The metatheory of the Calculus of Inductive Constructions: strong normalization and consistency in the presence of inductive types, which is what the general recipe of [Chapter 8](08-inductive-recipe.md) rests on ([Chapter 14](14-properties.md)).
