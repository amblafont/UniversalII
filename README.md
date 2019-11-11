### Agda code for "For Induction-Induction, Induction is Enough"

#### Installation

This folder has been tested with Agda 2.6.0.1. Newer Agda
versions likely work as well. An Agda standard library is also
needed. Instructions how to set up the standard library can be found
[here](https://agda.readthedocs.io/en/v2.6.0.1/tools/package-system.html),
the library itself can be downloaded from
[here](https://github.com/agda/agda-stdlib/releases).

#### Formalization

We construct a morphism from the syntax of the type theory of signatures to
an arbitrary model, and prove its uniqueness.

Files in the order of dependency with a short description:

1. [`EqLib.agda`](EqLib.agda): definitions and lemmas taking from the HoTT 
library (removing the univalence axiom).
2. [`Lib.agda`](Lib.agda): some useful lemmas, some of them requiring UIP
3. [`Syntax.agda`](Syntax.agda): syntax of the theory of signatures
4. [`Model.agda`](ModelRew.agda): definition of models
5. [`SyntaxIsModel.agda`](SyntaxIsModel.agda): syntax as a model
6. [`ModelRew.agda`](ModelRew.agda): postulated model with rewrite rules
7. [`Relation.agda`](Relation.agda): definition of the relation between the 
syntax and the postulated model
8. [`RelationWeakening.agda`](RelationWeakening.agda): stability of the relation
under weakening
9. [`RelationSubstitution.agda`](RelationSubstitution.agda): stability of the
relation under substitution
10. [`RelationInhabit.agda`](RelationInhabit.agda): construction of a related
semantic counterpart for each part of the syntax
11. [`ModelMorphism.agda`](ModelMorphism.agda): definition of model morphisms
12. [`ModelMorphismRew.agda`](ModelMorphismRew.agda): postulated model morphism
from the syntax to the postulated model
13. [`SyntaxIsInitial.agda`](SyntaxIsInitial.agda): construction of a morphism 
from the syntax to the postulated model, and proof that the postulated morphism
is pointwise equal to it.

