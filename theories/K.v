Add LoadPath "./theories".

Require Import Basis.


Definition K : Type
  := forall (A : Type) (x : A) (P : paths x x -> Type),
    P idpath -> forall p, P p .
