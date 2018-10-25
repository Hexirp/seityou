Add LoadPath "./theories".

Require Import Basis.


Definition K : Type
  := forall (A : Type) (x : A) (P : paths x x -> Type),
    P idpath -> forall p, P p .

Definition UIP : Type
  := forall (A : Type) (x y : A) (p q : paths x y),
    paths p q .

Definition UIP_refl : Type
  := forall (A : Type) (x : A) (p : paths x x),
    paths p idpath .


Definition K_UIP (axiom_K : K) : UIP
  := fun A x y p => _ .
