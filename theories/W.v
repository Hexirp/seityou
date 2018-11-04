Add LoadPath "./theories".

Require Import Basis.

Axiom W : forall (A : Type) (B : A -> Type), Type.

Axiom sup : forall (A : Type) (B : A -> Type) (x : A) (t : B x -> W A B), W A B.

Axiom wrec :
  forall (A : Type) (B : A -> Type) (C : W A B -> Type)
  (c : forall (x : A) (u : B x -> W A B) (v : forall y : B x, C (u y)), C (sup A B x u))
  (w : W A B), C w .
