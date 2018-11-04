Add LoadPath "./theories".

Require Import Basis.

Inductive w (A : Type) (B : A -> Type)
  :=
  | sup : forall x : A, (B x -> w A B) -> w A B
  .

Definition w_rect
  (A : Type) (B : A -> Type) (P : w A B -> Type)
  (case_sup : forall (x : A) (u : B x -> w A B), P (sup A B x u))
  (x : w A B) : P x
  := match x with sup _ _ x u => case_sup x u end .

Axiom W : forall (A : Type) (B : A -> Type), Type.

Axiom Sup : forall (A : Type) (B : A -> Type) (x : A) (t : B x -> W A B), W A B.

Axiom wrec :
  forall (A : Type) (B : A -> Type) (C : W A B -> Type)
  (c : forall (x : A) (u : B x -> W A B) (v : forall y : B x, C (u y)), C (Sup A B x u))
  (w : W A B), C w .
