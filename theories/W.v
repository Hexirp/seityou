Add LoadPath "./theories".

Require Import Basis.

Private Inductive w (A : Type) (B : A -> Type)
  :=
  | sup : forall x : A, (B x -> w A B) -> w A B
  .

Definition w_rect
  (A : Type) (B : A -> Type) (P : w A B -> Type)
  (case_sup : forall x u, (forall y, P (u y)) -> P (sup A B x u))
  (x : w A B) : P x
  .
Proof.
Admitted.

Definition w_rect_c
  (A : Type) (B : A -> Type) (P : w A B -> Type)
  (c : forall x u, (forall y, P (u y)) -> P (sup A B x u))
  (x : A) (u : B x -> w A B)
  : paths
    (w_rect A B P c (sup A B x u))
    (c x u (fun y => w_rect A B P c (u y)))
  .
Proof.
Admitted.
