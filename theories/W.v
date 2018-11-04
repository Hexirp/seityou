Add LoadPath "./theories".

Require Import Basis.

Polymorphic Cumulative Private Inductive w@{i j} (A : Type@{i}) (B : A -> Type@{j})
  :=
  | sup : forall x : A, (B x -> w A B) -> w A B
  .

Polymorphic Definition w_rect@{i j k}
  (A : Type@{i}) (B : A -> Type@{j}) (P : w A B -> Type@{k})
  (case_sup : forall x u, (forall y, P (u y)) -> P (sup A B x u))
  (x : w A B) : P x
  .
Proof.
Admitted.

Polymorphic Definition w_rect_c@{i j k}
  (A : Type@{i}) (B : A -> Type@{j}) (P : w A B -> Type@{k})
  (c : forall x u, (forall y, P (u y)) -> P (sup A B x u))
  (x : A) (u : B x -> w A B)
  : paths
    (w_rect A B P c (sup A B x u))
    (c x u (fun y => w_rect A B P c (u y)))
  .
Proof.
Admitted.

Definition nat@{i j k l} : Type@{k} := w@{i j} Type@{l} (fun A => sum unit A).

Definition zero@{i j k} : nat.
Proof.
 refine (sup@{i j} Type@{k} (fun A => sum unit A) nat _).
