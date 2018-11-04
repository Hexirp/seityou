Add LoadPath "./theories".

Require Import Basis.

Polymorphic Cumulative Private Inductive w@{i j k} (A : Type@{i}) (B : A -> Type@{j}) : Type@{k}
  :=
  | sup : forall x : A, (B x -> w A B) -> w A B
  .

Polymorphic Definition w_rect@{i j k l}
  (A : Type@{i}) (B : A -> Type@{j}) (P : w@{i j k} A B -> Type@{l})
  (case_sup : forall x u, (forall y, P (u y)) -> P (sup A B x u))
  (x : w A B) : P x
  .
Proof.
Admitted.

Polymorphic Definition w_rect_c@{i j k l}
  (A : Type@{i}) (B : A -> Type@{j}) (P : w@{i j k} A B -> Type@{l})
  (c : forall x u, (forall y, P (u y)) -> P (sup A B x u))
  (x : A) (u : B x -> w A B)
  : paths
    (w_rect A B P c (sup A B x u))
    (c x u (fun y => w_rect A B P c (u y)))
  .
Proof.
Admitted.

Polymorphic Definition nat@{i j k l} : Type@{l} := w@{j k l} Type@{i} (fun A => sum unit A).

Polymorphic Definition zero@{i j k l} : nat@{i j k l}.
Proof.
 refine (w_rect Type@{i} (fun A => sum unit A) (fun x => x) _ _) .
