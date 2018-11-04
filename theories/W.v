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

Definition ti : Type := w trunc_index (fun x => dsum (fun y => paths (trunc_succ y) x)).

Definition zero : ti.
Proof.
 refine (sup _ _ minus_two _).
 refine (fun H => _).
 refine (match H with dpair Hv HH => _ end).
 refine (absurd _).
 pose (D := trunc_index_rec empty (const unit) : trunc_index -> Type).
 change empty with (D minus_two).
 refine (transport HH _).
 change (D (trunc_succ Hv)) with unit.
 exact tt.
Defined.

Definition succ : ti -> ti.
Proof.
 refine (w_rect
     trunc_index (fun x => dsum (fun y => paths (trunc_succ y) x)) (fun _ => ti) _).
 refine (fun x u t => _).
