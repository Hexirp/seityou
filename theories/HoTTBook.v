Require Import Basis .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .
Import Basis.Notation.Path .


Arguments paths : clear implicits .
Arguments idpath : clear implicits .
Arguments paths_elim : clear implicits .
Arguments paths_elim_nop : clear implicits .

Definition book_1_12_2_a
  {A : Type} {P : forall a a', paths A a a' -> Type}
  (case_idpath : forall a, P a a (idpath A a))
  (a a' : A) (x : paths A a a') : P a a' x .
Proof.
 revert a' x .
 refine (paths_elim A a (P a) _) .
 exact (case_idpath a) .
Defined.

Definition book_1_12_2_b
  (A : Type) (a : A) (P : forall a', paths A a a' -> Type)
  (case_idpath : P a (idpath A a))
  (a' : A) (x : paths A a a') : P a' x .
Proof.
 revert a a' x P case_idpath .
 refine (paths_elim_nop A ?[ex_P] _) .
 refine (fun a P h => _) .
 exact h .
Defined.

Definition exerise_1_8
  (A : Type) (a : A) (P : forall a', paths A a a' -> Type)
  (case_idpath : P a (idpath A a))
  (a' : A) (x : paths A a a') : P a' x .
Proof.
Admitted.
