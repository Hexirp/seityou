Require Import Basis .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .


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

(* transport *)
Definition exerise_1_8_lemma_1
  (A : Type) (P : A -> Type)
  (x y : A) (p : paths A x y)
  (u : P x) : P y .
Proof.
 revert x y p u .
 refine (paths_elim_nop A (fun x y _ => P x -> P y) _) .
 exact (fun z v => v) .
Defined.

(* path_based_paths *)
Definition exerise_1_8_lemma_2
  (X : Type) (x : X) (p : dsum (paths X x))
  : paths (dsum (paths X x)) (dpair x (idpath X x)) p .
Proof.
 revert p .
 refine (dsum_elim _) .
 revert x .
 refine (paths_elim_nop X ?[ex_P] _) .
 exact (fun z => idpath (dsum (paths X z)) (dpair z (idpath X z))) .
Defined.

Definition exerise_1_8
  (A : Type) (a : A) (P : forall a', paths A a a' -> Type)
  (case_idpath : P a (idpath A a))
  (a' : A) (x : paths A a a') : P a' x .
Proof.
 pose (Q := fun h => P (dfst h) (dsnd h)) .
 pose (h := dpair a (idpath A a)) .
 pose (h' := dpair a' x) .
 change (Q h) in case_idpath .
 change (Q h') .
 refine (exerise_1_8_lemma_1 (dsum (paths A a)) Q h h' _ case_idpath) .
 change (paths (dsum (paths A a)) (dpair a (idpath A a)) h') .
 exact (exerise_1_8_lemma_2 A a h') .
Defined.
