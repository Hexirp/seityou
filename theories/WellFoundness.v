(** * WellFoundness

    整礎性に関する定理を記述する。 *)

Require Import Basis .
Require Import Relation .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .


(** *** Propagation of well-foundness

    整礎性の伝播に関する定理について。 *)

(** [rel_dsum] に [x] 以下の整礎性は遺伝する。 *)
Definition acc_rel_dsum
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  {x : A} (xH : acc R x) {xP : P x} : acc (rel_dsum R P) (dpair x xP) .
Proof.
 revert x xH xP .
 refine (@acc_rec A R ?[ex_P] _) .
 refine (fun x I xP => _) .
 refine (mk_acc _) .
 refine (dsum_elim _) .
 refine (fun xp xpP xpR => _) .
 refine (I xp _ xpP) .
 change (R xp x) in xpR .
 exact xpR .
Defined.

(** [rel_dsum] に整礎性は遺伝する。 *)
Definition wf_rel_dsum
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  (wf_R : well_founded R) : well_founded (rel_dsum R P) .
Proof.
 change (forall h, acc (rel_dsum R P) h) .
 refine (dsum_elim _) .
 refine (fun x xP => _) .
 refine (acc_rel_dsum _) .
 exact (wf_R x) .
Defined.

(** [rel_pre] である関数は、その維に関する [x] 以下の整礎性を後ろ側へ保つ。 *)
Definition acc_rel_pre_fiber
  {A : Type} {R : A -> A -> Type}
  {B : Type} {S : B -> B -> Type}
  (f : A -> B) (f_rel_pre : rel_pre R S f)
  {h : sigma y x, f x = y}
  (acc_h : acc (rel_dsum S (fun y => sigma x, f x = y)) h)
  : acc R (dfst (dsnd h)) .
Proof.
 revert h acc_h .
 refine (@acc_rec ?[ex_A] ?[ex_R] ?[ex_P] _) .
 refine (dsum_elim _) .
 refine (fun y => _) .
 refine (dsum_elim _) .
 refine (fun x xH I => _) .
 refine (mk_acc _) .
 refine (fun xp xpR => _) .
 pose (hp := dpair (f xp) (dpair xp idpath) : sigma y x, f x = y) .
 change (acc R (dfst (dsnd hp))) .
 refine (I hp _) .
 change (S (f xp) y) .
 refine (transport xH _) .
 change (forall x y : A, R x y -> S (f x) (f y)) in f_rel_pre .
 refine (f_rel_pre xp x _) .
 change (R xp x) in xpR .
 exact xpR .
Defined.

(** [rel_pre] である関数は [x] 以下の整礎性を後ろ側へ保つ。 *)
Definition acc_rel_pre
  {A : Type} {R : A -> A -> Type}
  {B : Type} {S : B -> B -> Type}
  (f : A -> B) (f_rel_pre : rel_pre R S f)
  {x : A} (acc_x : acc S (f x)) : acc R x .
Proof.
 pose (h := dpair (f x) (dpair x idpath) : sigma y x, f x = y) .
 change (acc R (dfst (dsnd h))) .
 refine (acc_rel_pre_fiber f f_rel_pre _) .
 refine (acc_rel_dsum _) .
 exact acc_x .
Defined.

(** [rec_pre] である関数は整礎性を後ろへ保つ。 *)
Definition wf_rel_pre
  {A : Type} {R : A -> A -> Type}
  {B : Type} {S : B -> B -> Type}
  (f : A -> B) (f_rel_pre : rel_pre R S f)
  (wf_S : well_founded S) : well_founded R .
Proof.
 refine (fun x => _) .
 refine (acc_rel_pre f f_rel_pre _) .
 exact (wf_S (f x)) .
Defined.

(** [rel_of] に整礎性は遺伝する。 *)
Definition wf_rel_of
  {A : Type} {B : Type} (S : B -> B -> Type) (f : A -> B)
  (wf_S : well_founded S) : well_founded (rel_of S f) .
Proof.
 refine (wf_rel_pre f (rel_pre_of f) _) .
 exact wf_S .
Defined.