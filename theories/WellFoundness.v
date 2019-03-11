(** * WellFoundness

    整礎性に関する定理を記述する。 *)

Require Import Basis .
Require Import Relation .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .


(** 反射推移閉包。 *)
Inductive retla {A : Type} (R : rel A A) : rel A A
  :=
  | retla_id : forall x, retla R x x
  | retla_comp : forall x y z, R x y -> retla R y z -> retla R x z
  .

(** 関係を保つ (relation-preserving) 関数である。 *)
Definition rel_pre
  {A : Type} (R : A -> A -> Type)
  {B : Type} (S : B -> B -> Type)
  (f : A -> B) : Type
  := forall x y : A, R x y -> S (f x) (f y) .

(** 関数の結果を見た関係。 *)
Definition rel_on {A : Type} {B : Type} (S : B -> B -> Type) (f : A -> B)
  : A -> A -> Type
  := fun x y => S (f x) (f y) .

(** [rel_of] は自明に関係を保つ関数を作る。 *)
Definition rel_pre_on {A : Type} {B : Type} {S : B -> B -> Type} (f : A -> B)
  : rel_pre (rel_on S f) S f .
Proof.
 change (forall x y, S (f x) (f y) -> S (f x) (f y)) .
 exact (fun x y => idmap) .
Defined.

(** [dsum] の第一引数だけを見た関係。 *)
Definition rel_dsum_on {A : Type} (R : A -> A -> Type) (P : A -> Type)
  : (sigma x, P x) -> (sigma x, P x) -> Type
  := rel_on R dfst .


(** 部分関係に [x] 以下の整礎性は遺伝する。 *)
Definition acc_rel_sub
  {A : Type} {R S : A -> A -> Type} (R_S : rel_sub R S)
  (x : A) (xH : acc S x) : acc R x .
Proof.
 revert x xH .
 refine (@acc_rec A S (acc R) _) .
 refine (fun x I => _) .
 refine (mk_acc _) .
 refine (fun xp xpR => _) .
 refine (I xp _) .
 refine (R_S xp x _) .
 exact xpR .
Defined.

(** [rel_on] に [x] 以下の整礎性は遺伝する。 *)
Definition acc_rel_on
  {A : Type} {B : Type} (S : B -> B -> Type) (f : A -> B)
  (x : A) (xfH : acc S (f x)) : acc (rel_on S f) x .
Proof.
 revert x xfH .
 refine (fix go (x : A) (xfH : acc S (f x)) : acc (rel_on S f) x := _) .
 refine (mk_acc _) .
 refine (fun xp xpfS => _) .
 refine (go xp _) .
 refine (inv_acc xfH _) .
 exact xpfS .
Defined.

(** [rel_on] に整礎性は遺伝する。 *)
Definition wf_rel_of
  {A : Type} {B : Type} (S : B -> B -> Type) (f : A -> B)
  (wf_S : well_founded S) : well_founded (rel_on S f) .
Proof.
 refine (wf_rel_pre f (rel_pre_on f) _) .
 exact wf_S .
Defined.

(** 部分関係に整礎性は遺伝する。 *)
Definition wf_rel_sub
  {A : Type} {R S : A -> A -> Type} (R_S : rel_sub R S)
  (wf_S : well_founded S) : well_founded R
  := fun x => acc_rel_sub R_S x (wf_S x) .

(** [rel_dsum] に [x] 以下の整礎性は遺伝する。 *)
Definition acc_rel_dsum
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  {x : A} (xH : acc R x) {xP : P x} : acc (rel_dsum_on R P) (dpair x xP) .
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
  (wf_R : well_founded R) : well_founded (rel_dsum_on R P) .
Proof.
 change (forall h, acc (rel_dsum_on R P) h) .
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
  (acc_h : acc (rel_dsum_on S (fun y => sigma x, f x = y)) h)
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


(** 参考文献:

    * https://github.com/coq/coq/blob/f4cf212efd98d01a6470ea7bfd1034d52e928906/theories/Init/Wf.v
    * https://github.com/agda/agda-stdlib/blob/a0bfe7422d2aa0f0f49c9647659ce34e6e741375/src/Induction/WellFounded.agda

    *)
