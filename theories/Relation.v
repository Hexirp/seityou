(** * Relation

    関係についての定義や定理を記述する。 *)

Require Import Basis .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .


(** [A] の関係 [R : A -> A -> Type] は [x : A] において整礎である。 *)
Inductive acc {A : Type} (R : A -> A -> Type) (x : A) : Type
  :=
  | mk_acc : (forall xp : A, R xp x -> acc R xp) -> acc R x
  .

Definition acc_case_nodep
  {A : Type} {R : A -> A -> Type} {x : A} {P : Type}
  (case_mk_acc : (forall xp : A, R xp x -> acc R xp) -> P)
  (H : acc R x) : P
  := match H with mk_acc _ _ Hp => case_mk_acc Hp end .

Definition acc_case
  {A : Type} {R : A -> A -> Type} {x : A} {P : acc R x -> Type}
  (case_mk_acc : forall Hp : forall xp : A, R xp x -> acc R xp, P (mk_acc R x Hp))
  (H : acc R x) : P H
  := match H with mk_acc _ _ Hp => case_mk_acc Hp end .

Definition acc_rec
  (A : Type) (R : A -> A -> Type) (P : A -> Type)
  (case_mk_acc : forall x : A, (forall xp : A, R xp x -> P xp) -> P x)
  (x : A) (H : acc R x) : P x .
Proof.
 revert x H .
 refine (fix go (x : A) (H : acc R x) {struct H} : P x := _) .
 refine (acc_case_nodep _ H) .
 -
  refine (fun Hp => _) .
  refine (case_mk_acc x _) .
  refine (fun xp xpR => _) .
  exact (go xp (Hp xp xpR)) .
Defined.

Definition acc_rect
  (A : Type) (R : A -> A -> Type) (P : forall x : A, acc R x -> Type)
  (case_mk_acc
          : forall (x : A) (Hp : forall xp : A, R xp x -> acc R xp),
              (forall (xp : A) (xpR : R xp x), P xp (Hp xp xpR)) -> P x (mk_acc R x Hp))
  (x : A) (H : acc R x) : P x H .
Proof.
 revert x H .
 refine (fix go (x : A) (H : acc R x) {struct H} : P x H := _) .
 refine (acc_case _ H) .
 -
  refine (fun Hp => _) .
  refine (case_mk_acc x Hp _) .
  refine (fun xp xpR => _) .
  exact (go xp (Hp xp xpR)) .
Defined.
