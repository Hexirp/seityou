(** * Relation

    関係についての定義や定理を記述する。 *)

Require Import Basis .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .


(** [A] の関係 [R] は [x : A] において整礎である。 *)
Inductive acc (A : Type) (R : A -> A -> Type) (x : A) : Type
  :=
  | mk_acc : (forall xp : A, R xp x -> acc A R xp) -> acc A R x
  .

Definition acc_case_nodep
  (A : Type) (R : A -> A -> Type) (x : A) (P : Type)
  (case_mk_acc : (forall xp : A, R xp x -> acc A R xp) -> P)
  (H : acc A R x) : P
  := match H with mk_acc _ _ _ Hp => case_mk_acc Hp end .

Definition acc_case
  (A : Type) (R : A -> A -> Type) (x : A) (P : acc A R x -> Type)
  (case_mk_acc
     : forall Hp : (forall xp : A, R xp x -> acc A R xp), P (mk_acc A R x Hp))
  (H : acc A R x) : P H
  := match H with mk_acc _ _ _ Hp => case_mk_acc Hp end .

Definition acc_rec
  (A : Type) (R : A -> A -> Type) (P : A -> Type)
  (case_mk_acc : forall x : A, (forall xp : A, R xp x -> P xp) -> P x)
  (x : A) (H : acc A R x) : P x .
Proof.
 revert x H .
 refine (fix go (x : A) (H : acc A R x) {struct H} : P x := _) .
 refine (acc_case_nodep A R x (P x) _ H) .
 -
  refine (fun Hp => _) .
  refine (case_mk_acc x _) .
  refine (fun xp xpR => _) .
  exact (go xp (Hp xp xpR)) .
Defined.

Definition acc_rect
  (A : Type)
  (R : A -> A -> Type)
  (P : forall x : A, acc A R x -> Type)
  (case_mk_acc
     : forall (x  : A)
              (Hp : forall xp : A,
                                R xp x ->
                                acc A R xp),
              (forall (xp  : A)
                      (xpR : R xp x),
                             P xp (Hp xp xpR)) ->
               P x (mk_acc A R x Hp))
  (x : A)
  (H : acc A R x)
     : P x H .
Proof.
 revert x H .
 refine (fix go (x : A) (H : acc A R x) {struct H} : P x H := _) .
 refine (acc_case A R x (P x) _ H) .
 -
  refine (fun Hp => _) .
  refine (case_mk_acc x Hp _) .
  refine (fun xp xpR => _) .
  exact (go xp (Hp xp xpR)) .
Defined.

Arguments acc {_} _ _ .
Arguments mk_acc {_ _ _} _ .
Arguments acc_case_nodep {_ _ _ _} _ _ .
Arguments acc_case {_ _ _ _} _ _ .
Arguments acc_rec {_ _ _} _ {_} _ .
Arguments acc_rect {_ _ _} _ {_} _ .


(** [R] は整礎である。 *)
Definition well_founded {A : Type} (R : A -> A -> Type) : Type
  := forall x : A, acc R x .

(** 非依存の整礎帰納法。

    「超限再帰的な定義」からの類推で、関数を整礎帰納法的に定義するともいえる。 *)
Definition wf_ind_nodep
  (A : Type) (R : A -> A -> Type) (H : well_founded R) (P : Type)
  (c: forall x : A, (forall xp : A, R xp x -> P) -> P)
  (x : A) : P .
Proof.
 refine (acc_rec _ (H x)) .
 exact c .
Defined.

(** 整礎帰納法。 *)
Definition wf_ind
  (A : Type) (R : A -> A -> Type) (H : well_founded R) (P : A -> Type)
  (c: forall x : A, (forall xp : A, R xp x -> P xp) -> P x)
  (x : A) : P x .
Proof.
 refine (acc_rec _ (H x)) .
 exact c .
Defined.


Section FixPoint .

  Variable A : Type .
  Variable R : A -> A -> Type .
  Variable wf_R : well_founded R .
  Variable P : A -> Type .
  Variable f : forall x : A, (forall y : A, R y x -> P y) -> P x .

  Definition fix_f (x : A) (H : acc R x) : P x .
  Proof.
   revert x H .
   exact (@acc_rec A R P f) .
  Defined.
