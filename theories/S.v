Require Import Basis .


Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".


Inductive list (A : Type) : Type
  :=
  | nil : list A
  | cons : A -> list A -> list A
  .

Inductive forall_elements (A : Type) (P : A -> Type) : list A -> Type
  :=
  | fe_nil : forall_elements A P (nil A)
  | fe_cons
          : forall (x : A) (xs : list A),
              P x -> forall_elements A P xs -> forall_elements A P (cons A x xs)
  .

Inductive is_sorted (A : Type) (R : A -> A -> Type) : list A -> Type
  :=
  | iss_nil : is_sorted A R (nil A)
  | iss_cons
          : forall (x : A) (xs : list A),
              forall_elements A (R x) xs -> is_sorted A R xs -> is_sorted A R (cons A x xs)
  .

Inductive sorted_list (A : Type) (R : A -> A -> Type) : Type
  :=
  | mk_sl : forall x : list A, is_sorted A R x -> sorted_list A R
  .


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
  (case_mk_acc : forall Hp : forall xp : A, R xp x -> acc A R xp, P (mk_acc A R x Hp))
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
  (A : Type) (R : A -> A -> Type) (P : forall x : A, acc A R x -> Type)
  (case_mk_acc
          : forall (x : A) (Hp : forall xp : A, R xp x -> acc A R xp),
              (forall (xp : A) (xpR : R xp x), P xp (Hp xp xpR)) -> P x (mk_acc A R x Hp))
  (x : A) (H : acc A R x) : P x H .
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
