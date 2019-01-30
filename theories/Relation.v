(** * Relation

    関係についての定義や定理を記述する。 *)

Require Import Basis .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .


(** 関係を保つ (relation-preserving) 関数である。 *)
Definition rel_pre
  {A : Type} (R : A -> A -> Type)
  {B : Type} (S : B -> B -> Type)
  (f : A -> B) : Type
  := forall x y : A, R x y -> S (f x) (f y) .

(** 関数の結果を見た関係。 *)
Definition rel_of {A : Type} {B : Type} (S : B -> B -> Type) (f : A -> B)
  : A -> A -> Type
  := fun x y => S (f x) (f y) .

(** [rel_of] は自明に関係を保つ関数を作る。 *)
Definition rel_pre_of {A : Type} {B : Type} {S : B -> B -> Type} (f : A -> B)
  : rel_pre (rel_of S f) S f .
Proof.
 change (forall x y, S (f x) (f y) -> S (f x) (f y)) .
 exact (fun x y => idmap) .
Defined.

(** [dsum] の第一引数だけを見た関係。 *)
Definition rel_dsum {A : Type} (R : A -> A -> Type) (P : A -> Type)
  : (sigma x, P x) -> (sigma x, P x) -> Type
  := rel_of R dfst .


(** ** Well foundness *)

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


(** [mk_acc] の反対。 *)
Definition inv_acc
  {A : Type} {R : A -> A -> Type} {x : A} (H : acc R x)
  {y : A} (yR : R y x) : acc R y .
Proof.
 revert y yR .
 exact (acc_case_nodep idmap H) .
Defined.


(** [R] は整礎である。 *)
Definition well_founded {A : Type} (R : A -> A -> Type) : Type
  := forall x : A, acc R x .

(** 非依存の整礎帰納法。

    「超限再帰的な定義」からの類推で、関数を整礎帰納法的に定義するともいえる。 *)
Definition wf_ind_nodep
  {A : Type} {R : A -> A -> Type} (H : well_founded R) {P : Type}
  (c: forall x : A, (forall xp : A, R xp x -> P) -> P)
  (x : A) : P
  := acc_rec c (H x) .

(** 整礎帰納法。 *)
Definition wf_ind
  {A : Type} {R : A -> A -> Type} (H : well_founded R) {P : A -> Type}
  (c: forall x : A, (forall xp : A, R xp x -> P xp) -> P x)
  (x : A) : P x
  := acc_rec c (H x) .


(** 整礎帰納法により構成される関数の不動点について。 *)

Section FixPoint .

  Variable A : Type .
  Variable R : A -> A -> Type .
  Variable P : A -> Type .
  Variable f : forall x : A, (forall y : A, R y x -> P y) -> P x .

  (** [f] の不動点。 *)
  Definition fix_f_acc {x : A} (H : acc R x) : P x
    := acc_rec f H .

  (** [fix_f] は不動点である。 *)
  Definition path_fix_f_acc {x : A} {H : acc R x}
    : f x (fun (y : A) (yR : R y x) => fix_f_acc (inv_acc H yR)) = fix_f_acc H .
  Proof.
   revert x H .
   refine (@acc_rect A R ?[P] _) .
   refine (fun x Hp PH => _) .
   exact idpath .
  Defined.

End FixPoint .

Arguments fix_f_acc {_ _ _} _ {_} _ .
Arguments path_fix_f_acc {_ _ _ _ _ _} .

(** [f] の全域に渡る不動点。 *)
Definition fix_f
  {A : Type} {R : A -> A -> Type} {H : well_founded R} {P : A -> Type}
  (f : forall x : A, (forall y : A, R y x -> P y) -> P x)
  (x : A) : P x
  := fix_f_acc f (H x) .


(** [rel_dsum] に [x] 以下の整礎性は遺伝する。 *)
Definition acc_rel_dsum
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  {x : A} (xh : acc R x) {px : P x} : acc (rel_dsum R P) (dpair x px) .
Proof.
 revert x xh px .
 refine (@acc_rec A R ?[ex] _) .
 refine (fun x xI px => _) .
 refine (mk_acc _) .
 refine (dsum_elim _) .
 refine (fun xp pxp xpr => _) .
 refine (xI xp _ pxp) .
 change (R xp x) in xpr .
 exact xpr .
Defined.

(** [rel_dsum] に整礎性は遺伝する。 *)
Definition wf_rel_dsum
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  (wf_R : well_founded R) : well_founded (rel_dsum R P) .
Proof.
 change (forall xh, acc (rel_dsum R P) xh) .
 refine (dsum_elim _) .
 refine (fun x px => _) .
 refine (acc_rel_dsum _) .
 exact (wf_R x) .
Defined.

(** [rel_pre] である関数は [x] 以下の整礎性を後ろ側へ保つ。 *)
Definition acc_rel_pre
  {A : Type} {R : A -> A -> Type}
  {B : Type} {S : B -> B -> Type}
  (f : A -> B) (fh : rel_pre R S f)
  {x : A} (xh : acc S (f x)) : acc R x .
Proof.
Admitted.

(** [rel_of] に [x] 以下の整礎性は遺伝する。 *)
Definition acc_rel_of
  {A : Type} {B : Type} {S : B -> B -> Type} {f : A -> B}
  {x : A} (xh : acc S (f x)) : acc (rel_of S f) x .
Proof.
Admitted.

(** [rel_of] に整礎性は遺伝する。 *)
Definition wf_rel_of
  {A : Type} {B : Type} (S : B -> B -> Type) (f : A -> B)
  (wf_S : well_founded S) : well_founded (rel_of S f) .
Proof.
 assert (forall b, forall a, S (f a) b -> acc (rel_of S f) a) .
 -
  refine (wf_ind wf_S _) .
  refine (fun b bH a aR => _) .
  refine (bH ?[bp] _ a aR) .
Admitted.


(** ** Others *)

(** [acc] についての弱い道。

    この場合は外延的な等しさ／点ごとの道になる。 *)
Inductive acc_weak_path
  (A : Type) (R : A -> A -> Type) (x : A)
  : acc R x -> acc R x -> Type
  :=
  | mk_acc_weak_path
      : forall (r : forall xp : A, R xp x -> acc R xp)
               (s : forall xp : A, R xp x -> acc R xp),
       (forall (xp  : A)
               (xpR : R xp x),
                      acc_weak_path A R xp (r xp xpR) (s xp xpR)) ->
           acc_weak_path A R x (mk_acc r) (mk_acc s) .
