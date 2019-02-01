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

Section Acc .

  Variable A : Type .
  Variable R : A -> A -> Type .

  (** [A] の関係 [R] は [x : A] において整礎である。 *)
  Inductive acc (x : A) : Type
    :=
    | mk_acc : (forall xp, R xp x -> acc xp) -> acc x
    .

  Definition acc_case_nodep
    (x : A) (P : Type)
    (case_mk_acc : (forall xp, R xp x -> acc xp) -> P)
    (H : acc x) : P
    := match H with mk_acc _ Hp => case_mk_acc Hp end .

  Definition acc_case
    (x : A) (P : acc x -> Type)
    (case_mk_acc : forall Hp , P (mk_acc x Hp))
    (H : acc x) : P H
    := match H with mk_acc _ Hp => case_mk_acc Hp end .

  Definition acc_rec
    (P : A -> Type)
    (case_mk_acc : forall x, (forall xp, R xp x -> P xp) -> P x)
    (x : A) (xH : acc x) : P x .
  Proof.
   revert x xH .
   refine (fix go (x : A) (xH : acc x) {struct xH} : P x := _) .
   refine (acc_case_nodep x (P x) _ xH) .
   refine (fun Hps => _) .
   refine (case_mk_acc x _) .
   refine (fun xp xpR => _) .
   exact (go xp (Hps xp xpR)) .
  Defined.

  Definition acc_rect
    (P : forall x, acc x -> Type)
    (case_mk_acc
       : forall x Hp, (forall xp xpR, P xp (Hp xp xpR)) -> P x (mk_acc x Hp))
    (x : A) (xH : acc x) : P x xH .
  Proof.
   revert x xH .
   refine (fix go (x : A) (xH : acc x) {struct xH} : P x xH := _) .
   refine (acc_case x (P x) _ xH) .
   refine (fun Hps => _) .
   refine (case_mk_acc x Hps _) .
   refine (fun xp xpR => _) .
   exact (go xp (Hps xp xpR)) .
  Defined.

End Acc.

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

Section FixPointNodep .

  Variable A : Type .
  Variable R : A -> A -> Type .
  Variable P : Type .
  Variable f : forall x : A, (forall y : A, R y x -> P) -> P .

  (** [f] の不動点。 *)
  Definition fix_f_acc_nodep {x : A} (H : acc R x) : P
    := acc_rec f H .

  (** [fix_f] は不動点である。 *)
  Definition path_fix_f_acc_nodep {x : A} {H : acc R x}
    : paths (f x (fun (y : A) (yR : R y x) => fix_f_acc_nodep (inv_acc H yR)))
            (fix_f_acc_nodep H) .
  Proof.
   revert x H .
   refine (@acc_rect A R ?[ex_P] _) .
   refine (fun x Hp I => _) .

   change (fix_f_acc_nodep (mk_acc Hp))
     with (acc_rec f (mk_acc Hp)) .

   change (acc_rec f (mk_acc Hp))
     with (f x (fun y yR => acc_rec f (Hp y yR))) .

   change (fun y yR => acc_rec f (Hp y yR))
     with (fun y yR => fix_f_acc_nodep (Hp y yR)) .

   change (fun y yR => fix_f_acc_nodep (Hp y yR))
     with (fun y yR => fix_f_acc_nodep (inv_acc (mk_acc Hp) (y := y) yR)) .

   exact idpath .
  Defined.

End FixPointNodep .

Arguments fix_f_acc_nodep {_ _ _} _ {_} _ .
Arguments path_fix_f_acc_nodep {_ _ _ _ _ _} .

(** [f] の全域に渡る不動点。 *)
Definition fix_f_nodep
  {A : Type} {R : A -> A -> Type} {wf_R : well_founded R} {P : Type}
  (f : forall x : A, (forall y : A, R y x -> P) -> P)
  (x : A) : P
  := fix_f_acc_nodep f (wf_R x) .

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
   refine (fun x Hp I => _) .

   change (fix_f_acc (mk_acc Hp))
     with (acc_rec f (mk_acc Hp)) .

   change (acc_rec f (mk_acc Hp))
     with (f x (fun y yR => acc_rec f (Hp y yR))) .

   change (fun y yR => acc_rec f (Hp y yR))
     with (fun y yR => fix_f_acc (Hp y yR)) .

   change (fun y yR => fix_f_acc (Hp y yR))
     with (fun y yR => fix_f_acc (inv_acc (mk_acc Hp) (y := y) yR)) .

   exact idpath .
  Defined.

End FixPoint .

Arguments fix_f_acc {_ _ _} _ {_} _ .
Arguments path_fix_f_acc {_ _ _ _ _ _} .

(** [f] の全域に渡る不動点。 *)
Definition fix_f
  {A : Type} {R : A -> A -> Type} {wf_R : well_founded R} {P : A -> Type}
  (f : forall x : A, (forall y : A, R y x -> P y) -> P x)
  (x : A) : P x
  := fix_f_acc f (wf_R x) .


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

(** [rel_pre] である関数は、その維に関する [x] 以下の整礎性を後ろ側へ保つ。 *)
Definition acc_rel_pre_fiber
  {A : Type} {R : A -> A -> Type}
  {B : Type} {S : B -> B -> Type}
  (f : A -> B) (fh : rel_pre R S f)
  {xh : sigma y x, f x = y}
  (acc_xh : acc (rel_dsum S (fun y => sigma x, f x = y)) xh)
  : acc R (dfst (dsnd xh)) .
Proof.
 revert xh acc_xh .
 refine (@acc_rec ?[ex_A] ?[ex_R] ?[ex_P] _) .
 refine (dsum_elim _) .
 refine (fun y => _) .
 refine (dsum_elim _) .
 refine (fun x xH => _) .
 refine (fun I => _) .
 refine (mk_acc _) .
 refine (fun xp xpR => _) .
 pose (xhp := dpair (f xp) (dpair xp idpath) : sigma y x, f x = y) .
 change (acc R (dfst (dsnd xhp))) .
 refine (I xhp _) .
 change (S (f xp) y) .
 refine (transport xH _) .
 change (forall x y : A, R x y -> S (f x) (f y)) in fh .
 refine (fh xp x _) .
 change (R xp x) in xpR .
 exact xpR .
Defined.

(** [rel_pre] である関数は [x] 以下の整礎性を後ろ側へ保つ。 *)
Definition acc_rel_pre
  {A : Type} {R : A -> A -> Type}
  {B : Type} {S : B -> B -> Type}
  (f : A -> B) (fh : rel_pre R S f)
  {x : A} (acc_x : acc S (f x)) : acc R x .
Proof.
 pose (xh := dpair (f x) (dpair x idpath) : sigma y x, f x = y) .
 change (acc R (dfst (dsnd xh))) .
 refine (acc_rel_pre_fiber f fh _) .
 refine (acc_rel_dsum _) .
 exact acc_x .
Defined.

(** [rec_pre] である関数は整礎性を後ろへ保つ。 *)
Definition wf_rel_pre
  {A : Type} {R : A -> A -> Type}
  {B : Type} {S : B -> B -> Type}
  (f : A -> B) (fh : rel_pre R S f)
  (wf_S : well_founded S) : well_founded R .
Proof.
 refine (fun x => _) .
 refine (acc_rel_pre f fh _) .
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
