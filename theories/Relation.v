(** * Relation

    関係についての定義や定理を記述する。 *)

Require Import Basis .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .


(** [A] と [B] の上の関係。 *)
Definition rel (A B : Type) : Type := A -> B -> Type .

(** 逆関係。 *)
Definition rel_inv {A B : Type} (R : rel A B) : rel B A
  := fun x y => R y x .

(** 関係の結び。 *)
Inductive rel_sum {A B : Type} (R S : rel A B) : rel A B
  :=
  | mk_rel_sum : forall x y, sum (R x y) (S x y) -> rel_sum R S x y
  .

(** 関係の交わり。 *)
Inductive rel_prod {A B : Type} (R S : rel A B) : rel A B
  :=
  | mk_rel_prod : forall x y, prod (R x y) (S x y) -> rel_prod R S x y
  .

(** 関係の合成。 *)
Inductive rel_comp {A B C : Type} (R : rel B C) (S : rel A B) : rel A C
  :=
  | mk_rel_comp : forall x y z, R y z -> S x y -> rel_comp R S x z
  .

(** 関数を関係に変換する。 *)
Definition rel_fun {A B : Type} (f : A -> B) : rel A B
  := fun x y => f x = y .

(** [R] は [S] の部分関係である。 *)
Definition rel_sub {A B : Type} (R S : rel A B) : Type
  := forall x y, R x y -> S x y .


(** ** Well-foundness *)

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
    (case_mk_acc : forall Hps, P (mk_acc x Hps))
    (H : acc x) : P H
    := match H with mk_acc _ Hps => case_mk_acc Hps end .

  Definition acc_rec
    (P : A -> Type)
    (case_mk_acc : forall x, (forall xp, R xp x -> P xp) -> P x)
    (x : A) (xH : acc x) : P x .
  Proof.
   revert x xH .
   refine (fix go (x : A) (xH : acc x) {struct xH} : P x := _) .
   refine (acc_case_nodep x (P x) _ xH) .
   refine (fun xHps => _) .
   refine (case_mk_acc x _) .
   refine (fun xp xpR => _) .
   exact (go xp (xHps xp xpR)) .
  Defined.

  Definition acc_rect
    (P : forall x, acc x -> Type)
    (case_mk_acc
       : forall x xHps,
                        (forall xp xpR, P xp (xHps xp xpR)) ->
                         P x (mk_acc x xHps))
    (x : A) (xH : acc x) : P x xH .
  Proof.
   revert x xH .
   refine (fix go (x : A) (xH : acc x) {struct xH} : P x xH := _) .
   refine (acc_case x (P x) _ xH) .
   refine (fun xHps => _) .
   refine (case_mk_acc x xHps _) .
   refine (fun xp xpR => _) .
   exact (go xp (xHps xp xpR)) .
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
 revert H y yR .
 refine (acc_case_nodep _) .
 exact idmap .
Defined.


(** [R] は整礎である。 *)
Definition well_founded {A : Type} (R : A -> A -> Type) : Type
  := forall x : A, acc R x .



(** *** Well-founded induction

    「超限再帰的な定義」からの類推で、関数を整礎帰納法的に定義するともいえる。 *)

(** 非依存の整礎帰納法。 *)
Definition wf_ind_nodep
  {A : Type} {R : A -> A -> Type} {P : Type}
  (c : forall x, (forall xp, R xp x -> P) -> P)
  (wf_R : well_founded R) (x : A) : P
  := acc_rec c (wf_R x) .

(** 整礎帰納法。 *)
Definition wf_ind
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  (c : forall x : A, (forall xp : A, R xp x -> P xp) -> P x)
  (wf_R : well_founded R) (x : A) : P x
  := acc_rec c (wf_R x) .

Definition infinite_descent_0
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  (c : forall x : A, (forall xp : A, R xp x -> P xp -> empty) -> P x -> empty)
  (wf_R : well_founded R) (x : A) : P x -> empty
  := (wf_ind c wf_R x) .

Definition infinite_descent_1
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  (c : forall x  : (sigma xv, P xv),
                   (forall xp : (sigma xv, P xv),
                                 R (dfst xp) (dfst x) ->
                                 empty) ->
                    empty)
  (wf_R : well_founded R) (x : sigma xv, P xv) : empty .
Proof.
 revert x .
 refine (dsum_elim_nodep _) .
 refine (infinite_descent_0 _ wf_R) .
 refine (fun x I xH => _) .
 refine (c (dpair x xH) _) .
 refine (dsum_elim _) .
 refine (fun xp xpH xpR => _) .
 refine (I xp _ xpH) .
 change (R xp x) in xpR .
 exact xpR .
Defined.

Definition infinite_descent_2
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  (c : forall x : (sigma xv, P xv),
                   sigma xp : (sigma xvp, P xvp), R (dfst xp) (dfst x))
  (wf_R : well_founded R) (x : sigma xv, P xv) : empty .
Proof.
 revert x .
 refine (infinite_descent_1 _ wf_R) .
 refine (fun x I => _) .
 generalize (c x) .
 refine (dsum_elim_nodep _) .
 refine (fun xp xpR => _) .
 refine (I xp _) .
 exact xpR .
Defined.

Definition infinite_descent_3
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  (c : forall xv, P xv -> sigma xpv, prod (P xpv) (R xpv xv))
  (wf_R : well_founded R) (xv : A) (xh : P xv) : empty .
Proof.
 refine (infinite_descent_2 _ wf_R (dpair xv xh)) ; clear xv xh .
 refine (dsum_elim _) .
 refine (fun xv xh => _) .
 generalize (c xv xh) .
 refine (dsum_elim_nodep _) .
 refine (fun xpv => _) .
 refine (prod_elim_nodep _) .
 refine (fun xph xpr => _) .
 refine (dpair (dpair xpv xph) _) .
 change (R xpv xv) .
 exact xpr .
Defined.

(** 無限降下法。

    [infinite_descent_0 <-> infinite_descent_1 -> infinite_descent_2 <-> infinite_descent_3] 。

    *)
Notation infinite_descent := infinite_descent_3 .


(** *** Existence of infinite descending sequence *)

Section Chain .

  Variable A : Type .
  Variable R : A -> A -> Type .

  (** [A] の関係 [R] は [x : A] において反整礎である。 *)
  CoInductive chain (x : A) : Type
    :=
    | chain_build : (sigma xp, prod (R xp x) (chain xp)) -> chain x
    .

  Definition ds_chain
    (x : A) (P : Type)
    (H : chain x) : sigma xp, prod (R xp x) (chain xp)
    := match H with chain_build _ Hp => Hp end .

  Definition chain_corec
    (P : A -> Type)
    (case_ds_chain : forall (x : A) (xH : P x), sigma xp, prod (R xp x) (P xp))
    (x : A) (xH : P x) : chain x .
  Proof.
   revert x xH .
   refine (cofix go (x : A) (xH : P x) : chain x := _) .
   refine (chain_build x _) .
   generalize (case_ds_chain x xH) .
   refine (dsum_elim _) .
   refine (fun xp => _) .
   refine (prod_elim _) .
   refine (fun Hr Hp => _) .
   refine (dpair xp _) .
   refine (pair Hr _) .
   exact (go xp Hp) .
  Defined.

End Chain.

(** 参考文献:

    * https://ja.wikipedia.org/w/index.php?oldid=70335496
    * https://en.wikipedia.org/w/index.php?oldid=886562428
    * https://github.com/coq/coq/blob/f4cf212efd98d01a6470ea7bfd1034d52e928906/theories/Init/Wf.v

    *)
