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



(** Well-founded induction

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

(** 無限降下法。 *)
Notation infinite_descent := infinite_descent_3 .


(** Fixpoints by well-founded induction

    整礎帰納法により構成される関数の不動点について。 *)

Section FixPointNodep .

  Variable A : Type .
  Variable R : A -> A -> Type .
  Variable P : Type .
  Variable f : forall x : A, (forall y : A, R y x -> P) -> P .

  (** [f] の不動点。 *)
  Definition fix_f_acc_nodep {x : A} (xH : acc R x) : P
    := acc_rec f xH .

  (** [fix_f] は不動点である。 *)
  Definition path_fix_f_acc_nodep
    {x : A} {xH : acc R x}
    : paths (f x (fun y yR => @fix_f_acc_nodep y (@inv_acc A R x xH y yR)))
            (@fix_f_acc_nodep x xH) .
  Proof.
   revert x xH .
   refine (@acc_rect A R ?[ex_P] _) .
   refine (fun x xHps I => _) .

   change (fix_f_acc_nodep (mk_acc xHps))
     with (acc_rec f (mk_acc xHps)) .

   change (acc_rec f (mk_acc xHps))
     with (f x (fun y yR => acc_rec f (xHps y yR))) .

   change (fun y yR => acc_rec f (xHps y yR))
     with (fun y yR => fix_f_acc_nodep (xHps y yR)) .

   change (fun y yR => fix_f_acc_nodep (xHps y yR))
     with (fun y yR => fix_f_acc_nodep (inv_acc (mk_acc xHps) (y := y) yR)) .

   exact idpath .
  Defined.

End FixPointNodep .

Arguments fix_f_acc_nodep {_ _ _} _ {_} _ .
Arguments path_fix_f_acc_nodep {_ _ _ _ _ _} .

(** [f] の全域に渡る不動点。 *)
Definition fix_f_nodep
  {A : Type} {R : A -> A -> Type} {P : Type}
  (f : forall x : A, (forall y : A, R y x -> P) -> P)
  (wf_R : well_founded R) (x : A) : P
  := fix_f_acc_nodep f (wf_R x) .

Section FixPoint .

  Variable A : Type .
  Variable R : A -> A -> Type .
  Variable P : A -> Type .
  Variable f : forall x : A, (forall y : A, R y x -> P y) -> P x .

  (** [f] の不動点。 *)
  Definition fix_f_acc {x : A} (xH : acc R x) : P x
    := acc_rec f xH .

  (** [fix_f] は不動点である。 *)
  Definition path_fix_f_acc {x : A} {xH : acc R x}
    : paths (f x (fun y yR => @fix_f_acc y (@inv_acc A R x xH y yR)))
            (@fix_f_acc x xH) .
  Proof.
   revert x xH .
   refine (@acc_rect A R ?[P] _) .
   refine (fun x xHps I => _) .

   change (fix_f_acc (mk_acc xHps))
     with (acc_rec f (mk_acc xHps)) .

   change (acc_rec f (mk_acc xHps))
     with (f x (fun y yR => acc_rec f (xHps y yR))) .

   change (fun y yR => acc_rec f (xHps y yR))
     with (fun y yR => fix_f_acc (xHps y yR)) .

   change (fun y yR => fix_f_acc (xHps y yR))
     with (fun y yR => fix_f_acc (inv_acc (mk_acc xHps) (y := y) yR)) .

   exact idpath .
  Defined.

End FixPoint .

Arguments fix_f_acc {_ _ _} _ {_} _ .
Arguments path_fix_f_acc {_ _ _ _ _ _} .

(** [f] の全域に渡る不動点。 *)
Definition fix_f
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  (f : forall x : A, (forall y : A, R y x -> P y) -> P x)
  (wf_R : well_founded R) (x : A) : P x
  := fix_f_acc f (wf_R x) .



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


Section Chain .

  Variable A : Type .
  Variable R : A -> A -> Type .

  (** [A] の関係 [R] は [x : A] において反整礎である。 *)
  CoInductive chain (x : A) : Type
    :=
    | mk_chain : forall xp, R xp x -> chain xp -> chain x
    .

  Definition chain_case_nodep
    (x : A) (P : Type)
    (case_mk_chain : forall xp, R xp x -> chain xp -> P)
    (H : chain x) : P
    := match H with mk_chain _ xp Hr Hp => case_mk_chain xp Hr Hp end .

  Definition chain_case
    (x : A) (P : chain x -> Type)
    (case_mk_chain : forall xp Hr Hp, P (mk_chain x xp Hr Hp))
    (H : chain x) : P H
    := match H with mk_chain _ xp Hr Hp => case_mk_chain xp Hr Hp end .

  Definition chain_corec
    (P : A -> Type)
    (case_mk_chain : forall x (xH : P x), sigma xp, prod (R xp x) (P xp))
    (x : A) (xH : P x) : chain x .
  Proof.
   revert x xH .
   refine (cofix go (x : A) (xH : P x) : chain x := _) .
   generalize (case_mk_chain x xH) .
   refine (dsum_elim _) .
   refine (fun xp => _) .
   refine (prod_elim _) .
   refine (fun Hr Hp => _) .
   refine (mk_chain x xp Hr _) .
   exact (go xp Hp) .
  Defined.

End Acc.


(** *** Others *)

Section AccPath .

  Variable A : Type .
  Variable R : A -> A -> Type .

  (** [acc] についての弱い道。

      この場合は外延的な等しさ／点ごとの道になる。 *)
  Inductive acc_path (x : A) : acc R x -> acc R x -> Type
    :=
    | mk_acc_path
      : forall r s,
                    (forall xp xpR, acc_path xp (r xp xpR) (s xp xpR)) ->
                     acc_path x (mk_acc r) (mk_acc s)
    .

End AccPath .

(** 参考文献:

    * https://github.com/coq/coq/blob/f4cf212efd98d01a6470ea7bfd1034d52e928906/theories/Init/Wf.v

    *)
