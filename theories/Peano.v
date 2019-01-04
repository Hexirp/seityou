(** * Peano

    ペアノの公理に従った自然数についての定義を行う。 *)

Require Export Basis.

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".

(** 記法を使う。 *)
Import Basis.Notation .


(** 自然数。

    ペアノの公理は、最初の自然数と後者関数により自然数を定義するものである。
    標準ライブラリはこれにより自然数を定義していて、このライブラリもこれを
    使う。 *)
Inductive nat : Type
  :=
  | O : nat
  | S : nat -> nat
  .

Definition nat_match
  {P : nat -> Type}
  (case_O : P O)
  (case_S : forall n, P (S n))
  (x : nat) : P x .
Proof.
 refine (match x with O => _ | S xp => _ end) .
 -
  exact case_O .
 -
  exact (case_S xp) .
Defined.

Definition nat_rec
  {P : Type}
  (case_O : P)
  (case_S : P -> P)
  (x : nat) : P .
Proof.
 revert x .
 refine (fix go (x : nat) {struct x} : P := _) .
 refine (nat_match _ _ x) .
 -
  exact case_O .
 -
  refine (fun xp => _) .
  exact (case_S (go xp)) .
Defined.

Definition nat_rect
  {P : nat -> Type}
  (case_O : P O)
  (case_S : forall n, P n -> P (S n))
  (x : nat) : P x .
Proof.
 revert x .
 refine (fix go (x : nat) {struct x} : P x := _) .
 refine (nat_match _ _ x) .
 -
  exact case_O .
 -
  refine (fun xp => _) .
  exact (case_S xp (go xp)) .
Defined.


(** ** Functions *)

(** 後者関数の別名。 *)
Notation succ := S (only parsing) .

(** 前者関数。 [pred O = O] 。 *)
Definition pred : nat -> nat .
Proof.
 refine (nat_match _ _) .
 -
  exact O .
 -
  exact idmap .
Defined.

(** 加法。 *)
Definition add : nat -> nat -> nat .
Proof.
 refine (fun x => _) .
 refine (nat_rec _ _) .
 -
  exact x .
 -
  exact S .
Defined.

(** 乗法。 *)
Definition mul : nat -> nat -> nat .
Proof.
 refine (fun x => _) .
 refine (nat_rec _ _) .
 -
  exact O .
 -
  exact (add x) .
Defined.

(** 減法。結果が負の値になるときは、ゼロへ丸められる。 *)
Definition sub : nat -> nat -> nat .
Proof.
 refine (fun x => _) .
 refine (nat_rec _ _) .
 -
  exact x .
 -
  exact pred .
Defined.


(** ** Notations

    自然数の記法を定義する。 *)

From Coq Require Init.Datatypes .

Definition nat_from_std : Datatypes.nat -> nat .
Proof.
 refine (Datatypes.nat_rec _ _) .
 -
  exact Datatypes.O .
 -
  exact Datatypes.S .
Defined.

Module Notation .

  (** 記法が使われる文脈を設定する。 *)
  Delimit Scope nat_scope with nat.

  (** 文脈を開く。 *)
  Open Scope nat_scope .

  (** 文脈を型と結びつける。 *)
  Bind Scope nat_scope with nat.

  Check 1 .

End Notation .
