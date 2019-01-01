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

Definition nat_rec
  {P : Type}
  (case_O : P)
  (case_S : P -> P)
  (x : nat) : P .
Proof.
 revert x .
 refine (fix go (x : nat) {struct x} : P := _) .
 refine (match x with O => _ | S xp => _ end) .
 -
  exact case_O .
 -
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
 refine (match x with O => _ | S xp => _ end) .
 -
  exact case_O .
 -
  exact (case_S xp (go xp)) .
Defined.
