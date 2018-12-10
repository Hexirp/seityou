(** * Peano

    ペアノの公理に従った自然数についての定義を行う。 *)

Require Export Basis.

Inductive nat : Type
  :=
  | O : nat
  | S : nat -> nat
  .
