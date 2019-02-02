Require Import Basis Path .

Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

Import Basis.Notation .
Import Basis.Notation.Path .

Inductive list (A : Type) : Type
  :=
  | nil : list A
  | cons : A -> list A -> list A
  .

Axiom deq : Type -> Type .

Axiom mk_deq : forall A, list A -> list A -> deq A .

Axiom rotate : Type .
