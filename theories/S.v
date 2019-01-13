Require Import Basis .

Inductive sorted_list {A : Type} (R : A -> A -> Type) (x : A) : Type
  :=
  | s_nil : sorted_list R x
  | s_cons : forall (y : A) (xs : sorted_list R y), R x y -> sorted_list R x
  .
