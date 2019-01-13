Require Import Basis .

Inductive sorted_list {A : Type} (R : A -> A -> Type) (x : A) : Type
  :=
  | s_nil : sorted_list R x
  | s_cons : forall (y : A) (xs : sorted_list R y), forall_le R x y xs -> sorted_list R x
with forall_le {A : Type} (R : A -> A -> Type) (x : A) : forall y : A, sorted_list y -> Type
  :=
  | f_nil : forall y : A, R x y -> forall_le R x y (s_nil R y)
  | f_cons : forall (y z : A) (xs : sorted_list R z), forall_le R y z 
  .
