Require Import Basis .

Inductive sorted_list {A : Type} (R : A -> A -> Type)
  :=
  | s_nil : sorted_list R
  | s_cons : forall (x : A) (xs : sorted_list R), forall_le R x xs -> sorted_list R
with forall_le {A : Type} (R : A -> A -> Type) : A -> sorted_list R -> Type
  :=
  | f_nil : forall x : A, forall_le R x (s_nil R)
  | f_cons : forall (x : A) (y : A) (ys : sorted_list R) (yH : forall_le R y ys), R x y -> forall_le R x ys -> forall_le R x (s_cons R y ys yH)
.
