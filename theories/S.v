Require Import Basis .

Inductive list (A : Type) : Type
  :=
  | nil : list A
  | cons : A -> list A -> list A
  .

Inductive forall_elements (A : Type) (P : A -> Type) : list A -> Type
  :=
  | fe_nil : forall_elements A P (nil A)
  | fe_cons
          : forall (x : A) (xs : list A),
              P x -> forall_elements A P xs -> forall_elements A P (cons A x xs)
  .

Inductive is_sorted (A : Type) (R : A -> A -> Type) : list A -> Type
  :=
  | iss_nil : is_sorted A R (nil A)
  | iss_cons
          : forall (x : A) (xs : list A),
              forall_elements A (R x) xs -> is_sorted A R xs -> is_sorted A R (cons A x xs)
  .

Inductive sorted_list (A : Type) (R : A -> A -> Type) : Type
  :=
  | mk_sl : forall x : list A, is_sorted A R x -> sorted_list A R
  .
