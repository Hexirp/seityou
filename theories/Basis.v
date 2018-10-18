Unset Elimination Schemes.

Notation "x -> y" := (forall (_ : x), y)
  (at level 99, right associativity, y at level 200)
  .

Inductive empty : Type
  :=
  .

Inductive unit : Type
  :=
  | tt : unit
  .

Inductive sum (A : Type) (B : Type) : Type
  :=
  | left : A -> sum A B
  | right : B -> sum A B
  .

Inductive prod (A : Type) (B : Type) : Type
  :=
  | pair : A -> B -> prod A B
  .

Inductive dsum (A : Type) (B : A -> Type) : Type
  :=
  | evi : forall x : A, B x -> dsum A B
  .

Definition dprod (A : Type) (B : A -> Type) : Type
  := forall x : A, B x .
