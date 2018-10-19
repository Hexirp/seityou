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


Module Categorical.

  Definition initial {A : Type} : empty -> A
    := fun x => match x with end .

  Definition terminal {A : Type} : A -> unit
    := fun _ => tt .

  Definition coproduct {A B C : Type}
    : (A -> C) -> (B -> C) -> (sum A B -> C)
    := fun f g x =>
      match x with left _ _ y => f y | right _ _ z => g z end .

  Definition product {A B C : Type}
    : (A -> B) -> (A -> C) -> (A -> prod B C)
    := fun f g x => pair _ _ (f x) (g x) .

  Definition dependent_coproduct
    {X : Type} {A : X -> Type} {B : Type}
    : (forall x, A x -> B) -> (dsum X A -> B)
    := fun f x => match x with evi _ _ xv xH => f xv xH end .

  Definition dependent_product
    {X : Type} {A : Type} {B : X -> Type}
    : (forall x, A -> B x) -> (A -> dprod X B)
    := fun f x => fun y => f y x .

End Categorical.
