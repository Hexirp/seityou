Unset Elimination Schemes.


Notation "x -> y" := (forall (_ : x), y)
  (at level 99, right associativity, y at level 200)
  .

Inductive empty : Type
  :=
  .

Definition empty_elim_nodep (P : Type) (x : empty) : P
  := match x with end .

Definition empty_elim (P : empty -> Type) (x : empty) : P x
  := match x with end .

Inductive unit : Type
  :=
  | tt : unit
  .

Definition unit_elim_nodep
  (P : Type) (case_tt : P) (x : unit) : P
  := match x with tt => case_tt end .

Definition unit_elim
  (P : unit -> Type) (case_tt : P tt) (x : unit) : P x
  := match x with tt => case_tt end .

Inductive sum (A : Type) (B : Type) : Type
  :=
  | left : A -> sum A B
  | right : B -> sum A B
  .

Definition sum_elim_nodep
  (A : Type) (B : Type) (P : Type)
  (case_left : A -> P) (case_right : B -> P)
  (x : sum A B) : P
  := match x with
    | left _ _ a => case_left a
    | right _ _ b => case_right b
  end .

Definition sum_elim
  (A : Type) (B : Type) (P : sum A B -> Type)
  (case_left : forall a, P (left A B a))
  (case_right : forall b, P (right A B b))
  (x : sum A B) : P x
  := match x with
    | left _ _ a => case_left a
    | right _ _ b => case_right b
  end .

Inductive prod (A : Type) (B : Type) : Type
  :=
  | pair : A -> B -> prod A B
  .

Definition prod_elim_nodep
  (A : Type) (B : Type) (P : Type)
  (case_pair : A -> B -> P)
  (x : prod A B) : P
  := match x with pair _ _ a b => case_pair a b end .

Definition prod_elim
  (A : Type) (B : Type) (P : prod A B -> Type)
  (case_pair : forall a b, P (pair A B a b))
  (x : prod A B) : P x
  := match x with pair _ _ a b => case_pair a b end .

Definition exp (A B : Type) : Type
  := A -> B.

Definition exp_elim_nodep
  (A : Type) (B : Type) (P : Type)
  (case : (A -> B) -> P)
  (x : exp A B) : P
  := case x .

Definition exp_elim
  (A : Type) (B : Type) (P : (A -> B) -> Type)
  (case : forall f, P f)
  (x : exp A B) : P x
  := case x .

Inductive dsum (A : Type) (B : A -> Type) : Type
  :=
  | evi : forall x : A, B x -> dsum A B
  .

Definition dsum_elim_nodep
  (A : Type) (B : A -> Type) (P : Type)
  (case_evi : forall x, B x -> P)
  (x : dsum A B) : P
  := match x with evi _ _ xv xH => case_evi xv xH end .

Definition dsum_elim
  (A : Type) (B : A -> Type) (P : dsum A B -> Type)
  (case_evi : forall xv xH, P (evi A B xv xH))
  (x : dsum A B) : P x
  := match x with evi _ _ xv xH => case_evi xv xH end .

Definition dprod (A : Type) (B : A -> Type) : Type
  := forall x : A, B x .

Definition dprod_elim_nodep
  (A : Type) (B : A -> Type) (P : Type)
  (case : (forall x, B x) -> P)
  (x : dprod A B) : P
  := case x .

Definition dprod_elim
  (A : Type) (B : A -> Type) (P : dprod A B -> Type)
  (case : forall f, P f)
  (x : dprod A B) : P x
  := case x .

Inductive paths (A : Type) (a : A) : A -> Type
  :=
  | idpath : paths A a a
  .

Definition paths_elim_nodep
  (A : Type) (a : A) (P : A -> Type)
  (case_idpath : P a)
  (a' : A) (x : paths A a a') : P a'
  := match x with idpath _ _ => case_idpath end .

Definition paths_elim
  (A : Type) (a : A) (P : forall a', paths A a a' -> Type)
  (case_idpath : P a (idpath A a))
  (a' : A) (x : paths A a a') : P a' x
  := match x with idpath _ _ => case_idpath end .


Module Functional.

  Local Arguments empty .
  Local Arguments empty_elim_nodep {_} _ .
  Local Arguments empty_elim {_} _ .

  Local Arguments unit .
  Local Arguments unit_elim_nodep {_} _ _ .
  Local Arguments unit_elim {_} _ _ .

  Local Arguments sum _ _ .
  Local Arguments left {_ _} _ .
  Local Arguments right {_ _} _ .
  Local Arguments sum_elim_nodep {_ _ _} _ _ _ .
  Local Arguments sum_elim {_ _ _} _ _ _ .

  Local Arguments prod _ _ .
  Local Arguments pair {_ _} _ _ .
  Local Arguments prod_elim_nodep {_ _ _} _ _ .
  Local Arguments prod_elim {_ _ _} _ _ .

  Local Arguments exp _ _ .
  Local Arguments exp_elim_nodep {_ _ _} _ _.
  Local Arguments exp_elim {_ _ _} _ _.

  Local Arguments dsum {_} _ .
  Local Arguments evi {_ _} _ _ .
  Local Arguments dsum_elim_nodep {_ _ _} _ _ .
  Local Arguments dsum_elim {_ _ _} _ _ .

  Local Arguments dprod {_} _ .
  Local Arguments dprod_elim_nodep {_ _ _} _ _.
  Local Arguments dprod_elim {_ _ _} _ _.

  Local Arguments paths {_} _ _ .
  Local Arguments idpath {_ _} , [_] _ .
  Local Arguments paths_elim_nodep {_ _ _} _ {_} _ .
  Local Arguments paths_elim {_ _ _} _ {_} _ .

  Definition idmap {A} : A -> A
    := fun x => x .

  Definition const {A B} : A -> B -> A
    := fun x y => x .

  Definition compose {A B C} : (B -> C) -> (A -> B) -> (A -> C)
    := fun f g x => f (g x) .

  Definition compose_dep
    {A B C} (f : forall b, C b) (g : A -> B)
    : forall a, C (g a)
    := fun x => f (g x) .

  Definition absurd {A} : empty -> A
    := empty_elim_nodep .

  Definition fst {A B} : prod A B -> A
    := prod_elim_nodep (fun a _ => a) .

  Definition snd {A B} : prod A B -> B
    := prod_elim_nodep (fun _ b => b) .

  Definition uncurry {A B C} : (A -> B -> C) -> (prod A B -> C)
    := prod_elim_nodep .

  Definition dsum_fst {A B} : @dsum A B -> A
    := dsum_elim_nodep (fun xv _ => xv) .

  Definition dsum_snd {A B} (x : @dsum A B) : B (dsum_fst x)
    := dsum_elim (P := fun x' => B (dsum_fst x')) (fun _ xH => xH) x .

  Definition paths_elim_nodep_nop
    {A : Type} {P : A -> A -> Type}
    (case_idpath : forall a, P a a)
    (a a' : A) (x : paths a a') : P a a'
    := paths_elim_nodep (case_idpath a) x .

  Definition paths_elim_nop
    {A : Type} {P : forall a a', paths a a' -> Type}
    (case_idpath : forall a, P a a idpath)
    (a a' : A) (x : paths a a') : P a a' x
    := paths_elim (case_idpath a) x .

  Definition inverse
    {A : Type} (x y : A)
    (p : paths x y) : paths y x
    := paths_elim_nodep (P := fun x' => paths x' x) idpath p .

  Definition concat
    {A : Type} {x y z : A}
    (p : paths x y) (q : paths y z) : paths x z
    := paths_elim_nodep (paths_elim_nodep idpath p) q .

  Definition transport
    {A : Type} {P : A -> Type}
    {x y : A} (p : paths x y)
    (u : P x) : P y
    := paths_elim_nodep u p .

  Definition ap
    {A B : Type} (f : A -> B)
    {x y : A} (p : paths x y)
    : paths (f x) (f y)
    := paths_elim_nodep (P := fun x' => paths (f x) (f x')) idpath p .

End Functional.


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
