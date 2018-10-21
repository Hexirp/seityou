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

Arguments empty .
Arguments empty_elim_nodep {_} _ .
Arguments empty_elim {_} _ .

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

Arguments unit .
Arguments unit_elim_nodep {_} _ _ .
Arguments unit_elim {_} _ _ .

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

Arguments sum _ _ .
Arguments left {_ _} _ .
Arguments right {_ _} _ .
Arguments sum_elim_nodep {_ _ _} _ _ _ .
Arguments sum_elim {_ _ _} _ _ _ .

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

Arguments prod _ _ .
Arguments pair {_ _} _ _ .
Arguments prod_elim_nodep {_ _ _} _ _ .
Arguments prod_elim {_ _ _} _ _ .

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

Arguments exp _ _ .
Arguments exp_elim_nodep {_ _ _} _ _.
Arguments exp_elim {_ _ _} _ _.

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

Arguments dsum {_} _ .
Arguments evi {_ _} _ _ .
Arguments dsum_elim_nodep {_ _ _} _ _ .
Arguments dsum_elim {_ _ _} _ _ .

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

Arguments dprod {_} _ .
Arguments dprod_elim_nodep {_ _ _} _ _.
Arguments dprod_elim {_ _ _} _ _.

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

Arguments paths {_} _ _ .
Arguments idpath {_ _} , [_] _ .
Arguments paths_elim_nodep {_ _ _} _ {_} _ .
Arguments paths_elim {_ _ _} _ {_} _ .


Module Functional.

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
    := paths_elim_nodep (P := fun y' => paths y' x) idpath p .

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
    := paths_elim_nodep (P := fun y' => paths (f x) (f y')) idpath p .

End Functional.


Module Categorical.

  Definition initial {A : Type} : empty -> A
    := fun x => match x with end .

  Definition terminal {A : Type} : A -> unit
    := fun _ => tt .

  Definition coproduct {A B C : Type}
    : (A -> C) -> (B -> C) -> (sum A B -> C)
    := fun f g x =>
      match x with left y => f y | right z => g z end .

  Definition product {A B C : Type}
    : (A -> B) -> (A -> C) -> (A -> prod B C)
    := fun f g x => pair (f x) (g x) .

  Definition dependent_coproduct
    {X : Type} {A : X -> Type} {B : Type}
    : (forall x, A x -> B) -> (dsum A -> B)
    := fun f x => match x with evi xv xH => f xv xH end .

  Definition dependent_product
    {X : Type} {A : Type} {B : X -> Type}
    : (forall x, A -> B x) -> (A -> dprod B)
    := fun f x => fun y => f y x .

End Categorical.


Module Homotopical.

  Export Functional.

  Definition ap00
    {A B : Type}
    (f : A -> B)
    (x : A)
    : B
    := f x .

  Definition ap01
    {A B : Type}
    (f : A -> B)
    {x y : A} (p : paths x y)
    : paths (f x) (f y)
    := ap f p .

  Definition ap10
    {A B : Type}
    {f g : A -> B} (p : paths f g)
    (x : A)
    : paths (f x) (g x)
    := paths_elim_nodep (P := fun g' => paths (f x) (g' x)) idpath p .

  Definition ap11
    {A B : Type}
    {f g : A -> B} (p : paths f g)
    {x y : A} (q : paths x y)
    : paths (f x) (g y)
    := paths_elim_nodep (P := fun g' => paths (f x) (g' y)) (ap f q) p .

  Definition ap01_2
    {A B C : Type}
    (f : A -> B -> C)
    (x y : A) (p : paths x y)
    (z w : B) (q : paths z w)
    : paths (f x z) (f y w)
    := ap11 (ap f p) q .

  Definition apD
    {A : Type} {B : A -> Type}
    (f : forall a, B a)
    {x y : A} (p : paths x y)
    : paths (transport p (f x)) (f y)
    := paths_elim idpath p
      (P := fun y' p' => paths (transport p' (f x)) (f y'))
      .

  Definition pwpaths
    {A : Type} {B : A -> Type} (f g : forall a, B a) : Type
    := forall a, paths (f a) (g a) .

  Definition pwpaths_paths
    {A B : Type}
    {f g : A -> B} (p : paths f g)
    : pwpaths f g
    := ap10 p .

  Definition pwpaths_compose10
    {A B C : Type}
    {f g : B -> C} (p : pwpaths f g)
    (h : A -> B)
    : pwpaths (compose f h) (compose g h)
    := composeD p h .

End Homotopical.