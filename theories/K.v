Add LoadPath "./theories".

Require Import Basis.


Declare ML Module "ltac_plugin".

Export Set Default Proof Mode "Classic".


Definition K : Type
  := forall (A : Type) (x : A) (P : paths x x -> Type),
    P idpath -> forall p, P p .

Definition UIP : Type
  := forall (A : Type) (x y : A) (p q : paths x y),
    paths p q .

Definition UIP_refl : Type
  := forall (A : Type) (x : A) (p : paths x x),
    paths p idpath .


Inductive JMeq (A : Type) (a : A) : forall B, B -> Type
  :=
  | JMeq_refl : JMeq A a A a
  .

Definition JMeq_elim_nodep
  (A : Type) (a : A) (P : forall B, B -> Type)
  (case_JMeq_refl : P A a)
  (B : Type) (b : B) (x : JMeq A a B b) : P B b
  := match x with JMeq_refl _ _ => case_JMeq_refl end .

Definition JMeq_elim
  (A : Type) (a : A) (P : forall B b, JMeq A a B b -> Type)
  (case_JMeq_refl : P A a (JMeq_refl A a))
  (B : Type) (b : B) (x : JMeq A a B b) : P B b x
  := match x with JMeq_refl _ _ => case_JMeq_refl end .

Arguments JMeq {_} _ {_} _ .
Arguments JMeq_refl {_ _}, [_] _ .
Arguments JMeq_elim_nodep {_ _ _} _ {_ _} _ .
Arguments JMeq_elim {_ _ _} _ {_ _} _ .

Definition JMeq_inverse
  {A B : Type} {a : A} {b : B}
  (x : JMeq a b) : JMeq b a
  := JMeq_elim_nodep (P := fun B' b' => JMeq b' a) JMeq_refl x .

Definition JMeq_concat
  {A B C : Type} {a : A} {b : B} {c : C}
  (x : JMeq a b) (y : JMeq b c) : JMeq a c
  := JMeq_elim_nodep (JMeq_elim_nodep JMeq_refl x) y .

Definition JMeq_transport
  {P : forall T, T -> Type} {A B : Type}
  {a : A} {b : B} (x : JMeq a b)
  (u : P A a) : P B b
  := JMeq_elim_nodep u x .

Definition JMeq_ap
  {P : forall T, T -> Type} {A B : Type}
  {a : A} {b : B} (f : forall T t, P T t)
  (x : JMeq a b) : JMeq (f A a) (f B b)
  := JMeq_elim_nodep (P := fun B' b' => JMeq (f A a) (f B' b')) JMeq_refl x .

Definition ap_dep_JMeq
  {A : Type} {B : A -> Type}
  (f : forall a, B a)
  {x y : A} (p : paths x y)
  : JMeq (f x) (f y)
  := paths_elim_nodep (P := fun y' => JMeq (f x) (f y')) JMeq_refl p .

Definition paths_JMeq
  {A : Type} {x y : A}
  (p : paths x y) : JMeq x y
  := paths_elim_nodep JMeq_refl p .

Definition JMeq_paths : Type
  := forall (A : Type) (x y : A), JMeq x y -> paths x y .

Definition JMeq_elim_nodep_eqlike : Type
  := forall (A : Type) (a : A) (P : A -> Type),
    P a -> forall a', JMeq a a' -> P a' .

Definition JMeq_elim_eqlike : Type
  := forall (A : Type) (a : A) (P : forall a', JMeq a a' -> Type),
    P a JMeq_refl -> forall a' x, P a' x .

Definition JMeq_K : Type
  := forall (A : Type) (x : A) (P : JMeq x x -> Type),
    P JMeq_refl -> forall p, P p .

Definition JMeq_UIP : Type
  := forall (A B : Type) (a : A) (b : B) (p : JMeq a b) (q : JMeq a b),
    paths p q .

Definition JMeq_UIP_refl : Type
  := forall (A : Type) (x : A) (p : JMeq x x),
    paths p JMeq_refl .

Definition UIP_JMeq
  {A : Type} {x y : A} (p q : paths x y) : JMeq p q .
Proof.
 refine (paths_elim (P := fun y' p' => JMeq p' q) _ p) .
 refine (paths_elim (P := fun y' q' => JMeq idpath q') _ q) .
 exact JMeq_refl .
Defined.

Definition UIP_JMeq_hetero
  {A : Type} {x y z : A} (p : paths x y) (q : paths x z) : JMeq p q .
Proof.
 refine (paths_elim (P := fun y' p' => JMeq p' q) _ p) .
 refine (paths_elim (P := fun z' q' => JMeq idpath q') _ q) .
 exact JMeq_refl .
Defined.

Definition UIP_refl_JMeq
  {A : Type} {x : A} (p : paths x x) : JMeq p (idpath x) .
Proof.
 refine (paths_elim (P := fun x' p' => JMeq p' idpath) _ p) .
 exact JMeq_refl .
Defined.

Definition UIP_refl_JMeq_hetero
  {A : Type} {x y : A} (p : paths x y) : JMeq p (idpath x) .
Proof.
 refine (paths_elim (P := fun y' p' => JMeq p' idpath) _ p) .
 exact JMeq_refl .
Defined.

Definition JMeq_UIP_JMeq
  {A B : Type} {a : A} {b : B} (p q : JMeq a b) : JMeq p q .
Proof.
 refine (JMeq_elim (P := fun B' b' p' => JMeq p' q) _ p) .
 refine (JMeq_elim (P := fun B' b' q' => JMeq JMeq_refl q') _ q) .
 exact JMeq_refl .
Defined.

Definition JMeq_UIP_JMeq_hetero
  {A B C : Type} {a : A} {b : B} {c : C} (p : JMeq a b) (q : JMeq a c)
  : JMeq p q .
Proof.
 refine (JMeq_elim (P := fun B' b' p' => JMeq p' q) _ p) .
 refine (JMeq_elim (P := fun C' c' q' => JMeq JMeq_refl q') _ q) .
 exact JMeq_refl .
Defined.

Definition JMeq_UIP_refl_JMeq
  {A : Type} {x : A} (p : JMeq x x) : JMeq p (JMeq_refl x) .
Proof.
 refine (JMeq_elim (P := fun A' x' p' => JMeq p' JMeq_refl) _ p) .
 exact JMeq_refl .
Defined.

Definition JMeq_UIP_refl_JMeq_hetero
  {A B : Type} {a : A} {b : B} (p : JMeq a b) : JMeq p (JMeq_refl a) .
Proof.
 refine (JMeq_elim (P := fun B' b' p' => JMeq p' JMeq_refl) _ p) .
 exact JMeq_refl .
Defined.


Section DependentEquality.

  Variable A : Type .
  Variable B : A -> Type .

  Arguments A : default implicits .
  Arguments B : default implicits .

  Inductive eq_dep (x : A) (xh : B x) : forall y, B y -> Type
    :=
    | eq_dep_refl : eq_dep x xh x xh
    .

  Definition eq_dep_elim_nodep
    (x : A) (xh : B x) (P : forall y, B y -> Type)
    (case_eq_dep_refl : P x xh)
    (y : A) (yh : B y)
    (x : eq_dep x xh y yh) : P y yh
    := match x with eq_dep_refl _ _ => case_eq_dep_refl end .

  Definition eq_dep_elim
    (x : A) (xh : B x) (P : forall y yh, eq_dep x xh y yh -> Type)
    (case_eq_dep_refl : P x xh (eq_dep_refl x xh))
    (y : A) (yh : B y)
    (x : eq_dep x xh y yh) : P y yh x
    := match x with eq_dep_refl _ _ => case_eq_dep_refl end .

  Arguments eq_dep {_} _ {_} _ .
  Arguments eq_dep_refl {_ _}, [_] _ .
  Arguments eq_dep_elim_nodep {_ _ _} _ {_ _} _ .
  Arguments eq_dep_elim {_ _ _} _ {_ _} .

  Definition eq_dep_inverse
    {x : A} {xh : B x} {y : A} {yh : B y}
    (p : eq_dep xh yh) : eq_dep yh xh
    := eq_dep_elim_nodep (P := fun y' yh' => eq_dep yh' xh) eq_dep_refl p .

  Definition eq_dep_concat
    {x : A} {xh : B x} {y : A} {yh : B y} {z : A} {zh : B z}
    (p : eq_dep xh yh) (q : eq_dep yh zh) : eq_dep xh zh
    := eq_dep_elim_nodep (eq_dep_elim_nodep eq_dep_refl p) q .

  Definition paths_eq_dep
    {x : A} {h i : B x} (p : paths h i) : eq_dep h i
    := paths_elim_nodep eq_dep_refl p .

  Definition eq_dep_JMeq
    {x y : A} {xh : B x} {yh : B y} (p : eq_dep xh yh) : JMeq xh yh
    := eq_dep_elim_nodep (P := fun y' yh' => JMeq xh yh') JMeq_refl p .

End DependentEquality.

Arguments eq_dep {_ _ _} _ {_} .
Arguments eq_dep_refl {_ _ _ _}, {_ _} [_] _ .

Definition JMeq_eq_dep_id
  {A B : Type} (a : A) (b : B) (p : JMeq a b)
  : @eq_dep Type idmap A a B b
  := JMeq_elim_nodep eq_dep_refl p .


Definition K_UIP (axiom_K : K) : UIP .
Proof.
 refine (fun A x y p => _) .
 refine (paths_elim (P := fun y' p' => forall q : paths x y', paths p' q) _ p) .
 refine (fun q => _) .
 refine (axiom_K A x (fun q' => paths idpath q') _ q) .
 exact idpath .
Defined.

Definition K_UIP_refl (axiom_K : K) : UIP_refl .
Proof.
 refine (fun A x p => _) .
 refine (axiom_K A x (fun p' => paths p' idpath) _ p) .
 exact idpath .
Defined.

Definition UIP_K (axiom_UIP : UIP) : K .
Proof.
 refine (fun A x P c p => _) .
 refine (paths_elim_nodep (P := fun p' => P p') c _) .
 exact (axiom_UIP A x x idpath p) .
Defined.

Definition UIP_UIP_refl (axiom_UIP : UIP) : UIP_refl .
Proof.
 refine (fun A x p => _) .
 exact (axiom_UIP A x x p idpath) .
Defined.

Definition UIP_refl_K (axiom_UIP_refl : UIP_refl) : K .
Proof.
 refine (fun A x P c p => _) .
 refine (paths_elim_nodep (P := fun p' => P p') c _) .
 refine (inverse _) .
 exact (axiom_UIP_refl A x p) .
Defined.

Definition UIP_refl_UIP (axiom_UIP_refl : UIP_refl) : UIP .
Proof.
 refine (fun A x y p => _) .
 refine (paths_elim (P := fun y' p' => forall q : paths x y', paths p' q) _ p) .
 refine (fun q => _) .
 refine (inverse _) .
 exact (axiom_UIP_refl A x q) .
Defined.
