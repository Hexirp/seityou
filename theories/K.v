Add LoadPath "./theories".

Require Import Basis.


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


Inductive eq_dep
  (A : Type) (P : A -> Type) (x : A) (h : P x) : forall y, P y -> Type
  :=
  | eq_dep_refl : eq_dep A P x h x h
  .


Declare ML Module "ltac_plugin".

Export Set Default Proof Mode "Classic".


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
