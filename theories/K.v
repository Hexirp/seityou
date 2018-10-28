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
