(** * Equivalence

    等価性に関する定理や定義。 *)


Require Export Homotopy.
Require Import Path.


Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


Lemma retraction_idmap
  {A : Type}
  : @retraction A A idmap idmap .
Proof.
 refine (fun x => _) .
 exact (idpath x) .
Defined.

Lemma section_idmap
  {A : Type}
  : @section A A idmap idmap .
Proof.
 refine (fun x => _) .
 exact (idpath x) .
Defined.

Lemma is_adjoint_idmap
  {A : Type}
  : @is_adjoint A A idmap idmap retraction_idmap section_idmap .
Proof.
 refine (fun x => _) .
 exact (idpath (idpath x)) .
Defined.

Definition is_equiv_idmap {A : Type} : is_equiv (@idmap A) .
Proof.
 refine (dpair idmap _) .
 refine (dpair retraction_idmap _) .
 refine (dpair section_idmap _) .
 exact is_adjoint_idmap .
Defined.

Definition equiv_idmap {A : Type} : equiv A A .
Proof.
 refine (dpair idmap _) .
 exact is_equiv_idmap .
Defined.

Definition is_equiv_compose
  {A B C : Type} {f : A -> B} {g : B -> C}
  (f_iv : is_equiv f) (g_iv : is_equiv g)
  : is_equiv (compose g f) .
Proof.
 refine (dpair (compose (equiv_inv f_iv) (equiv_inv g_iv)) _) .
