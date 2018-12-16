(** * Equivalence

    等価性に関する定理や定義。 *)


Require Export Homotopy.
Require Import Path.


Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


Lemma retr_idmap
  {A : Type}
  : @retraction A A idmap idmap .
Proof.
 refine (fun x => _) .
 exact (idpath x) .
Defined.

Lemma sect_idmap
  {A : Type}
  : @section A A idmap idmap .
Proof.
 refine (fun x => _) .
 exact (idpath x) .
Defined.

Lemma is_adj_idmap
  {A : Type}
  : @is_adjoint A A idmap idmap retr_idmap sect_idmap .
Proof.
 refine (fun x => _) .
 exact (idpath (idpath x)) .
Defined.

Definition is_equiv_idmap {A : Type} : is_equiv (@idmap A) .
Proof.
 refine (dpair idmap _) .
 refine (dpair retr_idmap _) .
 refine (dpair sect_idmap _) .
 exact is_adj_idmap .
Defined.

Definition equiv_idmap {A : Type} : equiv A A .
Proof.
 refine (dpair idmap _) .
 exact is_equiv_idmap .
Defined.

Lemma pwpaths_concat
  {A B : Type} {f g h : A -> B}
  (p : pwpaths f g) (q : pwpaths g h)
  : pwpaths f h .
Proof.
 refine (fun x => _) .
 refine (concat (y := g x) _ _) .
 -
  exact (p x) .
 -
  exact (q x) .
Defined.

Lemma pwpaths_compose11
  {A B C D : Type} {f : C -> D} {g h : B -> C} {i : A -> B}
  (p : pwpaths g h)
  : pwpaths (compose f (compose g i)) (compose f (compose h i)) .
Proof.
 refine (pwpaths_compose01 f _) .
 refine (pwpaths_compose10 _ i) .
 exact p .
Defined.

Lemma retr_compose
  {A B C : Type} {f : A -> B} {g : B -> A} {h : B -> C} {i : C -> B}
  (fg : is_equiv_rel f g) (hi : is_equiv_rel h i)
  : retraction (compose h f) (compose g i) .
Proof.
 unfold retraction .
 change (pwpaths (compose h (compose (compose f g) i)) idmap) .
 refine (pwpaths_concat (g := compose h i) _ _) .
 -
  

Lemma is_equiv_rel_compose
  {A B C : Type} {f : A -> B} {g : B -> A} {h : B -> C} {i : C -> B}
  (fg : is_equiv_rel f g) (hi : is_equiv_rel h i)
  : is_equiv_rel (compose h f) (compose g i) .
Proof.
 

Definition is_equiv_compose
  {A B C : Type} {f : A -> B} {g : B -> C}
  (f_iv : is_equiv f) (g_iv : is_equiv g)
  : is_equiv (compose g f) .
Proof.
 refine (dpair (compose (equiv_inv f_iv) (equiv_inv g_iv)) _) .
