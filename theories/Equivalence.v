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

Module Notation .

  Notation "f 'o' g" := (compose f g) (at level 40, right associativity) .

  Notation "f 'oP' p" := (pwpaths_compose01 f p) (at level 40, no associativity) .

  Notation "p 'Po' h" := (pwpaths_compose10 p h) (at level 40, no associativity) .

End Notation .

Import Notation .

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
  {A B C D : Type} {g h : B -> C}
  (f : C -> D) (p : pwpaths g h) (i : A -> B)
  : pwpaths (f o g o i) (f o h o i) .
Proof.
 refine (f oP _) .
 refine (_ Po i) .
 exact p .
Defined.

Lemma retr_compose
  {A B C : Type} {f : A -> B} {g : B -> A} {h : B -> C} {i : C -> B}
  (r_fg : retraction f g) (r_hi : retraction h i)
  : retraction (h o f) (g o i) .
Proof.
 unfold retraction .
 change (pwpaths (h o (f o g) o i) idmap) .
 refine (pwpaths_concat (g := h o i) _ _) .
 -
  change (pwpaths (h o (f o g) o i) (h o idmap o i)) .
  refine (h oP (_ Po i)) .
  exact r_fg .
 -
  exact r_hi .
Defined.

Lemma sect_compose
  {A B C : Type} {f : A -> B} {g : B -> A} {h : B -> C} {i : C -> B}
  (s_fg : section f g) (s_hi : section h i)
  : section (h o f) (g o i) .
Proof.
 unfold section .
 change (pwpaths (g o (i o h) o f) idmap) .
 refine (pwpaths_concat (g := g o f) _ _) .
 -
  change (pwpaths (g o (i o h) o f) (g o idmap o f)) .
  refine (g oP (_ Po f)) .
  exact s_hi .
 -
  exact s_fg .
Defined.

Lemma is_adj_compose
  {A B C : Type} {f : A -> B} {g : B -> A} {h : B -> C} {i : C -> B}
  (r_fg : retraction f g) (s_fg : section f g)
  (r_hi : retraction h i) (s_hi : section h i)
  (fg : is_adjoint r_fg s_fg) (hi : is_adjoint r_hi s_hi)
  : is_adjoint (retr_compose r_fg r_hi) (sect_compose s_fg s_hi) .
Proof.
 unfold is_adjoint .
 unfold retr_compose, sect_compose .
 unfold is_adjoint in fg, hi .
 change (
   pwpaths
     (pwpaths_concat ((h oP (r_fg Po i)) Po (h o f)) (r_hi Po (h o f)))
     (pwpaths_concat ((h o f) oP (g oP (s_hi Po f))) ((h o f) oP s_fg))
   ) .

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
