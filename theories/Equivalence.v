(** * Equivalence

    等価性に関する定理や定義。 *)

Require Export Homotopy.

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".

(** 記法を使う。 *)
Import Homotopy.Notation .


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

Lemma retr_compose
  {A B C : Type} {f : A -> B} {g : B -> A} {h : B -> C} {i : C -> B}
  (r_fg : retraction f g) (r_hi : retraction h i)
  : retraction (h o f) (g o i) .
Proof.
 unfold retraction ; unfold retraction in r_fg, r_hi .
 change (h o (f o g) o i == idmap) .
 refine (concat_pw (g := h o i) _ _) .
 -
  change (h o (f o g) o i == h o idmap o i) .
  refine (wiskerR_pw_fn _ i) .
  refine (wiskerL_pw_fn h _) .
  exact r_fg .
 -
  exact r_hi .
Defined.

Lemma sect_compose
  {A B C : Type} {f : A -> B} {g : B -> A} {h : B -> C} {i : C -> B}
  (s_fg : section f g) (s_hi : section h i)
  : section (h o f) (g o i) .
Proof.
 unfold section ; unfold section in s_fg, s_hi .
 change (g o (i o h) o f == idmap) .
 refine (concat_pw (g := g o f) _ _) .
 -
  change (g o (i o h) o f == g o idmap o f) .
  refine (wiskerR_pw_fn _ f) .
  refine (wiskerL_pw_fn g _) .
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
 unfold is_adjoint ; unfold is_adjoint in fg, hi .
 unfold retraction in r_fg, r_hi .
 unfold section in s_fg, s_hi .
 unfold retr_compose .
 unfold sect_compose .
 

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
