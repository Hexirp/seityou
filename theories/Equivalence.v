(** * Equivalence

    等価性に関する定理や定義。 *)

Require Export Basis .
Require Export Path .
Require Export Pwpath .
Require Export Homotopy.

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin".
Set Default Proof Mode "Classic".

(** 記法を使う。 *)
Import Basis.Notation .
Import Basis.Notation.Path .
Import Path.Notation .
Import Pwpath.Notation .
Import Pwpath.Notation.Chain .


(** ** Equivalence'

    Equivalence を使いやすい形で再定義する。
    これらは [change] で元の定義と互いに移り合う。 *)

(** [s] は [r] の断面 (section) である。

    * [s] は [r] の右逆射である。
    * [r] は [s] の引き込み (retraction) である。
    * [r] は [s] の左逆射である。 *)
Definition section
  {A B : Type}
  (s : A -> B) (r : B -> A)
  : Type
  := r o s == idmap .

(** [r] は [s] の引き込み (retraction) である。

    * [r] は [s] の左逆射である。
    * [s] は [r] の断面 (section) である。
    * [s] は [r] の右逆射である。 *)
Definition retraction
  {A B : Type}
  (r : B -> A) (s : A -> B)
  : Type
  := r o s == idmap .

(** [f] と [g] は [retr] と [sect] を通じて随伴的である。 *)
Definition is_adjoint
  {A B : Type}
  {f : A -> B} {g : B -> A}
  (retr : retraction f g) (sect : section f g)
  : Type
  := retr <@ f == f @> sect .

(** [A] と [B] は [f] と [g] を通じて等価 (equivalence) である。 *)
Definition is_equiv_rel
  {A B : Type}
  (f : A -> B) (g : B -> A)
  : Type
  := sigma retr sect, is_adjoint (f := f) (g := g) retr sect .

(** [f] は等価射 (equivalence) である。 *)
Definition is_equiv
  {A B : Type} (f : A -> B)
  : Type
  := sigma equiv_inv, is_equiv_rel f equiv_inv .

(** [A] と [B] は等価 (equivalence) である。 *)
Definition equiv
  (A B : Type) : Type
  := sigma f, is_equiv (A := A) (B := B) f .


(** ** equiv_idmap *)

Lemma retr_idmap
  {A : Type}
  : @retraction A A idmap idmap .
Proof.
 exact 1 .
Defined.

Lemma sect_idmap
  {A : Type}
  : @section A A idmap idmap .
Proof.
 exact 1 .
Defined.

Lemma is_adj_idmap
  {A : Type}
  : @is_adjoint A A idmap idmap retr_idmap sect_idmap .
Proof.
 exact 1 .
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


(** ** equiv_compose *)

Lemma retr_compose
  {A B C : Type} {f : A -> B} {g : B -> A} {h : B -> C} {i : C -> B}
  (r_fg : retraction f g) (r_hi : retraction h i)
  : retraction (h o f) (g o i) .
Proof.
 unfold retraction ; unfold retraction in r_fg, r_hi .
 change (h o (f o g) o i == idmap) .
  refine (
      (* h o (f o g) o i *)
    _
      @[ h o i ]
    _
      (* idmap *)
    ) .
 -
  change (h o (f o g) o i == h o idmap o i) .
  refine (h @> _ <@ i) .
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
  refine (
      (* g o (i o h) o f *)
    _
      @[ g o f ]
    _
      (* idmap *)
    ) .
 -
  change (g o (i o h) o f == g o idmap o f) .
  refine (g @> _ <@ f) .
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
 unfold retr_compose, sect_compose .
 refine (
     (* (h @> r_fg <@ i) @ r_hi <@ h o f *)
   _
     @[ (h @> r_fg <@ i <@ h o f) @ (r_hi <@ h o f) ]
   _
     @[ ((h @> r_fg <@ i o h) <@ f) @ ((h @> s_hi) <@ f) ]
   _
     @[ (h @> ((r_fg <@ i o h) @ s_hi)) <@ f ]
   _
     @[ h @> ((f o g @> s_hi) @ r_fg) <@ f ]
   _
     @[ (h @> (f o g @> s_hi) <@ f) @ (h @> r_fg <@ f) ]
   _
     @[ (h o f @> (g @> s_hi <@ f)) @ (h o f @> s_fg) ]
   _
     (* h o f @> (g @> s_hi <@ f) @ s_fg *)
   ).
 -
  exact wiskerR_pw_fn_pp .
 -
  admit.
 -
  refine (
    _ @[ (h @> r_fg <@ i o h) @ (h @> s_hi) <@ f ] _
    ) .
  +
   exact wiskerR_pw_fn_pp^ .
  +
   refine (wiskerR_pw_fn_p _ f) .
   refine ( _ @[ (h @> (r_fg <@ i o h)) @ (h @> s_hi) ] _ ).
   *
    refine (wiskerR_pw_pw _ (h @> s_hi)) .
    admit.
   *
    exact wiskerL_pw_fn_pp^ .
 -
  refine (wiskerR_pw_fn_p _ f) .
  refine (wiskerL_pw_fn_p h _) .
  exact concat_pw_swap^ .
 -
  refine (
    _ @[ (h @> f o g @> s_hi) @ (h @> r_fg) <@ f ] _
    ) .
  +
   refine (wiskerR_pw_fn_p _ f) .
   exact wiskerL_pw_fn_pp .
  +
   exact wiskerR_pw_fn_pp .
 -
  admit.
 -
  exact wiskerL_pw_fn_pp^ .
Admitted.


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
