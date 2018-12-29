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
  := retr wR f == f wL sect .

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
   begin
           h o (f o g) o i
   =( _ )
           h o i
   =( _ )
           (@idmap C)
   end
   ) .
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
 refine (fun x => _) .
 change (
   concat_pw (wiskerR_pw_fn (wiskerL_pw_fn h r_fg) i) r_hi ((h o f) x)
   =
   ap (h o f) (concat_pw (wiskerR_pw_fn (wiskerL_pw_fn g s_hi) f) s_fg x)
   ) .
 
 refine (
   concat_pw _ (inverse_pw _)
     (g := concat_pw
       (wiskerL_pw_fn (h o f) (wiskerR_pw_fn (wiskerL_pw_fn g s_hi) f))
       (wiskerL_pw_fn (h o f) s_fg)
     )
   ) .
 refine (
   concat_pw _ _
     (g := concat_pw
       (wiskerR_pw_fn (wiskerR_pw_fn (wiskerL_pw_fn h r_fg) i) (h o f))
       (wiskerR_pw_fn r_hi (h o f))
     )
   ) .
 -
  exact wiskerR_pw_fn_pp .
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
