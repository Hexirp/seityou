Require Import Basis.


Declare ML Module "ltac_plugin".

Export Set Default Proof Mode "Classic".


Definition coninv
  {A : Type} {x y z : A}
  (p : paths y x) (q : paths y z) : paths x z
  := concat (inverse p) q .

Definition coninv_pp
  {A : Type} {x y : A}
  (p : paths x y) : paths (coninv p p) idpath
  := paths_elim (P := fun y' p' => paths (coninv p' p') idpath) idpath p .


Definition path_contr
  {A : Type} (IC : is_contr A) (x y : A) : paths x y .
Proof.
 unfold is_contr in IC .
 refine (coninv (y := dsum_fst IC) _ _) .
 -
  exact (dsum_snd IC x) .
 -
  exact (dsum_snd IC y) .
Defined.

Lemma K_path_contr
  {A : Type} (IC : is_contr A) {x y : A} (p : paths x y)
  : paths (path_contr IC x y) p .
Proof.
 refine (paths_elim _ p
   (P := fun y' p' => paths (path_contr IC x y') p')) .
 unfold path_contr .
 exact (coninv_pp (dsum_snd IC x)) .
Defined.

Definition path_path_contr
  {A : Type} (IC : is_contr A) {x y : A} (p q : paths x y) : paths p q .
Proof.
 refine (coninv (y := path_contr IC x y) _ _) .
 -
  exact (K_path_contr IC p) .
 -
  exact (K_path_contr IC q) .
Defined.

Definition contr_paths_contr
  {A : Type} (IC : is_contr A) (x y : A) : is_contr (paths x y) .
Proof.
 unfold is_contr .
 refine (dpair (path_contr IC x y) _) .
 unfold is_contr_center .
 exact (K_path_contr IC) .
Defined.


Definition based_paths {X : Type} (x : X) : Type := dsum (paths x) .

Definition path_based_paths
  {X : Type} {x : X} (p : based_paths x)
  : paths (dpair x idpath) p .
Proof.
 refine (dsum_elim _ p) .
 refine (@paths_elim X x _ _) .
 exact idpath .
Defined.

Definition contr_based_paths
  {X : Type} (x : X) : is_contr (based_paths x) .
Proof.
 unfold is_contr .
 refine (dpair (dpair x idpath) _) .
 unfold is_contr_center .
 exact path_based_paths .
Defined.

Definition based_paths_elim
  {A : Type} (a : A) (P : based_paths a -> Type)
  (c : forall a' p, P (dpair a' p))
  (x : based_paths a) : P x
  := match x with dpair a' p => c a' p end .

Definition paths_elim_by_based_paths
  {A : Type} (a : A) (P : based_paths a -> Type)
  (c : P (dpair a idpath))
  (x : based_paths a) : P x .
Proof.
 refine (transport (x := dpair (dsum_fst x) (dsum_snd x)) _ _) .
 -
  refine (dsum_elim _ x
    (P := fun x' => paths (dpair (dsum_fst x') (dsum_snd x')) x')) .
  refine (fun xv xH => _) .
  unfold dsum_fst .
  unfold dsum_elim_nodep .
  unfold dsum_snd .
  unfold dsum_elim .
  exact idpath .
 -
  refine (paths_elim (P := fun a' p => P (dpair a' p)) c (dsum_snd x)).
Defined.


Definition contr_dom_equiv
  {A B : Type} (IC : is_contr A) (f : A -> B) {x y : A}
  : paths (f x) (f y) .
Proof.
 refine (ap f _) .
 exact (path_contr IC x y) .
Defined.

Definition contr_retract
  {X Y} (IC : is_contr X) (r : X -> Y) (s : Y -> X)
  (retr : retraction r s) : is_contr Y .
Proof.
 unfold is_contr .
 refine (dpair (r (dsum_fst IC)) _) .
 unfold is_contr_center .
 refine (fun y => _) .
 unfold retraction in retr .
 unfold pwpaths in retr .
 unfold compose in retr .
 unfold idmap in retr .
 refine (concat (y := r (s y)) _ _).
 -
  exact (contr_dom_equiv IC r) .
 -
  exact (retr y) .
Defined.
