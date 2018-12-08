Require Export Homotopy.
Require Import Path.

Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


Definition path_contr
  {A : Type} (IC : contr A) (x y : A) : paths x y .
Proof.
 refine (coninv (y := dfst IC) _ _) .
 -
  exact (dsnd IC x) .
 -
  exact (dsnd IC y) .
Defined.

Lemma K_path_contr
  {A : Type} (IC : contr A) {x y : A} (p : paths x y)
  : paths (path_contr IC x y) p .
Proof.
 refine (paths_elim _ p
   (P := fun y' p' => paths (path_contr IC x y') p')) .
 unfold path_contr .
 exact (coninv_pp (dsnd IC x)) .
Defined.

Definition path_path_contr
  {A : Type} (IC : contr A) {x y : A} (p q : paths x y) : paths p q .
Proof.
 refine (coninv (y := path_contr IC x y) _ _) .
 -
  exact (K_path_contr IC p) .
 -
  exact (K_path_contr IC q) .
Defined.

Definition contr_paths_contr
  {A : Type} (IC : contr A) (x y : A) : contr (paths x y) .
Proof.
 refine (dpair (path_contr IC x y) _) .
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
  {X : Type} (x : X) : contr (based_paths x) .
Proof.
 refine (dpair (dpair x idpath) _) .
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
 refine (transport (x := dpair (dfst x) (dsnd x)) _ _) .
 -
  refine (dsum_elim _ x
    (P := fun x' => paths (dpair (dfst x') (dsnd x')) x')) .
  refine (fun xv xH => _) .
  exact idpath .
 -
  exact (paths_elim (P := fun a' p => P (dpair a' p)) c (dsnd x)).
Defined.


Definition paths_contr_dom
  {A B : Type} (IC : contr A) (f : A -> B) {x y : A}
  : paths (f x) (f y) .
Proof.
 refine (ap f _) .
 exact (path_contr IC x y) .
Defined.

Definition contr_retract
  {X Y} (IC : contr X) (r : X -> Y) (s : Y -> X)
  (retr : retraction r s) : contr Y .
Proof.
 refine (dpair (r (dfst IC)) _) .
 refine (fun y => _) .
 refine (concat (y := r (s y)) _ _).
 -
  exact (paths_contr_dom IC r) .
 -
  exact (retr y) .
Defined.
