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


Definition paths_contr
  {A : Type} (IC : is_contr A) (x y : A) : paths x y .
Proof.
 unfold is_contr in IC .
 refine (coninv (y := dsum_fst IC) _ _) .
 -
  exact (dsum_snd IC x) .
 -
  exact (dsum_snd IC y) .
Defined.

Lemma K_paths_contr
  {A : Type} (IC : is_contr A) {x y : A} (p : paths x y)
  : paths (paths_contr IC x y) p .
Proof.
 refine (paths_elim _ p
   (P := fun y' p' => paths (paths_contr IC x y') p')) .
 unfold paths_contr .
 exact (coninv_pp (dsum_snd IC x)) .
Defined.

Definition paths_paths_contr
  {A : Type} (IC : is_contr A) {x y : A} (p q : paths x y) : paths p q .
Proof.
 refine (coninv (y := paths_contr IC x y) _ _) .
 -
  exact (K_paths_contr IC p) .
 -
  exact (K_paths_contr IC q) .
Defined.


Definition based_paths {X : Type} (x : X) : Type := dsum (paths x) .

Definition contr_based_paths
  {X : Type} (x : X) : is_contr (based_paths x) .
Proof.
 unfold is_contr .
 refine (dpair (dpair x idpath) _) .
 unfold is_contr_center .
 refine (dsum_elim _) .
 refine (@paths_elim X x _ _) .
 exact idpath .
Defined.
