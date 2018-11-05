Add LoadPath "./theories".

Require Import Basis.


Declare ML Module "ltac_plugin".

Export Set Default Proof Mode "Classic".


Definition paths_contr
  {A : Type} (IC : is_contr A) (x y : A) : paths x y .
Proof.
 refine (concat (y := dsum_fst IC) (inverse _) _) .
 -
  exact (dsum_snd IC x) .
 -
  exact (dsum_snd IC y) .
Defined.

Lemma K_paths_contr
  {A : Type} (IC : is_contr A) {x y : A} (p : paths x y)
  : paths p (paths_contr IC x y) .
Proof.
 refine (paths_elim (P := fun y' p' => paths p' (paths_contr IC x y')) _ p) .
 change (paths_contr IC x x) with (concat (inverse (dsum_snd IC x)) (dsum_snd IC x)) .
 refine (paths_elim (P := fun y' p' => paths idpath (concat (inverse p') p')) _ (dsum_snd IC x)) .
 exact idpath .
Defined.

Definition paths_paths_contr
  {A : Type} (IC : is_contr A) {x y : A} (p q : paths x y) : paths p q .
Proof.
 refine (concat (y := paths_contr IC x y) (inverse _) _) .
 -
  refine (inverse _) .
  exact (K_paths_contr IC p) .
 -
  refine (inverse _) .
  exact (K_paths_contr IC q) .
Defined.
