(** * Equivalence

    等価性に関する定理や定義。 *)


Require Export Homotopy.
Require Import Path.


Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


Definition is_equiv_idmap {A : Type} : is_equiv (@idmap A) .
Proof.
 refine (dpair idmap _) .
 assert (retr : @retraction A A idmap idmap) .
 -
  exact (fun x => idpath) .
 -
  refine (dpair retr _) .
  assert (sect : @section A A idmap idmap) .
  +
   exact (fun x => idpath) .
  +
   refine (dpair sect _) .
   exact idpath .
