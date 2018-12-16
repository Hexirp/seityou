(** * Equivalence

    等価性に関する定理や定義。 *)


Require Export Homotopy.
Require Import Path.


Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


Definition is_equiv_idmap {A : Type} : is_equiv (@idmap A) .
Proof.
 refine (dpair idmap _) .
 cut (@retraction A A idmap idmap) .
 -
  refine (fun retr => _) .
  refine (dpair retr _) .
  cut (@section A A idmap idmap) .
  +
   refine (fun sect => _) .
   refine (dpair sect _) .
   exact idpath .
