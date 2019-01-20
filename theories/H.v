Require Import Basis .

Import Basis.Notation .


Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .


Axiom lsum : Type -> Type -> Type .

Axiom lsum_left : forall A B, A -> lsum A B .
Axiom lsum_right : forall A B, B -> lsum A B .

Axiom lsum_elim_nodep
  : forall A B P (cl : A -> P) (cr : B -> P),
    (forall a b, cl a = cr b) ->
    lsum A B -> P .

Definition wk_dec (P : Type) := lsum (unit -> P) (P -> empty) .

Definition collapse (P : Type) (wdec : wk_dec P) : P -> P .
Proof.
 revert wdec .
 refine (lsum_elim_nodep (unit -> P) (P -> empty) (P -> P) ?[cl] ?[cr] _) .
Admitted.
