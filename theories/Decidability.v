(** * Decidability

    決定可能な命題についての定義や定理を証明する。 *)

Require Import Basis Path Homotopy Contraction .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .
Import Basis.Notation.Path .


(** [A] は決定可能である。 *)
Definition decidable (A : Type) : Type := sum A (A -> empty) .

(** [A] の道は決定可能である。 *)
Definition path_decidable (A : Type) : Type := paths_is decidable A .

(** [A] の二重否定は除去できる。 *)
Definition stable (A : Type) : Type := ((A -> empty) -> empty) -> A .

(** [A] が decidable であれば stable である。 *)
Definition stable_decidable (A : Type) (dec : decidable A) : stable A .
Proof.
 revert dec .
 refine (sum_elim_nodep _ _) .
 -
  refine (fun a nna => _) .
  exact a .
 -
  refine (fun na nna => _) .
  refine (absurd _) .
  exact (nna na) .
Defined.


Definition decidable_contr (A : Type) (ic : contr A) : decidable A .
Proof.
 refine (left _) .
 exact (center ic) .
Defined.

Definition path_decidable_ishprop
  (A : Type) (ihp : is_hprop A) : path_decidable A .
Proof.
 refine (fun x y => _) .
 pose (ic := ihp x y : contr (x = y)) .
 refine (left _) .
 exact (center ic) .
Defined.


(** 参考文献:

    * https://github.com/HoTT/HoTT/blob/1940297dd121d54d033274d84c5d023fdc56bfb4/theories/Basics/Decidable.v

    *)
