Require Import Basis.


Declare ML Module "ltac_plugin".

Export Set Default Proof Mode "Classic".


Definition contradict (A B : Type) : Type
  := A -> B -> empty .

Definition contradict' (A B : Type) : Type
  := prod A B -> empty .

Definition negate (A B : Type) : Type
  := A -> (B -> empty) .

Definition negate' (A B : Type) : Type
  := (A -> empty) -> B .


Definition contradict_contradict' {A B : Type}
  : contradict A B -> contradict' A B
  := uncurry .

Definition contradict_negate {A B : Type}
  : contradict A B -> negate A B
  := idmap .

Definition contradict'_contradict {A B : Type}
  : contradict' A B -> contradict A B
  := fun f a b => f (pair a b) .

Definition contradict'_negate {A B : Type}
  : contradict' A B -> negate A B
  := fun f a b => f (pair a b) .

Definition negate_contradict {A B : Type}
  : negate A B -> contradict A B
  := idmap .

Definition negate_contradict' {A B : Type}
  : negate A B -> contradict' A B
  := uncurry .

(* false: contradict A B -> negate' A B *)

(* false: negate' A B -> contradict A B *)


Definition sum_negate' {A B : Type}
  : sum A B -> negate' A B .
Proof.
 refine (sum_elim_nodep _ _) .
 -
  refine (fun a f => _) .
  refine (absurd _) .
  refine (f _) .
  exact a .
 -
  refine (fun b f => _) .
  exact b .
Defined.

(* classic: negate' A B -> sum A B *)

(* classic: negate' A B -> negate' B A *)

Definition inv_contradict {A B : Type}
  : contradict A B -> contradict B A
  := fun f a b => f b a .
