Require Import Basis Contraction.


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

Definition inv_contradict {A B : Type}
  : contradict A B -> contradict B A
  := fun f a b => f b a .


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


Definition id_contradict {A : Type}
  : contradict A (A -> empty)
  := fun x f => f x .

(* classic: sum A (A -> empty) *)

Definition down_contradict {A B : Type}
  (f : contradict ((A -> empty) -> empty) ((B -> empty) -> empty))
  : contradict A B .
Proof.
 refine (fun a b => _) .
 refine (f _ _) .
 -
  exact (fun f => f a) .
 -
  exact (fun f => f b) .
Defined.

(* classic: up_contradict *)

Definition up_sum {A B : Type}
  (H : sum A B)
  : sum ((A -> empty) -> empty) ((B -> empty) -> empty).
Proof.
 refine (sum_elim_nodep _ _ H) .
 -
  exact (fun a => left (fun f => f a)) .
 -
  exact (fun b => right (fun f => f b)) .
Defined.

(* classic: down_sum *)


Definition opposite (A B : Type) : Type := prod (contradict A B) (sum A B) .

Definition opposite' (A B : Type) : Type := is_contr (sum A B) .

Definition opposite'_contradict
  {A B : Type} (H : opposite' A B) : contradict A B .
Proof.
 revert H .
 refine (dsum_elim _) .
 refine (sum_elim _ _) .
 -
  refine (fun x p a b => _) .
  refine (cast (A := unit) (B := empty) _ tt) .
  pose (
    D := sum_elim_nodep (A := A) (B := B) (P := Type) (const unit) (const empty)
    ) .
  change (paths (D (left x)) (D (right b))) .
  refine (ap D _).
  exact (p (right b)) .
 -
  refine (fun x p a b => _) .
  refine (cast (A := unit) (B := empty) _ tt) .
  pose (
    D := sum_elim_nodep (A := A) (B := B) (P := Type) (const empty) (const unit)
    ) .
  change (paths (D (right x)) (D (left a))) .
  refine (ap D _).
  exact (p (left a)) .
Defined.

Definition opposite'_opposite
  {A B : Type} (H : opposite' A B) : opposite A B .
Proof.
 refine (pair _ _) .
 -
  exact (opposite'_contradict H) .
 -
  exact (dfst H) .
Defined.

(* false: opposite A B -> opposite' A B *)
(* true: is_hprop A -> is_hprop B -> opposite A B -> opposite' A B *)

Definition is_hprop (A : Type) : Type
  := is_trunc (trunc_succ minus_two) A .

Definition opposite_opposite'
  {A B : Type} (IHPA : is_hprop A) (IHPB : is_hprop B)
  (H : opposite A B) : opposite' A B .
Proof.
 revert H .
 refine (prod_elim_nodep _) .
 refine (fun CAB => _).
 refine (sum_elim_nodep _ _) .
 -
  refine (fun x => _) .
  refine (dpair (left x) _) .
  refine (sum_elim _ _) .
  +
   admit.
  +
   refine (fun b => _) .
   refine (absurd _) .
   refine (CAB x b) .
 -
  refine (fun x => _) .
  refine (dpair (right x) _) .
  refine (sum_elim _ _) .
  +
   refine (fun a => _) .
   refine (absurd _) .
   refine (CAB a x) .
  +
   admit.
Admitted.

Definition is_hprop_opposite'_left
  {A B : Type} (H : opposite' A B) : is_hprop A .
Proof.
 revert H .
 refine (dsum_elim_nodep _) .
 refine (sum_elim _ _) .
 -
  refine (fun x p => _) .
  refine (contr_paths_contr _) .
  refine (dpair x _) .
  refine (fun y => _) .
  pose (
    D := sum_elim_nodep (A := A) (B := B) idmap (const x)
    ) .
  change (paths (D (left x)) (D (left y))) .
  refine (ap D _) .
  exact (p (left y)) .
 -
  refine (fun x p b => _) .
  refine (absurd _) .
  exact (opposite'_contradict (dpair (right x) p) b x) .
Defined.

Definition is_hprop_opposite'_right
  {A B : Type} (H : opposite' A B) : is_hprop B .
Proof.
 revert H .
 refine (dsum_elim_nodep _) .
 refine (sum_elim _ _) .
 -
  refine (fun x p a => _) .
  refine (absurd _) .
  exact (opposite'_contradict (dpair (left x) p) x a) .
 -
  refine (fun x p => _) .
  refine (contr_paths_contr _) .
  refine (dpair x _) .
  refine (fun y => _) .
  pose (
    D := sum_elim_nodep (A := A) (B := B) (const x) idmap
    ) .
  change (paths (D (right x)) (D (right y))) .
  refine (ap D _) .
  exact (p (right y)) .
Defined.
