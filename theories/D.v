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
    D := sum_elim_nodep (A := A) (B := B) (const unit) (const empty)
    ) .
  change (paths (D (left x)) (D (right b))) .
 -
  refine (fun x p a b => _) .

Definition opposite'_opposite
  {A B : Type} (H : opposite' A B) : opposite A B .
Proof.
 unfold opposite .
 unfold opposite' in H .
 unfold is_contr in H .
 refine (dsum_elim_nodep _ H) .
 refine (fun Hv HH => _) .
 refine (pair _ _) .
 -
  unfold contradict .
  refine (fun a b => _) .
  revert Hv HH .
  refine (sum_elim _ _) .
  +
   refine (fun Hva I => _) .
   unfold is_contr_center in I .
   refine (cast (A := unit) (B := empty) _ tt) .
   pose (
     D
       := sum_elim_nodep (const unit) (const empty)
       : sum A B -> Type ) .
   change (paths (D (left Hva)) (D (right b))) .
   refine (ap D _) .
   exact (I (right b)) .
  +
   refine (fun Hvb I => _) .
   unfold is_contr_center in I .
   refine (cast (A := unit) (B := empty) _ tt) .
   pose (
     D
       := sum_elim_nodep (const empty) (const unit)
       : sum A B -> Type ) .
   change (paths (D (right Hvb)) (D (left a))) .
   refine (ap D _) .
   exact (I (left a)) .
 -
  exact Hv .
Defined.

Definition is_hprop (A : Type) : Type
  := is_trunc (trunc_succ minus_two) A .

Definition is_hprop_opposite'_left
  {A B : Type} (H : opposite' A B) : is_hprop A .
Proof.
 unfold is_hprop .
 unfold is_trunc .
 unfold trunc_index_rec .
 unfold paths_is .
 unfold opposite' in H .
 unfold is_contr in H .
 refine (dsum_elim_nodep (fun Hv HH => _) H) .
 unfold is_contr_center in HH .
 revert Hv HH .
 refine (sum_elim (fun Hva HH => _) (fun Hvb HH => _) ) .
 -
  refine (contr_paths_contr _) .
  unfold is_contr .
  refine (dpair Hva _) .
  unfold is_contr_center .
  refine (fun x => _) .
  pose (p := HH (left x)) .
  pose (
    D := sum_elim_nodep idmap (const Hva)
    : sum A B -> A ) .
  change (paths (D (left Hva)) (D (left x))) .
  refine (ap D _) .
  exact p .
 -
  refine (fun x => _) .
  refine (absurd _) .
  refine (_ x Hvb) .
  pose (H' := opposite'_opposite H) .
  exact (fst H') .
Defined.
