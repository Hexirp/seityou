Require Export Homotopy.


Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


Inductive Acc (A : Type) (R : A -> A -> Type) (x : A) : Type
  :=
  | acc : (forall y, R y x -> Acc A R y) -> Acc A R x
  .

Arguments Acc {_} _ _ .
Arguments acc {_ _ _} _ .

Definition well_founded {A : Type} (R : A -> A -> Type) : Type
  := forall x, Acc R x .

Inductive nat : Type := O : nat | S : nat -> nat .

Definition nat_rec
  {P : Type}
  (case_O : P)
  (case_S : P -> P)
  (x : nat) : P
  :=
    let go :=
      fix go x :=
        match x with
        | O => case_O
        | S xp => case_S (go xp)
        end
    in go x
  .

Definition nat_rect
  {P : nat -> Type}
  (case_O : P O)
  (case_S : forall xp, P xp -> P (S xp))
  (x : nat) : P x
  :=
    let go :=
      fix go x :=
        match x with
        | O => case_O
        | S xp => case_S xp (go xp)
        end
    in go x
  .

Definition succ (m n : nat) : Type := paths (S m) n .

Definition succ_no (m : nat) (x : succ m O) : empty .
Proof.
 pose (D := nat_rec (P := Type) empty (const unit)) .
 refine (cast (A := unit) _ tt) .
 change (paths (D (S m)) (D O)) .
 refine (ap D _) .
 exact x .
Defined.

Definition well_founded_succ : well_founded succ .
Proof.
 refine (nat_rect _ _) .
 -
  refine (acc _) .
  refine (fun y yH => _) .
  refine (absurd _) .
  exact (succ_no y yH) .
 -
  refine (fun xp xpH => _) .
  refine (acc _) .
  refine (fun y yH => _) .
  refine (transport (x := xp) _ _) .
  +
   refine (inverse _) .
   pose (D := nat_rect (P := fun _ => nat) O (fun xp _ => xp)) .
   change (paths (D (S y)) (D (S xp))) .
   refine (ap D _) .
   exact yH .
  +
   exact xpH .
Defined.

Inductive le (m : nat) : nat -> Type
  :=
  | le_refl : le m m
  | le_succ : forall n, le m n -> le m (S n)
  .

Definition lt (m n : nat) : Type := le (S m) n .

Definition well_founded_lt : well_founded lt .
Proof.
 refine (nat_rect _ _) .
 -
  refine (acc _) .
  refine (fun y yH => _) .
  refine (absurd _) .
  refine (_ (idpath O)) .
  refine (match yH in le _ z' return paths z' O -> empty with le_refl _ => _ | le_succ _ zp zpH => _ end) .
  +
   exact (succ_no y) .
  +
   exact (succ_no zp) .
 -
  refine (fun xp xpH => _) .
  refine (acc _) .
  refine (fun y yH => _) .
Admitted.

Definition ss (m n : nat) : Type := paths m (S (S n)) .

Definition well_founded_ss : well_founded ss .
Proof.
 refine (fun x => _) .
 refine (acc _) .
Admitted. (* [nat_rec] だけで証明せよ *)
