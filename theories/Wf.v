Require Export Homotopy.


Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


Inductive Acc (A : Type) (R : A -> A -> Type) (x : A) : Type
  :=
  | acc : (forall y, R y x -> Acc A R y) -> Acc A R x
  .

Arguments Acc {_} _ _ .
Arguments acc {_ _ _} _ .

Definition Acc_rec
  {A : Type} {R : A -> A -> Type} {P : A -> Type}
  (case_acc : forall a, (forall b, R b a -> P b) -> P a)
  (a : A) (x : Acc R a) : P a .
Proof.
 revert a x .
 refine (fix go a x {struct x} := _) .
 refine (case_acc a _) .
 refine (fun b bH => _) .
 refine (go b _) .
Admitted.

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

Definition pred (m : nat) : nat := match m with O => O | S mp => mp end .

Definition succ (m n : nat) : Type := paths (S m) n .

Definition succ_no {m : nat} (x : succ m O) : empty .
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
  exact (succ_no yH) .
 -
  refine (fun xp xpH => _) .
  refine (acc _) .
  refine (fun y yH => _) .
  refine (transport (x := xp) _ _) .
  +
   refine (inverse _) .
   pose (D := pred) .
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

Definition le_rec
  {m : nat} {P : nat -> Type}
  (case_le_refl : P m)
  (case_le_succ : forall np, le m np -> P np -> P (S np))
  (n : nat) (x : le m n) : P n .
Proof.
 revert n x .
 refine (fix go n x {struct x} := _) .
 refine (match x with le_refl _ => _ | le_succ _ np xp => _ end) .
 -
  exact case_le_refl .
 -
  refine (case_le_succ np xp _) .
  exact (go np xp) .
Defined.

Definition le_rect
  {m : nat} {P : forall n, le m n -> Type}
  (case_le_refl : P m (le_refl m))
  (case_le_succ : forall np xp, P np xp -> P (S np) (le_succ m np xp))
  (n : nat) (x : le m n) : P n x .
Proof.
 revert n x .
 refine (fix go n x {struct x} := _) .
 refine (match x with le_refl _ => _ | le_succ _ np xp => _ end) .
 -
  exact case_le_refl .
 -
  refine (case_le_succ np xp _) .
  exact (go np xp) .
Defined.

Definition lt (m n : nat) : Type := le (S m) n .

Definition lt_n_0 {n : nat} (x : lt n O) : empty .
Proof.
 unfold lt in x .
 refine (_ (idpath O)) .
 refine (
   match x in le _ i return paths i O -> empty with
   | le_refl _ => _
   | le_succ _ ip xp => _
   end ) .
 -
  exact succ_no .
 -
  exact succ_no .
Defined.

Definition lt_m_Sn_case {m n : nat} (x : lt m (S n)) : sum (paths m n) (lt m n) .
Proof.
 unfold lt ; unfold lt in x .
 pose (D := pred) .
 change (sum (paths m (D (S n))) (le (S m) (D (S n)))) .
 refine (
   match x in le _ sn return sum (paths m (D sn)) (le (S m) (D sn)) with
   | le_refl _ => _
   | le_succ _ snp xp => _
   end ) .
 -
  change (sum (paths m m) (le (S m) m)) .
  refine (left _) .
  exact idpath .
 -
  change (sum (paths m snp) (le (S m) snp)) .
  refine (right _) .
  exact xp .
Defined.

Definition well_founded_lt : well_founded lt .
Proof.
 refine (nat_rect _ _) .
 -
  refine (acc _) .
  refine (fun y yH => _) .
  refine (absurd _) .
  exact (lt_n_0 yH) .
 -
  refine (fun xp xpH_ => _) .
  refine (match xpH_ with acc xpH => _ end) .
  refine (acc _).
  refine (fun y yH => _) .
  refine (match lt_m_Sn_case yH with left yHL => _ | right yHR => _ end) .
  +
   exact (transport (inverse yHL) (acc xpH)) .
  +
   refine (xpH y _) .
   exact yHR .
Defined.

Definition ss (m n : nat) : Type := paths (S (S m)) n .

Definition well_founded_ss : well_founded ss .
Proof.
 refine (fun x => _) .
 refine (fst (B := Acc ss (S x)) _) .
 revert x .
 refine (nat_rect _ _) .
 -
  refine (pair _ _) .
  +
   refine (acc _) .
   refine (fun y yH => _) .
   refine (absurd _) .
   exact (succ_no yH) .
  +
   refine (acc _) .
   refine (fun y yH => _) .
   refine (absurd _) .
   refine (succ_no (m := y) _) .
   pose (D := pred) .
   change (paths (D (S (S y))) (D (S O))) .
   refine (ap D _) .
   exact yH .
 -
  refine (fun xp xpIH => _) .
  refine (pair _ _) .
  +
   exact (snd xpIH) .
  +
   refine (acc _) .
   refine (fun y yH => _) .
   refine (transport _ (fst xpIH)) .
   refine (inverse _) .
   pose (D := pred) .
   change (paths (D (D (S (S y)))) (D (D (S (S xp))))) .
   refine (ap D _) .
   refine (ap D _) .
   exact yH .
Defined.

Definition wf_ss : well_founded ss .
Proof.
 refine (fun x => _) .
 generalize (well_founded_lt x) .
 revert x .
Admitted.
