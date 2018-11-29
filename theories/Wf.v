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

Definition lt_n_0 : forall n, lt n O -> empty .
Proof.
 unfold lt .
 refine (fun n x => _) .
 refine (_ (idpath O)) .
 refine (
   match x in le _ i return paths i O -> empty with
   | le_refl _ => _
   | le_succ _ ip xp => _
   end ) .
 -
  exact (succ_no n) .
 -
  exact (succ_no ip) .
Defined.

Definition lt_m_Sn_case : forall m n, lt m (S n) -> sum (paths m n) (lt m n) .
Proof.
 unfold lt .
 refine (fun m n x => _) .
 pose (D := nat_rect (P := fun _ => nat) O (fun xp _ => xp)) .
 change (sum (paths m (D (S n))) (le (S m) (D (S n)))) .
 refine (
   match x in le _ sn return sum (paths m (D sn)) (le (S m) (D sn)) with
   | le_refl _ => _
   | le_succ _ snp xp => _ end ) .
 -
  change (sum (paths m m) (le (S m) m)) .
  refine (left _) .
  exact idpath .
 -
  change (sum (paths m snp) (le (S m) snp)) .
  refine (right _) .
  exact xp .
Defined.

Definition wf_lt : well_founded lt .
Proof.
 refine (nat_rect _ _) .
 -
  refine (acc _) .
  refine (fun y yH => _) .
  refine (absurd _) .
  exact (lt_n_0 y yH) .
 -
  refine (fun xp xpH_ => match xpH_ with acc xpH => acc _ end) .
  admit.
Admitted.

Lemma concat_lt_lt_S : forall m n o, lt m n -> le n o -> lt m o .
Proof.
 refine (fun m n o x y => _) .
 revert o y .
Admitted.

Lemma well_founded_lt_steps : forall m n, lt n m -> Acc lt n .
Proof.
 refine (nat_rect _ _) .
 -
  refine (fun n nH => _) .
  refine (absurd _) .
  refine (_ (idpath O)) .
  refine (match nH in le _ o' return paths o' O -> empty with le_refl _ => _ | le_succ _ op opH => _ end) .
  +
   exact (succ_no n) .
  +
   exact (succ_no op) .
 -
  refine (fun xp xpIH n nH => _) .
  refine (acc _) .
  refine (fun o oH => _) .
  refine (xpIH _ _) .
  refine (concat_lt_lt_S o n xp _ _) .
  +
   exact oH .
  +
   refine (_ (idpath (S xp))) .
   refine (match nH in le _ o' return paths o' (S xp) -> le n xp with le_refl _ => _ | le_succ _ op opH => _ end) .
   *
    refine (fun p => _) .
    refine (transport _ (le_refl n)) .
    pose (D := nat_rect (P := fun _ => nat) O (fun xp _ => xp)) .
    change (paths (D (S n)) (D (S xp))) .
    refine (ap D _) .
    exact p .
   *
   
Admitted.

Definition well_founded_lt : well_founded lt .
Proof.
 refine (fun x => _) .
 refine (acc _) .
 exact (well_founded_lt_steps x) .
Defined.

Definition ss (m n : nat) : Type := paths m (S (S n)) .

Definition well_founded_ss : well_founded ss .
Proof.
 refine (fun x => _) .
 refine (acc _) .
Admitted. (* [nat_rec] だけで証明せよ *)
