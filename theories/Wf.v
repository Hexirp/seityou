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

Definition ss (m n : nat) : Type := paths m (S (S n)) .

Definition well_founded_ss : well_founded ss .
Proof.
 refine (fun x => _) .
 refine (acc _) .
Admitted. (* [nat_rec] だけで証明せよ *)
