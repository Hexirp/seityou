Add LoadPath "./theories".

Require Import Basis.

(** [A] に関して [B] で添え字付けられた整礎的な型。

    [nat = 1 + nat] はよく知られているとおりである。
    [F X = 1 + X] として [F X = X] となるような [X] が [nat] である。
    さらに [tree = 1 + tree ^ 2] である。
    すなわち [F X = 1 + X ^ 2] から生成される。
    ここで、 [F X] を [X] の多項式として見なす。
    すなわち [F X = X ^ a_0 + X ^ a_1 + ... + X ^ a_n] として一般化する。
    すると、 [F X = Σ (k = 0 ... n) (X ^ a_k) である。
    さらに一般化すると [F X = Σ (k : A) (X ^ B k)] となる。
    最終的に [F X = dsum A (fun k : A => exp (B k) X)] となる。 *)
Private Inductive w (A : Type) (B : A -> Type) : Type
  :=
  | sup : forall x : A, (B x -> w A B) -> w A B
  .

Definition w_rect
  (A : Type) (B : A -> Type) (P : w A B -> Type)
  (case_sup : forall (x : A) (u : B x -> w A B), (forall y, P (u y)) -> P (sup A B x u))
  (x : w A B) : P x
  .
Proof.
Admitted.

Definition w_rect_c
  (A : Type) (B : A -> Type) (P : w A B -> Type)
  (c : forall (x : A) (u : B x -> w A B), (forall y, P (u y)) -> P (sup A B x u))
  (x : A) (u : B x -> w A B)
  : paths
    (w_rect A B P c (sup A B x u))
    (c x u (fun y => w_rect A B P c (u y)))
  .
Proof.
Admitted.

Definition nat : Type := w (sum unit unit) (sum_elim_nodep (const empty) (const unit)).

Definition zero : nat.
Proof.
 refine (sup _ _ (left tt) _).
 refine (fun H => _).
 refine (absurd _).
 exact H.
Defined.

Definition succ : nat -> nat.
Proof.
 refine (fun x => _).
 refine (sup _ _ (right tt) _).
 refine (fun H => _).
 exact x.
Defined.
