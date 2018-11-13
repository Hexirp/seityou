Require Import Basis.


Declare ML Module "ltac_plugin".

Export Set Default Proof Mode "Classic".


Definition contradict (A : Type) (B : Type) : Type
  := A -> B -> empty .

Definition contradict' (A : Type) (B : Type) : Type
  := prod A B -> empty .

Definition negate (A : Type) (B : Type) : Type
  := A -> (B -> empty) .

Definition negate' (A : Type) (B : Type) : Type
  := (A -> empty) -> B .
