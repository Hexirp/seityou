Require Export Basis .


Declare ML Module "ltac_plugin" .

Set Default Proof Mode "Classic" .


(** ** 記法 *)

Module Notation .

  Delimit Scope path_scope with path .

  Open Scope path_scope .

  Notation "x = y :> T" := (@paths T x y)
    (at level 70, y at next level, no associativity)
    : path_scope
    .

  Notation "x = y" := (x = y :> _)
    (at level 70, no associativity)
    : path_scope
    .

  Notation "1" := idpath
    : path_scope
    .

  Notation "p @ q" := (concat p q)
    (at level 20)
    : path_scope
    .

  Notation "p ^" := (inverse p)
    (at level 3, format "p '^'")
    : path_scope
    .

  Notation "p # x" := (transport p x)
    (right associativity, at level 65)
    : path_scope
    .

End Notation.

Import Notation.


(** [p] を反転して [q] を合成する。

    [forall y, x = y] のようなパターンの時に便利。 *)
Definition coninv
  {A : Type} {x y z : A}
  (p : y = x) (q : y = z) : x = z
  := p^ @ q .

(** [concat p p] は [idpath] に等しい。 *)
Definition coninv_pp
  {A : Type} {x y : A}
  (p : x = y) : coninv p p = 1 .
Proof.
 revert y p .
 refine (@paths_elim A x _ _) .
 exact 1 .
Defined.

(** [concat] の [transport] を使った定義。 *)
Definition contrans
  {A : Type} {x y z : A}
  (p : x = y) (q : y = z) : x = z
  := q # p .

(** [contrans] は [concat] と等しい。 *)
Definition contrans_concat
  {A : Type} {x y z : A}
  (p : x = y) (q : y = z)
  : p @ q = contrans p q .
Proof.
 revert z q .
 refine (@paths_elim A y _ _) .
 revert y p .
 refine (@paths_elim A x _ _) .
 exact 1 .
Defined.
