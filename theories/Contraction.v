Require Export Homotopy.
Require Import Path.

Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


(** [A] が [contr] であれば [x y : A] の間に道がある。 *)
Definition path_contr
  {A : Type} (IC : contr A) (x y : A) : paths x y .
Proof.
 refine (coninv (y := dfst IC) _ _) .
 -
  exact (dsnd IC x) .
 -
  exact (dsnd IC y) .
Defined.

(** [A] が [IC : contr A] であれば、その二点の間の道 [p : paths x y] は
    [path_contr IC x y] からの道を持つ。 *)
Lemma K_path_contr
  {A : Type} (IC : contr A) {x y : A} (p : paths x y)
  : paths (path_contr IC x y) p .
Proof.
 refine (
   paths_elim _ p
     (P := fun y' p' => paths (path_contr IC x y') p')
   ) .
 exact (coninv_pp (dsnd IC x)) .
Defined.

(** [A] が [contr] であれば [p q : paths x y] の間に道がある。 *)
Definition path_path_contr
  {A : Type} (IC : contr A) {x y : A} (p q : paths x y) : paths p q .
Proof.
 refine (coninv (y := path_contr IC x y) _ _) .
 -
  exact (K_path_contr IC p) .
 -
  exact (K_path_contr IC q) .
Defined.

(** [A] が [contr] であれば、その二点の間の [paths] も [contr] である。 *)
Definition contr_paths_contr
  {A : Type} (IC : contr A) (x y : A) : contr (paths x y) .
Proof.
 refine (dpair (path_contr IC x y) _) .
 exact (K_path_contr IC) .
Defined.


(** [x] を始点とする道の集まり。 *)
Definition based_paths {X : Type} (x : X) : Type := dsum (paths x) .

(** [p : based_paths x] は [dpair x idpath] からの道を持つ。 *)
Definition path_based_paths
  {X : Type} {x : X} (p : based_paths x)
  : paths (dpair x idpath) p .
Proof.
 refine (dsum_elim _ p) .
 refine (@paths_elim X x _ _) .
 exact idpath .
Defined.

(** [based_paths] は [contr] である。 *)
Definition contr_based_paths
  {X : Type} (x : X) : contr (based_paths x) .
Proof.
 refine (dpair (dpair x idpath) _) .
 exact path_based_paths .
Defined.

(** [based_paths] の除去子。 *)
Definition based_paths_elim
  {A : Type} (a : A) (P : based_paths a -> Type)
  (c : forall a' p, P (dpair a' p))
  (x : based_paths a) : P x .
Proof.
 revert x .
 refine (dsum_elim _) .
 exact c .
Defined.

(** [paths_elim] を [based_paths] を使って書き直したもの。 *)
Definition paths_elim_by_based_paths
  {A : Type} (a : A) (P : based_paths a -> Type)
  (c : P (dpair a idpath))
  (x : based_paths a) : P x .
Proof.
 revert x .
 refine (dsum_elim _) .
 refine (@paths_elim A a _ _) .
 exact c .
Defined.


(** 定義域 (domain) が [contr] である関数は、
    命題的定値 (propositionally constant) である。 *)
Definition contr_dom_constant
  {A B : Type} (IC : contr A) (f : A -> B) {x y : A}
  : paths (f x) (f y) .
Proof.
 refine (ap f _) .
 exact (path_contr IC x y) .
Defined.

(** [X] が [contr] で [r : Y -> X] が引き込み (retraction) であれば、
    [Y] もまた [contr] である。

    [s : Y -> X] は [Y -> unit] と同じように [const] によって自明に
    与えられることに注意せよ。 *)
Definition contr_retract
  {X Y} (IC : contr X) (r : X -> Y) (s : Y -> X)
  (retr : retraction r s) : contr Y .
Proof.
 refine (dpair (r (dfst IC)) _) .
 refine (fun y => _) .
 refine (concat (y := r (s y)) _ _).
 -
  exact (contr_dom_constant IC r) .
 -
  exact (retr y) .
Defined.
