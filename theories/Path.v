Require Export Homotopy.


Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


(** ** 名前について

    結合に関する定理は [concat_XX] と書かれ、その部分 [XX] は、その等式の
    左辺の式がどのような形をしているかを表す。右辺は推測する必要がある。
    この末尾につけられる注釈は、これらの記号を使って書かれる。

    * [1] は、ある恒等道 (identity path) を表す。
    * [p] は、ある道を表す。
    * [V] は、ある反転された道を表す。
    * [A] は、適用 [ap] を表す。
    * [M] は、ある移項されるものを表す。
    * [x] は、ある点を表し、それは [transport p x] といった道ではない全般
      である。
    * [2] は、2 次元の道に関するということを表す。
    * [3] は、3 次元の道に関するということを表す。以下同様……。

    結合性はアンダースコアにより指定される。これらは左辺がどういうものに
    なるかの例である。

    * [concat_1p] は [concat idpath p] 。
    * [concat_Vp] は [concat (inverse p) p] 。
    * [concat_p_pp] は [concat p (concat q r)] 。 *)


(** ** 記法 *)

Module Notation.

  Notation "x = y :> T"
    := (@paths T x y) (at level 70, y at next level, no associativity).

  Notation "x = y"
    := (x = y :> _) (at level 70, no associativity) .

  Notation "1"
    := idpath .

  Notation "p @ q"
    := (concat p q) (at level 20) .

  Notation "p ^"
    := (inverse p) (at level 3, format "p '^'") .

  Notation "p # x"
    := (transport p x) (right associativity, at level 65) .

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
  (p : x = y) : coninv p p = 1
  := paths_elim (P := fun y' p' => coninv p' p' = 1) 1 p .

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
 refine (
   paths_elim _ q
     (P := fun _ q' => p @ q' = contrans p q')
   ) .
 refine (
   paths_elim _ p
     (P := fun _ p' => p' @ 1 = contrans p' 1)
   ) .
 exact 1 .
Defined.
