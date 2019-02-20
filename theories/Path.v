(** * Path

    道に関する定義を行う。 *)

Require Import Basis .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .
Import Basis.Notation.Path .


(** ** Applications *)

(** [ap] のバリエーションは以下の命令規則に従う。

    [apNK] は関数のK次道を値のN次道に適用する。関数が依存版である場合は、
    [apNK_dep] となる。関数がLつの値を取るとき、値のN次道はLつあり、名前は
    [apNK_L] となる。

    K次道は値、値の道、値の道の道といったものを表す。これは切捨 (Truncation)
    にも関わる表記法である。型 [A] に対して、そのK次道は、

    * 0-path: A
    * 1-path: paths A x y
    * 2-path: paths (paths A x y) p q
    * 3-path: paths (paths (paths A x y) p q) r s

    このようなことである。 *)

(** [f] を [x] に適用する。 [apply] の別名。 *)
Notation ap00 := apply (only parsing) .

(** [ap00] の依存版。 [apply_dep] の別名。 *)
Notation ap00_dep := apply_dep (only parsing) .

(** [f] を [p] に適用する。 [ap] の別名。 *)
Notation ap01 := ap (only parsing) .

(** [p] を [x] に適用する。 *)
Definition ap10
  {A B : Type}
  {f g : A -> B} (p : f = g)
  (x : A)
  : f x = g x
  := paths_elim_nodep (P := fun g' => f x = g' x) 1 p .

(** [ap10] の依存版。 *)
Definition ap10_dep
  {A : Type} {B : A -> Type}
  {f g : forall a, B a} (p : f = g)
  (x : A)
  : f x = g x
  := paths_elim_nodep (P := fun g' => f x = g' x) 1 p .

(** [p] を [q] に適用する。 *)
Definition ap11
  {A B : Type}
  {f g : A -> B} (p : f = g)
  {x y : A} (q : x = y)
  : f x = g y
  := paths_elim_nodep (P := fun g' => f x = g' y) (ap f q) p .

(** [f] を [p] と [q] に適用する。 *)
Definition ap01_2
  {A B C : Type}
  (f : A -> B -> C)
  (x y : A) (p : x = y)
  (z w : B) (q : z = w)
  : f x z = f y w
  := ap11 (ap f p) q .

(** [ap] の依存版。

    返される型の [paths (transport p (f x)) (f y)] という形は「依存道」と
    呼ばれる。 [f x] と [f y] はそれぞれ [P x] と [P y] という型を持っている
    ため、そのまま [paths (f x) (f y)] と書くことはできない。そこで [f x] を
    [p] によって輸送することで両辺の型を合わせている。依存型に対する道。
    [p] に依存する道。詳細は等式型のバリエーションを集めた Equality に
    譲る。 *)
Definition ap_dep
  {A : Type} {B : A -> Type}
  (f : forall a, B a)
  {x y : A} (p : x = y)
  : p # f x = f y
  := paths_elim (P := fun y' p' => p' # f x = f y') idpath p .

(** [ap01] の依存版。 [ap_dep] の別名。 *)
Notation ap01_dep := ap_dep (only parsing) .


(** ** Others

    そのほかの関数など。 *)

(** 点ごとの道。関数の外延性等値性。

    名前は "pointwize paths" を縮めたもの。 *)
Definition pwpaths
  {A : Type} {B : A -> Type} (f g : forall a, B a) : Type
  := forall a, f a = g a .

(** [p] を反転して [q] を合成する。

    [forall y, x = y] のような、同じ方向の道のパターンの時に便利。 *)
Definition coninv
  {A : Type} {x y z : A}
  (p : y = x) (q : y = z) : x = z
  := p^ @ q .

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
 refine (@paths_elim A y ?[ex_P] _) .
 revert y p .
 refine (@paths_elim A x ?[ex_P] _) .
 exact 1 .
Defined.

(** [coninv] と [concat] を合わせた関数。

    同じ方向の道で、両辺を書き換えたいときに便利。 *)
Definition conconinv
  {A : Type} {x y z w : A}
  (p : paths y x) (q : paths y z) (r : paths z w)
  : paths x w .
Proof.
 refine (coninv p _) .
 refine (concat q _) .
 exact r .
Defined.

(** [transport] の依存版。 *)
Definition transport_dep
  {A : Type} {a : A} {P : forall a', a = a' -> Type}
  {a' : A} (p : a = a') (x : P a idpath) : P a' p .
Proof.
 revert a' p .
 refine (@paths_elim A a P _) .
 exact x .
Defined.


(** ** Groupoid Structures *)

(** [ap] の分配則。 *)
Definition ap_pp
  {A B : Type}
  (f : A -> B) {x y z : A}
  (p : x = y) (q : y = z)
  : ap f (p @ q) = ap f p @ ap f q .
Proof.
 revert z q .
 refine (@paths_elim A y ?[ex_P] _) .
 revert y p .
 refine (@paths_elim A x ?[ex_P] _) .
 exact 1 .
Defined.

(** [ap] の分配則その２。 *)
Definition ap_ff
  {A B C : Type}
  (f : B -> C) (g : A -> B)
  {x y : A} (p : x = y)
  : ap (f o g) p = ap f (ap g p) .
Proof.
 revert y p .
 refine (@paths_elim A x ?[ex_P] _) .
 exact 1 .
Defined.

(** 道の両辺に、左から道を合成する。 *)
Definition wiskerL
  {A : Type} {x y z : A}
  (p : x = y)
  {q r : y = z} (s : q = r)
  : p @ q = p @ r .
Proof.
 refine (ap (concat p) _) .
 exact s .
Defined.

(** 道の両辺に、右から道を合成する。 *)
Definition wiskerR
  {A : Type} {x y z : A}
  {p q : x = y} (r : p = q)
  (s : y = z)
  : p @ s = q @ s .
Proof.
 refine (ap (fun x => concat x s) _) .
 exact r .
Defined.

(** [concat p 1] は [p] に等しい。 *)
Definition concat_p1
  {A : Type}
  {x y : A} (p : x = y)
  : p @ 1 = p .
Proof.
 revert y p .
 refine (@paths_elim A x _ _) .
 exact 1 .
Defined.

(** [concat 1 p] は [p] に等しい。 *)
Definition concat_1p
  {A : Type}
  {x y : A} (p : x = y)
  : 1 @ p = p .
Proof.
 revert y p .
 refine (@paths_elim A x ?[ex_P] _) .
 exact 1 .
Defined.

(** 道の道を縦に合成する。 *)
Definition concat2
  {A : Type} {x y z : A}
  {p q : x = y} (r : p = q)
  {s t : y = z} (u : s = t)
  : p @ s = q @ t .
Proof.
 revert t u .
 refine (@paths_elim_nodep (y = z) s ?[ex_P] _) .
 revert q r .
 refine (@paths_elim_nodep (x = y) p ?[ex_P] _) .
 exact 1 .
Defined.

(** [coninv p p] は [idpath] に等しい。 *)
Definition coninv_pp
  {A : Type} {x y : A}
  (p : x = y) : coninv p p = 1 .
Proof.
 revert y p .
 refine (@paths_elim A x ?[ex_P] _) .
 exact 1 .
Defined.


(** ** Notations

    記法を定義する。 *)

Module Notation .

  (** [pwpaths] の記法。 *)
  Notation "f == g" := (pwpaths f g)
    (at level 70, no associativity)
    : type_scope
    .

End Notation .

(** 参考文献:

    * https://github.com/HoTT/HoTT/blob/1940297dd121d54d033274d84c5d023fdc56bfb4/theories/Basics/Notations.v
    * https://github.com/HoTT/HoTT/blob/1940297dd121d54d033274d84c5d023fdc56bfb4/theories/Basics/Overture.v
    * https://github.com/HoTT/HoTT/blob/1940297dd121d54d033274d84c5d023fdc56bfb4/theories/Basics/PathGroupoids.v

    *)
