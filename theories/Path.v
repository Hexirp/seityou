(** * Path

    道に関する定義を行う。 *)

Require Export Basis .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation Basis.Notation.Path .


(** ** Applications *)

(** [ap] のバリエーションは以下の命令規則に従う。

    [apNK] は関数のK次道を値のN次道に適用する。関数が依存版である場合は、
    [apNK_dep] となる。関数がLつの値を取るとき、値のN次道はLつあり、名前は
    [apNK_L] となる。

    K次道は値、値の道、値の道の道といったものを表す。これは縮小 (Truncation)
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


(** ** Pointwise paths *)

(** 点ごとの道。関数の外延性等値性。

    名前は "pointwize paths" を縮めたもの。 *)
Definition pwpaths
  {A : Type} {B : A -> Type} (f g : forall a, B a) : Type
  := forall a, f a = g a .

(** 道から、点ごとの道を得る。

    逆は [funext] であり、証明も反証もできない。 *)
Definition pwpaths_paths
  {A : Type} {B : A -> Type}
  {f g : forall a, B a} (p : paths f g)
  : pwpaths f g
  := ap10_dep p .

(** 点ごとの恒等道。 *)
Definition idpath_pw
  {A : Type} {B : A -> Type}
  (f : forall a, B a)
  : pwpaths f f
  := fun a => idpath (f a) .

Arguments idpath_pw {_ _ _}, [_ _] _ .

(** 点ごとの道の逆。 *)
Definition inverse_pw
  {A : Type} {B : A -> Type}
  {f g : forall a, B a}
  (p : pwpaths f g)
  : pwpaths g f
  := fun a => inverse (p a) .

(** 点ごとの道の合成。 *)
Definition concat_pw
  {A : Type} {B : A -> Type}
  {f g h : forall a, B a}
  (p : pwpaths f g) (q : pwpaths g h)
  : pwpaths f h
  := fun a => concat (p a) (q a) .

(** 点ごとの道の両辺に、左から関数を合成する。 *)
Definition wiskerL_pw_fn
  {A B C : Type}
  (f : B -> C)
  {g h : A -> B} (p : pwpaths g h)
  : pwpaths (compose f g) (compose f h) .
Proof.
 refine (fun x => _) .
 change (f (g x) = f (h x)) .
 refine (ap f _) .
 exact (p x) .
Defined.

(** 点ごとの道の両辺に、右から関数を合成する。 *)
Definition wiskerR_pw_fn
  {A B C : Type}
  {f g : B -> C} (p : pwpaths f g)
  (h : A -> B)
  : pwpaths (compose f h) (compose g h) .
Proof.
 refine (fun x => _) .
 change (f (h x) = g (h x)) .
 exact (p (h x)) .
Defined.


(** ** Others

    そのほかの、関数など。 *)

(** [p] を反転して [q] を合成する。

    [forall y, x = y] のような、同じ方向の道のパターンの時に便利。 *)
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


(** ** Notations *)

Module Notation .

  Export Basis.Notation Basis.Notation.Path .

  Notation "f == g" := (pwpaths f g)
    (at level 70, no associativity)
    : type_scope
    .

End Notation .
