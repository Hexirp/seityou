(** * Homotopy

    Homotopy Type Theory において一般的な定義をする。 *)

Require Import Basis .
Require Import Path .

(** 戦術を使う。 *)
Declare ML Module "ltac_plugin" .
Set Default Proof Mode "Classic" .

(** 記法を使う。 *)
Import Basis.Notation .
Import Basis.Notation.Path .


(** ** Equivalence *)

(** 等価性 (Equivalence) は相同型理論 (Homotopy Type Theory) の中心的な
    概念である。「等価性」、その定義には三つの種類がある。

    一つ目は、互いに逆であるような [f : A -> B] と [g : B -> A] が存在する
    ことを要求することで、その条件は相同的に表される (up to homotopy) 。
    相同論的に語るならば、私たちは、またいくつかの条件をその相同に課すべき
    であり、それは圏論の随伴に対する三角同一性 (triangle identities) の一つで
    ある。かように、この概念は随伴等価 (adjoint equivalence) と呼ばれる。

    要求しなかった他の三角等値性は最初の三角等値性から得られ、より高い全ての
    一貫性 (coherence) も同様であるため、それらのうち一つだけを課するのは
    合理的である。さらに、Equivalence でみることが出来るように、互いに
    逆であるような二つの写像、その相同があるだけで、三角同一性を満たす
    ようにその相同を修正することが常に行えることにより随伴等価が得られる。

    二つ目は、Vladimir Voevodsky による定義である、ある写像 [f : A -> B] の
    相同的繊維 (homotopy fiber) が可縮 (contractible) であるときであるという
    ものである。この概念は相同的全単射 (homotopy bijection) と呼ぶ。

    三つ目は、André Joyal による定義である、ある写像 [f : A -> B] が
    相同的逆射を右か左かに分けてそれぞれ持つときであるというものである。
    この概念は相同的同型 (homotopy isomorphism) と呼ぶ。

    このライブラリでは、HoTT のライブラリに倣い、随伴等価を採用する。 *)

(** [s] を適用した後に [r] を適用すると元に戻る。

    * [s] は [r] の右逆射である。
    * [s] は [r] の断面 (section) である。
    * [r] は [s] の左逆射である。
    * [r] は [s] の引き込み (retraction) である。 *)
Definition sect
  {A B : Type}
  (s : A -> B) (r : B -> A)
  : Type
  := forall x, r (s x) = x .

(** [f] と [g] は [retr] と [sect] を通じて随伴的である。

    [A] の値を対象として [@paths A] を射とした圏（実際は大群 (Groupoid) で
    ある）から [B] の値を対象とした同じような圏への関手は、ただの関数
    [f : A -> B] として表される。対象の変換は、そのまま適用すればよく、
    [x] から [y] への射の変換は [ap f : paths x y -> paths (f x) (f y)] と
    となる。この時、その関手 [f : A -> B] から [g : A -> B] への自然変換は
    [forall x, paths (f x) (g x)] で、すなわち [pwpaths f g] で表される。

    こう考えると、ある二つの等式圏 [A] と [B] の間に関手 [f : A -> B] と
    [g : B -> A] があり、それぞれ余単位射と単位射と呼ばれる二つの自然変換
    [r : pwpaths (compose f g) idmap] と [s : pwpaths idmap (compose g f)] が
    あるとし、さらにそれらの合成が二つの条件を満たすとき、随伴であると呼ばれる
    ことになる。これは、普通の圏での随伴の定義を適用しただけである。

    ここで Equivalence の前説で書いた通り、実際にはただ一つの条件だけでよく
    （むしろ、一つだけの方が相同的な性質に関してよく振る舞う）、これは等式圏
    であるからである。即ち、その条件は [r] の両辺に [f] を右から合成したもの
    と、そして [s] の両辺に [f] を左から合成したものを、さらに合成したとき、
    それが恒等関手になることだと定められる。

    この時 [s] を反転させて [s : pwpaths (compose g f) idmap] という風に
    [r] と綺麗に型をそろえてやると、一般的に、道を移項させることが出来ること
    から [paths (concat (inverse p) q) idpath)] は [paths q p] と同じこと
    になることから定義を簡略化でき、この定義もそのようになっている。 *)
Definition is_adjoint
  {A B : Type}
  {f : A -> B} {g : B -> A}
  (retr : sect g f) (sect : sect f g)
  : Type
  := forall x, retr (f x) = ap f (sect x) .

(** [A] と [B] は [f] と [g] を通じて等価 (equivalence) である。 *)
Definition is_equiv_rel
  {A B : Type}
  (f : A -> B) (g : B -> A)
  : Type
  := sigma retr sect, is_adjoint (f := f) (g := g) retr sect .

(** [f] は等価射 (equivalence) である。 *)
Definition is_equiv
  {A B : Type} (f : A -> B)
  : Type
  := sigma equiv_inv, is_equiv_rel f equiv_inv .

(** [is_equiv A B] から逆射 [B -> A] を取り出す。 *)
Definition equiv_inv
  {A B : Type} {f : A -> B} : is_equiv f -> B -> A
  := dfst .

(** [is_equiv A B] から引き込み条件を取り出す。

   名前は "equiv_inv is retraction" を縮めたもの。 *)
Definition eisretr
  {A B : Type} {f : A -> B} (H : is_equiv f) {x : B}
  : paths (f (equiv_inv H x)) x
  := dfst (dsnd H) x .

(** [is_equiv A B] から断面条件を取り出す。

    名前は "equiv_inv is section" を縮めたもの。 *)
Definition eissect
  {A B : Type} {f : A -> B} (H : is_equiv f) {x : A}
  : paths (equiv_inv H (f x)) x
  := dfst (dsnd (dsnd H)) x .

(** [is_equiv A B] から随伴条件を取り出す。

    名前は "equiv_inv is adjunction" を縮めたもの。若干の疑いあり。 *)
Definition eisadj
  {A B : Type} {f : A -> B} (H : is_equiv f) {x : A}
  : paths (eisretr H (x := f x)) (ap f (eissect H (x := x)))
  := dsnd (dsnd (dsnd H)) x .

(** [A] と [B] は等価 (equivalence) である。

    この型は "type of equivalences" と呼ばれる。 *)
Definition equiv
  (A B : Type) : Type
  := sigma f, is_equiv (A := A) (B := B) f .

(** [equiv A B] から等価射 [A -> B] を取り出す。 *)
Definition equiv_fun
  {A B : Type} : equiv A B -> A -> B
  := dfst .

(** [equiv_fun] は [is_equiv] である。 *)
Definition equiv_fun_is_equiv
  {A B : Type} : forall x : equiv A B, is_equiv (equiv_fun x)
  := dsnd .

(** ** Truncation *)

(** 切捨 (Truncation) は、型の複雑性を測定する。このライブラリでは、ある型が
    ｎ次切捨 (n-truncated) であるという証拠を [is_trunc n] として形式化する。
    これは HoTT ライブラリに倣ったものである。

    [is_trunc n (@paths A a b)] よりも [is_trunc (S n) A] の方を、
    [is_trunc n (forall a, P a)] よりも [forall a, is_trunc n (P a)] の方を、
    [is_trunc n (prod A B)] よりも [prod (is_trunc n A) (is_trunc n B)] の方を、
    つまり、より細かい型に対して記述するようにする。 *)

(** *** Contraction *)

(** 空間 [A] が可縮であるというのは、一つの点 [x : A] があって、一つの
    （点ごと）相同的接続 (homotopy connecting) 、それが [A] の上での
    恒等写像から [x] への定値写像 (constant map) までのがあるときである。
    ゆえに、一つの [contr A] の値は依存ペアで、最初の構成要素が一つの点
    [x] であり、二番目の構成要素が、一つの [A] から [x] への引き込み
    である。 *)

(** [x] は全ての点への道を持つ。 *)
Definition is_contr_center (A : Type) (x : A) : Type
  := forall y, paths x y .

(** [A] は可縮である。 *)
Definition is_contr (A : Type) : Type
  := sigma x, is_contr_center A x .

(** [A] が [contr] であるとき、その中心を得る。 *)
Definition center {A : Type} (IC : is_contr A) : A
  := dfst IC .

(** *** Truncation *)

(** 切捨 (Truncation) は、高階道空間の文脈において、型の複雑性を測る。
    (-2) 次切捨である型は、可縮である型のことであり、その相同 (Homotopy) は
    完全に自明である。また (n+1) 次切捨である型は、それらの道空間が n 次切捨
    である。

    ゆえに (-1) 次切捨であるということは「任意の二つの点の間の道の空間は可縮
    である」ということを意味する。そのような空間は部分単一 (sub-singleton)
    である、つまり、任意の二つの点は相同的に単一 (unique) である道で結ばれて
    いる。別の言葉でいえば (-1) 次切捨である空間は、真理値（私たちは「命題」と
    呼ぶ）である。

    次に 0 次切捨であるということは「任意の二つの点の間の道の空間は部分単一
    である」ということを意味する。ゆえに、二つの点は、その間に道を持たないか、
    単一の道を持つかである。そのような空間は沢山の点を持ち得るが、それは
    全ての道が自明であるという意味で、離散的である。私たちは、その空間群を
    「集合」と呼ぶ。 *)

(** 切捨度。つまり n 次切捨と書いたときの "n" を表す型。

    自然数のペアノの公理による定義と同じ構造を持っているが、
    -2 が最小の値である。 *)
Inductive trunc_index : Type
  :=
  | minus_two : trunc_index
  | trunc_S : trunc_index -> trunc_index
  .

Definition trunc_index_case_nodep
  {P : Type}
  (case_minus_two : P)
  (case_trunc_S : trunc_index -> P)
  (x : trunc_index) : P .
Proof.
 refine (match x with minus_two => _ | trunc_S xp => _ end) .
 -
  exact case_minus_two .
 -
  exact (case_trunc_S xp) .
Defined.

Definition trunc_index_case
  {P : trunc_index -> Type}
  (case_minus_two : P minus_two)
  (case_trunc_S : forall xp, P (trunc_S xp))
  (x : trunc_index) : P x .
Proof.
 refine (match x with minus_two => _ | trunc_S xp => _ end) .
 -
  exact case_minus_two .
 -
  exact (case_trunc_S xp) .
Defined.

Definition trunc_index_rec
  {P : Type}
  (case_minus_two : P) (case_trunc_S : P -> P)
  (x : trunc_index) : P .
Proof.
 revert x .
 refine (fix go (x : trunc_index) {struct x} := _) .
 refine (trunc_index_case_nodep _ _ x) .
 -
  exact case_minus_two .
 -
  refine (fun xp => _) .
  exact (case_trunc_S (go xp)) .
Defined.

Definition trunc_index_rect
  {P : trunc_index -> Type}
  (case_minus_two : P minus_two)
  (case_trunc_S : forall xp, P xp -> P (trunc_S xp))
  (x : trunc_index) : P x .
Proof.
 revert x .
 refine (fix go (x : trunc_index) {struct x} := _) .
 refine (trunc_index_case _ _ x) .
 -
  exact case_minus_two .
 -
  refine (fun xp => _) .
  exact (case_trunc_S xp (go xp)) .
Defined.

(** 全ての道空間が [P] という性質を満たす。 *)
Definition paths_is (P : Type -> Type) (A : Type) : Type
  := forall (x y : A), P (x = y) .

(** [A] は [n] 次切捨である。 *)
Definition is_trunc (n : trunc_index) (A : Type) : Type
  := trunc_index_rec is_contr paths_is n A .

(** *** Others *)

(** [A] は -2 次切捨（可縮）である。 *)
Definition contr (A : Type) : Type
  := is_trunc minus_two A .

(** [A] は -1 次切捨（命題）である。 *)
Definition is_hprop (A : Type) : Type
  := is_trunc (trunc_S minus_two) A .

(** [A] は 0 次切捨（集合）である。 *)
Definition is_hset (A : Type) : Type
  := is_trunc (trunc_S (trunc_S minus_two)) A .

(** [R] は -1 次切捨である値を持つ関係である。

    即ち、単に関係であることであり、複数の値を持たない。 *)
Definition is_mere_relation {A : Type} (R : A -> A -> Type) : Type
  := forall x y, is_hprop (R x y) .

(** 道に対する切捨。 *)
Definition trunc_paths
  (n : trunc_index) (A : Type) (H : is_trunc (trunc_S n) A)
  (x y : A) : is_trunc n (x = y)
  := H x y .

(** ** Others *)

(** 関数外延性の公理の型。 *)
Definition funext : Type
  := forall (A : Type) (B : A -> Type) (f g : forall a, B a),
    is_equiv (@ap10_dep A B f g) .

(** 全称量化に対する道。

    旧来の関数外延性の公理の導出とも捉えることが出来る。 *)
Definition path_forall
  (ax : funext)
  {A : Type} {P : A -> Type}
  {f g : forall x, P x}
  (p : forall x, paths (f x) (g x))
  : paths f g
  := equiv_inv (ax A P f g) p .

(** [path_forall] の二変数版。 *)
Definition path_forall_2
  (ax : funext)
  {A B : Type} {P : A -> B -> Type}
  {f g : forall x y, P x y}
  (p : forall x y, paths (f x y) (g x y))
  : paths f g
  := path_forall ax (fun x => path_forall ax (p x)) .

(** 点付きの型。

    名前は "pointed type" を縮めたもの。 *)
Definition pType : Type := sigma A, A .

(** 相同的繊維。 [f] で [y] に移される値の集まり。 

    名前は "homotopical fiber" を縮めたもの。点の相同的な逆像。 *)
Definition hfiber {A B : Type} (f : A -> B) (y : B) : Type
  := sigma x, f x = y .


(** ** Notations

    記法を定義する。 *)

Module Notation .

  (** 記法が使われる文脈を設定する。 *)
  Delimit Scope equiv_scope with equiv.
  Delimit Scope trunc_scope with trunc.

  (** 文脈を開く。 *)
  Open Scope equiv_scope.
  Open Scope trunc_scope.

  (** 文脈を型と結びつける。 *)
  Bind Scope equiv_scope with equiv .
  Bind Scope function_scope with trunc_index .

  (** 型の等価性の記法。 *)
  Notation "A <~> B" := (equiv A B)
    (at level 85, no associativity)
    : type_scope.

End Notation .

(** 参考文献:

    * https://github.com/HoTT/HoTT/blob/1940297dd121d54d033274d84c5d023fdc56bfb4/theories/Basics/Overture.v

    *)
