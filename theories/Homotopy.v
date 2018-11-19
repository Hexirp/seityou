(** * Homotopy - Homotopical definitions

    Homotopy Type Theory において一般的な定義をする。 *)


Require Export Function.


(** 最初の引数が依存関数である関数合成。

    [compose_dep] の別名。 *)
Definition compose10
  {A B C} (f : forall b, C b) (g : A -> B)
  : forall a, C (g a)
  := compose_dep f g .

(** 二番目の引数が依存関数である関数合成。 *)
Definition compose01
  {A B C} (f : forall a, B a -> C a) (g : forall a, B a)
  : forall a, C a
  := fun x : A => f x (g x) .

(** ** Application *)

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

(** [f] を [x] に適用する。 *)
Definition ap00
  {A B : Type}
  (f : A -> B)
  (x : A)
  : B
  := f x .

(** [f] を [p] に適用する。

    [ap] の別名。 *)
Definition ap01
  {A B : Type}
  (f : A -> B)
  {x y : A} (p : paths x y)
  : paths (f x) (f y)
  := ap f p .

(** [p] を [x] に適用する。 *)
Definition ap10
  {A B : Type}
  {f g : A -> B} (p : paths f g)
  (x : A)
  : paths (f x) (g x)
  := paths_elim_nodep (P := fun g' => paths (f x) (g' x)) idpath p .

(** [ap10] の依存版。 *)
Definition ap10_dep
  {A : Type} {B : A -> Type}
  {f g : forall a, B a} (p : paths f g)
  (x : A)
  : paths (f x) (g x)
  := paths_elim_nodep (P := fun g' => paths (f x) (g' x)) idpath p .

(** [p] を [q] に適用する。 *)
Definition ap11
  {A B : Type}
  {f g : A -> B} (p : paths f g)
  {x y : A} (q : paths x y)
  : paths (f x) (g y)
  := paths_elim_nodep (P := fun g' => paths (f x) (g' y)) (ap f q) p .

(** [f] を [p] と [q] に適用する。 *)
Definition ap01_2
  {A B C : Type}
  (f : A -> B -> C)
  (x y : A) (p : paths x y)
  (z w : B) (q : paths z w)
  : paths (f x z) (f y w)
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
  {x y : A} (p : paths x y)
  : paths (transport p (f x)) (f y)
  := paths_elim idpath p
    (P := fun y' p' => paths (transport p' (f x)) (f y'))
    .

(** [ap01] の依存版。

    [ap_dep] の別名。 *)
Definition ap01_dep
  {A : Type} {B : A -> Type}
  (f : forall a, B a)
  {x y : A} (p : paths x y)
  : paths (transport p (f x)) (f y)
  := ap_dep f p .

(** ** Pointwise paths *)

(** 点ごとの道。関数の外延性等値性。

    "pointwize paths" である。 *)
Definition pwpaths
  {A : Type} {B : A -> Type} (f g : forall a, B a) : Type
  := forall a, paths (f a) (g a) .

(** 道から、点ごとの道を得る。

    逆は [funext] であり、証明も反証もできない。 *)
Definition pwpaths_paths
  {A : Type} {B : A -> Type}
  {f g : forall a, B a} (p : paths f g)
  : pwpaths f g
  := ap10_dep p .

(** 点ごとの道の両辺に、左から関数を合成する。 *)
Definition pwpaths_compose01
  {A B C : Type}
  (f : B -> C)
  {g h : A -> B} (p : pwpaths g h)
  : pwpaths (compose f g) (compose f h)
  := compose01 (fun a => ap (x := g a) (y := h a) f) p .

(** 点ごとの道の両辺に、右から関数を合成する。 *)
Definition pwpaths_compose10
  {A B C : Type}
  {f g : B -> C} (p : pwpaths f g)
  (h : A -> B)
  : pwpaths (compose f h) (compose g h)
  := compose10 p h .

(** [s] は [r] の断面 (section) である。

    [s] は [r] の右逆射である。 *)
Definition section
  {A B : Type}
  (s : A -> B) (r : B -> A)
  : Type
  := pwpaths (compose r s) idmap .

(** [r] は [s] の引き込み (retraction) である。

    [r] は [s] の左逆射である。 *)
Definition retraction
  {A B : Type}
  (r : B -> A) (s : A -> B)
  : Type
  := pwpaths (compose r s) idmap .

(** ** Equivalence *)

(** 等価性 (Equivalence) は相同型理論 (Homotopy Type Theory) の中心的な
    概念である。「等価性」を定義する前に、私たちは [A] と [B] の二つの型が
    「同じ」と、どのようなときにいうべきかについて考えなければならない。

    一つ目は、互いに逆であるような [f : A -> B] と [g : B -> A] が存在する
    ことを要求することで、その条件は相同的に表される (up to homotopy) 。
    相同理論的に語るならば、また私たちは、いくつかの条件をその相同に課すべき
    であり、それは圏論の随伴に対する三角同一性 (triangle identities) の一つで
    ある。かように、この概念は随伴等価 (adjoint equivalence) と呼ばれる。

    要求しなかった他の三角等値性は最初の三角等値性から得られ、より高い全ての
    一貫性 (coherence) も同様であるため、それらのうち一つだけを課するのは
    合理的である。さらに、この Equivalence でみることが出来るように、互いに
    逆であるような二つの写像、その相同があるだけで、三角同一性を満たす
    ようにその相同を修正することが常に行えるため、随伴等価が得られる。

    二つ目は、ある写像 [f : A -> B] の相同的繊維 (homotopy fiber) が
    可縮 (contractible) であるときであるという Vladimir Voevodsky 氏の定義を
    使うことである。この概念は相同的全単射 (homotopy bijection) と呼ぶ。

    三つ目は、ある写像 [f : A -> B] が相同的逆射を右か左かに分けてそれぞれ
    持つときであるという André Joyal の興味深い提案による定義である。
    この概念は相同的同型 (homotopy isomorphism) と呼ぶ。

    このライブラリでは随伴等価を採用する。 *)

(** [f] と [g] は [retr] と [sect] を通じて随伴的である。

    [A] の値を対象として [@paths A] を射とした圏（実際は大群 (Groupoid) で
    ある）から [B] の値を対象とした同じような圏への関手は、ただの関数
    [f : A -> B] として表される。対象の変換は、そのまま適用すればよく、
    [x] から [y] への射の変換は [ap f : paths x y -> paths (f x) (f y)] と
    する。この時、その関手 [f : A -> B] から [g : A -> B] への自然変換は
    [pwpaths f g] で表される。

    [retr] は余単位であり [sect] は単位であるが、大群であるため逆を取ることが
    できる。そのため、区別はあまりない。それらの間で単位―余単位恒等式が
    成立すれば随伴であると認められる。見慣れない形だが、逆を取れば見慣れた形
    になる。 *)
Definition is_adjoint
  {A B : Type}
  (f : A -> B) (g : B -> A)
  (retr : retraction f g) (sect : section f g)
  : Type
  := pwpaths (pwpaths_compose10 retr f) (pwpaths_compose01 f sect) .

(** [A] と [B] は [f] と [g] を通じて等価 (equivalence) である。 *)
Definition is_equiv_rel
  {A B : Type}
  (f : A -> B) (g : B -> A)
  : Type
  := dsum (fun retr => dsum (fun sect => is_adjoint f g retr sect)) .

(** [f] は等価射 (equivalence) である。 *)
Definition is_equiv
  {A B : Type} (f : A -> B)
  : Type
  := dsum (fun equiv_inv => is_equiv_rel f equiv_inv) .

(** [A] と [B] は等価 (equivalence) である。

    この型は "type of equivalences" と呼ばれる。 *)
Definition equiv
  (A B : Type) : Type
  := dsum (fun f : A -> B => is_equiv f) .

(** ** Truncation *)

Inductive trunc_index : Type
  :=
  | minus_two : trunc_index
  | trunc_succ : trunc_index -> trunc_index
  .

Definition trunc_index_rec
  {P : Type}
  (case_minus_two : P) (case_trunc_succ : P -> P)
  (x : trunc_index) : P
  :=
    let go :=
      fix go x :=
        match x with
        | minus_two => case_minus_two
        | trunc_succ xp => case_trunc_succ (go xp)
        end
    in go x
  .

Definition trunc_index_rect
  {P : trunc_index -> Type}
  (case_minus_two : P minus_two)
  (case_trunc_succ : forall xp, P xp -> P (trunc_succ xp))
  (x : trunc_index) : P x
  :=
    let go :=
      fix go x :=
        match x with
        | minus_two => case_minus_two
        | trunc_succ xp => case_trunc_succ xp (go xp)
        end
    in go x
  .

Definition is_contr_center (A : Type) (x : A) : Type
  := forall y, paths x y .

Definition is_contr (A : Type) : Type
  := dsum (is_contr_center A) .

Definition paths_is (P : Type -> Type) (A : Type) : Type
  := forall (x y : A), P (paths x y) .

Definition is_trunc (n : trunc_index) (A : Type) : Type
  := trunc_index_rec is_contr paths_is n A .

Definition contr (A : Type) : Type
  := is_trunc minus_two A .

Definition is_hprop (A : Type) : Type
  := is_trunc (trunc_succ minus_two) A .

Definition is_hset (A : Type) : Type
  := is_trunc (trunc_succ (trunc_succ minus_two)) A .

Definition trunc_paths
  (n : trunc_index) (A : Type) (H : is_trunc (trunc_succ n) A)
  (x y : A) : is_trunc n (paths x y)
  := H x y .

(** ** Others *)

Definition funext : Type
  := forall (A : Type) (B : A -> Type) (f g : forall a, B a),
    pwpaths f g -> paths f g .

Definition funext_equiv : Type
  := forall (A : Type) (B : A -> Type) (f g : forall a, B a),
    is_equiv (pwpaths_paths (f := f) (g := g)) .

Definition funext__funext_equiv (H : funext_equiv) : funext
  := fun A B f g => dfst (H A B f g) .

Definition pType : Type := dsum (fun A => A) .

Definition hfiber {A B : Type} (f : A -> B) (y : B) : Type
  := dsum (fun x => paths (f x) y) .
