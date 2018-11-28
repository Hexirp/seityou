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
  := apply f x .

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

(** ** Equivalence *)

(** 等価性 (Equivalence) は相同型理論 (Homotopy Type Theory) の中心的な
    概念である。「等価性」を定義する前に、私たちは [A] と [B] の二つの型が
    「同じである」と、どのようなときに言うべきかについて考えなければならない。

    一つ目は、互いに逆であるような [f : A -> B] と [g : B -> A] が存在する
    ことを要求することで、その条件は相同的に表される (up to homotopy) 。
    相同論的に語るならば、また私たちは、いくつかの条件をその相同に課すべき
    であり、それは圏論の随伴に対する三角同一性 (triangle identities) の一つで
    ある。かように、この概念は随伴等価 (adjoint equivalence) と呼ばれる。

    要求しなかった他の三角等値性は最初の三角等値性から得られ、より高い全ての
    一貫性 (coherence) も同様であるため、それらのうち一つだけを課するのは
    合理的である。さらに、この Equivalence でみることが出来るように、互いに
    逆であるような二つの写像、その相同があるだけで、三角同一性を満たす
    ようにその相同を修正することが常に行えるため、随伴等価が得られる。

    二つ目は、Vladimir Voevodsky による定義である、ある写像 [f : A -> B] の
    相同的繊維 (homotopy fiber) が可縮 (contractible) であるときであるという
    ものである。この概念は相同的全単射 (homotopy bijection) と呼ぶ。

    興味深き三つ目は、André Joyal の提案による定義である、写像 [f : A -> B] が
    相同的逆射を右か左かに分けてそれぞれ持つときであるというものである。
    この概念は相同的同型 (homotopy isomorphism) と呼ぶ。

    二つ目は元々使われていたもので、最も簡潔なものでしたが、形式的な部分では
    一つ目を使用したほうが感覚にあい、それは一つ目の定義が最も直接的に
    「等価性」を構造としてあらわすからです。特に、 [f] の相同的逆射を得るのが
    簡単であり、これは私たちが実践において最も気に掛けることなのだ。それゆえに
    随伴等価は単に「等価」として参照されるものとする。 *)

(** 言い方: 体系的に [equiv] は「型の等価性」とし [is_equiv] は
    「与えられた射が等価射である」とする。 *)

(** [s] は [r] の断面 (section) である。

    言い換えると [s] は [r] の右逆射である。 *)
Definition section
  {A B : Type}
  (s : A -> B) (r : B -> A)
  : Type
  := pwpaths (compose r s) idmap .

(** [r] は [s] の引き込み (retraction) である。

    言い換えると [r] は [s] の左逆射である。 *)
Definition retraction
  {A B : Type}
  (r : B -> A) (s : A -> B)
  : Type
  := pwpaths (compose r s) idmap .

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

(** [is_equiv A B] から逆射 [B -> A] を取り出す。 *)
Definition equiv_inv
  {A B : Type} {f : A -> B} : is_equiv f -> B -> A
  := dfst .

(** [is_equiv A B] から引き込み条件を取り出す。

    "equiv_inv is retraction" である。 *)
Definition eisretr
  {A B : Type} {f : A -> B} (H : is_equiv f) {x : B}
  : paths (f (equiv_inv H x)) x
  := dfst (dsnd H) x .

(** [is_equiv A B] から断面条件を取り出す。

    "equiv_inv is section" である。 *)
Definition eissect
  {A B : Type} {f : A -> B} (H : is_equiv f) {x : A}
  : paths (equiv_inv H (f x)) x
  := dfst (dsnd (dsnd H)) x .

(** [is_equiv A B] から随伴条件を取り出す。

    "equiv_inv is adjunction" である。若干の疑いあり。 *)
Definition eisadj
  {A B : Type} {f : A -> B} (H : is_equiv f) {x : A}
  : paths (eisretr H (x := f x)) (ap f (eissect H (x := x)))
  := dsnd (dsnd (dsnd H)) x .

(** [A] と [B] は等価 (equivalence) である。

    この型は "type of equivalences" と呼ばれる。 *)
Definition equiv
  (A B : Type) : Type
  := dsum (fun f : A -> B => is_equiv f) .

(** [equiv A B] から等価射 [A -> B] を取り出す。 *)
Definition equiv_fun
  {A B : Type} : equiv A B -> A -> B
  := dfst .

(** [equiv_fun] は [is_equiv] である。 *)
Definition equiv_fun_is_equiv
  {A B : Type} : forall x : equiv A B, is_equiv (equiv_fun x)
  := dsnd .

(** ** Truncation *)

(** 縮小 (Truncation) は、型の複雑性を測定する。このライブラリでは、ある型が
    ｎ次縮小 (n-truncated) であるという証拠を [is_trunc n] として形式化する。

    [is_trunc n (@paths A a b)] よりも [is_trunc (S n) A] の方が良く、
    [is_trunc n (forall a, P a)] よりも [forall a, is_trunc n (P a)] が、
    [is_trunc n (prod A B)] よりも [prod (is_trunc n A) (is_trunc n B)] が、
    つまりより小さい型に対するものが良い。 *)

(** *** Contraction *)

(** 空間 [A] は、このような時で可縮であり、このような時というのは、一つの点
    [x : A] があって、一つの（点ごと）相同的接続 (homotopy connecting) 、
    [A] の上での恒等写像から [x] への定値写像 (constant map) までのがあるとき
    である。ゆえに、一つの [contr A] の値は依存ペアで、最初の構成要素が
    一つの点 [x] であり、二番目の構成要素が、一つの [A] から [x] への引き込み
    である。 *)

(** [x] は全ての点への道を持つ。 *)
Definition is_contr_center (A : Type) (x : A) : Type
  := forall y, paths x y .

(** [A] は可縮である。 *)
Definition is_contr (A : Type) : Type
  := dsum (is_contr_center A) .

(** *** Truncation *)

(** 縮小 (Truncation) は、高階道空間の文脈において、型の複雑性を測る。
    (-2) 次縮小である型は、可縮である型のことであり、その相同 (Homotopy) は
    完全に自明である。また (n+1) 次縮小である型は、それらの道空間が n 次縮小
    である。

    ゆえに (-1) 次縮小であるということは「任意の二つの点の間の道の空間は可縮
    である」ということを意味する。そのような空間は部分単一 (sub-singleton)
    である、つまり、任意の二つの点は相同的に単一 (unique) である道で結ばれて
    いる。別の言葉でいえば (-1) 次縮小である空間は、真理値（私たちは「命題」と
    呼ぶ）である。

    次に 0 次縮小であるということは「任意の二つの点の間の道の空間は部分単一
    である」ということを意味する。ゆえに、二つの点は、その間に道を持たないか、
    単一の道を持つかである。そのような空間は沢山の点を持ち得るが、それは
    全ての道が自明であるという意味で、離散的である。私たちは、その空間群を
    「集合」と呼ぶ。 *)

(** 縮小度。つまり n 次縮小と書いたときの "n" を表す型。

    -2 がスタートで、一つずつ増えていく。 *)
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

(** 全ての道空間が [P] という性質を満たす。 *)
Definition paths_is (P : Type -> Type) (A : Type) : Type
  := forall (x y : A), P (paths x y) .

(** [A] は [n] 次縮小である。 *)
Definition is_trunc (n : trunc_index) (A : Type) : Type
  := trunc_index_rec is_contr paths_is n A .

(** *** Others *)

(** [A] は -2 次縮小（可縮）である。 *)
Definition contr (A : Type) : Type
  := is_trunc minus_two A .

(** [A] は -1 次縮小（命題）である。 *)
Definition is_hprop (A : Type) : Type
  := is_trunc (trunc_succ minus_two) A .

(** [A] は 0 次縮小（集合）である。 *)
Definition is_hset (A : Type) : Type
  := is_trunc (trunc_succ (trunc_succ minus_two)) A .

(** 道に対する縮小。 *)
Definition trunc_paths
  (n : trunc_index) (A : Type) (H : is_trunc (trunc_succ n) A)
  (x y : A) : is_trunc n (paths x y)
  := H x y .

(** ** Others *)

(** 関数外延性の公理の型。 *)
Definition funext : Type
  := forall (A : Type) (B : A -> Type) (f g : forall a, B a),
    is_equiv (pwpaths_paths (f := f) (g := g)) .

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

    "pointed type" である。 *)
Definition pType : Type := dsum (fun A => A) .

(** 相同的繊維。 [f] で [y] に移される値の集まり。 

    "homotopical fiber" である。点の相同的な逆像。 *)
Definition hfiber {A B : Type} (f : A -> B) (y : B) : Type
  := dsum (fun x => paths (f x) y) .
