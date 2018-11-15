(** * Basis - Basic definitions

    標準的な定義を行う。 *)

(** 新しい帰納型を定義した時に、自動で帰納法の原理／除去子が定義されない
    ようにする。

    除去子を自動生成される名前ではなく独自の名前付け規則で定義したいためだ。

    悲しいことに、 [induction] と [elim] 戦略は、対象となる型の除去子が
    自動生成されるデフォルトの名前を持っていることを前提にしている。そのため、
    何も知らない人がこのモジュールをインポートし、普通に型を定義し、いざ、
    その型についての帰納法を [induction] 戦略を使って行おうとしたとき、
    エラーとなり、その人は顔を歪めることになるだろう。

    代わりに [Local Unset Elimination Schemes] を使えば、 このモジュールを
    インポートしてもこの設定は引き継がれないので、不愉快な驚きを発生させる
    ことはないだろう。また、自分で除去子を定義するにしても、自動生成される
    デフォルトの名前と同じ名前をつけてやれば [induction] 戦略などを使える
    ようになる。自動生成される除去子を使いたくない理由の一つは、 [Prop] での
    除去子が生成されるためであるが、この方法を使えば [induction] 戦略を
    使えるようにしたまま、 [Prop] を排除できる。しかし、デフォルトで生成される
    名前に魅力を感じないため、この方法をとらない。陽に除去規則を使うことで
    代替する。

    参考文献:
    - https://coq.inria.fr/refman/user-extensions/proof-schemes.html#coq:flag.elimination-schemes
    - https://github.com/HoTT/HoTT/blob/fd5b9b9002e40cc94d6434039698a423bf3068ad/theories/Basics/Overture.v#L15 *)
Export Unset Elimination Schemes.

(** 除去子の名前は、このようなルールで名付けられる。

    普通の型は、非帰納的であるか、帰納的であるか、余帰納的であるかである。
    また、除去子は、除去する値に型が依存しないか、依存するかの違いがある。

    型 [thing] に対して、
    - 非帰納的であるならば、 [thing_elim_nodep], [thing_elim]
    - 帰納的であるならば、 [thing_rec], [thing_rect]
    - 余帰納的であるならば、 [thing_corec], [thing_corect]

    ここでの [thing_corect] はどのようなものなのかわからない。依存型の圏論的な
    双対にヒントがあるのではないかと見ているが、納得できる答えは知らない。
    ここでは、単純に定義しないことにする。

    非帰納的な例:
    <<
      Inductive thing : Type := mk_thing : unit -> thing .

      Definition thing_elim_nodep
        (P : Type) (case_mk_thing : unit -> P) (x : thing) : P
        := match x with mk_thing a => case_mk_thing a end .

      Definition thing_elim
        (P : thing -> Type) (case_mk_thing : forall t, P (mk_thing t))
        (x : thing) : P x
        := match x with mk_thing a => case_mk_thing a end .
    >>

    帰納的な例:
    <<
      Inductive nat : Type := zero : nat | succ : nat -> nat .

      Definition nat_rec
        (P : Type) (case_zero : P) (case_succ : P -> P) (x : nat) : P
        :=
          let go :=
            fix go x :=
              match x with
              | zero => case_zero
              | succ xp => case_succ (go xp)
              end
          in
            go x
        .

      Definition nat_rect
        (P : nat -> Type)
        (case_zero : P zero)
        (case_succ : forall xp, P xp -> P (succ xp))
        (x : nat) : P x
        :=
          let go :=
            fix go x :=
              match x with
              | zero => case_zero
              | succ xp => case_succ (go xp)
              end
          in
            go x
        .
    >>

    余帰納的な例:
    <<
      CoInductive stream (A : Type) := cons : A -> stream A -> stream A .

      Definition
        (P : Type)
        (case_head : P -> A) (case_tail : P -> P)
        (x : P) : stream A
        :=
          let go :=
            cofix go x :=
              cons (case_head x) (case_tail (go x))
          in
            go x
        .
    >>

    [A] に対する除去子は [x : A |- P x : Type] を組み立てるものである。
    その引数の名前は「除去する値は [x] である」「述語は [P] である」
    「型が持つ引数は元の型の定義と同じ名前である」という制約以外は裁量を持つ。

    *)

(** ** Basic Types

    標準的な型を定義する。 *)

(** 関数型の記法。

    関数型は [y] が定数関数であるときの依存積型である。 *)
Notation "x -> y" := (forall (_ : x), y)
  (at level 99, right associativity, y at level 200)
  .

(** 値を持たない型。 *)
Inductive empty : Type
  :=
  .

Definition empty_elim_nodep (P : Type) (x : empty) : P
  := match x with end .

Definition empty_elim (P : empty -> Type) (x : empty) : P x
  := match x with end .

Arguments empty .
Arguments empty_elim_nodep {_} _ .
Arguments empty_elim {_} _ .


(** ただ一つの値を持つ型。 *)
Inductive unit : Type
  :=
  | tt : unit
  .

Definition unit_elim_nodep
  (P : Type) (case_tt : P) (x : unit) : P
  := match x with tt => case_tt end .

Definition unit_elim
  (P : unit -> Type) (case_tt : P tt) (x : unit) : P x
  := match x with tt => case_tt end .

Arguments unit .
Arguments unit_elim_nodep {_} _ _ .
Arguments unit_elim {_} _ _ .

(** [A] と [B] の直和型。 *)
Inductive sum (A : Type) (B : Type) : Type
  :=
  | left : A -> sum A B
  | right : B -> sum A B
  .

Definition sum_elim_nodep
  (A : Type) (B : Type) (P : Type)
  (case_left : A -> P) (case_right : B -> P)
  (x : sum A B) : P
  := match x with
    | left _ _ a => case_left a
    | right _ _ b => case_right b
  end .

Definition sum_elim
  (A : Type) (B : Type) (P : sum A B -> Type)
  (case_left : forall a, P (left A B a))
  (case_right : forall b, P (right A B b))
  (x : sum A B) : P x
  := match x with
    | left _ _ a => case_left a
    | right _ _ b => case_right b
  end .

Arguments sum _ _ .
Arguments left {_ _} _ .
Arguments right {_ _} _ .
Arguments sum_elim_nodep {_ _ _} _ _ _ .
Arguments sum_elim {_ _ _} _ _ _ .

(** [A] と [B] の直積型。 *)
Inductive prod (A : Type) (B : Type) : Type
  :=
  | pair : A -> B -> prod A B
  .

Definition prod_elim_nodep
  (A : Type) (B : Type) (P : Type)
  (case_pair : A -> B -> P)
  (x : prod A B) : P
  := match x with pair _ _ a b => case_pair a b end .

Definition prod_elim
  (A : Type) (B : Type) (P : prod A B -> Type)
  (case_pair : forall a b, P (pair A B a b))
  (x : prod A B) : P x
  := match x with pair _ _ a b => case_pair a b end .

Arguments prod _ _ .
Arguments pair {_ _} _ _ .
Arguments prod_elim_nodep {_ _ _} _ _ .
Arguments prod_elim {_ _ _} _ _ .

(** [A] から [B] への関数型。

    網羅性のためであって、普段使いは推奨されない。

    "exponential object" である。 *)
Definition exp (A B : Type) : Type
  := A -> B.

Definition exp_elim_nodep
  (A : Type) (B : Type) (P : Type)
  (case : (A -> B) -> P)
  (x : exp A B) : P
  := case x .

Definition exp_elim
  (A : Type) (B : Type) (P : (A -> B) -> Type)
  (case : forall f, P f)
  (x : exp A B) : P x
  := case x .

Arguments exp _ _ .
Arguments exp_elim_nodep {_ _ _} _ _.
Arguments exp_elim {_ _ _} _ _.

(** [A] と [B] の依存和型。

    "dependent sum type" である。 *)
Inductive dsum (A : Type) (B : A -> Type) : Type
  :=
  | dpair : forall x : A, B x -> dsum A B
  .

Definition dsum_elim_nodep
  (A : Type) (B : A -> Type) (P : Type)
  (case_evi : forall x, B x -> P)
  (x : dsum A B) : P
  := match x with dpair _ _ xv xH => case_evi xv xH end .

Definition dsum_elim
  (A : Type) (B : A -> Type) (P : dsum A B -> Type)
  (case_evi : forall xv xH, P (dpair A B xv xH))
  (x : dsum A B) : P x
  := match x with dpair _ _ xv xH => case_evi xv xH end .

Arguments dsum {_} _ .
Arguments dpair {_ _} _ _ .
Arguments dsum_elim_nodep {_ _ _} _ _ .
Arguments dsum_elim {_ _ _} _ _ .

(** [A] と [B] の依存積型。

    網羅性のためであって、普段使いは推奨されない。

    "dependent product type" である。 *)
Definition dprod (A : Type) (B : A -> Type) : Type
  := forall x : A, B x .

Definition dprod_elim_nodep
  (A : Type) (B : A -> Type) (P : Type)
  (case : (forall x, B x) -> P)
  (x : dprod A B) : P
  := case x .

Definition dprod_elim
  (A : Type) (B : A -> Type) (P : dprod A B -> Type)
  (case : forall f, P f)
  (x : dprod A B) : P x
  := case x .

Arguments dprod {_} _ .
Arguments dprod_elim_nodep {_ _ _} _ _.
Arguments dprod_elim {_ _ _} _ _.

(** [A] の上での等式型。

    "equality type" や "identity type" であり、旧来のCoqでは [eq] と
    呼ばれるが、HoTTの流儀に従い [paths] と名付ける。 *)
Inductive paths (A : Type) (a : A) : A -> Type
  :=
  | idpath : paths A a a
  .

Definition paths_elim_nodep
  (A : Type) (a : A) (P : A -> Type)
  (case_idpath : P a)
  (a' : A) (x : paths A a a') : P a'
  := match x with idpath _ _ => case_idpath end .

Definition paths_elim
  (A : Type) (a : A) (P : forall a', paths A a a' -> Type)
  (case_idpath : P a (idpath A a))
  (a' : A) (x : paths A a a') : P a' x
  := match x with idpath _ _ => case_idpath end .

Arguments paths {_} _ _ .
Arguments idpath {_ _} , [_] _ .
Arguments paths_elim_nodep {_ _ _} _ {_} _ .
Arguments paths_elim {_ _ _} _ {_} _ .


(** ** Functional - Basic functions

    標準的な関数を記述する。 *)

Module Functional.

  (** 恒等関数。

      HoTTのライブラリに見られるように [Notation idmap := (fun x => x)] と
      定義することもでき、展開が必要ないことや宇宙多相の関係で良い面があるが、
      意図しない変換を発生させうる [Notation] をできるたけ使いたくないため
      こうする。 *)
  Definition idmap {A} : A -> A
    := fun x => x .

  (** 定数関数。 *)
  Definition const {A B} : A -> B -> A
    := fun x y => x .

  (** 関数合成 *)
  Definition compose {A B C} : (B -> C) -> (A -> B) -> (A -> C)
    := fun f g x => f (g x) .

  (** 関数合成の依存版。 *)
  Definition compose_dep
    {A B C} (f : forall b, C b) (g : A -> B)
    : forall a, C (g a)
    := fun x => f (g x) .

  (** 矛盾による安全なエラー。

      [empty] の値は存在しえないため、"ex falso quodlibet" よりどのような型も
      返すことが出来る。旧来のCoqには [exfalso] として存在する。 *)
  Definition absurd {A} : empty -> A
    := empty_elim_nodep .

  (** 一番最初の値を取り出す。 *)
  Definition fst {A B} : prod A B -> A
    := prod_elim_nodep (fun a _ => a) .

  (** 二番目の値を取り出す。 *)
  Definition snd {A B} : prod A B -> B
    := prod_elim_nodep (fun _ b => b) .

  (** カリー化された関数を対からの関数に変換する。 *)
  Definition uncurry {A B C} : (A -> B -> C) -> (prod A B -> C)
    := prod_elim_nodep .

  (** [dsum] 版の [fst] 。 *)
  Definition dfst {A B} : @dsum A B -> A
    := dsum_elim_nodep (fun xv _ => xv) .

  (** [dsum] 版の [snd] 。 *)
  Definition dsnd {A B} (x : @dsum A B) : B (dfst x)
    := dsum_elim (P := fun x' => B (dfst x')) (fun _ xH => xH) x .

  (** 関数の結果に [fst] を適用する。

      スコーレム関数を取り出す、とも表現できる。 *)
  Definition skolem {A B C}
    (f : forall a, @dsum B (C a)) (a : A) : B
    := dfst (f a) .

  (** 関数の結果に [snd] を適用する。

      スコーレム関数が満たす条件を取り出す、とも表現できる。 *)
  Definition skolemize {A B C}
    (f : forall a, @dsum B (C a)) (a : A) : C a (skolem f a)
    := dsnd (f a) .

  (** [paths] には二つの定義方法が存在する。今までの定義は「基点付き」であり、
      「基点なし」もある。このような定義である。

      <<
        Inductive paths (A : Type) : A -> A -> Type
          :=
          | idpath : forall a : A, paths A a a
          .
      >>

      この二つの方法で定義された [paths] は等価である。この「等価」の意味は
      強い。詳細は等式型のバリエーションを集めた Equality に譲る。

      とにかく、帰納法も対応するものがある。 [paths] に対する帰納法は特に
      道帰納法と呼ばれるから、基点無し道帰納法となる。これは、左右対称である
      ことによって、いくつかのケースで便利かもしれない。 *)

  (** 依存無し基点無し道帰納法。 *)
  Definition paths_elim_nodep_nop
    {A : Type} {P : A -> A -> Type}
    (case_idpath : forall a, P a a)
    (a a' : A) (x : paths a a') : P a a'
    := paths_elim_nodep (case_idpath a) x .

  (** 基点無し道帰納法。 *)
  Definition paths_elim_nop
    {A : Type} {P : forall a a', paths a a' -> Type}
    (case_idpath : forall a, P a a idpath)
    (a a' : A) (x : paths a a') : P a a' x
    := paths_elim (case_idpath a) x .

  (** 道を反転する。

      旧来のCoqには [eq_sym] として存在する。 *)
  Definition inverse
    {A : Type} {x y : A}
    (p : paths x y) : paths y x
    := paths_elim_nodep (P := fun y' => paths y' x) idpath p .

  (** 道を結合する。

      旧来のCoqには [eq_truns] として存在する。

      <<
        paths_elim_nodep p q
      >>

      このような定義もできるが、ここでは [p] と [q] を両方分解することによって
      その引数の両方が [idpath] であるときだけ [idpath] に簡約されるように
      なるので、証明がもっと堅牢かつ対称的になっている。上の定義を使ったときは
      [q] が [idpath] であるだけで [p] に簡約されてしまう。このバージョンの
      定義は Path の [contrans] を見よ。 *)
  Definition concat
    {A : Type} {x y z : A}
    (p : paths x y) (q : paths y z) : paths x z
    := paths_elim_nodep (paths_elim_nodep idpath p) q .

  (** 道に沿って輸送する。

      [paths_elim_nodep] の重要な帰結であり、引数を並べ変えただけである。

      「 [transport A P x y] は [u : P x] を [p : paths x y] に沿って [P y] へ
      輸送する」。 *)
  Definition transport
    {A : Type} {P : A -> Type}
    {x y : A} (p : paths x y)
    (u : P x) : P y
    := paths_elim_nodep u p .

  (** 道の両辺に関数を適用する。

      "application" であり、 "action on path" でもある。旧来のCoqには [f_equal]
      として存在する。 *)
  Definition ap
    {A B : Type} (f : A -> B)
    {x y : A} (p : paths x y)
    : paths (f x) (f y)
    := paths_elim_nodep (P := fun y' => paths (f x) (f y')) idpath p .


  (** [A] と [B] が等しいとき [x : A] を [B] に変換する。 *)
  Definition cast
    {A B : Type}
    (p : paths A B) (x : A) : B
    := transport p x .

End Functional.


(** ** Homotopical - Homotopical definitions

    Homotopy Type Theory において一般的な定義をする。 *)

Module Homotopical.

  Export Functional.

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

  (** *** Application *)

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

  (** *** Pointwise paths *)

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

  (** *** Equivalence *)

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

  (** *** Truncation *)

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

  (** *** Others *)

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

End Homotopical.

Export Homotopical.
