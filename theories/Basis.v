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


(** ** Functional - Basic Functions

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
  Definition dsum_fst {A B} : @dsum A B -> A
    := dsum_elim_nodep (fun xv _ => xv) .

  (** [dsum] 版の [snd] 。 *)
  Definition dsum_snd {A B} (x : @dsum A B) : B (dsum_fst x)
    := dsum_elim (P := fun x' => B (dsum_fst x')) (fun _ xH => xH) x .

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

      旧来のCoqには [eq_truns] として存在する。 *)
  Definition concat
    {A : Type} {x y z : A}
    (p : paths x y) (q : paths y z) : paths x z
    := paths_elim_nodep (paths_elim_nodep idpath p) q .

  (** 道に沿って輸送する。 *)
  Definition transport
    {A : Type} {P : A -> Type}
    {x y : A} (p : paths x y)
    (u : P x) : P y
    := paths_elim_nodep u p .

  (** 道の両辺に関数を適用する。

      旧来のCoqには [f_equal] として存在する。 *)
  Definition ap
    {A B : Type} (f : A -> B)
    {x y : A} (p : paths x y)
    : paths (f x) (f y)
    := paths_elim_nodep (P := fun y' => paths (f x) (f y')) idpath p .

  Definition cast
    {A B : Type}
    (p : paths A B) (x : A) : B
    := transport p x .

End Functional.


(** ** Categorical - Categorical Functions

    これはあまり大真面目ではない部分である。削除されるかもしれない。 *)

Module Categorical.

  Definition initial {A : Type} : empty -> A
    := fun x => match x with end .

  Definition terminal {A : Type} : A -> unit
    := fun _ => tt .

  Definition coproduct {A B C : Type}
    : (A -> C) -> (B -> C) -> (sum A B -> C)
    := fun f g x =>
      match x with left y => f y | right z => g z end .

  Definition product {A B C : Type}
    : (A -> B) -> (A -> C) -> (A -> prod B C)
    := fun f g x => pair (f x) (g x) .

  Definition dependent_coproduct
    {X : Type} {A : X -> Type} {B : Type}
    : (forall x, A x -> B) -> (dsum A -> B)
    := fun f x => match x with dpair xv xH => f xv xH end .

  Definition dependent_product
    {X : Type} {A : Type} {B : X -> Type}
    : (forall x, A -> B x) -> (A -> dprod B)
    := fun f x => fun y => f y x .

End Categorical.


Module Homotopical.

  Export Functional.

  Definition compose10
    {A B C} (f : forall b, C b) (g : A -> B)
    : forall a, C (g a)
    := compose_dep f g .

  Definition compose01
    {A B C} (f : forall a, B a -> C a) (g : forall a, B a)
    : forall a, C a
    := fun x : A => f x (g x) .

  Definition ap00
    {A B : Type}
    (f : A -> B)
    (x : A)
    : B
    := f x .

  Definition ap01
    {A B : Type}
    (f : A -> B)
    {x y : A} (p : paths x y)
    : paths (f x) (f y)
    := ap f p .

  Definition ap10
    {A B : Type}
    {f g : A -> B} (p : paths f g)
    (x : A)
    : paths (f x) (g x)
    := paths_elim_nodep (P := fun g' => paths (f x) (g' x)) idpath p .

  Definition ap10_dep
    {A : Type} {B : A -> Type}
    {f g : forall a, B a} (p : paths f g)
    (x : A)
    : paths (f x) (g x)
    := paths_elim_nodep (P := fun g' => paths (f x) (g' x)) idpath p .

  Definition ap11
    {A B : Type}
    {f g : A -> B} (p : paths f g)
    {x y : A} (q : paths x y)
    : paths (f x) (g y)
    := paths_elim_nodep (P := fun g' => paths (f x) (g' y)) (ap f q) p .

  Definition ap01_2
    {A B C : Type}
    (f : A -> B -> C)
    (x y : A) (p : paths x y)
    (z w : B) (q : paths z w)
    : paths (f x z) (f y w)
    := ap11 (ap f p) q .

  Definition ap_dep
    {A : Type} {B : A -> Type}
    (f : forall a, B a)
    {x y : A} (p : paths x y)
    : paths (transport p (f x)) (f y)
    := paths_elim idpath p
      (P := fun y' p' => paths (transport p' (f x)) (f y'))
      .

  Definition ap01_dep
    {A : Type} {B : A -> Type}
    (f : forall a, B a)
    {x y : A} (p : paths x y)
    : paths (transport p (f x)) (f y)
    := ap_dep f p .

  Definition pwpaths
    {A : Type} {B : A -> Type} (f g : forall a, B a) : Type
    := forall a, paths (f a) (g a) .

  Definition pwpaths_paths
    {A : Type} {B : A -> Type}
    {f g : forall a, B a} (p : paths f g)
    : pwpaths f g
    := ap10_dep p .

  Definition pwpaths_compose01
    {A B C : Type}
    (f : B -> C)
    {g h : A -> B} (p : pwpaths g h)
    : pwpaths (compose f g) (compose f h)
    := compose01 (fun a => ap (x := g a) (y := h a) f) p .

  Definition pwpaths_compose10
    {A B C : Type}
    {f g : B -> C} (p : pwpaths f g)
    (h : A -> B)
    : pwpaths (compose f h) (compose g h)
    := compose10 p h .

  Definition section
    {A B : Type}
    (s : A -> B) (r : B -> A)
    : Type
    := pwpaths (compose r s) idmap .

  Definition retraction
    {A B : Type}
    (r : B -> A) (s : A -> B)
    : Type
    := pwpaths (compose r s) idmap .

  Definition is_adjoint
    {A B : Type}
    (f : A -> B) (g : B -> A)
    (retr : retraction f g) (sect : section f g)
    : Type
    := pwpaths (pwpaths_compose10 retr f) (pwpaths_compose01 f sect) .

  Definition is_equiv_rel
    {A B : Type}
    (f : A -> B) (g : B -> A)
    : Type
    := dsum (fun retr => dsum (fun sect => is_adjoint f g retr sect)) .

  Definition is_equiv
    {A B : Type} (f : A -> B)
    : Type
    := dsum (fun equiv_inv => is_equiv_rel f equiv_inv) .

  Definition equiv
    (A B : Type) : Type
    := dsum (fun f : A -> B => is_equiv f) .

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

  Definition trunc_paths
    (n : trunc_index) (A : Type) (H : is_trunc (trunc_succ n) A)
    (x y : A) : is_trunc n (paths x y)
    := H x y .

  Definition funext : Type
    := forall (A : Type) (B : A -> Type) (f g : forall a, B a),
      pwpaths f g -> paths f g .

  Definition funext_equiv : Type
    := forall (A : Type) (B : A -> Type) (f g : forall a, B a),
      is_equiv (pwpaths_paths (f := f) (g := g)) .

  Definition funext__funext_equiv (H : funext_equiv) : funext
    := fun A B f g => dsum_fst (H A B f g) .

  Definition pType : Type := dsum (fun A => A) .

  Definition hfiber {A B : Type} (f : A -> B) (y : B) : Type
    := dsum (fun x => paths (f x) y) .

End Homotopical.

Export Homotopical.
