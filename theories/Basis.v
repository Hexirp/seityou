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

(* Arguments empty . *)
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

(* Arguments unit . *)
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

(* Arguments sum _ _ . *)
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

(* Arguments prod _ _ . *)
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

(* Arguments exp _ _ . *)
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
