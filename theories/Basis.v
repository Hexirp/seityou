(** * Basis

    標準的な定義を行う。 *)

(** 新しい帰納型を定義した時に、自動で帰納法の原理／除去子が定義されない
    ようにする。

    除去子を自動生成される名前ではなく独自の名前付け規則で定義したいため。

    [induction] と [elim] 戦略は、対象となる型の除去子が、自動生成される
    デフォルトの名前を持っていることを前提にしているため、何も知らない人が
    このモジュールをインポートし、普通に型を定義し、いざ、その型についての
    帰納法を [induction] 戦略を使って行おうするその時、エラーとなってしまう。

    代わりに [Local Unset Elimination Schemes] を使えば、 このモジュールを
    インポートしてもこの設定は引き継がれないので、ユーザーをびっくりさせる
    ことはないだろし、自分で除去子を定義するにしても、自動生成される名前と、
    同じ名前をつけてやれば [induction] 戦略などを使える（と思う）。

    自動生成される除去子を使いたくない理由の一つは [Prop] での除去子が
    生成されるためだが、この方法を使えば [induction] 戦略を使えるように
    したまま [Prop] を排除できる。

    しかし、もう一つの使いたくない理由である、自動生成される名前が気に入らない
    という問題は解決できないので、この方法は選択しない。陽に除去子を使い、
    帰納法を行うことにする。

    参考文献:
    - https://coq.inria.fr/refman/user-extensions/proof-schemes.html#coq:flag.elimination-schemes
    - https://github.com/HoTT/HoTT/blob/fd5b9b9002e40cc94d6434039698a423bf3068ad/theories/Basics/Overture.v#L15 *)
Export Unset Elimination Schemes .

(** 除去子の名前のルール。

    普通の型は、非帰納的であるか、帰納的であるか、余帰納的であるかであり、
    さらに一つの型の除去子をとってみても、型が依存しないか、依存するかの
    違いがある。

    型 [thing] に対して、
    - 非帰納的であるならば、 [thing_elim_nodep], [thing_elim]
    - 帰納的であるならば、 [thing_rec], [thing_rect]
    - 余帰納的であるならば、 [thing_corec], [thing_corect]

    ここでの [thing_corect] はどのようなものなのかわからない。依存型の
    圏論的な双対にヒントがあるのではないかと考えてはいるが、納得できる
    答えは知らない。ここでは、単純に定義しないことにする。（そもそも、
    余帰納型に対する除去子というのはちょっと語弊があり、名前と違って
    値を構築するものになる）

    それら除去子の引数の名前は「除去する値は [x] である」「結果の型は
    [P] である」「型が持つ引数は元の型の定義と同じ名前である」という
    ことを除いて自由であるとする。

    名前につく "elim" は "elimination" 、"nodep" は "no dependent"、
    "rec" は "recursion" 、"rect" は "rec" に "type" を足したもの、
    "corec" は "corecursion" 、"corec" は "corec" に "type" を足したもの
    である。"rect", "corect" に関しては、Coq から引用した名前であり、
    この由来に対しては若干の疑いがある。 *)

(** ** Types

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
    名前は "function" を縮めたもの。 *)
Definition fn (A B : Type) : Type
  := A -> B.

Definition fn_elim_nodep
  (A : Type) (B : Type) (P : Type)
  (case : (A -> B) -> P)
  (x : fn A B) : P
  := case x .

Definition fn_elim
  (A : Type) (B : Type) (P : (A -> B) -> Type)
  (case : forall f, P f)
  (x : fn A B) : P x
  := case x .

(* Arguments fn _ _ . *)
Arguments fn_elim_nodep {_ _ _} _ _.
Arguments fn_elim {_ _ _} _ _.


(** [A] と [B] の依存和型。

    名前は "dependent sum type" を縮めたもの。 *)
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
    名前は "dependent product type" を縮めたもの。 *)
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

    "equality type" や "identity type" であり、旧来の Coq では [eq] と
    呼ばれるが、HoTT の流儀に従い [paths] と名付けた。 *)
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


(** ** Functions

    標準的な関数を定義する。 *)

(** 恒等関数。

    HoTT のライブラリに見られるように [Notation idmap := (fun x => x)] と
    定義することもでき、展開が必要ないことや宇宙多相の関係で良い面がある。
    しかし、意図しない表示を発生させうる [Notation] をできるたけ使いたく
    ないため、このように関数として書く。

    名前は "identity map" を縮めたもの。 *)
Definition idmap {A} : A -> A
  := fun x => x .

(** 定数関数。すなわち [const a b = a] であり [const a] は [a] を常に返す。

    名前は "constant" を縮めたもの。 *)
Definition const {A B} : A -> B -> A
  := fun x y => x .

(** 関数合成。すなわち [compose f g x] は [f (g x)] である。 *)
Definition compose {A B C} : (B -> C) -> (A -> B) -> (A -> C)
  := fun f g x => f (g x) .

(** 関数合成の依存版。 [f] が依存関数となっている。 *)
Definition compose_dep
  {A B C} (f : forall b, C b) (g : A -> B)
  : forall a, C (g a)
  := fun x => f (g x) .

(** 適用。そのほかに [idmap] を関数だけに制限したものと見ることもできる。 *)
Definition apply {A B} : (A -> B) -> A -> B
  := idmap .

(** 依存関数の適用。 [apply] と同様に [idmap] を制限したもの。 *)
Definition apply_dep {A B} : (forall a : A, B a) -> forall a : A, B a
  := idmap .

(** 矛盾による安全なエラー。

    [empty] の値は存在しえないため、"ex falso quodlibet" よりどのような型も
    返すことが出来る。旧来の Coq には [exfalso] として存在する。 *)
Definition absurd {A} : empty -> A
  := empty_elim_nodep .

(** 直積の一番最初の値を取り出す。

    名前は "first" を縮めたもの。 *)
Definition fst {A B} : prod A B -> A
  := prod_elim_nodep (fun a _ => a) .

(** 直積の二番目の値を取り出す。

    名前は "second" を縮めたもの。 *)
Definition snd {A B} : prod A B -> B
  := prod_elim_nodep (fun _ b => b) .

(** 対からの関数をカリー化する。 *)
Definition curry {A B C} : (prod A B -> C) -> (A -> B -> C)
  := fun f a b => f (pair a b) .

(** カリー化された関数を対からの関数に変換する。 *)
Definition uncurry {A B C} : (A -> B -> C) -> (prod A B -> C)
  := prod_elim_nodep .

(** [dsum] 版の [fst] 。 *)
Definition dfst {A B} : @dsum A B -> A
  := dsum_elim_nodep (fun xv _ => xv) .

(** [dsum] 版の [snd] 。 *)
Definition dsnd {A B} (x : @dsum A B) : B (dfst x)
  := dsum_elim (P := fun x' => B (dfst x')) (fun _ xH => xH) x .

(** 関数の結果に [dfst] を適用する。

    スコーレム関数を取り出す、とも表現できる。 *)
Definition dfst_forall {A B C}
  (f : forall a, @dsum (B a) (C a)) (a : A) : B a
  := dfst (f a) .

(** 関数の結果に [dsnd] を適用する。

    スコーレム関数が満たす条件を取り出す、とも表現できる。 *)
Definition dsnd_forall {A B C}
  (f : forall a, @dsum (B a) (C a)) (a : A) : C a (dfst_forall f a)
  := dsnd (f a) .

(** [paths] には二つの定義方法が存在する。Basis の定義は「基点付き」であり、
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
    ことによって、いくつかのケースで便利かもしれない。

    名前につく "nop" は "no point" を縮めたもの。 *)

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

    旧来の Coq には [eq_sym] として存在する。 *)
Definition inverse
  {A : Type} {x y : A}
  (p : paths x y) : paths y x
  := paths_elim_nodep (P := fun y' => paths y' x) idpath p .

(** 道を結合する。

    <<
      paths_elim_nodep q p
    >>

    このような定義もできるが、ここでは [p] と [q] を両方分解することによって
    その引数の両方が [idpath] であるときだけ [idpath] に簡約されるように
    なるので、証明がより堅牢かつ対称的になっている。上の定義を使ったときは
    [q] が [idpath] であるだけで [p] に簡約されてしまう。このバージョンの
    定義は Path の [contrans] を見よ。

    旧来の Coq には [eq_truns] として存在する。*)
Definition concat
  {A : Type} {x y z : A}
  (p : paths x y) (q : paths y z) : paths x z
  := paths_elim_nodep (paths_elim_nodep idpath p) q .

(** 道に沿って輸送する。

    [paths_elim_nodep] の引数を並べ変えただけであるが、重要な関数である。

    「 [transport A P x y] は [u : P x] を [p : paths x y] に沿って [P y] へ
    輸送する」と、表記される。ここで暗黙引数はないとした。 *)
Definition transport
  {A : Type} {P : A -> Type}
  {x y : A} (p : paths x y)
  (u : P x) : P y
  := paths_elim_nodep u p .

(** 道の両辺に関数を適用する。

    名前は "application" を縮めたものであり、 "action on path" を縮めたもの
    でもある。旧来の Coq には [f_equal] として存在する。 *)
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

(** 道帰納法の反転は、[pattern], [inverse] タクティックと同じことをやるために
    定義されている。名前の "rev" は "reverse" を縮めたもの。 *)

(** [paths_elim_nodep] の反転。 *)
Definition paths_rev_elim_nodep
  {A : Type} {a : A} {P : A -> Type}
  (c : forall a', paths a a' -> P a')
  : P a
  := c a idpath .

(** [paths_elim] の反転。

    網羅性のためであって意味はあまりない。 *)
Definition paths_rev_elim
  {A : Type} {a : A} {P : forall a', paths a a' -> Type}
  (c : forall a' p, P a' p)
  : P a idpath
  := c a idpath .


(** ** Notations

    記法を定義する。 *)

Module Notation .

  (** 記法が使われる文脈を設定する。 *)
  Delimit Scope type_scope with type .
  Delimit Scope function_scope with function .

  (** 文脈を開く。 *)
  Open Scope type_scope .
  Open Scope function_scope .

  (** 文脈を型と結びつける。 *)
  Bind Scope type_scope with Sortclass .
  Bind Scope function_scope with Funclass .

  (** 依存和は、ある型を渡る和として表現されるため "sigma" と書く。 *)
  Notation "'sigma' x .. y , p" := (dsum (fun x => .. (dsum (fun y => p)) ..))
    (at level 200, x binder, right associativity,
      format "'[' 'sigma'  '/ ' x .. y ,  '/ ' p ']'")
    : type_scope
    .

  (** 依存積は、ある型を渡る積として表現されるため "pi" と書く。
      対称性のためであって、普段使いは推奨されない。 *)
  Notation "'pi' x .. y , p" := (dprod (fun x => .. (dprod (fun y => p)) ..))
    (at level 200, x binder, right associativity,
      format "'[' 'pi'  '/ ' x .. y ,  '/ ' p ']'")
    : type_scope
    .

  (** [T] の上の道だと特に書きたいときの道の記法。 *)
  Notation "x = y :> T" := (@paths T x y)
    (at level 70, y at next level, no associativity)
    : type_scope
    .

  (** 普通の道の記法。 *)
  Notation "x = y" := (x = y :> _)
    (at level 70, no associativity)
    : type_scope
    .

  (** 関数合成の記法。 *)
  Notation "f 'o' g" := (compose f g)
    (at level 40, left associativity)
    : function_scope
    .

  (** 依存関数合成の記法。 *)
  Notation "f 'oD' g" := (compose_dep f g)
    (at level 40, left associativity)
    : function_scope
    .

  (** 道に関する関数の記法。その多くは圏論における道の可逆圏に由来する。 *)
  Module Path .

    (** 道に対する文脈を設定する。 *)
    Delimit Scope path_scope with path .

    (** 文脈を開く。 *)
    Open Scope path_scope .

    (** 文脈を型と結びつける。 *)
    Bind Scope path_scope with paths .

    (** 恒等道の記法。 *)
    Notation "1" := idpath
      : path_scope
      .

    (** 道の合成の記法。 *)
    Notation "p @ q" := (concat p q)
      (at level 20)
      : path_scope
      .

    (** 道の反転の記法。 *)
    Notation "p ^" := (inverse p)
      (at level 3, format "p '^'")
      : path_scope
      .

    (** 道の輸送の記法。関数の名前が長いため短く書きたいときに役に立つが、
        出力が読みづらくなるため入力時のみに使えるようにする。 *)
    Notation "p # x" := (transport p x)
      (right associativity, at level 65, only parsing)
      : path_scope
      .

  End Path .

End Notation .
