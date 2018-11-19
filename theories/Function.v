(** ** Function - Basic functions

    標準的な関数を記述する。 *)


Require Export Basis.


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
