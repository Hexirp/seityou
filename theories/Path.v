Require Export Homotopy.


Declare ML Module "ltac_plugin".

Set Default Proof Mode "Classic".


(** ** 名前付け

    私たちには、それを参照することなく定理に名前を付けることが出来る、
    良い名前付け規則が必要です。名前は定理の構造を表すはずですが、時には
    曖昧であり、その場合は、何が行われているのかを知る必要があります。

    私たちは、下のような原理に従います。

    * 長い名前をつけることを恐れない。
    * それが頻繁に使われるのならば、短い名前を付けることを恐れない。
    * アンダースコアを使う。
    * 定理や補題の名前は小文字を使う。
    * 記録体 (Record) やそのほかは大文字でも小文字でもよい。
    
    結合に関する定理は [concat_XXX] と書かれ、その部分 [XXX] は、その等式の
    左辺の式がどのような形をしているか教えてくれる。あなたは、右辺を推測する
    必要があります。この末尾につけられる注釈は、このような記号を使って
    書かれます。

    * [1] は、ある恒等道 (identity path) を表す。
    * [p] は、ある道を表す。
    * [V] は、ある反転された道を表す。
    * [A] は、適用 [ap] を表す。
    * [M] は、ある移項されるものを表す。
    * [x] は、ある点を表し、それは [transport p x] といった道ではない全般
      である。
    * [2] は、2 次元の道に関するということを表す。
    * [3] は、3 次元の道に関するということを表す。以下同様……。

    結合性はアンダースコアにより指定される。これらは左辺がどういうものに
    なるかの例である。

    * [concat_1p] は [concat idpath p] 。
    * [concat_Vp] は [concat (inverse p) p] 。
    * [concat_p_pp] は [concat p (concat q r)] 。 *)


(** [p] を反転して [q] を合成する。

    [forall y, x = y] のようなパターンの時に便利。 *)
Definition coninv
  {A : Type} {x y z : A}
  (p : paths y x) (q : paths y z) : paths x z
  := concat (inverse p) q .

Definition coninv_pp
  {A : Type} {x y : A}
  (p : paths x y) : paths (coninv p p) idpath
  := paths_elim (P := fun y' p' => paths (coninv p' p') idpath) idpath p .
