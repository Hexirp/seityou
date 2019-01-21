####
Wiki
####

このファイルは、このライブラリに関する事柄についての wiki である。

***************************
HoTT (Homotopy Type Theory)
***************************

Homotopy Type Theory とは、型を空間として要素を点として解釈することを基本的な
アイデアに据えた型理論である。

* https://en.wikipedia.org/wiki/Homotopy_type_theory - 英語版 Wikipedia の記事
* http://www.kurims.kyoto-u.ac.jp/~uemura/files/hott-intro-ja.pdf - 上村 太一
  氏による PDF で、ただ一つのアカデミアな出元を持つ日本語の情報
* https://gist.github.com/qnighy/bfb53e54d3ffcbbd0e84 - qnighy 氏による HoTT に
  関する覚え書き

このライブラリは Homotopy Type Theory の Coq での形式化を含む。

******************
Coq 標準ライブラリ
******************

Coq にデフォルトでバンドルされているライブラリである。このライブラリは、これを
参考にした部分も含むが、大部分が異なる。

* https://coq.inria.fr/distrib/current/stdlib/

*********************
HoTT ライブラリ (Coq)
*********************

HoTT を Coq で形式化したライブラリである。このライブラリの HoTT に関わる部分は
コメントも含めて、これの移し替えである。

* https://github.com/HoTT/HoTT/

****
訳語
****

訳語は好き放題に作っているので、このライブラリが正しいと勘違いしないように。

* notation - 記法
* tactic - 戦略
* scope - 文脈
* groupoid - 可逆圏
* equality type - 等式型
* equivalent - 等価
* truncation - 切捨
* homotopy - 相同
* fiber - 維

****************
コーディング規約
****************

このライブラリのコーディング規約は以下のとおりである。

indent
 スペース 1 個が基本であるが臨機応変にやる。

tactic
 refine, exact, revert, change, pose, instantiant しか使わない。exact を使える
 ところでは exact を使う。必ず bullet を使う。

module
 名前は省略無しの名詞にする。Export を使わない。記法は内部モジュールに分離
 する。

****
主義
****

出来るだけ単純に。例えば、できるだけプリミティブな実装をする。例えば、甲という
概念があり、それが乙から甲' として実装される場合、甲を甲' で置き換える
のではなく、甲と甲' が同じものであることを示すのに留める。

****
開発
****

Coq IDE を使う場合、coqide.sh から起動すること。カレントディレクトリに関わる
問題のため。build.sh によってビルドを行う。環境依存のコードだが、めんどくさい
のでそのまま。build-core.sh はしっかりとした所だけビルドする。

**********
インポート
**********

``-R Seityou`` オプションを指定しているため Coq 標準ライブラリからインポート
する時は ``From Coq Require ...`` としなければならない。

************
ホモトピー論
************

``f`` と ``g`` のホモトピーは ``forall x, f x = g x`` と表される。
