# seityou

ぐんぐん成長していくライブラリ。

学習のために Coq と HoTT の標準ライブラリを車輪の再発明する。ポリシーは一つ、
出来るだけ単純に。例えば、できるだけプリミティブな実装をする。例えば、甲という
概念があり、それが乙から甲' として実装される場合、甲を甲' で置き換える
のではなく、甲と甲' が同じものであることを示すのに留める。

## 開発

Coq IDE を使う場合、[coqide.sh](./coqide.sh) から起動すること。
`Add LoadPath` によるカレントディレクトリ関係の問題のため。
[build.sh](./build.sh) によってビルドを行う。環境依存のコードだが、
めんどくさいのでそのまま。

## 訳語

* path - 道
* dependent path - 依存道
* contraction - 可縮
* truncation - 縮小
* homotopy - ホモトピー、相同
* fiber - ファイバー、繊維
* pointwise path - 点ごとの道
* equivalence - 等価

### 等しさ

* 等しい
* 同値である
* 等値である
* 等価である
* 相同である
* 相似である
* 同型である
* 同一である
* 同相である
* 同位である
* 等一である
* 同価である
* 等位である

* identity
* equality
* equivalence
* isomorphism
* homology
* homotopy
