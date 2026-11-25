# Leanシャンテン計算の測定準備

このディレクトリは、容量付きモデルの計算を手牌ごとに実行し、
時間切れや失敗も含めて記録するためのもの。性能の基準値や目標を定めたものではない。
計算の正しさは既存の一般定理と回帰例で保証・検査し、測定値をその代わりにしない。

## 対象と入力

`ShantenBench.lean` は既存の `Capacity` 計算を呼び出す。
全ケースは実行時に既存の13枚相当・14枚相当の有効性述語で検査し、
無効なら計算せず失敗する。次の分類には重なりがある。

| ケース | 内容 |
|---|---|
| `closed-seven-ready-13` | 固定面子なし、七対子テンパイ |
| `closed-seven-quads-13` | 固定面子なし、七対子の四枚使い |
| `closed-seven-complete-14` | 固定面子なし、七対子完成 |
| `closed-orphans-ready-13` | 固定面子なし、国士テンパイ |
| `closed-orphans-far-13` | 固定面子なし、国士シャンテン13 |
| `closed-orphans-complete-14` | 固定面子なし、国士完成 |
| `closed-mentsu-complete-14` | 固定面子なし、面子手完成 |
| `kan-one-13`, `kan-one-14` | 東の槓1組、13・14枚相当 |
| `kan-two-13`, `kan-two-14` | 東の槓と南の刻子、13・14枚相当 |
| `kan-three-13`, `kan-three-14` | 上記に123萬の順子を追加、13・14枚相当 |
| `blocked-four-13`, `ready-four-13` | 固定牌の容量が異なる既存のA/B例 |
| `complete-four-14`, `blocked-four-14` | 面子手完成と、容量により値1となる未完成手 |
| `kan-four-13` | 槓を含む固定面子4組 |

具体的な牌は定義を正とする。A/Bと14枚相当の値などは
[既存の回帰例](../Shanten/Capacity/Examples.lean) で確認できる。
`seven`・`orphans` は固定面子があれば `none` を返す。
面子手の未完成手に対する値を、特殊形の値と混同しない。

## 実行

リポジトリルートで実行する。Leanと依存関係は既存のLake設定を使用し、
`lake update` やキャッシュ削除は行わない。Linux、Python 3、Leanが必要。
`LEAN_NUM_THREADS` は測定時に固定する。次の制限値は操作例であり、性能目標ではない。

```sh
export LEAN_NUM_THREADS=2
lake env lean --run benchmarks/ShantenBench.lean list
python3 benchmarks/measure.py --timeout 120 --max-memory-mib 16384 -- \
  lake env lean --run benchmarks/ShantenBench.lean mentsu ready-four-13
```

`list` は全ケース名、固定面子数、手元牌数と有効性を表示し、
いずれかが無効なら非ゼロ終了する。`check` は全入力の有効性と、既存の証明済み回帰例の
一部の結果を実際に計算して検査する。操作は `mentsu`、`overall`、`seven`、
`orphans` のいずれか。ケースを1つずつ、同じ設定で反復し、出力を保存する。
計算が重い可能性があるため、共有環境では並列実行せず、資源状況を確認する。
未知の操作やケース、無効な入力は明示的に失敗する。

計算時間とビルド時間を分けるため、ビルドは別コマンドとして測定する。
これは既存のビルド成果物を利用した**増分ビルド**であり、クリーンビルドではない。

```sh
python3 benchmarks/measure.py --timeout 600 --max-memory-mib 16384 -- lake build Shanten
```

## 出力の意味と制限

- Lean側の `calculation_ns` は入力検査後、選択した計算の開始から結果を得るまでの
  単調時計による経過時間。Leanの読み込み・ソース処理と結果の表示は含まない。
- `measure.py` のJSONはコマンド全体の経過秒数、Linux `wait4` の最大RSS（KiB）、
  終了コード、制限値と時間切れの有無を含む。コマンドの標準出力・標準エラーもそのまま表示する。
  時間切れはプロセスグループを停止し、記録したうえで終了コード124を返す。
  その他の失敗も成功として扱わない。
- 最大RSSは `wait4` が返す単一プロセスと回収された子の最大値であり、
  並列に動くプロセス群のRSS合計のピークではない。Leanの起動・読込みも含み、
  計算部分だけのメモリではない。`lake build` のメモリ使用量全体とも解釈しない。
- メモリ制限はLinuxの `RLIMIT_AS` による**各プロセスの仮想アドレス空間**の制限で、
  RSSやプロセス群のメモリ合計の上限ではない。Leanは大きなファイルをマップするため、
  RSSより大きな制限が必要になる場合がある。制限による失敗も失敗として記録する。
- `lean --run` による実行を測っており、ネイティブ実行ファイルや将来の実装の速度を
  示すものではない。比較対象では実行方式を揃える。

測定記録には上記の全出力に加え、日時、各リポジトリのコミットと作業ツリーの状態、
Lean・Mathlibの版、OS・CPU・メモリ、並列度、キャッシュ状態、実行順・反復回数、
時間・メモリ制限を残す。時間切れや資源不足も除外せず記録する。
異なる設定や負荷の測定値を同一条件の比較として扱わない。

測定器自体の検査は次で実行できる。

```sh
python3 -m unittest discover -s benchmarks -p 'test_*.py'
lake env lean --run benchmarks/ShantenBench.lean check
```
