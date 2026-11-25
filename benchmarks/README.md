# Leanシャンテン計算の測定準備

このディレクトリは、容量付きモデルの計算を手牌ごとに実行し、
時間切れや失敗も含めて記録するためのもの。利用想定と性能目標は
[現行計画](../docs/project/SHANTEN_LEAN4_PLAN.md#利用想定と性能目標)を参照する。
既存計算は一般定理と回帰例で保証・検査し、測定値をその代わりにしない。
実験的な色別DP・全牌種DP・枝刈り付き色別DPとその増分版は回帰検査を行うが、
一般の仕様一致は未証明である。
旧方式の初回測定の条件と集計は[性能測定記録](../docs/project/SHANTEN_LEAN4_PERFORMANCE.md#性能測定の初回結果2026-11-25)、
各実行の出力は[生データ](./baseline-2026-11-25.jsonl) を参照する。
旧方式の時間切れには起動時間が含まれるため、計算時間の下限や新方式との比較に使わない。
新方式の100回反復による結果は[性能測定記録](../docs/project/SHANTEN_LEAN4_PERFORMANCE.md#100回反復による測定2026-11-25)、
各実行の出力は[生データ](./baseline-2026-11-25-repeat100.jsonl)を参照する。
色別DPと基準探索の比較は[測定記録](../docs/project/SHANTEN_LEAN4_PERFORMANCE.md#色別dpの実験的実装と測定2026-11-25)と
[生データ](./suit-dp-2026-11-25.jsonl)を参照する。
全牌種DPと色別DPの比較は[測定記録](../docs/project/SHANTEN_LEAN4_PERFORMANCE.md#全牌種dpbと色別dpaの比較2026-11-25)と
[生データ](./tile-dp-2026-11-25.jsonl)を参照する。
枝刈り付き色別DPとの比較は[測定記録](../docs/project/SHANTEN_LEAN4_PERFORMANCE.md#色別dpと上限下界による枝刈りの組合せ2026-11-25)と
[生データ](./pruned-suit-2026-11-25.jsonl)を参照する。

## 対象と入力

`ShantenBench.lean` は既存の `Capacity` 計算と実験的な色別DPを呼び出す。
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
| `repeated-sequences-13`, `repeated-sequences-14` | 同じ123萬を4組使うテンパイ・完成 |
| `two-fixed-sequences-13`, `two-fixed-sequences-14` | 槓を含む固定面子2組と順子、テンパイ・完成 |
| `suit-boundary-13`, `pin-sou-boundary-13`, `sou-honor-boundary-13` | 色・字牌の境界をまたいだ順子を排除 |
| `suit-end-sequence-13` | 色の末尾789の順子 |

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
lake build Shanten.Experimental.TileDP Shanten.Experimental.IncrementalSuitDP
lake env lean --run benchmarks/ShantenBench.lean list
python3 benchmarks/measure_calculation.py \
  --startup-timeout 60 --calculation-timeout 120 --max-memory-mib 16384 -- \
  lake env lean --run benchmarks/ShantenBench.lean controlled mentsu ready-four-13 100
```

`list` は全ケース名、固定面子数、手元牌数と有効性を表示し、
いずれかが無効なら非ゼロ終了する。`check` は全入力の有効性と、既存の証明済み回帰例の
一部の結果を実際に計算して検査し、固定面子3・4組のケースは基準探索と両DPを比較する。
全ケースで両DPと枝刈り付き色別DP・増分版を比較する。遷移は共通の設計に基づき、
互いの一致は独立した正当性検証ではない。
`mentsu`・`overall` は既存探索、`suit-dp` は実験的な面子手DP、
`suit-overall` はDPと既存の七対子・国士無双計算の最小値を返す。
`tile-dp` は全牌種を一体で走査する実験的な面子手DP、
`tile-overall` はその結果と既存の特殊形計算の最小値を返す。
`pruned-suit` は不足枚数の上限と残りの手元牌による下界で枝刈りする色別DP、
`pruned-overall` はその結果と既存の特殊形計算の最小値を返す。
`incremental-suit` は局所探索の保留候補を上限引き上げ時に再利用する実験版、
`incremental-overall` はその結果と既存の特殊形計算の最小値を返す。
`seven`・`orphans` は既存の特殊形計算。最後の数値は同一ケースの計算回数で、省略時は1回。
短時間の計算は100回の合計を測って1回あたりに換算することを基本とし、
ケースを1つずつ同じ設定で測定して出力を保存する。
計算が重い可能性があるため、共有環境では並列実行せず、資源状況を確認する。
未知の操作やケース、無効な入力、0回や不正な回数は明示的に失敗する。

`controlled` モードはLeanの起動と入力検査の後に `SHANTEN_READY` を出力して待機する。
測定器はこの通知を受け取って `RUN` を送り、その時点から計算用の制限時間を監視する。
Leanは指示を受け取った後に計算の開始・終了時刻を測り、結果を通知する。
起動の時間切れ、計算の時間切れ、結果通知後の終了時間切れ、実行失敗は別々に記録する。

計算時間とビルド時間を分けるため、ビルドは別コマンドとして測定する。
これは既存のビルド成果物を利用した**増分ビルド**であり、クリーンビルドではない。

```sh
python3 benchmarks/measure.py --timeout 600 --max-memory-mib 16384 -- lake build Shanten
```

## 出力の意味と制限

- Lean側の `calculation_ns` は入力検査後、選択した計算の開始から結果を得るまでの
  単調時計による**全反復の合計**経過時間。Leanの読み込み・ソース処理と結果の表示は
  含まない。反復ループ、毎回の入力参照と結果の一致検査は含む。
- `iterations` は計算回数、`calculation_ns_per_iteration` は合計を回数で割った値。
  全反復が完了し、結果が一致した場合のみ得られる。同一入力の反復平均であり、
  手牌の分布に基づく牌譜全体の平均とは区別する。
- `measure_calculation.py` の `startup_elapsed_seconds` はプロセス起動から
  準備完了通知まで、`calculation_wall_seconds` は開始指示から結果通知までの時間。
  後者にはプロセス間通信・結果通知の遅延が含まれるため、計算自体の時間としては
  `calculation_ns` を使う。計算の時間切れは後者に基づく近似的な制限であり、
  通信やスケジューリングの遅延を含む。時間制限は1回ごとではなく全反復に対するもの。
  計算中に時間切れになった場合、完了回数と `calculation_ns` は得られない。
  結果通知を受け取った後に時間超過と判定した場合を含め、時間切れ時は平均を算出しない。
  重いケースは回数を減らした測定も別途記録し、100回の結果と混同しない。
- `measure.py` はビルドなどコマンド全体を測るための別の測定器で、計算の制限時間には使わない。
  そのJSONはコマンド全体の経過秒数、Linux `wait4` の最大RSS（KiB）、
  終了コード、制限値と時間切れの有無を含む。コマンドの標準出力・標準エラーもそのまま表示する。
  どちらの測定器も時間切れにはプロセスグループを停止し、終了コード124を返す。
  その他の失敗も成功として扱わない。
- 最大RSSは `wait4` が返す単一プロセスと回収された子の最大値であり、
  並列に動くプロセス群のRSS合計のピークではない。Leanの起動・読込みも含み、
  計算部分だけのメモリではない。時間切れ時には子を回収できず過小になることもある。
  `lake build` のメモリ使用量全体とも解釈しない。
- メモリ制限はLinuxの `RLIMIT_AS` による**各プロセスの仮想アドレス空間**の制限で、
  RSSやプロセス群のメモリ合計の上限ではない。Leanは大きなファイルをマップするため、
  RSSより大きな制限が必要になる場合がある。制限による失敗も失敗として記録する。
- `lean --run` による実行を測っており、ネイティブ実行ファイルや将来の実装の速度を
  示すものではない。比較対象では実行方式を揃える。

測定記録には上記の全出力に加え、日時、各リポジトリのコミットと作業ツリーの状態、
Lean・Mathlibの版、OS・CPU・メモリ、並列度、キャッシュ状態、実行順・反復回数、
時間・メモリ制限を残す。時間切れや資源不足も除外せず記録する。
異なる設定や負荷の測定値を同一条件の比較として扱わない。
特に旧方式の時間切れと新方式の計算時間切れは区別する。

測定器自体の検査は次で実行できる。

```sh
python3 -m unittest discover -s benchmarks -p 'test_*.py'
lake env lean --run benchmarks/ShantenBench.lean check
lake env lean --run benchmarks/SuitDPChecks.lean
```
