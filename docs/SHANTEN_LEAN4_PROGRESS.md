# シャンテン計算のLean4証明進捗

**文書更新:** 2026-11-16

**実装の確認基準:** R3の自動検証設定に続く、R2の容量付きモデルの段階導入とA/B受入証明（2026-11-16）

この台帳には現在の成果と未解決条件だけを記録する。作業範囲は
[現行計画](./SHANTEN_LEAN4_PLAN.md)、判断の根拠は
[追補レビュー](./MENTSU_HAND_PROGRESS_REVIEW_FOLLOWUP.md) を参照する。
過去の補題別履歴・撤回した計画は [アーカイブ](./archive/README.md) に分離した。
旧コードの除去によって、現在の未解決条件を完了扱いにはしていない。

## 現在地

| 対象 | 状態 | 成果と制約 |
|---|---|---|
| 基礎モデル | 部分完了 | 既存の固定面子数だけの抽象モデルに加え、実牌内容・槓の4枚消費を保持する容量付きモデルを段階導入済み。37種入力との対応は後続。 |
| 形の仕様 | 部分完了 | 3形の完成形・到達関係・形シャンテン仕様を定義済み。共有遷移・経路の4枚制限保存を証明済み。七対子・国士無双の補題もあるが、全体の完成とは扱わない。 |
| 全ターゲットDP | 仕様一致は完了 | 有効カウントと `tileCount hand + 3 * hand.fixedMelds = 13` の下で `mentsuHandTargetMinimumSearch` と `IsShapeShanten` の一致を証明済み。 |
| 牌種順グループ化 | データ層は完了 | 重複度を保つグループ化、残余列の空性、元の選択列との順列性を証明済み。 |
| 与えられた分解のバッチ走査 | 完了 | `MentsuHandBlockDecomposition.exists_tileBatchScan_complete` が分解だけから34牌種順の走査と完了状態を構成する。レビューの東雀頭・12萬ターツ4組も具体例で検査済み。 |
| 一般手牌のブロック探索 | 仕様一致・全域性は完了 | `ValidCounts hand` と `tileCount hand + 3 * hand.fixedMelds = 13` の下で、新しい `generalMentsuHandMinimumSearch` の結果の存在・一意性、探索の被覆性・最小値一致を証明済み。入力に分解は不要。 |
| 総合値・上限 | 部分完了 | 定義・一意性・条件付き上限補題などはある。現在の狭い分解の列挙だけで全体完了とはしない。 |
| 国士無双の最大値 | 有効13枚手で完了 | 仕様値の存在・上界13と、有効な中張牌のみの手牌が13を達成することを証明済み。閉形式との一般的一致・14枚手は対象外。 |
| 容量付き仕様 | 段階導入完了 | R2のA/Bで最短距離2・1、値1・0を証明済み。旧仕様への射影・下界関係と固定面子なしでの仕様同値を証明。容量付き一般探索は後続。 |
| 検証運用 | CI設定・成功確認済み | Go／Lean独立ジョブの成功を利用者が確認。主要23宣言の推移的な `sorryAx` 依存を通常ビルドで拒否する。R2追加分のGitHub上の実行はpush後。 |
| Go適合性 | 未着手 | Go計算器とLean仕様の値一致、共有fixtureは未実装。 |

公開入口は [MentsuHand.lean](../Shanten/MentsuHand.lean)、
[SevenPairs.lean](../Shanten/SevenPairs.lean) と
[ThirteenOrphans.lean](../Shanten/ThirteenOrphans.lean)、
実装の配置と読む順序は[構成表](./SHANTEN_LEAN4_PLAN.md#ファイル構成と読む順序)を参照する。
既存のターゲットDPの仕様一致は、新しいバッチ走査の成果とは別に数える。
手牌消費付きブロック探索は
[Search/BlockSearch.lean](../Shanten/MentsuHand/Search/BlockSearch.lean) に配置し、
公開入口 [Shanten.lean](../Shanten.lean) からimportする。

## レビューR1：共有遷移の有効性保存

[レビューR1](./PROJECT_REVIEW_2026-11-16.md#r1対応結果2026-11-16) に対応し、
[HandStep](../Shanten/Specification.lean) の交換分岐にも終了手の `ValidCounts` を要求した。

- `HandStep.validCounts`：ドロー・交換のいずれも終了手は有効。
- `ReachesHand.validCounts`：有効な開始手からの任意長の経路は有効性を保存する。
  任意の接頭辞にも適用できるため、中間状態も4枚制限を満たす。
- `ReachesCompletion.exists_reachesHand` / `exists_valid_completion`：
  完成経路を共有経路へ接続し、有効な開始手から有効な完成先を得る。
- `exchangeHand_step` は `validCounts_exchangeHand` を再利用する。
  目標到達・七対子の変換補題には開始手の有効性を引き継ぎ、目標への交換には
  目標の牌種別4枚制限を要求する。無効入力にも適用できた旧補題の型は制限したが、
  有効13枚相当手牌に対する一般探索の仕様一致・全域性の前提は維持した。
- [回帰例](../Shanten/MentsuHand/Examples.lean) に有効13枚手「東4・南4・西4・北1」を追加。
  北から東への交換と東5枚への任意長の経路を拒否する。
  東から北への有効な交換と、その逆向きに4枚目の東を引く交換は構成できる。

このR1保存定理の対象は手元牌の4枚制限まで。
固定面子の実牌内容を含む制約は、以下のR2容量付きモデルで別途扱う。

## レビューR2：容量付きモデルの段階導入

[Capacity.lean](../Shanten/Capacity.lean) を公開入口からimportした。
名前空間 `Shanten.Capacity` で既存の抽象仕様と区別する。
固定面子の実牌内容を不変の文脈として持ち、槓は1面子・4枚消費とする。
`ValidHand` は手元牌と固定牌の合算4枚制限を入力・完成先・各遷移に課す。
固定牌だけの超過も拒否し、残余容量の自然数減算で無効入力を隠さない。

- `ValidHand.exchange` / `ReachesHand.validHand`：容量を守る交換・経路の有効性保存。
- `ReachesCompletion.toAbstract`：容量を忘れても同じ距離の旧完成経路を得る。
- `IsShapeShanten.abstract_le`：両仕様で値が存在する場合、旧値は容量付き値の下界。
- `isShapeShanten_nil_iff`：`ValidHand [] hand` の下で、固定面子なしの3形の仕様は旧仕様と同値。
- [受入例](../Shanten/Capacity/Examples.lean) の `inputA_valid` / `inputB_valid`：
  レビューのA/Bはいずれも有効な13枚相当入力。
- `inputA_shanten` / `inputB_shanten`：Aは最短2手・値1、Bは最短1手・値0。
  到達上界だけでなく、これより短い完成経路がないことと値の一意性まで検査した。
- 容量超過のドロー・交換、槓で残余容量が0になる場合、固定牌だけで容量超過する場合の回帰例を追加。

[設計と再利用条件](./SHANTEN_LEAN4_PLAN.md#完了した段階導入容量付きモデルr2) に、
射影・下界関係・固定面子なしでの一致と、既存算術を再利用できる範囲を明記した。
既存の一般探索の計算結果は変更していない。容量付きの一般探索・全域性の接続、
37種の赤5統合前の容量検証とGo契約への対応は後続とする。

## レビューR3：自動検証

[Checksワークフロー](../.github/workflows/checks.yml) を追加した。
Goは `go.mod` 指定のバージョンで `go test ./...` / `go vet ./...` を実行する。
Leanは固定済みツールチェーンと依存manifestを使い、`lake update` せずに
import対象のMathlibキャッシュを取得して `lake build` を実行する。

[ProofChecks.lean](../Shanten/ProofChecks.lean) は公開入口からimportされるため、
ローカルの通常ビルドでも主要23宣言の推移的な `sorryAx` 依存を拒否する。
検査対象はR1保存定理・共有到達・一般探索・バッチ走査・七対子上限・国士最大値に加え、
R2の容量保存・旧仕様との対応・A/B受入証明。
Mathlib標準の `assert_no_sorry` を使用し、既存の `native_decide` 依存は許容する。
通常の警告は一律エラー化しない。新たな主要出口定理は同じ検査一覧に追加する。

R4は **Pending**。利用者側で仕様を整理して返す方針のため、
開発コンテナやGo契約の要求バージョンは変更していない。
R3設定後のCI成功は利用者から確認済みとの報告を受けた。

## モジュール整理

- 旧5,755行の `MentsuHand.lean` は15行の公開入口にし、面子手の実装は
  共通基盤6・`Scan` 5・`Search` 7・検証例1の計19モジュールへ分割した。最大589行。
- `GeneralMentsuHand.lean` の内容は、役割を表す `Search/BlockSearch.lean` と
  `Examples.lean` へ移動した。公開名前空間・定義・定理名は変更していない。
- `6fa7d3c` の2ファイルを基準に、全宣言・属性・証明本文がコメント・空白を除いて
  移動後と一致し、未移動・重複したコードがないことを機械照合した。
- Mathlibキャッシュの取得はサブディレクトリも走査するよう、READMEと両devcontainer設定を
  更新した。JSON構文と、必要な12 importを漏れなく取得対象にすることも検査済み。
- 旧1,665行の [SevenPairs.lean](../Shanten/SevenPairs.lean) は12行の公開入口にし、
  七対子固有の実装は基本定義・カウント・完成形・交換戦略・到達性の8モジュールに分割した。
  最大324行。汎用の不足枚数・交換操作・交換列は
  [Exchange.lean](../Shanten/Exchange.lean) に切り出し、面子手も直接共有する。
- テンパイ目標と完成時カウント、対を残す打牌、未登場牌種、単独牌の存在を表す名前を
  整理した。[改名表](./SHANTEN_LEAN_STRUCTURE.md#改名) の変更以外は公開名を維持する。
  `e7f741a` の92宣言すべてについて、改名後の宣言・命題・証明本文が移動先と一致し、
  未移動・重複した宣言がないことを機械照合した。到達上限などの証明範囲は拡張していない。

## 国士無双：最大シャンテン数13

[ThirteenOrphans.lean](../Shanten/ThirteenOrphans.lean) を公開入口からimportした。
対象は `IsThirteenTileHand` を満たす固定面子なしの有効な13枚手。

- `reaches_thirteenOrphans_completion`：完成形への14手以内の到達を構成する。
- `thirteenOrphansShanten_exists`：すべての対象手牌で仕様値が存在して13以下になる。
- `kokushiWorstCase_isThirteenTileHand`：既存の中張牌13枚の具体例が有効である。
- `kokushiWorstCase_completion_distance_ge_fourteen`：この具体例からどの国士完成形へも
  最低14手が必要である。不足牌数は1手につき最大1しか減らないことを使う。
- `kokushiWorstCase_shapeShanten`：具体例の仕様値が `some 13` となる。
- `thirteenOrphansShanten_maximum`：上界13とその達成をまとめた定理。

面子手にあった汎用の交換・目標到達補題12宣言を共有の
[Exchange.lean](../Shanten/Exchange.lean) へ移動し、完成形への到達と不足数の下界を
形に依存しない形へ一般化した。既存の面子手補題の名前・型は維持した。
`kokushiShanten` と仕様値の一般的一致、14枚手、Go実装は証明したとは扱わない。

## 一般手牌のブロック探索：完成した範囲

対象は34牌種モデルの有効な13枚相当手牌（固定面子があれば手牌は `13 - 3 * fixedMelds` 枚）。
雀頭・面子・ターツの存在は仮定しない。

- 雀頭候補と必要数の面子候補を順に選び、各ブロックに残り手牌から使える牌を割り当て、
  不足牌数を累積する有限探索を実装した。手牌側の部分ブロックは空・1枚・嵌張も許す。
  使われなかった孤立牌は交換時の捨て牌になる。
- `generalMentsuHandAddBlock_stateFor`：各段階で使用枚数が手牌と選択済み完成ブロックの
  枚数の最小値になり、不足数が正確な差分に一致する。牌を二重使用しない。
- `mem_generalMentsuHandStates_iff`：探索状態と、必要面子数・完成後4枚制限を満たす
  全完成形候補との対応を双方向に証明した。分解や探索成功を入力前提にしない。
- `generalMentsuHandDistances_eq`：上の手牌消費付き探索の候補距離集合が、
  既存の全ターゲットDPの候補距離集合と一致することを証明した。
- `generalMentsuHandMinimumSearch_eq_some_iff`：探索結果と `IsShapeShanten` の同値。
- `generalMentsuHandMinimumSearch_exists_unique`：対象手牌すべてで正しい結果が一意に存在する。
- `generalMentsuHandMinimumSearch_optimal`：最小値を実現する実際の探索状態が存在する。

旧 `MentsuHandBlockDecomposition` と旧ブロック探索を無条件に一般化したのではなく、
不足するブロックを表現できる別の状態・遷移を導入した。旧走査との同値や、
通常の面子数・ターツ数だけによる評価式、性能最適化を証明したとは扱わない。
14枚手の打牌選択、固定面子の実牌内容込みの容量検証、Go適合性は今回の定理の対象外。

## 完了済みの中間目標：与えられた分解のバッチ走査

### 1. 順序に依存しない遷移の妥当性

- [x] `MentsuHandChoiceSubmultiset` 等の重複度付き包含から、次の選択後の
  使用牌・面子数・搭子数の上限を導く。
- [x] 同じ途中状態について、搭子履歴と補完牌の4枚制限を導く。

`MentsuHandBlockDecomposition.forwardPath_of_perm` が元の選択列の任意の順列で
コピー制限付き経路を構成する。重複度付き包含を使い、牌種順に並べ替えた列へ
元の順序を要求しない。

### 2. 雀頭を含む経路の構成

- [x] 処理済み列の雀頭使用状況と `state.pair` を対応付ける。
- [x] 雀頭を含む牌種グループについても、分解からコピー制限付き経路を構成する。

雀頭の選択数と経路中の `state.pair` を対応付け、雀頭が後ろに移るグループ化後の列も
構成対象に含めた。

### 3. 分解から34牌種順の全走査を構成

- [x] 任意の `d : MentsuHandBlockDecomposition hand` から、初期状態を出発する
  `mentsuHandTileOrder` 上のバッチ走査を構成する。
- [x] 走査の選択列が `d.blockChoices` の牌種順グループ化であり、
  `final.pair = some d.pair` と `IsMentsuHandBlockSearchComplete hand final` を示す。
- [x] 「東の雀頭と12萬の搭子4組」を持つレビューの有効13枚手を、
  最終状態の完了条件まで通す。

**受入条件:** 入力は手牌とその分解であり、経路・バッチ・探索成功・各遷移の妥当性を
呼び出し側へ要求しない。上の1・2は3の前提を解消するための作業である。
達成済みの出口定理は `MentsuHandBlockDecomposition.exists_tileBatchScan_complete`。
内部で順列から経路、グループ化バッチ、牌種順バッチ走査へ接続し、雀頭と完了条件も返す。

## 残る別課題

- 旧一選択走査とバッチ走査の単純な同値化。
- 既存の狭い分解・走査と、新しい一般ブロック探索との同値化。
- 14枚手、固定面子の実牌内容を持つ入力モデルへの拡張。
- 一般手牌の到達上限、固定面子の牌内容付きモデル、Go移植、枝刈り・メモ化。

後続課題を廃止したのではなく、現在の統合定理の完了条件から分離している。
旧計画の数値上限や実装順序を、そのまま現在の作業へ戻さない。

## 検証記録

- 2026-11-16、国士無双の最大値13：
  `lake build Shanten` 成功（909 jobs）。既存・移動済みコードの警告と
  Mathlib import形式の警告は残る。
  `lake env lean --stdin` で公開入口からの仕様値の存在・上界の利用、
  具体例の `some 13`、13手では和了できないことを検査した。
  最大値・値の存在・具体例の仕様値・共有の到達定理・不足数の下界の5定理に
  `#print axioms` を実行し、依存は `propext`・`Classical.choice`・`Quot.sound` のみで、
  `sorryAx` や `native_decide` の公理への依存がないことを確認した。

- 2026-11-15、`f79ed59`：追補レビューで
  `lake env lean Shanten/MentsuHand.lean` 成功（約21.3秒、警告83件）。
- 同レビューで、任意の分解にグループ化順列定理を適用できることと、
  具体例の重複度保持・残余列の空性をLeanで確認済み。
- 2026-11-16のアーカイブ整理は文書変更のみ。Leanビルドは再実行していない。
- 2026-11-16、旧計画コード除去後：
  `lake env lean Shanten/MentsuHand.lean` 成功（警告64件）、
  `lake build Shanten` 成功（880 jobs）。
- 残した294宣言の命題・証明本文が、コメントと空白を除いて除去前と一致することを確認。
  公開入口をimportする一時Lean検査で、雀頭が後になるグループ化の重複度保持、
  グループ走査からバッチ走査への変換、完了したバッチ走査から仕様値の存在への接続を確認。
  ターゲットDPの仕様一致とバッチ到達性の定理に `sorryAx` がないことも確認した。
- 2026-11-16、分解から牌種順バッチ走査を構成する統合後：
  `lake env lean Shanten/MentsuHand.lean` 成功。新しい具体例では、
  13枚手「11112222萬 東東 9筒 9索 北」と分解「東雀頭、12萬ターツ4組」について、
  `exists_tileBatchScan_complete` が返す選択列・雀頭・完了条件まで検査した。
  続けて `lake build Shanten` も成功（880 jobs）。既存の警告は残る。
- 2026-11-16、一般ブロック探索の追加：
  `lake env lean Shanten/GeneralMentsuHand.lean` 成功（新モジュールの警告なし）。
  13種の么九牌を各1枚持つ手牌について、旧分解が存在しないことと新探索の全域性を検査。
  雀頭・面子とも該当牌がない場合も、使用牌0枚のまま不足数を2・5と累積することを検査。
  固定面子4組・東1枚の手牌の結果が `some 0`、13萬を123萬へ補う不足数が1、
  同じ面子を再選択しても手牌を二重使用せず累積不足数が4になること、
  完成後5枚を要求する候補が4枚制限で排除されることもLeanで検査した。
  `lake build Shanten` 成功（881 jobs）。ビルドには既存と同種のMathlib import形式の
  警告が残る。公開入口からのimportと全域性定理の適用も検査した。
  遷移不変条件・被覆性・距離集合一致・仕様一致・存在一意性・最適状態の6定理について
  `#print axioms` を実行し、依存は `propext`・`Classical.choice`・`Quot.sound` のみで、
  `sorryAx` がないことを確認した。
- 2026-11-16、モジュール分割後：`lake build Shanten` 成功（899 jobs）。
  `Shanten.MentsuHand` だけをimportする検査で、一般手牌の全域性定理の適用と、
  牌種順走査・ターゲットDP・手牌消費付き探索の主要8定理に `sorryAx` がないことを確認。
  旧走査には従来から `tile_mem_mentsuHandTileOrder` の `native_decide` 依存があり、
  今回も変更していない。Mathlib import形式・既存の証明スタイルに関する警告は残る。
- 2026-11-16、七対子の分割・改名後：`lake build Shanten` 成功（908 jobs）。
  `lake env lean --stdin` で `Shanten.SevenPairs` だけをimportし、
  テンパイからの和了定理の適用と改名後のテンパイ目標のカウント補題を検査した。
  分解・最後のドロー・7牌種への到達・6対への到達・保護付き6対への到達の5補題に
  `sorryAx` がないことを `#print axioms` で確認した。
  7牌種への到達には従来の `exists_missing_tile_kind` の `native_decide` 依存が残る。
  他の4補題の依存は `propext`・`Classical.choice`・`Quot.sound` のみ。
  面子手の全モジュールが七対子を直接importしないことも検査した。
  Mathlib import形式・既存の証明スタイルに関する警告は残る。

- 2026-11-16、レビューR1修正後：
  `lake build Shanten.Exchange Shanten.SevenPairs.Reachability` 成功（881 jobs）、
  回帰例を含む `lake build Shanten` 成功（909 jobs）。
  保存定理・共有到達・一般探索の仕様一致／全域性／最適状態・バッチ走査・七対子上限・
  国士最大値の主要14宣言を `lake env lean -j2 --stdin` の `#print axioms` で検査し、
  `sorryAx` 依存なし。新しい保存・完成経路接続の4補題は公理依存もない。
  既存のバッチ走査・七対子の `native_decide` 依存と、既存の警告は残る。
  修正前の基準はレビュー対象コミット `f3f49369dffb45c3ca04f89571471b2c122ee6cc`。

- 2026-11-16、レビューR3設定後：
  Go 1.26.4で `go test ./...` / `go vet ./...` 成功。
  `lake build Shanten.ProofChecks` 成功（909 jobs）、
  公開入口を含む `lake build` 成功（911 jobs）。
  `actionlint` v1.7.12でワークフロー検証成功。
  一時的なLean入力で、`sorry` を持つ定理を経由した別定理への
  `assert_no_sorry` が `contains sorry` エラーで非ゼロ終了することも検査した。
  GitHubホスト上のワークフロー実行はpush後に確認する。既存の警告は残る。
  修正前の基準コミットはR1対応済みの `7f06247`。

- 2026-11-16、レビューR2の段階導入後：
  `lake build Shanten.Capacity` 成功（879 jobs）、
  公開入口・既存証明・主要23宣言の証明穴検査を含む `lake build` 成功（915 jobs）。
  新たな主要9宣言を `#print axioms` で検査し、依存は
  `propext`・`Classical.choice`・`Quot.sound` の範囲のみ。
  `sorryAx`・新規の `native_decide` 依存なし。
  公開入口からA/Bの値1・0の一意性の適用も検査した。
  既存の警告は残る。修正前の基準コミットはR3対応済みの `29235ad`。

## 旧計画コードの除去（2026-11-16）

- 旧一選択走査、牌種位置ごとの遷移・到達関係、skip列と代表牌挿入、
  それらに限定された探索結果ラッパーを削除した。
- 分解の元の順序を要求する接頭辞・部分列ベースの妥当性ラッパー、
  非雀頭限定の経路構成、旧方向の選択列関係と専用補題を削除した。
- 削除した公開宣言は103個。互換ラッパーや無効な証明の代用品は追加していない。
  過去の実装はGit履歴 `225aa29` から参照できる。
- 対象ファイルは7,206行から5,036行へ縮小した。証明の前提や実行可能な探索の値は変更していない。
- ターゲットDPと仕様一致、バッチ・グループ走査、コピー制限付き前向き経路、
  共通の状態・履歴不変条件、順列・重複度付き包含・一般的な部分列単調性は維持した。
- 部分列単調性そのものは廃止した探索方針ではないため、共有の数学的補題として残した。

## 更新ルール

1. 実装変更ごとに、基準コミット・解消した未解決前提・検証コマンドと結果を更新する。
2. 完了したチェック項目は根拠となる定理とともに成果欄へ移す。
3. 経路を仮定する変換と、分解から経路を生成する定理を区別して報告する。
4. 撤回した方針や詳細な過去履歴はアーカイブへ移し、現行チェックリストに残さない。
5. 対象範囲や完了条件を変更するときは [現行計画](./SHANTEN_LEAN4_PLAN.md) も更新する。
