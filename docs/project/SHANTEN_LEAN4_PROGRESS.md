# シャンテン計算のLean4証明進捗

**文書更新:** 2026-11-25

**実装の確認基準:** Lean側の37種容量検証・正規化と容量付き34種モデルへの接続（2026-11-16）

この台帳には現在の成果と未解決条件だけを記録する。作業範囲は
[現行計画](SHANTEN_LEAN4_PLAN.md)、判断の根拠は
[追補レビュー](MENTSU_HAND_PROGRESS_REVIEW_FOLLOWUP.md) を参照する。
検証履歴は[検証記録](SHANTEN_LEAN4_VERIFICATION.md)、
過去の補題別履歴・撤回した計画は [アーカイブ](archive/README.md) に分離した。
旧コードの除去によって、現在の未解決条件を完了扱いにはしていない。

## 現在地

| 対象 | 状態 | 成果と制約 |
|---|---|---|
| 基礎モデル | Lean入力層まで接続済み | 容量付き34種モデルに加え、符号付き37種入力の統合前容量検証・正規化を追加し、有効入力からの接続を証明済み。Go実装は保留。 |
| 形の仕様 | 総合計算まで接続済み | 3形の完成形・到達関係・形シャンテン仕様を定義し、有効13・14枚相当入力で形ごと・総合の計算と仕様の一致を証明済み。Go対応は未完了。 |
| 全ターゲットDP | 仕様一致は完了 | 有効カウントと `tileCount hand + 3 * hand.fixedMelds = 13` の下で `mentsuHandTargetMinimumSearch` と `IsShapeShanten` の一致を証明済み。 |
| 牌種順グループ化 | データ層は完了 | 重複度を保つグループ化、残余列の空性、元の選択列との順列性を証明済み。 |
| 与えられた分解のバッチ走査 | 完了 | `MentsuHandBlockDecomposition.exists_tileBatchScan_complete` が分解だけから34牌種順の走査と完了状態を構成する。レビューの東雀頭・12萬ターツ4組も具体例で検査済み。 |
| 抽象版の一般ブロック探索 | 仕様一致・全域性は完了 | `ValidCounts hand` と `tileCount hand + 3 * hand.fixedMelds = 13` の下で、`Shanten.generalMentsuHandMinimumSearch` の存在一意性・被覆性・最小値一致を証明済み。容量付き版の列挙・消費部品としても再利用する。 |
| 総合値 | 13・14枚相当で仕様一致・全域性完了 | 適用可能な3形の達成最小値を仕様とし、計算結果との一致・存在一意性・下界−1・完成との同値・固定面子時の帰着を証明済み。追加の一般数値上限は後続。 |
| 国士無双の最大値 | 有効13枚手で完了 | 仕様値の存在・上界13と、有効な中張牌のみの手牌が13を達成することを証明済み。閉形式の13・14枚手との一般的一致は特殊形の行を参照。 |
| 容量付き仕様 | 段階導入完了 | R2のA/Bで最短距離2・1、値1・0を証明済み。旧仕様への射影・下界関係と固定面子なしでの仕様同値を証明。 |
| 容量付き一般探索 | 13・14枚相当で仕様一致・全域性完了 | `Capacity.generalMentsuHandMinimumSearch fixed hand` は固定牌込み容量を守る全候補を探索する。任意の有効13・14枚相当入力で結果の存在一意性・仕様一致・最適状態を証明済み。 |
| 色別DP高速版 | 実験的実装 | [SuitDP.lean](../../Shanten/Experimental/SuitDP.lean)に実装。局所列挙・具体例・基準探索との比較は検査するが、仕様一致の一般証明と公開入口への接続は未完了。 |
| 全牌種DP高速版 | 実験的実装 | [TileDP.lean](../../Shanten/Experimental/TileDP.lean)に実装。色別DPと遷移を共有し、色境界を含む具体例で比較するが、仕様一致の一般証明と公開入口への接続は未完了。 |
| 枝刈り付き色別DP | 実験的実装 | [PrunedSuitDP.lean](../../Shanten/Experimental/PrunedSuitDP.lean)に実装。上限・下界を用い、色別DPとの具体例比較を行ったが、枝刈りの安全性・仕様一致の一般証明と公開入口への接続は未完了。 |
| 枝刈り付き色別DPの増分版 | 実験的実装 | [IncrementalSuitDP.lean](../../Shanten/Experimental/IncrementalSuitDP.lean)に実装。上限引き上げ時に局所探索を再利用するが、再利用の正当性・仕様一致の一般証明と公開入口への接続は未完了。 |
| 14枚相当の打牌選択 | 面子手で完了 | 完成値−1と、未完成手の打牌後13枚相当最小値との一致を証明。最適打牌の全列挙・合法性・非空性を保証する。 |
| 特殊形の一般計算 | 13・14枚手で仕様一致完了 | 七対子・国士無双の閉形式を最短完成距離から証明。容量付き仕様と一致し、固定面子があれば暗槓も含め適用不可として `none` を返す。 |
| 37種入力 | Lean側で検証・正規化完了 | 非負性・統合前物理容量・面子構造・枚数を検証し、容量付き13・14枚相当入力へ接続。受理条件の同値と、赤の割当て変更に対する正規化結果・総合値の不変性を証明済み。 |
| 検証運用 | CI設定・成功確認済み | Go／Lean独立ジョブの成功を利用者が確認。主要87宣言の推移的な `sorryAx` 依存を通常ビルドで拒否する。今回追加分のGitHub上の実行はpush後。 |
| Go適合性 | 保留 | 利用者の別計画を先行し、現段階では実装しない。Go計算器とLean仕様の値一致、共有fixtureは未実装。 |

性能測定の結果は[性能測定記録](SHANTEN_LEAN4_PERFORMANCE.md)、
実行方法は[測定手順](../../benchmarks/README.md)に分離した。
起動を除いた100回反復の測定を実施したが、一部は計算時間切れで完了時間が未測定。
色別DPの試験測定は代表22ケースで完了したが、固定面子0〜3組の例は1msを超えた。
全牌種DPも26ケースで測定し、固定面子0〜3組の例は1msを超えた。詳細は性能測定記録を参照。
枝刈り付き色別DPは近い手で改善する例がある一方、遠い手では大幅に悪化した。
その増分版は遠い手での悪化を緩和する一方、近い手で遅くなる例があった。
追加の性能改善実験は実牌譜データで評価できるまで保留し、色ごとのプロセス内キャッシュと
事前注入の候補を[高速化方針](SHANTEN_LEAN4_ALGORITHM_DESIGN.md#保留中のキャッシュ案)に記録した。
性能目標の達成と実験版の一般証明は引き続き未確認。

公開入口は [MentsuHand.lean](../../Shanten/MentsuHand.lean)、
[SevenPairs.lean](../../Shanten/SevenPairs.lean) と
[ThirteenOrphans.lean](../../Shanten/ThirteenOrphans.lean)、
特殊形の一般式は [SevenPairsAndThirteenOrphans.lean](../../Shanten/SevenPairsAndThirteenOrphans.lean)、
実装の配置と読む順序は[構成表](SHANTEN_LEAN4_PLAN.md#ファイル構成と読む順序)を参照する。
既存のターゲットDPの仕様一致は、新しいバッチ走査の成果とは別に数える。
手牌消費付きブロック探索は
[Search/BlockSearch.lean](../../Shanten/MentsuHand/Search/BlockSearch.lean) に配置し、
公開入口 [Shanten.lean](../../Shanten.lean) からimportする。

## レビューR1：共有遷移の有効性保存

[レビューR1](PROJECT_REVIEW_2026-11-16.md#r1対応結果2026-11-16) に対応し、
[HandStep](../../Shanten/Specification.lean) の交換分岐にも終了手の `ValidCounts` を要求した。

- `HandStep.validCounts`：ドロー・交換のいずれも終了手は有効。
- `ReachesHand.validCounts`：有効な開始手からの任意長の経路は有効性を保存する。
  任意の接頭辞にも適用できるため、中間状態も4枚制限を満たす。
- `ReachesCompletion.exists_reachesHand` / `exists_valid_completion`：
  完成経路を共有経路へ接続し、有効な開始手から有効な完成先を得る。
- `exchangeHand_step` は `validCounts_exchangeHand` を再利用する。
  目標到達・七対子の変換補題には開始手の有効性を引き継ぎ、目標への交換には
  目標の牌種別4枚制限を要求する。無効入力にも適用できた旧補題の型は制限したが、
  有効13枚相当手牌に対する一般探索の仕様一致・全域性の前提は維持した。
- [回帰例](../../Shanten/MentsuHand/Examples.lean) に有効13枚手「東4・南4・西4・北1」を追加。
  北から東への交換と東5枚への任意長の経路を拒否する。
  東から北への有効な交換と、その逆向きに4枚目の東を引く交換は構成できる。

このR1保存定理の対象は手元牌の4枚制限まで。
固定面子の実牌内容を含む制約は、以下のR2容量付きモデルで別途扱う。

## レビューR2：容量付きモデルの段階導入

[Capacity.lean](../../Shanten/Capacity.lean) を公開入口からimportした。
名前空間 `Shanten.Capacity` で既存の抽象仕様と区別する。
固定面子の実牌内容を不変の文脈として持ち、槓は1面子・4枚消費とする。
`ValidHand` は手元牌と固定牌の合算4枚制限を入力・完成先・各遷移に課す。
固定牌だけの超過も拒否し、残余容量の自然数減算で無効入力を隠さない。

- `ValidHand.exchange` / `ReachesHand.validHand`：容量を守る交換・経路の有効性保存。
- `ReachesCompletion.toAbstract`：容量を忘れても同じ距離の旧完成経路を得る。
- `IsShapeShanten.abstract_le`：両仕様で値が存在する場合、旧値は容量付き値の下界。
- `isShapeShanten_nil_iff`：`ValidHand [] hand` の下で、固定面子なしの3形の仕様は旧仕様と同値。
- [受入例](../../Shanten/Capacity/Examples.lean) の `inputA_valid` / `inputB_valid`：
  レビューのA/Bはいずれも有効な13枚相当入力。
- `inputA_shanten` / `inputB_shanten`：Aは最短2手・値1、Bは最短1手・値0。
  到達上界だけでなく、これより短い完成経路がないことと値の一意性まで検査した。
- 容量超過のドロー・交換、槓で残余容量が0になる場合、固定牌だけで容量超過する場合の回帰例を追加。

[設計と再利用条件](SHANTEN_LEAN4_PLAN.md#完了した段階導入容量付きモデルr2) に、
射影・下界関係・固定面子なしでの一致と、既存算術を再利用できる範囲を明記した。
抽象版の一般探索の計算結果は変更していない。
容量付きの一般探索への接続は以下の順序4冒頭で完了した。
37種の赤5統合前の容量検証は以下で接続した。Go実装・適合性は利用者の別計画待ちとする。

## 順序4の冒頭：容量付き一般探索（13枚相当）

既存のブロック列挙・手牌消費を再利用し、
[Search.lean](../../Shanten/Capacity/Search.lean) で固定牌込みの完成容量を満たす候補だけを残す。
公開関数は `Capacity.generalMentsuHandMinimumSearch fixed hand`。
旧関数の結果を補正する方式ではなく、容量を満たす候補集合から最小値を取り直す。

- `mem_generalMentsuHandStates_iff`：容量を満たす全完成形候補の被覆性・健全性。
- `generalMentsuHandState_reaches`：各候補まで不足枚数ちょうどで到達する容量付き経路を構成。
- `exists_state_of_reachesCompletion`：任意の完成経路に対する不足枚数の下界。
- [Totality.lean](../../Shanten/Capacity/Totality.lean) の `exists_complete_target`：
  固定面子が占有しない字牌から必要な刻子・雀頭を構成し、有効目標の存在を入力前提に残さない。
- `generalMentsuHandMinimumSearch_eq_some_iff` /
  `generalMentsuHandMinimumSearch_exists_unique` /
  `generalMentsuHandMinimumSearch_optimal`：
  `IsThirteenTileEquivalentHand fixed hand` から仕様一致・存在一意性・最適状態を得る。
- `generalMentsuHandMinimumSearch_nil`：固定面子なしの対象入力で抽象版と計算結果が一致する。
- `inputA_search` / `inputB_search`：実際の探索を `decide` で実行し、`some 1` / `some 0` を検査。
  槓で東の残余容量が0でも、別種の雀頭で完成できる計算例も追加した。

共有の [Exchange.lean](../../Shanten/Exchange.lean) に
目標方向の算術的交換列 `ReachesTargetExchange` を抽出した。
同じ不足枚数の帰納構成を、旧経路・容量付き経路へそれぞれ有効性条件付きで変換する。
旧 `reachesHand_targetHand_of_equal_sum` の型・保証は維持した。

13枚相当の接続に続き、以下の14枚相当の面子手も完了した。
特殊形の一般計算・総合値・Lean側の37種入力も以下で接続した。Go対応は保留とする。

## 順序4：14枚相当と最適打牌（面子手）

[Fourteen.lean](../../Shanten/Capacity/Fourteen.lean) で、
`IsFourteenTileEquivalentHand fixed hand` を満たす任意の手牌について、
13枚相当と同じ一般探索の仕様一致・存在一意性・最適状態を証明した。
出口定理は `generalMentsuHandMinimumSearch_eq_some_iff_of_fourteen` /
`generalMentsuHandMinimumSearch_exists_unique_of_fourteen` /
`generalMentsuHandMinimumSearch_optimal_of_fourteen`。
完成目標と手牌の枚数が等しい場合の容量付き交換列を再利用し、
13枚相当向けの既存定理の型・保証は維持した。

[Discard.lean](../../Shanten/Capacity/Discard.lean) は手元牌の合法な打牌を列挙する。
固定面子は変更せず、持っている牌を1枚捨てると有効な13枚相当入力になる。

- `discardSearchResults`：各合法打牌と13枚相当探索結果の組。
- `minimumDiscardSearch`：それらの最小値。
- `generalMentsuHandMinimumSearch_eq_minimumDiscardSearch`：
  **未完成の**有効14枚相当入力では、元の探索値が打牌後の最小値と一致する。
- `optimalDiscards`：最小値を達成する全打牌種。
  `mem_optimalDiscards_iff` と `optimalDiscards_nonempty` により、
  未完成の有効14枚相当入力では合法性・最適性・候補の存在を保証する。
- `generalMentsuHandMinimumSearch_eq_neg_one_iff`：
  完成形と探索値−1が同値。完成済みの場合は打牌後最小値とは区別し、先に完成判定する。

回帰例では、固定面子4組と手元の東1・白1について、
Aは最適打牌が東のみ、Bは東・白の双方となることを実計算で検査した。
値1の未完成手、完成値−1と打牌後値0の違い、持っていない牌の除外、
槓を含む14枚相当完成形も検査した。この打牌選択の保証は面子手が対象であり、
特殊形の一般計算と総合値は以下で別途接続した。

## 順序4：七対子・国士無双の一般計算

[SevenPairsAndThirteenOrphans.lean](../../Shanten/SevenPairsAndThirteenOrphans.lean) で、固定面子なし・4枚制限を満たす
任意の13枚手または14枚手について、計算可能な閉形式の最短完成距離仕様との一致を証明した。

- `sevenPairsShanten_isShapeShanten`：
  `6 - pairCount hand + (7 - distinctTileCount hand)` が仕様値となる。
  最後の減算は自然数。四枚使いも1対種として数え、7牌種未満なら不足牌種の分も加算する。
  保持できる対種・登場種の数と不足枚数の等式から下界を証明し、それを達成する7対目標を構成する。
- `kokushiShanten_isShapeShanten`：
  既存の `kokushiShanten` が仕様値となる。対に数えるのは么九牌だけ。
  么九牌の対があればその牌を雀頭に選び、なければ任意の么九牌を選ぶことで最適目標を得る。
- 上限用の既存証明を仮定せず、共有の不足数下界と、
  ドロー／同枚数交換の到達証明を使って閉形式の最小性まで証明した。

[Capacity/SevenPairsAndThirteenOrphans.lean](../../Shanten/Capacity/SevenPairsAndThirteenOrphans.lean) は
`sevenPairsSearch hand` / `thirteenOrphansSearch hand` を公開する。
有効13・14枚相当入力に対し `*_eq_some_iff` が容量付き仕様との双方向の一致を保証する。
固定面子なしでは旧仕様との同値を再利用し、固定面子があれば `none` とする。
`*_eq_none_iff` により、暗槓を含む適用不可と `none` が同値。
適用可能なのに未計算という状態はない。入力の容量・枚数・固定文脈との整合検証は別途必要。

[回帰例](../../Shanten/Capacity/Examples.lean) は13枚テンパイ・14枚完成、
四枚使いを含む13枚の値6／14枚の値5、中張牌の対を数えない国士、
么九牌の刻子、国士の最大値13、暗槓での適用除外を検査した。
3形を最小値で統合する計算API・総合仕様との一致と、Lean側の37種入力は以下で完了した。
Go対応は未実装のまま保留する。

## 順序4：3形の総合値

容量付きの `IsOverallShanten fixed hand value` は、
いずれかの形の仕様値を達成し、全形の仕様値以下となることを要求する。
計算関数に依存しない達成最小値の定義であり、
`isOverallShanten_unique` と `isOverallShanten_neg_one_iff` を証明した。

[Overall.lean](../../Shanten/Capacity/Overall.lean) は
`shapeSearch fixed hand shape` と `overallMinimumSearch fixed hand` を公開する。
対象は `ValidHand fixed hand` と、13枚相当または14枚相当の枚数条件。

- `shapeSearch_eq_some_iff` / `shapeSearch_eq_none_iff`：
  形ごとの仕様一致と、`none` が適用不可と同値になることを保証する。
- `overallMinimumSearch_eq_some_iff` / `overallMinimumSearch_exists_unique`：
  適用可能な3形の最小値が総合仕様と一致し、結果が必ず存在し一意であることを保証する。
  計算には既存の `minOption` を使い、適用不可を値0として混ぜない。
- `overallMinimumSearch_of_fixed`：固定面子があれば、暗槓も含め面子手の結果だけとなる。
- `overallMinimumSearch_neg_one_le` / `overallMinimumSearch_eq_neg_one_iff`：
  結果は−1以上で、値−1といずれかの形の完成が同値。
- `overallMinimumSearch_nil`：固定面子なしの対象入力では
  既存の抽象仕様 `Shanten.OverallShanten` と結果が一致する。

回帰例はA/Bの総合値1・0と14枚相当未完成手の値1、
面子手・七対子・国士の各完成による総合値−1を検査した。
固定面子なしの完成例は、構造的完成・特殊形の実計算から一般定理を適用し、
面子手候補の巨大な全列挙は実行しない。新たな性能改善を行ったとは扱わない。
入力検証・37種正規化は以下で別途接続した。
Go対応と容量付きモデル全域での追加の数値上限は対象外。

## 順序4：37種入力の容量検証・正規化

[Input37.lean](../../Shanten/Input37.lean) はLean側の入力境界。
`Counts37 := Fin 37 → Int` により長さは型で固定し、負数は検証で拒否する。
赤5は0・10・20、通常数牌は1..9・11..19・21..29、字牌は30..36の契約上の添字を保持する。
入力は手元牌と、種類文字列・全実牌カウントを持つ固定面子のリスト。

- `normalizeCounts_sum` / `capacity_fiber`：
  整数上で赤5を統合し、総枚数と34種の各容量4への対応を証明した。
- `validateAndNormalize`：
  各欄の非負性、手元牌と全固定面子の合算物理容量、面子数、手元枚数、
  面子の種類・構造を検証し、成功時だけ正規化結果を返す。
  赤は1枚・通常5は3枚までを統合前に確認し、負数の相殺も認めない。
  失敗時は牌添字・面子添字などを持つ明示的なエラーを返す。
- `validateAndNormalize_accepts_iff`：
  成功結果の存在と宣言的な `Valid input` が同値。
- `parsedMelds_counts` / `validateAndNormalize_valid`：
  固定牌と槓の4枚占有を保存し、成功結果が有効13・14枚相当入力になる。
  自然数カウントへの変換にも非負性の証明を要求する。
- `validated_overall_eq_some_iff` / `validated_overall_exists_unique`：
  成功結果へ既存の総合計算の正当性・全域性を追加仮定なしで適用できる。
- `normalized_equivalent` / `overall_normalization_invariant`：
  両入力が受理され、正規化後の手元牌・面子の種類と牌内容が同じなら、
  赤の物理的割当てが異なっても、正規化結果と総合値は不変。

回帰例で3色の赤混在13・14枚手、赤を含むチー・ポン・暗槓／大明槓／加槓の受理、
赤2枚・通常5の4枚・固定面子との合算超過、負数の相殺、
不正面子・不明な種類・枚数不整合・面子5組の拒否を検査した。
ここで扱う整数はLeanの数学的整数。Goの機械整数・入力変換・エラーラップの実装や検証は含まない。
利用者の別計画を先行するためGo実装には着手せず、Goソース・開発コンテナは変更していない。

## レビューR3：自動検証

[Checksワークフロー](../../.github/workflows/checks.yml) を追加した。
Goは `go.mod` 指定のバージョンで `go test ./...` / `go vet ./...` を実行する。
Leanは固定済みツールチェーンと依存manifestを使い、`lake update` せずに
import対象のMathlibキャッシュを取得して `lake build` を実行する。

[ProofChecks.lean](../../Shanten/ProofChecks.lean) は公開入口からimportされるため、
ローカルの通常ビルドでも主要87宣言の推移的な `sorryAx` 依存を拒否する。
検査対象はR1保存定理・共有到達・一般探索・バッチ走査・七対子上限・国士最大値に加え、
R2の容量保存・旧仕様との対応・A/B受入証明、容量付き一般探索の仕様一致・全域性・計算結果、
14枚相当の仕様一致・全域性・最適打牌、特殊形の一般式・容量付き仕様一致・適用除外・回帰計算。
総合値の仕様一致・存在一意性・下界・完成値・旧仕様との一致と回帰例も検査する。
37種入力の受理条件・保存・容量付き入力への接続・赤の割当て不変性・拒否回帰も検査する。
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
- 旧1,665行の [SevenPairs.lean](../../Shanten/SevenPairs.lean) は12行の公開入口にし、
  七対子固有の実装は基本定義・カウント・完成形・交換戦略・到達性の8モジュールに分割した。
  最大324行。汎用の不足枚数・交換操作・交換列は
  [Exchange.lean](../../Shanten/Exchange.lean) に切り出し、面子手も直接共有する。
- テンパイ目標と完成時カウント、対を残す打牌、未登場牌種、単独牌の存在を表す名前を
  整理した。[改名表](../SHANTEN_LEAN_STRUCTURE.md#改名) の変更以外は公開名を維持する。
  `e7f741a` の92宣言すべてについて、改名後の宣言・命題・証明本文が移動先と一致し、
  未移動・重複した宣言がないことを機械照合した。到達上限などの証明範囲は拡張していない。

## 国士無双：最大シャンテン数13

[ThirteenOrphans.lean](../../Shanten/ThirteenOrphans.lean) を公開入口からimportした。
対象は `IsThirteenTileHand` を満たす固定面子なしの有効な13枚手。

- `reaches_thirteenOrphans_completion`：完成形への14手以内の到達を構成する。
- `thirteenOrphansShanten_exists`：すべての対象手牌で仕様値が存在して13以下になる。
- `kokushiWorstCase_isThirteenTileHand`：既存の中張牌13枚の具体例が有効である。
- `kokushiWorstCase_completion_distance_ge_fourteen`：この具体例からどの国士完成形へも
  最低14手が必要である。不足牌数は1手につき最大1しか減らないことを使う。
- `kokushiWorstCase_shapeShanten`：具体例の仕様値が `some 13` となる。
- `thirteenOrphansShanten_maximum`：上界13とその達成をまとめた定理。

面子手にあった汎用の交換・目標到達補題12宣言を共有の
[Exchange.lean](../../Shanten/Exchange.lean) へ移動し、完成形への到達と不足数の下界を
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

詳細な履歴は[Lean証明の検証記録](SHANTEN_LEAN4_VERIFICATION.md)を参照。

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

1. 実装変更ごとに、基準コミット・解消した未解決前提を台帳に、検証コマンドと結果を[検証記録](SHANTEN_LEAN4_VERIFICATION.md)に記録する。性能測定は[性能測定記録](SHANTEN_LEAN4_PERFORMANCE.md)に記録する。
2. 完了したチェック項目は根拠となる定理とともに成果欄へ移す。
3. 経路を仮定する変換と、分解から経路を生成する定理を区別して報告する。
4. 撤回した方針や詳細な過去履歴はアーカイブへ移し、現行チェックリストに残さない。
5. 対象範囲や完了条件を変更するときは [現行計画](SHANTEN_LEAN4_PLAN.md) も更新する。
