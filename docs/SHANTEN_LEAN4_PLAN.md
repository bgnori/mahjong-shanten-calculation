# シャンテン計算のLean4正当化計画

**更新:** 2026-11-16

この文書は現在の作業範囲と完了条件を定める。成果・検証状況の正は
[進捗台帳](./SHANTEN_LEAN4_PROGRESS.md) とする。
旧実装順序、完了済みの導入手順、撤回した探索方針は
[アーカイブ](./archive/README.md) に保存した。現在のTODOとして使わない。

## 目的と維持する契約

Leanで数学的仕様と計算可能な探索の一致を証明し、その仕様に対応するGo計算器を
後段で実装・検証する。Goの入力・結果・エラー契約は
[リポジトリのREADME](../README.md) を参照する。

- 37種入力の赤5を計算時に通常5へ統合する。固定面子は暗槓も含む。
- 面子手は常に適用可能。七対子・国士無双は固定面子がない場合だけ適用する。
- 和了は `-1`、テンパイは `0`。総合値は適用可能な形の最小値。
- 不正入力はエラーとし、対象外の形や失敗を成功値へ変換しない。
- 結果は決定的で、入力を変更しない。

抽象版の一般探索は34牌種に正規化済みで、固定面子は個数だけを持つ。
R2への段階導入として、固定面子の実牌内容と合算容量を保持する
[容量付きモデル](../Shanten/Capacity.lean) を別層に追加した。
このモデル上の `Capacity.generalMentsuHandMinimumSearch fixed hand` は、
有効13枚相当・14枚相当手牌すべてで面子手の容量付き仕様との一致・全域性まで証明済み。
14枚相当では未完成手の最適打牌との一致も証明した。
特殊形の一般計算・37種入力との対応は後続課題であり、契約全体を証明済みとは扱わない。

## ファイル構成と読む順序

[MentsuHand.lean](../Shanten/MentsuHand.lean) は公開import用の入口に限定する。
実装は [MentsuHand/](../Shanten/MentsuHand/) 以下の共通基盤・`Scan`・`Search` に分割した。
面子手の名前空間 `Shanten` と公開定義・定理名は維持し、証明内容は変更していない。

[SevenPairs.lean](../Shanten/SevenPairs.lean) も公開import入口とし、
[SevenPairs/](../Shanten/SevenPairs/) 以下を基本定義・カウント補題・完成形への接続・
交換戦略・到達性に分割した。汎用の不足枚数と交換操作は
[Exchange.lean](../Shanten/Exchange.lean) で面子手と共有する。
七対子の読む順序と改名対応は [構造文書](./SHANTEN_LEAN_STRUCTURE.md#七対子の構成と読む順序)
を参照する。以下は面子手の構成表である。

容量付きモデルは [Capacity.lean](../Shanten/Capacity.lean) を入口とし、
[Basic](../Shanten/Capacity/Basic.lean)（固定面子・残余容量）、
[Specification](../Shanten/Capacity/Specification.lean)（容量付き仕様・旧仕様との対応）、
[Reachability](../Shanten/Capacity/Reachability.lean)（容量を守る目標到達）、
[Search](../Shanten/Capacity/Search.lean)（容量付き候補と最小値）、
[Totality](../Shanten/Capacity/Totality.lean)（一般入力の全域性・仕様一致）、
[Fourteen](../Shanten/Capacity/Fourteen.lean)（14枚相当の仕様一致・完成値）、
[Discard](../Shanten/Capacity/Discard.lean)（最適打牌・打牌後最小値との対応）、
[Examples](../Shanten/Capacity/Examples.lean)（R2のA/B受入例・計算結果）の順に読む。
既存の抽象仕様を置き換えるものではなく、名前空間 `Shanten.Capacity` で区別する。

| 層 | モジュール | 責務 |
|---|---|---|
| 共通 | [Basic](../Shanten/MentsuHand/Basic.lean) | ターツ、状態・選択の型、選択が使う牌。 |
| 共通 | [ChoiceGrouping](../Shanten/MentsuHand/ChoiceGrouping.lean) | 代表牌による選択列の分類と重複度を保つ順列性。 |
| 共通 | [State](../Shanten/MentsuHand/State.lean) | 遷移、履歴不変条件、到達関係、34牌種順。 |
| 共通 | [Targets](../Shanten/MentsuHand/Targets.lean) | 完成目標と探索状態の対応。 |
| 共通 | [Exchange](../Shanten/MentsuHand/Exchange.lean) | 共有の交換・到達補題の面子手完成形への特殊化。 |
| 共通 | [Decomposition](../Shanten/MentsuHand/Decomposition.lean) | 雀頭＋4ブロック分解、選択列、完成後4枚制限。 |
| 牌種順走査 | [Scan/Basic](../Shanten/MentsuHand/Scan/Basic.lean) | 枚数制限付き遷移とバッチ走査の関係。 |
| 牌種順走査 | [Scan/Paths](../Shanten/MentsuHand/Scan/Paths.lean) | 前向き経路、不変条件、バッチとの接続。 |
| 牌種順走査 | [Scan/DecompositionPaths](../Shanten/MentsuHand/Scan/DecompositionPaths.lean) | 分解の任意の順列から合法な経路を構成。 |
| 牌種順走査 | [Scan/Grouping](../Shanten/MentsuHand/Scan/Grouping.lean) | 分解から34牌種順バッチ走査と完了状態を構成。 |
| 牌種順走査 | [Scan/Completion](../Shanten/MentsuHand/Scan/Completion.lean) | 走査状態から完成目標・シャンテン仕様への条件付き接続。 |
| 完成形探索 | [Search/Enumeration](../Shanten/MentsuHand/Search/Enumeration.lean) | 完成形候補の列挙、牌集合DP、妥当性判定。 |
| 完成形探索 | [Search/TargetDP](../Shanten/MentsuHand/Search/TargetDP.lean) | 不足数を累積する完成形DPと所属の特徴付け。 |
| 完成形探索 | [Search/Minimum](../Shanten/MentsuHand/Search/Minimum.lean) | 最小目標距離と到達距離の下界。 |
| 完成形探索 | [Search/Reachability](../Shanten/MentsuHand/Search/Reachability.lean) | 目標距離を実現する引牌・交換列の構成。 |
| 完成形探索 | [Search/Correctness](../Shanten/MentsuHand/Search/Correctness.lean) | 最小目標距離と数学的シャンテン仕様の対応。 |
| 完成形探索 | [Search/Totality](../Shanten/MentsuHand/Search/Totality.lean) | 一般13枚相当手牌の全域性とターゲットDPの仕様一致。 |
| 完成形探索 | [Search/BlockSearch](../Shanten/MentsuHand/Search/BlockSearch.lean) | 手牌消費・不足数を持つブロック探索と仕様一致。 |
| 検証例 | [Examples](../Shanten/MentsuHand/Examples.lean) | 重複ターツ、雀頭なし、孤立牌、嵌張、4枚制限の回帰証明。 |

一般手牌の計算を読む場合は共通基盤から `Search` を表の順に読む。
与えられた分解の牌種順走査を読む場合は、共通基盤から `Scan` を表の順に読む。
`Scan/Completion` は仕様への接続に `Search/Totality` も利用するが、`Search` は
`Scan` に依存しない。`Examples` は両方をimportし、公開入口のビルドで検証する。

旧 `GeneralMentsuHand.lean` は探索方式に合わせて `Search/BlockSearch.lean` へ移動した。
直接importしていた場合は `Shanten.MentsuHand.Search.BlockSearch` または公開入口
`Shanten.MentsuHand` に置き換える。`generalMentsuHand...` 等の公開名は互換性のため維持する。

## 完了した目標：国士無双の最大シャンテン数13

[ThirteenOrphans.lean](../Shanten/ThirteenOrphans.lean) で、固定面子なしの有効な13枚手
すべてに国士無双の仕様値が存在して13以下となることと、その上界を達成する手牌の
存在を証明した。出口定理は `thirteenOrphansShanten_maximum`、
値の存在は `thirteenOrphansShanten_exists`。

既存の閉形式 `kokushiShanten` の算術的上界だけではなく、
`IsShapeShanten` の最短到達距離を使う。任意の完成目標まで不足牌数だけの手順で到達し、
中張牌だけの具体例では完成に必要な14枚すべてが不足することから最短距離14を示す。
閉形式と仕様値の一般的な一致や14枚手への拡張は、この成果には含めない。

## 完了した中間目標：与えられた分解のバッチ走査

`MentsuHandBlockDecomposition hand` が与えられた場合に、その全選択を
固定34牌種順の `AppliesMentsuHandTileBatchScan` で実行できることを示した。
出口定理は `MentsuHandBlockDecomposition.exists_tileBatchScan_complete`。
重複度を保つ順列からコピー制限付き経路を構成し、既存の
`AppliesMentsuHandGroupedTileBatches` を経て牌種順のバッチ走査へ接続する。

### 出口の命題

任意の手牌 `hand` とその分解 `d` から、次を満たす `final` を構成する。

1. `initialMentsuHandState` から `mentsuHandTileOrder` を走査する。
2. 選択列は `d.blockChoices` を牌種順にグループ化した全選択である。
3. `final.pair = some d.pair` が成立する。
4. `IsMentsuHandBlockSearchComplete hand final` が成立する。

経路・バッチ・探索成功・個々の遷移の妥当性を入力前提として残さない条件を満たした。
レビューの「東の雀頭と12萬ターツ4組」の13枚手も具体例として最終状態まで検査した。
これは**与えられた分解の列挙**であり、一般手牌の最小値一致とは別の命題である。

### 完了した実装順序

1. 重複度付き包含から、走査途中の使用牌・ブロック数・補完牌の上限を導いた。
2. 処理済みの雀頭選択と `state.pair` を対応付け、雀頭を含む経路を構成した。
3. 各グループの経路を分解から生成し、34牌種順の全走査と完了状態へ接続した。

一般手牌に対する探索の被覆性・最小値一致は、この分解定理だけからは導かれない。
以下の別の一般ブロック探索で証明した。

## 完了した主目標：一般手牌の面子手シャンテン数

入力は `ValidCounts hand` と `tileCount hand + 3 * hand.fixedMelds = 13` を満たす
任意の手牌。雀頭なし・孤立牌・ブロック不足も含め、分解の存在を要求しない。

[Search/BlockSearch.lean](../Shanten/MentsuHand/Search/BlockSearch.lean) に、
次の有限探索を実装した。

1. 完成後の雀頭候補と `4 - hand.fixedMelds` 個の面子候補を順に選ぶ。
2. ブロックごとに、まだ使っていない手牌から一致する牌を消費し、不足牌数を加算する。
   手牌から割り当てる部分は空・1枚・嵌張でもよく、雀頭がなくても探索できる。
3. 完成後4枚制限を越える候補を各段階で排除し、最小不足牌数から1を引く。

これは既存のターゲットDPの名前を変えた入口ではなく、使用牌と不足数を保持する
別の状態・遷移による探索である。ただし全完成ブロック候補を列挙するため、
高速な通常の面子・ターツ数DPや枝刈りまで完成したという意味ではない。
旧牌種順バッチ走査を変更せず、新探索は雀頭・面子ブロックの順に処理する。

### 満たした完了条件

- 各ブロック追加後も牌を二重使用せず、不足数が完成候補までの不足距離に一致する。
- 妥当な全完成形候補を探索が被覆し、探索中の完成候補は必要面子数と4枚制限を満たす。
- 新しい探索の候補距離集合が既存の全ターゲットDPと一致する。
- `generalMentsuHandMinimumSearch_eq_some_iff` が `IsShapeShanten` との双方向の一致を与える。
- `generalMentsuHandMinimumSearch_exists_unique` が全対象手牌の結果の存在と一意性を与える。
- `generalMentsuHandMinimumSearch_optimal` が最小値を実現する探索状態の存在を与える。

数学的仕様との接続には既存のターゲットDPの証明を再利用するが、
新探索の遷移の不変条件・被覆性・距離集合の一致は別途証明した。
証明した対象は13枚相当・正規化34牌種・固定面子数だけの現行モデルに限る。
14枚手や固定面子の実牌内容の検証まで完成したとは扱わない。

## 完了した段階導入：容量付きモデル（R2）

### モデルと受入条件

- 固定面子は `List Capacity.FixedMeld` として経路全体で不変にする。
  通常の面子は既存 `Meld` を再利用し、槓は別の構成子で4枚を消費する。
  リスト長ではどちらも1面子であり、暗槓も特殊形を適用不可にする。
- `remainingCapacity fixed tile` は `4 - (fixedTiles fixed).count tile`。
  `ValidHand` は残余容量だけでなく手元牌と固定牌の**和が4以下**であることを要求する。
  そのため、自然数の減算が0に切り詰められても、固定牌だけで5枚以上ある入力を許さない。
  `hand.fixedMelds = fixed.length` と `fixed.length ≤ 4` も要求する。
- `IsThirteenTileEquivalentHand` は上記の有効性と
  `tileCount hand + 3 * fixed.length = 13`。槓の4枚消費は容量に反映しつつ、
  手牌枚数の換算では1面子として扱う。
- 容量付き `Complete` は容量の有効性と既存の構造的完成条件の積。
  容量付き `HandStep` は既存遷移に加えて開始手・終了手の容量有効性を要求する。
  ドロー・交換の構成補題は引く牌の残余枠を検査し、完成目標も同じ容量に従う。
- `ReachesHand` は0手の場合も有効性を要求する。
  `ReachesCompletion` は容量付きの経路と完成先、
  `IsShapeShanten` はその最短距離から1を引いた値を表す。
  値の一意性に加え、以下の13枚相当の容量付き一般探索との一致も証明済み。

[受入例](../Shanten/Capacity/Examples.lean) はレビューのA/Bについて、
入力の有効性だけでなく最短距離を検査する。
`inputA_shanten` は最短2手・値1、`inputB_shanten` は最短1手・値0。
Aの0手・1手の完成を否定し、東から白への交換と白のドローで2手を構成する。
Bは東を1枚引いて完成する。容量超過のドロー・交換、槓の残余容量0、
固定牌だけで容量を超える文脈の拒否も検査する。

### 旧モデルとの対応と再利用範囲

固定文脈を忘れる射影では、手元牌を既存の `Hand` のまま再利用する。

| 範囲 | 対応・再利用条件 |
|---|---|
| 有効性・完成形 | `ValidHand.validCounts` と完成条件の第2成分で旧モデルへ射影できる。逆方向には固定牌込みの容量検証が必要。 |
| 遷移・経路 | `HandStep.toAbstract`・`ReachesHand.toAbstract`・`ReachesCompletion.toAbstract` で距離を保って射影できる。旧経路を容量確認なしで持ち上げることはできない。 |
| 最小値 | `IsShapeShanten.abstract_le` により、両モデルで値が存在すれば旧値は容量付き値の下界。固定面子があれば一般に等しくない。 |
| 固定面子なし | `ValidHand [] hand` の下で `isShapeShanten_nil_iff` が3形すべての仕様一致を与える。既存の七対子・国士・面子手の値定理はこの条件で再利用できる。 |
| 牌の算術 | `exchangeCounts_*` や不足枚数の下界は既存の演算・射影を通して再利用できる。 |
| 一般探索 | 候補列挙・手牌消費を再利用し、完成後の手元牌と固定牌の合算容量で候補をフィルタする。13枚相当の被覆性・経路構成・最小値一致・全域性は接続済み。旧探索の最小値をそのまま返すのではない。 |

### 一般探索への接続（推奨順序4の冒頭・完了）

`Capacity.generalMentsuHandMinimumSearch fixed hand` は、
既存の `GeneralMentsuHandState` とブロック消費・不足枚数の計算を再利用する。
全完成候補のうち `state.completed + fixedTiles fixed` が4枚制限を守るものだけを残し、
残った候補の不足枚数の最小値から1を引く。
容量判定は完成候補の段階で行い、枝刈り・性能最適化は今回の対象にしない。

- `mem_generalMentsuHandStates_iff`：容量を守る全完成形と探索状態の対応を証明する。
- `generalMentsuHandState_reaches`：各候補の不足枚数で容量を守る完成経路を構成する。
  共有の `ReachesTargetExchange` に目標方向の交換列の構成を抽出し、
  既存の抽象経路・新しい容量付き経路の双方へ、それぞれの有効性条件付きで変換する。
- `exists_state_of_reachesCompletion`：任意の容量付き完成経路から、
  その経路長以下の不足枚数を持つ探索状態を得る。
- `exists_complete_target`：固定面子1組が占有する字牌は高々1種であることを使い、
  未占有の字牌から必要な刻子と雀頭を構成する。入力に完成目標の存在を仮定しない。
- `generalMentsuHandMinimumSearch_eq_some_iff` /
  `generalMentsuHandMinimumSearch_exists_unique` /
  `generalMentsuHandMinimumSearch_optimal`：
  `IsThirteenTileEquivalentHand fixed hand` だけを条件に仕様一致・存在一意性・最適状態を証明する。
- `generalMentsuHandMinimumSearch_nil`：固定面子なしの対象入力では抽象版の計算結果と一致する。

R2の `inputA_search` / `inputB_search` は実際の探索を `decide` で計算し、
結果がそれぞれ `some 1` / `some 0` であることを検査する。槓を含む計算例も検査済み。
従来の `Shanten.generalMentsuHandMinimumSearch` は抽象版として維持し、
固定面子の実牌容量を考慮する呼出側は `Shanten.Capacity` の関数へ固定文脈を渡す。

37種の赤5を統合する前の容量検証・正規化の値保存やGo入力との対応は未証明。
13枚相当の接続に続き、以下の14枚相当への拡張も完了した。

### 14枚相当の打牌選択と仕様一致（完了）

`IsFourteenTileEquivalentHand fixed hand` は `ValidHand fixed hand` と
`tileCount hand + 3 * fixed.length = 14` を要求する。
同じ `generalMentsuHandMinimumSearch` を使い、完成目標と手牌の枚数が等しい場合の
共有交換列を再利用して、不足枚数ちょうどの容量付き経路を構成する。
13枚相当向けの既存定理の型・保証は維持した。

- `generalMentsuHandMinimumSearch_eq_some_iff_of_fourteen` /
  `generalMentsuHandMinimumSearch_exists_unique_of_fourteen` /
  `generalMentsuHandMinimumSearch_optimal_of_fourteen`：
  有効14枚相当入力すべてで仕様一致・結果の存在一意性・最適状態を保証する。
- `generalMentsuHandMinimumSearch_eq_neg_one_iff`：
  完成形であることと、探索結果が `some (-1)` であることが同値。
- `discardHand` は手元牌だけを1枚減らす。実際に持つ牌を捨てると有効性を保ち、
  `IsFourteenTileEquivalentHand.discard` が有効な13枚相当入力を与える。
  固定面子から牌を捨てたり、固定面子数を減らしたりしない。
- `discardSearchResults` は持っている牌種だけを列挙し、
  各打牌と13枚相当探索の結果の組を返す。`minimumDiscardSearch` はその最小値。
- 未完成手では `generalMentsuHandMinimumSearch_eq_minimumDiscardSearch` が
  14枚相当の値と打牌後最小値の一致を保証する。
  各打牌で不足枚数は減らず、最適完成目標に対して余剰の牌を捨てれば不足枚数を保てることを使う。
- `optimalDiscards` はその最小値を達成する全打牌種を返す。
  `mem_optimalDiscards_iff` と `optimalDiscards_nonempty` で、
  未完成の有効14枚相当入力では全候補が合法で最適、かつ少なくとも1候補あることを保証する。

完成済みの手牌は打牌すると値が変わるため、打牌後最小値との一致の対象から除外する。
計算側は先に一般探索で完成値 `-1` を確認し、未完成の場合に打牌候補を使う。
回帰例は容量により最適打牌が1種／複数種となる場合、値1の未完成手、
完成値 `-1` と打牌後値0の違い、持っていない牌の除外、槓を含む14枚相当完成形を実計算で検査する。
今回の完了範囲は面子手までであり、七対子／国士の一般計算や総合値を完了扱いにしない。

## 現在の作業で維持する境界

- `mentsuHandTargetMinimumSearch` と `IsShapeShanten` の条件付き同値は既に証明済み。
  バッチ走査の新規成果と混同しない。
- 旧一選択走査は同一牌種で複数ブロックを選べないため、
  バッチ走査との単純な同値を目標にしない。
- 牌種順への再配置に `List.Sublist` を要求しない。重複度を保持すること。
- 現在の分解構造は、雀頭と合計4ブロック、完成後の4枚制限を前提とする。
  一般手牌の被覆性は、この構造ではなく新しい一般ブロック探索で保証する。
- 存在する経路を別の関係へ変換するだけの補題を、経路生成の完了として数えない。

旧一選択走査とその挿入・skip専用証明、元の分解順序に固定した経路構成は
2026-11-16に実装から削除した。履歴資料の同名宣言を現在のAPIとして使わない。
共有の部分列単調性や順列不変性は、重複度付き包含の証明でも使えるため維持する。

## 後続課題（現在の完了条件には含めない）

| 範囲 | 必要な成果 |
|---|---|
| 特殊形の一般計算 | 七対子／国士の13・14枚相当の計算と仕様一致。面子手の13・14枚相当と最適打牌は証明済み。 |
| 総合値・上限 | 適用可能性に従う3形の最小値と一般到達上限の証明。数値目標と前提を別途確定する。 |
| 入力モデル | 37種の赤5正規化・統合前容量検証と、容量付き34種モデルとの対応。 |
| Go実装・適合性 | Leanとの状態・遷移・評価の対応表、共有fixture、入力・エラー境界のテスト。 |
| 最適化 | 基準探索・仕様との値一致を維持したキャッシュ・枝刈り等。 |

長期的な成果物を廃止したのではなく、直近の統合証明と分離している。
後続課題を開始するときは、その対象・入力条件・完了定理をこの文書と台帳に明示する。

## 検証方針

関連する最小のLean検査を実施し、実行したコマンドと対象コミットを台帳に残す。
証明変更では、一般定理に加え、雀頭の代表牌が後になる例、同一牌種の複数ブロック、
重複度・4枚制限の境界を確認する。文書のみの整理で証明完成やビルド成功を追加報告しない。

将来のGo実装の適合性はLean検査とは別に確認する。最適化の正当性を基準探索の証明と
混同せず、共有fixtureと独立した基準値との比較を行う。
