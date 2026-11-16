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

現行Leanモデルは34牌種に正規化済みで、固定面子は個数だけを持つ。
固定面子の牌内容込みの容量検証や37種入力との完全な対応は後続課題であり、
現行モデルだけで契約全体を証明済みとは扱わない。

## ファイル構成と読む順序

[MentsuHand.lean](../Shanten/MentsuHand.lean) は公開import用の入口に限定する。
実装は [MentsuHand/](../Shanten/MentsuHand/) 以下の共通基盤・`Scan`・`Search` に分割した。
名前空間 `Shanten` と公開定義・定理名は維持し、証明内容は変更していない。

| 層 | モジュール | 責務 |
|---|---|---|
| 共通 | [Basic](../Shanten/MentsuHand/Basic.lean) | ターツ、状態・選択の型、選択が使う牌。 |
| 共通 | [ChoiceGrouping](../Shanten/MentsuHand/ChoiceGrouping.lean) | 代表牌による選択列の分類と重複度を保つ順列性。 |
| 共通 | [State](../Shanten/MentsuHand/State.lean) | 遷移、履歴不変条件、到達関係、34牌種順。 |
| 共通 | [Targets](../Shanten/MentsuHand/Targets.lean) | 完成目標と探索状態の対応。 |
| 共通 | [Exchange](../Shanten/MentsuHand/Exchange.lean) | 不足枚数、交換操作、固定目標への到達。 |
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
| 入力枚数の拡張 | 14枚手の打牌選択を含む計算と仕様の対応。13枚相当の一般手牌は新探索で証明済み。 |
| 総合値・上限 | 適用可能性に従う3形の最小値と一般到達上限の証明。数値目標と前提を別途確定する。 |
| 入力モデル | 赤5正規化、固定面子の牌内容・槓の消費牌数、合算容量検証との対応。 |
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
