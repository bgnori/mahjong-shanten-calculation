# Leanソースの構造

この文書は現在の配置を説明する。初回分割の移行指示は完了済みの計画として
[アーカイブ](./archive/2026-11-15_SHANTEN_LEAN_STRUCTURE.md) に移した。
現在の実装作業は [計画](./SHANTEN_LEAN4_PLAN.md) と
[台帳](./SHANTEN_LEAN4_PROGRESS.md) に従う。

## モジュール

| ファイル | 主な責務 |
|---|---|
| [Shanten.lean](../Shanten.lean) | 主要モジュールをまとめる公開入口（直接importは下記参照）。 |
| [Core.lean](../Shanten/Core.lean) | 牌・手牌・面子の基礎モデル、カウントや基本述語。 |
| [Specification.lean](../Shanten/Specification.lean) | 形、完成形、到達関係、形シャンテンと総合値の宣言的仕様。到達性からの値の存在・上界の共通証明。 |
| [Exchange.lean](../Shanten/Exchange.lean) | 形に依存しない不足枚数、交換操作、固定目標への到達、到達距離の下界。 |
| [SevenPairs.lean](../Shanten/SevenPairs.lean) | 七対子の公開import入口。実装は下表のモジュールに分割。 |
| [ThirteenOrphans.lean](../Shanten/ThirteenOrphans.lean) | 有効13枚手の国士無双の仕様値の存在・上界13と、最大値を達成する具体例。 |
| [Special.lean](../Shanten/Special.lean) | 七対子・国士無双の閉形式と最短完成距離仕様の一致。有効な固定面子なし13・14枚手を対象とする。 |
| [MentsuHand.lean](../Shanten/MentsuHand.lean) | 面子手のターゲットDP、選択列・バッチ走査、仕様への接続。 |
| [Bounds.lean](../Shanten/Bounds.lean) | 到達性からの条件付き上界、国士無双の閉形式の直接計算などの上位補題。 |
| [Capacity.lean](../Shanten/Capacity.lean) | 固定面子の実牌内容を持つ容量付きモデルの公開入口。既存抽象モデルとは別の段階導入。 |
| [Capacity/Basic.lean](../Shanten/Capacity/Basic.lean) | 槓を含む固定面子、残余容量、合算容量の有効性と保存。 |
| [Capacity/Specification.lean](../Shanten/Capacity/Specification.lean) | 容量付き完成・遷移・最短距離仕様、総合値の達成最小値仕様、旧モデルへの射影と固定面子なしでの同値。 |
| [Capacity/Reachability.lean](../Shanten/Capacity/Reachability.lean) | 共有の目標方向交換列を容量付き経路へ変換し、不足枚数で完成目標へ到達する。 |
| [Capacity/Search.lean](../Shanten/Capacity/Search.lean) | 既存ブロック探索の容量フィルタ、完成形との対応、到達上界・下界、最小値証明。 |
| [Capacity/Totality.lean](../Shanten/Capacity/Totality.lean) | 有効固定文脈の完成目標を構成し、13枚相当入力すべての全域性・仕様一致・最適状態を証明する。 |
| [Capacity/Fourteen.lean](../Shanten/Capacity/Fourteen.lean) | 14枚相当の全域性・仕様一致・最適状態、完成と値−1の同値。 |
| [Capacity/Discard.lean](../Shanten/Capacity/Discard.lean) | 合法打牌後の13枚相当入力、打牌結果・最適打牌列挙、未完成14枚相当の値と打牌後最小値の一致。 |
| [Capacity/Special.lean](../Shanten/Capacity/Special.lean) | 特殊形の計算API、13・14枚相当の容量付き仕様一致、固定面子による適用除外。 |
| [Capacity/Overall.lean](../Shanten/Capacity/Overall.lean) | 3形の計算窓口と総合最小値、仕様一致・存在一意性、完成値・固定面子時の帰着・旧総合仕様との一致。 |
| [Capacity/Examples.lean](../Shanten/Capacity/Examples.lean) | R2のA/B、14枚相当の最適打牌、特殊形・総合値、容量超過・槓の回帰例。 |
| [Input37.lean](../Shanten/Input37.lean) | 符号付き37種入力のLean側の公開入口。Go実装ではない。 |
| [Input37/Basic.lean](../Shanten/Input37/Basic.lean) | aka37添字・物理容量、整数上の赤5統合、総枚数保存、統合後容量、入力妥当性の宣言的仕様。 |
| [Input37/Validation.lean](../Shanten/Input37/Validation.lean) | 正規化前の検証と位置付きエラー、面子の構造認識、受理と入力仕様の同値。 |
| [Input37/Correctness.lean](../Shanten/Input37/Correctness.lean) | 枚数・固定牌の保存、容量付き入力への接続、総合計算の前提、赤の割当て変更に対する値不変性。 |
| [Input37/Examples.lean](../Shanten/Input37/Examples.lean) | 13・14枚の赤混在、赤を含む面子・槓、容量超過・負数・不正面子・枚数の回帰検査。 |
| [ProofChecks.lean](../Shanten/ProofChecks.lean) | 主要出口定理の推移的な `sorryAx` 依存を通常ビルドで拒否する。 |

## 七対子の構成と読む順序

[SevenPairs.lean](../Shanten/SevenPairs.lean) のimportと名前空間 `Shanten` は維持する。
テンパイは異なる6対と単独牌1種、完成形は異なる7対として区別する。
今回の整理で命題・証明の前提や到達距離は変更していない。

| モジュール | 主な責務 |
|---|---|
| [Basic](../Shanten/SevenPairs/Basic.lean) | テンパイ述語、テンパイ目標と完成時カウント、目標カウントの局所補題。 |
| [Counting](../Shanten/SevenPairs/Counting.lean) | filterの濃度、単独牌・余剰牌の存在、13枚手の牌種数・対数の上下界。 |
| [Completion](../Shanten/SevenPairs/Completion.lean) | テンパイ形の分解、完成条件、最後の1枚のドローによる和了。 |
| [Exchange/Basic](../Shanten/SevenPairs/Exchange/Basic.lean) | 対候補、対を保つ打牌、未登場牌種、各交換戦略の定義。 |
| [Exchange/Distinctness](../Shanten/SevenPairs/Exchange/Distinctness.lean) | 対を保ちながら牌種を1つ増やす交換の存在と不変条件。 |
| [Exchange/PairMaking](../Shanten/SevenPairs/Exchange/PairMaking.lean) | 牌種数を保ちながら単独牌を対にする交換の存在と不変条件。 |
| [Exchange/ProtectedPairMaking](../Shanten/SevenPairs/Exchange/ProtectedPairMaking.lean) | 保護対象7種の選択と不変条件、対象内で対を作る交換。 |
| [Reachability](../Shanten/SevenPairs/Reachability.lean) | 各交換の反復、交換列の不変条件、7牌種・6対への構成的な到達。 |

基本定義から `Counting`・`Completion` を読み、交換の定義と各戦略を経て
`Reachability` を読む。`Completion` は交換戦略に依存しない。
`Reachability` と `Completion` を組み合わせる上界定理は、従来どおり
[Bounds.lean](../Shanten/Bounds.lean) に置く。
面子手も使う `countDeficit`・`exchangeHand`・`TargetExchange`・`ReachesHand`
などは [Exchange.lean](../Shanten/Exchange.lean) に移し、面子手から七対子への依存を外した。
`ReachesHand` の改名前後の対応は下記参照。

### 改名

意味が曖昧だった次の名前を変更した。旧名の互換ラッパーは設けず、
リポジトリ内の参照を更新した。表以外の公開名は維持している。

| 旧名 | 新名 | 意図 |
|---|---|---|
| `sevenPairsTargetCounts` | `sevenPairsTenpaiTargetCounts` | 完成形ではなくテンパイ目標であることを示す。 |
| `sevenPairsTarget` | `sevenPairsTenpaiTarget` | 同上。 |
| `sevenPairsTargetCounts_*` / `sevenPairsTarget_*` | `sevenPairsTenpaiTargetCounts_*` / `sevenPairsTenpaiTarget_*` | 対応する局所補題も定義に合わせる。 |
| `sevenPairsCompleteCounts` | `sevenPairsCompletionCounts` | 完成形のカウントを表す名詞に統一する。 |
| `isSevenPairsTenpai_of_terminal` | `isSevenPairsTenpai_of_counts` | 探索終端でなく、枚数・牌種数・対数が前提であることを示す。 |
| `IsPreservingDiscard` | `IsPairPreservingDiscard` | 保存する対象が対であることを明示する。 |
| `IntroducesNewKind` | `IsAbsentTileKind` | 操作ではなく、現在のカウントが0という条件を表す。 |
| `exists_nonPair_kind` | `exists_singleton_kind_of_seven_kinds_lt_six_pairs` | 0枚の牌種ではなく単独牌の存在を、前提とともに示す。 |
| `ReachesExchange` | `ReachesHand` | 実際の遷移は `HandStep` であり、交換に加えてドローも許すことを明確にする。 |
| `*.toReachesExchange` | `*.toReachesHand` | 各七対子交換列から共有到達関係への変換も改名する。 |
| `reachesExchange_targetHand_of_equal_sum` | `reachesHand_targetHand_of_equal_sum` | 固定目標への到達補題を関係名に合わせる。 |

## モジュール間の依存

```text
Specification -> Core
Exchange      -> Specification
ThirteenOrphans -> Exchange
SevenPairs.Basic -> Exchange
SevenPairs.Counting -> Specification
SevenPairs.Completion -> SevenPairs.Basic
SevenPairs.Exchange.Basic -> Exchange
SevenPairs.Exchange.{Distinctness,PairMaking,ProtectedPairMaking}
              -> SevenPairs.Exchange.Basic, SevenPairs.Counting
SevenPairs.Reachability -> SevenPairs.Exchange.{Distinctness,PairMaking,ProtectedPairMaking}
SevenPairs    -> SevenPairs.Completion, SevenPairs.Reachability
MentsuHand.Targets -> MentsuHand.State, Exchange
Bounds        -> SevenPairs
Special       -> SevenPairs.Completion, SevenPairs.Counting, ThirteenOrphans
Capacity.Basic -> Exchange
Capacity.Specification -> Capacity.Basic
Capacity.Reachability -> Capacity.Specification
Capacity.Search -> Capacity.Reachability, MentsuHand.Search.BlockSearch
Capacity.Totality -> Capacity.Search
Capacity.Fourteen -> Capacity.Totality
Capacity.Discard -> Capacity.Fourteen
Capacity.Special -> Capacity.Specification, Special
Capacity.Overall -> Capacity.Fourteen, Capacity.Special
Capacity.Examples -> Capacity.Discard, Capacity.Special, Capacity.Overall
Capacity      -> Capacity.Basic, Capacity.Specification, Capacity.Reachability,
                 Capacity.Search, Capacity.Totality, Capacity.Fourteen,
                 Capacity.Discard, Capacity.Special, Capacity.Overall, Capacity.Examples
Input37.Basic -> Capacity.Basic
Input37.Validation -> Input37.Basic
Input37.Correctness -> Input37.Validation, Capacity.Overall
Input37.Examples -> Input37.Correctness
Input37       -> Input37.Basic, Input37.Validation, Input37.Correctness, Input37.Examples
ProofChecks   -> MentsuHand, ThirteenOrphans, Bounds, Capacity, Input37
Shanten       -> Core, Specification, SevenPairs, ThirteenOrphans, Special, MentsuHand, Bounds,
                 Capacity, Input37, ProofChecks
```

上表はプロジェクト内の依存を示す（Mathlibのimportは省略）。
面子手内部の詳細は [計画の構成表](./SHANTEN_LEAN4_PLAN.md#ファイル構成と読む順序) を参照する。
共有定義は既存の提供元を再利用し、循環importを作らない。
構造変更が必要になった場合も、宣言・命題の意味の変更とは分離して検証する。

国士無双の追加時に、面子手の `Exchange` にあった汎用の目標カウント・不足数・
交換列の補題を共有の [Exchange.lean](../Shanten/Exchange.lean) へ移動した。
既存の公開名・型を維持し、完成形への到達と不足数による下界を形に依存しない補題へ
一般化した。面子手の既存補題はその特殊化として利用する。

完成形の4枚制限の取り出しは `Complete.validCounts`、完成経路からのシャンテン
上界は `IsShapeShanten.le_of_completion_bound`、到達性からの値の存在は
`exists_isShapeShanten_of_reachesCompletion` に共通化した。形ごとの証明は
完成経路の構成に集中し、最小距離の選択や上界への変換を重複させない。
ドローと目標指向交換で不足数が1減る証明も、牌種ごとの等式を総和へ持ち上げる
同じ補題を利用する。完成条件・到達回数・シャンテン値の意味は変更していない。
