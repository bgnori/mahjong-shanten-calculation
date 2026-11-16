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
| [Specification.lean](../Shanten/Specification.lean) | 形、完成形、到達関係、形シャンテンと総合値の宣言的仕様。 |
| [Exchange.lean](../Shanten/Exchange.lean) | 形に依存しない不足枚数、交換操作、固定目標への到達、到達距離の下界。 |
| [SevenPairs.lean](../Shanten/SevenPairs.lean) | 七対子の公開import入口。実装は下表のモジュールに分割。 |
| [ThirteenOrphans.lean](../Shanten/ThirteenOrphans.lean) | 有効13枚手の国士無双の仕様値の存在・上界13と、最大値を達成する具体例。 |
| [MentsuHand.lean](../Shanten/MentsuHand.lean) | 面子手のターゲットDP、選択列・バッチ走査、仕様への接続。 |
| [Bounds.lean](../Shanten/Bounds.lean) | 到達性からの条件付き上界、国士無双の閉形式の直接計算などの上位補題。 |

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
面子手も使う `countDeficit`・`exchangeHand`・`TargetExchange`・`ReachesExchange`
などは [Exchange.lean](../Shanten/Exchange.lean) に移し、面子手から七対子への依存を外した。
これらの共有宣言名と型は維持した。

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
Shanten       -> Core, Specification, SevenPairs, ThirteenOrphans, MentsuHand, Bounds
```

上表はプロジェクト内の依存を示す（Mathlibのimportは省略）。
面子手内部の詳細は [計画の構成表](./SHANTEN_LEAN4_PLAN.md#ファイル構成と読む順序) を参照する。
共有定義は既存の提供元を再利用し、循環importを作らない。
構造変更が必要になった場合も、宣言・命題の意味の変更とは分離して検証する。

国士無双の追加時に、面子手の `Exchange` にあった汎用の目標カウント・不足数・
交換列の補題を共有の [Exchange.lean](../Shanten/Exchange.lean) へ移動した。
既存の公開名・型を維持し、完成形への到達と不足数による下界を形に依存しない補題へ
一般化した。面子手の既存補題はその特殊化として利用する。
