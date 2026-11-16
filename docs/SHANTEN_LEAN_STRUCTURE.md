# Leanソースの構造

この文書は現在の配置を説明する。初回分割の移行指示は完了済みの計画として
[アーカイブ](./archive/2026-11-15_SHANTEN_LEAN_STRUCTURE.md) に移した。
現在の実装作業は [計画](./SHANTEN_LEAN4_PLAN.md) と
[台帳](./SHANTEN_LEAN4_PROGRESS.md) に従う。追加分割を今回の作業とはしない。

## モジュール

| ファイル | 主な責務 |
|---|---|
| [Shanten.lean](../Shanten.lean) | 下記5モジュールをimportする公開入口。 |
| [Core.lean](../Shanten/Core.lean) | 牌・手牌・面子の基礎モデル、カウントや基本述語。 |
| [Specification.lean](../Shanten/Specification.lean) | 形、完成形、到達関係、形シャンテンと総合値の宣言的仕様。 |
| [SevenPairs.lean](../Shanten/SevenPairs.lean) | 七対子の証明、交換操作、不足距離などの補題。 |
| [MentsuHand.lean](../Shanten/MentsuHand.lean) | 面子手のターゲットDP、選択列・バッチ走査、仕様への接続。 |
| [Bounds.lean](../Shanten/Bounds.lean) | 到達性からの上界、国士無双の直接計算などの上位補題。 |

## リポジトリ内の直接import

```text
Specification -> Core
SevenPairs    -> Specification
MentsuHand    -> Specification, SevenPairs
Bounds        -> SevenPairs
Shanten       -> Core, Specification, SevenPairs, MentsuHand, Bounds
```

共有定義は既存の提供元を再利用し、循環importを作らない。
構造変更が必要になった場合も、宣言・命題の意味の変更とは分離して検証する。
