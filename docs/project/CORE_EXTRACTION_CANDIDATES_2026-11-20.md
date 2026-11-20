# core抽出候補の棚卸し

**確認日:** 2026-11-20
**対象:** `mahjong-domain-core`と二つのconsumerのLean定義
**目的:** W7後もconsumer側に残る基礎ドメイン定義を確認し、追加抽出と既存coreへの接続を区別する。

## 要約

ご指摘の[分類側 `Mahjong.Basic`](../../../mahjong-wait-classification/Mahjong/Basic.lean)には、
数牌のランク・スート・牌種の定義が残っている。ただし、これらの意味はすでに
[coreの `MahjongDomain.Tile`](../../../mahjong-domain-core/MahjongDomain/Tile.lean)にあり、
[分類側adapter](../../../mahjong-wait-classification/Mahjong/DomainAdapter.lean)には
牌種の対応と安定した数値順の一致を示す定理もある。したがって主な残作業は、
定義をそのまま再移植することではなく、consumerの既存APIと列挙順を保ちながら、
coreを表現の正本にする接続・互換化である。

このほか、[shantenの `Core`](../../Shanten/Core.lean)と
[`Input37.Basic`](../../Shanten/Input37/Basic.lean)にも、coreに同等定義がある一方で
consumer側に独立した定義が残っている。牌の表示形式はconsumer固有として除外せず、
すぐ使える共通機能として今回coreに追加する。探索状態や待ち分類の符号化は、
引き続き各consumerの責務とする。

## 候補一覧

| 優先度 | consumerに残る定義 | core側の対応・現状 | 判断 |
|---|---|---|---|
| 高 | 分類側の`Rank`、`Suit`、`Honor`、`Tile`、牌種列挙・順序キー（[`Mahjong.Basic`](../../../mahjong-wait-classification/Mahjong/Basic.lean)） | [`Tile.lean`](../../../mahjong-domain-core/MahjongDomain/Tile.lean)に`Suit`、0始まりの`Rank`、`Honor`、正規化`Tile`、`Tile.all`、`Tile.index`がある。分類側adapterの`tileIndex_val`は`Tile.orderKey`との一致を証明している。 | 既存の分類側型を直ちに削除せず、core型への変換・互換入口を保ったまま、共通の意味とインデックスをcoreへ集約する。`Manzu`等の名前付きconstructorや`all`の列挙順は公開互換性として確認する。 |
| 高 | shanten側の`Suit`、`Tile`、`TileCounts`、`Meld`と牌の多重集合定義（[`Shanten.Core`](../../Shanten/Core.lean)） | coreの[`Tile.lean`](../../../mahjong-domain-core/MahjongDomain/Tile.lean)と[`Parts.lean`](../../../mahjong-domain-core/MahjongDomain/Parts.lean)に対応する牌・カウント・面子・構成牌定義がある。[`Shanten.DomainAdapter`](../../Shanten/DomainAdapter.lean)は牌、対子、面子、カウントを接続する。 | 分類側と同じく、移植より正本化の候補。探索・特殊形で使う`Hand`や么九牌の計算はshanten固有なので残す。 |
| 高 | `Counts37`、正規化牌、容量、集約とその基本則（[`Input37.Basic`](../../Shanten/Input37/Basic.lean)） | [`Representation.lean`](../../../mahjong-domain-core/MahjongDomain/Representation.lean)に`Int37Index`、`Int37Counts`、正規化、容量、集約および保存則がある。[`Input37.DomainAdapter`](../../Shanten/Input37/DomainAdapter.lean)で定義間の一致を証明している。 | 入力全体の型・検証契約はshanten側に残し、正規化・容量・集約の計算はcoreを直接利用する方向が有力。37枠の型名やエラー契約は互換性を保つ。 |
| 中 | `PhysicalTile := Tile × Fin 4`、`copiesPerTile`、`deck`、`deckSize`（分類側[`Mahjong.Basic`](../../../mahjong-wait-classification/Mahjong/Basic.lean)） | coreには線形な`PhysicalTileId : Fin 136`と牌種・Int37への対応がある。分類側adapterは組表現からIDへの変換と牌種保存を証明するが、逆変換や全単射をAPIとしては示していない。 | 未完了のモデル候補。`Tile × Fin 4`をcoreに足すか、IDを正本にして牌種・copyの射影を提供するかを先に決める。全単射と既存列挙の順序を証明し、`deck`が本当に共通APIかも確認する。 |
| 低／既存接続 | `Toitsu`、`Shuntsu`、`MentsuCandidate`、`WinningComponent`とその牌列（分類側[`Pattern`](../../../mahjong-wait-classification/Mahjong/Pattern.lean)） | coreの[`Parts.lean`](../../../mahjong-domain-core/MahjongDomain/Parts.lean)に`Pair`、`Meld`、`Meld.tiles`があり、分類側[`PartsAdapter`](../../../mahjong-wait-classification/Mahjong/PartsAdapter.lean)で変換・牌数の対応を定義済み。 | ドメイン上の対子・順子・刻子は抽出済み。分類側のコンストラクタ名、`List Tile`による順序、列挙・正規化は分類の出力に関わるので、`Multiset`を使うcore表現へ一括置換しない。残るのは既存接続を活用する範囲の整理。 |
| 条件付き | `FixedMeld`、固定牌の集約、残余容量（[`Capacity.Basic`](../../Shanten/Capacity/Basic.lean)） | coreに`Meld.tiles`と`Kan.occupiedTiles`はあるが、固定面子列・shantenの`Hand`を含む容量契約はない。 | 槓や固定牌の占有計算を他consumerも使う場合に限り、汎用の占有計算を候補とする。`ValidHand`、手牌枚数条件、交換操作はshanten側に残す。 |
| 今回追加 | 分類側の`TileFormat`と`Tile.format`（[`Mahjong.Basic`](../../../mahjong-wait-classification/Mahjong/Basic.lean)） | coreの[`Tile.lean`](../../../mahjong-domain-core/MahjongDomain/Tile.lean)に`MahjongDomain.TileFormat`と`MahjongDomain.Tile.format`を追加。 | Unicodeとmpszをcoreから直接使える。正規化牌種に対する表示なので、赤5の区別は保持しない。consumer側の互換APIをcoreへ委譲する作業は別途扱う。 |

## coreへ追加しない定義

- 分類側の`Hand`は重複しない物理牌を選ぶ分類入力、shanten側の`Hand`は牌種カウントと固定面子数を持つ探索入力であり、同じ型へ統合しない。
- `Taatsu`、探索state／choice、入力の`Input`・`MeldInput`・検証エラー、待ち分解・分類ID・既約性・病的プロファイルはconsumer固有の意味・出力契約を持つ。
- 通常形の対子・面子の定義と、分類の正規順、牌列の順序・重複を保持する表現は別の層として扱う。共通定義の採用だけを理由に既存結果を変えない。

## 次の抽出判断

1. 最優先は、牌種・37表現・部品について既存adapterが証明している対応を使い、coreを意味上の正本にする範囲を決めること。互換APIの維持と出力順の不変を受入条件にする。
2. 物理牌モデルはcoreに既存の136-ID表現があるため、別表現を追加する前に双方向変換・全単射・山の列挙順を明確にする。
3. 固定牌・標準形の枚数などは、二つ以上のconsumerで再利用される定義・保存則に絞る。consumer固有の手牌条件や探索意味論は移さない。
4. coreへ型を移すだけで完了とせず、adapterを通じて既存の出力・不正入力契約・証明の保証が維持されることを検証する。

本書は候補調査であり、上記の抽出や公開API変更を実施した記録ではない。全体の境界と完了条件は
[共通ドメイン抽出計画](./SHARED_DOMAIN_EXTRACTION_PLAN_2026-11-17.md)を参照。
