# W5対応レビュー報告（2026-11-19）

## 結論

W5-SとW5-Cは、計画で定めた「既存の入口・計算／列挙を保ち、通常形仕様の出口から共有核を実利用する」という受入条件に沿っている。固定面子数の境界、部品リストの順序・反復、牌種ごとの多重度を保つ接続が証明されており、確認範囲でブロッカーとなる不具合は見つからなかった。

W5は共有仕様への接続段階であり、固定文脈付き待ちとshanten 0の同値、A/BケースはW6の対象である。今回のレビューではそれらの成立を主張しない。

## レビュー対象

| 対象 | 確認したリビジョン |
|---|---|
| shanten側 W5-S | `7233bf45589fe51989e4f7ebb8c99956398999e3` |
| 分類側 W5-C | `803ba634ab53b90c0b51add76f7ce36b1bf73b2c` |
| 共通核 | `6cbb59efcc56a45cf0f321b6cc8653d64cdadf57` |
| 受入条件 | [共通ドメイン抽出作業計画](SHARED_DOMAIN_EXTRACTION_PLAN_2026-11-17.md)のW5-S／W5-C |

shanten側は[DomainAdapter](../../Shanten/DomainAdapter.lean)、[通常形仕様](../../Shanten/Specification.lean)、[容量付き仕様](../../Shanten/Capacity/Specification.lean)、[37入力の正規化](../../Shanten/Input37/Validation.lean)、[証明穴検査](../../Shanten/ProofChecks.lean)と関連文書を確認した。分類側は[PartsAdapter](https://github.com/bgnori/mahjong-formalization/blob/803ba634ab53b90c0b51add76f7ce36b1bf73b2c/Mahjong/PartsAdapter.lean)、[WaitCompletionFinder](https://github.com/bgnori/mahjong-formalization/blob/803ba634ab53b90c0b51add76f7ce36b1bf73b2c/Mahjong/WaitCompletionFinder.lean)、用語文書、依存SHAを確認した。

## 受入条件ごとの確認

| 条件 | 判定 | 根拠 |
|---|---|---|
| shantenの分解と共有仕様の双方向対応 | 適合 | `standardCompletion_iff_shantenParts`が、共有完成仕様とshantenの対子・順序付き面子列の存在を対応させる。固定面子数が4以下という前提を明示し、部品列の長さと牌種ごとの枚数を保存する。 |
| shanten通常形・容量出口の接続 | 適合 | `mentsuComplete_iff_standardCompletion`と`Capacity.Complete.mentsuHand_iff_standardCompletion`が共有仕様を利用する。4固定面子時の対子判定も接続後の仕様から導かれている。 |
| 37入力の共有集約利用 | 適合 | `normalizedHand`が`MahjongDomain.aggregateInt37`を使用し、`normalizeCounts_matches_domain`および`normalizedHand_counts_cast`が従来の正規化結果との一致を示す。入力検証後の容量・牌数保証も維持されている。 |
| shanten証明保証 | 適合 | 主要な変換・完成・容量・入力検証定理が`ProofChecks.lean`の`sorryAx`不在検査に追加されている。探索器と特殊形の証明は変更されていない。 |
| 分類側の個別分解対応 | 適合 | `Toitsu`／`MentsuCandidate`と共有`Pair`／`Meld`の変換に往復定理があり、順序付き`List`のまま反復面子を保つ。部品ごとの牌種カウントを証明し、`WinningPartitionSpec.toDomainStandardCompletion`は分解仕様から共有完成証人を構成する。 |
| 分類側の和了・合法待ち接続 | 適合 | `IsStandardAgari.toDomainStandardCompletion`、`IsWaitFor.toDomainWait`、`waitingTiles_member_toDomainWait`により、既存の宣言的仕様および待ち列挙の所属から共有完成仕様へ接続する。 |
| 既存出力と入力順の保持 | 適合 | `winningPartitions`、`waitingTiles`、正規化・分類IDを計算する既存コードの振る舞いは変更されていない。共有変換は別アダプタで行われ、用語文書も列挙・重複度を維持すると明記する。 |
| 固定依存と共通語彙参照 | 適合 | 両側は共通核のW4 SHA `6cbb59ef...`に固定され、shantenと分類側の語彙文書は同SHAの共通用語集を参照する。 |

## 指摘・フォローアップ

今回の範囲で修正必須の指摘はない。共有`StandardCompletion`は完成の存在を表す仕様で、分類側の列挙APIそのものではない。分類側は従来の`winningPartitions`を維持し、個々の分解を共有`StandardDecomposition`へ写すアダプタを提供しているため、列挙順や重複度の責務を共有核へ移してはいない。

W6では固定文脈込みの待ち集合との同値、通常形shanten 0との接続、計画記載の容量A/Bケースを別途確認する必要がある。

## 検証状況と限界

- shantenのW5-S差分と分類側のW5-Cコミットに対する`git diff --check`は成功した。
- 作業計画の記録では、shantenの`lake build`（935 jobs）、分類側の`lake build Mahjong MahjongTests`（868 jobs）、分類側の`go test ./mahjong`（0.233秒）が成功している。
- 今回の実行環境では`lake`と`go`が見つからず、これらのビルド・テストは独立再実行できていない。上記の成功結果は作業記録に基づくもので、今回の再実行結果ではない。
