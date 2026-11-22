# W6対応レビュー報告（2026-11-19）

このレビューは当時のリビジョンを対象とする履歴です。W6パッケージは移行時の検証後に
解消されました。現状は[用語集](../GLOSSARY.md)を参照してください。

## 結論

W6の接続証明は、固定文脈付き通常形待ちと分類側`IsWaitFor`の同値、
通常形shanten 0との接続、および容量A/Bケースを構成している。
確認した証明の前提と牌数・容量の扱いに、同値を崩す論理上の問題は見つからなかった。

ただし、作業計画が求める推移的`sorryAx`不在検査にW6の主要定理が含まれていない。
この検証ギャップを解消するまでは、W6の形式検証保証はビルド成功の記録だけに依存する。
これは証明の誤りを示す指摘ではないが、計画の検査条件に対するフォローアップである。

## レビュー対象

| 対象 | 確認したリビジョン／条件 |
|---|---|
| W6接続パッケージ | `a177a053d701291b60fc6b3b061177aa6a264570` |
| 接続証明 | [`SharedDomainW6.lean`（削除前）](https://github.com/bgnori/mahjong-shanten-calculation/blob/bbfed07f8de7d437898dd12abc01fe3b4031f516/w6/SharedDomainW6.lean) |
| パッケージ設定 | [`lakefile.lean`（削除前）](https://github.com/bgnori/mahjong-shanten-calculation/blob/bbfed07f8de7d437898dd12abc01fe3b4031f516/w6/lakefile.lean)、[`lake-manifest.json`（削除前）](https://github.com/bgnori/mahjong-shanten-calculation/blob/bbfed07f8de7d437898dd12abc01fe3b4031f516/w6/lake-manifest.json) |
| 受入条件 | [共通ドメイン抽出作業計画](SHARED_DOMAIN_EXTRACTION_PLAN_2026-11-17.md)の3.2、W6、5節 |

## 受入条件ごとの確認

| 条件 | 判定 | 根拠 |
|---|---|---|
| 牌種変換と牌数対応 | 適合 | 両アダプタを介した牌種変換に往復定理があり、`CountsMatch.toDomain`と`CountsMatch.length_eq`が牌種ごとの個数一致から総牌数一致を導く。候補牌を加えた場合も`CountsMatch.draw`で対応を保つ。 |
| 固定文脈付き待ちと分類側待ちの同値 | 適合 | `fixedContextWait_iff_classificationWait`は、13枚相当の前提から分類側の手牌枚数条件と合法枚数条件を構成し、加牌後の共有完成仕様と`IsStandardAgari`を双方向に接続する。固定牌を含む容量条件は別の連言として保持され、単独の`IsWaitFor`と混同されていない。 |
| 固定面子数と完成分解数 | 適合 | 加牌後の牌数と分類側の分解の牌数から、分解面子数が`4 - fixed.length`であることを導く。固定面子数が4以下という前提は13枚相当の有効な固定文脈から得ており、不正な減算で条件を隠していない。 |
| 通常形shanten 0との接続 | 適合 | `isShapeShanten_zero_iff_exists_fixedContextWait`は、最小距離1の一歩についてdrawとexchangeを区別し、13枚相当の手からexchangeだけで完成する可能性を牌数で排除する。続く同値が分類側待ちへ接続する。総合shantenや特殊形の判定とは同一視していない。 |
| 容量A/Bケース | 適合 | `capacityAB`は同じ手元`111m`＋東と同じ牌姿単独の東待ちに対し、東刻子固定では容量超過、南刻子固定では東待ちが成立することを示す。`capacityB_shanten_zero`はBケースから通常形shanten 0を導く。 |
| 既存API・列挙器への影響 | 適合 | 変更は独立したW6パッケージ内に限られ、shanten・分類側のAPIや分類出力を変更していない。 |

## 指摘・フォローアップ

### 検証保証：W6定理の推移的`sorryAx`検査がない

W6パッケージ内に`assert_no_sorry`または`sorryAx`検査はなく、
shanten側の[ProofChecks.lean](../../Shanten/ProofChecks.lean)もW6パッケージをimportしていない。
したがって、同ファイルの既存検査が成功していても、次のW6接続定理について
推移的な`sorryAx`不在を保証しない。

- `fixedContextWait_iff_classificationWait`
- `isShapeShanten_zero_iff_exists_fixedContextWait`
- `isShapeShanten_zero_iff_exists_classificationWait`
- `capacityAB`、`capacityB_shanten_zero`

W6パッケージまたは専用の検査入口から、少なくとも上記の接続・受入定理を
推移的`sorryAx`不在検査へ追加することを推奨する。これは作業計画5節にある
「新しい保存定理・接続定理も同種の推移的`sorryAx`不在検査へ追加する」
という条件に対応する。

W6はshantenと分類側のローカルcheckoutをLakeのpath依存として参照する。
これは作業記録の検証構成と一致するが、両側のソースリビジョンを固定した再現検査ではない。
固定依存・CIへの移行はW7の受入条件として扱う。

## 検証状況と限界

- 作業計画には、Lean／mathlib `v4.35.0`で`cd w6 && lake build`が成功（921 jobs）と記録されている。
- 今回の実行環境では`lake`がPATH上にないため、ビルドを独立再実行できなかった。
  上記の成功結果は作業記録に基づき、今回の再実行結果ではない。
- 今回はW6の証明と依存設定を静的に確認した。W6定理に対する
  推移的`sorryAx`不在検査の実行結果は未確認である。
