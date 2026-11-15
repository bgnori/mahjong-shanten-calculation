# シャンテン計算のLean4証明進捗

この文書は、[Lean4正当化計画](./SHANTEN_LEAN4_PLAN.md) に対して、実装・証明が
どこまで進んでいるかを記録する進捗台帳である。作業を行うたびに、完了した補題、
現在の課題、検証結果を更新する。

## 現在の概要

**最終更新:** 2026-11-15  
**現在の主対象:** 面子手の完成形・到達関係・シャンテン仕様との接続  
**総合ステータス:** 進行中（ターゲットDPの仕様一致は完了、制約付きブロック探索の完全性が未完了）

面子手については、牌姿を構成するブロック探索と、探索結果から
`Complete .mentsuHand` および `IsShapeShanten` を導く補題まで実装済みである。
一方、タイル順に進む制約付きブロック探索が任意の有効な分解を列挙することは、
まだ完了していない。

## 計画に対する進捗

| 計画段階 | 内容 | 状態 | 現在の成果・残課題 |
|---|---|---|---|
| Phase 1 | 牌種、手牌、面子、完成形、入力不変条件 | 部分完了 | 34種正規化モデル、`ValidCounts`、`Complete`、`HandStep` を実装済み。固定面子は個数のみで、牌内容を保持する拡張は未着手。 |
| Phase 2 | 七対子・国士無双・面子手の宣言的シャンテン関係 | 部分完了 | 七対子の到達補題と国士無双の閉形式補題を実装済み。面子手は仕様接続の補題を拡張中。 |
| Phase 3 | 面子手の有限探索・DPと仕様の一致 | 進行中 | 全ターゲットを列挙するコストDPと `IsShapeShanten` の一致は証明済み。タイル順の制約付きブロック探索について、任意の分解を列挙する完全性が残っている。 |
| Phase 4 | 3形の総合値と上限・適用可能性 | 部分完了 | `OverallShanten`、形ごとの一意性、総合値の上限補題を実装済み。面子手の一般到達性が揃った後に総合証明を完成させる。 |
| Phase 5 | Go実装との適合性・共有fixture | 未着手 | Lean仕様と実行可能なGo計算器の値一致検証は未着手。 |

## 面子手証明の現在地

### 完了済み

実装場所は [MentsuHand.lean](../Shanten/MentsuHand.lean) である。

- 面子・搭子・雀頭を選ぶ有限状態と遷移を定義した。
- 探索状態が入力手牌の牌カウントを超えないことを証明した。
- 4枚制限を満たす探索状態だけを扱う制約付き探索を定義した。
- 完成したブロック探索状態から、`Complete .mentsuHand` を満たす完成形を構成した。
- 完成形の不足枚数が1枚多い場合、1回の交換で完成形へ到達できることを証明した。
- 上記から、制約付きブロック探索が完了すれば
  `∃ value, IsShapeShanten hand .mentsuHand value` を導出できるようにした。
- 全ターゲットを列挙する `mentsuHandTargetMinimumSearch` について、最小距離の検索結果が
  `IsShapeShanten` と一致することを証明した。
- 制約付きブロック探索の完成状態から、対応するターゲット距離が
  `validMentsuHandTargetDistances` に含まれることを証明した
  (`validMentsuHandTargetDistance_mem_of_constrainedBlockSearch`)。
- 非 `skip` の面子・搭子・雀頭選択ごとに、`mentsuHandTileOrder` 上で
  選択を処理できる代表牌が存在することを証明した
  (`exists_tile_mem_mentsuHandTileOrder_of_choice`)。
- 代表牌を `before ++ tile :: after` というタイル順の分割に変換する補題を追加した
  (`exists_mentsuHandTileOrder_split_of_choice`)。
- 分解の接頭辞と探索状態の `used` が一致する場合、次の選択が手牌カウント内に収まり、
  完成後のコピー制限も維持する補題を追加した
  (`nextChoice_count_le_hand`,
  `nextChoice_completion_count_le_four`)。
- 牌カウント以外の `melds`・`taatsu`・`pair` 条件を組み合わせて、
  `ValidMentsuHandChoice` を構成する補題を追加した
  (`valid_next_choice_of_prefix`)。
- 選択列の `meld`・`taatsu` の個数を定義し、選択列を適用した後の探索状態の
  `melds`・`taatsu` カウンタと一致することを証明した
  (`AppliesMentsuHandChoices.melds_eq`,
  `AppliesMentsuHandChoices.taatsu_eq`)。
- 雀頭選択を適用した状態の `pair` が選択した牌になることを、
  `applyMentsuHandChoice_pair_eq_some` として切り出した。

関連する主な補題:

- `complete_mentsuHand_of_constrainedBlockSearch`
- `exists_isShapeShanten_mentsuHand_of_constrainedBlockSearch`
- `exists_isShapeShanten_mentsuHand_of_constrainedBlockSearchOnTileOrder`

### 次に必要な証明

1. **制約付きブロック探索の完全性 (`searchResult_complete`)**
   - `MentsuHandBlockDecomposition` の任意の有効な分解が、
     `MentsuHandBlockSearchOnTileOrderWithCopyLimit` のいずれかの枝で生成されること。
   - 各ブロックの代表牌を `mentsuHandTileOrder` に挿入する際の、接頭辞状態の
     `ValidMentsuHandChoice` のうち、牌カウントと完成後コピー制限は完了。
   - 呼び出し側から探索状態の面子数・搭子数・雀頭状態を供給して妥当な選択を構成する補題は完了。
   - それらの状態不変条件を、分解選択列の接頭辞から自動的に構成することが残っている。
2. **探索結果とターゲットDPの接続**
   - 制約付きブロック探索からターゲット距離集合への健全性接続は完了。
   - 残りは、タイル順探索の完全性を示して逆方向の包含を得ること。
3. **13枚手に対する一様な到達上限**
   - 任意の有効な13枚手について、面子手の完成形へ7手以内（固定面子を含む場合は
     状態に応じた上限）で到達できることを、完全性から構成すること。
4. **総合シャンテン値への接続**
   - 面子手・七対子・国士無双の値を、適用可能性に従って最小化する証明を完成させること。

## 直近の作業履歴

| 日付 | 変更 | 意味 |
|---|---|---|
| 2026-11-15 | `af52253` `proof: derive completion reachability from block decomposition` | ブロック分解から面子手完成形への到達性を導出する補題を追加。 |
| 2026-11-15 | `acb37c9` `Reduce Lean build memory with focused mathlib imports` | Leanビルドのメモリ使用量を抑えるため import を整理。 |
| 2026-11-14 | `32b1b36` `proof: connect constrained block search to shanten` | 制約付きブロック探索を面子手シャンテン仕様へ接続。 |
| 2026-11-14 | `8144828` `proof: expose mentsu search correctness for thirteen-tile hands` | 13枚手に対する面子手探索の正当性補題を公開。 |
| 2026-11-14 | `4e5e5d8` `Connect recursive meld cost DP to shanten search` | 再帰的な面子コストDPとシャンテン探索を接続。 |
| 2026-11-15 | `MentsuHand.lean` の既存補題を確認 | 全ターゲット列挙DPの最小値と `IsShapeShanten` の一致が既に証明済みであることを進捗へ反映。 |
| 2026-11-15 | `validMentsuHandTargetDistance_mem_of_constrainedBlockSearch` | 制約付きブロック探索の結果を、仕様一致済みのターゲット距離集合へ接続。 |
| 2026-11-15 | `exists_tile_mem_mentsuHandTileOrder_of_choice` | 各ブロック選択をタイル順探索へ挿入するための代表牌の存在を証明。 |
| 2026-11-15 | `valid_next_choice_of_prefix` | 接頭辞条件から `ValidMentsuHandChoice` を構成。 |
| 2026-11-15 | `AppliesMentsuHandChoices.melds_eq`, `AppliesMentsuHandChoices.taatsu_eq` | 選択列の面子・搭子個数と探索状態カウンタを対応付け。 |
| 2026-11-15 | `applyMentsuHandChoice_pair_eq_some` | 雀頭選択後の `pair` 状態を確定する遷移補題を追加。 |
| 2026-11-15 | `exists_mentsuHandTileOrder_split_of_choice` | 代表牌をタイル順の前後リスト分割へ変換。 |
| 2026-11-15 | `nextChoice_count_le_hand`, `nextChoice_completion_count_le_four` | 接頭辞状態から次の選択の牌カウントとコピー制限を導出。 |

## 検証状況

最終更新時点で次の検証が成功している。

```text
lake build Shanten
Build completed successfully (880 jobs).
```

警告は残っているが、ビルドを失敗させるエラーはない。証明の意味論上の未完了項目は、
ビルド成功とは別に、上記の「次に必要な証明」で管理する。

## 更新ルール

今後の作業では、少なくとも次をこの文書に反映する。

1. 完了した補題または定義を「計画に対する進捗」と「面子手証明の現在地」に追加する。
2. 未完了の最重要課題を「次に必要な証明」に残し、完了したら削除または完了済みに移す。
3. 変更日、コミット、検証コマンドと結果を「直近の作業履歴」「検証状況」に記録する。
4. モデル上の制約変更があった場合は、[SHANTEN_LEAN4_PLAN.md](./SHANTEN_LEAN4_PLAN.md)
   の計画とこの進捗台帳の両方を更新する。
