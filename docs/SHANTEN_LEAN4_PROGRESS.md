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
- 既に雀頭がある状態では、雀頭以外の妥当な選択を適用しても `pair` が保持されることを、
  `applyMentsuHandChoice_pair_eq_of_not_pair` として証明した。
- 分解の `blockChoices` に含まれる面子・搭子選択数が、それぞれ元の `melds`・
  `taatsus` のリスト長と一致することを証明した
  (`blockChoices_meldCount`, `blockChoices_taatsuCount`)。
- `blockChoices` の面子・搭子部分に含まれる選択は、必ず雀頭選択ではないことを
  証明した (`blockChoices_tail_not_pair`)。
- 分解選択列の接頭辞に対して、次の選択後も面子数・搭子数が4以下であることを
  `blocks` 条件から導出する補題を追加した
  (`nextChoice_melds_le_four`, `nextChoice_taatsu_le_four`)。
- `used`・`melds`・`taatsu` の各接頭辞カウンタ一致と雀頭条件をまとめて受け取り、
  `ValidMentsuHandChoice` を構成する補題を追加した
  (`valid_next_choice_of_count_prefix`)。
- 非空の選択接頭辞では次の選択が雀頭でないことを、`blockChoices` の構造から導出し、
  空接頭辞での雀頭なし条件と合わせて妥当な選択を自動構成する補題を追加した
  (`nextChoice_not_pair_of_nonempty_prefix`,
  `valid_next_choice_of_count_prefix_of_pair`)。
- 初期探索状態から選択列を適用した場合の `used`・`melds`・`taatsu` の一致を、
  初期値を消去した簡約形として公開した
  (`used_eq_from_initial`, `melds_eq_from_initial`,
  `taatsu_eq_from_initial`)。
- 上記3つの状態不変条件をまとめる `MentsuHandChoiceStateMatches` と、
  初期状態からの選択列がこれを満たすことを示す
  `AppliesMentsuHandChoices.state_matches_from_initial` を追加した。
- 1回の妥当な選択遷移が、選択列を1要素延長した
  `MentsuHandChoiceStateMatches` を保つことを証明した
  (`applyMentsuHandChoice.state_matches_cons`)。
- `skip` 遷移では `used`・`pair`・`melds`・`taatsu` がすべて保持されることを
  証明した (`applyMentsuHandChoice_skip_fields`)。
- `skip` 遷移が分解選択列を延長せずに
  `MentsuHandChoiceStateMatches` を保持することを証明した
  (`applyMentsuHandChoice.skip_state_matches`)。
- 制約付き到達済み状態から `skip` 選択の妥当性を構成し、その後も
  `MentsuHandChoiceStateMatches` を保持する補題を追加した
  (`exists_skip_state_matches_of_reachable`)。
- 状態に選択を適用した結果を、分解接頭辞の向きに合わせた
  `choices ++ [choice]` 形式で表す補題を追加した
  (`applyMentsuHandChoice.state_matches_append_single`)。
- パッケージ化した `MentsuHandChoiceStateMatches` と雀頭条件から、
  次の選択の `ValidMentsuHandChoice` を直接構成する補題を追加した
  (`valid_next_choice_of_state_matches`)。
- 分解接頭辞を左から右へ拡張する前向き選択列関係
  `AppliesMentsuHandChoicesForward` と、初期状態からの状態不変条件補題
  `AppliesMentsuHandChoicesForward.state_matches_from_initial` を追加した。
- コピー制限を各遷移に保持する
  `AppliesMentsuHandChoicesForwardWithCopyLimit` を追加した。
- この関係から、選択列の長さを燃料とする
  `reachableWithinWithCopyLimit` を導出する帰納補題を完成させた
  (`reachableWithinWithCopyLimit_of_forward_choice_path`)。
- コピー制限付き前向き選択列でも、初期状態から
  `MentsuHandChoiceStateMatches` が成立することを証明した
  (`AppliesMentsuHandChoicesForwardWithCopyLimit.state_matches_from_initial`)。
- 選択列の搭子部分を抽出する `mentsuHandChoiceTaatsus` と、選択列の末尾追加に
  対応する `mentsuHandChoiceTaatsus_append` を追加した。
- 搭子列を選択へ写像した場合に、搭子抽出が元の搭子列を復元する
  `mentsuHandChoiceTaatsus_map_taatsu` を追加した。
- 搭子列の部分列に対する補完牌 Multiset の個数単調性
  (`taatsuCompletionTiles_count_le_of_sublist`) を追加した。
- 分解の接頭辞の牌数上限と、探索状態の搭子履歴が分解の搭子列の部分列であることから、
  `CompletionRespectsCopyLimit` を構成する
  (`MentsuHandBlockDecomposition.completion_respects_of_prefix`) 補題を追加した。
- 選択列の搭子抽出列がブロック分解の搭子列の部分列になることを証明した
  (`prefix_taatsus_sublist`)。
- コピー制限付き前向き選択列と分解接頭辞から、
  `CompletionRespectsCopyLimit` を構成する
  (`AppliesMentsuHandChoicesForwardWithCopyLimit.completion_respects_from_prefix`)
  補題を追加した。
- ブロック分解の選択列に `skip` が含まれないことを示す
  (`MentsuHandBlockDecomposition.blockChoices_ne_skip`) 補題を追加した。
- タイルを `skip` しながら、選択列に対する
  `MentsuHandChoiceStateMatches` を保持して到達性を延長する
  (`reachableOnTilesFromWithCopyLimit_skips_state_matches`) 補題を追加した。
- `skip` 列が探索状態の `pair` を変更しないことを追跡する
  (`reachableOnTilesFromWithCopyLimit_skips_pair`) 補題を追加した。
- `skip` 列について、状態不変条件と `pair` 保存を同じ最終状態に対して返す
  (`reachableOnTilesFromWithCopyLimit_skips_state_matches_pair`) 補題を追加した。
- 代表牌で1選択を適用した後、残りのタイル列を `skip` で進めても、
  選択列の状態不変条件を保持する
  (`reachableOnTilesFromWithCopyLimit_choice_then_skips_state_matches`) 補題を追加した。
- 前方 `skip`・代表牌選択・後方 `skip` を結合し、状態不変条件付きでタイル順到達性を
  構成する `reachableOnTilesFromWithCopyLimit_insert_choice_state_matches` を追加した。
- `skip` 遷移で `taatsuHistory.reverse` が不変であることを証明し
  (`applyMentsuHandChoice.skip_taatsuHistory_reverse`)、
  タイル列全体の `skip` に対して履歴対応を保持する
  (`reachableOnTilesFromWithCopyLimit_skips_taatsuHistory`) 補題を追加した。
- `skip` 列について、状態不変条件・`pair` 保存・`taatsuHistory` 対応を同じ最終状態へ
  統合する `reachableOnTilesFromWithCopyLimit_skips_invariants` を追加した。
- 分解接頭辞の妥当性、搭子履歴、コピー制限を統合し、代表牌の前後の `skip` と選択を
  結合する `MentsuHandBlockDecomposition.insert_choice_from_prefix` を追加した。
- `skip` 列について、状態不変条件・`pair`・`taatsuHistory` を同一の最終状態へ統合する
  `reachableOnTilesFromWithCopyLimit_skips_invariants` を実装し、分解接頭辞からの
  コピー制限付き選択挿入を実際に構成できる状態にした。
- ブロック選択が探索候補に属し、かつ `skip` ではないことを一つにまとめた
  `MentsuHandBlockDecomposition.blockChoices_mem_all_and_ne_skip` を追加した。
- 分解ブロック選択から、探索候補所属・非 `skip`・代表牌を含む
  `mentsuHandTileOrder` の分割を一括取得する
  `exists_tile_order_split_of_blockChoice` を追加した。
- 分解ブロック選択を指定するだけで上記の分割と状態不変条件付き挿入を呼び出せる
  `MentsuHandBlockDecomposition.insert_blockChoice_from_prefix` を追加した。
- 初期状態から分解の雀頭選択をタイル順探索へ挿入する基底補題
  (`insert_pair_from_initial`) を追加した。
- タイル列を一度だけ左から右へ走査し、各タイルで `skip` または有効な選択を行う
  `AppliesMentsuHandTileScan` を導入し、既存の
  `reachableOnTilesFromWithCopyLimit` へ変換する
  (`AppliesMentsuHandTileScan.to_reachable`) 補題を追加した。
- 一回走査関係の `skip`・`choose` 帰納に対して、選択列接頭辞と探索状態の
  `MentsuHandChoiceStateMatches` を最後まで保持する
  (`AppliesMentsuHandTileScan.state_matches_append`,
  `AppliesMentsuHandTileScan.state_matches_from_initial`) 補題を追加した。
- 任意の到達済み状態からタイル列全体を `skip` だけで一度走査し、
  `AppliesMentsuHandTileScan`・状態不変条件・雀頭保存を同時に得る
  (`AppliesMentsuHandTileScan.skips_state_matches`) 補題を追加した。
- 代表牌を選択した直後に残りのタイル列を一度だけ `skip` 走査し、
  `AppliesMentsuHandTileScan` と接頭辞状態不変条件を接続する
  (`AppliesMentsuHandTileScan.choose_then_skips_state_matches`) 補題を追加した。
- `skip` のみの走査と代表牌選択後の走査を連結し、任意の分解接頭辞から
  代表牌を一度だけ選ぶ一回走査を構成する
  (`AppliesMentsuHandTileScan.append_skips`,
  `MentsuHandBlockDecomposition.insert_choice_scan_from_prefix`) 補題を追加した。
- 分解の雀頭選択についても、初期状態から代表牌を選び残りを一回走査する
  (`MentsuHandBlockDecomposition.insert_pair_scan_from_initial`) 基底補題を追加した。
- 一回走査関係の前方区間と後方区間を、選択列を連結しながら結合する一般補題
  (`AppliesMentsuHandTileScan.append`) を追加した。
- 既に処理済みの一回走査区間へ、分解接頭辞の次のブロック選択を連結する
  (`MentsuHandBlockDecomposition.append_choice_scan_from_prefix`) 補題を追加した。
- タイル順に選択した結果、分解の選択列と順序が異なる場合に備え、
  `List.Perm` による選択列の順序変更が `used`・面子数・搭子数の
  `MentsuHandChoiceStateMatches` を保持する補題
  (`mentsuHandChoiceStateMatches_of_perm`) を追加した。
- 搭子の選択順序を並べ替えても補完牌の Multiset が変わらないことを
  (`taatsuCompletionTiles_of_perm`) として証明し、タイル順走査でのコピー制限の
  順序依存性を除去する基礎を追加した。
- 搭子履歴が順序変更された場合でも、既存のコピー制限を新しい履歴へ移送する
  (`completionRespectsCopyLimit_of_history_perm`) 補題を追加した。
- コピー制限付き前向き選択列の `taatsuHistory.reverse` が、選択列から抽出した
  搭子列と一致することを証明した
  (`AppliesMentsuHandChoicesForwardWithCopyLimit.taatsuHistory_reverse_from_initial`)。
- 既存の制約付き到達状態に、妥当性とコピー制限を満たす選択を1つ追加して
  `reachableWithinWithCopyLimit` を得る補題を追加した
  (`reachableWithinWithCopyLimit_append_choice`)。

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
| 2026-11-15 | `applyMentsuHandChoice_pair_eq_of_not_pair` | 雀頭以外の選択後に既存の `pair` が保持されることを証明。 |
| 2026-11-15 | `blockChoices_meldCount`, `blockChoices_taatsuCount` | ブロック選択列の面子・搭子数を分解リスト長へ対応付け。 |
| 2026-11-15 | `blockChoices_tail_not_pair` | 面子・搭子部分に雀頭選択が含まれないことを証明。 |
| 2026-11-15 | `nextChoice_melds_le_four`, `nextChoice_taatsu_le_four` | 接頭辞から次選択後の面子・搭子上限を導出。 |
| 2026-11-15 | `valid_next_choice_of_count_prefix` | 接頭辞カウンタ条件から次の選択の妥当性を一括構成。 |
| 2026-11-15 | `nextChoice_not_pair_of_nonempty_prefix`, `valid_next_choice_of_count_prefix_of_pair` | 接頭辞の空・非空から雀頭条件を導出し、妥当な選択を構成。 |
| 2026-11-15 | `used_eq_from_initial`, `melds_eq_from_initial`, `taatsu_eq_from_initial` | 初期状態からの選択列に対する状態不変条件の簡約形を追加。 |
| 2026-11-15 | `MentsuHandChoiceStateMatches`, `state_matches_from_initial` | 状態不変条件を一つの述語へパッケージ化。 |
| 2026-11-15 | `applyMentsuHandChoice.state_matches_cons` | 1回の選択遷移に対する状態不変条件の保存を証明。 |
| 2026-11-15 | `applyMentsuHandChoice_skip_fields` | タイル順探索の `skip` 遷移がブロック状態を保持することを証明。 |
| 2026-11-15 | `applyMentsuHandChoice.skip_state_matches` | `skip` 後も同じ分解接頭辞との状態対応を保持することを証明。 |
| 2026-11-15 | `exists_skip_state_matches_of_reachable` | 到達済み状態での `skip` 妥当性と状態不変条件を接続。 |
| 2026-11-15 | `applyMentsuHandChoice.state_matches_append_single` | 状態不変条件を接頭辞の末尾追加形式へ変換。 |
| 2026-11-15 | `valid_next_choice_of_state_matches` | パッケージ化した状態不変条件を選択妥当性へ接続。 |
| 2026-11-15 | `AppliesMentsuHandChoicesForward`, `state_matches_from_initial` | 接頭辞を左から右へ処理する前向き選択列関係を追加。 |
| 2026-11-15 | `AppliesMentsuHandChoicesForwardWithCopyLimit` | コピー制限付きの前向き選択列関係を追加。 |
| 2026-11-15 | `reachableWithinWithCopyLimit_of_forward_choice_path` | コピー制限付き前向き選択列を制約付き到達性へ変換。 |
| 2026-11-15 | `AppliesMentsuHandChoicesForwardWithCopyLimit.state_matches_from_initial` | コピー制限付き選択列の状態不変条件を証明。 |
| 2026-11-15 | `reachableWithinWithCopyLimit_append_choice` | 妥当な選択を制約付き到達性へ接続。 |
| 2026-11-15 | `mentsuHandChoiceTaatsus`, `taatsuHistory_reverse_from_initial` | 選択列の搭子列と探索状態の `taatsuHistory` を対応付け。 |
| 2026-11-15 | `prefix_taatsus_sublist`, `completion_respects_from_prefix` | 分解接頭辞からコピー制限付き前向き選択列の妥当性を構成。 |
| 2026-11-15 | `blockChoices_ne_skip` | タイル順探索への挿入対象がすべて非 `skip` であることを証明。 |
| 2026-11-15 | `skips_state_matches` | `skip` 列を状態不変条件付きのタイル順到達性へ拡張。 |
| 2026-11-15 | `skips_pair` | `skip` 列で雀頭状態が保持されることを証明。 |
| 2026-11-15 | `choice_then_skips_state_matches` | 選択適用後の残りタイル列でも状態不変条件を保持。 |
| 2026-11-15 | `insert_choice_state_matches` | 前後の `skip` と代表牌選択を結合してタイル順到達性を構成。 |
| 2026-11-15 | `skips_taatsuHistory` | `skip` 列で搭子履歴対応を保持。 |
| 2026-11-15 | `skips_invariants`, `insert_choice_from_prefix` | 3つの不変条件を統合し、分解接頭辞から代表牌選択を挿入。 |
| 2026-11-15 | `AppliesMentsuHandTileScan.state_matches_append`, `state_matches_from_initial` | 一回走査関係の依存帰納を修正し、状態不変条件を初期状態から最終状態まで接続。 |
| 2026-11-15 | `AppliesMentsuHandTileScan.skips_state_matches` | 到達済み状態からの全 `skip` 走査を一回走査関係へ持ち上げ、状態不変条件と雀頭保存を接続。 |
| 2026-11-15 | `AppliesMentsuHandTileScan.choose_then_skips_state_matches` | 代表牌選択と後続 `skip` 走査を結合し、一回走査の選択分岐を構成。 |
| 2026-11-15 | `AppliesMentsuHandTileScan.append_skips`, `insert_choice_scan_from_prefix` | 分解接頭辞の代表牌選択を前後の `skip` と連結し、一回走査へ持ち上げ。 |
| 2026-11-15 | `insert_blockChoice_scan_from_prefix`, `insert_pair_scan_from_initial` | 分解ブロック選択の一回走査版と、雀頭選択の初期状態基底を追加。 |
| 2026-11-15 | `AppliesMentsuHandTileScan.append` | 一回走査区間を一般化して連結し、選択列も連結する補題を追加。 |
| 2026-11-15 | `append_choice_scan_from_prefix` | 処理済み選択列の走査へ、次の分解ブロック選択を連結する補題を追加。 |
| 2026-11-15 | `mentsuHandChoiceStateMatches_of_perm` | 選択列の順序変更に対する状態カウンタ不変性を追加。 |
| 2026-11-15 | `taatsuCompletionTiles_of_perm` | 搭子列の順序変更に対する補完牌 Multiset の不変性を追加。 |
| 2026-11-15 | `completionRespectsCopyLimit_of_history_perm` | 搭子履歴の順序変更後もコピー制限を保持する補題を追加。 |
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
