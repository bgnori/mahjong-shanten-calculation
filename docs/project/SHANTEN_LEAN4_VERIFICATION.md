# Lean証明の検証記録

この文書は、各成果に対して実施した検証の履歴を記録する。
コマンド・モジュール名・検査対象数は実施当時のものであり、
現在の構成や最新の検査結果を示すものではない。
現在の成果と未解決条件は[進捗台帳](SHANTEN_LEAN4_PROGRESS.md)、
性能の実測は[性能測定記録](SHANTEN_LEAN4_PERFORMANCE.md) を参照する。

## 検証記録

- 2026-11-16、国士無双の最大値13：
  `lake build Shanten` 成功（909 jobs）。既存・移動済みコードの警告と
  Mathlib import形式の警告は残る。
  `lake env lean --stdin` で公開入口からの仕様値の存在・上界の利用、
  具体例の `some 13`、13手では和了できないことを検査した。
  最大値・値の存在・具体例の仕様値・共有の到達定理・不足数の下界の5定理に
  `#print axioms` を実行し、依存は `propext`・`Classical.choice`・`Quot.sound` のみで、
  `sorryAx` や `native_decide` の公理への依存がないことを確認した。

- 2026-11-15、`f79ed59`：追補レビューで
  `lake env lean Shanten/MentsuHand.lean` 成功（約21.3秒、警告83件）。
- 同レビューで、任意の分解にグループ化順列定理を適用できることと、
  具体例の重複度保持・残余列の空性をLeanで確認済み。
- 2026-11-16のアーカイブ整理は文書変更のみ。Leanビルドは再実行していない。
- 2026-11-16、旧計画コード除去後：
  `lake env lean Shanten/MentsuHand.lean` 成功（警告64件）、
  `lake build Shanten` 成功（880 jobs）。
- 残した294宣言の命題・証明本文が、コメントと空白を除いて除去前と一致することを確認。
  公開入口をimportする一時Lean検査で、雀頭が後になるグループ化の重複度保持、
  グループ走査からバッチ走査への変換、完了したバッチ走査から仕様値の存在への接続を確認。
  ターゲットDPの仕様一致とバッチ到達性の定理に `sorryAx` がないことも確認した。
- 2026-11-16、分解から牌種順バッチ走査を構成する統合後：
  `lake env lean Shanten/MentsuHand.lean` 成功。新しい具体例では、
  13枚手「11112222萬 東東 9筒 9索 北」と分解「東雀頭、12萬ターツ4組」について、
  `exists_tileBatchScan_complete` が返す選択列・雀頭・完了条件まで検査した。
  続けて `lake build Shanten` も成功（880 jobs）。既存の警告は残る。
- 2026-11-16、一般ブロック探索の追加：
  `lake env lean Shanten/GeneralMentsuHand.lean` 成功（新モジュールの警告なし）。
  13種の么九牌を各1枚持つ手牌について、旧分解が存在しないことと新探索の全域性を検査。
  雀頭・面子とも該当牌がない場合も、使用牌0枚のまま不足数を2・5と累積することを検査。
  固定面子4組・東1枚の手牌の結果が `some 0`、13萬を123萬へ補う不足数が1、
  同じ面子を再選択しても手牌を二重使用せず累積不足数が4になること、
  完成後5枚を要求する候補が4枚制限で排除されることもLeanで検査した。
  `lake build Shanten` 成功（881 jobs）。ビルドには既存と同種のMathlib import形式の
  警告が残る。公開入口からのimportと全域性定理の適用も検査した。
  遷移不変条件・被覆性・距離集合一致・仕様一致・存在一意性・最適状態の6定理について
  `#print axioms` を実行し、依存は `propext`・`Classical.choice`・`Quot.sound` のみで、
  `sorryAx` がないことを確認した。
- 2026-11-16、モジュール分割後：`lake build Shanten` 成功（899 jobs）。
  `Shanten.MentsuHand` だけをimportする検査で、一般手牌の全域性定理の適用と、
  牌種順走査・ターゲットDP・手牌消費付き探索の主要8定理に `sorryAx` がないことを確認。
  旧走査には従来から `tile_mem_mentsuHandTileOrder` の `native_decide` 依存があり、
  今回も変更していない。Mathlib import形式・既存の証明スタイルに関する警告は残る。
- 2026-11-16、七対子の分割・改名後：`lake build Shanten` 成功（908 jobs）。
  `lake env lean --stdin` で `Shanten.SevenPairs` だけをimportし、
  テンパイからの和了定理の適用と改名後のテンパイ目標のカウント補題を検査した。
  分解・最後のドロー・7牌種への到達・6対への到達・保護付き6対への到達の5補題に
  `sorryAx` がないことを `#print axioms` で確認した。
  7牌種への到達には従来の `exists_missing_tile_kind` の `native_decide` 依存が残る。
  他の4補題の依存は `propext`・`Classical.choice`・`Quot.sound` のみ。
  面子手の全モジュールが七対子を直接importしないことも検査した。
  Mathlib import形式・既存の証明スタイルに関する警告は残る。

- 2026-11-16、レビューR1修正後：
  `lake build Shanten.Exchange Shanten.SevenPairs.Reachability` 成功（881 jobs）、
  回帰例を含む `lake build Shanten` 成功（909 jobs）。
  保存定理・共有到達・一般探索の仕様一致／全域性／最適状態・バッチ走査・七対子上限・
  国士最大値の主要14宣言を `lake env lean -j2 --stdin` の `#print axioms` で検査し、
  `sorryAx` 依存なし。新しい保存・完成経路接続の4補題は公理依存もない。
  既存のバッチ走査・七対子の `native_decide` 依存と、既存の警告は残る。
  修正前の基準はレビュー対象コミット `f3f49369dffb45c3ca04f89571471b2c122ee6cc`。

- 2026-11-16、レビューR3設定後：
  Go 1.26.4で `go test ./...` / `go vet ./...` 成功。
  `lake build Shanten.ProofChecks` 成功（909 jobs）、
  公開入口を含む `lake build` 成功（911 jobs）。
  `actionlint` v1.7.12でワークフロー検証成功。
  一時的なLean入力で、`sorry` を持つ定理を経由した別定理への
  `assert_no_sorry` が `contains sorry` エラーで非ゼロ終了することも検査した。
  GitHubホスト上のワークフロー実行はpush後に確認する。既存の警告は残る。
  修正前の基準コミットはR1対応済みの `7f06247`。

- 2026-11-16、レビューR2の段階導入後：
  `lake build Shanten.Capacity` 成功（879 jobs）、
  公開入口・既存証明・主要23宣言の証明穴検査を含む `lake build` 成功（915 jobs）。
  新たな主要9宣言を `#print axioms` で検査し、依存は
  `propext`・`Classical.choice`・`Quot.sound` の範囲のみ。
  `sorryAx`・新規の `native_decide` 依存なし。
  公開入口からA/Bの値1・0の一意性の適用も検査した。
  既存の警告は残る。修正前の基準コミットはR3対応済みの `29235ad`。

- 2026-11-16、順序4冒頭の容量付き一般探索接続後：
  `lake build Shanten.Capacity` 成功（896 jobs）、
  既存証明と主要31宣言の証明穴検査を含む `lake build` 成功（918 jobs）。
  新たな主要8宣言を `#print axioms` で検査し、依存は
  `propext`・`Classical.choice`・`Quot.sound` のみ。新たな `native_decide` 依存なし。
  公開入口から、追加の目標存在仮定なしの全域性定理の適用と、
  A/Bの探索結果から容量付き仕様値1・0への接続も検査した。
  既存の警告は残る。修正前の基準コミットは `21c3043`。

- 2026-11-16、14枚相当の面子手・打牌選択接続後：
  `lake build Shanten.Capacity.Fourteen` 成功（895 jobs）、
  `lake build Shanten.Capacity.Discard` 成功（896 jobs）、
  回帰例を含む `lake build Shanten.Capacity` 成功（898 jobs）。
  既存証明と主要42宣言の証明穴検査を含む `lake build` 成功（920 jobs）。
  新たな主要11宣言を `#print axioms` で検査し、依存は
  `propext`・`Classical.choice`・`Quot.sound` のみ。新たな `native_decide` 依存なし。
  公開入口から、未完成の任意の有効14枚相当入力に対して、
  元の値を達成する合法打牌が得られることも検査した。
  既存の警告は残る。修正前の基準コミットは `898fc75`。

- 2026-11-16、七対子・国士無双の一般計算接続後：
  `lake build Shanten.Special` 成功（881 jobs）、
  `lake build Shanten.Capacity.Special` 成功（884 jobs）、
  回帰例と主要52宣言の証明穴検査を含む `lake build Shanten.ProofChecks` 成功（920 jobs）。
  最終的な `lake build` 成功（922 jobs）。
  新たな主要10宣言を `lake env lean -j2 --stdin` の `#print axioms` で検査し、
  依存は `propext`・`Classical.choice`・`Quot.sound` の範囲のみ。
  新たな `native_decide` 依存なし。既存の警告は残る。
  13枚・14枚の回帰計算から容量付き仕様への適用も検査した。
  修正前の基準コミットは `4d9c543`。

- 2026-11-16、3形の総合値接続後：
  `lake build Shanten.Capacity.Overall` 成功（902 jobs）。
  最終的な `lake build` 成功（923 jobs）。主要65宣言の証明穴検査を通過。
  新たな主要13宣言を `lake env lean -j2 --stdin` の `#print axioms` で検査し、
  依存は `propext`・`Classical.choice`・`Quot.sound` のみ。
  新たな `native_decide` 依存なし。既存の警告は残る。
  固定文脈の既存探索結果と、各形の構造的完成・特殊形の閉形式から、
  公開された総合計算の期待値への接続も検査した。
  修正前の基準コミットは `f22a660`。

- 2026-11-16、Lean側の37種入力検証・正規化接続後：
  `lake build Shanten.Input37.Validation` 成功（878 jobs）、
  `lake build Shanten.Input37.Correctness` 成功（905 jobs）、
  `lake build Shanten.Input37.Examples` 成功（906 jobs）。
  最終的な `lake build` 成功（928 jobs）。主要87宣言の証明穴検査を通過。
  新たな主要22宣言を `lake env lean -j2 --stdin` の `#print axioms` で検査し、
  依存は `propext`・`Classical.choice`・`Quot.sound` のみ。
  新たな `native_decide` 依存なし。既存の警告は残る。
  Goソース・開発コンテナは未変更。修正前の基準コミットは `7a71446`。
