# W3対応レビュー報告（2026-11-19）

## 結論

確認できた実装は、W3の技術的な受入条件に沿っている。共通核に136／37／34表現と
集約・容量の保存定理があり、shantenと分類側の両方に既存型とのアダプタが導入されている。
確認範囲で、意味の不一致や証明上のブロッカーは見つからなかった。

ただし、consumer側のW3変更は確認時点で各ローカル`main`にのみ存在し、
GitHubの`origin/main`には未反映だった。したがって「ローカルcheckoutでのW3実装完了」と
「他者が取得できる形での公開完了」は区別する必要がある。

## レビュー対象

| 対象 | 確認したリビジョン |
|---|---|
| 共通核 `mahjong-domain-core` | `a21dd8484d22901683eeedd2ed77625245031029`（`origin/main`と一致） |
| shanten | `da9746a61d9a533e712ba584907a3074432ad563`（`origin/main`より3コミット先行） |
| 分類 `mahjong-formalization` | `dc0633de94cd419ba15cd708a9db5e6a601c73ab`（`origin/main`より5コミット先行） |

ソース、共通用語集、両側の用語集リンク、`lakefile.lean`とmanifestの固定SHA、
および共通核の`sorry`検査対象を確認した。W4以降の通常形分解・固定文脈接続は対象外。

## 受入条件ごとの確認

| 条件 | 判定 | 根拠 |
|---|---|---|
| 136物理ID・37スロット・34牌種の対応 | 適合 | 共通核の`PhysicalTileId.int37Index`、`PhysicalTileId.tile`、`Int37Index.tile`と、`tile_int37Index`、`tile_index`、`int37_capacity_count`で対応を証明。 |
| 集約、総数、加算、容量の保存 | 適合 | `aggregateInt37_add`、`aggregateInt37_total`、`aggregateInt37_capacity`、`aggregateInt37_le_four`を定義し、`MahjongDomain/ProofChecks.lean`で`sorry`不在を検査。 |
| shantenアダプタ | 適合 | スート・牌・カウントの往復定理があり、Int37正規化牌・スロット容量・集約カウントの一致を`Shanten/ProofChecks.lean`の`sorry`検査に追加。 |
| 分類アダプタ | 適合 | スート・字牌・牌・カウントの往復を証明。物理牌から共有IDへの変換について、牌種とcopyの保存を証明。 |
| 共有語彙と依存固定 | 適合 | 共通核に英日用語集があり、両consumerが共通核SHA `a21dd8484d22901683eeedd2ed77625245031029`に固定。利用側の用語集は共通文書を参照し、固有語を残す。 |
| 既存計算への影響範囲 | 適合 | W3差分は型アダプタと接続用証明・文書に限定され、shanten探索と分類アルゴリズムの置換は確認されなかった。 |

## 指摘・フォローアップ

### 公開状態の同期（公開前に対応）

shantenはローカル`main`が`origin/main`より3コミット、分類側は5コミット先行しており、
両方にW3のアダプタ変更が含まれる。共通核の固定コミット自体は公開済みだが、
consumer側の変更は公開ブランチから再現できない。

W3の成果を共有・公開済みとして扱う前に、両consumerの変更をそれぞれ公開し、
公開リビジョンと検査結果を記録すること。これは確認時点の公開状態に関する指摘であり、
ローカル実装の正しさを否定するものではない。

## 検証状況と限界

作業記録には、共通核`lake build`、shanten `lake build`（934 jobs）、
分類 `lake build Mahjong MahjongTests`（866 jobs）、分類 `go test ./mahjong`の成功が記録されている。
今回のレビューでは証明・アダプタとその`sorry`検査登録をソース上で確認した。

一方、今回の環境にはホスト側の`lake`と`go`がなく、ビルドおよびGoテストを再実行できなかった。
したがって上記の成功は作業記録に基づくもので、今回の独立した再実行結果ではない。
consumer変更公開後、固定依存の状態で両Leanビルドと分類側Goテストを再実行するのが望ましい。
