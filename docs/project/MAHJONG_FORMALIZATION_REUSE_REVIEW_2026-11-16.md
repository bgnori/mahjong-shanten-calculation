# mahjong-formalizationとの共通化可能性調査

**調査日:** 2026-11-16

**shanten対象:** `78bb8046049c987e647a9d576bc5c2d1a41b580d`

**比較対象:** [bgnori/mahjong-formalization][formalization]、
`bd84dd915b8fade0a8d04746a60021e4028848e7`

> **補足・訂正（2026-11-16）:** 本調査はInt37の意味の違いを確認したものではない。
> 両者は同じ牌種値を、枚数列とカウント配列という異なる容器で受け取る。
> また分類側も解析対象牌姿とその完成形について4枚制約を検査している。
> 固定面子を別文脈として受け取らないという範囲の違いと、
> 分類結果が4枚制約を破ることは異なる。
> ドメイン語彙の安定化を目的に優先順位を見直した
> [独立Lean共通核の計画案](MAHJONG_DOMAIN_CORE_PLAN_2026-11-16.md)を参照。

## 1. 結論

**共通化する価値はある。ただし、計算器・分類器全体ではなく、
「牌と通常形の和了分解の意味論」を中心とする小さな共通核が適切である。**

現時点で最も費用対効果が高いのは、入力の対応仕様と共通回帰データを整備し、
両実装を相互検証に使うこと。独立した共有パッケージへの切り出しは、
Lean環境の整合と対応定理の検証を先に行い、その結果で判断することを推奨する。
単に似た型の重複を消すだけでは、既存証明と公開APIの移行費用を正当化しにくい。

| 対象 | 共通性・利点 | 判断 |
|---|---|---|
| 34牌種、順子・刻子・対子 | 同じ有限領域と牌の多重度。基礎定義・列挙・保存補題の二重保守を減らせる | 小さな共通核の有力候補 |
| 通常形の和了分解仕様 | ともに「雀頭1個＋所定数の順子／刻子」。待ちとシャンテン0の接続点になる | 最も意味のある共有境界 |
| 37種から34種への正規化 | 添字配置と赤1・通常5が3・合計4の意味が一致する | 対応仕様・テストを先行。検証器丸ごとの統合はしない |
| 通常形テンパイの検証データ | 分類側の複数待ち・複数分解・5枚目排除を計算側の検証にも使える | 今すぐ着手する価値が高い |
| 探索・重複除去の実装 | 発想を転用できるが、必要な情報と計算目的が異なる | 選択的に再利用。共通実装化は後段 |
| 最短距離、特殊形、固定面子容量 | 分類側に同じ契約がない | shanten側に残す |
| 待ち核、既約性、病的構造、分類ID | shanten値の計算には不要 | 分類側に残す |
| レポート生成、分散計算、Viewer | 分類の全列挙研究に固有 | 共通化しない |

今回行ったのは調査と文書化であり、共通ライブラリの実装、依存追加、
両Leanモデルの同値証明、Go計算器への接続は行っていない。

## 2. 調査範囲と前提

### 現在地を取り違えないための整理

- shantenのGoは[型とインターフェースだけ](../../shanten.go)で、数値計算器は未実装。
  Leanには、固定面子容量、13・14枚相当の通常形探索、特殊形、総合値、
  37種入力の検証・正規化が既にある。
  [既存レビュー](PROJECT_REVIEW_2026-11-16.md)は当初の指摘と対応結果を併記するため、
  古い「未対応」の記述だけを現在の不足として扱わなかった。
- 分類側は[Leanを仕様の正本][f-readme]とし、Go・Python等を従属実装としている。
  Leanの通常形待ち判定は1・4・7・10・13枚を対象とするが、
  [Goの公開入力][f-go-input]は4・7・10・13枚である。両者の範囲は同一ではない。
- 今回は両者の基礎型、完成・待ち・距離仕様、主要探索、正規化、分類の情報保持、
  テスト、依存設定を読んだ。分類の全証明・全計算基盤の監査ではない。
- 外部ソースへのリンクは上記コミットに固定した。shanten内リンクは相対リンクであり、
  行番号と評価は上記対象コミットを基準とする。

## 3. 実装上の対応関係

### 3.1 牌・面子はほぼ同じ数学的対象

| 概念 | shanten | mahjong-formalization |
|---|---|---|
| 数牌 | `Tile.suited Suit (Fin 9)` | `Tile.numbered Suit Rank`、`Rank = Fin 9` |
| 字牌 | `Tile.honor (Fin 7)` | `Tile.honor Honor`、東〜中の7コンストラクタ |
| 順子 | `Meld.sequence Suit (Fin 7)` | `MentsuCandidate.shuntsu (Shuntsu.shuntsu Suit (Fin 7))` |
| 刻子 | `Meld.triplet Tile` | `MentsuCandidate.koutsu Tile` |
| 対子 | `pairTiles Tile : Multiset Tile` | `Toitsu.toitsu Tile`とその`List Tile` |
| 物理牌 | 入力37種で赤を区別。構造計算は34牌種 | `PhysicalTile = Tile × Fin 4`。構造計算は34牌種 |

根拠はshantenの[Core](../../Shanten/Core.lean#L10)と、
分類側の[Basic][f-basic]・[Pattern][f-pattern]。
スート・字牌を明示的に対応させれば牌種間の全単射を構成でき、
順子開始位置もともに0〜6なので面子も対応する。
これは構造上の対応の確認であって、今回Leanで全単射を証明したという意味ではない。

ただし、型だけを移動しても効果は限定的である。
shantenの[Core](../../Shanten/Core.lean)には七対子・国士の式と補題も入り、
分類側の[Basic][f-basic]には表示・物理牌・列挙順も入る。
**どちらのファイルも丸ごと共通パッケージに移す単位ではない。**

### 3.2 手牌は同名でも別の責務を持つ

shantenの[Hand](../../Shanten/Core.lean#L32)は牌種別自然数カウントと固定面子数。
[容量付きモデル](../../Shanten/Capacity/Basic.lean#L28)が固定牌の内容を外部文脈として持ち、
手元牌と固定牌の合算4枚制限を課す。

分類側の[Hand][f-hand]は、面子数と、所定枚数の物理牌への埋め込みを持つ。
一方、主要なFinderの入力はこの型ではなく`List Tile`であり、
[合法性][f-legality]を別途判定する。物理牌への埋め込みがなくても待ち探索は呼べる。

分類側の面子数`n`は**解析する残余形に含める面子数**であり、
shantenの固定面子数`m`とは異なる。有効な13枚相当の通常形入力を比較するなら、
`n = 4 - m`、手元枚数は`3*n + 1`という対応になる。
分類側の4・7・10枚形は、それだけで固定面子の具体的内容を表してはいない。

したがって、共有するなら牌カウント・多重集合への変換と保存則であり、
両`Hand`を同一の大きな構造体にする必要はない。

### 3.3 最大の接点は通常形の和了分解

shantenの[Complete](../../Shanten/Specification.lean#L19)の通常形分岐は、
牌数上限と「雀頭＋面子列の牌多重集合との一致」を要求する。
分類側には[WinningPartitionSpec][f-partition]と、
実行列挙との同値定理`mem_winningPartitions_iff_spec`がある。
こちらは部品を連結した牌列と入力の`List.Perm`で同じ多重度を表す。

共有しやすい仕様は、例えば次の数学的関係である。

> `StandardCompletion(n, counts)`：
> ある雀頭1個と面子n個が存在し、それらを展開した牌種別枚数がcountsと一致する。

4枚制限は別の有効性述語として組み合わせる。
分類側の`IsStandardAgari`単体は列挙結果の非空性であり、
手牌合法性や5枚目の排除まで含むのは[IsWaitFor][f-wait]側である。
共有時に、和了分解可能性と合法な手牌という二つの条件を混同してはならない。

分類側はこの関係から**全分解と待ち牌**を必要とする。
shantenは完成候補ごとの不足枚数の**最小値**を必要とする。
共有仕様を持ち、実行アルゴリズムは別でもよい。

### 3.4 正規化は共通性が高いが、入力コンテナは異なる

shantenの[Input37](../../Shanten/Input37/Basic.lean#L22)と
分類側Goの[countsFromInt37][f-go-int37]は、ともに次を採用する。

- 0・10・20が赤5、1〜9・11〜19・21〜29が通常数牌、30〜36が字牌。
- 赤5は1枚、通常5は3枚、その他は4枚まで。構造判定では赤を通常5へ統合する。
- 赤2枚や通常5が4枚という不正は、統合後の4枚制限だけでは検出できない。

ただしshantenは符号付き37要素カウントと固定面子群、
分類側Goは**1枚ごとのInt37値の列**である。同じ37要素配列APIではない。
さらに分類側のTenhou入力は物理IDの重複を拒否するが、
Int37入力では同じ値の反復が通常の複数枚表現になる。

再利用対象は添字写像・容量規則・正規化保存則と検証データ。
shantenの負数検査、各入力欄の非負性、固定牌との合算、面子構造・枚数検査を、
分類側の入力関数で代替してはいけない。

## 4. そのまま共通化できない重要な境界

### 4.1 牌姿内で合法な待ちと、固定牌込みで合法な待ちは対象範囲が異なる

既存レビューのA/Bがそのまま共通化の受入条件になる。

| 入力 | 手元 | 固定面子 | 容量付き通常形shanten |
|---|---|---|---|
| A | 東1 | 東東東・123萬・123筒・123索 | 1 |
| B | 東1 | 南南南・123萬・123筒・123索 | 0 |

shantenでは[値と実探索結果](../../Shanten/Capacity/Examples.lean#L84)の両方を区別している。
分類側Leanへ残余形の「東1」だけを渡せば、[通常形待ち仕様][f-wait]では東待ちになる。
しかしAでは東を足すと固定牌を含めて5枚になる。分類側はその固定文脈を受け取らない。
なお「東1」は分類側Go公開APIでは枚数エラーになるため、
この比較を既存Go APIへそのまま投入することもできない。

有効な13枚相当入力、牌種変換・カウント一致、`n = 4 - m`を前提に、
将来接続すべき待ち集合の関係は次である。

```text
容量付きの待ち集合(fixed, L)
  = 分類側の通常形待ち集合(L)
      のうち、count(L, t) + count(fixed, t) < 4 を満たす牌種t
```

入力が既に合算容量を満たせば、加牌で新たに制限を破り得るのはその牌種だけなので、
待ち集合の段階ではこのフィルタを接続点にできる。
これは今回の定義比較から得た**接続案**であり、証明済みのリポジトリ間定理ではない。
非テンパイ入力の最短距離まで得るには、現在の待ちをフィルタするだけでは足りず、
shantenのように[完成目標・遷移・経路](../../Shanten/Capacity/Specification.lean)にも容量が必要。

### 4.2 通常形テンパイと総合shanten 0は同じではない

分類側の`IsTenpai`は通常形限定。shantenの総合値は七対子・国士無双も含む。
例えば`1122334455667z`は七対子テンパイだが通常形テンパイではなく、
么九13種各1枚も国士テンパイだが通常形ではない。
分類側の`ErrNotTenpai`を総合shantenが正である証拠にしてはいけない。

比較するのはまず**通常形の値0**と通常形待ちの存在。
13枚相当という前提も必要で、完成14枚の値−1や打牌後の最適値は別の接続である。
shanten側の[14枚仕様](../../Shanten/Capacity/Fourteen.lean)・
[最適打牌](../../Shanten/Capacity/Discard.lean#L150)は分類器にはない。

### 4.3 分解情報を潰してよい範囲が異なる

shantenの[一般探索状態](../../Shanten/MentsuHand/Search/BlockSearch.lean#L21)は
完成牌多重集合・使用牌・不足枚数を保持する。
同じ完成牌を作る異なる面子分解を同一状態にしても、最小不足枚数には支障がない。

分類側は[待ち牌＋正規化済み和了分解][f-completion]を保持し、
さらに待ち牌がどの部品を不完全にしたかを[展開][f-component-kind]する。
同じ完成牌多重集合から異なる待ち分解が生まれ得るため、
shantenの状態集合だけから分類結果を復元することはできない。

共通列挙器を作るなら、全分解を保持する仕様の上に、shanten用の射影・最小化を置く。
ただし全分解保持が数値計算を遅くするなら、実装まで統一しない。
分類側の[正規化][f-canonical]も、**部品順序だけを同一視し、同じ部品の個数は保存する**。
また[Goのコード集計][f-go-analysis]は「待ち牌・コード」の組を重複除去してから
コードを並べるので、異なる待ち牌に同じコードがあればコード値は重複し得る。
単なる集合化による共有は出力の意味を変えてしまう。

### 4.4 面子除去・ターツ・エラーの意味も統一しない

- 分類側の[待ち核保存除去][f-reduction]は、面子を牌姿から取り去った別の小さい牌姿を比較する。
  shantenで面子を「固定」する操作とは異なる。除去牌の容量を保持しないので、
  分類の可約性から固定面子ありの値不変性は導けない。
- shantenの旧[Taatsu](../../Shanten/MentsuHand/Basic.lean#L11)の`sequence`は連続2枚と一意の補充先。
  分類側の両面・嵌張・辺張とは同じ型ではない。一般探索が嵌張を扱えることと、
  この旧型を全待ち分類へ流用できることは別である。
- 分類側の非テンパイは分類APIではエラーだが、shanten計算器には通常の成功入力。
  分類不明・還元曖昧という分類固有エラーもshantenの
  [エラー契約](../../shanten.go#L61)には持ち込まない。
- 暗槓を含む固定面子と特殊形の適用除外、槓の4枚占有はshantenに残す。
  分類側の完成面子候補は順子・刻子であり、固定槓のモデルではない。

## 5. 再利用方法の比較

| 案 | 利点 | 費用・問題 | 評価 |
|---|---|---|---|
| 現状維持 | 移行不要、独立して変更できる | 意味論の乖離・重複検証が続く | 共有テストだけでも追加したい |
| 定義をコピー | 初期導入は軽い | 修正追従・出典・証明の二重管理が残る | 恒久策にはしない |
| 分類リポジトリへ直接依存 | 型・分解仕様を再利用できる | Lean版差、グローバル名、研究用APIの変更に結合する | 最小importでも環境整合が必要。現時点では非推奨 |
| 小さな独立Lean共通核 | 依存方向が明確、仕様・基礎証明を一元化できる | 抽出、互換層、証明移行、リリース調整が必要 | 対応検証後の有力案 |
| 全解析エンジンの統合 | 一見すると重複が最小 | 距離と全分解の情報量・容量・用途を混同しやすい | 非推奨 |

### 移行費用を左右する実際の障害

1. **Lean／Mathlibの版差。** shantenは
   [v4.35.0](../../lean-toolchain)／[Mathlib v4.35.0](../../lakefile.lean)、
   分類側は[v4.28.0][f-toolchain]／[Mathlib v4.28.0][f-lake]。
   同じLake依存グラフで両者の別バージョンをそのまま維持できるとは考えない。
   一方への版合わせと関連証明の再ビルドを独立工程にする必要がある。
2. **名前と表現。** 分類側の`Tile`・`Suit`・`Hand`はルート名前空間、
   shantenは`Shanten`名前空間。単なる`abbrev`では異なる帰納型が同一になるわけではない。
   共通型への移行か、双方向変換と対応補題が必要になる。
3. **証明の依存と信頼境界。** shantenは
   [ProofChecks](../../Shanten/ProofChecks.lean)で主要出口の推移的`sorryAx`を拒否する。
   分類側の[標準順キーの単射性][f-canonical]には`native_decide`が使われる。
   共有後も証明穴の不在とネイティブ計算への依存を区別して検査すべきで、
   移動だけで保証が強くなるわけではない。
4. **Goの契約を重くしない。** 分類側のGoコアは非公開の`handCounts`や分解関数。
   現行公開APIへの依存だけでは計算エンジンを取り出せない。
   shantenの契約モジュールは標準ライブラリのみという性質を保ち、
   再利用するとしても将来の実装・アダプタ側に置く。
5. **ライセンス。** 分類側には[MIT License][f-license]があるが、
   調査時点のshantenには追跡されたLICENSE／COPYINGファイルがない。
   コード抽出前に共有先のライセンス方針を確認し、移植元の表示・許諾条件を保持する。
   同じGitHub所有者であることだけを権利確認の代わりにしない。

これらから、抽出工数を行数だけで見積もるのは不適切。
現段階では日数や高速化率を見積もれる実測根拠はなく、
**共有テストは低費用、型・証明の抽出は中〜高費用、探索全統合は高費用**と評価する。

## 6. 推奨する段階導入と受入条件

### 段階1：依存を増やさず、比較可能な仕様・回帰データを作る

最初の実装タスクとして推奨する。両Lean版の統一を前提にしない。

- 34牌種の順序、37種の写像・容量、残余面子数の対応、比較対象を通常形に限定する条件を明文化。
- 言語中立の回帰データに入力形式・対象形・期待結果・生成元コミットを記録する。
  分類IDではなく、まず牌種カウント、合法性、通常形待ち集合、通常形テンパイ真偽を比較する。
- 分類側の[既存Finder例][f-finder-tests]・[Go回帰例][f-go-tests]を活用する。
  例：`1223m`、`3456678m`の複数待ち、5枚目排除、赤5の置換、
  同じ牌姿の順列。1枚形はLean向けに分離する。
- shanten側のA/B、槓、赤2枚・通常5が4枚、負数、特殊形だけのテンパイは、
  対応範囲外や意味の違いを誤って同一視しないための負例にする。

**受入条件:** 共通範囲で待ち集合と通常形値0が一致し、範囲外は明示的に区別されること。
ただし現在のshanten Goには計算器も待ちAPIもないため、
Go分類器と即座に数値差分テストできるという意味ではない。
当面はLeanの限定した計算例・証明例を使い、将来のGo実装の適合データにもする。
小さい残余形から始め、13枚の全列挙を初期受入条件にしない。
同一の共有実装を両側で呼ぶだけのテストにせず、独立したオラクルも残す。

### 段階2：Lean対応定理を検証し、小さな共通核の抽出を判断する

版合わせの試行後、最低限、次を機械検証する。

1. 牌種変換の往復、面子展開と牌種変換の可換性、枚数・多重度の保存。
2. `List.Perm`／`Multiset`／牌カウントを介した通常形分解仕様の同値。
3. 有効13枚相当入力に対する通常形shanten 0と、容量フィルタ後の待ちの存在の同値。
4. 分類結果の正規化で部品多重度・異なる分解・待ち牌ごとの情報を失わないこと。

抽出する場合の責務と依存方向は次に限定する。

```text
小さな共通核：牌種・面子・展開・多重度・通常形分解仕様
  ├─ shanten：固定容量・最短距離・特殊形・最小化・37種入力全体の検証
  └─ 分類：待ち分解・待ち核・既約性・病的構造・分類コード・全列挙
```

入力37種の写像・容量補題も候補だが、物理牌IDや各APIのエラー・手牌枚数制約は
利用側に残す。最初から可変ルール数・任意牌セット等の汎用エンジンにはしない。

**抽出へ進む条件:** 両側が同じ核を実際に利用でき、版整合後のビルド・主要出口証明が通り、
互換層で既存の値・分類コード・ID・入力拒否挙動を維持できること。
移行パッチが広がりすぎる場合は段階1の共有仕様・相互検証に留める判断も妥当。
コミット固定で導入し、研究用レポート生成をshantenの依存やCIへ巻き込まない。

### 段階3：性能上の再利用は測定後に行う

分類側の[直接生成][f-direct]は「完成形から1枚を除く」生成をFinderへ接続する。
さらに[計算共通処理][f-computation]は、非減少面子列、ストリーミング、
牌姿キーによる集約を使う。これらはshantenの完成候補列挙・重複削減の参考になる。
Go分類器の[先頭非ゼロ牌からの分解][f-go-partitions]も、和了判定の実装候補になる。

ただし、直接生成はテンパイ側の全列挙、shantenは任意入力からの最小距離という目的差がある。
分類コード表をシャンテン表として使うことはできず、
分類レポートの計算時間も1手牌のシャンテン計算性能を示さない。
待ち核キャッシュや分類用キーをそのまま容量付き計算のキャッシュに流用もしない。
後者では少なくとも手元牌と固定牌の残余容量等、値を決める文脈が必要。

**受入条件:** 同じ入力群・資源上限で時間とピークメモリを測定し、
既存仕様との一致を維持した上で効果が確認できること。
現段階ではアルゴリズムの知見の再利用を勧めるのであって、高速化を実証したものではない。

## 7. 今回の検証と限界

比較リポジトリはセッション用領域へshallow cloneし、上記HEADを確認した。
双方のソースを変更せず、分類側で以下の既存テストを選択実行した。

```sh
GOTOOLCHAIN=local GOCACHE=<セッション専用キャッシュ> \
  go test -p 1 ./mahjong \
  -run 'Test(Int37MappingCoversEveryTenhouPhysicalID|Int37Validation|Int37APIsMatchTenhouAPIs|Int37RedFiveSubstitutionPreservesClassification|PathologyProfiles|InvalidAndNonTenpaiInputs)$' \
  -count=1 -v
```

**結果：6テストすべて成功（入力形式一致のサブテスト5件を含む）。**
136物理IDのInt37対応、赤・通常5の容量、不正入力、両入力形式の分類一致、
赤置換不変性、病的プロファイルを確認した。
これはGo従属実装の限定的な実行確認であり、両リポジトリ間の形式的同値の検証ではない。

最初の実行は作業ディレクトリの指定漏れでshanten側のGo要件に当たり、
ローカルGo 1.24.5では要件1.26.4不足として失敗した。
比較リポジトリ（要件1.22）へ移動して上記を実行し成功した。
この指定漏れを比較対象側の不具合とは扱わない。依存や共有環境の設定は変更していない。

今回、Leanの版合わせ・再ビルド、全証明の公理依存監査、
全Goテスト、重い分類全列挙、性能ベンチマークは行っていない。
文書のみの追加なのでshanten本体の再ビルドは行っていない。
既存レビューのビルド結果を今回の実行実績としては数えていない。

## 8. 最終提案

**次の一手は「共有ライブラリを作る」ではなく、
通常形の意味論をつなぐ対応仕様と、小さい共通回帰ケースを作ること。**

その成果で両者の境界を固定し、Lean環境を整合できた段階で牌・面子・和了分解仕様だけを抽出する。
これなら共通化の価値である「仕様の乖離防止・証明部品の再利用・相互検証」を得つつ、
シャンテン距離とテンパイ分類という別の責務を維持できる。

## 参照：比較リポジトリの固定ソース

[formalization]: https://github.com/bgnori/mahjong-formalization/tree/bd84dd915b8fade0a8d04746a60021e4028848e7
[f-readme]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/README.ja.md#L1
[f-basic]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/Basic.lean#L51
[f-pattern]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/Pattern.lean#L141
[f-hand]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/Hand.lean#L16
[f-partition]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/WaitCompletionFinder.lean#L259
[f-legality]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/WaitCompletionFinder.lean#L323
[f-wait]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/WaitCompletionFinder.lean#L351
[f-completion]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/WaitCompletion.lean#L159
[f-canonical]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/WaitCompletion.lean#L20
[f-component-kind]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/WaitDecompositionCode.lean#L140
[f-reduction]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/WaitDecompositionCode.lean#L695
[f-direct]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/Mahjong/DirectWaitGeneration.lean#L808
[f-computation]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/MahjongComputations/Common.lean#L98
[f-go-input]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/mahjong/README.md#L1
[f-go-int37]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/mahjong/classifier.go#L136
[f-go-analysis]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/mahjong/classifier.go#L364
[f-go-partitions]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/mahjong/classifier.go#L423
[f-finder-tests]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/MahjongTests/WaitCompletionFinder.lean#L35
[f-go-tests]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/mahjong/classifier_test.go#L109
[f-toolchain]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/lean-toolchain#L1
[f-lake]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/lakefile.lean#L1
[f-license]: https://github.com/bgnori/mahjong-formalization/blob/bd84dd915b8fade0a8d04746a60021e4028848e7/LICENSE#L1
