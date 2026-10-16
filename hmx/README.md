# HMX 博士論文の原文転記

原典は親フォルダの `main.pdf`（Martin Sulzmann、May 2000）に固定する。第3・4章、必要な背景（印刷8〜16ページ）、付録（182〜226ページ）を対象とする。既存 EHMX とは独立した Lake プロジェクトである。

**定義・仮定・定理文を再照合し、発見した転記の欠落・追加条件を修正。証明は未着手。** 前回の完了判定では例の欠落と仮定の接続漏れを見逃していた。今回は例1–18も含め、番号付き119項目の144出現（記述・再掲140、既出番号への参照4）、15図、番号のない条件・規約57件を対応表に記録した。数学的結果は `def ... : Prop` であり、証明でも追加公理でもない。

原典に明示されない記号は引数にし、誤記候補は修正せず残す。以前の草案で追加した D4 の相異条件、一般化の分割前の同値、補題30や図4.2の修正などは撤回した。定義23の二つの表示は別に収録している。

## 完了の意味と限界

番号の対応だけでなく、定義の適用範囲、節の共通条件、式の各成分、本文と付録の表記差を照合した。意味論の条件の欠落、Weakening、制約形式の導出、定義23の版の参照、付録の因子分解などを修正した。各出現の照合内容は `audit/items.json`、発見した問題と対応は `audit/review.json` にある。

今回の再照合では、HERBRAND、DIM・INDEXの二つのソートの構文、例7–9の初期環境、比較の例10–18と本文中の例の定義を追加した。95頁の正規化の計算可能性と付録の節の仮定を対応する命題へ接続し、図4.1のΓ/Γxの違いを保存した。図4.3–4.5に印刷されていない二条件は削除し、δの定義域と式の重みの正値条件も明示した。原典の誤記候補は修正していない。

- 意味論の `Meaning.ModelConditions` はCPO領域方程式の抽象条件、項・型の意味関数の定義式、初期環境を結び、補題6・7・9・定理5・系2の前提へ接続する。背景HMにも対応する条件を置いた。モデルの構成・存在証明や、ideal性・健全性の証明は含めない。
- `let-realizable` の「monomorphic context」と還元の文脈閉包は原典に詳細がなく、明示的な引数としている。
- 未定義記号、本文と付録の違い、補題22の用語、領域の和・最小性の読みなどは `audit/ambiguities.json` に記録した。補題27と定理17の付録の別表記は別の命題である。誤記候補の数学的修正はしていない。
- 原文の式を保存することと、その主張や採用した読みの数学的妥当性を検証することは異なる。後者は今回の完了条件に含めない。証明段階で背景モデルと記号の読みを先に検討する。

## 確認方法

```sh
cd hmx
lake build
UV_CACHE_DIR=/tmp/ehmx-uv uv run --offline --no-project python scripts/check_audit.py --require-complete --lean-checks
UV_CACHE_DIR=/tmp/ehmx-uv uv run --offline --no-project python -m unittest discover -s scripts -p test_check_audit.py -v
UV_CACHE_DIR=/tmp/ehmx-uv uv run --offline spec/build_pdf.py
```

検査は原典のハッシュ、番号付き項目の全出現、対応するLean宣言、証明・公理による穴埋めの不在を確認する。`--require-coverage` は収録検査。`--require-complete` はさらに全項目・図・規約の照合記録、未修正の転記問題の不在、照合時点のLean・原典ページ・記録のハッシュを確認する。変更後の古い照合記録は失敗する。原典の問題を記録した状態は許容するが、未修正の実装上の欠落は許容しない。

これらの機械検査は人による式の照合や数学的証明の代わりにはならない。原文抽出には否定記号や添字の文字化けがあるため `main.pdf` が正本である。`review_method` と `visual_check` はテキスト照合とページ画像での確認を区別する。

`Example` の全出現も原典から列挙し、未登録の例を検出する。さらに `connections.json` の36宣言について、必要な条件がLeanの命題本体に使われているかを確認する。単なる引数の型やコメントの記載では合格しない。

## 対応資料

- `audit/source.json`: 原典・対象範囲・転記状態・数学的検証の状態。
- `audit/items.json`: 番号付き項目の位置、原文、Lean宣言。本文と再掲を分ける。
- `audit/figures.json`: 推論規則と関係図。背景の図2.1〜2.3も含む。
- `audit/conventions.json`: 番号のない条件、表記規約、証明中の注意。
- `audit/ambiguities.json`: 原文の問題、今回の扱い、撤回した修正案。
- `audit/review.json`: 再照合で発見した差、修正状況、照合範囲。
- `audit/modules.json`: Leanファイルから原典へ戻るための対応。
- `audit/connections.json`: 原典の条件と、実際に参照する命題・定義の接続。
- `output/pdf/hmx-statement-audit.pdf`: 上記の対応表とLeanファイルのハッシュを載せたPDF。

`transcribed` は転記を収録した状態、`reviewed` は照合記録あり、`reviewed_with_source_note` は原文の問題・読みを伴う照合である。`recorded_for_proof_review` は数学的検討を残した状態であり、いずれも「証明済み」ではない。
