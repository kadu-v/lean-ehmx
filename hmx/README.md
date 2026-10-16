# HMX 博士論文の原文転記

原典は親フォルダの `main.pdf`（Martin Sulzmann、May 2000）に固定する。第3・4章、必要な背景（印刷8〜16ページ）、付録（182〜226ページ）を対象とする。既存 EHMX とは独立した Lake プロジェクトである。

**原文の転記を収録した。証明は未着手。** 番号付き101項目（本文・付録の再掲を含む125出現）、15図、番号のない規約・節の前提を対応表に記録した。数学的結果は `def ... : Prop`、説明・注意書きは文字列であり、証明でも追加公理でもない。

原典に明示されない記号は引数にし、誤記候補は修正せず残す。以前の草案で追加した D4 の相異条件、一般化の分割前の同値、補題30や図4.2の修正などは撤回した。定義23の二つの表示は別に収録している。

## 完了の意味と限界

ここでの完了は**収録範囲についての転記完了**である。全命題の成立、原文との数学的同値、原典の省略の解消は主張しない。

- 意味論の `Meaning` は原典の解釈を表す引数。意味関数の式と定理を記述したが、CPOの最小解はまだ構成していない。
- `let-realizable` の「monomorphic context」と還元の文脈閉包は原典に詳細がなく、明示的な引数としている。
- 未定義記号、本文と付録の違い、補題22の用語の読みなどは `audit/ambiguities.json` に記録した。これらを解決済みとはしていない。
- 原文の式を保存することと、後で証明できる仕様を確定することは異なる。証明段階では上記の記号の読み・背景モデルとの接続を先に検討する。

## 確認方法

```sh
cd hmx
lake build
UV_CACHE_DIR=/tmp/ehmx-uv uv run --no-project python scripts/check_audit.py --require-complete --lean-checks
UV_CACHE_DIR=/tmp/ehmx-uv uv run --offline spec/build_pdf.py
```

検査は原典のハッシュ、番号付き項目の全出現、対応するLean宣言、証明・公理による穴埋めの不在を確認する。`--require-complete` は転記の収録検査であり、数学的な正しさの認証ではない。以前の「問題を解決してから仕様を固定する」基準とは分け、ユーザーが指定した「原文の転記を先に完成させる」段階を表す。

## 対応資料

- `audit/source.json`: 原典・対象範囲・転記状態・数学的検証の状態。
- `audit/items.json`: 番号付き項目の位置、原文、Lean宣言。本文と再掲を分ける。
- `audit/figures.json`: 推論規則と関係図。背景の図2.1〜2.3も含む。
- `audit/conventions.json`: 番号のない条件、表記規約、証明中の注意。
- `audit/ambiguities.json`: 原文の問題、今回の扱い、撤回した修正案。
- `audit/modules.json`: Leanファイルから原典へ戻るための対応。
- `output/pdf/hmx-statement-audit.pdf`: 上記の対応表とLeanファイルのハッシュを載せたPDF。

`transcribed` は転記を収録した状態、`recorded_for_proof_review` は原文の問題を記録し数学的検討を残した状態である。`verified` や「証明済み」と読み替えない。
