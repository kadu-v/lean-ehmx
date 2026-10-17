# EHM(X)：HMX を基盤とする形式化

System Fξ を参考に、`perform`・deep handler・値制限付き let を備える EHM(X) を証明するリポジトリです。**EHMX の構文・型付け・制約生成・評価、効果付き進行性、スキーム値代入、β・let・return の保存を実装しています。保存定理、推論の健全性・完全性・主要制約性、任意の到達状態の効果安全性は未証明です。**

基盤は『Advanced Topics in Types and Programming Languages』（ATTAPL）第10章 *The Essence of ML Type Inference* に基づく HM(X) の Lean 4 形式化です。抽象的な制約モデルをパラメータとする型付け・制約生成と、その健全性・完全性・主要制約性を扱います。

## 基盤の取り込みと次の作業

2026年10月17日に `/Users/kikemori/Documents/mprg/lean-hmx` のコミット `1e7ca30ce104e0e48001067eada5eeacc0c3ea9a` を取り込みました。Lean ソース・証明・依存設定・CI・ライセンス・原典対応文書・参考PDFをそのまま引き継ぎ、公開入口と名前空間は `HMX` を維持しています。取り込み元のリポジトリは変更していません。

旧 HMX・EHMX 実装、旧 TeX・生成仕様PDF・監査資料・TODO は撤去しました。旧資産は本リポジトリの Git 履歴（置き換え前のコミット `1c6dec08b0cd1114e110fc389342d353cd040754`）に残っています。ルートの作業指示は維持しています。`docs/references/` のPDFは原典・参考資料であり、新しい EHM(X) の仕様書ではありません。

EHMX は新しい名前空間・公開入口に追加し、HMX の定義と証明は維持しています。型・効果で多相な操作宣言、単一操作の deep handler、値だけを一般化する let と非値の単相 let を扱います。既存の `HMX.ValueRestricted` は EHMX の型付けの値制限として流用していません。

EHMX の [仕様](docs/ehmx-spec.md)、[仕様PDF](output/pdf/ehmx-spec.pdf)、[補題TODO](docs/ehmx-todo.md) に、前提・結論・証明状況と次の使用箇所を記録しています。型・効果代入と多相スキーム値代入は証明済みです。次の中心課題は、操作の量化変数の作用域を保った捕捉継続の型付けと操作簡約の保存です。

```lean
import EHMX

#check EHMX.progressEffectSafety
#check EHMX.emptyEffectProgress
#check EHMX.schemeValueSubstitution
#check EHMX.betaPreservation
#check EHMX.letPreservation
#check EHMX.returnPreservation
#check EHMX.generationWF
#check EHMX.Concrete.framework
```

`progressEffectSafety` は、閉じた型付き項が値・簡約可能・効果に含まれる未処理操作のいずれかであることを証明します。`emptyEffectProgress` は現在の項の進行性であり、未証明の保存定理を必要とする多歩安全性とは区別します。`EHMX.Goals` の `...Goal` は命題の定義であり、証明ではありません。

## 引き継いだ証明の範囲

原典の命題は `def ... : Prop` として保持し、証明を別の宣言に分離しています。制約推論・表現対応の51件と、型クラス固定モデルの構成・適用10件を証明しています。**章全体の証明ではありません。健全性・主要制約性の証明は作用域条件付きの別命題が対象です。**

## 導入とビルド

[elan](https://github.com/leanprover/elan) を導入し、このリポジトリのルートで実行します。初回のツールチェーン・依存ライブラリ・キャッシュの取得にはネットワーク接続が必要です。

```sh
lake exe cache get
lake build
```

Lean は [lean-toolchain](lean-toolchain) の `leanprover/lean4:v4.34.1`、mathlib は [lakefile.toml](lakefile.toml) のコミット `d13f23b723b8a846827a245b89c10fc7d3f11612` に固定しています。推移的依存も [lake-manifest.json](lake-manifest.json) に固定しています。Lake のパッケージ名は `hmx`、ライブラリと既定ビルド対象は `HMX` と `EHMX` です。

```lean
import HMX

#check HMX.Proofs.theorem10_4_4_soundness_scoped
#check HMX.Proofs.theorem10_4_8_completeness
#check HMX.Proofs.constraintGenerationPrincipality_scoped
```

[CI](.github/workflows/lean.yml) は push・pull request 時に、[Lean Action](https://github.com/leanprover/lean-action) で固定ツールチェーンを準備し、mathlib キャッシュを取得して `lake build` を実行します。Lean 内の回帰例もビルド対象です。

仕様PDFは [生成スクリプト](tools/build_ehmx_spec.py) で再生成します。Python の依存はスクリプト内に固定し、TeX は不要です。Lean の規則と最終目標の宣言を付録へ直接取り込みます。`--check` はソースとPDFのハッシュの対応を読み取り専用で検査します。

```sh
uv run tools/build_ehmx_spec.py
uv run tools/build_ehmx_spec.py --check
lake env lean tests/EHMXAxioms.lean
lake env lean tests/EHMXGoals.lean
```

## モジュール構成

| モジュール | 内容 |
| --- | --- |
| [HMX.lean](HMX.lean) | ライブラリの入口、証明と回帰例の import |
| [Syntax](HMX/Syntax.lean)・[Binding](HMX/Binding.lean) | 名前付き構文、kind、代入、α同値 |
| [Semantics](HMX/Semantics.lean)・[ConstraintLaws](HMX/ConstraintLaws.lean) | モデル、含意・同値、制約法則 |
| [Typing](HMX/Typing.lean)・[Inference](HMX/Inference.lean) | DM・HM(X) の規則、制約生成、原典の命題 |
| [SolvedForms](HMX/SolvedForms.lean) | 解形式・MGU・DM翻訳の命題 |
| [Operational](HMX/Operational.lean)・[Safety](HMX/Safety.lean) | 操作的意味論と型安全性の命題 |
| [LocallyNameless](HMX/LocallyNameless/Syntax.lean) | 束縛変数を添字で表す証明用構文・意味論・型付け |
| [Correspondence](HMX/LocallyNameless/Correspondence.lean) | 名前付き表現との対応、作用域条件付き命題 |
| [Proofs](HMX/LocallyNameless/Proofs.lean) | 補助補題、表現対応、推論定理の証明 |
| [TypeClasses](HMX/TypeClasses.lean) | 単一引数クラス・スーパークラス・条件付きインスタンスの固定モデル |

## 主要な証明

| 原典との対応 | 証明宣言 |
| --- | --- |
| 10.4.4 Soundness の作用域条件付き版 | [HMX.Proofs.theorem10_4_4_soundness_scoped](HMX/LocallyNameless/Proofs/InferenceTransfer.lean#L38) |
| 10.4.8 Completeness | [HMX.Proofs.theorem10_4_8_completeness](HMX/LocallyNameless/Proofs/InferenceTransfer.lean#L57) |
| 429–430頁の主要制約性の作用域条件付き版（原典番号・固有名なし） | [HMX.Proofs.constraintGenerationPrincipality_scoped](HMX/LocallyNameless/Proofs/InferenceTransfer.lean#L75) |
| 名前付き／locally nameless 型付けの対応（形式化の補助命題） | [HMX.LN.Proofs.typingCorrespondence](HMX/LocallyNameless/Proofs/TypingCorrespondence.lean#L149) |

作用域条件は `t.fpi ⊆ Γ.dpi` です。完全性には既存の環境実現可能性条件があり、健全性にはありません。原文の作用域条件なしの健全性・主要制約性、DM翻訳、型安全性、ソルバーの正当性は未証明です。

## 詳細とライセンス

- [出典と表現上の選択](docs/sources.md)：PDFの書誌情報・ハッシュ、定義の対応、曖昧さと未解決事項。
- [証明範囲と原典番号の対応](docs/proofs.md)：61件の内訳、証明経路、原文の命題との区別。
- [型クラスの具体モデル](docs/typeclasses.md)：モデルの構成、定理の適用、Lean 内の回帰例。

コードと本リポジトリ独自の文書は [MIT License](LICENSE)（Copyright (c) 2026 kadu-v）です。`docs/references/` の第三者PDFはMITライセンスの対象外で、各資料の権利者に著作権が帰属します。
