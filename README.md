# lean-ehmx

**代数的効果と deep handler を備える EHM(X) の Lean 4 形式化。**

『Advanced Topics in Types and Programming Languages』（ATTAPL）第10章 *The Essence of ML Type Inference* の HM(X) を基盤に、`perform`、述語条件付きの多相操作、単一操作の deep handler、値制限付き let を扱います。System Fξ を参考に、型・効果の安全性と、制約生成の健全性・完全性・主要制約性を証明しています。

| ライブラリ | 対象 | 現在の証明範囲 |
| --- | --- | --- |
| [HMX](HMX.lean) | 原典に基づく HM(X) | 作用域条件付きの健全性・主要制約性、完全性、名前付き表現と locally nameless 表現の対応 |
| [EHMX](EHMX.lean) | 効果・多相操作・deep handler を加えた EHM(X) | 推論三定理、一歩・多歩保存、進行性、到達状態の効果安全性 |
| [CEHMX](CEHMX.lean) | 資源量を扱う coeffect 拡張 | 資源代数、記録付き意味論、消去後の型・効果安全性。資源型付けと使用上限保証は未実装 |

証明済みの範囲と必要な前提は、以下の「証明の範囲」に記載しています。原典の章全体や、CEHMX の資源安全性の完成を主張するものではありません。

## ビルドと検証

[elan](https://github.com/leanprover/elan) を導入し、リポジトリのルートで実行します。初回のツールチェーン・依存ライブラリ・キャッシュの取得にはネットワーク接続が必要です。

```sh
lake exe cache get
lake build
```

`lake build` は `HMX`・`EHMX`・`CEHMX` の証明と、各入口から import される回帰例を検査します。

| 設定 | 固定値・定義先 |
| --- | --- |
| Lean | `leanprover/lean4:v4.34.1` · [lean-toolchain](lean-toolchain) |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` · [lakefile.toml](lakefile.toml) |
| 推移的依存 | [lake-manifest.json](lake-manifest.json) |
| Lake パッケージ名 | `hmx` |

Goal の型、推論定理の適用、CEHMX の基礎命題、依存公理は次のコマンドで検査します。

```sh
lake env lean tests/EHMXGoals.lean
lake env lean tests/EHMXInference.lean
lake env lean tests/EHMXAxioms.lean
lake env lean tests/CEHMXFoundations.lean
lake env lean tests/CEHMXAxioms.lean
```

[CI](.github/workflows/lean.yml) も push・pull request 時に、固定ツールチェーンと mathlib キャッシュを準備し、ビルドと上記の検査を実行します。PDF の更新・再生成・整合性検査は Lean 検証の必須処理に含めません。

## 証明の範囲

### EHMX：効果を持つ型推論と安全性

推論三定理は [EHMX/Goals.lean](EHMX/Goals.lean) の前提・結論を維持して証明しています。`...Goal` は命題の定義であり、証明は別の `theorem` 宣言です。

| 保証 | 主な証明宣言 | 内容 |
| --- | --- | --- |
| 健全性 | `EHMX.inferenceSoundness` | 生成制約の下で、要求した型・効果による型付けが成立する |
| 完全性 | `EHMX.inferenceCompleteness` | 環境実現可能性の条件の下で、型付けの制約が生成制約を含意する |
| 主要制約性 | `EHMX.constraintGenerationPrincipality` | 固定した要求型・効果について、生成制約が型付けを与え、同じ型付けを与える任意の制約から含意される |
| 値代入・操作捕捉 | `EHMX.schemeValueSubstitution`、`EHMX.operationPreservation` | 多相 let の値代入と、deep handler による操作捕捉で型付けを保つ |
| 保存 | `EHMX.preservation`、`EHMX.preservationSteps` | 一歩・多歩の簡約で型と効果を保つ |
| 進行性 | `EHMX.progressEffectSafety`、`EHMX.emptyEffectProgress` | 閉じた型付き項は値・簡約可能・効果に含まれる未処理操作のいずれか。空効果なら値または簡約可能 |
| 到達状態の安全性 | `EHMX.effectSafety`、`EHMX.emptyEffectSafety` | 進行性の保証を任意の到達状態に適用する |

健全性は ATTAPL 10.4.4 の作用域を明示した EHMX 版、完全性は 10.4.8 に対応します。主要制約性は同章429–430頁の議論に対応し、ソルバーや最汎代入の存在は保証しません。

推論三定理は制約・効果モデルの法則と操作宣言の整形式性を前提とします。健全性・主要制約性には作用域・kind・環境の整形式性、完全性には環境実現可能性の条件があります。推論の証明に、充足可能性、`ArrowSeparated`、意味論の値を型構文で表せるという前提は追加していません。

保存と型安全性は ATTAPL §10.5 の10.5.8・10.5.11に対応する EHMX 固有の拡張です。安全性には `ArrowSeparated` を含む `SafetyAssumptions` を使います。進行性と到達状態の保証には制約を満たす割当てが必要で、空効果の安全性では制約の充足可能性を要求します。

公開入口から主要な定理を確認できます。

```lean
import EHMX

#check EHMX.inferenceSoundness
#check EHMX.inferenceCompleteness
#check EHMX.constraintGenerationPrincipality
#check EHMX.preservationSteps
#check EHMX.effectSafety
#check EHMX.emptyEffectSafety
```

正確な命題と証明状況は [EHMX の仕様](docs/ehmx-spec.md) と [証明 TODO](docs/ehmx-todo.md) を参照してください。

### EHMX：条件付き多相操作と型クラス

操作宣言は `op : ∀β. P ⇒ A → B` の形を取り、条件 `P` は通常のスキームと同じ `Constraint` です。省略時は `truth` になります。呼出側は具体化した条件を満たし、handler の操作節は宣言条件を仮定できます。操作宣言の矢印に効果欄はありません。

let は値だけを一般化し、非値は単相で扱います。この値制限は EHMX の型付けで定めており、`HMX.ValueRestricted` の流用ではありません。

[条件付き操作の回帰例](EHMX/ConditionalOperationsRegression.lean)では、`op : ∀β. Eq β ⇒ β → β` と操作節 `let _ = eq z z in k z` を扱います。handler 全体の空効果、推論三定理、`Int` による充足可能性、実際の操作捕捉の保存を検査しています。実装計画と検査結果は [todo.md](todo.md) に記録しています。

また、[型クラスの固定モデル](docs/typeclasses.md)を具体的な X として構成しています。`EHMX.TypeClasses.fixedFramework` は HMX と宣言データを共有し、関数型の潜在効果と反変・共変の順序を保持します。同名前空間の推論三定理はモデル法則を内部で証明し、作用域・kind・環境実現可能性の条件を維持します。

[型クラスの回帰例](EHMX/TypeClassesRegression.lean)では、資格付き `eq` の利用と多相操作を処理する deep handler について、直接型付け、生成制約への含意、主要制約性、`Int` の割当てによる充足可能性を検査しています。

### CEHMX：資源量を扱う拡張

CEHMX は EHMX から独立した公開入口に追加しています。現在は、次の基礎を証明しています。

- 抽象資源代数と、`Nat + ∞`・使用有無のモデル。
- grade と資源環境の代入、継続の識別子を保持する記録付き簡約。
- 元の EHMX との双方向の簡約対応と、消去後の型・効果の保存・進行・到達状態の効果安全性。

[回帰例](CEHMX/Examples.lean)では、別名、高階関数、継続を捕捉して返す関数、入れ子の handler、1・2・4回の使用記録を検査します。

**資源型付け、型付けからの使用上限保証、資源制約を含む推論三定理は未実装です。** 記録付き意味論は予算超過で実行を止めません。`WithinBudget.prefix` は上限内の記録の接頭辞も上限内であることを示す補題であり、型付きプログラムの使用上限を保証する定理ではありません。

次の作業は、操作捕捉で複製される文脈と、返される関数が捕捉する継続の要求量を保持する型付けを定め、その同時代入・保存を証明することです。資源安全性の完成後に制約生成へ進みます。各補題の使用先と完了条件は [CEHMX の証明 TODO](docs/cehmx-todo.md) に記録しています。

### HMX：原典から引き継いだ基盤

原典の命題は `def ... : Prop` として保持し、証明を別の宣言に分離しています。制約推論・表現対応51件と、型クラス固定モデルの構成・適用10件を証明しています。件数は章全体の命題数ではなく、[登録済みの証明の内訳](docs/proofs.md)です。

| 原典との対応 | 証明宣言 |
| --- | --- |
| 10.4.4 Soundness の作用域条件付き版 | [`HMX.Proofs.theorem10_4_4_soundness_scoped`](HMX/LocallyNameless/Proofs/InferenceTransfer.lean) |
| 10.4.8 Completeness | [`HMX.Proofs.theorem10_4_8_completeness`](HMX/LocallyNameless/Proofs/InferenceTransfer.lean) |
| 429–430頁の主要制約性の作用域条件付き版 | [`HMX.Proofs.constraintGenerationPrincipality_scoped`](HMX/LocallyNameless/Proofs/InferenceTransfer.lean) |
| 名前付き表現と locally nameless 表現の型付け対応 | [`HMX.LN.Proofs.typingCorrespondence`](HMX/LocallyNameless/Proofs/TypingCorrespondence.lean) |

作用域条件は `t.fpi ⊆ Γ.dpi` です。完全性には既存の環境実現可能性条件があり、健全性にはありません。原文の作用域条件なしの健全性・主要制約性、DM 翻訳、HMX の型安全性、ソルバーの正当性は未証明です。EHMX の安全性定理は、これらの HMX の命題を証明済みに変更するものではありません。

```lean
import HMX

#check HMX.Proofs.theorem10_4_4_soundness_scoped
#check HMX.Proofs.theorem10_4_8_completeness
#check HMX.Proofs.constraintGenerationPrincipality_scoped
```

## ソースの構成

| 入口・ディレクトリ | 内容 |
| --- | --- |
| [HMX.lean](HMX.lean)・[HMX/](HMX/) | HM(X) の名前付き構文、意味論、型付け、制約生成、原典の命題 |
| [HMX/LocallyNameless/](HMX/LocallyNameless/) | 束縛変数を添字で表す証明用構文と、名前付き表現との対応 |
| [HMX/LocallyNameless/Proofs/](HMX/LocallyNameless/Proofs/) | HM(X) の補助補題・表現対応・推論定理の証明 |
| [EHMX.lean](EHMX.lean)・[EHMX/](EHMX/) | 効果付き構文、操作的意味論、型付け、制約生成、最終目標の命題 |
| [EHMX/Proofs/](EHMX/Proofs/) | 代入、推論三定理、進行性、保存、効果安全性の証明 |
| [EHMX/TypeClasses.lean](EHMX/TypeClasses.lean)・[その証明](EHMX/Proofs/TypeClasses.lean) | 型クラスの固定モデルと推論三定理の特殊化 |
| [CEHMX.lean](CEHMX.lean)・[CEHMX/](CEHMX/) | 資源代数、grade、資源環境、記録付き意味論の基礎 |
| [tests/](tests/) | Goal の型検査、定理の適用回帰、依存公理の監査 |

## 関連文書

| 文書 | 内容 |
| --- | --- |
| [EHMX の仕様](docs/ehmx-spec.md) | 構文・規則・最終目標の前提と結論 |
| [EHMX の証明 TODO](docs/ehmx-todo.md) | 補題の依存関係と証明状況 |
| [CEHMX の証明 TODO](docs/cehmx-todo.md) | 資源安全性に向けた設計・証明義務・完了条件 |
| [型クラスの具体モデル](docs/typeclasses.md) | モデルの構成、定理の適用、回帰例 |
| [証明範囲と原典番号の対応](docs/proofs.md) | HMX の証明の内訳、証明経路、原文の命題との区別 |
| [出典と表現上の選択](docs/sources.md) | 参考資料の書誌情報・ハッシュ、定義の対応、未解決事項 |

[既存の仕様 PDF](output/pdf/ehmx-spec.pdf) は Lean の変更に合わせて更新していません。PDF 作業は明示的な依頼がある場合に行います。[生成スクリプト](tools/build_ehmx_spec.py)を用意しています。`docs/references/` の PDF は原典・参考資料であり、EHM(X) の仕様書ではありません。