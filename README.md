# EHM(X)：構文・定義と証明対象

HM(X) の制約付き型推論に、効果・`perform`・handler・値制限を加える Lean 形式化です。

**今回修正したのは構文・定義・条件・仮定・定理のステートメントです。定理7・16・17・系7は未証明です。** [Statements.lean](lean/EHMX/HMX/Statements.lean) は `def … : Prop` で命題を定義し、証明や公理を提供しません。

旧 `Constraints`、固定解釈の型順序、独立した代入作用、旧四定理・旧正規化と依存する具体 solver は削除しました。補助的な旧意味論モデルも削除し、構文の検査例と独立した論理的補題を残しています。

[仕様PDF](output/pdf/ehmx-formal-spec-review.pdf) と [TeX](tex/ehmx/rules.tex) は現在の Lean 定義に対応します。比較対象は Martin Sulzmann の [学位論文（2000）](https://www.researchgate.net/publication/213884919_A_General_Framework_for_HindleyMilner_Type_Systems_with_Constraints)、§§3–4、Appendix C.4 です。証明の順序は [TODO](TODO.md) に記載します。

## 原典との対応

| 原典・対象 | 現在の定義・修正 |
|---|---|
| 定義2：有限トークン集合・含意 | `ConstraintTheory` は論理的含意を独立に与える。有限集合は `ConstraintSyntax.TokenSet` と `denoteSet` で連言に対応させる |
| 定義3–5：射影・自由変数・充足可能性 | `existsNames`、`freeNames`、`Satisfiable`。充足可能性は存在閉包の論理的妥当性。保存範囲と自由変数を区別 |
| §3.2：型項 | `TypeSignature`・`TypeTerm` は任意の構成子を持つ自由項代数。`TypeSyntax` はその表現と操作・自由変数の対応を持つ。閉型の存在を要求しない |
| 定義6：代入 | 内部の有限写像 `FiniteSubstitution` と、冪等性を持つ `Substitution`、有限置換 `Renaming` を分離。合成・制限に冪等性を自動付与しない |
| 定義7：D1–D6 | `TermConstraintTheory`。D6 は述語に課す。D4 は異なる変数という慣習を `i ≠ j` と明記 |
| 制約への同時代入 | `ConstraintSyntax.subst` で構成し、`Theory.subst` はこの作用のみを使う。符号化に連言などの構文的一致を要求しない |
| 代入の導出される性質 | `SubstitutionRespectsEquivalence`・`SubstitutionPreservesEntailment`・`SubstitutionPresentationIndependent` は未証明命題。新しい構造体フィールドや四定理の前提ではない |
| 型比較 | 論理的述語に REFL・ASYM・TRANS・CONTRA を課す。ground 値の順序から定義しない |
| 定数・初期環境 | `Constant` と重複のない有限初期定数表。`Context` は定数表と局所変数を持ち、両方を自由変数・代入・許容性の対象とする。必須の閉型 `Literals` を廃止 |
| §3.2・3.4.5：スキーム | 一層の qualified スキーム。`Scheme.Equivalent` は改名と条件の論理的同値を含む。比較・型付け・環境に同値移送を用意 |
| スキーム比較 i | `Comparison.forallLeft` の右辺を任意のスキームにする。単相型だけへの正規化済み関係を公開定義にしない |
| 定義14–15：環境比較 | `Context.Instance` と `Context.ConstrainedInstance`。定数名と局所変数の位置を保つ |
| 定義17：整合性 | `ConsistentConstraint`・`Scheme.Consistent`・`Context.Consistent`。代入後の許容性を要求する。S の任意代入閉性は課さない |
| 定義18：近似 | 元スキームは Sat で許容、対象と C は S で許容。最初の比較は `Instance X X.top source target`。最大性は解決済み比較導出で述べる |
| §3.4.4：一般化 | `Generalizes` は制約分割・射影・非脱出を持つ関係。最大の束縛集合を選ぶ関数ではない。原典にない `C ≡ C₁ ∧ C₂` は追加しない |
| 図3.1と図3.4 | `Presentation.term/constraint` を S の選択から分離。constraint 形式の型の位置は変数・矢印に制限し、述語引数は任意の項を許す |
| 二つの全称除去 | `forallElimSubst` と `forallElimConstraint`。後者は `C ⇒ ∃A.D` から子の条件を `C ∧ D` にする図3.4の規則 |
| 存在導入 | `existsIntro` は図3.4の規則であり、EHMX 独自ではない。即時効果についての非脱出は拡張 |
| 導出全体の制限 | `Derivation` に提示形式と `Fragment.core/handlers` の添字を持たせ、入力・出力の両方を制限。入力だけの `UsesHMXRules` を廃止 |
| 定義20：代入域・値域 | `changedNames` は構文的に変更される名前。`codomain` と保存範囲 `supportBound` を分離 |
| 定義22–25：正規化 | 一般の問題 `(C, σ)`、冪等性、制約の固定性、一つの全変数共通因子、全正規形に対する主要性 |
| 定義26–28、注3 | 型だけの等式自由性、有限原始述語集合、コード上の計算可能性、全正規形の残余一致、lifting を分離。文字どおりの S と許容代表元方式も区別 |
| 図4.4：生成・再構成 | 帰納的な `Generates`・`Reconstructs` と実装 `generate`・`inferTerm` を分離。Equ は関係では任意段階に適用可能 |
| 生成の局所変数 | 各子の結果型は新鮮な変数。ラムダ・適用・let で内部変数を射影。値 let は結果変数を一般化し、内部の存在変数を全称化しない |
| perform・handler | 子の結果型と要求型を別に割り当て、実際の型比較を生成。handler の `∀B.∃W` と非脱出を維持 |
| 定義29：主要な組 | `Statements.PrincipalPair`。EHMX の `PrincipalValue`・`PrincipalComputationScheme` とは別定義 |
| 閉じているという条件 | `Context.Closed`・`Scheme.Closed`・`ClosedJudgment` を分離 |

## 定理のステートメント

全宣言が**未証明**です。「HMX 対応」は下記の承認済み変更を維持した対応を意味し、原典と全く同じ言語の定理という意味ではありません。

| 宣言 | 前提・結論 |
|---|---|
| `theorem7` | `S ⊆ Sat`・主要正規形・射影閉性。同じ term/core 規則のまま Sat から S へ導出を変換。単相型は保ち、実現可能なスキームは近似する |
| `theorem16` | `S ⊆ Sat`・主要正規形・射影閉性。再構成関係の健全性と出力の固定性。入力環境の top での実現可能性は仮定しない |
| `theorem17` | `S ⊆ Sat`・主要正規形。開環境・qualified 型の完全性。一般化結果と共通因子の存在を結論に置く。全体の射影・改名閉性を加えない |
| `corollary7` | `S ⊆ Sat`・主要正規形。閉環境・top での型付けから、外側の条件を top にした一般化と対象型への比較を得る |
| 各 `EHMX` 版 | 対応する前提に `AdmissibleLifting` と閉じた操作宣言を加え、handler を含む主張を分ける |
| `presentationCorrespondence` | term 形式と constraint 形式の対応を独立した命題にする |

`SolvedForms` は `S ⊆ Sat` のみです。一律の連言閉性はなく、比較導出では個々の判断制約の許容性を `Comparison.Valid` で確認します。

`Lifting` は定義28(iv)の文字どおりの所属条件です。`AdmissibleLifting` は両方の所属を `Adm S` に換えた別条件で、EHMX の命題はこちらを使います。両者の同一性を仮定していません。定義28全体の `LiftingProperty` は四定理の共通前提ではありません。

`PrincipalNormalizer.ofExistence` は非計算的な選択による存在モデルです。`ProjectionFreeProcedure` は有限原始述語集合の入力を実際に符号化し、コード上の関数に `Computable` を要求します。抽象的な関数を含む問題型全体に `Primcodable` を仮定しません。

## 実装への接続

`implementationGeneration`、`implementationSoundness`、`implementationCompleteness`、`implementationCorollary7` は実際の生成関数・`inferTerm` に関する**別の未証明命題**です。健全性・完全性・系7は同じ簡約器 N と正規化器 P を使います。関係の定理だけを記述して、実装が証明されたことにはしません。

`implementationPrincipalComputation` は同じ出力について、即時効果を含む主要性と、値なら主要な値スキームであることを述べる追加の命題です。原典の系7の結論と区別します。`ComputationScheme.FiniteInstance` は引き続き対象制約の下で比較します。

## 維持する原典との差異

1. 型と効果の二種類の名前、潜在効果、有限集合の効果項、perform、handler、値制限。
2. 正規形比較を対象残余の下で行うこと。一つの有限因子を全変数・全評価に共通して使うこと。
3. 定理17の環境・効果の一致を対象制約 C の下で述べること。
4. 比較の `forallRight` の結論は C とする承認済み変更。型付けの全称導入は射影のガードを維持すること。
5. 原典付録197ページの解決済み比較導出の条件を明示すること。
6. EHMX 版に許容版 lifting を明示し、等式自由性は型項に限って効果等式を許すこと。

代入の有限保存範囲、式変数の de Bruijn 添字、明示的な同値関係は表現上の選択です。D4 の異なる変数という慣習も明記しています。`existsIntro` 自体を追加規則とは扱いません。

## 検証と次の作業

```sh
cd lean
lake build
```

全残存モジュールを `EHMX.lean` から参照します。`DefinitionChecks` は型・効果の捕獲回避、入れ子の量化、述語引数・潜在効果への代入を検査します。多相 let・handler・局所射影を持つ生成規則についての検査は**型検査**であり、推論の正しさの証明ではありません。

次は、構成した代入の同値・含意保存を原典の法則から導き、定理7の一般化と多相 let の近似を証明します。続いて定理16、定理17、系7と、同じ正規化器を使う実装の命題を詰めます。具体的な Haskell 型クラス系の構築はその後です。
