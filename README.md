# EHM(X)：証明範囲と HM(X) との対応

HM(X) の制約付き型推論を、効果・`perform`・handler と値制限付き一般化を持つ体系へ拡張し、Lean で形式化するプロジェクトです。

**制約形式 `S = Sat_X` では、開環境を含む生成完全性と qualified 型への主要性比較まで証明済みです。型領域 `equalityTypes` では、明示した条件の下で、一般の解決済み集合 `S` への再構成の健全性（定理16）と、環境・qualified 型・外側制約を一つの代入で比較する完全性（定理17）、閉環境の主要計算型・値の主要型（系7）を証明しています。定理7は13規則と生成される単相射影・perform・handler の変換まで証明済みです。EHMXで追加した任意の qualified 型への射影変換と、具体的制約系が全前提を満たす証明は残っています。具体的な型クラス solver の完全性は、明示した判定断片に限られます。**

ここで「証明済み」は、現行 Lean の定義と明示された前提の下で定理があることを指します。原典の体系全体をそのまま機械検証したという意味ではありません。詳細な作業項目は [TODO.md](TODO.md)、数式による仕様は [PDF](output/pdf/ehmx-formal-spec-review.pdf)、そのソースは [rules.tex](tex/ehmx/rules.tex) を参照してください。README・TODO・PDF の保証範囲を Lean と一致させます。

## 1. 三つの証明範囲

| 範囲 | 現在の到達点 | 残る条件・証明 |
| --- | --- | --- |
| 抽象 `X` の制約形式：`S = Sat_X` | 生成の健全性・完全性、開環境での qualified 型比較、閉環境の主要計算型、値の主要対 | 実行可能な完全推論には、対象制約言語全体の充足可能性判定器が必要 |
| 条件を満たす一般の `S` への型項再構成 | `equalityTypes` で生成導出の変換・同じ `S` の出力健全性、qualified 型までの再構成完全性・閉環境の主要型 | 健全性には環境等の追加条件が必要。具体的制約系の全条件、EHMXの任意の qualified 射影変換、任意の `TypeDomain` への拡張は未証明 |
| 具体的 `X_tc` と型クラス solver | 実行可能な部分 solver、成功時の健全性・閉環境主要性、指定断片での完全性 | handler-free な生成制約全体の判定と、その後の handler の量化制約への拡張 |

qualified 型とは `∀A. D ⇒ t` のように量化と制約を持つ型スキームです。「推論が成功する」「出力が型付けできる」「出力が任意の対象型より一般的である」は別の保証です。

`Sat_X(C)` は制約 `C` の充足可能性、`S` は選択した解決済み制約の集合です。`Typing_S` は、内部の制約・環境・型スキームを含む導出の妥当性を `S` に対して要求します。出力の残余制約 `R` が `S` に属するだけでは `Typing_S` の証明にはなりません。

## 2. 原典 HM(X) との対応

比較対象は Martin Sulzmann, [*A General Framework for Hindley/Milner Type Systems with Constraints*（学位論文、2000）](https://www.researchgate.net/publication/213884919_A_General_Framework_for_HindleyMilner_Type_Systems_with_Constraints) です。主に §3.6、§4.2、§4.4.1、§4.4.2 に対応します。

原典では、下表の導出変換・健全性・完全性・主要型は定理として述べられています。定理7の証明は付録 C.4、定理16・17の証明は付録 C.8 にあります。**下表の「未証明」は本リポジトリでの形式化の状態です。**

| 原典 | 内容 | 本リポジトリの対応・状態 |
| --- | --- | --- |
| §4.4.1 定理14 | 制約形式の推論の健全性 | 現行の値制限付き体系で証明済み。`generateProjected_sound`、`SatDecider.infer_sound_of_admissible` |
| §4.4.1 定理15 | 開環境での完全性、外側条件と型スキームの比較 | `S = Sat_X` で証明済み。`Typing.inference_complete_scheme`、`Typing.principal_computation_open_at` |
| §4.4.1 系6 | 閉じた判断での主要型 | 現行体系の主要計算型・値の主要型として証明済み。`Typing.principal_closed_from_open` |
| §4.2 | 正規形と主要正規化 | 契約と `Sat_X` のモデルを形式化。型項再構成には有限の入力変数上で比較する `ScopedPrincipalNormalizer` を使用。存在と計算可能性を区別 |
| §3.6 定理7 | 制約形式から型項形式への導出変換 | 現行定義・追加条件・対象13規則の下で証明済み。`Derivation.theorem7_core`、`theorem7_mono_core`。生成導出について単相射影・perform・handler まで変換を拡張 |
| §4.4.2 定理16 | 型項再構成の出力健全性 | 追加条件下で同じ `S` の健全性を証明。`inferTermAt_sound`、`inferTermAt_sound_effectOnly`。後者は入力環境の許容性と `Realizable top` から代入後の環境条件を導く |
| §4.4.2 定理17 | 再構成の完全性と qualified 型までの一般性比較 | `equalityTypes`、主要正規化器・`SolvedClosure`・対象環境の実現可能性の下で証明済み。`inferTerm_complete_scheme` が実際の推論成功と同じ因子による環境・qualified 型・外側条件の比較、効果保存を返す |
| §4.4.2 系7 | 再構成された主要型 | 定理16の追加条件と閉じた実現可能な環境の下で証明済み。`inferTerm_principal_closed`、`Typing.corollary7`。元の環境・同じ `S` で主要計算型と値の主要型を返す |

原典の定理も無条件に任意の `S` を扱うものではありません。定理7・16には射影閉性と principal constraint property、定理17・系7には principal constraint property と環境の実現可能性などの前提があります。現行の `ScopedPrincipalNormalizer` と追加の閉性条件だけで原典の前提・結論をすべて再現したとは主張しません。

原典の図3.1に独立した `existsIntro` 規則はありません。これはEHMXで追加した外側制約の射影規則です。その qualified 型への導出変換が未証明であることと、HMXの規則に対応する定理7の証明範囲を区別します。

### 原典からの拡張と相違

| 要素 | 現行 Lean での扱い |
| --- | --- |
| 抽象的な型代数・制約領域 | `TypeDomain`、`TypeOrder`、`Constraints`。代入・論理演算・射影・有限台の法則を明示 |
| 制約付き多相型・一般化 | `Scheme`、`Instance`、`Generalization`。一般化には値制限を設ける |
| 効果 | 型と効果を区別し、計算スキーム `∀A. D ⇒ (t ! ε)` を用いる |
| 操作と handler | `perform`・handler を追加。handler 制約は `∀B.∃J.D` として剛体変数と証人の依存を表す |
| 変数表現 | 項は de Bruijn index、型・効果変数は名前付き。捕獲回避と有限台を形式化 |
| 追加の導出変換 | 単相 `existsIntro`・`perform`・handler を証明。handler の束縛名変更・`∀B.∃J`・非脱出を保存。qualified 型への `existsIntro` は対象外 |

したがって、原典の値制限なしの体系そのものの証明、あるいは原典の定理だけによる handler 拡張の正当化を完了したとは扱いません。

## 3. 証明済みの内容

以下の抽象定理は主に名前空間 `EHMX.HMX` にあります。前提の正確な形はリンク先の Lean 定理を基準にします。

### 3.1 制約生成と `S = Sat_X` での主要性

- 固定した生成算法 `generate`・`generateProjected` の健全性・完全性を証明しています。操作宣言の閉性と ground 環境の実現可能性の下で、生成制約の成立と ground 型付けが対応します（`generateProjected_ground_iff`）。ここでの ground 型付けは、変数を解釈した型付け関係です。
- 開環境で、型付けと対象制約 `C` の下での環境の実現可能性から、実際の生成成功と生成制約 `D` の充足可能性を導きます。
- 一般化の外側条件 `P = ∃A.D` を保持し、比較対象ごとに `C ⊨ P` と任意の qualified 型への構文的 `Instance` を証明しています。単相の型・効果については、すべての評価で共通に使える一つの有限代入で比較します。
- 値の主要対を全対象判断と比較する定理には `Realizable top` を要求します。閉環境では主要計算型と、値の主要型を導きます。
- これらの生成完全性・主要性は充足可能性判定器を仮定せず、handler を含みます。

参照：[AlgorithmCorrectness.lean](lean/EHMX/HMX/AlgorithmCorrectness.lean)、[GenerationCompleteness.lean](lean/EHMX/HMX/GenerationCompleteness.lean)、[OpenCompleteness.lean](lean/EHMX/HMX/OpenCompleteness.lean)、[PrincipalCompleteness.lean](lean/EHMX/HMX/PrincipalCompleteness.lean)。

### 3.2 solver との合成

- `PartialSolver` の成功・未解決・不整合の契約と、完全性の追加条件 `PartialSolver.Complete` を定義しています。契約の下で成功時健全性、閉環境主要性、開環境の有限因子比較を証明しています。
- `SatDecider X` は Bool 判定と充足可能性の同値を要求します。この判定器から、元の残余制約と恒等代入を返す完全な solver を構成しています。
- その solver と実際の推論算法を合成し、推論成功に加え、開環境の qualified 型比較まで証明しています（`SatDecider.infer_complete_scheme`、`infer_principal_open`）。
- `SatDecider.infer_sound_of_admissible` は、閉じた操作宣言と許容な環境から健全性を示し、`Realizable top` を要求しません。

抽象的な `X` 全体に対する実行可能な判定器を自動的に得たわけではありません。handler を含む合成完全性に使う判定器は `∀B.∃J.D` も扱う必要があります。非計算的な solver の存在モデルは実行可能な判定器と区別します。

参照：[PartialSolving.lean](lean/EHMX/HMX/PartialSolving.lean)、[SolverContract.lean](lean/EHMX/HMX/SolverContract.lean)、[AbstractInference.lean](lean/EHMX/HMX/AbstractInference.lean)。

### 3.3 一般の `S` への型項再構成

生成後に一度正規化する `inferTermAt`・`inferTerm` と、出力から計算スキームを作る `reconstructedScheme` を実装しています。

| 証明済みの項目 | 前提・保証範囲 | 主な定義・定理 |
| --- | --- | --- |
| 主要正規化の契約 | 有限の入力変数上で比較。主要正規形の存在と計算可能な実装を分離 | `PrincipalNormalForms`、`ScopedPrincipalNormalizer` |
| `S` の閉性 | 許容性の改名・整合する連言・射影による保存を別の条件として定義。`Sat_X` のモデルあり | `SolvedClosure`、`SolvedClosure.satisfiable` |
| 捕獲回避代入 | 任意の qualified 対象への `Instance` の代入保存、環境の ground 解釈との対応、実現可能性と新鮮な名前の保護 | `Instance.subst`、`Context.ground_subst`、`Context.Realizable.subst`、`Context.subst_avoids` |
| 環境近似と変数規則 | 各評価で型の実例が存在すれば、許容な環境は自分自身を近似する。推移性・lookup・同じ `S` での qualified 対象への変数規則を証明 | `Context.Approximates.refl_of_ground`、`Context.Approximates.variable_scheme` |
| 条件付きの近似の存在 | `equalityTypes`、全変数で比較する `PrincipalNormalizer`、恒真な解決済み制約、外側条件の許容性、スキーム・環境の実現可能性の下で構成 | `Scheme.approximation_exists`、`Context.approximation_exists` |
| 値の型の比較 | `SolvedClosure` の下で、値の `Instance` 比較を任意の許容な qualified 型への型付けに反映。環境と衝突する束縛名を改名 | `Typing.instance_value` |
| 一般化と定理7相当の変換 | 有限入力変数上の主要正規化・追加条件からスキーム近似と `Typing_S` を構成。元の導出への帰納法を13規則について証明 | `SchemeApproximation.generalized_approximation`、`Derivation.theorem7_core`、`Derivation.theorem7_mono_core` |
| 有限の比較正規形 | スキームの実現可能性・束縛名の新鮮さ・外側条件の許容性から構成。ground 値の閉じた型項表現は不要 | `Scheme.Realizable.solved_witness_finite`、`NormalForm.exists_of_realizable_finite` |
| 比較正規形の構成 | 改名閉性の下で新鮮化を使用。対象代入の解決済み性や残余不変性は要求しない | `ScopedPrincipalNormalizer.complete_of_substitution` |
| 制約形式の出力健全性 | 閉じた操作宣言と `Realizable top` の下で、実際に代入した環境における `Typing_Sat` を構成 | `inferTermAt_sound_constraint` |
| 同じ `S` での出力健全性 | 定理7と同じ正規化・閉性・射影の追加条件、閉じた操作宣言、`Realizable top`、代入後の環境の許容性から `Typing_S` を構成。効果だけの残余制約では入力環境の許容性から代入後の条件を導く | `inferTermAt_sound`、`inferTermAt_sound_effectOnly`、`inferTerm_sound`、`inferTerm_sound_effectOnly` |
| 単相判断からの完全性 | 改名閉性と対象環境の実現可能性の下で成功。一つの有限因子で環境・型・効果の解釈と残余含意を比較 | `inferTermAt_complete_mono`、`reconstruction_factor` |
| qualified 判断からの受理 | `SolvedClosure` と対象環境の実現可能性の下で実際の `inferTerm` が成功 | `inferTerm_complete_acceptance` |
| qualified 型までの完全性（定理17） | `equalityTypes`、主要正規化器・`SolvedClosure`・対象環境の実現可能性。一つの有限因子で環境・qualified 型・外側条件・効果を比較。対象スキームの実現可能性は不要 | `inferTerm_complete_scheme` |
| 再構成後の一般化 | 元の環境の変数の代入先だけを保持し、型付けを同じ `S` の計算スキームへ一般化する | `Substitution.imageSupport`、`ComputationScheme.generalizeWithSupport`、`Typing.reconstructed_computation` |

`inferTerm_complete_acceptance` は対象スキーム自体の実現可能性を追加要求しませんが、出力スキームと対象スキームの主要性比較は結論に含みません。また、`inferTermAt_sound_constraint` の結論は `Typing_Sat` であり `Typing_S` ではありません。

定理17の `inferTerm_complete_scheme` は、任意の対象導出を扱い、qualified 型への `existsIntro` も除外しません。これは導出変換ではなく完全性の保証です。`ScopedPrincipalNormalizer` と `SolvedClosure` を使い、定理16の lifting 条件・恒真な解決済み制約・効果等式の追加閉性は要求しません。比較対象の環境は `C` の下で実現可能であればよく、`Realizable top` や対象スキームの実現可能性は不要です。

`reconstructedScheme` は `U = ψ.imageSupport Γ.support` を計算し、残余制約・結果型・効果の support から `U` を除いた名前を量化します。`(Γ[ψ]).support` は無関係な代入先まで含む場合があるため、一般化の禁止範囲として使いません。`generalizeWithSupport_subst_avoids` は、同じ比較因子による環境上の一致から量化変数の非脱出を証明します。型スキームの比較を得た後、`ComputationScheme.outer_of_typing_instance` が同じ因子による外側制約の含意を導きます。

`ReconstructionCompletenessExamples` は、閉じた qualified 環境の下の恒等関数について実際の生成制約と局所主要正規形を接続し、一般化が失われないことを確認します。対象スキームが実現可能でない例と、型・効果の名前衝突を伴う qualified 射影も、実在する `Sat_X` 正規化器で定理17へ接続しています。`mixed_reconstruction_complete` は定理16の条件付き出力を定理17へ渡し、多相 let・perform・入れ子 handler を含む開いた式を同じ `S` で比較します。

系7の `Typing.corollary7` は、`top` の下で型付け可能な閉環境の式から、実際の `inferTerm` の成功を導きます。同じ出力について、外側制約と `top` の同値、元の環境での `PrincipalComputationScheme`、全単相判断への `FiniteInstance`、全 qualified 判断への `Instance` を証明します。値の場合は同じ `S` の `PrincipalPair` も返します。比較対象は qualified な `existsIntro` を含む全導出です。型領域は `equalityTypes`、環境の閉性は `Γ.support = ∅` とし、定理16の閉性・lifting・効果等式の追加閉性・恒真な解決済み制約と、閉じた操作宣言・`Γ.Realizable top` を前提にします。対象型の実現可能性や代入後の環境の許容性は追加しません。

`Context.subst_approximates_closed` が捕獲回避代入後の環境を元の閉環境へ戻し、`inferTerm_finite_closed` が比較を一つの推論結果にそろえます。`Sat_X` の実在する非計算的な正規化器では全前提を満たし、恒等関数、閉じた qualified 環境、射影、名前衝突、多相 let・perform・入れ子 handler の主要性を確認します。これは具体的な型項・効果専用残余の solver の完全性ではありません。

系7の実装：[ReconstructionPrincipality.lean](lean/EHMX/HMX/ReconstructionPrincipality.lean)、[ReconstructionPrincipalityExamples.lean](lean/EHMX/HMX/ReconstructionPrincipalityExamples.lean)。

定理17の実装：[ReconstructionCompleteness.lean](lean/EHMX/HMX/ReconstructionCompleteness.lean)、[ReconstructionGeneralization.lean](lean/EHMX/HMX/ReconstructionGeneralization.lean)、[ReconstructionCompletenessExamples.lean](lean/EHMX/HMX/ReconstructionCompletenessExamples.lean)。

`Instance.subst` は任意の有限代入を扱い、solver や `GroundRepresentation` を仮定しません。`Context.subst_avoids` は環境の support と代入の range の外側を保護します。有限証人の構成に必要なスキームの実現可能性は、一般の型付け結果からは自動的に得られません。`PrincipalNormalizer.normalize_realizable_finite` も ground 値の閉じた型項表現を要求しませんが、スキームの実現可能性・束縛名の新鮮さ・外側条件の許容性は必要です。これらの補題だけで一般の多相 `let` や handler の導出全体の変換が完成したとはしません。

定理7相当の導出変換は、`equalityTypes`、`ScopedPrincipalNormalizer`、`SolvedClosure`、恒真な解決済み制約、および次の二条件の下で証明済みです。

- 型変数を変更しない有限代入 `θ` について、`R` が許容され、`R ∧ graph θ` が充足可能なら、その連言も許容される。
- `∃A.D` が許容されるなら、`dom θ ⊆ A` かつ `θD` が許容される有限代入 `θ` が存在する。これは定義28④に対応する許容性の条件で、`θ.Solved` は要求しない。

定義28全体は仮定していません。効果制約 `μ ⊆ {op}` を残余に保持する例、効果等式の追加閉性、通常の型等式 `α = Int` が効果専用の残余に属さないことを `TransformationExamples.EffectResiduals` で検証しています。この例だけで具体的 solver 全体の前提を証明したとは扱いません。

`Derivation.UsesHMXRules` は、導出の全節点を変数・定数・関数・適用・多相/単相 let・Sub・一般化・特殊化・制約の強化・効果等式・改名の13規則に限定します。`existsIntro`・`perform`・`handle` は対象外です。式に handler がないことだけでは、この導出条件を満たしません。値制限と、両比較を外側制約の下で行う現行の近似の定義を使います。

`Derivation.theorem7_core` は、許容な外側制約 `C` と入力環境の近似 `Γ ≈C Γ′` の下で、導出から `Typing_S C Γ′ e s′ ε` と `s ≈C s′` を構成します。`Derivation.theorem7_mono_core` は元の単相型と効果をそのまま保存します。内部スキーム・環境の一様な実現可能性は前提にありません。Lean の公開定理は規則に従う導出を直接受け取り、元の `Valid Sat_X` も要求しません。

証明は任意の代入・許容な外側制約に帰納仮定を広げ、元の子導出へ合成した代入で適用します（`Derivation.transform_to_solved_subst`）。一般化では環境の自由変数を保護する正規化、射影に沿った近似の移送、全 qualified 対象へのスキーム近似を証明します。多相 let では値から得た近似で環境を延長して本体を変換します。`Scheme.Approximates.realizable_iff` と整合し、近似から実現可能性を作り出しません。

`TransformationExamples` では公開定理を用い、入れ子の多相 let と特殊化、開環境での名前の衝突、空でない潜在効果の保存を確認しています。既存の実現可能でないスキームを持つ let の例も保持します。強い `PrincipalNormalizer` による `forallIntro_normal_form`・`generalize_normal_form` は既存 API として保持しますが、新しい定理の証明では使いません。

定理16に使う `Derivation.UsesReconstructionRules` は全規則を許し、`existsIntro` の結果だけを単相に限定します。`Inference.sound_reconstruction` は全ての生成導出についてこの条件を満たす導出を構成するため、定理16では式に対する追加の制限はありません。`transform_to_solved_subst_reconstruction` は元の子導出に帰納仮定を適用し、handler でも操作宣言の改名、節の量化、型・効果の比較、非脱出を保存します。既存の13規則の変換はこの拡張の系です。

`inferTermAt_sound` の結論は、実際の出力 `(R, θ)` に対する `Typing_S R (Γ[θ]) e (θt) (θε)` です。一般の `S` では `Γ[θ].Admissible S` を前提に取ります。`EffectResiduals.Solved X = Satisfiable ∧ EffectOnly`、すなわち充足可能で型変数の評価に依存しない残余制約の場合、`inferTermAt_sound_effectOnly` は入力 `Γ.Admissible S` と `Γ.Realizable top` から代入後の環境の許容性・自己近似を導きます。環境を別の近似環境に置き換えません。`inferTerm` にも同じ保証があります。

`ReconstructionExamples` では、多相 let と入れ子 handler・perform を組み合わせた開いた式の実際の生成、公開健全性定理の適用、型・効果の代入先と束縛名の衝突、qualified 射影が対象外であることを検証します。正規化器の条件と正規化成功は条件付きの適用例で明示しており、具体的な完全 solver の構成とは区別します。

`unrepresented(D)` は、選んだ `S` における正規形が存在しないことを表します。一般には `D` の不充足を意味しません。`SatDecider.normalizer` も実装していますが、その解決済み集合は `Sat_X` です。

参照：[ScopedNormalization.lean](lean/EHMX/HMX/ScopedNormalization.lean)、[ContextSubstitution.lean](lean/EHMX/HMX/ContextSubstitution.lean)、[ContextApproximation.lean](lean/EHMX/HMX/ContextApproximation.lean)、[NormalizationCompleteness.lean](lean/EHMX/HMX/NormalizationCompleteness.lean)、[DerivationTransformation.lean](lean/EHMX/HMX/DerivationTransformation.lean)、[FreshNormalForms.lean](lean/EHMX/HMX/FreshNormalForms.lean)、[TermReconstruction.lean](lean/EHMX/HMX/TermReconstruction.lean)、[ReconstructionSoundness.lean](lean/EHMX/HMX/ReconstructionSoundness.lean)、[EffectResiduals.lean](lean/EHMX/HMX/EffectResiduals.lean)。

### 3.4 具体的な型クラス・効果 solver

`EHMX.TypeClasses` では、型構築子、型クラス、再帰的インスタンス、superclass の宣言と検査を実装しています。クラス意味論との対応、有限状態による共同存在判定、効果制約の判定、型等式の分解・occurs check、型・効果の存在消去と同値正規化を証明しています。

具体的 solver は停止する部分判定手続きで、`solved`・`unresolved`・`inconsistent` の各契約を満たします。`inferClasses_sound` は成功時の ground 健全性、`inferClasses_principal` は閉環境・実現可能性・許容性・操作宣言の閉性の下で成功した出力の主要計算型を保証します。

完全性の定理 `solver_complete_fragment` は、`simplify(G ∧ normalize(W))` が `DecisionFragment` に入り、`G ∧ W` が充足可能な場合に成功を保証します。判定断片の概形は次のとおりです。

```text
F ::= ⊤ | F ∧ F | C(α) | ε ⊆ η | o ∉ ε
D ::= F | ∃A.D
```

型等式の逐次消去も実装していますが、handler-free な生成制約すべてがこの判定域へ到達する証明はありません。具体的 solver 全体の `PartialSolver.Complete` や、全制約言語の `SatDecider` は未構成です。

参照：[Solver.lean](lean/EHMX/TypeClasses/Solver.lean)、[Completeness.lean](lean/EHMX/TypeClasses/Completeness.lean)、[Decision.lean](lean/EHMX/TypeClasses/Decision.lean)、[Normalizer.lean](lean/EHMX/TypeClasses/Normalizer.lean)。

## 4. これから証明すべきことと完了条件

### 優先1：抽象 `X` と一般の `S` で型項再構成を完了する

1. **具体的な制約系の条件**：定理7で明示した主要正規化・閉性・lifting を具体的な解決済み集合について証明する。効果専用の残余の局所例と、全制約の正規化器の存在を区別する。
2. **導出変換の残り**：任意の qualified 型への `existsIntro` の変換を証明する。定理16に必要な生成導出の変換は完了している。
3. **定理17の後続**：`equalityTypes` での環境・qualified 型・外側条件の同時比較は完了。任意の `TypeDomain` への拡張は別途検討する。
4. **系7相当は完了**：明示した前提の下で、同じ `S`・元の閉環境の主要計算型と値の主要型を証明済み。次は具体的制約系がその前提を満たすことを証明する。

この段階の完了条件は、**同じ `S` での出力健全性と qualified 型までの完全性・主要性が、実際の `inferTerm` の結果について成立すること**です。受理だけ、単相型の有限因子だけ、または `S = Sat_X` での `normalized_principal_computation` をもって完了とはしません。必要な導出変換や qualified 比較を、証明せず推論契約の仮定に追加することもしません。

### 優先2：具体的 `X_tc` の handler-free な範囲を完全にする

検査済み宣言に対し、次の基底断片全体の充足可能性判定を実装し、正しさ・停止性・充足可能な入力での成功を証明します。

```text
B ::= ⊤ | ⊥ | B ∧ B | t = u | C(t) | ε ⊆ η | o ∉ ε | ∃A.B
```

存在量化、suspension、型等式、新鮮化、捕獲回避、量化の移動を扱い、消去回数の上限の十分性を証明するか整礎再帰へ置き換えます。その上で、式だけでなく環境内の制約もこの範囲に制限し、handler-free な生成制約が判定域に入ることと合成完全性を証明します。残余から等式や存在量化をすべて除去すること自体は完了条件にしません。

### 優先3：handler の量化制約を具体的に判定する

基底断片の完全性の後に、`∀B.∃J.D` の判定域を定義します。証人がどの変数に依存できるか、外側変数の保護、非脱出、量化順序と同値性の保存を証明し、生成・solver との合成を行います。

現時点では handler による完全性の不可能性や判定不能性を主張していません。未解決を返す例や未証明箇所だけでは、その根拠になりません。不完全性を主張する場合は、基底の実装不足と分け、量化・依存関係・出力形式・解法の制限に由来する反例を示す必要があります。

## 5. 検証と対象外

証明・実行例は次のファイルにあります。判定器を仮定した例と、具体的 solver を実行した例を区別しています。

| ファイル | 検証内容 |
| --- | --- |
| [AlgorithmExamples.lean](lean/EHMX/HMX/AlgorithmExamples.lean) | 多相 let、再開 handler、入れ子 handler。抽象判定器を仮定した主要出力など |
| [OpenExamples.lean](lean/EHMX/HMX/OpenExamples.lean) | 非恒真の外側条件、対象制約下でのみ実現可能な開環境、qualified 型比較、開環境の handler |
| [ReconstructionExamples.lean](lean/EHMX/HMX/ReconstructionExamples.lean) | 捕獲回避、非冪等な代入、新鮮化、表現不能と不整合の区別、判定器を仮定した再構成の受理 |
| [TransformationExamples.lean](lean/EHMX/HMX/TransformationExamples.lean) | 定理7の公開定理による入れ子の多相 let・特殊化、開環境の捕獲回避、潜在効果の保存。効果専用の残余の例 |
| [TypeClasses/Examples.lean](lean/EHMX/TypeClasses/Examples.lean) | 具体的 solver による型クラス、多相 let、perform、handler、量化順序の実行検証と、再開 handler の ground 型付け証明 |

Lean と mathlib のバージョンは [lean-toolchain](lean/lean-toolchain) と [lakefile.toml](lean/lakefile.toml) で固定しています。全体ビルドは次のコマンドです。

```sh
cd lean
lake build
```

定理7の公理依存は、`lean/` で次のように確認できます。依存は `propext`・`Classical.choice`・`Quot.sound` のみです。

```sh
lake env lean --stdin <<'LEAN'
import EHMX
#print axioms EHMX.HMX.Derivation.theorem7_core
#print axioms EHMX.HMX.Derivation.theorem7_mono_core
LEAN
```

証明を変更した際は全体ビルドと公理依存の監査を行い、`sorry`・`admit`・独自公理・`native_decide` で証明を置き換えません。PDF の定義・前提・保証範囲も更新し、再生成と表示確認を行います。

対象は Lean と PDF による型付け・推論の形式化です。実行時の preservation/progress（型・効果安全性）は未証明で、現在の完了条件には含めません。Rust 実装、未注釈 let 全体の単相化も対象外です。
