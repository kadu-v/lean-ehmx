# 証明範囲と原典番号の対応

この文書の件数と原典対応は既存の **HMX 基盤**についてのものです。追加した EHMX の効果付き進行性、型・効果代入、スキーム値代入、操作捕捉を含む保存・到達状態の安全性と、推論三定理の証明は [EHMX の証明 TODO](ehmx-todo.md) と [仕様](ehmx-spec.md) に分けて記録しています。

EHMX では ATTAPL §10.5 の保存（10.5.8）・型安全性（10.5.11）に対応する拡張を証明しました。`operationElimination` は存在量化の内側で操作の型引数・継続・二値代入を扱い、`operationPreservation` は `OperationPreservationGoal` を満たします。[Preservation.lean](../EHMX/Proofs/Preservation.lean) の `preservation`、`preservationSteps`、`effectSafety`、`emptyEffectSafety` が一歩・多歩保存と到達状態の保証を与えます。これらは EHMX 固有の多相操作・deep handler・値制限付き let を含む定理であり、以下の HMX の未証明命題を証明済みに変更するものではありません。

## 証明済みの範囲

制約推論・表現対応51件、型クラス固定モデルの構成・適用10件、合計61件の登録済み命題に、それぞれ元の命題と同じ型の証明があります。この数は章全体の命題数ではありません。原文のステートメントは `def ... : Prop`、証明は別の `theorem` 宣言です。型付け規則の `inductive` 宣言やステートメントの型検査だけを証明済みと数えません。

名前付き版の証明は [InferenceTransfer.lean](../HMX/LocallyNameless/Proofs/InferenceTransfer.lean) にあります。

- `HMX.Proofs.theorem10_4_4_soundness_scoped` は `HMX.theorem10_4_4_soundness_scoped` を証明します。原文の10.4.4の転記とは別に `t.fpi ⊆ Γ.dpi` を明示した命題です。環境の実現可能性は要求しません。
- `HMX.Proofs.theorem10_4_8_completeness` は原文に対応する `HMX.theorem10_4_8_completeness` を証明します。既存の環境実現可能性条件 `C ⊨ Γ.exists_` を保ち、追加の充足可能性や作用域条件は要求しません。
- `HMX.Proofs.constraintGenerationPrincipality_scoped` は `HMX.constraintGenerationPrincipality_scoped` を証明します。作用域条件付きの健全性と完全性を組み合わせた、固定した環境・項・期待型に対する主要制約性です。最汎代入やソルバーの存在を述べるものではありません。

作用域条件付き命題の定義は [Correspondence.lean](../HMX/LocallyNameless/Correspondence.lean#L77) にあります。原文の作用域条件なしの `HMX.theorem10_4_4_soundness` と `HMX.constraintGenerationPrincipality` は [Inference.lean](../HMX/Inference.lean) に保存され、未証明です。LN版が要求する項の局所閉性 `LCAt 0` は、名前付き構文の符号化について `encodingWF` から得ます。

## 原典の定理・補題・系

次表の命題は名前付き転記です。LN版で証明した補題と、名前付き転記そのものの証明を区別しています。固有名のない項目に名前を補っていません。番号のない429–430頁の主要制約性は上記のとおり扱います。

| 原典番号・正式名 | 印刷頁 | 名前付き命題 | 証明の範囲 |
| --- | --- | --- | --- |
| Theorem 10.2.13 / Congruence | 416 | [HMX.theorem10_2_13_congruence](../HMX/ConstraintLaws.lean#L54) | 名前付き命題は未証明。[LN版の証明](../HMX/LocallyNameless/Proofs/ConstraintLaws.lean#L12) |
| Theorem 10.2.15 / 固有名なし | 417 | [HMX.theorem10_2_15](../HMX/ConstraintLaws.lean#L140) | 未証明 |
| Lemma 10.2.17 / 固有名なし | 420 | [HMX.lemma10_2_17](../HMX/ConstraintLaws.lean#L149) | 未証明 |
| Lemma 10.2.19 / 固有名なし | 421 | [HMX.lemma10_2_19](../HMX/SolvedForms.lean#L51) | 未証明 |
| Lemma 10.2.21 / 固有名なし | 422 | [HMX.lemma10_2_21](../HMX/SolvedForms.lean#L55) | 未証明 |
| Lemma 10.3.1 / Weakening | 426 | [HMX.lemma10_3_1_weakening](../HMX/Typing.lean#L103) | 名前付き命題は未証明。[LN版の証明](../HMX/LocallyNameless/Proofs/Weakening.lean#L208) |
| Theorem 10.3.4 / 固有名なし | 427 | [HMX.theorem10_3_4](../HMX/Typing.lean#L113) | 名前付き命題は未証明。[LN版の証明](../HMX/LocallyNameless/Proofs/TypingEquivalence.lean#L345) |
| Theorem 10.3.6 / 固有名なし | 428 | [HMX.theorem10_3_6](../HMX/Typing.lean#L117) | 未証明 |
| Theorem 10.3.7 / 固有名なし | 428 | [HMX.theorem10_3_7](../HMX/SolvedForms.lean#L81) | 未証明 |
| Theorem 10.4.4 / Soundness | 433 | [HMX.theorem10_4_4_soundness](../HMX/Inference.lean#L34) | 原文の命題は未証明。[別の作用域条件付き命題の証明](../HMX/LocallyNameless/Proofs/InferenceTransfer.lean#L38) |
| Lemma 10.4.5 / 固有名なし | 433 | [HMX.lemma10_4_5](../HMX/Inference.lean#L38) | 名前付き命題は未証明。[LN版の証明](../HMX/LocallyNameless/Proofs/GenerationProperties.lean#L93) |
| Lemma 10.4.6 / 固有名なし | 433 | [HMX.lemma10_4_6](../HMX/Inference.lean#L42) | 名前付き命題は未証明。[LN版の証明](../HMX/LocallyNameless/Proofs/GenerationProperties.lean#L98) |
| Lemma 10.4.7 / 固有名なし | 433 | [HMX.lemma10_4_7](../HMX/Inference.lean#L46) | 名前付き命題は未証明。[LN版の証明](../HMX/LocallyNameless/Proofs/GenerationProperties.lean#L132) |
| Theorem 10.4.8 / Completeness | 434 | [HMX.theorem10_4_8_completeness](../HMX/Inference.lean#L50) | [HMX.Proofs.theorem10_4_8_completeness](../HMX/LocallyNameless/Proofs/InferenceTransfer.lean#L57) |
| Lemma 10.5.1 / 固有名なし | 434 | [HMX.lemma10_5_1](../HMX/Safety.lean#L7) | 未証明 |
| Lemma 10.5.7 / 固有名なし | 438 | [HMX.lemma10_5_7](../HMX/Safety.lean#L99) | 未証明 |
| Theorem 10.5.8 / Subject reduction | 438 | [HMX.theorem10_5_8_subjectReduction](../HMX/Safety.lean#L103) | 未証明 |
| Corollary 10.5.9 / 固有名なし | 438 | [HMX.corollary10_5_9](../HMX/Safety.lean#L108) | 未証明 |
| Theorem 10.5.10 / Progress | 438 | [HMX.theorem10_5_10_progress](../HMX/Safety.lean#L113) | 未証明 |
| Theorem 10.5.11 / Type Soundness | 438 | [HMX.theorem10_5_11_typeSoundness](../HMX/Safety.lean#L123) | 未証明 |

## 61件の内訳

以下は証明ファイルごとに集約した範囲です。名前は命題の末尾名で、最初の22行は制約推論・表現対応51件、最後の行は `HMX.TypeClasses` の新しい構成・適用10件です。`InferenceTransfer` の3件は名前付き `HMX`、それ以外の51件側は `HMX.LN` の命題です。原典番号のない補助命題に番号は割り当てません。各ファイルには、この集計外の証明用補助補題も含まれます。

| 証明ファイル | 件数 | 対象命題（末尾名） |
| --- | ---: | --- |
| [Binding.lean](../HMX/LocallyNameless/Proofs/Binding.lean) | 3 | `termOpeningClosing`、`typeOpeningClosing`、`constraintOpeningClosing` |
| [WellFormed.lean](../HMX/LocallyNameless/Proofs/WellFormed.lean) | 2 | `typeOpeningWF`、`freeSubstitutionWF` |
| [Substitution.lean](../HMX/LocallyNameless/Proofs/Substitution.lean) | 2 | `termOpeningSubstitution`、`typeOpeningSubstitution` |
| [Semantics.lean](../HMX/LocallyNameless/Proofs/Semantics.lean) | 5 | `evaluationKind`、`schemeDenotationValid`、`semanticLocality`、`semanticSubstitution`、`groundEnvironmentMonotonicity` |
| [Permutations.lean](../HMX/LocallyNameless/Proofs/Permutations.lean) | 1 | `binderPermutationSemantics` |
| [ConstraintLaws.lean](../HMX/LocallyNameless/Proofs/ConstraintLaws.lean) | 3 | `constraintCongruence`、`basicConstraintLaws`、`letSub` |
| [Environment.lean](../HMX/LocallyNameless/Proofs/Environment.lean) | 5 | `prefixConjunction`、`prefixExists`、`prefixLookup`、`letDup`、`letSchemeMonotonicity` |
| [Generation.lean](../HMX/LocallyNameless/Proofs/Generation.lean) | 6 | `generationWF`、`generationFreeVariables`、`generationSubstitution`、`generationOpening`、`generationFreshChoices`、`closedGenerationWF` |
| [TypingSupport.lean](../HMX/LocallyNameless/Proofs/TypingSupport.lean) | 1 | `typingProperties` |
| [Weakening.lean](../HMX/LocallyNameless/Proofs/Weakening.lean) | 1 | `lemma10_3_1_weakening` |
| [TypingSubstitution.lean](../HMX/LocallyNameless/Proofs/TypingSubstitution.lean) | 2 | `alternateWeakening`、`alternateSubstitution` |
| [TypingEquivalence.lean](../HMX/LocallyNameless/Proofs/TypingEquivalence.lean) | 2 | `schemeElimination`、`theorem10_3_4` |
| [GenerationProperties.lean](../HMX/LocallyNameless/Proofs/GenerationProperties.lean) | 3 | `lemma10_4_5`、`lemma10_4_6`、`lemma10_4_7` |
| [GeneratedSchemes.lean](../HMX/LocallyNameless/Proofs/GeneratedSchemes.lean) | 2 | `generatedInstance`、`generalizedLetComparison` |
| [InferenceSoundness.lean](../HMX/LocallyNameless/Proofs/InferenceSoundness.lean) | 1 | `theorem10_4_4_soundness_scoped` |
| [InferenceCompleteness.lean](../HMX/LocallyNameless/Proofs/InferenceCompleteness.lean) | 1 | `theorem10_4_8_completeness` |
| [InferencePrincipality.lean](../HMX/LocallyNameless/Proofs/InferencePrincipality.lean) | 1 | `constraintGenerationPrincipality_scoped` |
| [Encoding.lean](../HMX/LocallyNameless/Proofs/Encoding.lean) | 4 | `encodingWF`、`encodingFreeVariables`、`encodingAlpha`、`encodingSemantics` |
| [FrameworkCorrespondence.lean](../HMX/LocallyNameless/Proofs/FrameworkCorrespondence.lean) | 1 | `frameworkCorrespondence` |
| [TypingCorrespondence.lean](../HMX/LocallyNameless/Proofs/TypingCorrespondence.lean) | 1 | `typingCorrespondence` |
| [GenerationCorrespondence.lean](../HMX/LocallyNameless/Proofs/GenerationCorrespondence.lean) | 1 | `generationCorrespondence` |
| [InferenceTransfer.lean](../HMX/LocallyNameless/Proofs/InferenceTransfer.lean) | 3 | `theorem10_4_4_soundness_scoped`、`theorem10_4_8_completeness`、`constraintGenerationPrincipality_scoped` |
| [TypeClasses.lean](../HMX/LocallyNameless/Proofs/TypeClasses.lean) | 10 | `fixedModelRequirements`、`fixedArrowLaw`、`fixedIsolation`、`fixedFramework`、`classAtomMeaning`、`superclassEntailment`、`instanceEntailment`、`namedSoundness`、`namedCompleteness`、`namedPrincipality` |

## 証明経路

束縛操作・WF・代入、意味論、制約法則、型付け、制約生成の順に基礎を整え、10.4.5 → 10.4.6 → 10.4.7を証明しています。Figure 10-6は必要な法則を用い、全21法則や穴0個を含む10.2.17を証明の前提にはしていません。新鮮名は有限の除外集合から選び、環境キーの一意性は仮定しません。

LN健全性は項の構造への帰納法を使い、Figure 10-8と10.3.4を経て元の型付けへ戻します。LN完全性はFigure 10-8の導出への帰納法で、環境実現可能性を各帰納仮説へ接続します。完全性の証明は健全性に依存しません。LN主要制約性は健全性と完全性を組み合わせます。

名前付き／LN型付けの対応はFigure 10-7の導出に対する両方向の帰納法です。任意の整形式LN制約・スキームから、意味と自由名集合を保存する名前付き代表を選びます。定数タグの遮蔽を含む任意の構文的逆変換を要求せず、新鮮な項変数による `def` 束縛で代表を構成します。代表の意味保存をα同値や `BinderEq` と同一視しません。環境全体が実現不能でも未使用の束縛を含む型付けは可能なので、型付け対応を推論完全性へ迂回させていません。

Framework・生成制約・型付けの対応から名前付き版へ移送します。生成制約の同値は既存の `convert` で型付けに反映し、完全性では既存の環境実現可能性を符号化してLN完全性を適用します。名前付き主要制約性は移送済みの名前付き健全性と完全性から得ます。モデル要素一般を型構文で表せるという仮定は追加していません。

型クラスの10件は、具体モデルの要件・関数型法則・分離・Framework・所属の意味・スーパークラス・条件付きインスタンスを示した上で、名前付き推論3定理を適用する構成です。原典の新たな番号付き定理とは扱いません。

## 限界と検証

DM翻訳（10.3.7）、型安全性（10.5）、ソルバー（10.6以降）、原文の作用域条件なしの健全性・主要制約性は証明範囲外です。原典の省略や表現上の選択の未解決事項は [sources.md](sources.md) に残しています。証明済みの表現対応も、操作的意味論全体の商構文との同値を主張しません。

`lake build` は全証明と [CorrespondenceRegression.lean](../HMX/LocallyNameless/Proofs/CorrespondenceRegression.lean)、[TypeClassesRegression.lean](../HMX/LocallyNameless/Proofs/TypeClassesRegression.lean) の回帰例を検査します。証明に穴埋めや追加公理は用いず、許容する標準公理依存は `propext`・`Classical.choice`・`Quot.sound` です。有限個の回帰例とビルド成功は、未証明命題の成立や原典との完全一致を証明するものではありません。
