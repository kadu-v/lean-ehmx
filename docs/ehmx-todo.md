# EHMX の証明 TODO

最終目標は制約生成の健全性（ATTAPL 10.4.4の拡張）、完全性（10.4.8の拡張）、主要制約性（429–430頁の拡張）、保存・進行・到達状態の効果安全性である。**進行性、スキーム値代入、操作捕捉を含む一歩・多歩保存、到達状態の効果安全性は証明済み。推論の健全性・完全性・主要制約性は未証明。** チェックは名前を宣言しただけでは付けず、Lean の証明と依存を確認して付ける。

## 証明済み

- [x] 構文・kind・値・操作宣言・評価文脈・deep handler の簡約を追加。
- [x] 型付けに値 let と単相 let を分けて追加。型・効果で多相な操作節を任意の変数の下で検査。
- [x] 全称制約の意味と構文に沿う generate / infer を追加。生成規則の健全性は別項目。
- [x] Concrete.framework / Concrete.arrowSeparated。具体モデルで抽象的な前提を検証。安全性そのものを前提に含めない。
- [x] kindShift / kindAppend。型変数の文脈拡張で kind を保存。生成規則と操作節の束縛に使用。
- [x] operationInstantiation。宣言の型・効果変数を kind の合う引数で具体化。perform と操作節の代入の基礎。
- [x] evalKind / evalShift。解釈の kind 保存と、束縛の持上げ・割当ての拡張の整合性。制約の存在量化と進行性で使用。
- [x] forallHoldsIntro / forallHoldsElim / forallConjunction。全称制約の基本法則。型付け・生成の対応全体は未証明。
- [x] schemeUpperSet / monoInstance。スキーム解釈の上方閉性と単相スキームの自己具体化。変数型付けと将来の代入証明で使用。
- [x] valuePure。型付き値は空効果で型付け可能。β、let、return、操作簡約の値代入で使用。
- [x] closedValueLambda。閉じた値は lambda 抽象。進行性の適用分岐で使用。
- [x] evalCtxShiftPlug / valueShift / resumeValue。文脈の持上げと穴埋めの交換、値の保存、継続が値であること。継続の型付けは下記の resumeTyping で証明。
- [x] generationWF / generationScope。生成制約の kind・束縛・自由項変数の性質。健全性の整形式条件で使用。
- [x] typingDeclared / unknownPerformNotTypable。型付け可能な項の操作宣言の存在。健全性の入力条件を検証。
- [x] progressGeneral / progressEffectSafety。充足する割当ての下で値・簡約・許された未処理操作の三場合を証明。
- [x] emptyEffectProgress。空効果での現在の状態の進行。任意の到達状態の安全性とは別。

## 保存に必要な代入・反転・文脈の証明

- [x] `typingTypeEffectSubstitution`。任意の型文脈への型・効果代入に対して、制約・スキーム・環境・結果型・効果を同時に変換する。letPoly / handle / exists_ で持ち上げた代入を使用する。`BoundSubst.Valid` は、型文脈の未使用の未宣言 kind も同じ kind の添字へ移せる。最終 Goal に型文脈全体の宣言済み条件を追加していない。
- [x] `kindSubstBound`、`substBoundWF`、`substBoundFpi`、`substBoundSemantics`、`entailsSubstBound`。上記の各規則に必要な kind・整形式性・自由項識別子・意味解釈・含意の保存。存在／全称量化と def / defFree の双方を扱い、意味論の証人の構文による表現可能性を仮定しない。
- [x] `typingInstantiate`、`operationClauseInstantiation`。操作の型・効果変数を同じ引数列で具体化する。後者は操作節の型付けの具体化であり、項の二値同時代入や操作簡約の保存ではない。
- [x] `typingWeakeningAt`、`typingWeakening`。任意の項束縛位置に整形式スキームを挿入する。使用先は値代入の束縛分岐と継続の新しい lambda。return は一束縛、操作節は二束縛として扱う。
- [x] `schemeValueInstantiation`、`generalizedValueRealizes`。一般化導出から、型文脈変更と制約強化の後の各利用時の型付けを構成する。`RealizesScheme` は値代入の帰納法の局所前提であり、最終定理では一般化導出から証明している。モデルに安全性の仮定を加えたものではない。
- [x] `typingValueSubstitutionAux`、`schemeValueSubstitution`。強い制約について帰納仮定を一般化し、exists_ の内側では強い外側制約の shift と内側制約の連言を使用する。`schemeValueSubstitution : SchemeValueSubstitutionGoal S M sig` をそのまま証明した。
- [x] `valueSubstitution`、`valueOpening`。単相値代入を上記から導出し、β・return・単相 let に適用する。値制限は項の開きが値を保つことで維持する。
- [x] `valueNoStep`、`evalCtxValue`、`evalCtxReplacement`。文脈内で簡約可能な穴は値ではなく、letPoly 分岐を除外できる。穴の置換を Δ・C・Γ・型・効果の全体について量化することで、exists_ を含む文脈の簡約に対応する。
- [x] `lambdaApplication`、`betaPreservation`、`letPreservation`、`returnPreservation`。lambda の反転は制約強化と存在量化を含む。let は単相・多相の両方を扱い、閉項や具体モデルへの制限を加えていない。

## 操作保存・保存・到達状態の安全性

ATTAPL §10.5 の保存（10.5.8）・型安全性（10.5.11）に対応する EHMX 拡張を完成した。`Goals.lean` の前提・結論を維持し、閉項・具体モデルへの保存定理の限定や、操作保存を前提とした最終定理は導入していない。

`ContextTyping` は任意の型文脈の拡張・制約強化・新しい項束縛の下で評価文脈を再構成する局所命題である。各評価文脈の構成子について元の導出から証明し、最終定理の追加前提にはしていない。`operationElimination` の帰納法では、外側の Γ・制約・操作節を存在量化の内側へ移し、同じ引数列から操作の入力型・結果型を具体化する。

- [x] `ContextTyping.appFun` / `appArg` / `letRhs` / `perform` / `handle`、`ContextTyping.shift` / `stronger` / `sub`、`operationClauseShift`。評価文脈の全構成子と型文脈・制約の移動を扱う。
- [x] `operationElimination`、`resumeContextTyping`、`resumeTyping`。存在量化の内側で継続と代入結果を構成し、最後に Typing.exists_ と制約強化で元の判断へ戻す。外側に一律の型引数の存在を要求しない。letPoly の右辺は操作を含む項が非値であることから除外する。
- [x] `exprOpenShiftSucc`、`exprOpenTwo`、`twoValueSubstitution`。操作節の `[継続, 引数値]` の順序で型付き同時代入を証明。開いた環境でも外側の項変数を保持し、一束縛・二束縛の構文を扱う。
- [x] `operationPreservation : OperationPreservationGoal S M sig`。外側の sub / strengthen / exists_ も含む操作捕捉の保存。
- [x] `preservation : PreservationGoal S M sig`。Step の帰納法で Δ・C・Γ・型・効果を一般化し、β・let・return・操作捕捉・文脈簡約を統合。
- [x] `preservationSteps`、`effectSafety`、`emptyEffectSafety`。多歩保存は任意の Δ C Γ T ε を保持する。安全性は既存の進行性と結合し、二つの SafetyGoal 全体を満たす。

## 推論の健全性 完全性 主要制約性

- [x] 全称制約と束縛された型・効果代入の意味的交換は `substBoundSemantics` で証明。これを使用する handlerGeneration 自体は未証明。
- [ ] inferWF / inferScope。環境を付加した infer の整形式性と自由項識別子の消去。generationWF / generationScope だけでは完了にしない。
- [ ] generationMonotone。要求型・評価効果の上界を広げる場合の含意。使用先は完全性の部分型分岐。handler の内部出力型・効果を外側の要求で置き換えない。
- [ ] valueLetGeneration / monoLetGeneration。値の一般化と、非値で単相型を共有する生成規則の両方向の対応。使用先は健全性・完全性の let 分岐。
- [ ] performGeneration / handlerGeneration。宣言の具体化、入力効果包含、return 節、任意の型・効果変数に対する操作節の対応。使用先は健全性・完全性の新しい分岐。
- [ ] syntaxDirectedTypingEquivalence。宣言的型付けから構文に沿う型付けへの変換と逆方向。一般化を値だけに制限する。使用先は完全性の帰納法。
- [ ] environmentRealizabilityExtension。lambda、let、return、操作節の環境拡張で必要な実現可能性。使用先は完全性の各帰納仮定。
- [ ] generatedSchemeComparison。値 let の宣言スキームと生成スキームの意味的包含。既存 HMX の completenessLet に対応する使用先を確認してから証明。
- [ ] inferenceSoundness。InferenceSoundnessGoal を証明。項の作用域と Expr.Declared を明示し、未宣言操作の拒否と区別する。
- [ ] inferenceCompleteness。InferenceCompletenessGoal を証明。環境実現可能性を各分岐へ引き継ぐ。
- [ ] constraintGenerationPrincipality。健全性と完全性を結合して PrincipalityGoal を証明。主要解・ソルバーの正当性は主張しない。

## 回帰と文書

- [x] 型・効果の混合引数を持つ操作宣言の整形式性。
- [x] identityTyping / polymorphicLetTyping。推論定理に依存しない恒等関数と多相 let の型付け導出。
- [x] let 右辺での操作捕捉、同じ操作の内側 handler、異なる操作の透過、操作節から同じ操作を再実行する場合。
- [x] 未宣言操作の偽制約と型付け不能、非値 let が共有する単相型の生成構造、作用域外の型変数の kind 不成立。
- [ ] 一つの let 多相値を異なる型・効果で同時に使う型付け例と非値での非導出。
- [x] `mixedClauseTyping`、`mixedClauseInstantiated`、`returnHandlerTyping`。型・効果の混合引数を持つ操作節と、完全な return handler の型付け。操作捕捉の保存を適用する回帰ではない。
- [x] `SafetyRegression.lean`。混合引数の操作捕捉、let 右辺、継続の二回利用とその多歩簡約、外側の項変数、同じ操作の内側 handler、異なる操作の通過、操作節からの再実行について、実際の型付けに最終保存定理を適用。
- [x] `existentialOperationTyping`、`existentialCapturePreserved`。操作の具体化引数に存在束縛の型変数そのものを使い、操作への経路上で exists_ / strengthen / sub を重ねる。
- [x] `resumedHandlerReachableSafe`、`emptyEffectMultistepSafety`、`nonemptyEffectReachableSafety`、`reperformAllowedUnhandled`。空効果の到達状態の安全性と、非空効果で許された再実行操作を検査。
- [ ] 型変数の逃走を試みるプログラムの非導出。現在の回帰は kind の作用域外参照の拒否と、存在量化内での捕捉・保存を検査している。
- [ ] 推論定理完成後、生成制約の充足と型付けの両方向を具体例に適用。
- [x] `betaTypedReduction`、`monomorphicLetTypedReduction`、`polymorphicLetTypedReduction`、`returnTypedReduction`。実際の型付け導出に簡約別の保存を適用。
- [x] `wrappedBetaTypedReduction`、`letRhsBetaTypedReduction`。exists_ / strengthen / sub を重ねた導出と let 右辺の文脈簡約に保存補題を適用。
- [x] 既存 HMX を維持し、EHMX と回帰例を標準ビルド対象に追加。
- [x] 仕様の日本語説明と Lean 宣言の直接取り込みによる仕様PDFの生成手順を追加。
- [x] 保存・安全性の最終定理を標準 import に含め、依存公理と正確な Goal 型を検査する。
- [ ] 推論三定理の完成時に、その Goal 型と依存公理も検査する。PDF 作業は明示的な依頼があった場合のみ行う。

## 計画から具体化した点

健全性に操作の宣言済み条件 Expr.Declared を追加して明示した。未宣言の perform は偽制約の下でも型付け不能なため、この条件なしの健全性は目標にしない。自由な変数の名前を生成せず内部に束縛添字を使うため、generationFreshInvariant の代わりに束縛の持上げ・開閉と意味の整合性を証明する。型シグネチャの追加と効果付き関数型は EHMX 内に置き、HMX の二引数関数型を変更しない。

帰納法が閉じない場合は、先に目標の前提・結論と帰納仮定を比較する。必要な前提の追加や対象の制限は必ずここにも記録し、元の目標全体の完成と混同しない。

## 今回の検査範囲

標準 `EHMX` import に新しい全証明と回帰例を含める。`tests/EHMXGoals.lean` は `ProgressGoal`、`SchemeValueSubstitutionGoal`、`OperationPreservationGoal`、`PreservationGoal`、`EffectSafetyGoal`、`EmptyEffectSafetyGoal` と、任意の Δ C Γ T ε に対する `preservationSteps` の完全な型を検査する。公理監査は標準の三公理以外を認めず、追加の安全性公理や sorry を認めない。

検査結果：`lake build`（828 jobs）、`lake env lean tests/EHMXAxioms.lean`（782件の定理）、`lake env lean tests/EHMXGoals.lean`、`git diff --check` が成功。推論三定理は検査対象となる証明がまだなく、今回の保存・安全性の完成には含めない。PDF の更新・再生成・整合性検査は実施していない。

次の証明作業は `InferenceSoundnessGoal` に必要な `inferWF`・`inferScope`。既存の `generationWF`・`generationScope` を環境付きの infer へ接続し、各型付け判断の制約の整形式性と自由項識別子の消去を確保する。
