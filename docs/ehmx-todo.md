# EHMX の証明 TODO

最終目標は制約生成の健全性（ATTAPL 10.4.4の拡張）、完全性（10.4.8の拡張）、主要制約性（429–430頁の拡張）、保存・進行・到達状態の効果安全性である。**現時点では進行性まで証明済みであり、計画全体は未完了。** チェックは名前を宣言しただけでは付けず、Lean の証明と依存を確認して付ける。

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
- [x] evalCtxShiftPlug / valueShift / resumeValue。文脈の持上げと穴埋めの交換、値の保存、継続が値であること。継続の型付け自体は未証明。
- [x] generationWF / generationScope。生成制約の kind・束縛・自由項変数の性質。健全性の整形式条件で使用。
- [x] typingDeclared / unknownPerformNotTypable。型付け可能な項の操作宣言の存在。健全性の入力条件を検証。
- [x] progressGeneral / progressEffectSafety。充足する割当ての下で値・簡約・許された未処理操作の三場合を証明。
- [x] emptyEffectProgress。空効果での現在の状態の進行。任意の到達状態の安全性とは別。

## 保存定理へ向けた次の作業

以下の順序で行う。各補題を始める前に、使用先の分岐で必要な環境・制約・束縛深さを展開する。

- [ ] **最優先：typingTypeEffectSubstitution。** kind を保つ型・効果代入について、制約・スキーム・環境も同時に代入して型付けを保存する。letPoly と handle の量化変数を捕獲しない代入操作と、その意味の交換則から実装する。使用先はスキーム値代入と操作節の具体化。
- [ ] typingWeakening。項環境の改名・拡張と型付けの保存。使用先は捕捉した継続の新しい lambda 束縛と、値代入の帰納法。
- [ ] valueSubstitution。Gamma,x:A の下の項へ、Gamma で空効果の値 v:A を捕獲回避代入する。使用先は β と return。
- [ ] **schemeValueSubstitution。** Goals.SchemeValueSubstitutionGoal の全前提・結論を満たす証明。値 v の一般化導出と各具体化の対応を保つ。使用先は多相 let の簡約。単相の代入だけでは完了にしない。
- [ ] typingInversion。部分型・制約強化・存在量化を含む導出の反転。存在変数に依存する具体化引数を、その作用域の外へ出さない。使用先は簡約別の保存。
- [ ] evalCtxReplacement / evalCtxSubterm。let 右辺を含む評価文脈の型付け。多相化可能な値と、実際に評価する非値の区別を帰納法に保持する。使用先は文脈簡約と継続構成。
- [ ] **resumeTyping。** 操作簡約の導出を反転した文脈の内側で、捕捉した継続を OpResult ->[epsOut] B として型付けする。操作の型引数は任意に選ばず、反転で得た具体化を使う。外側に一律の型引数の存在を要求する補題は追加しない。
- [ ] operationClauseInstantiation。操作節の量化変数を具体化し、[継続, 引数値] を同時代入する。使用先は OperationPreservationGoal。
- [ ] betaPreservation / letPreservation / returnPreservation / operationPreservation。上記の代入と反転から簡約ごとの保存を証明。
- [ ] preservation。PreservationGoal 全体を証明。進行性や保存そのものを仮定に入れない。
- [ ] preservationSteps / effectSafety / emptyEffectSafety。一歩保存から多歩保存を証明し、証明済みの進行性と結合する。EffectSafetyGoal と EmptyEffectSafetyGoal の成立を確認。

## 推論の健全性 完全性 主要制約性

- [ ] forallConstraintLaws の改名・代入部分。全称制約と型・効果代入の意味的な交換、内側の存在量化との作用域を検証。使用先は handlerGeneration。
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
- [ ] 多相操作の完全な handler 型付け、継続の複数回利用、型変数の逃走を試みるプログラムの非導出。
- [ ] 推論定理完成後、生成制約の充足と型付けの両方向を具体例に適用。
- [x] 既存 HMX を維持し、EHMX と回帰例を標準ビルド対象に追加。
- [x] 仕様の日本語説明と Lean 宣言の直接取り込みによる仕様PDFの生成手順を追加。
- [ ] 保存・推論の最終定理が通った時点で、全目標の依存公理と仕様PDFの証明状況を再確認する。

## 計画から具体化した点

健全性に操作の宣言済み条件 Expr.Declared を追加して明示した。未宣言の perform は偽制約の下でも型付け不能なため、この条件なしの健全性は目標にしない。自由な変数の名前を生成せず内部に束縛添字を使うため、generationFreshInvariant の代わりに束縛の持上げ・開閉と意味の整合性を証明する。型シグネチャの追加と効果付き関数型は EHMX 内に置き、HMX の二引数関数型を変更しない。

帰納法が閉じない場合は、先に目標の前提・結論と帰納仮定を比較する。必要な前提の追加や対象の制限は必ずここにも記録し、元の目標全体の完成と混同しない。
