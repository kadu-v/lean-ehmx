import EHMX

/-! 推論の環境・生成・局所規則補題を公開入口から型検査する。
InferenceSoundnessGoal / InferenceCompletenessGoal / PrincipalityGoal 全体は未証明。
最終三定理の型検査をこのファイルで代用しない。 -/
#check EHMX.inferWF
#check EHMX.inferScope
#check EHMX.generationSubstitution
#check EHMX.generationMonotone
#check EHMX.generationValuePure
#check EHMX.generatedSchemeComparison
#check EHMX.inferenceVariable
#check EHMX.inferenceValueLet
#check EHMX.InferenceRegression.shadowedVariableSoundness
#check EHMX.InferenceRegression.deepVariableSoundness
#check EHMX.InferenceRegression.impossibleEnvironmentSoundness
#check EHMX.InferenceRegression.openValueLetSoundness
#check EHMX.InferenceRegression.mixedHandlerInferWF
#check EHMX.InferenceRegression.mixedHandlerGenerationSubstitution
#check EHMX.InferenceRegression.mixedUniversalEnvironment
#check EHMX.InferenceRegression.valueLetAtTwoRequests
