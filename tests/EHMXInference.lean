import EHMX

/-! 推論補題の公開入口と、最終三定理の具体例への適用を検査する。
Goal 型そのものの検査は EHMXGoals.lean で行う。 -/
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

open EHMX EHMX.Regression EHMX.InferenceRegression

example : Entails Concrete.signature Concrete.model [] .truth
    (infer signature openEnv (.ident (.free 7)) identityType .empty) := openShadowedRoundTrip.1

example : Typing Concrete.signature Concrete.model signature []
    (infer signature openEnv (.ident (.bound 2)) base .empty)
    openEnv (.ident (.bound 2)) base .empty := deepBoundRoundTrip.2

example : Entails Concrete.signature Concrete.model [] .truth
    (infer signature {} identity identityType .empty) := lambdaRoundTrip.1

example : Entails Concrete.signature Concrete.model [] .truth
    (infer signature {} (.app identity identity) identityType emptyTriple) := applicationRoundTrip.1

example : Entails Concrete.signature Concrete.model [] .truth
    (infer safetySignature {} letCaptured identityType .empty) := nonValueLetRoundTrip.1

example : Entails Concrete.signature Concrete.model [] .truth
    (infer signature {} (.letE identity (.ident (.bound 0))) identityType (.union .empty .empty)) :=
  valueMonoRoundTrip.1

example : Satisfiable Concrete.signature Concrete.model []
    (infer signature {} twoUses secondUseType (.union .empty .empty)) := polymorphicTwoUsesSatisfiable

example : Entails Concrete.signature Concrete.model [] .truth
    (infer safetySignature {} (.perform 0 identity) identityType (.union (.singleton 0) .empty)) :=
  wrappedOperationComplete

example : Typing Concrete.signature Concrete.model safetySignature []
    (infer safetySignature {} resumedHandler identityType .empty) {} resumedHandler identityType .empty :=
  deepHandlerRoundTrip.2

example : Entails Concrete.signature Concrete.model [] (.conj .truth .truth)
    (infer safetySignature {} resumedHandler identityType .empty) := handlerAlternativeConstraint

example : ¬ Satisfiable Concrete.signature Concrete.model []
    (infer signature ⟨[(7, .all [] .falsity base)], []⟩ (.ident (.free 7)) base .empty) :=
  impossibleGeneratedConstraint.2

example : generate signature (.perform 9 identity) base .empty = .falsity := unknownOperationRejected
example (C : Constraint) : ¬ Typing Concrete.signature Concrete.model signature [] C {}
    (.perform 9 identity) base .empty := unknownOperationHasNoDerivation C

namespace TypeClassesPublic
open EHMX.TypeClasses
open EHMX.TypeClasses.Regression

example : EffectFramework (TypeClasses.signature E) (TypeClasses.model E) := fixedFramework E

example : Typing (TypeClasses.signature exampleEnv) (TypeClasses.model exampleEnv) operations []
    (infer operations initialEnv eqLambda (eqType alpha) .empty) initialEnv eqLambda (eqType alpha) .empty :=
  TypeClasses.inferenceSoundness exampleEnv operations operationsWF [] initialEnv eqLambda (eqType alpha) .empty
    (by simp) initialEnvWF (typingWF eqLambdaTyping).2.2.2.1 (typingDeclared eqLambdaTyping)
    (eqTypeKind alphaKind) (emptyKind (fixedFramework exampleEnv).signature)

example : Entails (TypeClasses.signature exampleEnv) (TypeClasses.model exampleEnv) [] eqConstraint
    (infer operations argumentEnv handledMethod boolTy .empty) :=
  TypeClasses.inferenceCompleteness exampleEnv operations operationsWF [] eqConstraint argumentEnv
    handledMethod boolTy .empty (by simp) argumentEnvRealizable handledMethodTyping

example : PrincipalConstraint (TypeClasses.signature exampleEnv) (TypeClasses.model exampleEnv) operations []
    argumentEnv handledMethod boolTy .empty (infer operations argumentEnv handledMethod boolTy .empty) :=
  TypeClasses.constraintGenerationPrincipality exampleEnv operations operationsWF [] argumentEnv handledMethod
    boolTy .empty (by simp) argumentEnvWF (typingWF handledMethodTyping).2.2.2.1
    (typingDeclared handledMethodTyping) boolKind (emptyKind (fixedFramework exampleEnv).signature)

example : Satisfiable (TypeClasses.signature exampleEnv) (TypeClasses.model exampleEnv) []
    (infer operations argumentEnv handledMethod boolTy .empty) := handledMethodGeneratedSatisfiable
end TypeClassesPublic
