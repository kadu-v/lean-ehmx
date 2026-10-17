import EHMX

/-! 最終命題の型を直接検査する。推論三定理も元の Goal 型そのものを満たす。 -/
example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.ProgressGoal S M sig := EHMX.progressEffectSafety S M sig

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.SchemeValueSubstitutionGoal S M sig := EHMX.schemeValueSubstitution S M sig

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.OperationPreservationGoal S M sig := EHMX.operationPreservation S M sig

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.PreservationGoal S M sig := EHMX.preservation S M sig

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.EffectSafetyGoal S M sig := EHMX.effectSafety S M sig

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.EmptyEffectSafetyGoal S M sig := EHMX.emptyEffectSafety S M sig

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.SafetyAssumptions S M sig → ∀ Δ C Γ e e' T ε,
      EHMX.Typing S M sig Δ C Γ e T ε → EHMX.Steps e e' →
      EHMX.Typing S M sig Δ C Γ e' T ε := by
  intro hA Δ C Γ e e' T ε ht hs
  exact EHMX.preservationSteps hA ht hs

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.InferenceSoundnessGoal S M sig := EHMX.inferenceSoundness S M sig

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.InferenceCompletenessGoal S M sig := EHMX.inferenceCompleteness S M sig

example (S : EHMX.Signature) (M : EHMX.Model) (sig : EHMX.OpSignature) :
    EHMX.PrincipalityGoal S M sig := EHMX.constraintGenerationPrincipality S M sig
