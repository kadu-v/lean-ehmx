import EHMX.Proofs.Operation

/-! ATTAPL §10.5 の保存・型安全性に対応する EHMX の定理。
多相操作、deep handler、値制限付き let を含み、Goals の前提を変更しない。 -/
namespace EHMX

theorem preservation (S : Signature) (M : Model) (sig : OpSignature) :
    PreservationGoal S M sig := by
  intro hA Δ C Γ e e' T ε ht hs
  induction hs generalizing Δ C Γ T ε with
  | beta hv => exact betaPreservation hA.1.1 hA.1.2 hv ht rfl
  | letValue hv => exact letPreservation hA.1.1 hA.1.2 hv ht rfl
  | returnValue hv => exact returnPreservation hA.1.1 hA.1.2 hv ht rfl
  | operation hv hn => exact operationPreservation S M sig hA _ _ _ _ _ _ _ _ _ _ hv hn ht
  | context hs ih =>
      exact evalCtxReplacement (fun hv => valueNoStep hv hs)
        (fun Δ C Γ T ε ht => ih Δ C Γ T ε ht) ht _ rfl

/-- 開いた環境でも同じ制約・型・効果上界を保持する多歩保存。 -/
theorem preservationSteps (hA : SafetyAssumptions S M sig)
    (ht : Typing S M sig Δ C Γ e T ε) (hs : Steps e e') : Typing S M sig Δ C Γ e' T ε := by
  induction hs with
  | refl => exact ht
  | tail _ hs ih => exact preservation S M sig hA _ _ _ _ _ _ _ ih hs

theorem effectSafety (S : Signature) (M : Model) (sig : OpSignature) :
    EffectSafetyGoal S M sig := by
  intro hA C e e' T ε ht hs
  exact progressEffectSafety S M sig hA C e' T ε (preservationSteps hA ht hs)

theorem emptyEffectSafety (S : Signature) (M : Model) (sig : OpSignature) :
    EmptyEffectSafetyGoal S M sig := by
  intro hA C e e' T hsat ht hs
  exact emptyEffectProgress hA.1.1 hsat (preservationSteps hA ht hs)

end EHMX
