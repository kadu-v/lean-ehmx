import HMX.LocallyNameless.Proofs.InferenceSoundness
import HMX.LocallyNameless.Proofs.InferenceCompleteness

namespace HMX.LN.Proofs

/-- The least-specific-constraint consequence described on pp.429–430. -/
theorem constraintGenerationPrincipality_scoped (S : Signature) (M : Model) (I : Set Nat) :
    HMX.LN.constraintGenerationPrincipality_scoped S M I := by
  intro hF Γ t T hΓ hf ht hs hT
  constructor
  · exact theorem10_4_4_soundness_scoped S M I hF Γ t T hΓ hf ht hs hT
  · intro C he hc hd
    exact theorem10_4_8_completeness S M I hF C Γ t T he hc hd

end HMX.LN.Proofs
