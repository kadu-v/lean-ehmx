import EHMX.Proofs.InferenceCompleteness

namespace EHMX

/-- Principal constraints for a fixed environment, term, requested type and effect.
This is the EHM(X) extension of ATTAPL pp.429–430, not a solver or principal substitution. -/
theorem constraintGenerationPrincipality (S : Signature) (M : Model) (sig : OpSignature) :
    PrincipalityGoal S M sig := by
  intro hA Δ Γ e T ε hΔ hΓ he hd hT hε
  exact ⟨inferenceSoundness S M sig hA Δ Γ e T ε hΔ hΓ he hd hT hε,
    fun C hΓe ht => inferenceCompleteness S M sig hA Δ C Γ e T ε hΔ hΓe ht⟩

end EHMX
