import HMX.LocallyNameless.Proofs.TypingCorrespondence
import HMX.LocallyNameless.Proofs.InferenceSoundness
import HMX.LocallyNameless.Proofs.InferenceCompleteness

namespace HMX.LN.Proofs

theorem namedEnvExistsWF (Γ : HMX.Env) (hΓ : Γ.WF S) : Γ.exists_.WF S := by
  apply encodingConstraintWFReflection Γ.exists_ [] []
  rw [encodingEnvExists]
  exact envExistsWF (ofEnv Γ) ((encodingEnvWF Γ).mpr hΓ)

/-- Generation WF is transferred independently of inference soundness. -/
theorem namedInferWF (hS : S.Valid) (Γ : HMX.Env) (t : HMX.Expr) (T : HMX.Ty)
    (hΓ : Γ.WF S) (hT : T.HasKind S 0) : (HMX.infer Γ t T).WF S := by
  apply encodingConstraintWFReflection (HMX.infer Γ t T) [] []
  apply (constraintBinderEqWF (generationCorrespondence Γ t T) [] 0).mpr
  exact inferWF hS ((encodingEnvWF Γ).mpr hΓ) ((encodingWF S).1 t)
    ((encodingWF S).2.1 T 0 hT)

/-- Binder correspondence is used through its semantics, not as syntactic equality. -/
theorem encodingInferEquivalent (hM : M.Requirements S)
    (Γ : HMX.Env) (t : HMX.Expr) (T : HMX.Ty)
    (hΓ : Γ.WF S) (hT : T.HasKind S 0) :
    Equivalent S M (ofConstraint [] [] (HMX.infer Γ t T))
      (infer (ofEnv Γ) (ofExpr [] t) (ofTy [] T)) := by
  exact (binderPermutationSemantics S M hM).1 _ _
    ((encodingWF S).2.2.1 _ (namedInferWF hM.1 Γ t T hΓ hT))
    (inferWF hM.1 ((encodingEnvWF Γ).mpr hΓ) ((encodingWF S).1 t)
      ((encodingWF S).2.1 T 0 hT)) (generationCorrespondence Γ t T)

end HMX.LN.Proofs

namespace HMX.Proofs

open LN.Proofs

/-- ATTAPL 10.4.4 (Soundness), transferred to the existing scoped named statement. -/
theorem theorem10_4_4_soundness_scoped (S : Signature) (M : Model) (I : Set Nat) :
    HMX.theorem10_4_4_soundness_scoped S M I := by
  intro hF Γ t T hΓ hf hs hT
  have hΓf : (LN.ofEnv Γ).fpi = ∅ := (encodingEnvFpi Γ).trans hf
  have hscope : (LN.ofExpr [] t).fpi ⊆ (LN.ofEnv Γ).dpi := by
    rw [encodingFreeVariables.1,encodingEnvDpi]; exact hs
  have hp := LN.Proofs.theorem10_4_4_soundness_scoped S M I
    ((frameworkCorrespondence S M I).mpr hF) _ _ _ ((encodingEnvWF Γ).mpr hΓ)
    hΓf ((encodingWF S).1 t) hscope ((encodingWF S).2.1 T 0 hT)
  have hW := (encodingWF S).2.2.1 _ (namedInferWF hF.1.1 Γ t T hΓ hT)
  have hCf := (constraintBinderEqFpi (generationCorrespondence Γ t T)).trans
    (inferFpi _ _ _ hΓf hscope)
  have he := encodingInferEquivalent hF.1 Γ t T hΓ hT
  apply (typingCorrespondence S M I hF _ Γ t (.mono T)).mpr
  rw [encodingMono]
  exact ⟨_,.convert (judgmentChangeConstraint (LN.Proofs.derivationWF hp.choose_spec) hW hCf)
    hp.choose_spec ⟨he.2,he.1⟩ (envBinderEqRefl _) .refl⟩

/-- ATTAPL 10.4.8 (Completeness), retaining exactly its feasibility premise. -/
theorem theorem10_4_8_completeness (S : Signature) (M : Model) (I : Set Nat) :
    HMX.theorem10_4_8_completeness S M I := by
  intro hF C Γ t T he hf hd
  have hw := derivationWF hd.choose_spec
  have hT : T.HasKind S 0 := hw.2.2.1.2.2
  have he' := (encodingEntails hF.1 hw.1 (namedEnvExistsWF Γ hw.2.1)).mpr he
  rw [encodingEnvExists] at he'
  have hf' : (LN.ofConstraint [] [] C).fpi ∪ (LN.ofEnv Γ).fpi = ∅ := by
    rw [(encodingFreeVariables.2.1 C).2,encodingEnvFpi]; exact hf
  have hd' := (typingCorrespondence S M I hF C Γ t (.mono T)).mp hd
  rw [encodingMono] at hd'
  have hp := LN.Proofs.theorem10_4_8_completeness S M I
    ((frameworkCorrespondence S M I).mpr hF) _ _ _ _ he' hf' hd'
  apply (encodingEntails hF.1 hw.1 (namedInferWF hF.1.1 Γ t T hw.2.1 hT)).mp
  intro ρ ι hρ hι hh
  exact (encodingInferEquivalent hF.1 Γ t T hw.2.1 hT).2 ρ ι hρ hι (hp ρ ι hρ hι hh)

/-- The least-specific constraint described on pp.429–430, via the named theorems. -/
theorem constraintGenerationPrincipality_scoped (S : Signature) (M : Model) (I : Set Nat) :
    HMX.constraintGenerationPrincipality_scoped S M I := by
  intro hF Γ t T hΓ hf hs hT
  constructor
  · exact theorem10_4_4_soundness_scoped S M I hF Γ t T hΓ hf hs hT
  · intro C he hc hd
    exact theorem10_4_8_completeness S M I hF C Γ t T he hc hd

end HMX.Proofs
