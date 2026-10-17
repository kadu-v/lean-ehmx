import HMX.LocallyNameless.Proofs.EncodingSupport

namespace HMX.LN.Proofs

theorem encodingWF (S : Signature) : HMX.LN.encodingWF S := by
  refine ⟨fun t => encodingExprLC t [], ?_, ?_, ?_⟩
  · intro T k h; exact encodingTyKind h []
  · intro C h; exact encodingConstraintWF C h [] []
  · intro s h; exact encodingSchemeWF s h [] []

theorem encodingFreeVariables : HMX.LN.encodingFreeVariables := by
  refine ⟨?_, ?_, ?_⟩
  · intro t; simpa using encodingExprFpi t []
  · intro C; simpa using encodingConstraintVars C [] []
  · intro s; simpa using encodingSchemeVars s [] []

theorem encodingAlpha : HMX.LN.encodingAlpha := by
  refine ⟨?_, ?_, ?_⟩
  · intro t u
    exact encodingExprRelated t u [] [] Eq (fun _ _ => by simp [ofId])
  · intro C D h
    exact encodingConstraintRelated h [] [] [] []
      (fun _ _ h => by cases h; rfl) (fun _ _ h => by cases h; rfl)
  · intro s u h
    exact encodingSchemeRelated h [] [] [] []
      (fun _ _ h => by cases h; rfl) (fun _ _ h => by cases h; rfl)

theorem encodingSemantics (S : Signature) (M : Model) : HMX.LN.encodingSemantics S M := by
  intro _ ρ ι hρ _
  constructor
  · intro C hC
    exact encodingConstraintSem C hC [] [] M ρ ρ ι ι _ _ hρ
      (fun _ => rfl) (fun _ => rfl)
  · intro s hs
    exact encodingSchemeSem s hs [] [] M ρ ρ ι ι _ _ hρ
      (fun _ => rfl) (fun _ => rfl)

end HMX.LN.Proofs
