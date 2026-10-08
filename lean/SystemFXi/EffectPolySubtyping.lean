import SystemFXi.EffectPolyTyping

/-!
# 効果多相な部分型の基本性質

関数型の効果包含は、すべての効果変数の有限集合解釈で成立する包含である。
-/

namespace SystemFXi.Poly

/-- σ <: σ はすべての型で成り立つ。 -/
theorem Subtype.refl {sig : Signature} (σ : Ty) :
    ∀ (Δ : List Kind), Subtype sig Δ σ σ := by
  induction σ with
  | var _ => intro Δ; exact .var
  | arr _ _ _ ihA ihB =>
      intro Δ
      exact .arr (ihA Δ)
        ⟨fun _ hx => hx, fun _ hx => hx⟩ (ihB Δ)
  | all κ _ ih =>
      intro Δ
      exact .all (ih (κ :: Δ))

/-- σ₁ <: σ₂ と σ₂ <: σ₃ から σ₁ <: σ₃。 -/
theorem Subtype.trans {sig : Signature} {Δ : List Kind} {a b c : Ty}
    (hab : Subtype sig Δ a b) (hbc : Subtype sig Δ b c) :
    Subtype sig Δ a c := by
  induction b generalizing Δ a c with
  | var _ =>
      cases hab with
      | var =>
          cases hbc with
          | var => exact .var
  | arr _ _ _ ihA ihB =>
      cases hab with
      | arr hArg₁ hEff₁ hResult₁ =>
          cases hbc with
          | arr hArg₂ hEff₂ hResult₂ =>
              exact .arr (ihA hArg₂ hArg₁)
                ⟨fun _ hx => hEff₂.1 (hEff₁.1 hx),
                 fun _ hx => hEff₂.2 (hEff₁.2 hx)⟩
                (ihB hResult₁ hResult₂)
  | all κ _ ih =>
      cases hab with
      | all h₁ =>
          cases hbc with
          | all h₂ => exact .all (ih h₁ h₂)

end SystemFXi.Poly
