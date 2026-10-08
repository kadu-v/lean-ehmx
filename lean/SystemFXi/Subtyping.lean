import SystemFXi.Typing

/-!
# 部分型の基本性質

TeX の反射律と推移律は、構造的な `Subtype` の導出から得られる。
-/

namespace SystemFXi

/-- 任意の型 `σ` に対し `Δ ⊢ σ <: σ`。整形式は型付け側で検査する。 -/
theorem Subtype.refl {sig : Signature} (σ : Ty) :
    ∀ (n : Nat), Subtype sig n σ σ := by
  induction σ with
  | var _ => intro n; exact .var
  | arr _ _ _ ihA ihB =>
      intro n
      exact .arr (ihA n) (by intro x hx; exact hx) (ihB n)
  | all _ ih => intro n; exact .all (ih (n + 1))

/-- `Δ ⊢ σ₁ <: σ₂` かつ `Δ ⊢ σ₂ <: σ₃` なら `Δ ⊢ σ₁ <: σ₃`。 -/
theorem Subtype.trans {sig : Signature} {n : Nat} {a b c : Ty}
    (hab : Subtype sig n a b) (hbc : Subtype sig n b c) :
    Subtype sig n a c := by
  induction b generalizing n a c with
  | var i =>
      cases hab with
      | var =>
          cases hbc with
          | var => exact .var
  | arr domain ε codomain ihDomain ihCodomain =>
      cases hab with
      | arr hArg₁ hEff₁ hResult₁ =>
          cases hbc with
          | arr hArg₂ hEff₂ hResult₂ =>
              exact .arr (ihDomain hArg₂ hArg₁)
                (by intro x hx; exact hEff₂ (hEff₁ hx))
                (ihCodomain hResult₁ hResult₂)
  | all body ih =>
      cases hab with
      | all h₁ =>
          cases hbc with
          | all h₂ => exact .all (ih h₁ h₂)

end SystemFXi
