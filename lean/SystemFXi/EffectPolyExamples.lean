import SystemFXi.EffectPolySafety

/-!
# 効果多相性の型付け例

二つの型変数 `α, β` を仮定し、潜在効果そのものが `μ` の関数を
引数に取る恒等関数を構成する。
-/

namespace SystemFXi.Poly

/-- `α, β` の下で `Λμ::E. λf:(α →μ β). f` を型付けできる。 -/
theorem effect_polymorphic_identity (sig : Signature) :
    let latent : Ty :=
      .arr (.var 1) (Effect.var 0) (.var 2)
    Typing sig [.type, .type] []
      (.tlam .effect (.lam latent (.var 0)))
      (.all .effect (.arr latent ∅ latent)) ∅ := by
  dsimp
  have hlatent : Ty.WF sig [.effect, .type, .type]
      (.arr (.var 1) (Effect.var 0) (.var 2)) := by
    apply Ty.WF.arr
    · exact .var rfl
    · constructor
      · intro op hop
        simp [Effect.var] at hop
      · intro μ hμ
        have hzero : μ = 0 := by simpa [Effect.var] using hμ
        subst μ
        rfl
    · exact .var rfl
  exact Typing.tlam (Typing.lam hlatent (Typing.var rfl hlatent))

end SystemFXi.Poly
