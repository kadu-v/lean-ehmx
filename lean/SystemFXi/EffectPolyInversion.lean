import SystemFXi.EffectPolyContextLemmas
import SystemFXi.EffectPolyProgress

/-!
# 効果多相な値の型付けを逆向きに読む補題

部分型の使用を取り除き、項抽象と kind 抽象の本体の型付けを取り出す。
-/

namespace SystemFXi.Poly

/-- 値 `v` の評価効果は空にできる: `Δ ∣ Γ ⊢ v : σ ∣ ε ⇒ Δ ∣ Γ ⊢ v : σ ∣ ∅`。 -/
theorem Typing.value_pure {sig : Signature} {Δ : List Kind}
    {Γ : TermCtx} {v : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig Δ Γ v σ ε) :
    Value v → Typing sig Δ Γ v σ ∅ := by
  induction ht with
  | var hlookup hwf => intro _; exact .var hlookup hwf
  | lam hwf hbody _ => intro _; exact .lam hwf hbody
  | tlam hbody _ => intro _; exact .tlam hbody
  | app => intro hv; cases hv
  | tapp => intro hv; cases hv
  | perform => intro hv; cases hv
  | handle => intro hv; cases hv
  | sub _ hsub hσ _ _ ih =>
      intro hv
      exact .sub (ih hv) hsub hσ Effect.WF.empty
        (by constructor <;> simp)

/-- `Δ ∣ Γ ⊢ λx:ann.e : a →ε b ∣ η` なら、本体と元の矢印部分型を得る。 -/
theorem Typing.lambda_arrow_inv {sig : Signature} {Δ : List Kind}
    {Γ : TermCtx} {ann : Ty} {body : Expr}
    {a b : Ty} {ε εval : Effect}
    (ht : Typing sig Δ Γ (.lam ann body) (.arr a ε b) εval) :
    Ty.WF sig Δ ann ∧ ∃ b₀ ε₀,
      Typing sig Δ (ann :: Γ) body b₀ ε₀ ∧
      Subtype sig Δ (.arr ann ε₀ b₀) (.arr a ε b) := by
  generalize he : Expr.lam ann body = e at ht
  generalize hty : Ty.arr a ε b = ty at ht
  induction ht generalizing ann body a ε b with
  | lam hwf hbody =>
      cases he
      cases hty
      exact ⟨hwf, _, _, hbody, Subtype.refl _ _⟩
  | sub _ hsub _ _ _ ih =>
      cases hty
      cases hsub with
      | arr harg heff hresult =>
          obtain ⟨hwf, b₀, ε₀, hbody, hs⟩ := ih he rfl
          exact ⟨hwf, b₀, ε₀, hbody,
            Subtype.trans hs (.arr harg heff hresult)⟩
  | var => cases he
  | app => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he
  | handle => cases he

/-- `Δ ∣ Γ ⊢ Λβ::κ.e : ∀β::κ.σ ∣ ε` なら抽象本体の型付けを得る。 -/
theorem Typing.kindLambda_all_inv {sig : Signature} {Δ : List Kind}
    {Γ : TermCtx} {κ κ' : Kind} {body : Expr} {σ : Ty} {εval : Effect}
    (ht : Typing sig Δ Γ (.tlam κ body) (.all κ' σ) εval) :
    κ = κ' ∧ ∃ σ₀,
      Typing sig (κ :: Δ) (Γ.liftKind 1) body σ₀ ∅ ∧
      Subtype sig Δ (.all κ σ₀) (.all κ σ) := by
  generalize he : Expr.tlam κ body = e at ht
  generalize hty : Ty.all κ' σ = ty at ht
  induction ht generalizing κ body κ' σ with
  | tlam hbody =>
      cases he
      cases hty
      exact ⟨rfl, _, hbody, Subtype.refl _ _⟩
  | sub _ hsub _ _ _ ih =>
      cases hty
      cases hsub with
      | all hbodySub =>
          obtain ⟨hκ, σ₀, hbody, hs⟩ := ih he rfl
          subst κ'
          exact ⟨rfl, σ₀, hbody,
            Subtype.trans hs (.all hbodySub)⟩
  | var => cases he
  | lam => cases he
  | app => cases he
  | tapp => cases he
  | perform => cases he
  | handle => cases he

end SystemFXi.Poly
