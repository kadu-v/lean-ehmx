import SystemFXi.EffectPolyPreservation

/-!
# 効果多相な多歩簡約と効果安全性

型付けの評価効果は、実行途中に露出し得る操作の上界である。
閉じた項では効果変数が現れないので、操作ラベル成分で述べられる。
-/

namespace SystemFXi.Poly

/-- `e →* e′` は零回以上の小ステップ簡約。 -/
inductive Steps (sig : Signature) : Expr → Expr → Prop where
  | refl (e : Expr) : Steps sig e e
  | tail {e e' e'' : Expr} :
      Steps sig e e' → Step sig e' e'' → Steps sig e e''

/-- `Δ ∣ Γ ⊢ e : σ ∣ ε` と `e →* e′` から `Δ ∣ Γ ⊢ e′ : σ ∣ ε`。 -/
theorem preservation_steps {sig : Signature}
    (hsigwf : Signature.WF sig) {Δ : List Kind} {Γ : TermCtx}
    {e e' : Expr} {σ : Ty} {ε : Effect}
    (hΓ : TermCtx.WF sig Δ Γ)
    (ht : Typing sig Δ Γ e σ ε) (hs : Steps sig e e') :
    Typing sig Δ Γ e' σ ε := by
  induction hs with
  | refl => exact ht
  | tail _ hstep ih => exact preservation hsigwf hΓ ih hstep

/-- 閉項の到達状態は値・一歩簡約可能・許された未処理操作のいずれか。 -/
theorem effect_safety {sig : Signature}
    (hsigwf : Signature.WF sig) {e e' : Expr}
    {σ : Ty} {ε : Effect}
    (ht : Typing sig [] [] e σ ε) (hs : Steps sig e e') :
    Value e' ∨ (∃ e'', Step sig e' e'') ∨
      ∃ op, Unhandled e' op ∧ op ∈ ε.labels := by
  exact progress_effect_safety
    (preservation_steps hsigwf (TermCtx.WF.nil sig []) ht hs)

/-- 空効果の閉項は、到達したどの状態でも値か一歩進む式である。 -/
theorem empty_effect_safety {sig : Signature}
    (hsigwf : Signature.WF sig) {e e' : Expr}
    {σ : Ty} (ht : Typing sig [] [] e σ ∅)
    (hs : Steps sig e e') :
    Value e' ∨ ∃ e'', Step sig e' e'' := by
  exact progress_empty_effect
    (preservation_steps hsigwf (TermCtx.WF.nil sig []) ht hs)

end SystemFXi.Poly
