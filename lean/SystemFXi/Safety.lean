import SystemFXi.Preservation

/-!
# 多歩簡約と効果安全性

型付けの効果集合は、実行途中に外側へ露出し得る操作の上界である。
-/

namespace SystemFXi

/-- `e →* e′` は零回以上の小ステップ簡約。 -/
inductive Steps (sig : Signature) : Expr → Expr → Prop where
  | refl (e : Expr) : Steps sig e e
  | tail {e e' e'' : Expr} :
      Steps sig e e' → Step sig e' e'' → Steps sig e e''

/-- `Γ ⊢ e : σ ∣ ε` と `e →* e′` なら `Γ ⊢ e′ : σ ∣ ε`。 -/
theorem preservation_steps {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat} {Γ : TermCtx}
    {e e' : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ e σ ε) (hs : Steps sig e e') :
    Typing sig n Γ e' σ ε := by
  induction hs with
  | refl => exact ht
  | tail _ hstep ih => exact preservation hsigwf ih hstep

/-- 閉項の任意の到達状態では、値・簡約可能・許された未処理操作のいずれか。 -/
theorem effect_safety {sig : Signature}
    (hsigwf : Signature.WF sig) {e e' : Expr}
    {σ : Ty} {ε : Effect}
    (ht : Typing sig 0 [] e σ ε) (hs : Steps sig e e') :
    Value e' ∨ (∃ e'', Step sig e' e'') ∨
      ∃ op, Unhandled e' op ∧ op ∈ ε := by
  exact progress_effect_safety (preservation_steps hsigwf ht hs)

/-- 空効果の閉項は、任意の到達状態で値か簡約可能な式である。 -/
theorem empty_effect_safety {sig : Signature}
    (hsigwf : Signature.WF sig) {e e' : Expr}
    {σ : Ty} (ht : Typing sig 0 [] e σ ∅)
    (hs : Steps sig e e') :
    Value e' ∨ ∃ e'', Step sig e' e'' := by
  exact progress_empty_effect (preservation_steps hsigwf ht hs)

end SystemFXi
