import SystemFXi.Inversion

/-!
# 基本簡約の型保存

項 β、型 β、return の各簡約で置換補題を適用する。
-/

namespace SystemFXi

/-- `Γ ⊢ (λx:ann.e) v : σ ∣ ε` なら `Γ ⊢ e[x ↦ v] : σ ∣ ε`。 -/
theorem Typing.beta_preserves {sig : Signature} (hsigwf : Signature.WF sig)
    {n : Nat} {Γ : TermCtx} {ann : Ty} {body v : Expr}
    {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (.app (.lam ann body) v) σ ε)
    (hv : Value v) :
    Typing sig n Γ (body.instantiate v) σ ε := by
  generalize he : Expr.app (.lam ann body) v = e at ht
  induction ht generalizing ann body v with
  | @app n Γ f x a b εf εx εbody hfun harg =>
      cases he
      obtain ⟨b₀, ε₀, hbody, hs⟩ := hfun.lambda_arrow_inv
      cases hs with
      | arr hcontra heff hresult =>
          have hval : Typing sig n Γ x ann ∅ :=
            .sub (harg.value_pure hv) hcontra (by simp)
          have hred := hbody.instantiateTerm hsigwf hval
          exact .sub hred hresult (by
            intro op hop
            simp only [Finset.mem_union]
            exact Or.inr (heff hop))
  | sub _ hs hε ih =>
      exact .sub (ih hv he) hs hε
  | var => cases he
  | lam => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he
  | handle => cases he

/-- `Γ ⊢ (Λα.e)[τ] : σ ∣ ε` なら `Γ ⊢ e[α ↦ τ] : σ ∣ ε`。 -/
theorem Typing.typeBeta_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat} {Γ : TermCtx}
    {body : Expr} {arg σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (.tapp (.tlam body) arg) σ ε) :
    Typing sig n Γ
      (body.substTy (fun | 0 => arg | i + 1 => .var i)) σ ε := by
  generalize he : Expr.tapp (.tlam body) arg = e at ht
  induction ht generalizing body arg with
  | @tapp n Γ e σ₀ ε₀ arg₀ hfun harg =>
      cases he
      obtain ⟨σ₁, hbody, hs⟩ := hfun.typeLambda_all_inv
      cases hs with
      | all hsub =>
          have hred := hbody.instantiateTy hsigwf harg
          let τ : Nat → Ty := fun | 0 => arg₀ | i + 1 => .var i
          have hτ : ∀ i, i < n + 1 → Ty.WF sig n (τ i) := by
            intro i hi
            cases i with
            | zero => exact harg
            | succ j => exact .var (by omega)
          have hsub' := hsub.subst_preserves τ hτ
          change Subtype sig n (σ₁.instantiate arg₀) (σ₀.instantiate arg₀) at hsub'
          exact .sub hred hsub' (by simp)
  | sub _ hs hε ih => exact .sub (ih he) hs hε
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | perform => cases he
  | handle => cases he

/-- `Γ ⊢ handle v with h : σ ∣ ε` なら return 節への置換後も同じ型と効果。 -/
theorem Typing.return_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat} {Γ : TermCtx}
    {v : Expr} {op arity : Nat} {ret clause : Expr}
    {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (.handle v op arity ret clause) σ ε)
    (hv : Value v) :
    Typing sig n Γ (ret.instantiate v) σ ε := by
  generalize he : Expr.handle v op arity ret clause = e at ht
  induction ht generalizing v op arity ret clause with
  | @handle n Γ body op₀ arity₀ ret₀ clause₀ decl σin σout
      εin εout hsig harity hbody hsubset hret hclause =>
      cases he
      exact hret.instantiateTerm hsigwf (hbody.value_pure hv)
  | sub _ hs hε ih => exact .sub (ih hv he) hs hε
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he

end SystemFXi
