import SystemFXi.EffectPolyInversion

/-!
# 効果多相な基本簡約の型保存

項 β、kind β、handler の return 節の三つの簡約を扱う。
-/

namespace SystemFXi.Poly

/-- `Δ ∣ Γ ⊢ (λx:a.e) v : σ ∣ ε` なら `Δ ∣ Γ ⊢ e[x ↦ v] : σ ∣ ε`。 -/
theorem Typing.beta_preserves {sig : Signature} (hsigwf : Signature.WF sig)
    {Δ : List Kind} {Γ : TermCtx} {ann : Ty} {body v : Expr}
    {σ : Ty} {ε : Effect}
    (hΓ : TermCtx.WF sig Δ Γ)
    (ht : Typing sig Δ Γ (.app (.lam ann body) v) σ ε)
    (hv : Value v) :
    Typing sig Δ Γ (body.instantiate v) σ ε := by
  generalize he : Expr.app (.lam ann body) v = e at ht
  induction ht generalizing ann body v with
  | @app Δ Γ f x a b εf εx εbody hfun harg =>
      cases he
      obtain ⟨hann, b₀, ε₀, hbody, hs⟩ := hfun.lambda_arrow_inv
      cases hs with
      | arr hcontra heff hresult =>
          have hval : Typing sig Δ Γ x ann ∅ := by
            exact .sub (harg.value_pure hv) hcontra
              hann
              Effect.WF.empty (by constructor <;> simp)
          have hred := hbody.instantiateTerm hsigwf hΓ hval
          have hwf := (Typing.app hfun harg).wf hsigwf
          exact .sub hred hresult hwf.1 hwf.2 (by
            constructor
            · intro op hop
              simp only [Effect.labels_union, Finset.mem_union]
              exact Or.inr (heff.1 hop)
            · intro μ hμ
              simp only [Effect.vars_union, Finset.mem_union]
              exact Or.inr (heff.2 hμ))
  | sub _ hs hσ hε hsubset ih =>
      exact .sub (ih hΓ hv he) hs hσ hε hsubset
  | var => cases he
  | lam => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he
  | handle => cases he

/-- `Δ ∣ Γ ⊢ (Λβ::κ.e)[θ] : σ ∣ ε` なら具体化後も同じ型と効果。 -/
theorem Typing.kindBeta_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {Δ : List Kind} {Γ : TermCtx}
    {κ : Kind} {body : Expr} {arg : Arg} {σ : Ty} {ε : Effect}
    (ht : Typing sig Δ Γ (.tapp (.tlam κ body) arg) σ ε) :
    Typing sig Δ Γ
      (body.substKind (KindSubst.single arg)) σ ε := by
  generalize he : Expr.tapp (.tlam κ body) arg = e at ht
  induction ht generalizing body arg with
  | @tapp Δ Γ e κ₀ σ₀ ε₀ arg₀ hfun harg =>
      cases he
      obtain ⟨hκ, σ₁, hbody, hs⟩ := hfun.kindLambda_all_inv
      subst κ₀
      cases hs with
      | all hsub =>
          have hred := hbody.instantiateKind hsigwf harg
          have hsub' := hsub.subst_preserves
            (KindSubst.single arg₀) (KindSubst.single_valid harg)
          have hwf := (Typing.tapp hfun harg).wf hsigwf
          change Subtype sig Δ (σ₁.instantiate arg₀)
            (σ₀.instantiate arg₀) at hsub'
          have heff : (∅ : Effect).substKind
              (KindSubst.single arg₀) = ∅ := rfl
          rw [heff] at hred
          exact .sub hred hsub' hwf.1 hwf.2
            (by constructor <;> simp)
  | sub _ hs hσ hε hsubset ih =>
      exact .sub (ih he) hs hσ hε hsubset
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | perform => cases he
  | handle => cases he

/-- `Δ ∣ Γ ⊢ handle v with h : σ ∣ ε` なら return 節への置換後も保存。 -/
theorem Typing.return_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {Δ : List Kind} {Γ : TermCtx}
    {v : Expr} {op arity : Nat} {ret clause : Expr}
    {σ : Ty} {ε : Effect}
    (hΓ : TermCtx.WF sig Δ Γ)
    (ht : Typing sig Δ Γ (.handle v op arity ret clause) σ ε)
    (hv : Value v) :
    Typing sig Δ Γ (ret.instantiate v) σ ε := by
  generalize he : Expr.handle v op arity ret clause = e at ht
  induction ht generalizing v op arity ret clause with
  | @handle Δ Γ body op₀ arity₀ ret₀ clause₀ decl σin σout
      εin εout hsig harity hbody hsubset hret hclause =>
      cases he
      exact hret.instantiateTerm hsigwf hΓ (hbody.value_pure hv)
  | sub _ hs hσ hε hsubset ih =>
      exact .sub (ih hΓ hv he) hs hσ hε hsubset
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he

end SystemFXi.Poly
