import SystemFXi.ContextLemmas

/-!
# Preservation

一歩簡約は結果型と評価効果の上界を保存する。
-/

namespace SystemFXi

/-- handler が捕捉する操作の簡約は型と効果を保存する。 -/
theorem Typing.operation_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat} {Γ : TermCtx}
    {E : EvalCtx} {op arity : Nat} {ret clause v : Expr}
    {args : List Ty} {decl : OpDecl} {σ : Ty} {ε : Effect}
    (hsig : sig op = some decl) (harity : arity = decl.arity)
    (hlen : args.length = arity) (hv : Value v)
    (ht : Typing sig n Γ
      (.handle (E.plug (.perform op args v)) op arity ret clause) σ ε) :
    Typing sig n Γ
      ((clause.instantiateManyTy args).instantiateOp
        (Expr.resume E op arity ret clause
          (decl.output.instantiateMany args)) v) σ ε := by
  generalize he : Expr.handle (E.plug (.perform op args v))
    op arity ret clause = e at ht
  induction ht generalizing E op arity ret clause v args with
  | @handle n Γ body op₀ arity₀ ret₀ clause₀ decl₀ σin σout
      εin εout hsig₀ harity₀ hbody hsubset hret hclause =>
      cases he
      have hdecl : decl₀ = decl := Option.some.inj (hsig₀.symm.trans hsig)
      subst decl₀
      obtain ⟨τ, η, hperf⟩ := E.subterm hbody
      obtain ⟨hargs, εarg, harg, houtput, hmem⟩ := hperf.perform_inv hsig
      have hlen' : args.length = arity₀ := hlen
      have hclause' := hclause.instantiateOpClause hsigwf args hlen' hargs
      have hout : Ty.WF sig n (decl.output.instantiateMany args) :=
        (hsigwf op₀ decl hsig).2.instantiateMany args
          (hlen.trans harity) hargs
      have hhandler : Typing sig n Γ
          (.handle (E.plug (.perform op₀ args v)) op₀ arity₀ ret₀ clause₀)
          σout εout :=
        .handle hsig harity hbody hsubset hret hclause
      have hresume := Typing.resume_preserves hsig hout hhandler
      exact hclause'.instantiateOp_preserves hsigwf hresume
        (harg.value_pure hv)
  | sub _ hs hε ih => exact .sub (ih hsig harity hlen hv he) hs hε
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he

/-- `Γ ⊢ e : σ ∣ ε` かつ `e → e′` なら `Γ ⊢ e′ : σ ∣ ε`。 -/
theorem preservation {sig : Signature} (hsigwf : Signature.WF sig)
    {n : Nat} {Γ : TermCtx} {e e' : Expr}
    {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ e σ ε) (hs : Step sig e e') :
    Typing sig n Γ e' σ ε := by
  induction hs generalizing n Γ σ ε with
  | beta hv => exact ht.beta_preserves hsigwf hv
  | typeBeta => exact ht.typeBeta_preserves hsigwf
  | ret hv => exact ht.return_preserves hsigwf hv
  | operation hsig harity hlen hv _ =>
      exact ht.operation_preserves hsigwf hsig harity hlen hv
  | context _ ih =>
      exact EvalCtx.replace ht (fun h => ih h)

end SystemFXi
