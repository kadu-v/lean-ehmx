import SystemFXi.EffectPolyRedex

/-!
# 効果多相な一歩簡約の型保存

操作節の具体化では型と効果の混合引数を一括置換する。捕捉した評価文脈を
handler で包み直す継続の型を使って、操作簡約を証明する。
-/

namespace SystemFXi.Poly

/-- `op` を捕捉する handler の一歩簡約は結果型と効果上界を保存する。 -/
theorem Typing.operation_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {Δ : List Kind} {Γ : TermCtx}
    {E : EvalCtx} {op arity : Nat} {ret clause v : Expr}
    {args : List Arg} {decl : OpDecl} {σ : Ty} {ε : Effect}
    (hΓ : TermCtx.WF sig Δ Γ)
    (hsig : sig op = some decl) (harity : arity = decl.kinds.length)
    (hlen : args.length = arity) (hv : Value v)
    (ht : Typing sig Δ Γ
      (.handle (E.plug (.perform op args v)) op arity ret clause) σ ε) :
    Typing sig Δ Γ
      ((clause.instantiateMany args).instantiateOp
        (Expr.resume E op arity ret clause
          (decl.output.instantiateMany args)) v) σ ε := by
  generalize he : Expr.handle (E.plug (.perform op args v))
    op arity ret clause = e at ht
  induction ht generalizing E op arity ret clause v args with
  | @handle Δ Γ body op₀ arity₀ ret₀ clause₀ decl₀ σin σout
      εin εout hsig₀ harity₀ hbody hsubset hret hclause =>
      cases he
      have hdecl : decl₀ = decl := Option.some.inj (hsig₀.symm.trans hsig)
      subst decl₀
      obtain ⟨τ, η, hperf⟩ := E.subterm hbody
      obtain ⟨hargs, εarg, harg, houtput, hmem⟩ :=
        hperf.perform_inv hsig
      have hout : Ty.WF sig Δ (decl.output.instantiateMany args) :=
        (hsigwf op₀ decl hsig).2.instantiateMany hargs
      have hhandler : Typing sig Δ Γ
          (.handle (E.plug (.perform op₀ args v))
            op₀ arity₀ ret₀ clause₀) σout εout :=
        .handle hsig harity hbody hsubset hret hclause
      have hresume := Typing.resume_preserves hsigwf hsig hout hhandler
      have hclause' :=
        (show Typing sig (decl.kinds ++ Δ)
          ((.arr decl.output
            (εout.rename (fun i => i + decl.kinds.length))
            (σout.rename (fun i => i + decl.kinds.length))) ::
            decl.input :: Γ.liftKind decl.kinds.length)
          clause₀ (σout.rename (fun i => i + decl.kinds.length))
          (εout.rename (fun i => i + decl.kinds.length)) from
          by simpa only [harity₀] using hclause).instantiateOpClause
            hsigwf hargs
      exact hclause'.instantiateOp_preserves hsigwf hΓ hresume
        (harg.value_pure hv)
  | sub _ hs hσ hε hsubset ih =>
      exact .sub (ih hΓ hsig harity hlen hv he) hs hσ hε hsubset
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he

/-- `Δ ∣ Γ ⊢ e : σ ∣ ε` と `e → e′` から `Δ ∣ Γ ⊢ e′ : σ ∣ ε`。 -/
theorem preservation {sig : Signature} (hsigwf : Signature.WF sig)
    {Δ : List Kind} {Γ : TermCtx} {e e' : Expr}
    {σ : Ty} {ε : Effect}
    (hΓ : TermCtx.WF sig Δ Γ)
    (ht : Typing sig Δ Γ e σ ε) (hs : Step sig e e') :
    Typing sig Δ Γ e' σ ε := by
  induction hs generalizing Δ Γ σ ε with
  | beta hv => exact ht.beta_preserves hsigwf hΓ hv
  | kindBeta => exact ht.kindBeta_preserves hsigwf
  | ret hv => exact ht.return_preserves hsigwf hΓ hv
  | operation hsig harity hlen hv _ =>
      exact ht.operation_preserves hsigwf hΓ hsig harity hlen hv
  | context _ ih =>
      exact EvalCtx.replace ht (fun h => ih hΓ h)

end SystemFXi.Poly
