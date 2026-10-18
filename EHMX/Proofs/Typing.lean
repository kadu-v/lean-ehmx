import EHMX.Typing
import EHMX.Proofs.ConstraintLaws

namespace EHMX

theorem judgmentEmptyEffect (hS : S.WF) (h : JudgmentWF S Δ C Γ e T ε) :
    JudgmentWF S Δ C Γ e T .empty :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, emptyKind hS⟩

/-- Used before substituting values in beta, let, return, and operation reductions. -/
theorem valuePure (hF : EffectFramework S M)
    (ht : Typing S M sig Δ C Γ v T ε) (hv : Value v) :
    Typing S M sig Δ C Γ v T .empty := by
  induction ht with
  | var hw hl he => exact .var hw hl he
  | lam hw hb _ => exact .lam hw hb
  | app | letMono | letPoly | perform | handle => simp [Value, Expr.isValue] at hv
  | sub hw hd hT _ ih =>
      exact .sub (judgmentEmptyEffect hF.signature hw) (ih hv) hT
        (leRefl hF hF.signature.2.1 (emptyKind hF.signature))
  | strengthen hw hd he ih =>
      exact .strengthen (judgmentEmptyEffect hF.signature hw) (ih hv) he
  | exists_ hw hd ih =>
      apply Typing.exists_ (judgmentEmptyEffect hF.signature hw)
      simpa only [Ty.empty, Ty.shift, List.map_nil] using ih hv

/-- Canonical form of a closed value; no type or model assumption is needed. -/
theorem closedValueLambda (hc : e.Closed) (hv : Value e) : ∃ body, e = .lam body := by
  cases e with
  | ident x =>
      cases x with
      | free x => simp [Expr.Closed, Expr.fv] at hc
      | bound i => simp [Expr.Closed, Expr.LCAt] at hc
  | lam body => exact ⟨body, rfl⟩
  | app | letE | perform | handle => simp [Value, Expr.isValue] at hv

theorem typingDeclared (ht : Typing S M sig Δ C Γ e T ε) : e.Declared sig := by
  induction ht with
  | var => trivial
  | lam _ _ ih => exact ih
  | app _ _ _ ihf ihx => exact ⟨ihf, ihx⟩
  | letMono _ _ _ ihr ihb => exact ⟨ihr, ihb⟩
  | letPoly _ _ _ _ _ ihr ihb => exact ⟨ihr, ihb⟩
  | perform _ hs _ _ _ ih => exact ⟨by simp [hs], ih⟩
  | handle _ hs _ _ _ _ ihb ihr ihc => exact ⟨by simp [hs], ihb, ihr, ihc⟩
  | sub _ _ _ _ ih => exact ih
  | strengthen _ _ _ ih => exact ih
  | exists_ _ _ ih => exact ih

theorem unknownPerformNotTypable (hs : sig op = none) :
    ¬ Typing S M sig Δ C Γ (.perform op arg) T ε := by
  intro ht
  exact (typingDeclared ht).1 hs

end EHMX
