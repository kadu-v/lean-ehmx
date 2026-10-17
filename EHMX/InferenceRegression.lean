import EHMX.Proofs.InferenceSupport
import EHMX.Regression

/-! 推論補題の回帰。最終推論三定理の適用検査ではない。
開いた環境、遮蔽、複数段の束縛、値 let、多相操作の型・効果代入を検査する。 -/
namespace EHMX.InferenceRegression
open Regression

/-- The later binding of 7 has a different type; bound entries are nearest first. -/
def openEnv : Env :=
  ⟨[(7, .mono base), (7, .mono identityType)],
    [.mono base, .mono identityType, .mono base]⟩

theorem openEnvWF : openEnv.WF Concrete.signature [] := by
  have hb := baseKind (Δ := [])
  have hi : Ty.HasKind Concrete.signature [] identityType 0 :=
    arrowKind hb (emptyKind Concrete.framework.signature) hb
  simp [openEnv, Env.WF, Scheme.mono, Scheme.WF, Scheme.fpi,
    Constraint.WF, Constraint.fpi, hb, hi]

theorem shadowedLookup : openEnv.lookup (.free 7) = some (.mono identityType) := rfl

theorem deepLookup : openEnv.lookup (.bound 2) = some (.mono base) := rfl

theorem shadowedInterpretation (ρ : Assignment Concrete.model) bs ι :
    (openEnv.interpret Concrete.model ρ bs ι).lookup (.free 7) =
      (Scheme.mono identityType).denote Concrete.model ρ bs ι :=
  envInterpretLookup openEnvWF shadowedLookup ρ bs ι

theorem deepInterpretation (ρ : Assignment Concrete.model) bs ι :
    (openEnv.interpret Concrete.model ρ bs ι).lookup (.bound 2) =
      (Scheme.mono base).denote Concrete.model ρ bs ι :=
  envInterpretLookup openEnvWF deepLookup ρ bs ι

theorem shadowedVariableSoundness :
    Typing Concrete.signature Concrete.model signature []
      (infer signature openEnv (.ident (.free 7)) identityType (.singleton 0))
      openEnv (.ident (.free 7)) identityType (.singleton 0) := by
  apply inferenceVariable Concrete.framework _ entailsRefl
  apply inferJudgmentWF Concrete.framework.signature signatureWF openEnvWF
  · simp [Expr.Scoped, Expr.LCAt, Expr.fv, openEnv, Env.dpi]
  · trivial
  · exact arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind
  · exact singletonKind 0

theorem deepVariableSoundness :
    Typing Concrete.signature Concrete.model signature []
      (infer signature openEnv (.ident (.bound 2)) base .empty)
      openEnv (.ident (.bound 2)) base .empty := by
  apply inferenceVariable Concrete.framework _ entailsRefl
  apply inferJudgmentWF Concrete.framework.signature signatureWF openEnvWF
  · simp [Expr.Scoped, Expr.LCAt, Expr.fv, openEnv]
  · trivial
  · exact baseKind
  · exact emptyKind Concrete.framework.signature

/-- No satisfiability hypothesis is added to the variable soundness lemma. -/
theorem impossibleEnvironmentSoundness :
    let Γ : Env := ⟨[(7, .all [] .falsity base)], []⟩
    Typing Concrete.signature Concrete.model signature []
      (infer signature Γ (.ident (.free 7)) base .empty)
      Γ (.ident (.free 7)) base .empty := by
  intro Γ
  apply inferenceVariable Concrete.framework _ entailsRefl
  apply inferJudgmentWF Concrete.framework.signature signatureWF
  · simp [Γ, Env.WF, Scheme.WF, Scheme.fpi, Constraint.WF, Constraint.fpi, baseKind]
  · simp [Γ, Expr.Scoped, Expr.LCAt, Expr.fv, Env.dpi]
  · trivial
  · exact baseKind
  · exact emptyKind Concrete.framework.signature

/-- Exercise both subterm hypotheses of value-let soundness in an open environment. -/
theorem openValueLetSoundness :
    let e : Expr := .letE (.ident (.free 7)) (.ident (.bound 0))
    Typing Concrete.signature Concrete.model signature []
      (infer signature openEnv e identityType (.singleton 0))
      openEnv e identityType (.singleton 0) := by
  intro e
  apply inferenceValueLet Concrete.framework signatureWF
  · apply inferJudgmentWF Concrete.framework.signature signatureWF openEnvWF
    · simp [e, Expr.Scoped, Expr.LCAt, Expr.fv, openEnv, Env.dpi]
    · trivial
    · exact arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind
    · exact singletonKind 0
  · trivial
  · rfl
  · exact entailsRefl
  · intro Δ C Γ T ε hw he
    exact inferenceVariable Concrete.framework hw he
  · intro Δ C Γ T ε hw he
    exact inferenceVariable Concrete.framework hw he

theorem mixedHandlerInferWF :
    JudgmentWF Concrete.signature []
      (infer signature openEnv resumedHandler identityType .empty)
      openEnv resumedHandler identityType .empty := by
  apply inferJudgmentWF Concrete.framework.signature signatureWF openEnvWF
  · simp [resumedHandler, identity, Expr.Scoped, Expr.LCAt, Expr.fv, openEnv]
  · simp [resumedHandler, identity, Expr.Declared, signature]
  · exact arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind
  · exact emptyKind Concrete.framework.signature

/-- Both kinds occur in the declaration and in the substituted outer context. -/
theorem mixedHandlerGenerationSubstitution :
    (generate signature resumedHandler (.bound 0) (.bound 1)).substBound
      (BoundSubst.many [identityType, .empty]) =
      generate signature resumedHandler identityType .empty := by
  rw [generationSubstitution signatureWF]
  simp [Ty.substBound, BoundSubst.many]

/-- Universal clauses are interpreted under shifted environments; feasibility
remains outside the universal quantifier. -/
theorem mixedUniversalEnvironment (D : Constraint) (ρ : Assignment Concrete.model) bs ι :
    (openEnv.letIn (.forall_ [0,1] D)).Holds Concrete.model ρ bs ι ↔
      openEnv.exists_.Holds Concrete.model ρ bs ι ∧
      (Constraint.forall_ [0,1] ((openEnv.shift 2).letIn D)).Holds Concrete.model ρ bs ι :=
  envLetInForall openEnvWF [0,1] D ρ bs ι

/-- The same value-let scheme comparison is available for different requested
result types and evaluation effects. It does not assert solver existence. -/
theorem valueLetAtTwoRequests (T U : Ty) (ε η : Effect) :
    Equivalent Concrete.signature Concrete.model []
      (infer signature openEnv (.letE identity (.ident (.bound 0))) T ε)
      (infer signature (openEnv.push (generatedScheme signature openEnv identity))
        (.ident (.bound 0)) T ε) ∧
    Equivalent Concrete.signature Concrete.model []
      (infer signature openEnv (.letE identity (.ident (.bound 0))) U η)
      (infer signature (openEnv.push (generatedScheme signature openEnv identity))
        (.ident (.bound 0)) U η) := by
  constructor <;> apply valueLetGeneration Concrete.framework.signature signatureWF openEnvWF
  all_goals simp [identity, Expr.Scoped, Expr.LCAt, Expr.fv, openEnv, Expr.Declared,
    Value, Expr.isValue]

end EHMX.InferenceRegression
