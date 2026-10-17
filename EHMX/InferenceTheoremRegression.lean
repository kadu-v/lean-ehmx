import EHMX.Proofs.InferencePrincipality
import EHMX.InferenceRegression
import EHMX.SafetyRegression

/-! 最終推論三定理を、独立した型付け導出と具体例に適用する回帰。 -/
namespace EHMX.InferenceRegression
open Regression

private theorem identityKind : Ty.HasKind Concrete.signature Δ identityType 0 :=
  arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind

/-- Both implications use the public final theorems, with the original constraint retained. -/
private theorem bothDirections (hA : Assumptions S M sig)
    (hΔ : ∀ k ∈ Δ, k ∈ S.kinds) (hΓe : Entails S M Δ C Γ.exists_)
    (ht : Typing S M sig Δ C Γ e T ε) :
    Entails S M Δ C (infer sig Γ e T ε) ∧
      Typing S M sig Δ (infer sig Γ e T ε) Γ e T ε := by
  have hw := typingWF ht
  exact ⟨inferenceCompleteness S M sig hA Δ C Γ e T ε hΔ hΓe ht,
    inferenceSoundness S M sig hA Δ Γ e T ε hΔ hw.2.2.1 hw.2.2.2.1
      (typingDeclared ht) hw.2.2.2.2.1 hw.2.2.2.2.2⟩

private theorem emptyFeasible : Entails S M Δ C ({} : Env).exists_ :=
  fun _ _ _ _ _ _ _ => trivial

private theorem openFeasible : Entails Concrete.signature Concrete.model [] .truth openEnv.exists_ := by
  intro ρ bs ι _ _ _ _
  simp [openEnv, Env.exists_, Env.letIn, Constraint.letFree, Constraint.letBound,
    Scheme.mono, Scheme.exists_, Constraint.Holds, KindValues]

theorem openShadowedRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth
      (infer signature openEnv (.ident (.free 7)) identityType .empty) ∧
    Typing Concrete.signature Concrete.model signature []
      (infer signature openEnv (.ident (.free 7)) identityType .empty)
      openEnv (.ident (.free 7)) identityType .empty := by
  apply bothDirections ⟨Concrete.framework, signatureWF⟩ (by simp) openFeasible
  exact .var ⟨trivial, rfl, openEnvWF,
    by simp [Expr.Scoped, Expr.LCAt, Expr.fv, openEnv, Env.dpi], identityKind,
    emptyKind Concrete.framework.signature⟩ shadowedLookup (monoInstance Concrete.framework identityKind)

theorem deepBoundRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth
      (infer signature openEnv (.ident (.bound 2)) base .empty) ∧
    Typing Concrete.signature Concrete.model signature []
      (infer signature openEnv (.ident (.bound 2)) base .empty)
      openEnv (.ident (.bound 2)) base .empty := by
  apply bothDirections ⟨Concrete.framework, signatureWF⟩ (by simp) openFeasible
  exact .var ⟨trivial, rfl, openEnvWF,
    by simp [Expr.Scoped, Expr.LCAt, Expr.fv, openEnv], baseKind,
    emptyKind Concrete.framework.signature⟩ deepLookup (monoInstance Concrete.framework baseKind)

theorem lambdaRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth (infer signature {} identity identityType .empty) ∧
    Typing Concrete.signature Concrete.model signature [] (infer signature {} identity identityType .empty)
      {} identity identityType .empty :=
  bothDirections ⟨Concrete.framework, signatureWF⟩ (by simp) emptyFeasible
    (identityTyping Concrete.framework baseKind)

theorem applicationRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth
      (infer signature {} (.app identity identity) identityType emptyTriple) ∧
    Typing Concrete.signature Concrete.model signature []
      (infer signature {} (.app identity identity) identityType emptyTriple)
      {} (.app identity identity) identityType emptyTriple :=
  bothDirections ⟨Concrete.framework, signatureWF⟩ (by simp) emptyFeasible betaTyping

/-- The RHS is a value, but the original derivation uses letMono. -/
theorem valueMonoRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth
      (infer signature {} (.letE identity (.ident (.bound 0))) identityType (.union .empty .empty)) ∧
    Typing Concrete.signature Concrete.model signature []
      (infer signature {} (.letE identity (.ident (.bound 0))) identityType (.union .empty .empty))
      {} (.letE identity (.ident (.bound 0))) identityType (.union .empty .empty) :=
  bothDirections ⟨Concrete.framework, signatureWF⟩ (by simp) emptyFeasible monomorphicLetTyping

theorem polyLetRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth
      (infer signature {} (.letE identity (.ident (.bound 0))) identityType .empty) ∧
    Typing Concrete.signature Concrete.model signature []
      (infer signature {} (.letE identity (.ident (.bound 0))) identityType .empty)
      {} (.letE identity (.ident (.bound 0))) identityType .empty :=
  bothDirections ⟨Concrete.framework, signatureWF⟩ (by simp) emptyFeasible
    (polymorphicLetTyping Concrete.framework baseKind)

theorem mixedOperationRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth
      (infer safetySignature {} (.perform 0 identity) identityType (.union (.singleton 0) .empty)) ∧
    Typing Concrete.signature Concrete.model safetySignature []
      (infer safetySignature {} (.perform 0 identity) identityType (.union (.singleton 0) .empty))
      {} (.perform 0 identity) identityType (.union (.singleton 0) .empty) :=
  bothDirections safetyAssumptions.1 (by simp) emptyFeasible mixedOperationTyping

theorem deepHandlerRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth
      (infer safetySignature {} resumedHandler identityType .empty) ∧
    Typing Concrete.signature Concrete.model safetySignature []
      (infer safetySignature {} resumedHandler identityType .empty) {} resumedHandler identityType .empty :=
  bothDirections safetyAssumptions.1 (by simp) emptyFeasible resumedHandlerTyping

/-- A non-value let shares its RHS type and is handled by a universal clause. -/
theorem nonValueLetRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth
      (infer safetySignature {} letCaptured identityType .empty) ∧
    Typing Concrete.signature Concrete.model safetySignature []
      (infer safetySignature {} letCaptured identityType .empty) {} letCaptured identityType .empty :=
  bothDirections safetyAssumptions.1 (by simp) emptyFeasible letCapturedTyping

/-- The derivation contains sub, strengthen and an existential operation argument. -/
theorem wrappedOperationComplete :
    Entails Concrete.signature Concrete.model [] .truth
      (infer safetySignature {} (.perform 0 identity) identityType (.union (.singleton 0) .empty)) :=
  inferenceCompleteness _ _ _ safetyAssumptions.1 _ _ _ _ _ _ (by simp) emptyFeasible
    existentialOperationTyping

/-- Fixed request: every feasible typing constraint entails the generated one. -/
theorem handlerPrincipal : PrincipalConstraint Concrete.signature Concrete.model safetySignature [] {}
    resumedHandler identityType .empty (infer safetySignature {} resumedHandler identityType .empty) := by
  have hw := typingWF resumedHandlerTyping
  exact constraintGenerationPrincipality _ _ _ safetyAssumptions.1 _ _ _ _ _ (by simp)
    hw.2.2.1 hw.2.2.2.1 (typingDeclared resumedHandlerTyping) hw.2.2.2.2.1 hw.2.2.2.2.2

theorem handlerAlternativeConstraint :
    Entails Concrete.signature Concrete.model [] (.conj .truth .truth)
      (infer safetySignature {} resumedHandler identityType .empty) := by
  apply handlerPrincipal.2 _ emptyFeasible
  exact .strengthen ⟨⟨trivial, trivial⟩, rfl, (typingWF resumedHandlerTyping).2.2⟩
    resumedHandlerTyping (fun _ _ _ _ _ _ _ => trivial)

/-- Soundness does not require a satisfiable generated constraint. -/
theorem impossibleGeneratedConstraint :
    let Γ : Env := ⟨[(7, .all [] .falsity base)], []⟩
    Typing Concrete.signature Concrete.model signature []
      (infer signature Γ (.ident (.free 7)) base .empty) Γ (.ident (.free 7)) base .empty ∧
    ¬ Satisfiable Concrete.signature Concrete.model [] (infer signature Γ (.ident (.free 7)) base .empty) := by
  intro Γ
  constructor
  · apply inferenceSoundness _ _ _ ⟨Concrete.framework, signatureWF⟩ _ _ _ _ _ (by simp)
    · simp [Γ, Env.WF, Scheme.WF, Scheme.fpi, Constraint.WF, Constraint.fpi, baseKind]
    · simp [Γ, Expr.Scoped, Expr.LCAt, Expr.fv, Env.dpi]
    · trivial
    · exact baseKind
    · exact emptyKind Concrete.framework.signature
  · rintro ⟨_, ρ, bs, ι, _, _, _, h⟩
    have hh := ((envLetInHolds _ _ _ _ _).mp h).1
    simp [Γ, Env.exists_, Env.letIn, Constraint.letFree, Scheme.exists_, Constraint.Holds] at hh


/-- One polymorphic binding is used at base→base and at identity→identity,
with different latent effects. -/
def twoUses : Expr := .letE identity (.letE (.ident (.bound 0)) (.ident (.bound 1)))
def secondUseType : Ty := .arrow identityType (.singleton 0) identityType

private theorem twoUsesTyping : Typing Concrete.signature Concrete.model signature [] .truth {}
    twoUses secondUseType (.union .empty .empty) := by
  have hem := emptyKind (Δ := []) Concrete.framework.signature
  have hsecond : Ty.HasKind Concrete.signature [] secondUseType 0 :=
    arrowKind identityKind (singletonKind 0) identityKind
  have hα : Ty.HasKind Concrete.signature [0] (.bound 0) 0 := .bound rfl Concrete.framework.signature.1
  have hsw : identityScheme.WF Concrete.signature [] 0 :=
    ⟨by simp [Concrete.signature], trivial, arrowKind hα (emptyKind Concrete.framework.signature) hα⟩
  have hΓ : (({} : Env).push identityScheme).WF Concrete.signature [] := by
    refine ⟨by simp [Env.push], ?_⟩
    intro s hs
    simp only [Env.push, List.mem_cons, List.mem_nil_iff, or_false] at hs
    subst s
    exact ⟨hsw, rfl⟩
  have hΓ' := envPushMonoWF hΓ (identityKind (Δ := []))
  have hfirst : Typing Concrete.signature Concrete.model signature [] .truth
      (({} : Env).push identityScheme) (.ident (.bound 0)) identityType .empty :=
    .var ⟨trivial, rfl, hΓ, by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi], identityKind, hem⟩
      rfl (identitySchemeInstance Concrete.framework baseKind)
  have hsecondPure : Typing Concrete.signature Concrete.model signature [] .truth
      ((({} : Env).push identityScheme).push (.mono identityType)) (.ident (.bound 1))
      (.arrow identityType .empty identityType) .empty :=
    .var ⟨trivial, rfl, hΓ', by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi],
      arrowKind identityKind hem identityKind, hem⟩ rfl
      (identitySchemeInstance Concrete.framework identityKind)
  have hsecondTyped : Typing Concrete.signature Concrete.model signature [] .truth
      ((({} : Env).push identityScheme).push (.mono identityType)) (.ident (.bound 1)) secondUseType .empty := by
    apply Typing.sub (S := Concrete.signature) (Δ := []) (C := .truth) ⟨trivial, rfl, hΓ', (typingWF hsecondPure).2.2.2.1, hsecond, hem⟩ hsecondPure
    · intro ρ bs ι _ _ _ _
      simp only [Constraint.le, Constraint.Holds, Predicate.eval, secondUseType, identityType, base,
        Ty.arrow, Ty.empty, Ty.singleton, Ty.eval, List.map_cons, List.map_nil]
      simp only [Concrete.model, Concrete.constructor, Concrete.kind, Concrete.below]
      exact ⟨trivial, trivial, .arrow (Concrete.groundRefl _) (by simp) (Concrete.groundRefl _)⟩
    · exact leRefl Concrete.framework Concrete.framework.signature.2.1 hem
  have hbody := Typing.letMono (S := Concrete.signature) (Δ := []) (C := .truth)
    ⟨trivial, rfl, hΓ, scopedLet (typingWF hfirst).2.2.2.1 (typingWF hsecondTyped).2.2.2.1,
      hsecond, unionKind hem hem⟩ hfirst hsecondTyped
  apply Typing.letPoly (S := Concrete.signature) (Δ := []) (C := .truth) (rhs := identity) (ks := [0]) (D := .truth) (A := .arrow (.bound 0) .empty (.bound 0))
    ⟨trivial, rfl, by simp [Env.WF], by simp [identity, Expr.Scoped, Expr.LCAt, Expr.fv, Env.dpi],
      hsecond, unionKind hem hem⟩ rfl _ _ hbody
  · have ht := identityTyping (sig := signature) Concrete.framework hα
    exact .strengthen ⟨⟨trivial, trivial⟩, rfl, (typingWF ht).2.2⟩ ht (fun _ _ _ _ _ _ _ => trivial)
  · intro ρ bs ι hρ hbs _ _
    exact ⟨[base.eval Concrete.model ρ bs], .cons (evalKind Concrete.framework hρ hbs baseKind) .nil, trivial⟩

theorem polymorphicTwoUsesRoundTrip :
    Entails Concrete.signature Concrete.model [] .truth
      (infer signature {} twoUses secondUseType (.union .empty .empty)) ∧
    Typing Concrete.signature Concrete.model signature []
      (infer signature {} twoUses secondUseType (.union .empty .empty))
      {} twoUses secondUseType (.union .empty .empty) :=
  bothDirections ⟨Concrete.framework, signatureWF⟩ (by simp) emptyFeasible twoUsesTyping

/-- Completeness gives actual satisfiability, not just a derivation under its own constraint. -/
theorem polymorphicTwoUsesSatisfiable : Satisfiable Concrete.signature Concrete.model []
    (infer signature {} twoUses secondUseType (.union .empty .empty)) :=
  ⟨(typingWF polymorphicTwoUsesRoundTrip.2).1,
    testAssignment, [], testGroundEnv, testAssignmentValid, .nil, testGroundEnvValid,
    polymorphicTwoUsesRoundTrip.1 _ _ _ testAssignmentValid .nil testGroundEnvValid trivial⟩

end EHMX.InferenceRegression
