import EHMX.Concrete
import EHMX.Proofs.Generation
import EHMX.Proofs.Progress

/-! 回帰例。実行・生成・型付けを区別し、未証明の推論定理は使わない。 -/
namespace EHMX.Regression

def identity : Expr := .lam (.ident (.bound 0))
def base : Ty := .con (.other 0) []
def identityType : Ty := .arrow base .empty base

/-- A declaration with both a type and an effect argument. -/
def mixed : OpDecl := ⟨[0,1], .arrow (.bound 0) (.bound 1) (.bound 0),
  .arrow (.bound 0) (.bound 1) (.bound 0)⟩
def signature : OpSignature := fun op => if op = 0 then some mixed else none

theorem signatureWF : OpSignature.WF Concrete.signature signature := by
  intro op d h
  simp only [signature] at h
  split at h
  · cases h
    have ha : Ty.HasKind Concrete.signature [0,1] (.bound 0) 0 := .bound rfl (by simp [Concrete.signature])
    have he : Ty.HasKind Concrete.signature [0,1] (.bound 1) 1 := .bound rfl (by simp [Concrete.signature])
    exact ⟨by simp [mixed, Concrete.signature], arrowKind ha he ha,
      arrowKind ha he ha, by simp [mixed, Ty.fv, Ty.arrow], by simp [mixed, Ty.fv, Ty.arrow]⟩
  · cases h

theorem baseKind : Ty.HasKind Concrete.signature Δ base 0 := .con (by trivial) .nil

theorem identityTyping (hF : EffectFramework S M) (hA : Ty.HasKind S Δ A 0) :
    Typing S M sig Δ .truth {} identity (.arrow A .empty A) .empty := by
  apply Typing.lam
  · refine ⟨trivial, rfl, ?_, ?_, arrowKind hA (emptyKind hF.signature) hA,
      emptyKind hF.signature⟩
    · simp [Env.WF]
    · simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.dpi]
  · apply Typing.var
    · refine ⟨trivial, rfl, ?_, ?_, hA, emptyKind hF.signature⟩
      · simp [Env.WF, Env.push, Scheme.mono, Scheme.WF, Scheme.fpi,
          Constraint.WF, Constraint.fpi, hA]
      · simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi]
    · rfl
    · exact monoInstance hF hA

def identityScheme : Scheme := .all [0] .truth (.arrow (.bound 0) .empty (.bound 0))

theorem identitySchemeInstance (hF : EffectFramework S M) (hA : Ty.HasKind S Δ A 0) :
    Entails S M Δ .truth (identityScheme.instanceConstraint (.arrow A .empty A)) := by
  intro ρ bs ι hρ hbs _ _
  simp only [identityScheme, Scheme.instanceConstraint, Constraint.Holds]
  refine ⟨[A.eval M ρ bs], .cons (evalKind hF hρ hbs hA) .nil, trivial, ?_⟩
  have hs := evalShift (M := M) (.arrow A .empty A) ρ bs [A.eval M ρ bs]
  simp only [List.length_cons, List.length_nil] at hs
  have ht := evalKind hF hρ hbs (arrowKind hA (emptyKind hF.signature) hA)
  simp only [Constraint.le, Constraint.Holds, List.map_cons, List.map_nil,
    Predicate.eval, List.length_cons, List.length_nil] at ⊢
  rw [hs]
  simpa only [Ty.arrow, Ty.empty, Ty.eval, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.getElem?_cons_zero, Option.getD_some] using
    And.intro ht (And.intro ht (hF.belowRefl 0 hF.signature.1 _ ht))

/-- An actual polymorphic let derivation, independent of inference soundness. -/
theorem polymorphicLetTyping (hF : EffectFramework S M) (hA : Ty.HasKind S Δ A 0) :
    Typing S M sig Δ .truth {} (.letE identity (.ident (.bound 0)))
      (.arrow A .empty A) .empty := by
  have hbound : Ty.HasKind S ([0] ++ Δ) (.bound 0) 0 := .bound rfl hF.signature.1
  have hpoly := identityTyping (sig := sig) hF hbound
  have hArrow := arrowKind hA (emptyKind hF.signature) hA
  apply Typing.letPoly (ks := [0]) (D := .truth)
    (A := .arrow (.bound 0) .empty (.bound 0))
  · refine ⟨trivial, rfl, ?_, ?_, hArrow, emptyKind hF.signature⟩
    · simp [Env.WF]
    · simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.dpi, identity]
  · rfl
  · apply Typing.strengthen (C := .truth)
    · exact ⟨⟨trivial,trivial⟩, rfl, (typingWF hpoly).2.2⟩
    · exact hpoly
    · intro _ _ _ _ _ _ _; trivial
  · intro ρ bs ι hρ hbs _ _
    exact ⟨[A.eval M ρ bs], .cons (evalKind hF hρ hbs hA) .nil, trivial⟩
  · apply Typing.var (s := identityScheme)
    · refine ⟨trivial, rfl, ?_, ?_, hArrow, emptyKind hF.signature⟩
      · constructor
        · simp [Env.push]
        intro s hs
        simp only [Env.push, List.mem_cons, List.mem_nil_iff, or_false] at hs
        subst s
        exact ⟨⟨by simp [hF.signature.1], trivial,
          arrowKind hbound (emptyKind hF.signature) hbound⟩, rfl⟩
      · simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi]
    · rfl
    · exact identitySchemeInstance hF hA

def resumedHandler : Expr :=
  .handle (.perform 0 identity) 0 (.ident (.bound 0))
    (.app (.ident (.bound 0)) (.ident (.bound 1)))

theorem handlerGenerationWF :
    (generate signature resumedHandler identityType .empty).WF Concrete.signature [] 0 := by
  apply generationWF Concrete.framework.signature signatureWF
  · simp [resumedHandler, identity, Expr.LCAt]
  · exact arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind
  · exact emptyKind Concrete.framework.signature

theorem simultaneousClauseOpening :
    (Expr.app (.ident (.bound 0)) (.ident (.bound 1))).openAt 0 [identity, .ident (.free 7)] =
      .app identity (.ident (.free 7)) := by
  simp [Expr.openAt, Expr.shift, identity]

theorem letRhsCaptures :
    Step (.handle (.letE (.perform 0 identity) (.ident (.bound 0))) 0
      (.ident (.bound 0)) (.app (.ident (.bound 0)) (.ident (.bound 1))))
      ((Expr.app (.ident (.bound 0)) (.ident (.bound 1))).openAt 0
        [Expr.resume (.letRhs .hole (.ident (.bound 0))) 0 (.ident (.bound 0))
          (.app (.ident (.bound 0)) (.ident (.bound 1))), identity]) :=
  .operation (E := .letRhs .hole (.ident (.bound 0))) (v := identity)
    rfl (by simp [EvalCtx.handled])

theorem nestedSameOperationDoesNotEscape :
    ¬ (0 ∉ (EvalCtx.handle .hole 0 (.ident (.bound 0)) (.ident (.bound 1))).handled) := by
  simp [EvalCtx.handled]

theorem otherHandlerPasses :
    Unhandled (.handle (.perform 0 identity) 1 (.ident (.bound 0)) (.ident (.bound 1))) 0 := by
  exact ⟨.handle .hole 1 (.ident (.bound 0)) (.ident (.bound 1)), identity,
    rfl, rfl, by simp [EvalCtx.handled]⟩

theorem clauseRunsOutsideHandler :
    Step (.handle (.perform 0 identity) 0 (.ident (.bound 0))
      (.perform 0 (.ident (.bound 1)))) (.perform 0 identity) := by
  have h := Step.operation (E := .hole) (v := identity) (ret := .ident (.bound 0))
    (clause := .perform 0 (.ident (.bound 1))) (op := 0) rfl (by simp [EvalCtx.handled])
  simpa [EvalCtx.plug, Expr.openAt, Expr.shift, identity] using h

theorem unknownOperationRejected :
    generate signature (.perform 9 identity) base .empty = .falsity := by
  simp [generate, signature]

theorem unknownOperationHasNoDerivation (C : Constraint) :
    ¬ Typing Concrete.signature Concrete.model signature [] C {} (.perform 9 identity) base .empty :=
  unknownPerformNotTypable (by simp [signature])

theorem nonValueLetSharesType (body : Expr) :
    generate signature (.letE (.perform 0 identity) body) base .empty =
      .exists_ [0,1,1] (.conj (generate signature (.perform 0 identity) (.bound 0) (.bound 1))
        (.conj (.def_ (.mono (.bound 0)) (generate signature body (base.shift 3 0) (.bound 2)))
          (.le 1 (.union (.bound 1) (.bound 2)) (Ty.empty.shift 3 0)))) := by
  simp only [generate, Expr.isValue, Bool.false_eq_true, ↓reduceIte]

theorem clauseCannotEscapeKind : ¬ Ty.HasKind Concrete.signature [] (.bound 0) 0 := by
  intro h
  cases h with | bound hi _ => simp at hi

end EHMX.Regression
