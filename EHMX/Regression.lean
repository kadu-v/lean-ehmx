import EHMX.Concrete
import EHMX.Proofs.Generation
import EHMX.Proofs.Progress
import EHMX.Proofs.Reduction

/-! 回帰例。実行・生成・型付けを区別し、推論定理に依存しない導出を構成する。 -/
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

/-- 簡約別の保存補題を実際の型付け導出へ適用する。
操作捕捉と最終安全性定理の回帰は SafetyRegression.lean にある。 -/
def emptyTriple : Effect := .union (.union .empty .empty) .empty

theorem betaTyping : Typing Concrete.signature Concrete.model signature [] .truth {}
    (.app identity identity) identityType emptyTriple := by
  have hI : Ty.HasKind Concrete.signature [] identityType 0 :=
    arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind
  have hf := identityTyping (sig := signature) Concrete.framework hI
  have hx := identityTyping (sig := signature) Concrete.framework (baseKind (Δ := []))
  exact .app ⟨trivial, rfl, by simp [Env.WF], by
    simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.dpi, identity], hI,
    unionKind (unionKind (emptyKind Concrete.framework.signature)
      (emptyKind Concrete.framework.signature)) (emptyKind Concrete.framework.signature)⟩ hf hx

theorem betaTypedReduction : Typing Concrete.signature Concrete.model signature [] .truth {}
    identity identityType emptyTriple := by
  have h := betaPreservation Concrete.framework signatureWF (v := identity)
    (body := .ident (.bound 0)) rfl betaTyping rfl
  simpa [Expr.openAt, Expr.shift, identity, identityType] using h

theorem polymorphicLetTypedReduction :
    Typing Concrete.signature Concrete.model signature [] .truth {} identity identityType .empty := by
  have h := letPreservation Concrete.framework signatureWF (v := identity) rfl
    (polymorphicLetTyping (sig := signature) Concrete.framework (baseKind (Δ := []))) rfl
  simpa [Expr.openAt, Expr.shift, identity, identityType] using h

private theorem variableSelf (hΓ : Env.WF S Δ Γ) (hA : Ty.HasKind S Δ A 0)
    (hF : EffectFramework S M) (hl : Γ.lookup x = some (.mono A))
    (hs : (Expr.ident x).Scoped Γ) : Typing S M sig Δ .truth Γ (.ident x) A .empty :=
  .var ⟨trivial, rfl, hΓ, hs, hA, emptyKind hF.signature⟩ hl (monoInstance hF hA)

theorem monomorphicLetTyping : Typing Concrete.signature Concrete.model signature [] .truth {}
    (.letE identity (.ident (.bound 0))) identityType (.union .empty .empty) := by
  have hI : Ty.HasKind Concrete.signature [] identityType 0 :=
    arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind
  have hbody : Typing Concrete.signature Concrete.model signature [] .truth
      (({} : Env).push (.mono identityType)) (.ident (.bound 0)) identityType .empty := by
    refine variableSelf ?_ hI Concrete.framework rfl ?_
    · simp [Env.WF, Env.push, Scheme.mono, Scheme.WF, Scheme.fpi, Constraint.WF, Constraint.fpi, hI]
    · simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi]
  exact .letMono ⟨trivial, rfl, by simp [Env.WF], by
    simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.dpi, identity], hI,
    unionKind (emptyKind Concrete.framework.signature) (emptyKind Concrete.framework.signature)⟩
    (identityTyping Concrete.framework baseKind) hbody

theorem monomorphicLetTypedReduction : Typing Concrete.signature Concrete.model signature [] .truth {}
    identity identityType (.union .empty .empty) := by
  have h := letPreservation Concrete.framework signatureWF (v := identity) rfl monomorphicLetTyping rfl
  simpa [Expr.openAt, Expr.shift, identity, identityType] using h

/-- Fully typed mixed type/effect operation clause, with a deep continuation. -/
theorem mixedClauseTyping : Typing Concrete.signature Concrete.model signature [0,1] .truth
    ((({} : Env).push (.mono mixed.input)).push (.mono (.arrow mixed.output .empty identityType)))
    (.app (.ident (.bound 0)) (.ident (.bound 1))) identityType .empty := by
  have ha : Ty.HasKind Concrete.signature [0,1] (.bound 0) 0 := .bound rfl (by simp [Concrete.signature])
  have he : Ty.HasKind Concrete.signature [0,1] (.bound 1) 1 := .bound rfl (by simp [Concrete.signature])
  have hR : Ty.HasKind Concrete.signature [0,1] mixed.input 0 := arrowKind ha he ha
  have hI : Ty.HasKind Concrete.signature [0,1] identityType 0 :=
    arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind
  have hK := arrowKind hR (emptyKind Concrete.framework.signature) hI
  have hΓ : Env.WF Concrete.signature [0,1]
      ((({} : Env).push (.mono mixed.input)).push (.mono (.arrow mixed.output .empty identityType))) := by
    simp [Env.WF, Env.push, Scheme.mono, Scheme.WF, Scheme.fpi, Constraint.WF,
      Constraint.fpi, hR, hK, show mixed.output = mixed.input from rfl]
  have hk := variableSelf (sig := signature) hΓ hK Concrete.framework (x := .bound 0) rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi])
  have hx := variableSelf (sig := signature) hΓ hR Concrete.framework (x := .bound 1) rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi])
  have happ : Typing Concrete.signature Concrete.model signature [0,1] .truth _
      (.app (.ident (.bound 0)) (.ident (.bound 1))) identityType emptyTriple :=
    .app ⟨trivial, rfl, hΓ, scopedApp (typingWF hk).2.2.2.1 (typingWF hx).2.2.2.1,
      hI, unionKind (unionKind (emptyKind Concrete.framework.signature)
        (emptyKind Concrete.framework.signature)) (emptyKind Concrete.framework.signature)⟩ hk hx
  refine .sub (judgmentEmptyEffect Concrete.framework.signature (typingWF happ)) happ
    (leRefl Concrete.framework Concrete.framework.signature.1 hI) ?_
  intro ρ bs ι hρ hbs hι hC
  simp only [emptyTriple, Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.empty,
    Ty.eval, List.map_cons, List.map_nil]
  simp [Concrete.model, Concrete.constructor, Concrete.kind, Concrete.below]

theorem mixedClauseInstantiated : Typing Concrete.signature Concrete.model signature [] .truth
    ((({} : Env).push (.mono identityType)).push (.mono (.arrow identityType .empty identityType)))
    (.app (.ident (.bound 0)) (.ident (.bound 1))) identityType .empty := by
  have h := operationClauseInstantiation Concrete.framework signatureWF (ks := [0,1])
    (Δ := []) (C := .truth) (Γ := {}) (A := mixed.input) (R := mixed.output)
    (B := identityType) (ε := .empty)
    (by simpa [Constraint.shift, Env.shift, identityType, base, Ty.arrow, Ty.empty,
      Ty.shift] using mixedClauseTyping)
    (args := [base, .empty]) (.cons baseKind (.cons (emptyKind Concrete.framework.signature) .nil))
  simpa [mixed, identityType, base, Ty.arrow, Ty.openAt, Ty.shift, Ty.empty] using h

theorem returnHandlerTyping : Typing Concrete.signature Concrete.model signature [] .truth {}
    (.handle identity 0 (.ident (.bound 0))
      (.app (.ident (.bound 0)) (.ident (.bound 1)))) identityType .empty := by
  have hI : Ty.HasKind Concrete.signature [] identityType 0 :=
    arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind
  have hid := identityTyping (sig := signature) Concrete.framework (baseKind (Δ := []))
  apply Typing.handle (decl := mixed) (A := identityType) (εin := .empty)
  · exact ⟨trivial, rfl, by simp [Env.WF], by
      simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.dpi, identity], hI,
      emptyKind Concrete.framework.signature⟩
  · simp [signature]
  · exact hid
  · exact effectEmptyBelow Concrete.framework
      (unionKind (singletonKind 0) (emptyKind Concrete.framework.signature))
  · refine variableSelf ?_ hI Concrete.framework rfl ?_
    · simp [Env.WF, Env.push, Scheme.mono, Scheme.WF, Scheme.fpi, Constraint.WF, Constraint.fpi, hI]
    · simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi]
  · simpa [mixed, Constraint.shift, Env.shift, identityType, base, Ty.arrow, Ty.empty, Ty.shift]
      using mixedClauseTyping

theorem returnTypedReduction : Typing Concrete.signature Concrete.model signature [] .truth {}
    identity identityType .empty := by
  have h := returnPreservation Concrete.framework signatureWF (v := identity) rfl returnHandlerTyping rfl
  simpa [Expr.openAt, Expr.shift, identity, identityType] using h

/-- Preservation passes through exists_, strengthen and sub in one derivation. -/
theorem wrappedBetaTypedReduction :
    Typing Concrete.signature Concrete.model signature []
      (.exists_ [0] (.conj .truth .truth)) {} identity identityType emptyTriple := by
  have ht := typingShift Concrete.framework signatureWF betaTyping [0]
  have hw := typingWF ht
  have hs := Typing.sub hw ht (leRefl Concrete.framework Concrete.framework.signature.1 hw.2.2.2.2.1)
    (leRefl Concrete.framework Concrete.framework.signature.2.1 hw.2.2.2.2.2)
  have hstrength := Typing.strengthen (D := .conj .truth .truth)
    ⟨⟨trivial, trivial⟩, rfl, hw.2.2⟩ hs (fun _ _ _ _ _ _ _ => trivial)
  have houter : Typing Concrete.signature Concrete.model signature []
      (.exists_ [0] (.conj .truth .truth)) {} (.app identity identity) identityType emptyTriple := by
    apply Typing.exists_ (ks := [0]) (C := .conj .truth .truth)
      ⟨⟨by simp [Concrete.signature], ⟨trivial, trivial⟩⟩, rfl, (typingWF betaTyping).2.2⟩
    exact hstrength
  have h := betaPreservation Concrete.framework signatureWF (v := identity) rfl houter rfl
  simpa [Expr.openAt, Expr.shift, identity] using h

/-- A typed beta step inside a let RHS uses the fully quantified context lemma. -/
theorem letRhsBetaTypedReduction :
    Typing Concrete.signature Concrete.model signature [] .truth {}
      (.letE identity (.ident (.bound 0))) identityType (.union emptyTriple .empty) := by
  have hI : Ty.HasKind Concrete.signature [] identityType 0 :=
    arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind
  have hb : Typing Concrete.signature Concrete.model signature [] .truth
      (({} : Env).push (.mono identityType)) (.ident (.bound 0)) identityType .empty := by
    refine variableSelf ?_ hI Concrete.framework rfl ?_
    · simp [Env.WF, Env.push, Scheme.mono, Scheme.WF, Scheme.fpi, Constraint.WF, Constraint.fpi, hI]
    · simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi]
  have ht : Typing Concrete.signature Concrete.model signature [] .truth {}
      (.letE (.app identity identity) (.ident (.bound 0))) identityType (.union emptyTriple .empty) :=
    .letMono ⟨trivial, rfl, by simp [Env.WF],
      scopedLet (typingWF betaTyping).2.2.2.1 (typingWF hb).2.2.2.1, hI,
      unionKind (typingWF betaTyping).2.2.2.2.2 (emptyKind Concrete.framework.signature)⟩ betaTyping hb
  have hreplace : ∀ Δ C Γ T ε, Typing Concrete.signature Concrete.model signature Δ C Γ
      (.app identity identity) T ε → Typing Concrete.signature Concrete.model signature Δ C Γ identity T ε := by
    intro Δ C Γ T ε h
    simpa [Expr.openAt, Expr.shift, identity] using
      betaPreservation Concrete.framework signatureWF (v := identity) rfl h rfl
  exact evalCtxReplacement (by simp [Value, Expr.isValue]) hreplace ht
    (.letRhs .hole (.ident (.bound 0))) rfl

end EHMX.Regression
