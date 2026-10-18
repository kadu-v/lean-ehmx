import EHMX.Regression
import EHMX.Proofs.Preservation

/-! 最終保存・安全性定理を実際の型付け導出へ適用する回帰例。 -/
namespace EHMX.Regression

/-- 透過する別操作の handler も同じ多相宣言を使う。 -/
def safetySignature : OpSignature := fun _ => some mixed

theorem safetySignatureWF : OpSignature.WF Concrete.signature safetySignature := by
  intro op d h
  cases h
  exact signatureWF 0 mixed rfl

theorem safetyAssumptions : SafetyAssumptions Concrete.signature Concrete.model safetySignature :=
  ⟨⟨Concrete.framework, safetySignatureWF⟩, Concrete.arrowSeparated⟩

private theorem identityKind : Ty.HasKind Concrete.signature Δ identityType 0 :=
  arrowKind baseKind (emptyKind Concrete.framework.signature) baseKind

@[simp] private theorem identityTypeShift (n d : Nat) : identityType.shift n d = identityType := by
  simp [identityType, base, Ty.arrow, Ty.empty, Ty.shift]

private theorem pushWF (hΓ : Env.WF S Δ Γ) (hA : Ty.HasKind S Δ A 0) :
    (Γ.push (.mono A)).WF S Δ := by
  refine ⟨hΓ.1, ?_⟩
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact monoWF hA
  · exact hΓ.2 s hs

private theorem zeroTyping (hΓ : Env.WF Concrete.signature Δ Γ)
    (hA : Ty.HasKind Concrete.signature Δ A 0) :
    Typing Concrete.signature Concrete.model safetySignature Δ .truth
      (Γ.push (.mono A)) (.ident (.bound 0)) A .empty :=
  .var ⟨trivial, rfl, pushWF hΓ hA, by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push],
    hA, emptyKind Concrete.framework.signature⟩ rfl (monoInstance Concrete.framework hA)

private theorem raiseEffect (ht : Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ e T .empty)
    (hε : Ty.HasKind Concrete.signature Δ ε 1) :
    Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ e T ε :=
  .sub ⟨trivial, rfl, (typingWF ht).2.2.1, (typingWF ht).2.2.2.1, (typingWF ht).2.2.2.2.1, hε⟩ ht
    (leRefl Concrete.framework Concrete.framework.signature.1 (typingWF ht).2.2.2.2.1)
    (effectEmptyBelow Concrete.framework hε)

private theorem unionBelow (hε : Ty.HasKind Concrete.signature Δ ε 1)
    (hη : Ty.HasKind Concrete.signature Δ η 1) (hζ : Ty.HasKind Concrete.signature Δ ζ 1)
    (h₁ : Entails Concrete.signature Concrete.model Δ C (.le 1 ε ζ))
    (h₂ : Entails Concrete.signature Concrete.model Δ C (.le 1 η ζ)) :
    Entails Concrete.signature Concrete.model Δ C (.le 1 (.union ε η) ζ) := by
  intro ρ bs ι hρ hbs hι hC
  have hεv := evalKind Concrete.framework hρ hbs hε
  have hηv := evalKind Concrete.framework hρ hbs hη
  have hζv := evalKind Concrete.framework hρ hbs hζ
  have huv := evalKind Concrete.framework hρ hbs (unionKind hε hη)
  refine ⟨huv, hζv, (Concrete.framework.effectOrder _ _ huv hζv).mpr ?_⟩
  rw [effectsUnion Concrete.framework hρ hbs (unionKind hε hη)]
  exact Set.union_subset
    ((Concrete.framework.effectOrder _ _ hεv hζv).mp (h₁ _ _ _ hρ hbs hι hC).2.2)
    ((Concrete.framework.effectOrder _ _ hηv hζv).mp (h₂ _ _ _ hρ hbs hι hC).2.2)

private theorem appPure (hf : Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ f (.arrow A ε B) .empty)
    (hx : Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ x A .empty) :
    Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ (.app f x) B ε := by
  have hks := arrowKinds (typingWF hf).2.2.2.2.1
  have he := emptyKind (Δ := Δ) Concrete.framework.signature
  have ht := Typing.app (S := Concrete.signature) (C := .truth) ⟨trivial, rfl, (typingWF hf).2.2.1,
    scopedApp (typingWF hf).2.2.2.1 (typingWF hx).2.2.2.1, hks.2.2,
    unionKind (unionKind he he) hks.2.1⟩ hf hx
  exact .sub ⟨trivial, rfl, (typingWF ht).2.2.1, (typingWF ht).2.2.2.1, hks.2.2, hks.2.1⟩ ht
    (leRefl Concrete.framework Concrete.framework.signature.1 hks.2.2)
    (unionBelow (unionKind he he) hks.2.1 hks.2.1
      (unionBelow he he hks.2.1 (effectEmptyBelow Concrete.framework hks.2.1)
        (effectEmptyBelow Concrete.framework hks.2.1))
      (leRefl Concrete.framework Concrete.framework.signature.2.1 hks.2.1))

private theorem letSameEffect
    (hr : Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ rhs A ε)
    (hb : Typing Concrete.signature Concrete.model safetySignature Δ .truth (Γ.push (.mono A)) body B ε) :
    Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ (.letE rhs body) B ε := by
  have hε := (typingWF hr).2.2.2.2.2
  have hB := (typingWF hb).2.2.2.2.1
  have ht := Typing.letMono (S := Concrete.signature) (C := .truth) ⟨trivial, rfl, (typingWF hr).2.2.1,
    scopedLet (typingWF hr).2.2.2.1 (typingWF hb).2.2.2.1, hB, unionKind hε hε⟩ hr hb
  exact .sub ⟨trivial, rfl, (typingWF hr).2.2.1, (typingWF ht).2.2.2.1, hB, hε⟩ ht
    (leRefl Concrete.framework Concrete.framework.signature.1 hB)
    (unionBelow hε hε hε (leRefl Concrete.framework Concrete.framework.signature.2.1 hε)
      (leRefl Concrete.framework Concrete.framework.signature.2.1 hε))

def resumeClause : Expr := .app (.ident (.bound 0)) (.ident (.bound 1))
def twiceClause : Expr := .letE resumeClause (.app (.ident (.bound 1)) (.ident (.bound 2)))

private theorem resumeClauseGeneral (hΓ : Env.WF Concrete.signature Δ Γ)
    (hε : Ty.HasKind Concrete.signature Δ ε 1) :
    Typing Concrete.signature Concrete.model safetySignature ([0,1] ++ Δ) .truth
      (((Γ.shift 2).push (.mono mixed.input)).push
        (.mono (.arrow mixed.output (ε.shift 2 0) identityType))) resumeClause identityType (ε.shift 2 0) := by
  have ha : Ty.HasKind Concrete.signature ([0,1] ++ Δ) (.bound 0) 0 := .bound rfl (by simp [Concrete.signature])
  have he : Ty.HasKind Concrete.signature ([0,1] ++ Δ) (.bound 1) 1 := .bound rfl (by simp [Concrete.signature])
  have hR : Ty.HasKind Concrete.signature ([0,1] ++ Δ) mixed.input 0 := arrowKind ha he ha
  have hΓ' := envSubstBoundWF hΓ (BoundSubst.validShift [0,1])
  rw [← envShiftSubstBound] at hΓ'
  have hK := arrowKind hR (kindShift hε [0,1]) identityKind
  have hk := zeroTyping (pushWF hΓ' hR) hK
  have hx := typingWeakening (zeroTyping hΓ' hR) (monoWF hK)
  exact appPure hk hx

private theorem twiceClauseGeneral (hΓ : Env.WF Concrete.signature Δ Γ)
    (hε : Ty.HasKind Concrete.signature Δ ε 1) :
    Typing Concrete.signature Concrete.model safetySignature ([0,1] ++ Δ) .truth
      (((Γ.shift 2).push (.mono mixed.input)).push
        (.mono (.arrow mixed.output (ε.shift 2 0) identityType))) twiceClause identityType (ε.shift 2 0) := by
  have ht := resumeClauseGeneral hΓ hε
  exact letSameEffect ht (typingWeakening ht (monoWF identityKind))

private theorem performIdentity
    (ht : Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ v identityType .empty) (op : Op) :
    Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ (.perform op v) identityType
      (.union (.singleton op) .empty) := by
  have hi : mixed.input.openAt 0 [base, .empty] = identityType := by
    simp [mixed, identityType, Ty.arrow, Ty.openAt]
  have ho : mixed.output.openAt 0 [base, .empty] = identityType := hi
  have h := Typing.performTruth rfl (sig := safetySignature) (decl := mixed) (args := [base, .empty])
    (op := op) (ε := .empty)
    (show JudgmentWF Concrete.signature Δ .truth Γ (.perform op v)
      (mixed.output.openAt 0 [base, .empty]) (.union (.singleton op) .empty) from
      ⟨trivial, rfl, (typingWF ht).2.2.1, (typingWF ht).2.2.2.1, ho ▸ identityKind,
        unionKind (singletonKind op) (emptyKind Concrete.framework.signature)⟩)
    rfl (.cons baseKind (.cons (emptyKind Concrete.framework.signature) .nil)) (hi ▸ ht)
  simpa only [ho] using h

private theorem handleIdentity
    (ht : Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ body identityType εin)
    (hε : Ty.HasKind Concrete.signature Δ εout 1)
    (he : Entails Concrete.signature Concrete.model Δ .truth (.le 1 εin (.union (.singleton op) εout)))
    (hc : Typing Concrete.signature Concrete.model safetySignature ([0,1] ++ Δ) .truth
      (((Γ.shift 2).push (.mono mixed.input)).push
        (.mono (.arrow mixed.output (εout.shift 2 0) identityType))) clause identityType (εout.shift 2 0)) :
    Typing Concrete.signature Concrete.model safetySignature Δ .truth Γ
      (.handle body op (.ident (.bound 0)) clause) identityType εout := by
  have hr := raiseEffect (zeroTyping (typingWF ht).2.2.1 identityKind) hε
  exact .handleTruth rfl ⟨trivial, rfl, (typingWF ht).2.2.1,
    scopedHandle (typingWF ht).2.2.2.1 (typingWF hr).2.2.2.1 (typingWF hc).2.2.2.1,
    identityKind, hε⟩ rfl ht he hr (by simpa only [mixed, List.length_cons,
      List.length_nil, Constraint.shift, identityTypeShift] using hc)

theorem mixedOperationTyping :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} (.perform 0 identity)
      identityType (.union (.singleton 0) .empty) :=
  performIdentity (identityTyping Concrete.framework baseKind) 0

theorem resumedHandlerTyping :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} resumedHandler identityType .empty :=
  handleIdentity mixedOperationTyping (emptyKind Concrete.framework.signature)
    (leRefl Concrete.framework Concrete.framework.signature.2.1 (unionKind (singletonKind 0)
      (emptyKind Concrete.framework.signature)))
    (resumeClauseGeneral (by simp [Env.WF]) (emptyKind Concrete.framework.signature))

theorem mixedOperationPreserved : Typing Concrete.signature Concrete.model safetySignature [] .truth {}
    (resumeClause.openAt 0 [Expr.resume .hole 0 (.ident (.bound 0)) resumeClause, identity]) identityType .empty :=
  operationPreservation _ _ _ safetyAssumptions _ _ _ _ _ _ _ _ _ _ rfl (by simp [EvalCtx.handled])
    resumedHandlerTyping

def letCaptured : Expr := .handle (.letE (.perform 0 identity) (.ident (.bound 0))) 0
  (.ident (.bound 0)) resumeClause

theorem letCapturedTyping :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} letCaptured identityType .empty := by
  have hε := unionKind (singletonKind (S := Concrete.signature) (Δ := []) 0)
    (emptyKind Concrete.framework.signature)
  have hb := letSameEffect mixedOperationTyping
    (raiseEffect (zeroTyping (by simp [Env.WF]) identityKind) hε)
  exact handleIdentity hb (emptyKind Concrete.framework.signature)
    (leRefl Concrete.framework Concrete.framework.signature.2.1 hε)
    (resumeClauseGeneral (by simp [Env.WF]) (emptyKind Concrete.framework.signature))

theorem letCapturedPreserved :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {}
      (resumeClause.openAt 0 [Expr.resume (.letRhs .hole (.ident (.bound 0))) 0
        (.ident (.bound 0)) resumeClause, identity]) identityType .empty :=
  preservation _ _ _ safetyAssumptions _ _ _ _ _ _ _ letCapturedTyping
    (.operation (E := .letRhs .hole (.ident (.bound 0))) rfl (by simp [EvalCtx.handled]))

def twiceHandler : Expr := .handle (.perform 0 identity) 0 (.ident (.bound 0)) twiceClause

theorem twiceHandlerTyping :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} twiceHandler identityType .empty :=
  handleIdentity mixedOperationTyping (emptyKind Concrete.framework.signature)
    (leRefl Concrete.framework Concrete.framework.signature.2.1
      (unionKind (singletonKind 0) (emptyKind Concrete.framework.signature)))
    (twiceClauseGeneral (by simp [Env.WF]) (emptyKind Concrete.framework.signature))

theorem twiceContinuationPreserved :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {}
      (twiceClause.openAt 0 [Expr.resume .hole 0 (.ident (.bound 0)) twiceClause, identity]) identityType .empty :=
  preservation _ _ _ safetyAssumptions _ _ _ _ _ _ _ twiceHandlerTyping
    (.operation (E := .hole) rfl (by simp [EvalCtx.handled]))

/-- 引数も return 節も外側の項変数を実際に使う。 -/
def openHandler : Expr := .handle (.perform 0 (.ident (.bound 0))) 0 (.ident (.bound 1)) resumeClause

theorem openHandlerTyping :
    Typing Concrete.signature Concrete.model safetySignature [] .truth
      (({} : Env).push (.mono identityType)) openHandler identityType .empty := by
  have hv := zeroTyping (Δ := []) (Γ := {}) (by simp [Env.WF]) identityKind
  have hb := performIdentity hv 0
  have hr := typingWeakening hv (monoWF identityKind)
  have hc := resumeClauseGeneral (typingWF hv).2.2.1 (emptyKind Concrete.framework.signature)
  apply Typing.handleTruth rfl (S := Concrete.signature) (C := .truth) (decl := mixed)
    ⟨trivial, rfl, (typingWF hv).2.2.1,
      scopedHandle (typingWF hb).2.2.2.1 (typingWF hr).2.2.2.1 (typingWF hc).2.2.2.1,
      identityKind, emptyKind Concrete.framework.signature⟩ rfl hb
    (leRefl Concrete.framework Concrete.framework.signature.2.1 (typingWF hb).2.2.2.2.2) hr
  simpa only [mixed, List.length_cons, List.length_nil, Constraint.shift,
    Ty.empty, Ty.shift, List.map_nil, identityTypeShift] using hc

theorem openHandlerPreserved :
    Typing Concrete.signature Concrete.model safetySignature [] .truth
      (({} : Env).push (.mono identityType))
      (resumeClause.openAt 0 [Expr.resume .hole 0 (.ident (.bound 1)) resumeClause, .ident (.bound 0)])
      identityType .empty :=
  preservation _ _ _ safetyAssumptions _ _ _ _ _ _ _ openHandlerTyping
    (.operation (E := .hole) rfl (by simp [EvalCtx.handled]))

theorem openContinuationKeepsOuterVariable :
    Expr.resume .hole 0 (.ident (.bound 1)) resumeClause =
      .lam (.handle (.ident (.bound 0)) 0 (.ident (.bound 2)) resumeClause) := by
  simp [Expr.resume, EvalCtx.shift, EvalCtx.plug, Expr.shift, resumeClause]

def nestedSame : Expr := .handle resumedHandler 0 (.ident (.bound 0)) resumeClause

theorem nestedSameTyping :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} nestedSame identityType .empty :=
  handleIdentity resumedHandlerTyping (emptyKind Concrete.framework.signature)
    (effectEmptyBelow Concrete.framework (unionKind (singletonKind 0) (emptyKind Concrete.framework.signature)))
    (resumeClauseGeneral (by simp [Env.WF]) (emptyKind Concrete.framework.signature))

theorem nestedSamePreserved :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {}
      (.handle (resumeClause.openAt 0 [Expr.resume .hole 0 (.ident (.bound 0)) resumeClause, identity])
        0 (.ident (.bound 0)) resumeClause) identityType .empty :=
  preservation _ _ _ safetyAssumptions _ _ _ _ _ _ _ nestedSameTyping
    (.context (E := .handle .hole 0 (.ident (.bound 0)) resumeClause)
      (.operation (E := .hole) rfl (by simp [EvalCtx.handled])))

def passOther : Expr := .handle (.handle (.perform 0 identity) 1 (.ident (.bound 0)) resumeClause)
  0 (.ident (.bound 0)) resumeClause

theorem passOtherTyping :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} passOther identityType .empty := by
  have hε := (typingWF mixedOperationTyping).2.2.2.2.2
  have hb := handleIdentity (op := 1) mixedOperationTyping hε
    (effectUnionRight Concrete.framework (singletonKind 1) hε)
    (resumeClauseGeneral (by simp [Env.WF]) hε)
  exact handleIdentity hb (emptyKind Concrete.framework.signature)
    (leRefl Concrete.framework Concrete.framework.signature.2.1 hε)
    (resumeClauseGeneral (by simp [Env.WF]) (emptyKind Concrete.framework.signature))

theorem passOtherPreserved :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {}
      (resumeClause.openAt 0 [Expr.resume (.handle .hole 1 (.ident (.bound 0)) resumeClause)
        0 (.ident (.bound 0)) resumeClause, identity]) identityType .empty :=
  preservation _ _ _ safetyAssumptions _ _ _ _ _ _ _ passOtherTyping
    (.operation (E := .handle .hole 1 (.ident (.bound 0)) resumeClause) rfl (by simp [EvalCtx.handled]))

theorem resumedHandlerSteps : Steps resumedHandler identity := by
  have h₁ : Step resumedHandler (.app (Expr.resume .hole 0 (.ident (.bound 0)) resumeClause) identity) := by
    simpa [resumedHandler, resumeClause, Expr.openAt, Expr.shift, Expr.resume, EvalCtx.shift, EvalCtx.plug,
      identity] using (Step.operation (E := .hole) (op := 0) (v := identity)
        (ret := .ident (.bound 0)) (clause := resumeClause) rfl (by simp [EvalCtx.handled]))
  have h₂ : Step (.app (Expr.resume .hole 0 (.ident (.bound 0)) resumeClause) identity)
      (.handle identity 0 (.ident (.bound 0)) resumeClause) := by
    simpa [Expr.resume, Expr.openAt, Expr.shift, EvalCtx.shift, EvalCtx.plug, resumeClause, identity] using
      (Step.beta (body := .handle (.ident (.bound 0)) 0 (.ident (.bound 0)) resumeClause) (v := identity) rfl)
  have h₃ : Step (.handle identity 0 (.ident (.bound 0)) resumeClause) identity := by
    simpa [Expr.openAt, Expr.shift, identity] using
      (Step.returnValue (v := identity) (op := 0) (ret := .ident (.bound 0)) (clause := resumeClause) rfl)
  exact ((Steps.refl _).tail h₁).tail h₂ |>.tail h₃

theorem resumedHandlerMultistepPreserved :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} identity identityType .empty :=
  preservationSteps safetyAssumptions resumedHandlerTyping resumedHandlerSteps

def testAssignment : Assignment Concrete.model := fun X =>
  if X.1 = 1 then .effect ∅ else .type (.base 0)
def testGroundEnv : GroundEnv Concrete.model := ⟨fun _ => ∅, []⟩

theorem testAssignmentValid : Assignment.Valid Concrete.signature Concrete.model testAssignment := by
  intro X hX
  have h : X.1 = 0 ∨ X.1 = 1 := hX
  rcases h with h | h <;> simp [testAssignment, h, Concrete.model, Concrete.kind]

theorem testGroundEnvValid : testGroundEnv.Valid := by
  simp [testGroundEnv, GroundEnv.Valid, UpperSet]

theorem truthSatisfiable : Satisfiable Concrete.signature Concrete.model [] .truth :=
  ⟨trivial, testAssignment, [], testGroundEnv, testAssignmentValid, .nil, testGroundEnvValid, trivial⟩

theorem resumedHandlerReachableSafe (hs : Steps resumedHandler e') : Value e' ∨ ∃ e'', Step e' e'' :=
  emptyEffectSafety _ _ _ safetyAssumptions _ _ _ _ truthSatisfiable resumedHandlerTyping hs

theorem emptyEffectMultistepSafety : Value identity ∨ ∃ e', Step identity e' :=
  emptyEffectSafety _ _ _ safetyAssumptions _ _ _ _ truthSatisfiable resumedHandlerTyping resumedHandlerSteps

def reperformHandler : Expr := .handle (.perform 0 identity) 0 (.ident (.bound 0)) (.perform 0 identity)

theorem reperformHandlerTyping :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} reperformHandler identityType
      (.union (.singleton 0) .empty) := by
  have hε := (typingWF mixedOperationTyping).2.2.2.2.2
  have hclauseEnv := (typingWF (resumeClauseGeneral (Δ := []) (Γ := {}) (by simp [Env.WF]) hε)).2.2.1
  have hid : Typing Concrete.signature Concrete.model safetySignature [0,1] .truth _ identity identityType .empty :=
    .lam ⟨trivial, rfl, hclauseEnv, by simp [Expr.Scoped, Expr.LCAt, Expr.fv],
      identityKind, emptyKind Concrete.framework.signature⟩ (zeroTyping hclauseEnv baseKind)
  have hc := performIdentity hid 0
  exact handleIdentity mixedOperationTyping hε
    (effectUnionRight Concrete.framework (singletonKind 0) hε)
    (by simpa [Ty.union, Ty.singleton, Ty.empty, Ty.shift] using hc)

theorem reperformHandlerStep : Step reperformHandler (.perform 0 identity) := by
  simpa [reperformHandler, Expr.openAt, Expr.shift, identity, EvalCtx.plug] using
    (Step.operation (E := .hole) (v := identity) (op := 0) (ret := .ident (.bound 0))
      (clause := .perform 0 identity) rfl (by simp [EvalCtx.handled]))

theorem reperformPreserved :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} (.perform 0 identity) identityType
      (.union (.singleton 0) .empty) :=
  preservation _ _ _ safetyAssumptions _ _ _ _ _ _ _ reperformHandlerTyping reperformHandlerStep

theorem reperformAllowedUnhandled : Unhandled (.perform 0 identity) 0 ∧
    0 ∈ Concrete.model.effects ((Ty.union (.singleton 0) .empty).eval Concrete.model testAssignment []) := by
  constructor
  · exact ⟨.hole, identity, rfl, rfl, by simp [EvalCtx.handled]⟩
  · rw [effectsUnion Concrete.framework testAssignmentValid (.nil)
      (unionKind (singletonKind 0) (emptyKind Concrete.framework.signature))]
    exact Or.inl (by rw [effectsSingleton Concrete.framework]; exact Set.mem_singleton 0)

theorem nonemptyEffectReachableSafety :
    Value (.perform 0 identity) ∨ (∃ e', Step (.perform 0 identity) e') ∨
      ∃ op, Unhandled (.perform 0 identity) op ∧
        op ∈ Concrete.model.effects ((Ty.union (.singleton 0) .empty).eval Concrete.model testAssignment []) :=
  effectSafety _ _ _ safetyAssumptions _ _ _ _ _ reperformHandlerTyping
    ((Steps.refl _).tail reperformHandlerStep) testAssignment testGroundEnv
    testAssignmentValid testGroundEnvValid trivial

/-- 操作に使う型引数そのものを存在量化し、その作用域内で sub と strengthen を通す。 -/
theorem existentialOperationTyping :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} (.perform 0 identity)
      identityType (.union (.singleton 0) .empty) := by
  let A : Ty := .arrow (.bound 0) .empty (.bound 0)
  let K : Constraint := .le 0 A identityType
  have hα : Ty.HasKind Concrete.signature [0] (.bound 0) 0 := .bound rfl (by simp [Concrete.signature])
  have hA : Ty.HasKind Concrete.signature [0] A 0 := arrowKind hα (emptyKind Concrete.framework.signature) hα
  have hid := identityTyping (sig := safetySignature) Concrete.framework hα
  have hidA : Typing Concrete.signature Concrete.model safetySignature [0] .truth {} identity A .empty := hid
  have hi : mixed.input.openAt 0 [.bound 0, .empty] = A := by
    simp [mixed, A, Ty.arrow, Ty.openAt]
  have hop : Typing Concrete.signature Concrete.model safetySignature [0] .truth {}
      (.perform 0 identity) A (.union (.singleton 0) .empty) := by
    have ht := Typing.performTruth rfl (S := Concrete.signature) (C := .truth) (sig := safetySignature)
      (decl := mixed) (args := [.bound 0, .empty]) (op := 0) (ε := .empty) (arg := identity)
      ⟨trivial, rfl, (typingWF hid).2.2.1, (typingWF hid).2.2.2.1, hi ▸ hA,
        unionKind (singletonKind 0) (emptyKind Concrete.framework.signature)⟩
      rfl (.cons hα (.cons (emptyKind Concrete.framework.signature) .nil)) (hi ▸ hidA)
    simpa only [show mixed.output = mixed.input from rfl, hi] using ht
  have hK : K.WF Concrete.signature [0] 0 :=
    leConstraintWF Concrete.framework.signature.1 hA identityKind
  have hstrong := typingStronger hop hK rfl (fun _ _ _ _ _ _ _ => trivial)
  have hsub : Typing Concrete.signature Concrete.model safetySignature [0] K {}
      (.perform 0 identity) identityType (.union (.singleton 0) .empty) :=
    .sub ⟨hK, rfl, (typingWF hop).2.2.1, (typingWF hop).2.2.2.1, identityKind,
      (typingWF hop).2.2.2.2.2⟩ hstrong entailsRefl
      (leRefl Concrete.framework Concrete.framework.signature.2.1 (typingWF hop).2.2.2.2.2)
  have hex : Typing Concrete.signature Concrete.model safetySignature [] (.exists_ [0] K) {}
      (.perform 0 identity) identityType (.union (.singleton 0) .empty) := by
    apply Typing.exists_ ⟨⟨by simp [Concrete.signature], hK⟩, rfl, (typingWF mixedOperationTyping).2.2⟩
    simpa [Env.shift, Ty.union, Ty.singleton, Ty.empty, Ty.shift] using hsub
  apply typingStronger (D := .truth) hex trivial rfl
  intro ρ bs ι hρ hbs hι _
  refine ⟨[base.eval Concrete.model ρ bs], .cons (evalKind Concrete.framework hρ hbs baseKind) .nil, ?_⟩
  have hle := leRefl (Δ := []) (C := .truth) Concrete.framework Concrete.framework.signature.1 identityKind
    ρ bs ι hρ hbs hι trivial
  simpa [K, A, identityType, base, Constraint.le, Constraint.Holds, Predicate.eval,
    Ty.arrow, Ty.empty, Ty.eval] using hle

theorem existentialCapturePreserved : Typing Concrete.signature Concrete.model safetySignature [] .truth {}
    (resumeClause.openAt 0 [Expr.resume .hole 0 (.ident (.bound 0)) resumeClause, identity]) identityType .empty := by
  have ht := handleIdentity existentialOperationTyping (emptyKind Concrete.framework.signature)
    (leRefl Concrete.framework Concrete.framework.signature.2.1 (typingWF existentialOperationTyping).2.2.2.2.2)
    (resumeClauseGeneral (by simp [Env.WF]) (emptyKind Concrete.framework.signature))
  exact preservation _ _ _ safetyAssumptions _ _ _ _ _ _ _ ht
    (.operation (E := .hole) rfl (by simp [EvalCtx.handled]))

theorem twiceHandlerSteps : Steps twiceHandler identity := by
  let k := Expr.resume .hole 0 (.ident (.bound 0)) twiceClause
  have h₁ : Step twiceHandler (.letE (.app k identity) (.app k identity)) := by
    simpa [twiceHandler, twiceClause, resumeClause, k, Expr.resume, EvalCtx.shift, EvalCtx.plug,
      Expr.openAt, Expr.shift, identity] using
      (Step.operation (E := .hole) (v := identity) (op := 0) (ret := .ident (.bound 0))
        (clause := twiceClause) rfl (by simp [EvalCtx.handled]))
  have hcall : Step (.app k identity) (.handle identity 0 (.ident (.bound 0)) twiceClause) := by
    simpa [k, Expr.resume, Expr.openAt, Expr.shift, EvalCtx.shift, EvalCtx.plug, twiceClause,
      resumeClause, identity] using
      (Step.beta (body := .handle (.ident (.bound 0)) 0 (.ident (.bound 0)) twiceClause) (v := identity) rfl)
  have hret : Step (.handle identity 0 (.ident (.bound 0)) twiceClause) identity := by
    simpa [Expr.openAt, Expr.shift, identity] using
      (Step.returnValue (v := identity) (op := 0) (ret := .ident (.bound 0)) (clause := twiceClause) rfl)
  have hlet : Step (.letE identity (.app k identity)) (.app k identity) := by
    simpa [k, Expr.resume, Expr.openAt, Expr.shift, EvalCtx.shift, EvalCtx.plug, twiceClause,
      resumeClause, identity] using (Step.letValue (v := identity) (body := .app k identity) rfl)
  exact ((((((Steps.refl _).tail h₁).tail
    (.context (E := .letRhs .hole (.app k identity)) hcall)).tail
    (.context (E := .letRhs .hole (.app k identity)) hret)).tail hlet).tail hcall).tail hret

theorem twiceContinuationMultistepPreserved :
    Typing Concrete.signature Concrete.model safetySignature [] .truth {} identity identityType .empty :=
  preservationSteps safetyAssumptions twiceHandlerTyping twiceHandlerSteps

end EHMX.Regression
