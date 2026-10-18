import EHMX.TypeClassesRegression
import EHMX.Proofs.Preservation

/-! 述語条件付き操作は EHM(X) 固有の拡張。直接導出、推論、操作捕捉を検査する。 -/
namespace EHMX.ConditionalOperationsRegression
open TypeClasses TypeClasses.Regression

def operation : OpDecl :=
  { kinds := [0], input := .bound 0, output := .bound 0,
    condition := classAtom 0 (.bound 0) }
def operations : OpSignature := fun op => if op = 0 then some operation else none

theorem operationsWF : operations.WF (signature exampleEnv) := by
  intro op d hd
  simp only [operations] at hd
  split at hd
  · cases hd
    exact ⟨by simp [operation, signature], .bound rfl (by simp [signature]),
      .bound rfl (by simp [signature]), (by simp [operation, Ty.fv]), (by simp [operation, Ty.fv]),
      classWF (by simp [exampleEnv]) (.bound rfl (by simp [signature])), rfl, by simp [operation, classAtom, Constraint.fv, Ty.fv]⟩
  · cases hd

private theorem monoVariable (hC : C.WF (signature exampleEnv) Δ 0) (hf : C.fpi = ∅)
    (hΓ : Γ.WF (signature exampleEnv) Δ) (hT : T.HasKind (signature exampleEnv) Δ 0)
    (hl : Γ.lookup x = some (.mono T)) (hs : (Expr.ident x).Scoped Γ) :
    Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ (.ident x) T .empty :=
  .var ⟨hC, hf, hΓ, hs, hT, emptyKind (fixedFramework exampleEnv).signature⟩ hl
    (monoInstance (fixedFramework exampleEnv) hT)

/-- Normalize just the application effects; no inference theorem is used. -/
private theorem application (hf : Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ
      f (.arrow A .empty B) εf)
    (hx : Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ x A εx)
    (he : Entails (signature exampleEnv) (model exampleEnv) Δ C
      (.le 1 (.union (.union εf εx) .empty) ε))
    (hε : ε.HasKind (signature exampleEnv) Δ 1) :
    Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ (.app f x) B ε := by
  have hwf := typingWF hf
  have hwx := typingWF hx
  have hB := (arrowKinds hwf.2.2.2.2.1).2.2
  have hs : (Expr.app f x).Scoped Γ :=
    ⟨⟨hwf.2.2.2.1.1, hwx.2.2.2.1.1⟩, Finset.union_subset hwf.2.2.2.1.2 hwx.2.2.2.1.2⟩
  have ht := Typing.app ⟨hwf.1, hwf.2.1, hwf.2.2.1, hs, hB,
    unionKind (unionKind hwf.2.2.2.2.2 hwx.2.2.2.2.2) (emptyKind (fixedFramework exampleEnv).signature)⟩ hf hx
  exact .sub ⟨hwf.1, hwf.2.1, hwf.2.2.1, hs, hB, hε⟩ ht
    (leRefl (fixedFramework exampleEnv) (by simp [signature]) hB) he

private theorem pureApplication (hf : Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ
      f (.arrow A .empty B) .empty)
    (hx : Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ x A .empty) :
    Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ (.app f x) B .empty := by
  apply application hf hx _ (emptyKind (fixedFramework exampleEnv).signature)
  intro ρ bs ι _ _ _ _
  simp [Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.empty, Ty.eval,
    constructor, kind, below]


private theorem methodAt (hC : C.WF (signature exampleEnv) Δ 0) (hf : C.fpi = ∅)
    (hΓ : Γ.WF (signature exampleEnv) Δ) (hA : A.HasKind (signature exampleEnv) Δ 0)
    (hl : Γ.lookup (.free 0) = some eqScheme) (hs : (Expr.ident (.free 0)).Scoped Γ)
    (hp : Entails (signature exampleEnv) (model exampleEnv) Δ C (classAtom 0 A)) :
    Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ
      (.ident (.free 0)) (eqType A) .empty :=
  .var ⟨hC, hf, hΓ, hs, eqTypeKind hA, emptyKind (fixedFramework exampleEnv).signature⟩ hl
    (entailsTrans hp (methodInstance hA))

/-- Input, output and condition are instantiated with exactly [A]. -/
theorem performAt (hA : A.HasKind (signature exampleEnv) Δ 0)
    (ht : Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ arg A ε)
    (hp : Entails (signature exampleEnv) (model exampleEnv) Δ C (classAtom 0 A)) :
    Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ (.perform 0 arg) A
      (.union (.singleton 0) ε) := by
  have hw := typingWF ht
  have hi : operation.input.openAt 0 [A] = A := by simp [operation, Ty.openAt]
  have ho : operation.output.openAt 0 [A] = A := hi
  have hh := Typing.perform (sig := operations) (op := 0) (decl := operation) (args := [A])
    (show JudgmentWF (signature exampleEnv) Δ C Γ (.perform 0 arg)
      (operation.output.openAt 0 [A]) (.union (.singleton 0) ε) from
      ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, ho.symm ▸ hA,
        unionKind (singletonKind 0) hw.2.2.2.2.2⟩)
    (by simp [operations]) (.cons hA .nil)
    (by simpa [operation, classAtom, Constraint.substBound, Ty.substBound, BoundSubst.many] using hp)
    (by rw [hi]; exact ht)
  simpa only [ho] using hh

def checkingClause : Expr :=
  .letE (.app (.app (.ident (.free 0)) (.ident (.bound 1))) (.ident (.bound 1)))
    (.app (.ident (.bound 1)) (.ident (.bound 2)))

/-- The outer constraint is truth: Eq β comes solely from the declaration. -/
theorem clauseFromCondition {Γ : Env} (hΓ : Γ.WF (signature exampleEnv) Δ)
    (hl : Γ.lookup (.free 0) = some eqScheme) (hscope : 0 ∈ Γ.dpi)
    (hA : A.HasKind (signature exampleEnv) Δ 0) (hB : B.HasKind (signature exampleEnv) Δ 0) :
    Typing (signature exampleEnv) (model exampleEnv) operations Δ (.conj .truth (classAtom 0 A))
      ((Γ.push (.mono A)).push (.mono (.arrow A .empty B))) checkingClause B .empty := by
  let C := Constraint.conj .truth (classAtom 0 A)
  let G := (Γ.push (.mono A)).push (.mono (.arrow A .empty B))
  have hc : C.WF (signature exampleEnv) Δ 0 := ⟨trivial, classWF (by simp [exampleEnv]) hA⟩
  have hcf : C.fpi = ∅ := rfl
  have hk := arrowKind hA (emptyKind (fixedFramework exampleEnv).signature) hB
  have hg : G.WF (signature exampleEnv) Δ := envPushMonoWF (envPushMonoWF hΓ hA) hk
  have hm := methodAt hc hcf hg hA hl (by
    simpa [Expr.Scoped, Expr.LCAt, Expr.fv, G, Env.push, Env.dpi] using hscope)
    (fun _ _ _ _ _ _ h => h.2)
  have hz := monoVariable hc hcf hg hA (x := .bound 1) rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, G, Env.push])
  have hr := pureApplication (pureApplication hm hz) hz
  have hgb := envPushMonoWF hg boolKind
  have hk' := monoVariable hc hcf hgb hk (x := .bound 1) rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, G, Env.push])
  have hz' := monoVariable hc hcf hgb hA (x := .bound 2) rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, G, Env.push])
  have hb := pureApplication hk' hz'
  have ht := Typing.letMono ⟨hc, hcf, hg,
    scopedLet (typingWF hr).2.2.2.1 (typingWF hb).2.2.2.1, hB,
    unionKind (emptyKind (fixedFramework exampleEnv).signature) (emptyKind (fixedFramework exampleEnv).signature)⟩ hr hb
  exact .sub ⟨hc, hcf, hg, (typingWF ht).2.2.2.1, hB, emptyKind (fixedFramework exampleEnv).signature⟩ ht
    (leRefl (fixedFramework exampleEnv) (by simp [signature]) hB) (by
      intro ρ bs ι _ _ _ _
      simp [Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.empty, Ty.eval, constructor, kind, below])

def handledMethod : Expr :=
  .handle (.app (.app (.ident (.free 0)) (.perform 0 (.ident (.bound 1)))) (.ident (.bound 0)))
    0 (.ident (.bound 0)) checkingClause
theorem handledMethodWithCall
    (hp : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint argumentEnv
      (.perform 0 (.ident (.bound 1))) alpha (.union (.singleton 0) .empty)) : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint
    argumentEnv handledMethod boolTy .empty := by
  have hem := emptyKind (Δ := []) (fixedFramework exampleEnv).signature
  have hop := singletonKind (S := signature exampleEnv) (Δ := []) 0
  have hΓ := argumentEnvWF (Δ := [])
  have hm := methodAt eqConstraintWF rfl hΓ alphaKind rfl
    (by simp [argumentEnv, initialEnv, Env.push, Env.dpi, Expr.Scoped, Expr.LCAt, Expr.fv]) entailsRefl
  have hy := monoVariable eqConstraintWF rfl hΓ alphaKind (x := .bound 0) rfl
    (by simp [argumentEnv, initialEnv, Env.push, Expr.Scoped, Expr.LCAt, Expr.fv])
  have ha : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint argumentEnv
      (.app (.ident (.free 0)) (.perform 0 (.ident (.bound 1))))
      (.arrow alpha .empty boolTy) (.singleton 0) := by
    apply application hm hp _ hop
    intro ρ bs ι _ _ _ _
    simp [Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.empty, Ty.singleton,
      Ty.eval, constructor, kind, below]
  have hb : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint argumentEnv
      (.app (.app (.ident (.free 0)) (.perform 0 (.ident (.bound 1)))) (.ident (.bound 0)))
      boolTy (.singleton 0) := by
    apply application ha hy _ hop
    intro ρ bs ι _ _ _ _
    simp [Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.empty, Ty.singleton,
      Ty.eval, constructor, kind, below]
  apply Typing.handle (decl := operation) (A := boolTy) (εin := .singleton 0)
  · exact ⟨eqConstraintWF, rfl, hΓ, by
      simp [argumentEnv, initialEnv, Env.push, Env.dpi, Expr.Scoped, Expr.LCAt, Expr.fv, checkingClause],
      boolKind, hem⟩
  · simp [operations]
  · exact hb
  · intro ρ bs ι _ _ _ _
    simp [Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.empty, Ty.singleton,
      Ty.eval, constructor, kind, below]
  · exact monoVariable eqConstraintWF rfl (envPushMonoWF hΓ boolKind) boolKind (x := .bound 0) rfl
      (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push])
  · have hc := clauseFromCondition (envShiftWF hΓ [0])
      (by simp [argumentEnv, initialEnv, Env.shift, Env.push, Env.lookup, eqScheme,
        Scheme.shift, Constraint.shift, classAtom, eqType, boolTy, Ty.shift, Ty.arrow, Ty.empty])
      (by simp [argumentEnv, initialEnv, Env.shift, Env.push, Env.dpi])
      (Ty.HasKind.bound (i := 0) rfl (by simp [signature])) (boolKind (Δ := [0]))
    have hc' := typingConjStronger hc (constraintShiftWF (eqConstraintWF (Δ := []) (n := 0)) [0])
      rfl (fun _ _ _ _ _ _ _ => trivial)
    simpa [operation, Ty.shift, Ty.empty, boolTy] using hc'

theorem handledMethodTyping : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint
    argumentEnv handledMethod boolTy .empty := by
  apply handledMethodWithCall
  exact performAt alphaKind (monoVariable eqConstraintWF rfl argumentEnvWF alphaKind (x := .bound 1) rfl
    (by simp [argumentEnv, initialEnv, Env.push, Expr.Scoped, Expr.LCAt, Expr.fv])) entailsRefl

/-- Each component invokes a public specialization, retaining the independent derivation. -/
private theorem inferenceGuarantees
    (ht : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint Γ e T .empty)
    (hf : Entails (signature exampleEnv) (model exampleEnv) [] eqConstraint Γ.exists_) :
    Typing (signature exampleEnv) (model exampleEnv) operations [] (infer operations Γ e T .empty) Γ e T .empty ∧
    Entails (signature exampleEnv) (model exampleEnv) [] eqConstraint (infer operations Γ e T .empty) ∧
    PrincipalConstraint (signature exampleEnv) (model exampleEnv) operations [] Γ e T .empty
      (infer operations Γ e T .empty) := by
  have hw := typingWF ht
  exact ⟨TypeClasses.inferenceSoundness exampleEnv operations operationsWF _ _ _ _ _ (by simp)
      hw.2.2.1 hw.2.2.2.1 (typingDeclared ht) hw.2.2.2.2.1 hw.2.2.2.2.2,
    TypeClasses.inferenceCompleteness exampleEnv operations operationsWF _ _ _ _ _ _ (by simp) hf ht,
    TypeClasses.constraintGenerationPrincipality exampleEnv operations operationsWF _ _ _ _ _ (by simp)
      hw.2.2.1 hw.2.2.2.1 (typingDeclared ht) hw.2.2.2.2.1 hw.2.2.2.2.2⟩


theorem handledMethodInferenceSoundness :
    Typing (signature exampleEnv) (model exampleEnv) operations []
      (infer operations argumentEnv handledMethod boolTy .empty) argumentEnv handledMethod boolTy .empty :=
  (inferenceGuarantees handledMethodTyping argumentEnvRealizable).1

theorem handledMethodInferenceCompleteness :
    Entails (signature exampleEnv) (model exampleEnv) [] eqConstraint
      (infer operations argumentEnv handledMethod boolTy .empty) :=
  (inferenceGuarantees handledMethodTyping argumentEnvRealizable).2.1

theorem handledMethodPrincipalConstraint :
    PrincipalConstraint (signature exampleEnv) (model exampleEnv) operations [] argumentEnv handledMethod boolTy .empty
      (infer operations argumentEnv handledMethod boolTy .empty) :=
  (inferenceGuarantees handledMethodTyping argumentEnvRealizable).2.2

private theorem generatedSatisfiable
    (ht : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint Γ e T .empty)
    (hc : Entails (signature exampleEnv) (model exampleEnv) [] eqConstraint (infer operations Γ e T .empty)) :
    Satisfiable (signature exampleEnv) (model exampleEnv) [] (infer operations Γ e T .empty) := by
  obtain ⟨_, ρ, bs, ι, hρ, hbs, hι, h⟩ := eqConstraintSatisfiable
  have hw := typingWF ht
  exact ⟨inferWF (fixedFramework exampleEnv).signature operationsWF hw.2.2.1 hw.2.2.2.1
    hw.2.2.2.2.1 hw.2.2.2.2.2, ρ, bs, ι, hρ, hbs, hι, hc ρ bs ι hρ hbs hι h⟩

theorem handledMethodGeneratedSatisfiable : Satisfiable (signature exampleEnv) (model exampleEnv) []
    (infer operations argumentEnv handledMethod boolTy .empty) :=
  generatedSatisfiable handledMethodTyping handledMethodInferenceCompleteness

def intTy : Ty := .con (.other 1) []
def listTy (A : Ty) : Ty := .con (.other 3) [A]

theorem intKind : intTy.HasKind (signature exampleEnv) Δ 0 :=
  .con (by change 0 < 1 ∧ 1 < 4; decide) .nil

theorem listKind (hA : A.HasKind (signature exampleEnv) Δ 0) :
    (listTy A).HasKind (signature exampleEnv) Δ 0 :=
  .con (by change 0 < 3 ∧ 3 < 4; decide) (.cons hA .nil)

private theorem callVariable (hC : C.WF (signature exampleEnv) Δ 0) (hf : C.fpi = ∅)
    (hA : A.HasKind (signature exampleEnv) Δ 0)
    (hp : Entails (signature exampleEnv) (model exampleEnv) Δ C (classAtom 0 A)) :
    Typing (signature exampleEnv) (model exampleEnv) operations Δ C
      (({} : Env).push (.mono A)) (.perform 0 (.ident (.bound 0))) A (.union (.singleton 0) .empty) := by
  exact performAt hA (monoVariable hC hf (envPushMonoWF (by simp [Env.WF]) hA) hA rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push])) hp

theorem intCall : Typing (signature exampleEnv) (model exampleEnv) operations [] .truth
    (({} : Env).push (.mono intTy)) (.perform 0 (.ident (.bound 0))) intTy (.union (.singleton 0) .empty) := by
  apply callVariable (C := .truth) trivial rfl intKind
  intro ρ bs ι _ _ _ _
  exact (classAtomMeaning exampleEnv 0 intTy ρ bs ι).mpr ⟨.int, by simp [intTy, Ty.eval, constructor, construct], eqInt⟩

theorem boolCall : Typing (signature exampleEnv) (model exampleEnv) operations [] .truth
    (({} : Env).push (.mono boolTy)) (.perform 0 (.ident (.bound 0))) boolTy (.union (.singleton 0) .empty) := by
  apply callVariable (C := .truth) trivial rfl boolKind
  intro ρ bs ι _ _ _ _
  exact (classAtomMeaning exampleEnv 0 boolTy ρ bs ι).mpr ⟨.bool, by simp [boolTy, Ty.eval, constructor, construct], eqBool⟩

theorem conditionalListCall : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint
    (({} : Env).push (.mono (listTy alpha))) (.perform 0 (.ident (.bound 0)))
    (listTy alpha) (.union (.singleton 0) .empty) :=
  callVariable eqConstraintWF rfl (listKind alphaKind) (eqEntailsList alphaKind)

theorem ordCall : Typing (signature exampleEnv) (model exampleEnv) operations [] (classAtom 1 alpha)
    (({} : Env).push (.mono alpha)) (.perform 0 (.ident (.bound 0))) alpha (.union (.singleton 0) .empty) :=
  callVariable (classWF (by simp [exampleEnv]) alphaKind) rfl alphaKind (ordEntailsEq alpha)

/-- This is the actual evaluation context of eq (perform op x) y. -/
def callContext : EvalCtx :=
  .appFun (.appArg (.ident (.free 0)) rfl .hole) (.ident (.bound 0))
def captured : Expr := checkingClause.openAt 0
  [Expr.resume callContext 0 (.ident (.bound 0)) checkingClause, .ident (.bound 1)]

theorem captureStep : Step handledMethod captured :=
  .operation (E := callContext) (v := .ident (.bound 1)) rfl (by simp [callContext, EvalCtx.handled])

theorem capturePreserved : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint
    argumentEnv captured boolTy .empty :=
  preservation _ _ _ ⟨⟨fixedFramework exampleEnv, operationsWF⟩, fixedArrowSeparated exampleEnv⟩
    _ _ _ _ _ _ _ handledMethodTyping captureStep

/-- Existential and strengthening rules remain above an actual conditioned capture. -/
theorem existentialCapturePreserved :
    Typing (signature exampleEnv) (model exampleEnv) operations [] (.exists_ [0] (eqConstraint.shift 1 0))
      argumentEnv captured boolTy .empty := by
  have ht := typingShift (fixedFramework exampleEnv) operationsWF handledMethodTyping [0]
  have hs := typingStronger ht (typingWF ht).1 (typingWF ht).2.1 entailsRefl
  have he : Typing (signature exampleEnv) (model exampleEnv) operations []
      (.exists_ [0] (eqConstraint.shift 1 0)) argumentEnv handledMethod boolTy .empty :=
    .exists_ ⟨⟨by simp [signature], (typingWF hs).1⟩,
      by simpa only [Constraint.fpi, constraintShiftFpi] using (typingWF handledMethodTyping).2.1,
      (typingWF handledMethodTyping).2.2⟩ hs
  exact preservation _ _ _ ⟨⟨fixedFramework exampleEnv, operationsWF⟩, fixedArrowSeparated exampleEnv⟩
    _ _ _ _ _ _ _ he captureStep

/-- The whole ordinary Constraint language is available, including local definitions. -/
def mixedCondition : Constraint :=
  .conj (.exists_ [0] (.eq 0 (.bound 0) (.bound 1)))
    (.forall_ [1] (.def_ (.all [0] (.eq 0 (.bound 0) (.bound 2)) (.bound 0))
      (.inst (.bound 0) (.bound 1))))
def mixedOperation : OpDecl :=
  { kinds := [0,1], input := .arrow (.bound 0) (.bound 1) (.bound 0),
    output := .bound 0, condition := mixedCondition }

theorem mixedConditionWF : mixedCondition.WF (signature exampleEnv) [0,1] 0 := by
  have h0 : 0 ∈ (signature exampleEnv).kinds := by simp [signature]
  have h1 : 1 ∈ (signature exampleEnv).kinds := by simp [signature]
  exact ⟨⟨by simp [h0], ⟨h0, .cons (.bound rfl h0) (.cons (.bound rfl h0) .nil)⟩⟩,
    ⟨by simp [h1], ⟨by simp [h0], ⟨h0, .cons (.bound rfl h0) (.cons (.bound rfl h0) .nil)⟩, .bound rfl h0⟩,
      .bound rfl h0, by decide⟩⟩

theorem mixedOperationWF : OpSignature.WF (signature exampleEnv) (fun _ => some mixedOperation) := by
  intro op d hd
  cases hd
  have h0 : 0 ∈ (signature exampleEnv).kinds := by simp [signature]
  have h1 : 1 ∈ (signature exampleEnv).kinds := by simp [signature]
  exact ⟨by simp [mixedOperation, h0, h1], arrowKind (.bound rfl h0) (.bound rfl h1) (.bound rfl h0),
    .bound rfl h0, by simp [mixedOperation, Ty.arrow, Ty.fv], by simp [mixedOperation, Ty.fv],
    mixedConditionWF, rfl, by simp [mixedOperation, mixedCondition, Constraint.fv, Scheme.fv, Constraint.eq, Ty.fv]⟩

theorem mixedConditionInstantiation :
    mixedCondition.substBound (BoundSubst.many [alpha, .singleton 7]) =
      .conj (.exists_ [0] (.eq 0 (.bound 0) alpha))
        (.forall_ [1] (.def_ (.all [0] (.eq 0 (.bound 0) alpha) (.bound 0))
          (.inst (.bound 0) alpha))) := by
  simp [mixedCondition, Constraint.substBound, Scheme.substBound, Constraint.eq,
    Ty.substBound, BoundSubst.lift, BoundSubst.many, alpha, Ty.shift]

theorem mixedConditionOuterShift : mixedCondition.shift 3 2 = mixedCondition := by
  rw [shiftSubstBound.1]
  exact (substBoundCongruence.1 _ _ _ mixedConditionWF _ Ty.bound
    (fun i hi => by have hi' : i < 2 := hi; simp [hi'])).trans (substBoundId.1 _)

def localFreeCondition : Constraint := .defFree 7 (.mono (.bound 0)) (.inst (.free 7) (.bound 0))

theorem localFreeConditionClosed : localFreeCondition.WF (signature exampleEnv) [0] 0 ∧
    localFreeCondition.fpi = ∅ ∧ localFreeCondition.fv = ∅ := by
  exact ⟨⟨⟨by simp, trivial, .bound rfl (by simp [signature])⟩,
    .bound rfl (by simp [signature]), trivial⟩,
    by simp [localFreeCondition, Constraint.fpi, Scheme.mono, Scheme.fpi],
    by simp [localFreeCondition, Constraint.fv, Scheme.mono, Scheme.fv, Ty.fv]⟩

def withCondition (P : Constraint) : OpDecl := { operation with condition := P }
def conditionSignature (P : Constraint) : OpSignature := fun _ => some (withCondition P)

theorem conditionSignatureWF (hw : P.WF (signature exampleEnv) [0] 0)
    (hf : P.fpi = ∅) (hfv : P.fv = ∅) : (conditionSignature P).WF (signature exampleEnv) := by
  intro op d hd
  cases hd
  exact ⟨by simp [withCondition, operation, signature], .bound rfl (by simp [signature]),
    .bound rfl (by simp [signature]), by simp [withCondition, operation, Ty.fv],
    by simp [withCondition, operation, Ty.fv], hw, hf, hfv⟩

theorem falseDeclarationWF : (conditionSignature .falsity).WF (signature exampleEnv) :=
  conditionSignatureWF trivial rfl rfl

theorem falseCallUnsatisfiable : ¬ Satisfiable (signature exampleEnv) (model exampleEnv) Δ
    (generate (conditionSignature .falsity) (.perform 0 arg) T ε) := by
  rintro ⟨_, ρ, bs, ι, _, _, _, vs, _, hp, _⟩
  exact hp

theorem missingClassCallUnsatisfiable : ¬ Satisfiable (signature exampleEnv) (model exampleEnv) Δ
    (generate (conditionSignature (classAtom 2 (.bound 0))) (.perform 0 arg) T ε) := by
  rintro ⟨_, ρ, bs, ι, _, _, _, vs, _, hp, _⟩
  obtain ⟨v, _, hm⟩ := (classAtomMeaning exampleEnv 2 (.bound 0) ρ (vs ++ bs) ι).mp hp
  exact emptyClass v hm

theorem falseClauseVacuous (ρ : Assignment (model exampleEnv)) bs ι (D : Constraint) :
    (Constraint.forall_ [0] (.implies .falsity D)).Holds (model exampleEnv) ρ bs ι :=
  fun _ _ h => False.elim h

/-- The ambient term environment is still required when an implication is vacuous. -/
theorem falseConditionKeepsEnvironment (Γ : Env) (D : Constraint)
    (ρ : Assignment (model exampleEnv)) bs ι :
    (Γ.letIn (.implies .falsity D)).Holds (model exampleEnv) ρ bs ι ↔
      Γ.exists_.Holds (model exampleEnv) ρ bs ι := by
  rw [envLetInHolds]
  simp [Constraint.Holds]

theorem rejectFreeTypeCondition : ¬ (conditionSignature (.eq 0 (.free (0,0)) (.bound 0))).WF
    (signature exampleEnv) := by
  intro h
  have hf := (h 0 _ rfl).2.2.2.2.2.2.2
  simp [withCondition, Constraint.fv, Constraint.eq, Ty.fv] at hf

theorem rejectFreeEffectCondition : ¬ (conditionSignature (.eq 1 (.free (1,0)) .empty)).WF
    (signature exampleEnv) := by
  intro h
  have hf := (h 0 _ rfl).2.2.2.2.2.2.2
  simp [withCondition, Constraint.fv, Constraint.eq, Ty.fv, Ty.empty] at hf

theorem rejectFreeTermCondition : ¬ (conditionSignature (.inst (.free 9) (.bound 0))).WF
    (signature exampleEnv) := by
  intro h
  have hf := (h 0 _ rfl).2.2.2.2.2.2.1
  simp [withCondition, Constraint.fpi] at hf

theorem rejectOuterTermCondition : ¬ (conditionSignature (.inst (.bound 0) (.bound 0))).WF
    (signature exampleEnv) := by
  intro h
  exact Nat.not_lt_zero 0 (h 0 _ rfl).2.2.2.2.2.1.2

theorem rejectOutOfScopeCondition : ¬ (conditionSignature (classAtom 0 (.bound 1))).WF
    (signature exampleEnv) := by
  intro h
  have ht := (h 0 _ rfl).2.2.2.2.2.1.2
  cases ht with
  | cons hk _ => cases hk with | bound hi _ => cases hi

theorem rejectKindMismatchCondition : ¬ (conditionSignature (classAtom 0 .empty)).WF
    (signature exampleEnv) := by
  intro h
  have ht := (h 0 _ rfl).2.2.2.2.2.1.2
  cases ht with
  | cons hk _ => cases hk

/-- Even a locally bound outer term variable is forbidden in an antecedent. -/
theorem rejectDependentImplication : ¬ (Constraint.implies (.inst (.bound 0) intTy) .truth).WF
    (signature exampleEnv) [] 1 := fun h => Nat.not_lt_zero 0 h.1.2

/-- A false declaration is legal, and its clause may use its false assumption. -/
theorem falseHandlerTyping :
    Typing (signature exampleEnv) (model exampleEnv) (conditionSignature .falsity) [] .truth
      (({} : Env).push (.mono intTy))
      (.handle (.ident (.bound 0)) 0 (.ident (.bound 0)) (.ident (.bound 1))) intTy .empty := by
  let G := ({} : Env).push (.mono intTy)
  have hg : G.WF (signature exampleEnv) [] := envPushMonoWF (by simp [Env.WF]) intKind
  have hx : Typing (signature exampleEnv) (model exampleEnv) (conditionSignature .falsity) [] .truth
      G (.ident (.bound 0)) intTy .empty :=
    .var ⟨trivial, rfl, hg, by simp [G, Expr.Scoped, Expr.LCAt, Expr.fv, Env.push],
      intKind, emptyKind (fixedFramework exampleEnv).signature⟩ rfl (monoInstance (fixedFramework exampleEnv) intKind)
  apply Typing.handle (decl := withCondition .falsity) (A := intTy) (εin := .empty)
  · exact ⟨trivial, rfl, hg, by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push],
      intKind, emptyKind (fixedFramework exampleEnv).signature⟩
  · rfl
  · exact hx
  · exact effectEmptyBelow (fixedFramework exampleEnv)
      (unionKind (singletonKind 0) (emptyKind (fixedFramework exampleEnv).signature))
  · exact .var ⟨trivial, rfl, envPushMonoWF hg intKind,
      by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push], intKind,
      emptyKind (fixedFramework exampleEnv).signature⟩ rfl (monoInstance (fixedFramework exampleEnv) intKind)
  · have hb : Ty.HasKind (signature exampleEnv) [0] (.bound 0) 0 := .bound rfl (by simp [signature])
    have henv := envPushMonoWF (envPushMonoWF (envShiftWF hg [0]) hb)
      (arrowKind hb (emptyKind (fixedFramework exampleEnv).signature) (intKind (Δ := [0])))
    simp only [withCondition, operation, List.length_cons, List.length_nil, Nat.reduceAdd,
      Constraint.shift, intTy, Ty.empty, Ty.shift, List.map_nil]
    apply Typing.var
    · exact ⟨⟨trivial, trivial⟩, rfl, by
        simpa [G, withCondition, operation, Ty.shift, Ty.empty, intTy] using henv,
        by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push],
        by simpa [withCondition, operation, intTy, Ty.shift] using (intKind (Δ := [0])),
        emptyKind (fixedFramework exampleEnv).signature⟩
    · rfl
    · intro ρ bs ι _ _ _ h
      exact False.elim h.2

/-- Non-derivability explicitly assumes a satisfiable outer constraint and feasible environment. -/
theorem falseCallNotTypable (hC : Satisfiable (signature exampleEnv) (model exampleEnv) [] C)
    (hΓ : Entails (signature exampleEnv) (model exampleEnv) [] C Γ.exists_) :
    ¬ Typing (signature exampleEnv) (model exampleEnv) (conditionSignature .falsity) [] C Γ
      (.perform 0 arg) T ε := by
  intro ht
  have hc := EHMX.inferenceCompleteness _ _ _ ⟨fixedFramework exampleEnv, falseDeclarationWF⟩
    _ _ _ _ _ _ (by simp) hΓ ht
  obtain ⟨_, ρ, bs, ι, hρ, hbs, hι, hh⟩ := hC
  have hg := ((envLetInHolds _ _ _ _ _).mp (hc ρ bs ι hρ hbs hι hh)).2
  obtain ⟨_, _, hp, _⟩ := hg
  exact hp

/-- Truth conditions recover the old perform generation formula. -/
theorem truthPerformGeneration (hs : sig op = some decl) (hp : decl.condition = .truth)
    (ρ : Assignment M) bs ι :
    (generate sig (.perform op arg) T ε).Holds M ρ bs ι ↔
    (Constraint.exists_ (decl.kinds ++ [1]) (.conj
      (generate sig arg decl.input (.bound decl.kinds.length))
      (resultConstraint decl.output (T.shift (decl.kinds.length + 1) 0)
        (.union (.singleton op) (.bound decl.kinds.length)) (ε.shift (decl.kinds.length + 1) 0)))).Holds M ρ bs ι := by
  simp [generate, hs, hp, Constraint.Holds]

/-- In a truth-conditioned handler the universal clause has the former meaning. -/
theorem truthHandlerGeneration (hs : sig op = some decl) (hp : decl.condition = .truth)
    (ρ : Assignment M) bs ι :
    (generate sig (.handle body op ret clause) T ε).Holds M ρ bs ι ↔
    (Constraint.exists_ [0,1,0,1] (.conj (generate sig body (.bound 0) (.bound 1))
      (.conj (.le 1 (.bound 1) (.union (.singleton op) (.bound 3)))
      (.conj (.def_ (.mono (.bound 0)) (generate sig ret (.bound 2) (.bound 3)))
      (.conj (.forall_ decl.kinds (.def_ (.mono decl.input)
        (.def_ (.mono (.arrow decl.output ((Ty.bound 3).shift decl.kinds.length 0)
          ((Ty.bound 2).shift decl.kinds.length 0)))
          (generate sig clause ((Ty.bound 2).shift decl.kinds.length 0)
            ((Ty.bound 3).shift decl.kinds.length 0)))))
        (resultConstraint (.bound 2) (T.shift 4 0) (.bound 3) (ε.shift 4 0))))))).Holds M ρ bs ι := by
  simp [generate, hs, hp, Constraint.Holds]

/-- Removing or adding a truth conjunct preserves the whole typing derivation. -/
theorem typingTruthConditionIff :
    Typing S M sig Δ (.conj C .truth) Γ e T ε ↔ Typing S M sig Δ C Γ e T ε := by
  constructor
  · intro h
    have hw := typingWF h
    exact .strengthen ⟨hw.1.1, by simpa only [Constraint.fpi, Finset.union_empty] using hw.2.1,
      hw.2.2⟩ h (fun _ _ _ _ _ _ hc => ⟨hc, trivial⟩)
  · exact Typing.withConjTruth

/-- The operation's actual type argument is the existentially bound variable.
Its Eq proof stays inside that scope, through strengthen and sub. -/
theorem existentialCall :
    Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint argumentEnv
      (.perform 0 (.ident (.bound 1))) alpha (.union (.singleton 0) .empty) := by
  let F := fixedFramework exampleEnv
  let K : Constraint := .conj (eqConstraint.shift 1 0) (.eq 0 (.bound 0) alpha)
  have hβ : Ty.HasKind (signature exampleEnv) [0] (.bound 0) 0 := .bound rfl (by simp [signature])
  have hwK : K.WF (signature exampleEnv) [0] 0 :=
    ⟨constraintShiftWF (eqConstraintWF (Δ := []) (n := 0)) [0],
      ⟨by simp [Predicate.WF, signature], .cons hβ (.cons alphaKind .nil)⟩⟩
  have hfK : K.fpi = ∅ := rfl
  have hx : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint argumentEnv
      (.ident (.bound 1)) alpha .empty :=
    monoVariable eqConstraintWF rfl argumentEnvWF alphaKind rfl
      (by simp [argumentEnv, initialEnv, Env.push, Expr.Scoped, Expr.LCAt, Expr.fv])
  have hx' := typingShift F operationsWF hx [0]
  have hxK := typingStronger hx' hwK hfK (fun _ _ _ _ _ _ h => h.1)
  have hto : Entails (signature exampleEnv) (model exampleEnv) [0] K (.le 0 alpha (.bound 0)) := by
    intro ρ bs ι _ _ _ h
    have hh : (Constraint.eq 0 (.bound 0) alpha).Holds (model exampleEnv) ρ bs ι := h.2
    change _ ∧ _ ∧ _ at hh ⊢
    rw [hh.2.2]
    exact ⟨hh.2.1, hh.2.1, F.belowRefl 0 (by simp [signature]) _ hh.2.1⟩
  have hfrom : Entails (signature exampleEnv) (model exampleEnv) [0] K (.le 0 (.bound 0) alpha) := by
    intro ρ bs ι _ _ _ h
    have hh : (Constraint.eq 0 (.bound 0) alpha).Holds (model exampleEnv) ρ bs ι := h.2
    change _ ∧ _ ∧ _ at hh ⊢
    rw [hh.2.2]
    exact ⟨hh.2.1, hh.2.1, F.belowRefl 0 (by simp [signature]) _ hh.2.1⟩
  have harg : Typing (signature exampleEnv) (model exampleEnv) operations [0] K (argumentEnv.shift 1)
      (.ident (.bound 1)) (.bound 0) .empty := by
    apply Typing.sub ⟨hwK, hfK, (typingWF hxK).2.2.1, (typingWF hxK).2.2.2.1, hβ,
      emptyKind F.signature⟩ hxK
    · simpa [alpha, Ty.shift] using hto
    · simpa [Ty.empty, Ty.shift] using
        (leRefl (Δ := [0]) (C := K) F F.signature.2.1 (emptyKind F.signature))
  have hp : Entails (signature exampleEnv) (model exampleEnv) [0] K (classAtom 0 (.bound 0)) := by
    intro ρ bs ι _ _ _ h
    have heq : (Ty.bound 0).eval (model exampleEnv) ρ bs = alpha.eval (model exampleEnv) ρ bs := h.2.2.2
    have ha : (classAtom 0 alpha).Holds (model exampleEnv) ρ bs ι := by
      simpa [eqConstraint, Constraint.shift, classAtom, alpha, Ty.shift] using h.1
    obtain ⟨v, hv, hm⟩ := (classAtomMeaning exampleEnv 0 alpha ρ bs ι).mp ha
    exact (classAtomMeaning exampleEnv 0 (.bound 0) ρ bs ι).mpr ⟨v, heq.trans hv, hm⟩
  have hop := performAt hβ harg hp
  have hop' : Typing (signature exampleEnv) (model exampleEnv) operations [0] K (argumentEnv.shift 1)
      (.perform 0 (.ident (.bound 1))) alpha (.union (.singleton 0) .empty) :=
    .sub ⟨hwK, hfK, (typingWF hop).2.2.1, (typingWF hop).2.2.2.1, alphaKind,
      (typingWF hop).2.2.2.2.2⟩ hop hfrom (leRefl F F.signature.2.1 (typingWF hop).2.2.2.2.2)
  have hex : Typing (signature exampleEnv) (model exampleEnv) operations [] (.exists_ [0] K)
      argumentEnv (.perform 0 (.ident (.bound 1))) alpha (.union (.singleton 0) .empty) := by
    apply Typing.exists_ (ks := [0]) (C := K) (e := .perform 0 (.ident (.bound 1)))
      ⟨⟨by simp [signature], hwK⟩, hfK, argumentEnvWF, by exact (typingWF hx).2.2.2.1,
      alphaKind, unionKind (singletonKind 0) (emptyKind F.signature)⟩
    simpa [alpha, Ty.shift, Ty.union, Ty.singleton, Ty.empty] using hop'
  apply typingStronger hex eqConstraintWF rfl
  intro ρ bs ι hρ hbs _ hc
  let vs := [alpha.eval (model exampleEnv) ρ bs]
  refine ⟨vs, .cons (evalKind F hρ hbs alphaKind) .nil, ?_, ?_⟩
  · exact (constraintShiftHolds (eqConstraintWF (Δ := []) (n := 0)) ρ bs vs ι).mpr hc
  · have hk := evalKind F hρ hbs (alphaKind (Δ := []))
    simpa [vs, Constraint.eq, Constraint.Holds, Predicate.eval, Ty.eval, alpha] using And.intro hk (And.intro hk (rfl : alpha.eval (model exampleEnv) ρ bs = alpha.eval (model exampleEnv) ρ bs))

theorem existentialArgumentCapturePreserved :
    Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint argumentEnv
      captured boolTy .empty :=
  preservation _ _ _ ⟨⟨fixedFramework exampleEnv, operationsWF⟩, fixedArrowSeparated exampleEnv⟩
    _ _ _ _ _ _ _ (handledMethodWithCall existentialCall) captureStep

end EHMX.ConditionalOperationsRegression
