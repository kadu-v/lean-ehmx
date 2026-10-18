import EHMX.Proofs.TypeClasses

namespace EHMX.TypeClasses.Regression

/-- Eq = 0, Ord = 1, Empty = 2. The six instances and superclass edge are data. -/
def exampleEnv : ClassEnv :=
  ⟨[], {0,1,2}, [(1,0)],
    [⟨0,1,[]⟩, ⟨0,2,[]⟩, ⟨0,3,[(0,0)]⟩,
     ⟨1,1,[]⟩, ⟨1,2,[]⟩, ⟨1,3,[(1,0)]⟩]⟩

theorem exampleEnvWF : exampleEnv.WF := by
  simp [HMX.TypeClasses.ClassEnv.WF, HMX.TypeClasses.InstanceRule.WF, exampleEnv, HMX.TypeClasses.arity]

theorem eqInt : Member exampleEnv 0 .int := by
  exact .instanceRule ⟨0,1,[]⟩ [] ∅ (by simp [exampleEnv]) rfl (by simp)

theorem eqBool : Member exampleEnv 0 .bool := by
  exact .instanceRule ⟨0,2,[]⟩ [] ∅ (by simp [exampleEnv]) rfl (by simp)

theorem ordInt : Member exampleEnv 1 .int := by
  exact .instanceRule ⟨1,1,[]⟩ [] ∅ (by simp [exampleEnv]) rfl (by simp)

theorem ordBool : Member exampleEnv 1 .bool := by
  exact .instanceRule ⟨1,2,[]⟩ [] ∅ (by simp [exampleEnv]) rfl (by simp)

theorem memberList (c : Nat) (hc : c = 0 ∨ c = 1) (v : GroundType exampleEnv.extraArities)
    (h : Member exampleEnv c v) : Member exampleEnv c (.list v) := by
  apply Member.instanceRule (E := exampleEnv) ⟨c,3,[(c,0)]⟩ [v] ∅
  · rcases hc with rfl | rfl <;> simp [exampleEnv]
  · rfl
  · simpa using h

theorem nestedListEq : Member exampleEnv 0 (.list (.list (.list .int))) :=
  memberList 0 (Or.inl rfl) _ (memberList 0 (Or.inl rfl) _ (memberList 0 (Or.inl rfl) _ eqInt))

theorem nestedListOrd : Member exampleEnv 1 (.list (.list .bool)) :=
  memberList 1 (Or.inr rfl) _ (memberList 1 (Or.inr rfl) _ ordBool)

/-- Inversion of the least derivation, including superclass steps. -/
theorem memberNotArrowTag (c : Nat) (v : GroundType exampleEnv.extraArities) (h : Member exampleEnv c v) : v.tag ≠ 0 := by
  induction h with
  | instanceRule r vs ε hr hl _ =>
    have hw := exampleEnvWF.2 r hr
    rw [constructTag _ _ _ _ hw.2.1 hl]
    simp only [exampleEnv, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  | superclass c d v _ _ ih => exact ih

theorem noEqArrow (ε : Finset Op) (a b : GroundType exampleEnv.extraArities) : ¬ Member exampleEnv 0 (.arrow a ε b) := by
  intro h
  exact memberNotArrowTag _ _ h rfl

theorem emptyClass (v : GroundType exampleEnv.extraArities) : ¬ Member exampleEnv 2 v := by
  suffices ∀ c v, Member exampleEnv c v → c ≠ 2 from fun h => this 2 v h rfl
  intro c v h
  induction h with
  | instanceRule r vs ε hr _ _ =>
    simp only [exampleEnv, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  | superclass c d v hr _ _ =>
    have : (c,d) = (1,0) := by simpa [exampleEnv] using hr
    cases this
    decide

theorem emptyClassNotSatisfiable (ks : List Kind) (T : Ty) :
    ¬ Satisfiable (signature exampleEnv) (model exampleEnv) Δ (.exists_ ks (classAtom 2 T)) := by
  rintro ⟨_, ρ, bs, ι, _, _, _, vs, _, h⟩
  obtain ⟨v, _, hm⟩ := (classAtomMeaning exampleEnv 2 T ρ (vs ++ bs) ι).mp h
  exact emptyClass v hm

def emptyEnv : ClassEnv := ⟨[], ∅, [], []⟩

theorem emptyEnvWF : emptyEnv.WF := by simp [HMX.TypeClasses.ClassEnv.WF, emptyEnv]

theorem emptyEnvFramework : EffectFramework (signature emptyEnv) (model emptyEnv) := fixedFramework emptyEnv

theorem emptyEnvNoMember (c : Nat) (v : GroundType emptyEnv.extraArities) : ¬ Member emptyEnv c v := by
  intro h
  cases h with
  | instanceRule r vs ε hr _ _ => simp [emptyEnv] at hr
  | superclass c d v hr _ => simp [emptyEnv] at hr

/-- Extra names 4 and 5 have arities zero and three. -/
def extraEnv : ClassEnv := ⟨[0,3], ∅, [], []⟩

theorem extraEnvFramework : EffectFramework (signature extraEnv) (model extraEnv) := fixedFramework extraEnv

theorem extraConstructorsSeparated :
    construct [0,3] ∅ 4 [] ≠ construct [0,3] ∅ 5 [.int,.bool,.list .int] := by
  intro h
  have ht := congrArg GroundType.tag h
  rw [constructTag _ _ _ _ (by decide) rfl, constructTag _ _ _ _ (by decide) rfl] at ht
  cases ht



/-- A separate declaration permits arrows at every latent effect. -/
def arrowEnv : ClassEnv := ⟨[], {0}, [], [⟨0,0,[(0,0),(0,1)]⟩, ⟨0,1,[]⟩]⟩

theorem arrowEnvWF : arrowEnv.WF := by
  simp [arrowEnv, HMX.TypeClasses.ClassEnv.WF, HMX.TypeClasses.InstanceRule.WF, HMX.TypeClasses.arity]
  intro a b h; rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide

theorem effectfulArrowMember (ε : Finset Op) : Member arrowEnv 0 (.arrow .int ε .int) := by
  have hi : Member arrowEnv 0 .int := .instanceRule ⟨0,1,[]⟩ [] ∅ (by simp [arrowEnv]) rfl (by simp)
  apply Member.instanceRule ⟨0,0,[(0,0),(0,1)]⟩ [.int,.int] ε (by simp [arrowEnv]) rfl
  simpa using And.intro hi hi

/-- Cycles alone do not create a derivation in the least relation. -/
theorem superclassCycleEmpty (c : Nat) (v : GroundType []) :
    ¬ Member ⟨[], {0,1}, [(0,1),(1,0)], []⟩ c v := by
  suffices ∀ E : ClassEnv, E.instances = [] → ∀ c v, ¬ Member E c v from this ⟨[], {0,1}, [(0,1),(1,0)], []⟩ rfl c v
  intro E hE c v h
  induction h with
  | instanceRule r vs ε hr _ _ => rw [hE] at hr; cases hr
  | superclass _ _ _ _ _ ih => exact ih

def alpha : Ty := .free (0,0)
def boolTy : Ty := .con (.other 2) []
def eqType (A : Ty) : Ty := .arrow A .empty (.arrow A .empty boolTy)
def eqScheme : Scheme := .all [0] (classAtom 0 (.bound 0)) (eqType (.bound 0))
def initialEnv : Env := ⟨[(0, eqScheme)], []⟩
def eqConstraint : Constraint := classAtom 0 alpha

def eqLambda : Expr := .lam (.lam (.app (.app (.ident (.free 0)) (.ident (.bound 1))) (.ident (.bound 0))))

def operation : OpDecl := ⟨[0], .bound 0, .bound 0, .truth⟩
def operations : OpSignature := fun op => if op = 0 then some operation else none

theorem operationsWF : operations.WF (signature exampleEnv) := by
  intro op d hd
  simp only [operations] at hd
  split at hd
  · cases hd
    exact ⟨by simp [operation, signature], .bound rfl (by simp [signature]),
      .bound rfl (by simp [signature]), by simp [operation, Ty.fv], by simp [operation, Ty.fv, Constraint.WF, Constraint.fpi, Constraint.fv]⟩
  · cases hd

theorem alphaKind : alpha.HasKind (signature exampleEnv) Δ 0 := .free (by simp [signature])
theorem boolKind : boolTy.HasKind (signature exampleEnv) Δ 0 :=
  .con (by change 0 < 2 ∧ 2 < 4; decide) .nil

theorem eqTypeKind (hA : A.HasKind (signature exampleEnv) Δ 0) :
    (eqType A).HasKind (signature exampleEnv) Δ 0 :=
  arrowKind hA (emptyKind (fixedFramework exampleEnv).signature)
    (arrowKind hA (emptyKind (fixedFramework exampleEnv).signature) boolKind)

theorem classWF (hc : c ∈ exampleEnv.classes) (hA : A.HasKind (signature exampleEnv) Δ 0) :
    (classAtom c A).WF (signature exampleEnv) Δ n := ⟨hc, .cons hA .nil⟩

theorem eqConstraintWF : eqConstraint.WF (signature exampleEnv) Δ n :=
  classWF (by simp [exampleEnv]) alphaKind

theorem eqSchemeWF : eqScheme.WF (signature exampleEnv) Δ 0 :=
  ⟨by simp [signature], classWF (by simp [exampleEnv]) (.bound rfl (by simp [signature])),
    eqTypeKind (.bound rfl (by simp [signature]))⟩

theorem initialEnvWF : initialEnv.WF (signature exampleEnv) Δ := by
  constructor
  · intro p hp
    have : p = (0, eqScheme) := by simpa [initialEnv] using hp
    subst p
    exact ⟨eqSchemeWF, rfl⟩
  · simp [initialEnv]

theorem methodInstance (hA : A.HasKind (signature exampleEnv) Δ 0) :
    Entails (signature exampleEnv) (model exampleEnv) Δ (classAtom 0 A)
      (eqScheme.instanceConstraint (eqType A)) := by
  intro ρ bs ι hρ hbs _ hc
  obtain ⟨V, hv, hm⟩ := (classAtomMeaning exampleEnv 0 A ρ bs ι).mp hc
  refine ⟨[.type V], .cons rfl .nil, ?_, ?_⟩
  · exact (classAtomMeaning exampleEnv 0 (.bound 0) ρ (.type V :: bs) ι).mpr ⟨V, by simp [Ty.eval], hm⟩
  · have ht := evalKind (fixedFramework exampleEnv) hρ hbs (eqTypeKind hA)
    have hs := evalShift (M := model exampleEnv) (eqType A) ρ bs [Ground.type V]
    simp only [List.length_cons, List.length_nil] at hs
    change _ ∧ _ ∧ _
    simp only [List.length_cons, List.length_nil]
    rw [hs]
    have he : (eqType (.bound 0)).eval (model exampleEnv) ρ ([Ground.type V] ++ bs) =
        (eqType A).eval (model exampleEnv) ρ bs := by
      simp [eqType, Ty.arrow, Ty.empty, boolTy, Ty.eval, hv]
    rw [he]
    exact ⟨ht, ht, (fixedFramework exampleEnv).belowRefl 0 (by simp [signature]) _ ht⟩

private theorem monoVariable (hC : C.WF (signature exampleEnv) Δ 0) (hf : C.fpi = ∅)
    (hΓ : Γ.WF (signature exampleEnv) Δ) (hT : T.HasKind (signature exampleEnv) Δ 0)
    (hl : Γ.lookup x = some (.mono T)) (hs : (Expr.ident x).Scoped Γ) :
    Typing (signature exampleEnv) (model exampleEnv) operations Δ C Γ (.ident x) T .empty :=
  .var ⟨hC, hf, hΓ, hs, hT, emptyKind (fixedFramework exampleEnv).signature⟩ hl
    (monoInstance (fixedFramework exampleEnv) hT)

private theorem methodTyping (hΓ : Γ.WF (signature exampleEnv) Δ)
    (hl : Γ.lookup (.free 0) = some eqScheme) (hs : (Expr.ident (.free 0)).Scoped Γ) :
    Typing (signature exampleEnv) (model exampleEnv) operations Δ eqConstraint Γ
      (.ident (.free 0)) (eqType alpha) .empty :=
  .var ⟨eqConstraintWF, rfl, hΓ, hs, eqTypeKind alphaKind,
    emptyKind (fixedFramework exampleEnv).signature⟩ hl (methodInstance alphaKind)

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

theorem eqLambdaTyping : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint
    initialEnv eqLambda (eqType alpha) .empty := by
  let Γx := initialEnv.push (.mono alpha)
  let Γxy := Γx.push (.mono alpha)
  have hx : Γx.WF (signature exampleEnv) [] := envPushMonoWF initialEnvWF alphaKind
  have hxy : Γxy.WF (signature exampleEnv) [] := envPushMonoWF hx alphaKind
  have hm := methodTyping hxy rfl (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Γxy, Γx, initialEnv, Env.push, Env.dpi])
  have vx := monoVariable eqConstraintWF rfl hxy alphaKind (x := .bound 1) rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Γxy, Γx, initialEnv, Env.push])
  have vy := monoVariable eqConstraintWF rfl hxy alphaKind (x := .bound 0) rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Γxy, Γx, initialEnv, Env.push])
  have hb := pureApplication (pureApplication hm vx) vy
  apply Typing.lam
  · exact ⟨eqConstraintWF, rfl, initialEnvWF, by
      simp [Expr.Scoped, Expr.LCAt, Expr.fv, initialEnv, Env.dpi],
      eqTypeKind alphaKind, emptyKind (fixedFramework exampleEnv).signature⟩
  apply Typing.lam
  · exact ⟨eqConstraintWF, rfl, hx, by
      simp [Expr.Scoped, Expr.LCAt, Expr.fv, initialEnv, Env.push, Env.dpi],
      arrowKind alphaKind (emptyKind (fixedFramework exampleEnv).signature) boolKind,
      emptyKind (fixedFramework exampleEnv).signature⟩
  exact hb


def argumentEnv : Env := (initialEnv.push (.mono alpha)).push (.mono alpha)
def handledMethod : Expr :=
  .handle (.app (.app (.ident (.free 0)) (.perform 0 (.ident (.bound 1)))) (.ident (.bound 0)))
    0 (.ident (.bound 0)) (.app (.ident (.bound 0)) (.ident (.bound 1)))

theorem argumentEnvWF : argumentEnv.WF (signature exampleEnv) Δ :=
  envPushMonoWF (envPushMonoWF initialEnvWF alphaKind) alphaKind

/-- This clause is typed for every operation type, with the outer Eq constraint shifted. -/
theorem universalClauseTyping {Γ : Env} (hΓ : Γ.WF (signature exampleEnv) []) :
    Typing (signature exampleEnv) (model exampleEnv) operations [0] (eqConstraint.shift 1 0)
      (((Γ.shift 1).push (.mono (.bound 0))).push (.mono (.arrow (.bound 0) .empty boolTy)))
      (.app (.ident (.bound 0)) (.ident (.bound 1))) boolTy .empty := by
  have hA : Ty.HasKind (signature exampleEnv) [0] (.bound 0) 0 := .bound rfl (by simp [signature])
  have hK := arrowKind hA (emptyKind (fixedFramework exampleEnv).signature) (boolKind (Δ := [0]))
  have hctx := envPushMonoWF (envPushMonoWF (envShiftWF hΓ [0]) hA) hK
  have hC := constraintShiftWF (eqConstraintWF (Δ := []) (n := 0)) [0]
  have hk := monoVariable hC rfl hctx hK (x := .bound 0) rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push])
  have hx := monoVariable hC rfl hctx hA (x := .bound 1) rfl
    (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push])
  exact pureApplication hk hx

theorem handledMethodTyping : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint
    argumentEnv handledMethod boolTy .empty := by
  have hem := emptyKind (Δ := []) (fixedFramework exampleEnv).signature
  have hop := singletonKind (S := signature exampleEnv) (Δ := []) 0
  have hΓ := argumentEnvWF (Δ := [])
  have hm := methodTyping hΓ rfl
    (by simp [argumentEnv, initialEnv, Env.push, Env.dpi, Expr.Scoped, Expr.LCAt, Expr.fv])
  have hx := monoVariable eqConstraintWF rfl hΓ alphaKind (x := .bound 1) rfl
    (by simp [argumentEnv, initialEnv, Env.push, Expr.Scoped, Expr.LCAt, Expr.fv])
  have hy := monoVariable eqConstraintWF rfl hΓ alphaKind (x := .bound 0) rfl
    (by simp [argumentEnv, initialEnv, Env.push, Expr.Scoped, Expr.LCAt, Expr.fv])
  have hp : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint argumentEnv
      (.perform 0 (.ident (.bound 1))) alpha (.union (.singleton 0) .empty) := by
    have ht := Typing.performTruth rfl (S := signature exampleEnv) (M := model exampleEnv) (sig := operations)
      (decl := operation) (args := [alpha])
      (show JudgmentWF (signature exampleEnv) [] eqConstraint argumentEnv
        (.perform 0 (.ident (.bound 1))) (operation.output.openAt 0 [alpha]) (.union (.singleton 0) .empty) from
        ⟨eqConstraintWF, rfl, hΓ, (typingWF hx).2.2.2.1,
          by simpa [operation, Ty.openAt, Ty.shift, alpha] using (alphaKind (Δ := [])), unionKind hop hem⟩)
      (by simp [operations]) (.cons alphaKind .nil)
      (by simpa [operation, Ty.openAt, Ty.shift, alpha] using hx)
    simpa [operation, Ty.openAt, Ty.shift, alpha] using ht
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
  apply Typing.handleTruth rfl (decl := operation) (A := boolTy) (εin := .singleton 0)
  · exact ⟨eqConstraintWF, rfl, hΓ, by
      simp [argumentEnv, initialEnv, Env.push, Env.dpi, Expr.Scoped, Expr.LCAt, Expr.fv],
      boolKind, hem⟩
  · simp [operations]
  · exact hb
  · intro ρ bs ι _ _ _ _
    simp [Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.empty, Ty.singleton,
      Ty.eval, constructor, kind, below]
  · exact monoVariable eqConstraintWF rfl (envPushMonoWF hΓ boolKind) boolKind (x := .bound 0) rfl
      (by simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push])
  · simpa [operation, Ty.shift, Ty.empty, boolTy] using universalClauseTyping hΓ

theorem initialEnvRealizable :
    Entails (signature exampleEnv) (model exampleEnv) Δ eqConstraint initialEnv.exists_ := by
  intro ρ bs ι _ _ _ hc
  obtain ⟨V, _, hm⟩ := (classAtomMeaning exampleEnv 0 alpha ρ bs ι).mp hc
  change (∃ vs, KindValues (model exampleEnv) [0] vs ∧
    (classAtom 0 (.bound 0)).Holds (model exampleEnv) ρ (vs ++ bs) ι) ∧ True
  exact ⟨⟨[.type V], .cons rfl .nil,
    (classAtomMeaning exampleEnv 0 (.bound 0) ρ (.type V :: bs) ι).mpr
      ⟨V, by simp [Ty.eval], hm⟩⟩, trivial⟩

theorem argumentEnvRealizable :
    Entails (signature exampleEnv) (model exampleEnv) Δ eqConstraint argumentEnv.exists_ := by
  intro ρ bs ι hρ hbs hι hc
  have hi := initialEnvRealizable ρ bs ι hρ hbs hι hc
  have hs : (Scheme.mono alpha).WF (signature exampleEnv) Δ 0 := ⟨by simp, trivial, alphaKind⟩
  have hm : (Scheme.mono alpha).exists_.Holds (model exampleEnv) ρ bs ι := ⟨[], .nil, trivial⟩
  exact (envPushExists hs rfl ρ bs ι).mpr ⟨(envPushExists hs rfl ρ bs ι).mpr ⟨hi, hm⟩, hm⟩

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


theorem eqLambdaInferenceSoundness :
    Typing (signature exampleEnv) (model exampleEnv) operations []
      (infer operations initialEnv eqLambda (eqType alpha) .empty) initialEnv eqLambda (eqType alpha) .empty :=
  (inferenceGuarantees eqLambdaTyping initialEnvRealizable).1

theorem eqLambdaInferenceCompleteness :
    Entails (signature exampleEnv) (model exampleEnv) [] eqConstraint
      (infer operations initialEnv eqLambda (eqType alpha) .empty) :=
  (inferenceGuarantees eqLambdaTyping initialEnvRealizable).2.1

theorem eqLambdaPrincipalConstraint :
    PrincipalConstraint (signature exampleEnv) (model exampleEnv) operations [] initialEnv eqLambda (eqType alpha) .empty
      (infer operations initialEnv eqLambda (eqType alpha) .empty) :=
  (inferenceGuarantees eqLambdaTyping initialEnvRealizable).2.2

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

def intAssignment : Assignment (model exampleEnv) :=
  fun X => if X.1 = 1 then .effect ∅ else .type .int

theorem intAssignmentValid : intAssignment.Valid (signature exampleEnv) (model exampleEnv) := by
  intro X hX
  rcases (show X.1 = 0 ∨ X.1 = 1 from hX) with h | h <;> simp [intAssignment, h, kind]

def emptyGroundEnv : GroundEnv (model exampleEnv) := ⟨fun _ => ∅, []⟩

theorem emptyGroundEnvValid : emptyGroundEnv.Valid := by
  simp [emptyGroundEnv, GroundEnv.Valid, UpperSet]

theorem eqConstraintSatisfiable : Satisfiable (signature exampleEnv) (model exampleEnv) [] eqConstraint := by
  refine ⟨eqConstraintWF, intAssignment, [], emptyGroundEnv, intAssignmentValid, .nil, emptyGroundEnvValid, ?_⟩
  exact (classAtomMeaning exampleEnv 0 alpha _ _ _).mpr ⟨.int, by simp [alpha, Ty.eval, intAssignment], eqInt⟩

private theorem generatedSatisfiable
    (ht : Typing (signature exampleEnv) (model exampleEnv) operations [] eqConstraint Γ e T .empty)
    (hc : Entails (signature exampleEnv) (model exampleEnv) [] eqConstraint (infer operations Γ e T .empty)) :
    Satisfiable (signature exampleEnv) (model exampleEnv) [] (infer operations Γ e T .empty) := by
  obtain ⟨_, ρ, bs, ι, hρ, hbs, hι, h⟩ := eqConstraintSatisfiable
  have hw := typingWF ht
  exact ⟨inferWF (fixedFramework exampleEnv).signature operationsWF hw.2.2.1 hw.2.2.2.1
    hw.2.2.2.2.1 hw.2.2.2.2.2, ρ, bs, ι, hρ, hbs, hι, hc ρ bs ι hρ hbs hι h⟩

theorem eqLambdaGeneratedSatisfiable : Satisfiable (signature exampleEnv) (model exampleEnv) []
    (infer operations initialEnv eqLambda (eqType alpha) .empty) :=
  generatedSatisfiable eqLambdaTyping eqLambdaInferenceCompleteness

theorem handledMethodGeneratedSatisfiable : Satisfiable (signature exampleEnv) (model exampleEnv) []
    (infer operations argumentEnv handledMethod boolTy .empty) :=
  generatedSatisfiable handledMethodTyping handledMethodInferenceCompleteness

/-- Public specialization entry points are applied, not merely checked by name. -/
example : PrincipalConstraint (signature exampleEnv) (model exampleEnv) operations [] initialEnv
    eqLambda (eqType alpha) .empty (infer operations initialEnv eqLambda (eqType alpha) .empty) :=
  TypeClasses.constraintGenerationPrincipality exampleEnv operations operationsWF [] initialEnv eqLambda
    (eqType alpha) .empty (by simp) initialEnvWF (typingWF eqLambdaTyping).2.2.2.1
    (typingDeclared eqLambdaTyping) (eqTypeKind alphaKind) (emptyKind (fixedFramework exampleEnv).signature)

example : Typing (signature exampleEnv) (model exampleEnv) operations []
    (infer operations argumentEnv handledMethod boolTy .empty) argumentEnv handledMethod boolTy .empty :=
  TypeClasses.inferenceSoundness exampleEnv operations operationsWF [] argumentEnv handledMethod boolTy .empty
    (by simp) argumentEnvWF (typingWF handledMethodTyping).2.2.2.1 (typingDeclared handledMethodTyping)
    boolKind (emptyKind (fixedFramework exampleEnv).signature)

example : Entails (signature exampleEnv) (model exampleEnv) [] eqConstraint
    (infer operations argumentEnv handledMethod boolTy .empty) :=
  TypeClasses.inferenceCompleteness exampleEnv operations operationsWF [] eqConstraint argumentEnv
    handledMethod boolTy .empty (by simp) argumentEnvRealizable handledMethodTyping


theorem ordEntailsEq (T : Ty) :
    Entails (signature exampleEnv) (model exampleEnv) Δ (classAtom 1 T) (classAtom 0 T) :=
  superclassEntailment exampleEnv 1 0 (by simp [exampleEnv]) T

theorem eqEntailsList (hT : T.HasKind (signature exampleEnv) Δ 0) :
    Entails (signature exampleEnv) (model exampleEnv) Δ (classAtom 0 T)
      (classAtom 0 (.con (.other 3) [T])) := by
  have hi := instanceEntailment exampleEnv exampleEnvWF ⟨0,3,[(0,0)]⟩ (by simp [exampleEnv]) [T] rfl
    (by simpa using hT) .empty (emptyKind (fixedFramework exampleEnv).signature)
  intro ρ bs ι hρ hbs hι hc
  apply hi ρ bs ι hρ hbs hι
  simpa [instanceContext, Constraint.Holds] using And.intro hc True.intro

theorem conditionalArrowEntailment
    (hA : A.HasKind (signature arrowEnv) Δ 0) (hB : B.HasKind (signature arrowEnv) Δ 0)
    (hε : ε.HasKind (signature arrowEnv) Δ 1) :
    Entails (signature arrowEnv) (model arrowEnv) Δ (.conj (classAtom 0 A) (classAtom 0 B))
      (classAtom 0 (.arrow A ε B)) := by
  have hi := instanceEntailment arrowEnv arrowEnvWF ⟨0,0,[(0,0),(0,1)]⟩ (by simp [arrowEnv]) [A,B] rfl
    (by simpa using And.intro hA hB) ε hε
  intro ρ bs ι hρ hbs hι hc
  apply hi ρ bs ι hρ hbs hι
  simpa [instanceContext, Constraint.Holds] using And.intro hc.1 (And.intro hc.2 True.intro)

example : ∃ v, constructor [0,3] (.other 5)
    [.type (.arrow .int {7} .bool), .type .int, .type (.list (.arrow .bool {9} .int))] = .type v ∧
    v.tag = 5 ∧ v.arguments = [.arrow .int {7} .bool, .int, .list (.arrow .bool {9} .int)] :=
  constructorPreserves extraEnv 5 (by change 0 < 5 ∧ 5 < 6; decide)
    [.arrow .int {7} .bool, .int, .list (.arrow .bool {9} .int)] rfl

example : constructor [] (.other 3) [.effect {0}] = .type .int := rfl
example : constructor [] (.other 0) [.type .int, .type .bool] = .type .int := rfl
example : constructor [] (.other 3) [.type .int, .type .bool] = .type .int := rfl
example : ¬ Symbol.Declared (signature exampleEnv) (.other 0) := by simp [Symbol.Declared, signature]

/-- Contravariance in the domain and covariance in latent effects are both used. -/
example : GroundType.Below (extras := [])
    (.arrow (.arrow .int {0} .int) ∅ .bool)
    (.arrow (.arrow .int ∅ .int) {1} .bool) :=
  .arrow (.arrow .int (by simp) .int) (by simp) .bool

example (v : HMX.TypeClasses.Ground exampleEnv.extraArities) :
    Member exampleEnv 0 (embed v) ↔ HMX.TypeClasses.Member exampleEnv 0 v :=
  memberEmbedIff exampleEnv 0 v

end EHMX.TypeClasses.Regression
