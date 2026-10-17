import HMX.LocallyNameless.Proofs.TypeClasses

namespace HMX.TypeClasses.Regression

open HMX.TypeClasses.Proofs

/-- Eq = 0, Ord = 1, Empty = 2. The six instances and superclass edge are data. -/
def exampleEnv : ClassEnv :=
  ⟨[], {0,1,2}, [(1,0)],
    [⟨0,1,[]⟩, ⟨0,2,[]⟩, ⟨0,3,[(0,0)]⟩,
     ⟨1,1,[]⟩, ⟨1,2,[]⟩, ⟨1,3,[(1,0)]⟩]⟩

theorem exampleEnvWF : exampleEnv.WF := by
  simp [ClassEnv.WF, InstanceRule.WF, exampleEnv, arity]

theorem ordEntailsEq (T : Ty) :
    Entails (signature exampleEnv) (model exampleEnv) (classAtom 1 T) (classAtom 0 T) :=
  Proofs.superclassEntailment exampleEnv 1 0 (by simp [exampleEnv]) T

theorem eqEntailsList (T : Ty) :
    Entails (signature exampleEnv) (model exampleEnv) (classAtom 0 T) (classAtom 0 (.con 3 [T])) := by
  have h := Proofs.instanceEntailment exampleEnv exampleEnvWF ⟨0,3,[(0,0)]⟩
    (by simp [exampleEnv]) [T] rfl
  intro ρ ι hρ hι hc
  apply h ρ ι hρ hι
  simpa [instanceContext, Constraint.Holds] using And.intro hc True.intro

theorem eqInt : Member exampleEnv 0 .int := by
  exact .instanceRule ⟨0,1,[]⟩ [] (by simp [exampleEnv]) rfl (by simp)

theorem eqBool : Member exampleEnv 0 .bool := by
  exact .instanceRule ⟨0,2,[]⟩ [] (by simp [exampleEnv]) rfl (by simp)

theorem ordInt : Member exampleEnv 1 .int := by
  exact .instanceRule ⟨1,1,[]⟩ [] (by simp [exampleEnv]) rfl (by simp)

theorem ordBool : Member exampleEnv 1 .bool := by
  exact .instanceRule ⟨1,2,[]⟩ [] (by simp [exampleEnv]) rfl (by simp)

theorem memberList (c : Nat) (hc : c = 0 ∨ c = 1) (v : Ground exampleEnv.extraArities)
    (h : Member exampleEnv c v) : Member exampleEnv c (.list v) := by
  apply Member.instanceRule (E := exampleEnv) ⟨c,3,[(c,0)]⟩ [v]
  · rcases hc with rfl | rfl <;> simp [exampleEnv]
  · rfl
  · simpa using h

theorem nestedListEq : Member exampleEnv 0 (.list (.list (.list .int))) :=
  memberList 0 (Or.inl rfl) _ (memberList 0 (Or.inl rfl) _ (memberList 0 (Or.inl rfl) _ eqInt))

theorem nestedListOrd : Member exampleEnv 1 (.list (.list .bool)) :=
  memberList 1 (Or.inr rfl) _ (memberList 1 (Or.inr rfl) _ ordBool)

/-- Inversion of the least derivation, including superclass steps. -/
theorem memberNotArrowTag (c : Nat) (v : Ground exampleEnv.extraArities) (h : Member exampleEnv c v) : v.tag ≠ 0 := by
  induction h with
  | instanceRule r vs hr hl _ =>
    have hw := exampleEnvWF.2 r hr
    rw [constructTag _ _ _ hw.2.1 hl]
    simp only [exampleEnv, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  | superclass c d v _ _ ih => exact ih

theorem noEqArrow (a b : Ground exampleEnv.extraArities) : ¬ Member exampleEnv 0 (.arrow a b) := by
  intro h
  exact memberNotArrowTag _ _ h rfl

theorem emptyClass (v : Ground exampleEnv.extraArities) : ¬ Member exampleEnv 2 v := by
  suffices ∀ c v, Member exampleEnv c v → c ≠ 2 from fun h => this 2 v h rfl
  intro c v h
  induction h with
  | instanceRule r vs hr _ _ =>
    simp only [exampleEnv, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  | superclass c d v hr _ _ =>
    have : (c,d) = (1,0) := by simpa [exampleEnv] using hr
    cases this
    decide

theorem emptyClassExistsFalse (A : Vars) (T : Ty) (ρ : Assignment (model exampleEnv))
    (ι : GroundEnv (model exampleEnv)) :
    ¬ (Constraint.exists_ A (classAtom 2 T)).Holds (signature exampleEnv) (model exampleEnv) ρ ι := by
  rintro ⟨ρ',_,_,h⟩
  exact emptyClass _ ((Proofs.classAtomMeaning exampleEnv 2 T ρ' ι).mp h)

theorem emptyClassNotSatisfiable (A : Vars) (T : Ty) :
    ¬ Satisfiable (signature exampleEnv) (model exampleEnv) (.exists_ A (classAtom 2 T)) := by
  rintro ⟨_,ρ,ι,_,_,h⟩
  exact emptyClassExistsFalse A T ρ ι h

def emptyEnv : ClassEnv := ⟨[], ∅, [], []⟩

theorem emptyEnvWF : emptyEnv.WF := by simp [ClassEnv.WF, emptyEnv]

theorem emptyEnvFramework : fixedFramework emptyEnv := Proofs.fixedFramework emptyEnv

theorem emptyEnvNoMember (c : Nat) (v : Ground emptyEnv.extraArities) : ¬ Member emptyEnv c v := by
  intro h
  cases h with
  | instanceRule r vs hr _ _ => simp [emptyEnv] at hr
  | superclass c d v hr _ => simp [emptyEnv] at hr

/-- Extra names 4 and 5 have arities zero and three. -/
def extraEnv : ClassEnv := ⟨[0,3], ∅, [], []⟩

theorem extraEnvFramework : fixedFramework extraEnv := Proofs.fixedFramework extraEnv

theorem extraConstructorsSeparated :
    construct [0,3] 4 [] ≠ construct [0,3] 5 [.int,.bool,.list .int] := by
  intro h
  have ht := congrArg Ground.tag h
  rw [constructTag _ _ _ (by decide) rfl, constructTag _ _ _ (by decide) rfl] at ht
  cases ht

def alpha : Ty := .var (0,0)
def boolTy : Ty := .con 2 []
def eqType : Ty := .arrow alpha (.arrow alpha boolTy)
def eqConstraint : Constraint := classAtom 0 alpha
def eqScheme : Scheme := methodScheme 0 (0,0) eqType
def initialEnv : Env := [(.const 0, eqScheme)]
def eqLambda : Expr := .lam 0 (.lam 1 (.app (.app (.ident (.const 0)) (.ident (.var 0))) (.ident (.var 1))))

theorem alphaKind : alpha.HasKind (signature exampleEnv) 0 := .var _ rfl

theorem boolKind : boolTy.HasKind (signature exampleEnv) 0 :=
  .con 2 [] (by change 2 < 4; decide) .nil

theorem arrowKind {E : ClassEnv} {T U : Ty} (hT : T.HasKind (signature E) 0)
    (hU : U.HasKind (signature E) 0) : (Ty.arrow T U).HasKind (signature E) 0 :=
  .con 0 [T,U] (by change 0 < 4 + E.extraArities.length; omega) (.cons hT (.cons hU .nil))

theorem eqTypeKind : eqType.HasKind (signature exampleEnv) 0 :=
  arrowKind alphaKind (arrowKind alphaKind boolKind)

theorem classWF {E : ClassEnv} (c : Nat) (hc : c ∈ E.classes) (T : Ty)
    (hT : T.HasKind (signature E) 0) : (classAtom c T).WF (signature E) :=
  ⟨hc,.cons hT .nil⟩

theorem eqConstraintWF : eqConstraint.WF (signature exampleEnv) :=
  classWF 0 (by simp [exampleEnv]) alpha alphaKind

theorem monoWF {E : ClassEnv} {T : Ty} (hT : T.HasKind (signature E) 0) :
    (Scheme.mono T).WF (signature E) := ⟨by simp, trivial, hT⟩

theorem eqSchemeWF : eqScheme.WF (signature exampleEnv) :=
  ⟨by simp [signature], eqConstraintWF, eqTypeKind⟩

theorem initialEnvWF : initialEnv.WF (signature exampleEnv) := by
  intro p hp
  have : p = (.const 0,eqScheme) := by simpa [initialEnv] using hp
  subst p
  exact eqSchemeWF

theorem initialEnvFpi : initialEnv.fpi = ∅ := by
  simp [initialEnv, Env.fpi, eqScheme, methodScheme, Scheme.fpi, classAtom, Constraint.fpi]

theorem extendedEnvWF (Γ : Env) (hΓ : Γ.WF (signature exampleEnv)) (z : Nat) :
    (Γ ++ [(Id.var z, Scheme.mono alpha)]).WF (signature exampleEnv) := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hΓ p hp
  · have : p = (Id.var z,Scheme.mono alpha) := by simpa using hp
    subst p
    exact monoWF alphaKind

theorem extendedEnvFpi (Γ : Env) (hf : Γ.fpi = ∅) (z : Nat) :
    (Γ ++ [(Id.var z, Scheme.mono alpha)]).fpi = ∅ := by
  simpa [Env.fpi, Scheme.mono, Scheme.fpi, Constraint.fpi] using hf

theorem monoJudgment (Γ : Env) (T : Ty) (hΓ : Γ.WF (signature exampleEnv))
    (hf : Γ.fpi = ∅) (hT : T.HasKind (signature exampleEnv) 0) :
    JudgmentWF (signature exampleEnv) eqConstraint Γ (.mono T) :=
  ⟨eqConstraintWF,hΓ,monoWF hT,rfl,hf,rfl⟩

theorem eqSchemeExists : Entails (signature exampleEnv) (model exampleEnv) eqConstraint eqScheme.exists_ := by
  intro ρ ι hρ _ h
  exact ⟨ρ,hρ,fun _ _ => rfl,h⟩

theorem methodTyping (Γ : Env) (hΓ : Γ.WF (signature exampleEnv)) (hf : Γ.fpi = ∅)
    (hl : lookup Γ (.const 0) = some eqScheme) :
    Typing (signature exampleEnv) (model exampleEnv) eqConstraint Γ (.ident (.const 0)) (.mono eqType) := by
  have hv : Typing (signature exampleEnv) (model exampleEnv) eqConstraint Γ (.ident (.const 0)) eqScheme :=
    ⟨_,.var ⟨eqConstraintWF,hΓ,eqSchemeWF,rfl,hf,rfl⟩ hl eqSchemeExists⟩
  have hi : Typing (signature exampleEnv) (model exampleEnv) (.conj eqConstraint eqConstraint)
      Γ (.ident (.const 0)) (.mono eqType) :=
    ⟨_,.inst ⟨⟨eqConstraintWF,eqConstraintWF⟩,hΓ,monoWF eqTypeKind,rfl,hf,rfl⟩ hv.choose_spec⟩
  exact HMX.Proofs.typingConstraintEquivalent hi eqConstraintWF rfl
    ⟨fun _ _ _ _ h => h.1, fun _ _ _ _ h => ⟨h,h⟩⟩

theorem monoVariable (Γ : Env) (z : Nat) (hΓ : Γ.WF (signature exampleEnv)) (hf : Γ.fpi = ∅)
    (hl : lookup Γ (.var z) = some (.mono alpha)) :
    Typing (signature exampleEnv) (model exampleEnv) eqConstraint Γ (.ident (.var z)) (.mono alpha) := by
  refine ⟨_,.var (monoJudgment Γ alpha hΓ hf alphaKind) hl ?_⟩
  intro ρ ι hρ _ _
  exact ⟨ρ,hρ,fun _ _ => rfl, trivial⟩

/-- The thesis's λx.λy.eq x y, with eq explicitly supplied by the initial environment. -/
theorem eqLambdaTyping :
    Typing (signature exampleEnv) (model exampleEnv) eqConstraint initialEnv eqLambda (.mono eqType) := by
  let Γx := initialEnv ++ [(.var 0, Scheme.mono alpha)]
  let Γxy := Γx ++ [(.var 1, Scheme.mono alpha)]
  have hx := extendedEnvWF initialEnv initialEnvWF 0
  have hxy := extendedEnvWF Γx hx 1
  have hxf := extendedEnvFpi initialEnv initialEnvFpi 0
  have hxyf := extendedEnvFpi Γx hxf 1
  have heq := methodTyping Γxy hxy hxyf rfl
  have vx := monoVariable Γxy 0 hxy hxyf rfl
  have vy := monoVariable Γxy 1 hxy hxyf rfl
  have appx : Typing (signature exampleEnv) (model exampleEnv) eqConstraint Γxy
      (.app (.ident (.const 0)) (.ident (.var 0))) (.mono (.arrow alpha boolTy)) :=
    ⟨_,.app (monoJudgment _ _ hxy hxyf (arrowKind alphaKind boolKind)) heq.choose_spec vx.choose_spec⟩
  have appy : Typing (signature exampleEnv) (model exampleEnv) eqConstraint Γxy
      (.app (.app (.ident (.const 0)) (.ident (.var 0))) (.ident (.var 1))) (.mono boolTy) :=
    ⟨_,.app (monoJudgment _ _ hxy hxyf boolKind) appx.choose_spec vy.choose_spec⟩
  exact ⟨_,.abs (monoJudgment _ _ initialEnvWF initialEnvFpi eqTypeKind)
    (.abs (monoJudgment _ _ hx hxf (arrowKind alphaKind boolKind)) appy.choose_spec)⟩

theorem initialEnvRealizable :
    Entails (signature exampleEnv) (model exampleEnv) eqConstraint initialEnv.exists_ := by
  intro ρ ι hρ hι h
  exact ⟨trivial, eqSchemeExists ρ ι hρ hι h⟩

theorem eqLambdaScope : eqLambda.fpi ⊆ initialEnv.dpi := by
  decide +kernel

theorem eqLambdaInferenceSoundness :
    Typing (signature exampleEnv) (model exampleEnv) (infer initialEnv eqLambda eqType)
      initialEnv eqLambda (.mono eqType) :=
  Proofs.theorem10_4_4_soundness_scoped exampleEnv _ _ _ initialEnvWF initialEnvFpi eqLambdaScope eqTypeKind

theorem eqLambdaInferenceCompleteness :
    Entails (signature exampleEnv) (model exampleEnv) eqConstraint (infer initialEnv eqLambda eqType) :=
  Proofs.theorem10_4_8_completeness exampleEnv _ _ _ _ initialEnvRealizable
    (by simp [eqConstraint, classAtom, Constraint.fpi, initialEnvFpi]) eqLambdaTyping

theorem eqLambdaPrincipalConstraint :
    PrincipalConstraint (signature exampleEnv) (model exampleEnv) initialEnv eqLambda eqType
      (infer initialEnv eqLambda eqType) :=
  Proofs.constraintGenerationPrincipality_scoped exampleEnv _ _ _ initialEnvWF initialEnvFpi eqLambdaScope eqTypeKind

theorem assignmentsValid (ρ : Assignment (model E)) : ρ.Valid (signature E) (model E) := by
  intro X hX
  exact hX.symm

theorem emptyGroundEnvValid : GroundEnv.Valid (model E) (fun _ => ∅) := by
  intro x
  exact ⟨by simp,by simp⟩

theorem emptyClassNotEquivalentTrue :
    ¬ Equivalent (signature exampleEnv) (model exampleEnv)
      (.exists_ {(0,0)} (classAtom 2 alpha)) .truth := by
  intro h
  exact emptyClassExistsFalse _ _ (fun _ => .int) (fun _ => ∅)
    (h.2 (fun _ => .int) (fun _ => ∅) (assignmentsValid _) emptyGroundEnvValid trivial)

theorem functionEqNotSatisfiable :
    ¬ Satisfiable (signature exampleEnv) (model exampleEnv)
      (classAtom 0 (.arrow alpha boolTy)) := by
  rintro ⟨_,ρ,ι,_,_,h⟩
  have hm := (Proofs.classAtomMeaning exampleEnv 0 _ ρ ι).mp h
  simp only [Ty.arrow, Ty.eval, List.map_cons, List.map_nil, construct] at hm
  exact noEqArrow _ _ hm

/-- A concrete witness checks conjunction and existential satisfaction together. -/
theorem classConjunctionExistsSatisfiable :
    Satisfiable (signature exampleEnv) (model exampleEnv)
      (.exists_ {(0,0)} (.conj eqConstraint (classAtom 0 (.con 3 [alpha])))) := by
  refine ⟨⟨by simp [signature],eqConstraintWF, classWF 0 (by simp [exampleEnv]) _ ?_⟩,
    (fun _ => .int), (fun _ => ∅), assignmentsValid _, emptyGroundEnvValid, ?_⟩
  · exact .con 3 [alpha] (by change 3 < 4; decide) (.cons alphaKind .nil)
  · refine ⟨(fun _ => .int),assignmentsValid _,fun _ _ => rfl,?_,?_⟩
    · exact (Proofs.classAtomMeaning exampleEnv 0 alpha _ _).mpr (by simpa [alpha, Ty.eval] using eqInt)
    · apply (Proofs.classAtomMeaning exampleEnv 0 (.con 3 [alpha]) _ _).mpr
      simpa [alpha, Ty.eval, construct] using memberList 0 (Or.inl rfl) _ eqInt

theorem eqConstraintSatisfiable : Satisfiable (signature exampleEnv) (model exampleEnv) eqConstraint := by
  refine ⟨eqConstraintWF,(fun _ => .int),(fun _ => ∅),assignmentsValid _,emptyGroundEnvValid,?_⟩
  exact (Proofs.classAtomMeaning exampleEnv 0 alpha _ _).mpr (by simpa [alpha, Ty.eval] using eqInt)

theorem generatedConstraintSatisfiable :
    Satisfiable (signature exampleEnv) (model exampleEnv) (infer initialEnv eqLambda eqType) := by
  obtain ⟨_,ρ,ι,hρ,hι,h⟩ := eqConstraintSatisfiable
  exact ⟨HMX.LN.Proofs.namedInferWF (signatureValid exampleEnv) _ _ _ initialEnvWF eqTypeKind,
    ρ,ι,hρ,hι,eqLambdaInferenceCompleteness ρ ι hρ hι h⟩

end HMX.TypeClasses.Regression
