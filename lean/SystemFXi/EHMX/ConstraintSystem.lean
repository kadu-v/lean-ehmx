import SystemFXi.EHMX.PrincipalScheme
import SystemFXi.EHMX.Classes

namespace SystemFXi.EHMX

/-- The constraint parameter of EHM(X).  In the HM(X) sense, `Formula` is the
whole constraint domain, rather than the type of extra atomic predicates.
There are two projection operators because EHM(X) has type and effect names.
The last three operations are the signature required by effect handlers. -/
structure ConstraintSystem where
  Formula : Type
  holds : Formula → Valuation → Prop
  trivial : Formula
  combine : Formula → Formula → Formula
  hideType : Nat → Formula → Formula
  hideEffect : Nat → Formula → Formula
  equalType : Ty → Ty → Formula
  includedEffect : Effect → Effect → Formula
  excludes : Op → Effect → Formula
  handlerClause : Finset Nat → Finset Nat → Finset Nat →
    Finset Nat → Formula → Formula
  freeTypes : Formula → Finset Nat
  freeEffects : Formula → Finset Nat
  trivial_iff : ∀ v, holds trivial v ↔ True
  combine_iff : ∀ c d v, holds (combine c d) v ↔ holds c v ∧ holds d v
  hideType_iff : ∀ i c v,
    holds (hideType i c) v ↔
      ∃ t, holds c { v with types := Function.update v.types i t }
  hideEffect_iff : ∀ i c v,
    holds (hideEffect i c) v ↔
      ∃ ε, holds c { v with effects := Function.update v.effects i ε }
  projection_iff : ∀ (bt be : Finset Nat) (c : Formula) (v : Valuation),
    holds ((bt.sort (· ≤ ·)).foldr hideType
      ((be.sort (· ≤ ·)).foldr hideEffect c)) v ↔
      ∃ ft : Nat → GroundTy, ∃ fe : Nat → Finset Op,
        (∀ i, i ∉ bt → ft i = v.types i) ∧
        (∀ i, i ∉ be → fe i = v.effects i) ∧
        holds c ⟨ft, fe⟩
  equalType_iff : ∀ a b v, holds (equalType a b) v ↔ a.eval v = b.eval v
  includedEffect_iff : ∀ a b v,
    holds (includedEffect a b) v ↔ a.eval v.effects ⊆ b.eval v.effects
  excludes_iff : ∀ op ε v,
    holds (excludes op ε) v ↔ op ∉ ε.eval v.effects
  handlerClause_iff : ∀ bt be lt le c v,
    holds (handlerClause bt be lt le c) v ↔
      ∀ ft : Nat → GroundTy, ∀ fe : Nat → Finset Op,
        (∀ i, i ∉ bt → ft i = v.types i) →
        (∀ i, i ∉ be → fe i = v.effects i) →
        ∃ wt : Nat → GroundTy, ∃ we : Nat → Finset Op,
          (∀ i, i ∉ lt → wt i = ft i) ∧
          (∀ i, i ∉ le → we i = fe i) ∧
          holds c ⟨wt, we⟩
  free_support : ∀ c v w,
    (∀ i ∈ freeTypes c, v.types i = w.types i) →
    (∀ i ∈ freeEffects c, v.effects i = w.effects i) →
    (holds c v ↔ holds c w)

namespace ConstraintSystem

def Entails (X : ConstraintSystem) (c d : X.Formula) : Prop :=
  ∀ v, X.holds c v → X.holds d v

def Equivalent (X : ConstraintSystem) (c d : X.Formula) : Prop :=
  X.Entails c d ∧ X.Entails d c

theorem entails_refl (X : ConstraintSystem) (c : X.Formula) :
    X.Entails c c := fun _ h => h

theorem entails_trans (X : ConstraintSystem) {a b c : X.Formula}
    (hab : X.Entails a b) (hbc : X.Entails b c) : X.Entails a c :=
  fun v h => hbc v (hab v h)

theorem entails_hideType (X : ConstraintSystem) (i : Nat)
    (c : X.Formula) : X.Entails c (X.hideType i c) := by
  intro v hc
  apply (X.hideType_iff i c v).2
  exact ⟨v.types i, by simpa using hc⟩

theorem entails_hideEffect (X : ConstraintSystem) (i : Nat)
    (c : X.Formula) : X.Entails c (X.hideEffect i c) := by
  intro v hc
  apply (X.hideEffect_iff i c v).2
  exact ⟨v.effects i, by simpa using hc⟩

theorem hideType_mono (X : ConstraintSystem) (i : Nat)
    {c d : X.Formula} (h : X.Entails c d) :
    X.Entails (X.hideType i c) (X.hideType i d) := by
  intro v hc
  obtain ⟨t, ht⟩ := (X.hideType_iff i c v).1 hc
  exact (X.hideType_iff i d v).2 ⟨t, h _ ht⟩

theorem hideEffect_mono (X : ConstraintSystem) (i : Nat)
    {c d : X.Formula} (h : X.Entails c d) :
    X.Entails (X.hideEffect i c) (X.hideEffect i d) := by
  intro v hc
  obtain ⟨ε, hε⟩ := (X.hideEffect_iff i c v).1 hc
  exact (X.hideEffect_iff i d v).2 ⟨ε, h _ hε⟩

/-- Handler-clause quantification preserves semantic entailment. -/
theorem handlerClause_mono (X : ConstraintSystem)
    (bt be lt le : Finset Nat) {c d : X.Formula}
    (h : X.Entails c d) :
    X.Entails (X.handlerClause bt be lt le c)
      (X.handlerClause bt be lt le d) := by
  intro v hc
  apply (X.handlerClause_iff bt be lt le d v).2
  intro ft fe hft hfe
  obtain ⟨wt, we, hwt, hwe, hcd⟩ :=
    (X.handlerClause_iff bt be lt le c v).1 hc ft fe hft hfe
  exact ⟨wt, we, hwt, hwe, h _ hcd⟩

theorem hideType_combine (X : ConstraintSystem) (i : Nat)
    (c d : X.Formula) :
    X.Equivalent
      (X.hideType i (X.combine c (X.hideType i d)))
      (X.combine (X.hideType i c) (X.hideType i d)) := by
  constructor
  · intro v hv
    obtain ⟨t, ht⟩ := (X.hideType_iff i _ v).1 hv
    obtain ⟨hc, hd⟩ := (X.combine_iff _ _ _).1 ht
    refine (X.combine_iff _ _ _).2 ⟨(X.hideType_iff i c v).2 ⟨t, hc⟩, ?_⟩
    obtain ⟨u, hu⟩ := (X.hideType_iff i d _).1 hd
    apply (X.hideType_iff i d v).2
    exact ⟨u, by simpa [Function.update] using hu⟩
  · intro v hv
    obtain ⟨hc, hd⟩ := (X.combine_iff _ _ _).1 hv
    obtain ⟨t, ht⟩ := (X.hideType_iff i c v).1 hc
    obtain ⟨u, hu⟩ := (X.hideType_iff i d v).1 hd
    apply (X.hideType_iff i _ v).2
    refine ⟨t, (X.combine_iff _ _ _).2 ⟨ht, ?_⟩⟩
    apply (X.hideType_iff i d _).2
    exact ⟨u, by simpa [Function.update] using hu⟩

theorem hideType_comm (X : ConstraintSystem) (i j : Nat)
    (c : X.Formula) :
    X.Equivalent (X.hideType i (X.hideType j c))
      (X.hideType j (X.hideType i c)) := by
  by_cases hij : i = j
  · subst j
    exact ⟨X.entails_refl _, X.entails_refl _⟩
  constructor
  · intro v hv
    obtain ⟨t, ht⟩ := (X.hideType_iff i _ v).1 hv
    obtain ⟨u, hu⟩ := (X.hideType_iff j c _).1 ht
    apply (X.hideType_iff j _ v).2
    refine ⟨u, (X.hideType_iff i c _).2 ⟨t, ?_⟩⟩
    simpa [Function.update_comm hij] using hu
  · intro v hv
    obtain ⟨u, hu⟩ := (X.hideType_iff j _ v).1 hv
    obtain ⟨t, ht⟩ := (X.hideType_iff i c _).1 hu
    apply (X.hideType_iff i _ v).2
    refine ⟨t, (X.hideType_iff j c _).2 ⟨u, ?_⟩⟩
    simpa [Function.update_comm hij] using ht

/-- HM(X) expresses a substitution by a diagonal equality followed by
projection. The occurs condition is needed only when this is simplified to a
direct syntactic substitution. -/
def substituteType (X : ConstraintSystem) (i : Nat) (τ : Ty)
    (c : X.Formula) : X.Formula :=
  X.hideType i (X.combine c (X.equalType (.var i) τ))

theorem substituteType_iff (X : ConstraintSystem) (i : Nat)
    (τ : Ty) (c : X.Formula) (v : Valuation) :
    X.holds (X.substituteType i τ c) v ↔
      ∃ t, X.holds c {v with types := Function.update v.types i t} ∧
        t = τ.eval {v with types := Function.update v.types i t} := by
  simp [substituteType, X.hideType_iff, X.combine_iff,
    X.equalType_iff, Ty.eval]

def equalEffect (X : ConstraintSystem) (a b : Effect) : X.Formula :=
  X.combine (X.includedEffect a b) (X.includedEffect b a)

theorem equalEffect_iff (X : ConstraintSystem) (a b : Effect)
    (v : Valuation) :
    X.holds (X.equalEffect a b) v ↔
      a.eval v.effects = b.eval v.effects := by
  simp [equalEffect, X.combine_iff, X.includedEffect_iff,
    Finset.Subset.antisymm_iff]

def split (X : ConstraintSystem) (op : Op) (input rest : Effect) :
    X.Formula :=
  X.combine (X.includedEffect rest input)
    (X.combine
      (X.includedEffect input (Poly.Effect.singleton op ∪ rest))
      (X.excludes op rest))

theorem split_iff (X : ConstraintSystem) (op : Op)
    (input rest : Effect) (v : Valuation) :
    X.holds (X.split op input rest) v ↔
      rest.eval v.effects ⊆ input.eval v.effects ∧
      input.eval v.effects ⊆
        (Poly.Effect.singleton op ∪ rest).eval v.effects ∧
      op ∉ rest.eval v.effects := by
  simp [split, X.combine_iff, X.includedEffect_iff, X.excludes_iff]

def project (X : ConstraintSystem) (types effects : Finset Nat)
    (c : X.Formula) : X.Formula :=
  (types.sort (· ≤ ·)).foldr X.hideType
    ((effects.sort (· ≤ ·)).foldr X.hideEffect c)

/-- The free-name laws of conjunction and projection used by HM(X)
generalization, plus the bound-name law needed by handler clauses. -/
structure LawfulFV (X : ConstraintSystem) : Prop where
  combine_types : ∀ c d,
    X.freeTypes (X.combine c d) ⊆ X.freeTypes c ∪ X.freeTypes d
  combine_effects : ∀ c d,
    X.freeEffects (X.combine c d) ⊆ X.freeEffects c ∪ X.freeEffects d
  project_types : ∀ bt be c,
    X.freeTypes (X.project bt be c) ⊆ X.freeTypes c \ bt
  project_effects : ∀ bt be c,
    X.freeEffects (X.project bt be c) ⊆ X.freeEffects c \ be
  handler_types : ∀ bt be lt le c,
    X.freeTypes (X.handlerClause bt be lt le c) ⊆
      X.freeTypes c \ (bt ∪ lt)
  handler_effects : ∀ bt be lt le c,
    X.freeEffects (X.handlerClause bt be lt le c) ⊆
      X.freeEffects c \ (be ∪ le)

/-- Free-name laws for the distinguished HM(X) constraints. The original
HM(X) free-variable definition is induced by projection; this explicit
interface records the corresponding finite syntactic bounds. -/
structure LawfulGeneratedFV (X : ConstraintSystem) : Prop where
  trivial_types : X.freeTypes X.trivial = ∅
  trivial_effects : X.freeEffects X.trivial = ∅
  equalType_types : ∀ a b,
    X.freeTypes (X.equalType a b) ⊆ a.fvTypes ∪ b.fvTypes
  equalType_effects : ∀ a b,
    X.freeEffects (X.equalType a b) ⊆ a.fvEffects ∪ b.fvEffects
  includedEffect_types : ∀ a b,
    X.freeTypes (X.includedEffect a b) = ∅
  includedEffect_effects : ∀ a b,
    X.freeEffects (X.includedEffect a b) ⊆ a.vars ∪ b.vars
  excludes_types : ∀ op ε,
    X.freeTypes (X.excludes op ε) = ∅
  excludes_effects : ∀ op ε,
    X.freeEffects (X.excludes op ε) ⊆ ε.vars

theorem LawfulFV.handlerClause_rigid_free {X : ConstraintSystem}
    (h : X.LawfulFV) (bt be lt le : Finset Nat) (c : X.Formula) :
    Disjoint bt (X.freeTypes (X.handlerClause bt be lt le c)) ∧
    Disjoint be (X.freeEffects (X.handlerClause bt be lt le c)) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hib hif
    have hi := h.handler_types bt be lt le c hif
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hib)
  · apply Finset.disjoint_left.mpr
    intro i hib hif
    have hi := h.handler_effects bt be lt le c hif
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hib)

/-- The operation clause's eigenvariable check is a metalevel judgment.
It uses only X's entailment and existential projection; no universal
constraint constructor is imposed on X. -/
def ClauseValid (X : ConstraintSystem) (ambient clause : X.Formula)
    (localTypes localEffects : Finset Nat) : Prop :=
  X.Entails ambient (X.project localTypes localEffects clause)

theorem clauseValid_iff_handlerClause (X : ConstraintSystem)
    (ambient clause : X.Formula)
    (rigidTypes rigidEffects localTypes localEffects : Finset Nat)
    (ht : Disjoint rigidTypes (X.freeTypes ambient))
    (he : Disjoint rigidEffects (X.freeEffects ambient)) :
    X.ClauseValid ambient clause localTypes localEffects ↔
      X.Entails ambient
        (X.handlerClause rigidTypes rigidEffects
          localTypes localEffects clause) := by
  constructor
  · intro hc v hav
    apply (X.handlerClause_iff rigidTypes rigidEffects
      localTypes localEffects clause v).2
    intro ft fe hft hfe
    have hta : ∀ i ∈ X.freeTypes ambient, ft i = v.types i := by
      intro i hi
      apply hft
      intro hri
      exact (Finset.disjoint_left.mp ht hri hi).elim
    have hea : ∀ i ∈ X.freeEffects ambient, fe i = v.effects i := by
      intro i hi
      apply hfe
      intro hri
      exact (Finset.disjoint_left.mp he hri hi).elim
    have hav' : X.holds ambient ⟨ft, fe⟩ :=
      (X.free_support ambient v ⟨ft, fe⟩
        (fun i hi => (hta i hi).symm)
        (fun i hi => (hea i hi).symm)).mp hav
    exact (X.projection_iff localTypes localEffects clause ⟨ft, fe⟩).1
      (hc ⟨ft, fe⟩ hav')
  · intro hc v hav
    have hh := (X.handlerClause_iff rigidTypes rigidEffects
      localTypes localEffects clause v).1 (hc v hav)
    have hp := hh v.types v.effects
      (by intros; rfl) (by intros; rfl)
    exact (X.projection_iff localTypes localEffects clause v).2 hp

/-- A solved residual formula and a substitution form a normal form in X. -/
structure NormalForm (X : ConstraintSystem) where
  residual : X.Formula
  subst : Substitution

def NormalForm.Represents {X : ConstraintSystem} (n : X.NormalForm)
    (v : Valuation) : Prop :=
  ∃ w, X.holds n.residual w ∧ v = w.pullbackSubst n.subst

def NormalForm.SoundFor {X : ConstraintSystem} (n : X.NormalForm)
    (d : X.Formula) : Prop :=
  ∀ v, n.Represents v → X.holds d v

def NormalForm.Covers {X : ConstraintSystem} (n : X.NormalForm)
    (d : X.Formula) : Prop :=
  ∀ v, X.holds d v → n.Represents v

def SemFreeType (X : ConstraintSystem) (d : X.Formula) (i : Nat) : Prop :=
  ∃ v : Valuation, ∃ t : GroundTy,
    ¬ X.holds d v ∧
      X.holds d {v with types := Function.update v.types i t}

def SemFreeEffect (X : ConstraintSystem) (d : X.Formula) (i : Nat) : Prop :=
  ∃ v : Valuation, ∃ ε : Finset Op,
    ¬ X.holds d v ∧
      X.holds d {v with effects := Function.update v.effects i ε}

def NormalForm.IsNormalForm {X : ConstraintSystem}
    (solved : X.Formula → Prop) (d : X.Formula) (n : X.NormalForm) : Prop :=
  solved n.residual ∧ n.SoundFor d

def NormalForm.MoreGeneralThanOn {X : ConstraintSystem}
    (d : X.Formula) (n m : X.NormalForm) : Prop :=
  ∀ v, m.Represents v → ∃ w, n.Represents w ∧
    (∀ i, X.SemFreeType d i → w.types i = v.types i) ∧
    (∀ i, X.SemFreeEffect d i → w.effects i = v.effects i)

def NormalForm.IsPrincipal {X : ConstraintSystem}
    (solved : X.Formula → Prop) (d : X.Formula) (n : X.NormalForm) : Prop :=
  n.IsNormalForm solved d ∧
  ∀ m, m.IsNormalForm solved d → n.MoreGeneralThanOn d m

theorem NormalForm.principal_of_covers {X : ConstraintSystem}
    (solved : X.Formula → Prop) (d : X.Formula) (n : X.NormalForm)
    (hn : n.IsNormalForm solved d) (hc : n.Covers d) :
    n.IsPrincipal solved d := by
  refine ⟨hn, ?_⟩
  intro m hm v hv
  exact ⟨v, hc v (hm.2 v hv), fun _ _ => rfl, fun _ _ => rfl⟩

/-- HM(X)'s principal constraint property, separate from the cylindric
constraint laws. -/
def PrincipalConstraintProperty (X : ConstraintSystem)
    (solved : X.Formula → Prop) : Prop :=
  (∀ r : X.Formula, solved r → ∃ v, X.holds r v) ∧
    ∀ d : X.Formula,
      (¬ ∃ n : X.NormalForm, n.IsNormalForm solved d) ∨
        ∃ n : X.NormalForm, n.IsPrincipal solved d

structure PrincipalNormalizer (X : ConstraintSystem) where
  solved : X.Formula → Prop
  solved_satisfiable : ∀ r, solved r → ∃ v, X.holds r v
  normalize : X.Formula → Option X.NormalForm
  principal_result : ∀ d n, normalize d = some n →
    n.IsPrincipal solved d
  failure : ∀ d, normalize d = none ↔
    ¬ ∃ n : X.NormalForm, n.IsNormalForm solved d

theorem PrincipalNormalizer.implies_property {X : ConstraintSystem}
    (N : X.PrincipalNormalizer) : X.PrincipalConstraintProperty N.solved := by
  constructor
  · exact N.solved_satisfiable
  intro d
  cases h : N.normalize d with
  | none => exact Or.inl ((N.failure d).mp h)
  | some n => exact Or.inr ⟨n, N.principal_result d n h⟩

theorem PrincipalNormalizer.success_has_solution {X : ConstraintSystem}
    (N : X.PrincipalNormalizer) (d : X.Formula)
    (n : X.NormalForm) (h : N.normalize d = some n) :
    ∃ v, X.holds d v := by
  obtain ⟨w, hw⟩ := N.solved_satisfiable n.residual
    (N.principal_result d n h).1.1
  exact ⟨w.pullbackSubst n.subst,
    (N.principal_result d n h).1.2 _ ⟨w, hw, rfl⟩⟩

/-- A qualified computation type over the complete constraint domain X. -/
structure ComputationScheme (X : ConstraintSystem) where
  typeVars : Finset Nat
  effectVars : Finset Nat
  condition : X.Formula
  result : Ty
  effect : Effect

def ComputationScheme.GroundInstance {X : ConstraintSystem}
    (σ : X.ComputationScheme) (ρ : Valuation)
    (t : GroundTy) (η : Finset Op) : Prop :=
  ∃ v : Valuation,
    (∀ i, i ∉ σ.typeVars → v.types i = ρ.types i) ∧
    (∀ i, i ∉ σ.effectVars → v.effects i = ρ.effects i) ∧
    X.holds σ.condition v ∧
    σ.result.eval v = t ∧
    σ.effect.eval v.effects = η

def ComputationScheme.Subsumes {X : ConstraintSystem}
    (general specific : X.ComputationScheme) : Prop :=
  ∀ ρ t η, specific.GroundInstance ρ t η →
    general.GroundInstance ρ t η

theorem ComputationScheme.subsumes_refl {X : ConstraintSystem}
    (σ : X.ComputationScheme) : σ.Subsumes σ :=
  fun _ _ _ h => h

theorem ComputationScheme.subsumes_trans {X : ConstraintSystem}
    {a b c : X.ComputationScheme} (hab : a.Subsumes b)
    (hbc : b.Subsumes c) : a.Subsumes c :=
  fun ρ t η hc => hab ρ t η (hbc ρ t η hc)

end ConstraintSystem

/-- The existing syntax is one concrete constraint system.  This instance
also provides the bridge used to compare the older proofs with the HM(X)
interface.  The carrier contains all type, effect and class constraints. -/
def syntaxConstraintSystem (D : Domain) (h : LawfulSupport D) :
    ConstraintSystem where
  Formula := Constraint D
  holds := fun c v => c.holds v
  trivial := .top
  combine := .and
  hideType := .exTy
  hideEffect := .exEff
  equalType := .typeEq
  includedEffect := .effectLe
  excludes := .lacks
  handlerClause := fun bt be lt le c =>
    Constraint.close bt be (Constraint.project lt le c)
  freeTypes := Constraint.fvTypes
  freeEffects := Constraint.fvEffects
  trivial_iff := by intro v; rfl
  combine_iff := by intro c d v; rfl
  hideType_iff := by intro i c v; rfl
  hideEffect_iff := by intro i c v; rfl
  projection_iff := by
    intro bt be c v
    exact Constraint.project_holds_iff bt be c v
  equalType_iff := by intro a b v; rfl
  includedEffect_iff := by intro a b v; rfl
  excludes_iff := by intro op ε v; rfl
  handlerClause_iff := by
    intro bt be lt le c v
    exact Constraint.close_project_holds_iff bt be lt le c v
  free_support := by
    intro c v w ht he
    exact Constraint.holds_support h c v w ht he

theorem syntaxSystem_lawfulFV (D : Domain) (h : LawfulSupport D) :
    ConstraintSystem.LawfulFV (syntaxConstraintSystem D h) := by
  constructor
  · intro c d i hi
    simpa [syntaxConstraintSystem, Constraint.fvTypes] using hi
  · intro c d i hi
    simpa [syntaxConstraintSystem, Constraint.fvEffects] using hi
  · intro bt be c
    change Constraint D at c
    change (Constraint.project bt be c).fvTypes ⊆ c.fvTypes \ bt
    intro i hi
    rw [Constraint.project_fvTypes] at hi
    exact hi
  · intro bt be c
    change Constraint D at c
    change (Constraint.project bt be c).fvEffects ⊆ c.fvEffects \ be
    intro i hi
    rw [Constraint.project_fvEffects] at hi
    exact hi
  · intro bt be lt le c
    change Constraint D at c
    change (Constraint.close bt be
      (Constraint.project lt le c)).fvTypes ⊆ c.fvTypes \ (bt ∪ lt)
    intro i hi
    rw [Constraint.close_fvTypes, Constraint.project_fvTypes] at hi
    simp only [Finset.mem_sdiff, Finset.mem_union] at hi ⊢
    exact ⟨hi.1.1, fun h => h.elim hi.2 hi.1.2⟩
  · intro bt be lt le c
    change Constraint D at c
    change (Constraint.close bt be
      (Constraint.project lt le c)).fvEffects ⊆ c.fvEffects \ (be ∪ le)
    intro i hi
    rw [Constraint.close_fvEffects, Constraint.project_fvEffects] at hi
    simp only [Finset.mem_sdiff, Finset.mem_union] at hi ⊢
    exact ⟨hi.1.1, fun h => h.elim hi.2 hi.1.2⟩

theorem syntaxSystem_lawfulGeneratedFV (D : Domain)
    (h : LawfulSupport D) :
    ConstraintSystem.LawfulGeneratedFV
      (syntaxConstraintSystem D h) := by
  constructor
  · simp [syntaxConstraintSystem, Constraint.fvTypes]
  · simp [syntaxConstraintSystem, Constraint.fvEffects]
  · intro a b
    simp [syntaxConstraintSystem, Constraint.fvTypes]
  · intro a b
    simp [syntaxConstraintSystem, Constraint.fvEffects]
  · intro a b
    simp [syntaxConstraintSystem, Constraint.fvTypes]
  · intro a b
    simp [syntaxConstraintSystem, Constraint.fvEffects]
  · intro op ε
    simp [syntaxConstraintSystem, Constraint.fvTypes]
  · intro op ε
    simp [syntaxConstraintSystem, Constraint.fvEffects]

def classConstraintSystem (I : ClassEnv) : ConstraintSystem :=
  syntaxConstraintSystem (classDomain I) (classDomain_lawfulSupport I)

def syntaxNormalForm (D : Domain) (h : LawfulSupport D)
    (n : SystemFXi.EHMX.NormalForm D) :
    (syntaxConstraintSystem D h).NormalForm :=
  ⟨n.residual, n.subst⟩

def syntaxComputationScheme (D : Domain) (h : LawfulSupport D)
    (σ : SystemFXi.EHMX.ComputationScheme D) :
    (syntaxConstraintSystem D h).ComputationScheme :=
  ⟨σ.typeVars, σ.effectVars, σ.predicates, σ.result, σ.effect⟩

theorem syntaxComputationScheme_instance_iff (D : Domain)
    (h : LawfulSupport D) (σ : SystemFXi.EHMX.ComputationScheme D)
    (ρ : Valuation) (t : GroundTy) (η : Finset Op) :
    (syntaxComputationScheme D h σ).GroundInstance ρ t η ↔
      σ.GroundInstance ρ t η := by
  rfl

theorem syntaxComputationScheme_subsumes_iff (D : Domain)
    (h : LawfulSupport D)
    (a b : SystemFXi.EHMX.ComputationScheme D) :
    (syntaxComputationScheme D h a).Subsumes
      (syntaxComputationScheme D h b) ↔ a.Subsumes b := by
  rfl

theorem syntaxNormalForm_principal_iff (D : Domain)
    (h : LawfulSupport D) (solved : Constraint D → Prop)
    (d : Constraint D) (n : SystemFXi.EHMX.NormalForm D) :
    (syntaxNormalForm D h n).IsPrincipal solved d ↔
      n.IsPrincipal solved d := by
  simp only [ConstraintSystem.NormalForm.IsPrincipal,
    SystemFXi.EHMX.NormalForm.IsPrincipal,
    ConstraintSystem.NormalForm.IsNormalForm,
    SystemFXi.EHMX.NormalForm.IsNormalForm,
    ConstraintSystem.NormalForm.MoreGeneralThanOn,
    SystemFXi.EHMX.NormalForm.MoreGeneralThanOn,
    ConstraintSystem.NormalForm.SoundFor,
    SystemFXi.EHMX.NormalForm.SoundFor,
    ConstraintSystem.NormalForm.Represents,
    SystemFXi.EHMX.NormalForm.Represents,
    ConstraintSystem.SemFreeType, ConstraintSystem.SemFreeEffect,
    Constraint.semFreeType, Constraint.semFreeEffect,
    syntaxNormalForm, syntaxConstraintSystem]
  constructor
  · rintro ⟨hn, hg⟩
    refine ⟨hn, ?_⟩
    intro m hm
    exact hg ⟨m.residual, m.subst⟩ hm
  · rintro ⟨hn, hg⟩
    refine ⟨hn, ?_⟩
    intro m hm
    exact hg ⟨m.residual, m.subst⟩ hm

/-- The existing abstract normalizer is an instance of the constraint-system
normalizer interface. Its principal-normal-form theorem is preserved. -/
def syntaxPrincipalNormalizer (D : Domain) (h : LawfulSupport D)
    (N : SystemFXi.EHMX.PrincipalNormalizer D) :
    (syntaxConstraintSystem D h).PrincipalNormalizer where
  solved := N.solved
  solved_satisfiable := N.solved_satisfiable
  normalize := fun d => (N.normalize d).map (syntaxNormalForm D h)
  principal_result := by
    intro d n hn
    cases hz : N.normalize d with
    | none => simp [hz] at hn
    | some old =>
        simp [hz] at hn
        cases hn
        exact (syntaxNormalForm_principal_iff D h N.solved d old).2
          (N.principal_result d old hz)
  failure := by
    intro d
    constructor
    · intro hn
      have hold : N.normalize d = none := by
        cases hz : N.normalize d with
        | none => rfl
        | some old => simp [syntaxNormalForm, hz] at hn
      intro hnormal
      obtain ⟨n, hn⟩ := hnormal
      apply (N.fail_iff_no_normal_form d).mp hold
      exact ⟨⟨n.residual, n.subst⟩, hn⟩
    · intro hnone
      have hold : N.normalize d = none := by
        apply (N.fail_iff_no_normal_form d).2
        intro hnormal
        obtain ⟨n, hn⟩ := hnormal
        apply hnone
        exact ⟨syntaxNormalForm D h n, hn⟩
      simp [hold]

theorem syntaxConstraintSystem_project (D : Domain) (h : LawfulSupport D)
    (types effects : Finset Nat) (c : Constraint D) :
    (syntaxConstraintSystem D h).project types effects c =
      Constraint.project types effects c := rfl

/-- When the ambient constraint does not depend on the operation's bound
names, one fresh rigid instance of the clause checks every instance. -/
theorem syntaxClauseValid_iff_closed (D : Domain) (h : LawfulSupport D)
    (ambient clause : Constraint D)
    (rigidTypes rigidEffects localTypes localEffects : Finset Nat)
    (ht : Disjoint rigidTypes ambient.fvTypes)
    (he : Disjoint rigidEffects ambient.fvEffects) :
    (syntaxConstraintSystem D h).ClauseValid ambient clause
      localTypes localEffects ↔
    ambient.Entails
      (Constraint.close rigidTypes rigidEffects
        (Constraint.project localTypes localEffects clause)) := by
  let p := Constraint.project localTypes localEffects clause
  change ambient.Entails p ↔
    ambient.Entails (Constraint.close rigidTypes rigidEffects p)
  constructor
  · intro hc v hav
    apply (Constraint.close_holds_iff rigidTypes rigidEffects p v).2
    intro ft fe hft hfe
    have hta : ∀ i ∈ ambient.fvTypes, ft i = v.types i := by
      intro i hi
      apply hft
      intro hri
      exact (Finset.disjoint_left.mp ht hri hi).elim
    have hea : ∀ i ∈ ambient.fvEffects, fe i = v.effects i := by
      intro i hi
      apply hfe
      intro hri
      exact (Finset.disjoint_left.mp he hri hi).elim
    have hav' : ambient.holds ⟨ft, fe⟩ :=
      (Constraint.holds_support h ambient v ⟨ft, fe⟩
        (fun i hi => (hta i hi).symm)
        (fun i hi => (hea i hi).symm)).mp hav
    exact hc ⟨ft, fe⟩ hav'
  · intro hc v hav
    exact (Constraint.close_current rigidTypes rigidEffects p) v
      (hc v hav)

/-- The second instance has the same type/effect/handler constraints and no
additional class tokens. -/
def emptyDomain : Domain where
  Pred := PEmpty
  rename := fun _ _ p => nomatch p
  holds := fun _ p => nomatch p
  fvTypes := fun p => nomatch p
  fvEffects := fun p => nomatch p

theorem emptyDomain_lawfulSupport : LawfulSupport emptyDomain := by
  constructor
  intro p
  exact PEmpty.elim p

theorem emptyDomain_lawfulRename : LawfulRename emptyDomain := by
  constructor
  intro ρ η p
  exact PEmpty.elim p

theorem emptyDomain_lawfulFVRename : LawfulFVRename emptyDomain := by
  constructor
  · intro ρ η p
    exact PEmpty.elim p
  · intro ρ η p
    exact PEmpty.elim p

def emptyConstraintSystem : ConstraintSystem :=
  syntaxConstraintSystem emptyDomain emptyDomain_lawfulSupport

theorem classSystem_split_semantics (I : ClassEnv) (op : Op)
    (input rest : Effect) (v : Valuation) :
    (classConstraintSystem I).holds
      ((classConstraintSystem I).split op input rest) v ↔
      rest.eval v.effects ⊆ input.eval v.effects ∧
      input.eval v.effects ⊆
        (Poly.Effect.singleton op ∪ rest).eval v.effects ∧
      op ∉ rest.eval v.effects := by
  exact (classConstraintSystem I).split_iff op input rest v

/-- The previously proved principal-generation theorem applies to the
empty-predicate concrete system as well as the Eq/Show instance. -/
theorem emptySystem_generate_principal
    {sig : Signature} (hClosed : sig.Closed)
    (Γ : Context emptyDomain) (e : Expr) (s : Supply)
    {C : Constraint emptyDomain} {τ : Ty} {ε : Effect}
    (hTyping : Typing sig emptyDomain C Γ e τ ε) :
    ∃ r : Output emptyDomain,
      generateFresh sig emptyDomain Γ e s = some r ∧
      Typing sig emptyDomain r.constraints Γ e r.ty r.effect ∧
      ∀ (D : Constraint emptyDomain) (a : Ty) (η : Effect),
        Typing sig emptyDomain D Γ e a η →
        r.MoreGeneralThan Γ D a η :=
  hTyping.generateFresh_principal emptyDomain_lawfulRename
    emptyDomain_lawfulSupport emptyDomain_lawfulFVRename
    hClosed Γ e s

theorem classSystem_generate_principal (I : ClassEnv)
    {sig : Signature} (hClosed : sig.Closed)
    (Γ : Context (classDomain I)) (e : Expr) (s : Supply)
    {C : Constraint (classDomain I)} {τ : Ty} {ε : Effect}
    (hTyping : Typing sig (classDomain I) C Γ e τ ε) :
    ∃ r : Output (classDomain I),
      generateFresh sig (classDomain I) Γ e s = some r ∧
      Typing sig (classDomain I) r.constraints Γ e r.ty r.effect ∧
      ∀ (D : Constraint (classDomain I)) (a : Ty) (η : Effect),
        Typing sig (classDomain I) D Γ e a η →
        r.MoreGeneralThan Γ D a η :=
  hTyping.generateFresh_principal (classDomain_lawfulRename I)
    (classDomain_lawfulSupport I) (classDomain_lawfulFVRename I)
    hClosed Γ e s

end SystemFXi.EHMX
