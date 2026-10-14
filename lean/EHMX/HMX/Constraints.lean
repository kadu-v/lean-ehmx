import EHMX.HMX.TypeDomain

namespace EHMX.HMX

/-- The comparison parameter of HM(X). Effects on arrows are held equal;
general effect subtyping is not an assumption of this extension. -/
structure TypeOrder (T : TypeDomain) where
  le : T.Value → T.Value → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  antisymm : ∀ {a b}, le a b → le b a → a = b
  arrow : ∀ {a a' b b'} e, le a' a → le b b' →
    le (T.groundArrow a e b) (T.groundArrow a' e b')

def TypeOrder.equality (T : TypeDomain) : TypeOrder T where
  le := Eq
  refl := Eq.refl
  trans := Eq.trans
  antisymm := fun h _ => h
  arrow := by intro a a' b b' e ha hb; cases ha; cases hb; rfl

/-- First-order constraints over the chosen type algebra. `support` is an
implementation bound. Semantic free variables are defined below by projection,
as in the paper, rather than identified with that bound. -/
structure Constraints (T : TypeDomain) (O : TypeOrder T) where
  Formula : Type
  holds : Formula → Valuation T.Value → Prop
  top : Formula
  and : Formula → Formula → Formula
  existsNames : Names → Formula → Formula
  eq : T.Term → T.Term → Formula
  le : T.Term → T.Term → Formula
  effectLe : Effect → Effect → Formula
  lacks : Op → Effect → Formula
  clause : Names → Names → Formula → Formula
  subst : Substitution T → Formula → Formula
  support : Formula → Names
  holds_top : ∀ v, holds top v ↔ True
  holds_and : ∀ c d v, holds (and c d) v ↔ holds c v ∧ holds d v
  holds_exists : ∀ a c v, holds (existsNames a c) v ↔
    ∃ w, w.AgreeOutside v a ∧ holds c w
  holds_eq : ∀ a b v, holds (eq a b) v ↔ T.eval v a = T.eval v b
  holds_le : ∀ a b v, holds (le a b) v ↔ O.le (T.eval v a) (T.eval v b)
  holds_effectLe : ∀ a b v, holds (effectLe a b) v ↔
    a.eval v.effects ⊆ b.eval v.effects
  holds_lacks : ∀ op a v, holds (lacks op a) v ↔ op ∉ a.eval v.effects
  holds_clause : ∀ rigid witnesses c v, holds (clause rigid witnesses c) v ↔
    ∀ w, w.AgreeOutside v rigid →
      ∃ u, u.AgreeOutside w witnesses ∧ holds c u
  holds_subst : ∀ s c v, holds (subst s c) v ↔ holds c (s.pullback v)
  holds_support : ∀ c v w, v.AgreeOn w (support c) → (holds c v ↔ holds c w)

namespace Constraints
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

def Entails (c d : X.Formula) : Prop := ∀ v, X.holds c v → X.holds d v
def Equivalent (c d : X.Formula) : Prop := X.Entails c d ∧ X.Entails d c
def Satisfiable (c : X.Formula) : Prop := ∃ v, X.holds c v
def FreeType (c : X.Formula) (i : Nat) : Prop :=
  ¬ X.Equivalent (X.existsNames ⟨{i}, ∅⟩ c) c
def FreeEffect (c : X.Formula) (i : Nat) : Prop :=
  ¬ X.Equivalent (X.existsNames ⟨∅, {i}⟩ c) c

theorem entails_refl (c : X.Formula) : X.Entails c c := fun _ h => h
theorem entails_trans {a b c : X.Formula} (h : X.Entails a b)
    (k : X.Entails b c) : X.Entails a c := fun v hv => k v (h v hv)
theorem entails_left (c d : X.Formula) : X.Entails (X.and c d) c :=
  fun v h => ((X.holds_and c d v).mp h).1
theorem entails_right (c d : X.Formula) : X.Entails (X.and c d) d :=
  fun v h => ((X.holds_and c d v).mp h).2
theorem exists_intro (a : Names) (c : X.Formula) : X.Entails c (X.existsNames a c) := by
  intro v hv
  exact (X.holds_exists a c v).mpr ⟨v, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, hv⟩

theorem exists_mono (a : Names) {c d : X.Formula} (h : X.Entails c d) :
    X.Entails (X.existsNames a c) (X.existsNames a d) := by
  intro v hv
  obtain ⟨w, hw, hc⟩ := (X.holds_exists a c v).mp hv
  exact (X.holds_exists a d v).mpr ⟨w, hw, h w hc⟩

/-- The original paper restricts every constraint in a valid judgment to be
equivalent to a solved form. This is not a global assumption that `top ∈ S`. -/
def Admissible (solved : X.Formula → Prop) (c : X.Formula) : Prop :=
  ∃ d, solved d ∧ X.Equivalent c d

end Constraints
variable {T : TypeDomain}

private structure SupportedFormula (T : TypeDomain) where
  test : Valuation T.Value → Prop
  support : Names
  stable : ∀ v w, v.AgreeOn w support → (test v ↔ test w)

private def SupportedFormula.neg (c : SupportedFormula T) : SupportedFormula T :=
  ⟨fun v => ¬ c.test v, c.support, fun v w h => not_congr (c.stable v w h)⟩

private def SupportedFormula.conj (c d : SupportedFormula T) : SupportedFormula T :=
  ⟨fun v => c.test v ∧ d.test v, c.support.union d.support,
    fun v w h => and_congr
      (c.stable v w (h.mono (Names.subset_union_left _ _)))
      (d.stable v w (h.mono (Names.subset_union_right _ _)))⟩

private def SupportedFormula.project (a : Names) (c : SupportedFormula T) : SupportedFormula T := by
  refine ⟨fun v => ∃ w, w.AgreeOutside v a ∧ c.test w, c.support, ?_⟩
  have go (v w : Valuation T.Value) (h : v.AgreeOn w c.support)
      (hv : ∃ z, z.AgreeOutside v a ∧ c.test z) :
      ∃ z, z.AgreeOutside w a ∧ c.test z := by
    obtain ⟨z, hz, hc⟩ := hv
    refine ⟨w.patch z a, Valuation.patch_agreeOutside _ _ _, (c.stable _ z ?_).mpr hc⟩
    constructor
    · intro i hi
      by_cases ha : i ∈ a.types
      · simp [Valuation.patch, ha]
      · simp [Valuation.patch, ha, hz.1 i ha, h.1 i hi]
    · intro i hi
      by_cases ha : i ∈ a.effects
      · simp [Valuation.patch, ha]
      · simp [Valuation.patch, ha, hz.2 i ha, h.2 i hi]
  intro v w h
  exact ⟨go v w h, go w v ⟨fun i hi => (h.1 i hi).symm, fun i hi => (h.2 i hi).symm⟩⟩

private def SupportedFormula.compare (r : T.Value → T.Value → Prop)
    (a b : T.Term) : SupportedFormula T :=
  ⟨fun v => r (T.eval v a) (T.eval v b), (T.support a).union (T.support b), by
    intro v w h
    rw [T.eval_support v w a (h.mono (Names.subset_union_left _ _)),
      T.eval_support v w b (h.mono (Names.subset_union_right _ _))]⟩

private def SupportedFormula.substitute (s : Substitution T) (c : SupportedFormula T) :
    SupportedFormula T := by
  let a : Names := c.support.union
    ⟨s.domain.types.biUnion (fun i => (T.support (s.types i)).types),
     s.domain.types.biUnion (fun i => (T.support (s.types i)).effects) ∪
     s.domain.effects.biUnion (fun i => (s.effects i).vars)⟩
  refine ⟨fun v => c.test (s.pullback v), a, ?_⟩
  intro v w h
  apply c.stable
  constructor
  · intro i hi
    by_cases hd : i ∈ s.domain.types
    · apply T.eval_support
      constructor
      · intro j hj
        exact h.1 j (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hd, hj⟩))
      · intro j hj
        exact h.2 j (Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨i, hd, hj⟩)))
    · simpa [Substitution.pullback, s.types_outside i hd, T.eval_var] using
        h.1 i (Finset.mem_union_left _ hi)
  · intro i hi
    by_cases hd : i ∈ s.domain.effects
    · apply Effect.eval_support
      intro j hj
      exact h.2 j (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨i, hd, hj⟩)))
    · simpa [Substitution.pullback, s.effects_outside i hd, Effect.eval, Effect.var] using
        h.2 i (Finset.mem_union_left _ hi)

/-- The constraint interface has a concrete model for every type domain and
order: predicates with a finite support, interpreted at valuations. -/
def Constraints.semantic (T : TypeDomain) (O : TypeOrder T) : Constraints T O where
  Formula := SupportedFormula T
  holds := SupportedFormula.test
  top := ⟨fun _ => True, Names.empty, by intros; rfl⟩
  and := SupportedFormula.conj
  existsNames := SupportedFormula.project
  eq := SupportedFormula.compare Eq
  le := SupportedFormula.compare O.le
  effectLe := fun a b => ⟨fun v => a.eval v.effects ⊆ b.eval v.effects,
    ⟨∅, a.vars ∪ b.vars⟩, by
      intro v w h
      rw [Effect.eval_support a v.effects w.effects (fun i hi => h.2 i (Finset.mem_union_left _ hi)),
        Effect.eval_support b v.effects w.effects (fun i hi => h.2 i (Finset.mem_union_right _ hi))]⟩
  lacks := fun op a => ⟨fun v => op ∉ a.eval v.effects, ⟨∅, a.vars⟩, by
    intro v w h; rw [Effect.eval_support a v.effects w.effects h.2]⟩
  clause := fun a b c => ((c.project b).neg.project a).neg
  subst := SupportedFormula.substitute
  support := SupportedFormula.support
  holds_top := by intros; rfl
  holds_and := by intros; rfl
  holds_exists := by intros; rfl
  holds_eq := by intros; rfl
  holds_le := by intros; rfl
  holds_effectLe := by intros; rfl
  holds_lacks := by intros; rfl
  holds_clause := by
    intro a b c v
    classical
    simp [SupportedFormula.neg, SupportedFormula.project]
  holds_subst := by intros; rfl
  holds_support := SupportedFormula.stable

/-- Add an interpreted predicate to the semantic model by proving its finite
support. This exposes no unchecked constraint or new semantic axiom. -/
def Constraints.semanticAtom (T : TypeDomain) (O : TypeOrder T)
    (support : Names) (test : Valuation T.Value → Prop)
    (stable : ∀ v w, v.AgreeOn w support → (test v ↔ test w)) :
    (Constraints.semantic T O).Formula := ⟨test, support, stable⟩

theorem Constraints.holds_semanticAtom (T : TypeDomain) (O : TypeOrder T)
    (support : Names) (test : Valuation T.Value → Prop)
    (stable : ∀ v w, v.AgreeOn w support → (test v ↔ test w))
    (v : Valuation T.Value) :
    (Constraints.semantic T O).holds (Constraints.semanticAtom T O support test stable) v ↔ test v :=
  Iff.rfl

end EHMX.HMX
