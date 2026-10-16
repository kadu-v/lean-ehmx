import EHMX.HMX.TypeSyntax

/-!
The logical constraint interface of HM(X), dissertation Definitions 2--5.

Entailment is supplied by the theory. It is not defined by truth in a fixed
ground interpretation. `existsNames` is the finite, two-sorted version of
the paper's single-variable projection; empty/union express finite iteration.
The type/effect distinction is the EHMX extension.
-/
namespace EHMX.HMX

structure ConstraintTheory where
  Formula : Type
  Entails : Formula → Formula → Prop
  top : Formula
  and : Formula → Formula → Formula
  existsNames : Names → Formula → Formula
  support : Formula → Names
  entails_refl : ∀ c, Entails c c
  entails_trans : ∀ {a b c}, Entails a b → Entails b c → Entails a c
  entails_top : ∀ c, Entails c top
  entails_left : ∀ c d, Entails (and c d) c
  entails_right : ∀ c d, Entails (and c d) d
  entails_and : ∀ {c d e}, Entails c d → Entails c e → Entails c (and d e)
  exists_intro : ∀ a c, Entails c (existsNames a c)
  exists_mono : ∀ a {c d}, Entails c d → Entails (existsNames a c) (existsNames a d)
  exists_absorb : ∀ a c d,
    Entails (existsNames a (and c (existsNames a d)))
      (and (existsNames a c) (existsNames a d)) ∧
    Entails (and (existsNames a c) (existsNames a d))
      (existsNames a (and c (existsNames a d)))
  exists_comm : ∀ a b c,
    Entails (existsNames a (existsNames b c)) (existsNames b (existsNames a c))
  exists_empty : ∀ c, Entails (existsNames Names.empty c) c
  exists_union : ∀ a b c,
    Entails (existsNames (a.union b) c) (existsNames a (existsNames b c)) ∧
    Entails (existsNames a (existsNames b c)) (existsNames (a.union b) c)
  project_outside_support : ∀ a c, a.Disjoint (support c) →
    Entails (existsNames a c) c

namespace ConstraintTheory
variable (X : ConstraintTheory)

def Equivalent (c d : X.Formula) : Prop := X.Entails c d ∧ X.Entails d c

def FreeType (c : X.Formula) (i : Nat) : Prop :=
  ¬ X.Equivalent (X.existsNames ⟨{i}, ∅⟩ c) c

def FreeEffect (c : X.Formula) (i : Nat) : Prop :=
  ¬ X.Equivalent (X.existsNames ⟨∅, {i}⟩ c) c

noncomputable def freeNames (c : X.Formula) : Names := by
  classical
  exact ⟨(X.support c).types.filter (X.FreeType c),
    (X.support c).effects.filter (X.FreeEffect c)⟩

/-- Definition 5. This is validity of the existential closure, not existence
of one satisfying valuation in one selected interpretation. -/
def Satisfiable (c : X.Formula) : Prop :=
  X.Entails X.top (X.existsNames (X.freeNames c) c)

def Admissible (S : X.Formula → Prop) (c : X.Formula) : Prop :=
  ∃ d, S d ∧ X.Equivalent c d

theorem equivalent_refl (c : X.Formula) : X.Equivalent c c :=
  ⟨X.entails_refl c, X.entails_refl c⟩

theorem equivalent_symm {c d : X.Formula} (h : X.Equivalent c d) :
    X.Equivalent d c := ⟨h.2, h.1⟩

theorem equivalent_trans {c d e : X.Formula}
    (h : X.Equivalent c d) (k : X.Equivalent d e) : X.Equivalent c e :=
  ⟨X.entails_trans h.1 k.1, X.entails_trans k.2 h.2⟩

theorem and_mono {a b c d : X.Formula}
    (h : X.Entails a b) (k : X.Entails c d) : X.Entails (X.and a c) (X.and b d) :=
  X.entails_and (X.entails_trans (X.entails_left _ _) h)
    (X.entails_trans (X.entails_right _ _) k)

theorem and_comm (c d : X.Formula) : X.Equivalent (X.and c d) (X.and d c) :=
  ⟨X.entails_and (X.entails_right _ _) (X.entails_left _ _),
   X.entails_and (X.entails_right _ _) (X.entails_left _ _)⟩

theorem and_top (c : X.Formula) : X.Equivalent (X.and c X.top) c :=
  ⟨X.entails_left _ _, X.entails_and (X.entails_refl _) (X.entails_top _)⟩

theorem top_and (c : X.Formula) : X.Equivalent (X.and X.top c) c :=
  ⟨X.entails_right _ _, X.entails_and (X.entails_top _) (X.entails_refl _)⟩

theorem exists_congr (a : Names) {c d : X.Formula} (h : X.Equivalent c d) :
    X.Equivalent (X.existsNames a c) (X.existsNames a d) :=
  ⟨X.exists_mono a h.1, X.exists_mono a h.2⟩

theorem exists_top (a : Names) : X.Equivalent (X.existsNames a X.top) X.top :=
  ⟨X.entails_top _, X.exists_intro _ _⟩

theorem exists_idem (a : Names) (c : X.Formula) :
    X.Equivalent (X.existsNames a (X.existsNames a c)) (X.existsNames a c) := by
  have h := X.exists_absorb a X.top c
  have e := X.exists_congr a (X.top_and (X.existsNames a c))
  exact ⟨X.entails_trans e.2 (X.entails_trans h.1 (X.entails_right _ _)),
    X.exists_intro _ _⟩

theorem freeType_mem_support {c : X.Formula} {i : Nat} (hi : X.FreeType c i) :
    i ∈ (X.support c).types := by
  classical
  by_contra hn
  apply hi
  refine ⟨X.project_outside_support _ _ ?_, X.exists_intro _ _⟩
  exact ⟨by simpa using hn, by simp⟩

theorem freeEffect_mem_support {c : X.Formula} {i : Nat} (hi : X.FreeEffect c i) :
    i ∈ (X.support c).effects := by
  classical
  by_contra hn
  apply hi
  refine ⟨X.project_outside_support _ _ ?_, X.exists_intro _ _⟩
  exact ⟨by simp, by simpa using hn⟩

@[simp] theorem mem_freeNames_types (c : X.Formula) (i : Nat) :
    i ∈ (X.freeNames c).types ↔ X.FreeType c i := by
  classical
  simp only [freeNames, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨X.freeType_mem_support h, h⟩⟩

@[simp] theorem mem_freeNames_effects (c : X.Formula) (i : Nat) :
    i ∈ (X.freeNames c).effects ↔ X.FreeEffect c i := by
  classical
  simp only [freeNames, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨X.freeEffect_mem_support h, h⟩⟩

theorem admissible_equivalent {S : X.Formula → Prop} {c d : X.Formula}
    (hc : X.Admissible S c) (h : X.Equivalent d c) : X.Admissible S d := by
  obtain ⟨r, hr, eqv⟩ := hc
  exact ⟨r, hr, X.equivalent_trans h eqv⟩

/-- Theorem hypotheses on solved forms, deliberately without conjunction
closure. Renaming is specified with the term operations in TermConstraintTheory. -/
def ProjectionClosed (S : X.Formula → Prop) : Prop :=
  ∀ a c, X.Admissible S c → X.Admissible S (X.existsNames a c)

/-- Logical freshness is absence from the free names of Definition 4. -/
def Avoids (c : X.Formula) (a : Names) : Prop :=
  (∀ i ∈ a.types, ¬ X.FreeType c i) ∧
  (∀ i ∈ a.effects, ¬ X.FreeEffect c i)

theorem avoids_iff_disjoint (c : X.Formula) (a : Names) :
    X.Avoids c a ↔ a.Disjoint (X.freeNames c) := by
  classical
  simp only [Avoids, Names.Disjoint, Finset.disjoint_left,
    mem_freeNames_types, mem_freeNames_effects]

theorem exists_of_avoids {c : X.Formula} {a : Names}
    (fresh : X.Avoids c a) : X.Equivalent (X.existsNames a c) c := by
  classical
  have types (s : Finset Nat) (h : ∀ i ∈ s, ¬ X.FreeType c i) :
      X.Entails (X.existsNames ⟨s, ∅⟩ c) c := by
    induction s using Finset.induction_on with
    | empty => exact X.exists_empty c
    | @insert i s hi ih =>
      have one : X.Equivalent (X.existsNames ⟨{i}, ∅⟩ c) c :=
        Classical.not_not.mp (h i (Finset.mem_insert_self _ _))
      have rest := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have parts := (X.exists_union ⟨{i}, ∅⟩ ⟨s, ∅⟩ c).1
      exact X.entails_trans (by simpa [Names.union] using parts)
        (X.entails_trans (X.exists_mono _ rest) one.1)
  have effects (s : Finset Nat) (h : ∀ i ∈ s, ¬ X.FreeEffect c i) :
      X.Entails (X.existsNames ⟨∅, s⟩ c) c := by
    induction s using Finset.induction_on with
    | empty => exact X.exists_empty c
    | @insert i s hi ih =>
      have one : X.Equivalent (X.existsNames ⟨∅, {i}⟩ c) c :=
        Classical.not_not.mp (h i (Finset.mem_insert_self _ _))
      have rest := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have parts := (X.exists_union ⟨∅, {i}⟩ ⟨∅, s⟩ c).1
      exact X.entails_trans (by simpa [Names.union] using parts)
        (X.entails_trans (X.exists_mono _ rest) one.1)
  refine ⟨?_, X.exists_intro _ _⟩
  have split := (X.exists_union ⟨a.types, ∅⟩ ⟨∅, a.effects⟩ c).1
  exact X.entails_trans (by simpa [Names.union] using split)
    (X.entails_trans (X.exists_mono _ (effects _ fresh.2)) (types _ fresh.1))

theorem exists_and_of_avoids {a : Names} {c d : X.Formula}
    (fresh : X.Avoids c a) :
    X.Equivalent (X.existsNames a (X.and c d)) (X.and c (X.existsNames a d)) := by
  have hc := X.exists_of_avoids fresh
  have h := X.exists_absorb a d c
  constructor
  · apply X.entails_trans
      (X.exists_mono a (X.and_mono (X.exists_intro a c) (X.entails_refl d)))
    apply X.entails_trans (X.exists_mono a (X.and_comm _ _).1)
    exact X.entails_trans h.1
      (X.entails_and (X.entails_trans (X.entails_right _ _) hc.1) (X.entails_left _ _))
  · have initial := X.entails_and (X.entails_right c (X.existsNames a d))
      (X.entails_trans (X.entails_left _ _) hc.2)
    exact X.entails_trans initial (X.entails_trans h.2
      (X.entails_trans (X.exists_mono a (X.and_mono (X.entails_refl _) hc.1))
        (X.exists_mono a (X.and_comm _ _).1)))

/-- Used to project a comparison constraint without changing its outer assumptions. -/
theorem projected_entails_outer {a : Names} {c r : X.Formula}
    (fresh : X.Avoids c a) (h : X.Entails r c) :
    X.Entails (X.existsNames a r) c :=
  X.entails_trans (X.exists_mono a h) (X.exists_of_avoids fresh).1

theorem freeNames_equivalent {c d : X.Formula} (h : X.Equivalent c d) :
    X.freeNames c = X.freeNames d := by
  have eqv (a : Names) :
      X.Equivalent (X.existsNames a c) c ↔ X.Equivalent (X.existsNames a d) d :=
    ⟨fun k => X.equivalent_trans (X.equivalent_symm (X.exists_congr a h))
        (X.equivalent_trans k h),
      fun k => X.equivalent_trans (X.exists_congr a h)
        (X.equivalent_trans k (X.equivalent_symm h))⟩
  change Names.mk (X.freeNames c).types (X.freeNames c).effects =
    Names.mk (X.freeNames d).types (X.freeNames d).effects
  apply congrArg₂ Names.mk <;> apply Finset.ext <;> intro i
  · simp only [mem_freeNames_types, FreeType, eqv]
  · simp only [mem_freeNames_effects, FreeEffect, eqv]

theorem satisfiable_equivalent {c d : X.Formula} (h : X.Equivalent c d) :
    X.Satisfiable c ↔ X.Satisfiable d := by
  unfold Satisfiable
  rw [X.freeNames_equivalent h]
  exact ⟨fun k => X.entails_trans k (X.exists_mono _ h.1),
    fun k => X.entails_trans k (X.exists_mono _ h.2)⟩

/-- Projection closure and the original satisfiability definition supply
an admissible true constraint. It is not an extra solver assumption. -/
theorem admissible_top_of_solved {S : X.Formula → Prop}
    (sound : ∀ c, S c → X.Satisfiable c) (project : X.ProjectionClosed S)
    {r : X.Formula} (hr : S r) : X.Admissible S X.top := by
  have hp := project (X.freeNames r) r ⟨r, hr, X.equivalent_refl r⟩
  exact X.admissible_equivalent hp ⟨sound r hr, X.entails_top _⟩

theorem solved_truth_of_solved {S : X.Formula → Prop}
    (sound : ∀ c, S c → X.Satisfiable c) (project : X.ProjectionClosed S)
    {r : X.Formula} (hr : S r) : ∃ q, S q ∧ X.Entails X.top q := by
  obtain ⟨q, hq, eqv⟩ := X.admissible_top_of_solved sound project hr
  exact ⟨q, hq, eqv.1⟩

theorem not_freeType_exists_of_not_free {c : X.Formula} {a : Names} {i : Nat}
    (h : ¬ X.FreeType c i) : ¬ X.FreeType (X.existsNames a c) i := by
  classical
  have e := Classical.not_not.mp h
  apply not_not.mpr
  exact ⟨X.entails_trans (X.exists_comm ⟨{i}, ∅⟩ a c) (X.exists_mono a e.1),
    X.exists_intro _ _⟩

theorem not_freeEffect_exists_of_not_free {c : X.Formula} {a : Names} {i : Nat}
    (h : ¬ X.FreeEffect c i) : ¬ X.FreeEffect (X.existsNames a c) i := by
  classical
  have e := Classical.not_not.mp h
  apply not_not.mpr
  exact ⟨X.entails_trans (X.exists_comm ⟨∅, {i}⟩ a c) (X.exists_mono a e.1),
    X.exists_intro _ _⟩

theorem not_freeType_exists_of_bound (a : Names) (c : X.Formula)
    {i : Nat} (hi : i ∈ a.types) : ¬ X.FreeType (X.existsNames a c) i := by
  apply not_not.mpr
  refine ⟨?_, X.exists_intro _ _⟩
  have h := (X.exists_union ⟨{i}, ∅⟩ a c).2
  simpa [Names.union, Finset.insert_eq_of_mem hi] using h

theorem not_freeEffect_exists_of_bound (a : Names) (c : X.Formula)
    {i : Nat} (hi : i ∈ a.effects) : ¬ X.FreeEffect (X.existsNames a c) i := by
  apply not_not.mpr
  refine ⟨?_, X.exists_intro _ _⟩
  have h := (X.exists_union ⟨∅, {i}⟩ a c).2
  simpa [Names.union, Finset.insert_eq_of_mem hi] using h

theorem existential_closure_avoids (c : X.Formula) (a : Names) :
    X.Avoids (X.existsNames (X.freeNames c) c) a := by
  classical
  constructor
  · intro i _
    by_cases hi : X.FreeType c i
    · exact X.not_freeType_exists_of_bound _ _ ((X.mem_freeNames_types c i).mpr hi)
    · exact X.not_freeType_exists_of_not_free hi
  · intro i _
    by_cases hi : X.FreeEffect c i
    · exact X.not_freeEffect_exists_of_bound _ _ ((X.mem_freeNames_effects c i).mpr hi)
    · exact X.not_freeEffect_exists_of_not_free hi

theorem satisfiable_of_entails {c d : X.Formula} (hc : X.Satisfiable c)
    (h : X.Entails c d) : X.Satisfiable d := by
  apply X.entails_trans hc
  apply X.entails_trans (X.exists_intro (X.freeNames d) _)
  apply X.entails_trans (X.exists_comm _ _ _)
  apply X.entails_trans (X.exists_mono (X.freeNames c) (X.exists_mono (X.freeNames d) h))
  exact (X.exists_of_avoids (X.existential_closure_avoids d (X.freeNames c))).1

/-- HM(X) Lemma 2, obtained from the projection laws, without valuations. -/
theorem satisfiable_exists_iff (a : Names) (c : X.Formula) :
    X.Satisfiable (X.existsNames a c) ↔ X.Satisfiable c := by
  constructor
  · intro h
    apply X.entails_trans h
    apply X.entails_trans (X.exists_intro (X.freeNames c) _)
    apply X.entails_trans (X.exists_comm _ _ _)
    apply X.entails_trans (X.exists_mono _ (X.exists_comm _ _ _))
    apply X.entails_trans (X.exists_mono _
      (X.exists_of_avoids (X.existential_closure_avoids c a)).1)
    exact (X.exists_of_avoids (X.existential_closure_avoids c _)).1
  · intro h
    exact X.satisfiable_of_entails h (X.exists_intro a c)

theorem satisfiable_top : X.Satisfiable X.top :=
  X.exists_intro _ _

theorem admissible_satisfiable {S : X.Formula → Prop}
    (sound : ∀ r, S r → X.Satisfiable r) {c : X.Formula}
    (h : X.Admissible S c) : X.Satisfiable c := by
  obtain ⟨r, hr, eqv⟩ := h
  exact (X.satisfiable_equivalent eqv).mpr (sound r hr)

theorem satisfiable_projectionClosed : X.ProjectionClosed X.Satisfiable := by
  intro a c hc
  have h := X.admissible_satisfiable (fun _ h => h) hc
  exact ⟨_, (X.satisfiable_exists_iff a c).mpr h, X.equivalent_refl _⟩

end ConstraintTheory
end EHMX.HMX
