import HMX.ConstraintTheory
import HMX.ConstraintPresentation

namespace HMX
noncomputable section
local instance soundnessDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- A finite simultaneous substitution of CLOSED types for the listed variables.
    This is not an assumption that all ground semantic values have term names. -/
def ClosedInstantiation (A : Finset V) (φ : Assignment V K arity) : Prop :=
  φ.IsSubstitution ∧ φ.domain ⊆ (A : Set V) ∧ ∀ a ∈ A, (φ a).IsMonotype

/-- Definition 9, p.33. The output remains projected over A. -/
def ConstraintTheory.Sound (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ A C, C ∈ S → X.Entails ∅ (X.project A C) →
    ∃ φ, ClosedInstantiation A φ ∧ X.Entails ∅ (X.project A (Constraint.graphOn φ A ∪ C))

/-- Definitions 12 and 13 (the same condition is restated on p.39).
    The listed variables B may differ from the initially projected variables A. -/
def ConstraintTheory.StronglySound (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (presentation : ConstraintPresentation X) : Prop :=
  ∀ C A D, C ∈ S → C = X.project A D → presentation.ProjectionFree D → X.Satisfiable D →
    ∃ B φ, ClosedInstantiation B φ ∧ X.Entails ∅ (D.subst φ)
/-- The separate assumption on pp.37–38, after Definition 12. This is not
part of Definitions 12/13 themselves. -/
def ConstraintTheory.SolvedProjectionFree (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (presentation : ConstraintPresentation X) : Prop :=
  ∀ C ∈ S, presentation.ProjectionFree C

/-- The strengthened denotational setting described after Theorem 5.
It is recorded separately, without rewriting that theorem or adding this
condition to the syntactic statement on p.39. -/
def ConstraintTheory.StrongDenotationalConditions (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (presentation : ConstraintPresentation X) : Prop :=
  X.StronglySound S presentation ∧ X.SolvedProjectionFree S presentation
end
end HMX
