import HMX.ConstraintTheory

namespace HMX
noncomputable section
local instance presentationDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- A presentation of the abstract tokens of Definition 2. Some tokens may
    themselves represent quantified formulas (Example 2, p.21). Thus primitive
    must not be defined as 'any value of Predicate'. This syntax is used only
    where the source distinguishes projection-free presentations. -/
inductive ConstraintExpression (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) where
  | primitive : Predicate V K arity P parity → ConstraintExpression V K arity P parity
  | truth
  | conjunction : ConstraintExpression V K arity P parity → ConstraintExpression V K arity P parity →
      ConstraintExpression V K arity P parity
  | projection : V → ConstraintExpression V K arity P parity → ConstraintExpression V K arity P parity

def ConstraintExpression.interpret (X : ConstraintTheory V K arity P parity) :
    ConstraintExpression V K arity P parity → Constraint V K arity P parity
  | .primitive p => {p}
  | .truth => ∅
  | .conjunction C D => C.interpret X ∪ D.interpret X
  | .projection a C => X.projectOne a (C.interpret X)

def ConstraintExpression.WellFormed (primitive : Set (Predicate V K arity P parity)) :
    ConstraintExpression V K arity P parity → Prop
  | .primitive p => p ∈ primitive
  | .truth => True
  | .conjunction C D => C.WellFormed primitive ∧ D.WellFormed primitive
  | .projection _ C => C.WellFormed primitive

/-- The presentation needed by §§3.5 and 4.2.1, separate from the abstract
    cylindric laws. Coverage says that constraints have finite presentations;
    it does not assume that normalization or elimination of projections exists. -/
structure ConstraintPresentation (X : ConstraintTheory V K arity P parity) where
  primitive : Set (Predicate V K arity P parity)
  equality : ∀ t u, Predicate.equal t u ∈ primitive
  order : ∀ t u, Predicate.less t u ∈ primitive
  subst : ∀ p ∈ primitive, ∀ φ : Assignment V K arity,
    φ.IsSubstitution → p.subst φ ∈ primitive
  coverage : ∀ C, ∃ E : ConstraintExpression V K arity P parity,
    E.WellFormed primitive ∧ E.interpret X = C

/-- Definition 27: literal primitive-token membership, not logical equivalence
    to a projection-free constraint. -/
def ConstraintPresentation.ProjectionFree {X : ConstraintTheory V K arity P parity}
    (presentation : ConstraintPresentation X) (C : Constraint V K arity P parity) : Prop :=
  ∀ p ∈ C, p ∈ presentation.primitive

end
end HMX
