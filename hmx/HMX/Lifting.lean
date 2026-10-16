import HMX.Normalization
import HMX.ConstraintPresentation
import Mathlib.Computability.Partrec

namespace HMX
noncomputable section
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- A fixed representation for the effective language in Definition 28(1).
    It codes finite substitutions, not the uncountable space of raw assignments.
    This representation is an explicit parameter, not chosen after the solver.
    The source does not specify a particular machine encoding. -/
structure ProblemCoding (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) where
  decode : Nat → Option (Problem V K arity P parity)
  sound : ∀ k p, decode k = some p → p.substitution.IsSubstitution
  complete : ∀ p : Problem V K arity P parity, p.substitution.IsSubstitution →
    ∃ k, decode k = some p

namespace ConstraintTheory
variable (X : ConstraintTheory V K arity P parity)

/-- Definition 28(1). `none` is a terminating failure report; it does not
    stand for divergence. Correctness is required for every encoding of each
    projection-free input. The computability predicate is Mathlib's actual
    recursive-function predicate, not an uninterpreted Boolean or proposition. -/
def EffectiveProjectionFreeNormalization (S : Set (Constraint V K arity P parity))
    (presentation : ConstraintPresentation X) (coding : ProblemCoding V K arity P parity) : Prop :=
  ∃ run : Nat → Option Nat, Computable run ∧
    ∀ k p, coding.decode k = some p → p.IsProblem → presentation.ProjectionFree p.constraint →
      (∀ j, run k = some j → ∃ n, coding.decode j = some n ∧ p.Principal X S n) ∧
      (run k = none ↔ ¬ p.HasNormalForm X S)

/-- All four numbered conditions of Definition 28, p.93. The variant in
    Remark 3 using unique representatives is not silently substituted for (2). -/
def LiftingProperty (S : Set (Constraint V K arity P parity))
    (presentation : ConstraintPresentation X) (coding : ProblemCoding V K arity P parity) : Prop :=
  X.EffectiveProjectionFreeNormalization S presentation coding ∧
  X.LiftingSolvedForms S ∧ X.LiftingNormalForms S ∧ X.LiftingWitnesses S
end ConstraintTheory
end
end HMX
