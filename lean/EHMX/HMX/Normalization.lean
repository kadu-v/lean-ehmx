import EHMX.HMX.LogicalNormalization
import Mathlib.Computability.Partrec

namespace EHMX.HMX
variable {T : TypeSyntax}

abbrev Theory.Problem (X : Theory T) := Logical.ConstraintProblem X

/-- Contract for one actual normalizer. No typing conclusion is a field.
Failure means no normal form, not necessarily inconsistency. -/
structure PrincipalNormalizer (X : Theory T) (S : X.Formula → Prop) where
  run : X.Problem → Option X.Problem
  principal : ∀ p n, run p = some n → Logical.ConstraintProblem.IsPrincipal S p n
  failure : ∀ p, run p = none ↔ ¬ ∃ n, Logical.ConstraintProblem.IsNormal S p n

/-- A noncomputable existence model, separate from Def.28(i). -/
noncomputable def PrincipalNormalizer.ofExistence {X : Theory T} {S : X.Formula → Prop}
    (P : Logical.PrincipalNormalForms X S) : PrincipalNormalizer X S := by
  classical
  refine { run := fun p => if h : ∃ n, Logical.ConstraintProblem.IsNormal S p n
               then some (Classical.choose (P p h)) else none
           principal := ?_, failure := ?_ }
  · intro p n h
    split at h
    · rename_i hn
      cases Option.some.inj h
      exact Classical.choose_spec (P p hn)
    · cases h
  · intro p
    simp

namespace Theory
variable (X : Theory T)

/-- Definition 28(iii) ranges over all normal forms. -/
def ExactResidual (S : X.Formula → Prop) : Prop :=
  ∀ p n, Logical.ConstraintProblem.IsNormal S p n →
    X.Equivalent n.constraint (X.subst n.substitution p.constraint)

/-- Literal Definition 28(ii), with the approved type-sort restriction. -/
def AllTypeEquationFree (S : X.Formula → Prop) : Prop :=
  ∀ c, S c ↔ X.Satisfiable c ∧
    ∀ t u, X.Entails c (X.eq t u) → X.Entails X.top (X.eq t u)

/-- Definition 24 / Remark 3: representatives are an alternative convention,
not the same condition as literal membership in all equation-free constraints. -/
def SyntacticallyUnique (S : X.Formula → Prop) : Prop :=
  ∀ c d, S c → S d → X.Equivalent c d → c = d

def EquationFreeRepresentatives (S : X.Formula → Prop) : Prop :=
  X.SyntacticallyUnique S ∧ ∀ c, X.Admissible S c ↔ X.Satisfiable c ∧
    ∀ t u, X.Entails c (X.eq t u) → X.Entails X.top (X.eq t u)

/-- Definition 27: an actual finite set of primitive predicates. -/
structure PrimitiveProblem where
  predicates : Finset (ConstraintAtom T X.language.predicates)
  substitution : Substitution T

noncomputable def PrimitiveProblem.problem (p : X.PrimitiveProblem) : X.Problem :=
  ⟨X.language.predicatesSet p.predicates, p.substitution⟩

/-- Effective codes belong to the concrete solver. The abstract problem type
contains functions and is not postulated Primcodable. Both decoded inputs and
outputs participate in the correctness contract. -/
structure SolverEncoding where
  input : Nat → Option X.PrimitiveProblem
  output : Nat → Option X.Problem
  coversInput : ∀ p, ∃ code, input code = some p

def ProjectionFreeProcedure (S : X.Formula → Prop) : Prop :=
  ∃ enc : X.SolverEncoding, ∃ run : Nat → Option Nat, Computable run ∧
    ∀ code p, enc.input code = some p → p.problem.WellFormed →
      (∀ out, run code = some out → ∃ n, enc.output out = some n ∧
        Logical.ConstraintProblem.IsPrincipal S p.problem n) ∧
      (run code = none ↔ ¬ ∃ n, Logical.ConstraintProblem.IsNormal S p.problem n)

/-- Full Definition 28 is not a common premise of the four typing statements. -/
structure LiftingProperty (S : X.Formula → Prop) : Prop where
  procedure : X.ProjectionFreeProcedure S
  equationFree : X.AllTypeEquationFree S
  exactResidual : X.ExactResidual S
  witnesses : X.Lifting S

end Theory
end EHMX.HMX
