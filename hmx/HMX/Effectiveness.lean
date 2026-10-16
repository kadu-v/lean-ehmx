import HMX.Lifting
import HMX.EagerInference

namespace HMX
noncomputable section
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- p.95: the inference rules describe an algorithm only when normalize is
    computable. This is stronger than its mathematical Specification. -/
def Normalizer.Effective (coding : ProblemCoding V K arity P parity)
    (normalize : Normalizer V K arity P parity) : Prop :=
  ∃ run : Nat → Option Nat, Computable run ∧ ∀ k p,
    coding.decode k = some p → p.IsProblem →
      (normalize p = none ↔ run k = none) ∧
      (∀ n, normalize p = some n ↔ ∃ j, run k = some j ∧ coding.decode j = some n)

/-- §4.4.1. Deciding satisfiability is a separate requirement for executable
    constraint inference; it is not a premise of the logical typing relation. -/
def EffectiveSatisfiability (X : ConstraintTheory V K arity P parity)
    (coding : ProblemCoding V K arity P parity) : Prop :=
  ∃ run : Nat → Bool, Computable run ∧ ∀ k p,
    coding.decode k = some p → (run k = true ↔ X.Satisfiable p.constraint)

/-- Fixed encodings for the domain and range of gen (p.96). As in ProblemCoding,
    these encodings are parameters established before choosing a procedure. -/
structure GeneralizationCoding (N : Type*) (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) where
  input : Nat → Option (Constraint V K arity P parity × Environment N V K arity P parity × Ty V K arity)
  output : Nat → Option (Constraint V K arity P parity × Scheme V K arity P parity)
  inputComplete : ∀ C Γ t, ∃ k, input k = some (C, Γ, t)
  outputComplete : ∀ C s, ∃ k, output k = some (C, s)

/-- p.96: effectiveness of the selected maximal generalization. This does not
    assert that every abstract X permits such a selection algorithm. -/
def Generalizer.Effective (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity))
    (coding : GeneralizationCoding N V K arity P parity)
    (gen : Generalizer N V K arity P parity) : Prop :=
  ∃ run : Nat → Nat, Computable run ∧ ∀ k C Γ t,
    coding.input k = some (C, Γ, t) → X.Admissible S C → X.EnvironmentAdmissible S Γ →
      coding.output (run k) = some (gen C Γ t)

namespace Statement
/-- The invariant stated in §§4.4.1 and 4.4.2. It is a proposition to prove,
    not an extra field in the constraint theory. -/
def constraintInferenceSupport (X : ConstraintTheory V K arity P parity) (N Const : Type) : Prop :=
  ∀ C (Γ : Environment (N ⊕ Const) V K arity P parity) e a,
    ConstraintInference X C Γ e a → X.fv C ⊆ X.envFV Γ ∪ {a} ∧ a ∉ X.envFV Γ
end Statement
end
end HMX
