import HMX.Statements
import HMX.Lifting
import HMX.IntermediateInference
import HMX.ByNeedInference

namespace HMX
noncomputable section
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- Normalization results are compared as equivalence classes, as specified
    immediately before `normalize` on p.88. Failure is a distinct outcome. -/
def NormalizationResultEquivalent (X : ConstraintTheory V K arity P parity) :
    Option (Problem V K arity P parity) → Option (Problem V K arity P parity) → Prop
  | none, none => True
  | some p, some q => p.Equivalent X q
  | _, _ => False

/-- Combining problems may itself fail when substitutions have no upper bound. -/
def CombinedNormalization (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity) (p q : Problem V K arity P parity)
    (out : Option (Problem V K arity P parity)) : Prop :=
  (∃ r, p.Combines X q r ∧ normalize r = out) ∨
  (out = none ∧ ¬ ∃ r, p.Combines X q r)

def DeferredNormalization (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity) (p q : Problem V K arity P parity)
    (out : Option (Problem V K arity P parity)) : Prop :=
  (normalize p = none ∧ out = none) ∨
  ∃ p', normalize p = some p' ∧ CombinedNormalization X normalize p' q out

namespace Statement
variable (X : ConstraintTheory V K arity P parity)
variable (S : Set (Constraint V K arity P parity))
variable (presentation : ConstraintPresentation X) (coding : ProblemCoding V K arity P parity)

/-- p.92. The source proof explicitly interprets the equation in terms of
    successful results in both directions; p.88 identifies principal normal
    forms up to semantic equivalence. We do not require identical representatives. -/
def theorem9 (normalize : Normalizer V K arity P parity) : Prop :=
  Normalizer.Specification X S normalize → X.PrincipalConstraintProperty S → X.Unitary →
  ∀ p q, p.IsProblem → q.IsProblem → p.Independent X q →
    (∀ out, CombinedNormalization X normalize p q out →
      ∃ out', DeferredNormalization X normalize p q out' ∧ NormalizationResultEquivalent X out out') ∧
    (∀ out, DeferredNormalization X normalize p q out →
      ∃ out', CombinedNormalization X normalize p q out' ∧ NormalizationResultEquivalent X out out')

def lemma29 : Prop := X.LiftingProperty S presentation coding →
  ∀ A D φ, Problem.IsProblem ⟨X.project A D, φ⟩ →
    (Problem.HasNormalForm X S ⟨X.project A D, φ⟩ ↔ Problem.HasNormalForm X S ⟨D, φ⟩)

def lemma30 : Prop := X.LiftingProperty S presentation coding →
  ∀ A D φ (n : Problem V K arity P parity) π,
    Problem.IsProblem ⟨X.project A D, φ⟩ → Problem.Principal X S ⟨D, φ⟩ n →
    Freshening A (X.fv D ∪ φ.domain ∪ φ.codomain ∪ n.substitution.domain ∪ n.substitution.codomain) π →
    let ψ := π.comp (n.substitution.without A)
    Problem.Principal X S ⟨X.project A D, φ⟩ ⟨X.project A (D.subst ψ), ψ⟩

def theorem10 : Prop := X.LiftingProperty S presentation coding → X.PrincipalConstraintProperty S

/-- p.97, retaining the unspecified psi-prime of Figure 4.2. As with Theorem 18, exact output
    representatives require a separate review; this is a draft statement. -/
def theorem11 (policy : WeakeningPolicy) (N Const : Type)
    (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity) : Prop :=
  CoreAssumptions X S policy → Normalizer.Specification X S normalize →
  Generalizer.Specification X S gen → X.PrincipalConstraintProperty S → X.Unitary →
  ∀ ψ C (Γ : Environment (N ⊕ Const) V K arity P parity) e t,
    EagerInference X normalize gen ψ C Γ e t ↔ ByNeedInference X normalize gen ψ C Γ e t

/-- The literal-output equivalence printed on p.109. Its dependence on a
    representative-selection convention is tracked separately in the audit. -/
def theorem18 (policy : WeakeningPolicy) (N Const : Type)
    (normalize : Normalizer V K arity P parity) : Prop :=
  CoreAssumptions X S policy → Normalizer.Specification X S normalize →
  X.LiftingProperty S presentation coding →
  ∀ φ C (Γ : Environment (N ⊕ Const) V K arity P parity) e t,
    TermInference X normalize φ C Γ e t ↔ IntermediateTermInference X normalize φ C Γ e t
end Statement
end
end HMX
