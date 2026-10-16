import HMX.ConstraintTheory

namespace HMX
noncomputable section
local instance normalizationDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance normalizationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

namespace ConstraintTheory
variable (X : ConstraintTheory V K arity P parity)
def Regular : Prop := ∀ t u, X.Entails ∅ (Constraint.eq t u) → t.fv = u.fv

/-- D20's first `=U`: unconditional equality, NOT equality under a residual. -/
def Agrees (U : Set V) (ψ φ : Assignment V K arity) : Prop :=
  ∀ a ∈ U, X.Entails ∅ (Constraint.eq (ψ a) (φ a))
def Factors (U : Set V) (ψ κ φ : Assignment V K arity) : Prop :=
  κ.IsSubstitution ∧ X.Agrees U (κ.comp ψ) φ
def SubstitutionMoreGeneral (U : Set V) (ψ φ : Assignment V K arity) : Prop :=
  ψ.IsSubstitution ∧ φ.IsSubstitution ∧ ∃ κ, X.Factors U ψ κ φ
/-- D20 overloads `=U` for this second, different relation. -/
def EquallyGeneral (U : Set V) (ψ φ : Assignment V K arity) : Prop :=
  X.SubstitutionMoreGeneral U ψ φ ∧ X.SubstitutionMoreGeneral U φ ψ
def SubstitutionLUB (φ ψ θ : Assignment V K arity) : Prop :=
  X.SubstitutionMoreGeneral Set.univ φ θ ∧ X.SubstitutionMoreGeneral Set.univ ψ θ ∧
  ∀ χ, X.SubstitutionMoreGeneral Set.univ φ χ → X.SubstitutionMoreGeneral Set.univ ψ χ →
    X.SubstitutionMoreGeneral Set.univ θ χ
def Unitary : Prop := ∀ φ ψ, φ.IsSubstitution → ψ.IsSubstitution →
  (∃ θ, X.SubstitutionLUB φ ψ θ) ∨
  ¬ ∃ θ, X.SubstitutionMoreGeneral Set.univ φ θ ∧ X.SubstitutionMoreGeneral Set.univ ψ θ
end ConstraintTheory

structure Problem (V : Type u) (K : Type v) (arity : K → Nat) (P : Type w) (parity : P → Nat) where
  constraint : Constraint V K arity P parity
  substitution : Assignment V K arity

namespace Problem
variable (X : ConstraintTheory V K arity P parity)
/-- D22 uses literal equality here. D23's output uses logical equivalence. -/
def IsProblem (p : Problem V K arity P parity) : Prop :=
  p.substitution.IsSubstitution ∧ p.constraint.subst p.substitution = p.constraint
def MoreGeneral (p q : Problem V K arity P parity) : Prop :=
  ∃ κ, X.Factors Set.univ p.substitution κ q.substitution ∧
    X.Entails q.constraint (p.constraint.subst κ)
def Equivalent (p q : Problem V K arity P parity) : Prop := p.MoreGeneral X q ∧ q.MoreGeneral X p
def Combines (p q r : Problem V K arity P parity) : Prop :=
  X.SubstitutionLUB p.substitution q.substitution r.substitution ∧
    r.constraint = (p.constraint ∪ q.constraint).subst r.substitution
def NormalForm (S : Set (Constraint V K arity P parity)) (p n : Problem V K arity P parity) : Prop :=
  p.IsProblem ∧ n.substitution.IsSubstitution ∧ n.constraint ∈ S ∧
    X.Equivalent (n.constraint.subst n.substitution) n.constraint ∧ p.MoreGeneral X n
def Principal (S : Set (Constraint V K arity P parity)) (p n : Problem V K arity P parity) : Prop :=
  p.NormalForm X S n ∧ ∀ m, p.NormalForm X S m → n.MoreGeneral X m
def HasNormalForm (S : Set (Constraint V K arity P parity)) (p : Problem V K arity P parity) : Prop :=
  ∃ n, p.NormalForm X S n
def Independent (p q : Problem V K arity P parity) : Prop :=
  Disjoint p.substitution.domain q.substitution.codomain ∧
  Disjoint q.substitution.domain p.substitution.codomain ∧
  Disjoint (X.fv p.constraint) q.substitution.domain ∧
  Disjoint (X.fv q.constraint) p.substitution.domain
end Problem

namespace ConstraintTheory
variable (X : ConstraintTheory V K arity P parity)
def PrincipalConstraintProperty (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ p : Problem V K arity P parity, p.IsProblem → p.HasNormalForm X S → ∃ n, p.Principal X S n
def SyntacticallyUnique (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ C ∈ S, ∀ D ∈ S, X.Equivalent C D → C = D
def EquationFreeConstraint (C : Constraint V K arity P parity) : Prop :=
  ∀ t u, X.Entails C (Constraint.eq t u) → X.Entails ∅ (Constraint.eq t u)
def EquationFree (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ C ∈ S, X.EquationFreeConstraint C
end ConstraintTheory

abbrev Normalizer (V : Type u) (K : Type v) (arity : K → Nat) (P : Type w) (parity : P → Nat) :=
  Problem V K arity P parity → Option (Problem V K arity P parity)

namespace Normalizer
def Specification (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
    (normalize : Normalizer V K arity P parity) : Prop :=
  ∀ p, p.IsProblem →
    (∀ n, normalize p = some n → p.Principal X S n) ∧
    (normalize p = none ↔ ¬ ∃ n, p.Principal X S n)
end Normalizer

/- The syntactic presentation and effective computation in D27/D28(1) are in
   ConstraintPresentation.lean and Lifting.lean. -/
namespace ConstraintTheory
variable (X : ConstraintTheory V K arity P parity)
/-- D28(2), including 'this is the only condition', with implicit satisfiability.
    This is stronger than merely requiring every member of S to be equation-free. -/
def LiftingSolvedForms (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ C, C ∈ S ↔ X.Satisfiable C ∧ X.EquationFreeConstraint C
/-- D28(3), retaining the printed equality. The possible conflict with
    condition (2) is recorded, not repaired in the source transcription. -/
def LiftingNormalForms (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ p n : Problem V K arity P parity, p.NormalForm X S n →
    n.constraint = p.constraint.subst n.substitution
def LiftingWitnesses (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ A C, X.project A C ∈ S → ∃ φ : Assignment V K arity,
    φ.IsSubstitution ∧ φ.domain ⊆ (A : Set V) ∧ C.subst φ ∈ S
end ConstraintTheory
end
end HMX
