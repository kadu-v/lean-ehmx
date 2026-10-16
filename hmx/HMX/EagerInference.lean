import HMX.Inference

namespace HMX
noncomputable section
local instance eagerDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance eagerDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

def Freshening (A : Finset V) (avoid : Set V) (π : Assignment V K arity) : Prop :=
  π.IsSubstitution ∧ ∃ ρ : Equiv.Perm V,
    π = (fun a => if a ∈ A then Ty.var (ρ a) else .var a) ∧
    Disjoint (ρ '' (A : Set V)) ((A : Set V) ∪ avoid)

abbrev Generalizer (N : Type*) (V : Type u) (K : Type v) (arity : K → Nat) (P : Type w) (parity : P → Nat) :=
  Constraint V K arity P parity → Environment N V K arity P parity → Ty V K arity →
    Constraint V K arity P parity × Scheme V K arity P parity

def Generalizer.Specification (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (gen : Generalizer N V K arity P parity) : Prop :=
  ∀ C Γ t, X.Admissible S C → X.EnvironmentAdmissible S Γ →
    AlgorithmicGeneralizes X S C Γ (.type t) (gen C Γ t).1 (gen C Γ t).2

/-- Figure 4.1. The normalizer and generalizer are fixed for the whole relation. -/
inductive EagerInference (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity) : Assignment V K arity →
    Constraint V K arity P parity → Environment (N ⊕ Const) V K arity P parity →
    Expr N Const → Ty V K arity → Prop where
  | var (lookup : Γ.lookup (.inl x) = some s) (view : FlatView s A D t)
      (boundFresh : Disjoint (A : Set V) (X.envFV Γ))
      (fresh : Freshening A (X.envFV Γ ∪ X.fv D ∪ (t.fv : Set V)) π)
      (result : normalize ⟨D.subst π, π⟩ = some n) :
      EagerInference X normalize gen (n.substitution.restrict (X.envFV Γ)) n.constraint Γ (.var x) (t.subst n.substitution)
  | constant (lookup : Γ.lookup (.inr c) = some s) (view : FlatView s A D t)
      (boundFresh : Disjoint (A : Set V) (X.envFV Γ))
      (fresh : Freshening A (X.envFV Γ ∪ X.fv D ∪ (t.fv : Set V)) π)
      (result : normalize ⟨D.subst π, π⟩ = some n) :
      EagerInference X normalize gen (n.substitution.restrict (X.envFV Γ)) n.constraint Γ (.constant c) (t.subst n.substitution)
  | abs (d : EagerInference X normalize gen ψ C (Γ.extend (.inl x) (.type (.var a))) e t)
      (fresh : a ∉ X.envFV Γ) :
      EagerInference X normalize gen (ψ.without {a}) C Γ (.lam x e) (.arrow (ψ a) t)
  | app (f : EagerInference X normalize gen ψ₁ C₁ Γ e₁ t₁)
      (d : EagerInference X normalize gen ψ₂ C₂ Γ e₂ t₂)
      (fresh : a ∉ X.envFV Γ ∪ X.fv C₁ ∪ X.fv C₂ ∪ (t₁.fv : Set V) ∪ (t₂.fv : Set V) ∪
        ψ₁.domain ∪ ψ₁.codomain ∪ ψ₂.domain ∪ ψ₂.codomain)
      (combine₁ : Problem.Combines X ⟨C₁, ψ₁⟩ ⟨C₂, ψ₂⟩ q)
      (combine₂ : q.Combines X ⟨Constraint.le t₁ (.arrow t₂ (.var a)), Assignment.id⟩ p)
      (result : normalize p = some n) :
      EagerInference X normalize gen (n.substitution.restrict (X.envFV Γ)) n.constraint Γ (.app e₁ e₂) (n.substitution a)
  | letE (d : EagerInference X normalize gen ψ₁ C₁ Γ e t)
      (subst : Environment.Substitutes ψ₁ Γ Δ) (g : gen C₁ Δ t = (C₂, s))
      (b : EagerInference X normalize gen ψ₂ C₃ (Γ.extend (.inl x) s) e' t')
      (combine : Problem.Combines X ⟨C₂, ψ₁⟩ ⟨C₃, ψ₂⟩ p) (result : normalize p = some n) :
      EagerInference X normalize gen (n.substitution.restrict (X.envFV Γ)) n.constraint Γ (.letE x e e') (t'.subst n.substitution)

/-- §4.3.1, p.97. Syntactic fixedness is not conflated with entailment. -/
def TypingConfiguration (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (Γ : Environment N V K arity P parity)
    (C : Constraint V K arity P parity) (s : Scheme V K arity P parity) (ψ : Assignment V K arity) : Prop :=
  C ∈ S ∧ ψ.IsSubstitution ∧ C.subst ψ = C ∧ s.subst ψ = s ∧ X.ConsistentEnvironment S ψ Γ

def ConfigurationMoreGeneral (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (Γ : Environment N V K arity P parity)
    (C : Constraint V K arity P parity) (s : Scheme V K arity P parity) (ψ : Assignment V K arity)
    (D : Constraint V K arity P parity) (t : Scheme V K arity P parity) (φ : Assignment V K arity) : Prop :=
  ∃ κ s', X.Factors (X.envFV Γ) ψ κ φ ∧ Scheme.Substitutes κ s s' ∧
    X.Entails D (C.subst κ) ∧ Instance X S D s' t
end
end HMX
