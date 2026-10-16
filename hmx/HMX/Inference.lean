import HMX.Judgments
import HMX.Normalization

namespace HMX
noncomputable section
local instance inferenceDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance inferenceDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- The conventional empty-quantifier abbreviation, needed for monomorphic variables. -/
def FlatView (s : Scheme V K arity P parity) (A : Finset V)
    (D : Constraint V K arity P parity) (t : Ty V K arity) : Prop :=
  Scheme.Alpha s (.all A D (.type t)) ∨ (Scheme.Alpha s (.type t) ∧ A = ∅ ∧ D = ∅)

/-- Figures 4.3 and 4.4 share these constraint inference rules.
    Satisfiability is the validity convention stated in §4.4.1.
    Freshness is made explicit at each rule, rather than implemented by a counter. -/
inductive ConstraintInference (X : ConstraintTheory V K arity P parity) :
    Constraint V K arity P parity → Environment (N ⊕ Const) V K arity P parity →
    Expr N Const → V → Prop where
  | var (lookup : Γ.lookup (.inl x) = some s) (view : FlatView s A D t)
      (boundFresh : Disjoint (A : Set V) (X.envFV Γ))
      (fresh : b ∉ X.envFV Γ ∪ X.fv D ∪ (t.fv : Set V) ∪ (A : Set V))
      (env : X.EnvironmentAdmissible X.Satisfiable Γ)
      (sat : X.Satisfiable (X.project A (Constraint.eq (.var b) t ∪ D))) :
      ConstraintInference X (X.project A (Constraint.eq (.var b) t ∪ D)) Γ (.var x) b
  | constant (lookup : Γ.lookup (.inr c) = some s) (view : FlatView s A D t)
      (boundFresh : Disjoint (A : Set V) (X.envFV Γ))
      (fresh : b ∉ X.envFV Γ ∪ X.fv D ∪ (t.fv : Set V) ∪ (A : Set V))
      (env : X.EnvironmentAdmissible X.Satisfiable Γ)
      (sat : X.Satisfiable (X.project A (Constraint.eq (.var b) t ∪ D))) :
      ConstraintInference X (X.project A (Constraint.eq (.var b) t ∪ D)) Γ (.constant c) b
  | abs (d : ConstraintInference X C (Γ.extend (.inl x) (.type (.var a))) e g)
      (freshInput : a ∉ X.envFV Γ)
      (fresh : b ∉ X.envFV Γ ∪ X.fv C ∪ ({a, g} : Set V))
      (sat : X.Satisfiable (X.project {a, g} (Constraint.eq (.var b) (.arrow (.var a) (.var g)) ∪ C))) :
      ConstraintInference X (X.project {a, g} (Constraint.eq (.var b) (.arrow (.var a) (.var g)) ∪ C)) Γ (.lam x e) b
  | app (f : ConstraintInference X C₁ Γ e₁ a₁) (d : ConstraintInference X C₂ Γ e₂ a₂)
      (distinct : a₁ ≠ a₂)
      (fresh : a ∉ X.envFV Γ ∪ X.fv C₁ ∪ X.fv C₂ ∪ ({a₁, a₂} : Set V))
      (sat : X.Satisfiable (X.project {a₁, a₂} (C₁ ∪ C₂ ∪ Constraint.le (.var a₁) (.arrow (.var a₂) (.var a))))) :
      ConstraintInference X (X.project {a₁, a₂} (C₁ ∪ C₂ ∪ Constraint.le (.var a₁) (.arrow (.var a₂) (.var a))))
        Γ (.app e₁ e₂) a
  | letE (d : ConstraintInference X C₁ Γ e a)
      (b : ConstraintInference X C₃ (Γ.extend (.inl x) (.all {a} C₁ (.type (.var a)))) e' β)
      (sat : X.Satisfiable (X.project {a} C₁ ∪ C₃)) :
      ConstraintInference X (X.project {a} C₁ ∪ C₃) Γ (.letE x e e') β

  | equ (d : ConstraintInference X C Γ e a) (h : X.Equivalent C D) : ConstraintInference X D Γ e a

/-- Figure 4.4: one reconstruction, after the entire constraint derivation.
    The normalizer's substitution and the reported restricted substitution differ. -/
inductive TermInference (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity) : Assignment V K arity →
    Constraint V K arity P parity → Environment (N ⊕ Const) V K arity P parity →
    Expr N Const → Ty V K arity → Prop where
  | reconstruct (d : ConstraintInference X C Γ e a)
      (result : normalize ⟨C, Assignment.id⟩ = some n) :
      TermInference X normalize (n.substitution.restrict (X.envFV Γ)) n.constraint Γ e (n.substitution a)

/-- The maximal-set selection of §4.3 is separate from logical `Generalizes`.
    Maximal does not mean greatest: the source permits incomparable choices. -/
def AlgorithmicGeneralizes (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity)
    (Γ : Environment N V K arity P parity) (s : Scheme V K arity P parity)
    (Co : Constraint V K arity P parity) (so : Scheme V K arity P parity) : Prop :=
  X.Admissible S C ∧ X.EnvironmentAdmissible S Γ ∧ X.SchemeAdmissible S s ∧
  ∃ A : Finset V,
    (A : Set V) ⊆ (X.fv C ∪ X.schemeFV s) \ X.envFV Γ ∧
    X.Admissible S (X.project A C) ∧
    (∀ B : Finset V, A ⊆ B → (B : Set V) ⊆ (X.fv C ∪ X.schemeFV s) \ X.envFV Γ →
      X.Admissible S (X.project B C) → B = A) ∧
    ∃ C₁ C₂, X.Equivalent C (C₁ ∪ C₂) ∧
      X.Equivalent Co (X.project A C) ∧ X.Equivalent Co (C₁ ∪ X.project A C₂) ∧
      so = .all A C₂ s ∧ Disjoint (A : Set V) (X.fv C₁ ∪ X.envFV Γ) ∧
      X.SchemeAdmissible S so
end
end HMX
