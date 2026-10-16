import HMX.Inference

namespace HMX
noncomputable section
local instance intermediateDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/- Figure 4.5: Wc2 and Wc are mutually defined. The explicit two phases
    ensure normalization after every syntax rule. The support condition comes
    from p.108, immediately before the figure. -/
mutual
inductive IntermediateStep (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity) :
    Constraint V K arity P parity → Environment (N ⊕ Const) V K arity P parity →
    Expr N Const → V → Prop where
  | var (lookup : Γ.lookup (.inl x) = some s) (view : FlatView s A D t)
      (boundFresh : Disjoint (A : Set V) (X.envFV Γ))
      (fresh : b ∉ X.envFV Γ ∪ X.fv D ∪ (t.fv : Set V) ∪ (A : Set V))
      (env : X.EnvironmentAdmissible X.Satisfiable Γ)
      (sat : X.Satisfiable (X.project A (Constraint.eq (.var b) t ∪ D))) :
      IntermediateStep X normalize (X.project A (Constraint.eq (.var b) t ∪ D)) Γ (.var x) b
  | constant (lookup : Γ.lookup (.inr c) = some s) (view : FlatView s A D t)
      (boundFresh : Disjoint (A : Set V) (X.envFV Γ))
      (fresh : b ∉ X.envFV Γ ∪ X.fv D ∪ (t.fv : Set V) ∪ (A : Set V))
      (env : X.EnvironmentAdmissible X.Satisfiable Γ)
      (sat : X.Satisfiable (X.project A (Constraint.eq (.var b) t ∪ D))) :
      IntermediateStep X normalize (X.project A (Constraint.eq (.var b) t ∪ D)) Γ (.constant c) b
  | abs (unbound : Γ.lookup (.inl x) = none) (d : IntermediateConstraintInference X normalize C (Γ.extend (.inl x) (.type (.var a))) e g)
      (freshInput : a ∉ X.envFV Γ)
      (fresh : b ∉ X.envFV Γ ∪ X.fv C ∪ ({a, g} : Set V))
      (sat : X.Satisfiable (X.project {a, g} (Constraint.eq (.var b) (.arrow (.var a) (.var g)) ∪ C))) :
      IntermediateStep X normalize (X.project {a, g} (Constraint.eq (.var b) (.arrow (.var a) (.var g)) ∪ C)) Γ (.lam x e) b
  | app (f : IntermediateConstraintInference X normalize C₁ Γ e₁ a₁) (d : IntermediateConstraintInference X normalize C₂ Γ e₂ a₂)
      (distinct : a₁ ≠ a₂)
      (fresh : a ∉ X.envFV Γ ∪ X.fv C₁ ∪ X.fv C₂ ∪ ({a₁, a₂} : Set V))
      (sat : X.Satisfiable (X.project {a₁, a₂} (C₁ ∪ C₂ ∪ Constraint.le (.var a₁) (.arrow (.var a₂) (.var a))))) :
      IntermediateStep X normalize (X.project {a₁, a₂} (C₁ ∪ C₂ ∪ Constraint.le (.var a₁) (.arrow (.var a₂) (.var a))))
        Γ (.app e₁ e₂) a
  | letE (unbound : Γ.lookup (.inl x) = none) (d : IntermediateConstraintInference X normalize C₁ Γ e a)
      (b : IntermediateConstraintInference X normalize C₃ (Γ.extend (.inl x) (.all {a} C₁ (.type (.var a)))) e' β)
      (sat : X.Satisfiable (X.project {a} C₁ ∪ C₃)) :
      IntermediateStep X normalize (X.project {a} C₁ ∪ C₃) Γ (.letE x e e') β

inductive IntermediateConstraintInference (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity) :
    Constraint V K arity P parity → Environment (N ⊕ Const) V K arity P parity →
    Expr N Const → V → Prop where
  | normalize (A : Finset V) (d : IntermediateStep X normalize C Γ e a)
      (result : normalize ⟨C, Assignment.id⟩ = some n)
      (support : n.substitution.domain ⊆ X.envFV Γ ∪ {a})
      (domain : (A : Set V) = n.substitution.domain)
      (sat : X.Satisfiable (n.constraint ∪ Constraint.graphOn n.substitution A)) :
      IntermediateConstraintInference X normalize
        (n.constraint ∪ Constraint.graphOn n.substitution A) Γ e a
  | equ (d : IntermediateConstraintInference X normalize C Γ e a) (h : X.Equivalent C D) :
      IntermediateConstraintInference X normalize D Γ e a

end

inductive IntermediateTermInference (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity) : Assignment V K arity →
    Constraint V K arity P parity → Environment (N ⊕ Const) V K arity P parity →
    Expr N Const → Ty V K arity → Prop where
  | reconstruct (d : IntermediateConstraintInference X normalize C Γ e a)
      (result : normalize ⟨C, Assignment.id⟩ = some n) :
      IntermediateTermInference X normalize (n.substitution.restrict (X.envFV Γ))
        n.constraint Γ e (n.substitution a)
end
end HMX
