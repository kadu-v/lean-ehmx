import HMX.EagerInference

namespace HMX
noncomputable section
local instance byneedDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/- Figure 4.2, with documented repairs (audit WBYNEED):
   * W' accumulates an unapplied constraint C and substitution phi;
   * normalization therefore receives (phi C, phi), a constraint problem;
   * the undefined psi-prime in Let is removed, leaving the unapplied body type.
   These are proposed repairs, not a claim that the printed rules are unambiguous. -/
mutual
inductive DeferredInference (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity) : Assignment V K arity →
    Constraint V K arity P parity → Environment (N ⊕ Const) V K arity P parity →
    Expr N Const → Ty V K arity → Prop where
  | var (lookup : Γ.lookup (.inl x) = some s) (view : FlatView s A D t)
      (boundFresh : Disjoint (A : Set V) (X.envFV Γ))
      (fresh : Freshening A (X.envFV Γ ∪ X.fv D ∪ (t.fv : Set V)) π) :
      DeferredInference X normalize gen π D Γ (.var x) t
  | constant (lookup : Γ.lookup (.inr c) = some s) (view : FlatView s A D t)
      (boundFresh : Disjoint (A : Set V) (X.envFV Γ))
      (fresh : Freshening A (X.envFV Γ ∪ X.fv D ∪ (t.fv : Set V)) π) :
      DeferredInference X normalize gen π D Γ (.constant c) t
  | abs (d : DeferredInference X normalize gen ψ C (Γ.extend (.inl x) (.type (.var a))) e t)
      (fresh : a ∉ X.envFV Γ) :
      DeferredInference X normalize gen ψ C Γ (.lam x e) (.arrow (.var a) t)
  | app (f : DeferredInference X normalize gen ψ₁ C₁ Γ e₁ t₁)
      (d : DeferredInference X normalize gen ψ₂ C₂ Γ e₂ t₂)
      (fresh : a ∉ X.envFV Γ ∪ X.fv C₁ ∪ X.fv C₂ ∪ (t₁.fv : Set V) ∪ (t₂.fv : Set V) ∪
        ψ₁.domain ∪ ψ₁.codomain ∪ ψ₂.domain ∪ ψ₂.codomain)
      (lub : X.SubstitutionLUB ψ₁ ψ₂ ψ) :
      DeferredInference X normalize gen ψ (C₁ ∪ C₂ ∪ Constraint.le t₁ (.arrow t₂ (.var a))) Γ
        (.app e₁ e₂) (.var a)
  | letE (d : ByNeedInference X normalize gen ψ₁ C₁ Γ e t)
      (subst : Environment.Substitutes ψ₁ Γ Δ) (g : gen C₁ Δ t = (C₂, s))
      (b : DeferredInference X normalize gen ψ₂ C₃ (Γ.extend (.inl x) s) e' t')
      (lub : X.SubstitutionLUB ψ₁ ψ₂ ψ) :
      DeferredInference X normalize gen ψ (C₂ ∪ C₃) Γ (.letE x e e') t'

inductive ByNeedInference (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity) : Assignment V K arity →
    Constraint V K arity P parity → Environment (N ⊕ Const) V K arity P parity →
    Expr N Const → Ty V K arity → Prop where
  | normalize (d : DeferredInference X normalize gen φ C Γ e t)
      (result : normalize ⟨C.subst φ, φ⟩ = some n) :
      ByNeedInference X normalize gen (n.substitution.restrict (X.envFV Γ)) n.constraint Γ e
        (t.subst n.substitution)
end
end
end HMX
