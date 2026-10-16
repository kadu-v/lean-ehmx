import HMX.Statements
import HMX.ConstraintPresentation

namespace HMX
noncomputable section
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
variable {N Const : Type}

/-- §3.5.5 uses 'appears in a monomorphic context' without a formal definition.
    That source predicate is an explicit parameter; no particular analysis of
    uses is silently substituted for it. -/
def Expr.LetRealizable (monomorphicUse : N → Expr N Const → Prop) : Expr N Const → Prop
  | .var _ | .constant _ => True
  | .lam _ e => e.LetRealizable monomorphicUse
  | .app e b => e.LetRealizable monomorphicUse ∧ b.LetRealizable monomorphicUse
  | .letE x e b => monomorphicUse x b ∧ e.LetRealizable monomorphicUse ∧ b.LetRealizable monomorphicUse

def Scheme.ProjectionFree {X : ConstraintTheory V K arity P parity}
    (presentation : ConstraintPresentation X) : Scheme V K arity P parity → Prop
  | .type _ => True
  | .all _ C s => presentation.ProjectionFree C ∧ s.ProjectionFree presentation

/-- The smallest projection-closed superset, not an assumed conjunction closure. -/
def ConstraintTheory.IsProjectionClosure (X : ConstraintTheory V K arity P parity)
    (S T : Set (Constraint V K arity P parity)) : Prop :=
  S ⊆ T ∧ X.ProjectionClosed T ∧ ∀ U, S ⊆ U → X.ProjectionClosed U → T ⊆ U

namespace Statement
variable (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
variable (policy : WeakeningPolicy) (presentation : ConstraintPresentation X)
variable (monomorphicUse : N → Expr N Const → Prop)

def theorem6 : Prop := CoreAssumptions X S policy →
  ∀ C (Γ : Environment (N ⊕ Const) V K arity P parity) e t,
    Typing X S policy C Γ e (.type t) → e.LetRealizable monomorphicUse →
    (∀ x s, Γ.lookup x = some s → s.ProjectionFree presentation) →
    ∃ C', X.Equivalent C' C ∧
      ∃ d : LogicalTyping .ordinary X S policy C' Γ e (.type t),
        d.AllConstraints presentation.ProjectionFree

def corollary3 : Prop := CoreAssumptions X S policy →
  ∀ T, X.IsProjectionClosure S T → CoreAssumptions X T policy →
  ∀ e : Expr N Const, e.LetRealizable monomorphicUse →
    ((∃ C Γ s, Typing X S policy C Γ e s) ↔ ∃ C Γ s, Typing X T policy C Γ e s)
end Statement
end
end HMX
