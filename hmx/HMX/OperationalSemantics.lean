import HMX.Statements
import HMX.SoundnessConditions
import Mathlib.Logic.Relation

namespace HMX
noncomputable section
local instance operationalDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance operationalDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w

namespace Expr
variable {N Const : Type*}
def fv : Expr N Const → Finset N
  | .var x => {x}
  | .constant _ => ∅
  | .lam x e => e.fv.erase x
  | .app e e' => e.fv ∪ e'.fv
  | .letE x e e' => e.fv ∪ e'.fv.erase x
def rename (π : Equiv.Perm N) : Expr N Const → Expr N Const
  | .var x => .var (π x)
  | .constant c => .constant c
  | .lam x e => .lam (π x) (e.rename π)
  | .app e e' => .app (e.rename π) (e'.rename π)
  | .letE x e e' => .letE (π x) (e.rename π) (e'.rename π)
inductive Alpha : Expr N Const → Expr N Const → Prop
  | refl (e) : Alpha e e
  | symm : Alpha e e' → Alpha e' e
  | trans : Alpha e e' → Alpha e' e'' → Alpha e e''
  | lam : Alpha e e' → Alpha (.lam x e) (.lam x e')
  | app : Alpha e₁ e₁' → Alpha e₂ e₂' → Alpha (.app e₁ e₂) (.app e₁' e₂')
  | letE : Alpha e₁ e₁' → Alpha e₂ e₂' → Alpha (.letE x e₁ e₂) (.letE x e₁' e₂')
  | rename (π : Equiv.Perm N) (e : Expr N Const) (fixes : ∀ x ∈ e.fv, π x = x) :
      Alpha e (e.rename π)

def replace (x : N) (v : Expr N Const) : Expr N Const → Expr N Const
  | .var y => if y = x then v else .var y
  | .constant c => .constant c
  | .lam y e => .lam y (if y = x then e else replace x v e)
  | .app e e' => .app (replace x v e) (replace x v e')
  | .letE y e e' => .letE y (replace x v e) (if y = x then e' else replace x v e')
def SafeReplacement (x : N) (v : Expr N Const) : Expr N Const → Prop
  | .var _ | .constant _ => True
  | .lam y e => y = x ∨ (y ∉ v.fv ∧ SafeReplacement x v e)
  | .app e e' => SafeReplacement x v e ∧ SafeReplacement x v e'
  | .letE y e e' => SafeReplacement x v e ∧ (y = x ∨ (y ∉ v.fv ∧ SafeReplacement x v e'))
def Substitutes (x : N) (v e e' : Expr N Const) : Prop :=
  ∃ r, Alpha e r ∧ SafeReplacement x v r ∧ Alpha (replace x v r) e'

/-- Figure C.1. Positivity is a condition on the input weights, not a change
    to the printed recurrence. Constants use their initial-environment names. -/
def weightedSize (weights : N ⊕ Const → Nat) : Expr N Const → Nat
  | .var x => weights (.inl x)
  | .constant c => weights (.inr c)
  | .lam _ e => 1 + e.weightedSize weights
  | .app e e' => e.weightedSize weights + e'.weightedSize weights
  | .letE x e e' => e.weightedSize weights +
      e'.weightedSize (Function.update weights (.inl x) (e.weightedSize weights))

inductive Subexpression : Expr N Const → Expr N Const → Prop
  | refl (e) : Subexpression e e
  | lam : Subexpression e b → Subexpression e (.lam x b)
  | appLeft : Subexpression e f → Subexpression e (.app f a)
  | appRight : Subexpression e a → Subexpression e (.app f a)
  | letDefinition : Subexpression e d → Subexpression e (.letE x d b)
  | letBody : Subexpression e b → Subexpression e (.letE x d b)
end Expr

/-- p.39: a partial primitive operation on constants and closed values. The
    requirement that it respects constant types is NOT included by the source;
    see the separate audit issue REDUCTION. -/
structure PrimitiveReduction (N Const : Type*) where
  delta : Const → Expr N Const → Option (Expr N Const)
  closedValue : ∀ c v r, v.Value → v.fv = ∅ → delta c v = some r → r.Value ∧ r.fv = ∅

/-- The three rules actually printed on p.39, before any context closure. -/
inductive RootReduction (δ : PrimitiveReduction N Const) : Expr N Const → Expr N Const → Prop
  | primitive (value : v.Value) (h : δ.delta c v = some r) : RootReduction δ (.app (.constant c) v) r
  | beta (value : v.Value) (subst : Expr.Substitutes x v e r) : RootReduction δ (.app (.lam x e) v) r
  | letE (value : v.Value) (subst : Expr.Substitutes x v e r) : RootReduction δ (.letE x v e) r

/-- The source calls the contextual closure standard without specifying it.
The closure relation is supplied explicitly; only the printed root rules above
are fixed here. No evaluation order is silently chosen by the transcription. -/
structure ReductionContext (δ : PrimitiveReduction N Const) where
  step : Expr N Const → Expr N Const → Prop
  root : ∀ e e', RootReduction δ e e' → step e e'

def Faulty (δ : PrimitiveReduction N Const) (e : Expr N Const) : Prop :=
  ∃ c v, v.Value ∧ Expr.Subexpression (.app (.constant c) v) e ∧ δ.delta c v = none

/-- p.40 is expressed relationally because the source gives no value for
    divergence. Zero steps are allowed for an expression already faulty. -/
def EvaluatesWrong (δ : PrimitiveReduction N Const) (context : ReductionContext δ) (e : Expr N Const) : Prop :=
  ∃ e', Relation.ReflTransGen context.step e e' ∧ Faulty δ e'
def EvaluatesValue (δ : PrimitiveReduction N Const) (context : ReductionContext δ) (e v : Expr N Const) : Prop :=
  Relation.ReflTransGen context.step e v ∧ v.Value

namespace Statement
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
variable (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
variable (policy : WeakeningPolicy) (N Const : Type) (δ : PrimitiveReduction N Const) (context : ReductionContext δ)

/-- p.39. A transcription, not a proof: the source does not give a type
    compatibility condition for delta. Its mathematical adequacy is deferred to proof review. -/
def lemma8Printed (presentation : ConstraintPresentation X) : Prop :=
  CoreAssumptions X S policy → X.StronglySound S presentation →
  ∀ C (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e e' s s' φ,
    Typing X S policy C Γ e s → φ.IsSubstitution →
    Environment.Substitutes φ Γ Δ → Scheme.Substitutes φ s s' →
    X.envFV Δ = ∅ → X.schemeFV s' = ∅ → X.Entails ∅ (C.subst φ) →
    X.ConsistentEnvironment S φ Γ → Relation.TransGen context.step e e' →
      Typing X S policy ∅ Δ e' s'

/-- Explicitly a conjecture in the dissertation, p.40; it assumes Sound,
    not StronglySound. It is not promoted to a theorem here. -/
def conjecture1 : Prop := CoreAssumptions X S policy → X.Sound S →
  ∀ C (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s s' φ,
    Typing X S policy C Γ e s → φ.IsSubstitution →
    Environment.Substitutes φ Γ Δ → Scheme.Substitutes φ s s' →
    X.envFV Δ = ∅ → X.schemeFV s' = ∅ → X.Entails ∅ (C.subst φ) →
    X.ConsistentEnvironment S φ Γ → ¬ EvaluatesWrong δ context e
end Statement
end
end HMX
