import EHMX.TypeClasses.Classes
import EHMX.HMX.SolverContract

namespace EHMX.TypeClasses
open HMX

/-- Inspectable constraints. A substitution node is a capture-avoiding
suspension: its valuation is transformed before entering any binder. -/
inductive Formula (K : Constructors) (n : Nat) where
  | top | bot
  | and : Formula K n → Formula K n → Formula K n
  | eq : Ty K → Ty K → Formula K n
  | pred : Fin n → Ty K → Formula K n
  | effectLe : Effect → Effect → Formula K n
  | lacks : Op → Effect → Formula K n
  | ex : Names → Formula K n → Formula K n
  | clause : Names → Names → Formula K n → Formula K n
  | subst : HMX.Substitution (types K) → Formula K n → Formula K n

abbrev semantic (K : Constructors) := HMX.Constraints.semantic (types K) (TypeOrder.equality (types K))

def Formula.meaning {K} (E : ClassEnv K) : Formula K E.count → (semantic K).Formula
  | .top => (semantic K).top
  | .bot => (semantic K).eq (.base .int) (.base .bool)
  | .and a b => (semantic K).and (a.meaning E) (b.meaning E)
  | .eq a b => (semantic K).eq a b
  | .pred c t => HMX.Constraints.semanticAtom (types K) (TypeOrder.equality (types K))
      ⟨t.types, t.effects⟩ (fun v => c ∈ (t.eval v).classes E) (by
        intro v w h
        rw [t.eval_support v w h.1 h.2])
  | .effectLe a b => (semantic K).effectLe a b
  | .lacks op a => (semantic K).lacks op a
  | .ex a c => (semantic K).existsNames a (c.meaning E)
  | .clause a b c => (semantic K).clause a b (c.meaning E)
  | .subst s c => (semantic K).subst s (c.meaning E)

def Formula.Holds {K} (E : ClassEnv K) (c : Formula K E.count) (v : Valuation (Ground K)) : Prop :=
  (semantic K).holds (c.meaning E) v

abbrev constraints {K} (E : ClassEnv K) : HMX.Constraints (types K) (TypeOrder.equality (types K)) where
  Formula := Formula K E.count
  holds := Formula.Holds E
  top := .top
  and := .and
  existsNames := .ex
  eq := .eq
  le := .eq
  effectLe := .effectLe
  lacks := .lacks
  clause := .clause
  subst := .subst
  support := fun c => (semantic K).support (c.meaning E)
  holds_top := (semantic K).holds_top
  holds_and := fun a b => (semantic K).holds_and (a.meaning E) (b.meaning E)
  holds_exists := fun a c => (semantic K).holds_exists a (c.meaning E)
  holds_eq := (semantic K).holds_eq
  holds_le := (semantic K).holds_eq
  holds_effectLe := (semantic K).holds_effectLe
  holds_lacks := (semantic K).holds_lacks
  holds_clause := fun a b c => (semantic K).holds_clause a b (c.meaning E)
  holds_subst := fun s c => (semantic K).holds_subst s (c.meaning E)
  holds_support := fun c => (semantic K).holds_support (c.meaning E)

@[simp] theorem holds_top {K} (E : ClassEnv K) (v) :
    Formula.Holds E .top v ↔ True := (constraints E).holds_top v

@[simp] theorem holds_and {K} (E : ClassEnv K) (a b v) :
    Formula.Holds E (.and a b) v ↔ Formula.Holds E a v ∧ Formula.Holds E b v :=
  (constraints E).holds_and a b v

@[simp] theorem holds_eq {K} (E : ClassEnv K) (a b v) :
    Formula.Holds E (.eq a b) v ↔ a.eval v = b.eval v := (constraints E).holds_eq a b v

@[simp] theorem holds_ex {K} (E : ClassEnv K) (a c v) :
    Formula.Holds E (.ex a c) v ↔ ∃ w, w.AgreeOutside v a ∧ Formula.Holds E c w :=
  (constraints E).holds_exists a c v

@[simp] theorem holds_subst {K} (E : ClassEnv K) (s c v) :
    Formula.Holds E (.subst s c) v ↔ Formula.Holds E c (s.pullback v) :=
  (constraints E).holds_subst s c v

@[simp] theorem holds_clause {K} (E : ClassEnv K) (a b c v) :
    Formula.Holds E (.clause a b c) v ↔
      ∀ w, w.AgreeOutside v a → ∃ u, u.AgreeOutside w b ∧ Formula.Holds E c u :=
  (constraints E).holds_clause a b c v

@[simp] theorem holds_effectLe {K} (E : ClassEnv K) (a b v) :
    Formula.Holds E (.effectLe a b) v ↔ a.eval v.effects ⊆ b.eval v.effects :=
  (constraints E).holds_effectLe a b v

@[simp] theorem holds_lacks {K} (E : ClassEnv K) (op a v) :
    Formula.Holds E (.lacks op a) v ↔ op ∉ a.eval v.effects :=
  (constraints E).holds_lacks op a v

theorem eval_apply {K} (s : HMX.Substitution (types K)) (t : Ty K) v :
    (s.apply t).eval v = t.eval (s.pullback v) := t.eval_subst v s.types s.effects

@[simp] theorem holds_pred {K} (E : ClassEnv K) (c t v) :
    Formula.Holds E (.pred c t) v ↔ c ∈ (t.eval v).classes E := Iff.rfl

@[simp] theorem holds_bot {K} (E : ClassEnv K) (v) :
    ¬ Formula.Holds E .bot v := by
  change ¬ Ground.base BaseTy.int = Ground.base BaseTy.bool
  simp

theorem holds_pred_declarative {K} (E : ClassEnv K) (wf : E.WellFormed) (c t v) :
    Formula.Holds E (.pred c t) v ↔ Holds E c (t.eval v) := (holds_iff E wf c _).symm

end EHMX.TypeClasses
