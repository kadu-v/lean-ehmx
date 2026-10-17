import HMX.Binding
import Mathlib.Logic.Relation

namespace HMX

/-- Finite maps are represented by association lists with distinct keys. -/
abbrev Store := List (Nat × Expr)
def Store.dom (μ : Store) : Finset Nat := (μ.map Prod.fst).toFinset
def Store.locations (μ : Store) : Finset Id := (μ.map (fun p => p.2.fpi)).foldr (· ∪ ·) ∅
def Store.WF (L : Language) (μ : Store) : Prop :=
  (μ.map Prod.fst).Nodup ∧ ∀ p ∈ μ, Value L p.2 ∧ p.2.Closed

structure Config where
  term : Expr
  store : Store

def Expr.WF (L : Language) (t : Expr) : Prop :=
  ∀ c, Id.const c ∈ t.fpi → c ∈ L.constants

def Config.Closed (L : Language) (p : Config) : Prop :=
  p.term.Closed ∧ p.term.WF L ∧ p.store.WF L ∧
  (∀ q ∈ p.store, q.2.WF L) ∧
  ∀ m, Id.loc m ∈ p.term.fpi ∪ p.store.locations → m ∈ p.store.dom

/-- Equality of finite-map representatives, with expression alpha-conversion. -/
def Store.Equivalent (μ ν : Store) : Prop :=
  μ.dom = ν.dom ∧ ∀ p ∈ μ, ∃ q ∈ ν, p.1 = q.1 ∧ p.2.Alpha q.2

def Config.Alpha (p q : Config) : Prop :=
  p.term.Alpha q.term ∧ p.store.Equivalent q.store

inductive EvalContext where
  | hole
  | appLeft : EvalContext → Expr → EvalContext
  | appRight : Expr → EvalContext → EvalContext
  | letE : Nat → EvalContext → Expr → EvalContext

def EvalContext.plug : EvalContext → Expr → Expr
  | .hole, t => t
  | .appLeft E u, t => .app (E.plug t) u
  | .appRight v E, t => .app v (E.plug t)
  | .letE z E u, t => .letE z (E.plug t) u

def EvalContext.Valid (L : Language) (allowLet : Bool) : EvalContext → Prop
  | .hole => True
  | .appLeft E _ => E.Valid L allowLet
  | .appRight v E => Value L v ∧ E.Valid L allowLet
  | .letE _ E _ => allowLet = true ∧ E.Valid L allowLet

abbrev Delta := Config → Config → Prop

/-- p.396: fully applied destructors; stores can grow, never shrink. -/
def Delta.Requirements (L : Language) (δ : Delta) : Prop :=
  ∀ p q, δ p q → p.store.dom ⊆ q.store.dom ∧
    ∃ c vs, c ∈ L.constants ∧ ¬ L.constructor c ∧ vs.length = L.arity c ∧
      (∀ v ∈ vs, Value L v) ∧ p.term = Expr.apply c vs

/-- Figure 10-2, the base relation before evaluation-context closure. -/
inductive Step (L : Language) (δ : Delta) : Config → Config → Prop where
  | beta : Value L v → Expr.Substitutes z v t u →
      Step L δ ⟨.app (.lam z t) v, μ⟩ ⟨u, μ⟩
  | letE : Value L v → Expr.Substitutes z v t u →
      Step L δ ⟨.letE z v t, μ⟩ ⟨u, μ⟩
  | delta : δ p q → Step L δ p q
  | extend : Step L δ ⟨t, μ⟩ ⟨u, ν⟩ →
      Disjoint ξ.dom ν.dom →
      (∀ m ∈ ν.dom \ μ.dom, Id.loc m ∉ ξ.locations) →
      Step L δ ⟨t, μ ++ ξ⟩ ⟨u, ν ++ ξ⟩

  | convert : Step L δ p q → p.Alpha p' → q.Alpha q' → Step L δ p' q'

def ReduceWith (L : Language) (δ : Delta) (allowLet : Bool) (p q : Config) : Prop :=
  p.Closed L ∧ q.Closed L ∧ ∃ (E : EvalContext) (t u : Expr),
    E.Valid L allowLet ∧ p.term = E.plug t ∧ q.term = E.plug u ∧
    Step L δ ⟨t, p.store⟩ ⟨u, q.store⟩

def Reduce (L : Language) (δ : Delta) := ReduceWith L δ true

def Reducible (L : Language) (δ : Delta) (p : Config) : Prop := ∃ q, Reduce L δ p q

def Stuck (L : Language) (δ : Delta) (p : Config) : Prop :=
  p.Closed L ∧ ¬ Reducible L δ p ∧ ¬ Value L p.term

def GoesWrong (L : Language) (δ : Delta) (t : Expr) : Prop :=
  t.Closed ∧ t.Source ∧ ∃ q,
    Relation.ReflTransGen (Reduce L δ) ⟨t, []⟩ q ∧ Stuck L δ q

def PureSemantics (δ : Delta) : Prop :=
  ∀ t u μ ν, δ ⟨t, μ⟩ ⟨u, ν⟩ ↔ μ = ν ∧ δ ⟨t, []⟩ ⟨u, []⟩

/-- Definition 10.5.6, without the optional relaxed nonexpansive variant. -/
def ValueRestricted (L : Language) : Expr → Prop
  | .ident _ => True
  | .lam _ t => ValueRestricted L t
  | .app t u => ValueRestricted L t ∧ ValueRestricted L u
  | .letE _ t u => Value L t ∧ ValueRestricted L t ∧ ValueRestricted L u

/-- The restriction applies to stored programs as well as the active term. -/
def Config.ValueRestricted (L : Language) (p : Config) : Prop :=
  HMX.ValueRestricted L p.term ∧ ∀ q ∈ p.store, HMX.ValueRestricted L q.2

end HMX
