import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic

/-! Pure HM(X) syntax. Source: main.pdf, §§3.1–3.2.
No declarations in this file assert any of the dissertation's results.
-/
namespace HMX
noncomputable section
local instance syntaxDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance syntaxDecidable (p : Prop) : Decidable p := Classical.propDecidable p

universe u v w

/-- The distinguished binary constructor is represented by `Ty.arrow`.
    `arity` supplies the other constructors of the open signature. -/
inductive Ty (V : Type u) (K : Type v) (arity : K → Nat) where
  | var : V → Ty V K arity
  | arrow : Ty V K arity → Ty V K arity → Ty V K arity
  | con (k : K) : (Fin (arity k) → Ty V K arity) → Ty V K arity

namespace Ty
variable {V : Type u} {K : Type v} {arity : K → Nat}

def fv : Ty V K arity → Finset V
  | .var a => {a}
  | .arrow t u => t.fv ∪ u.fv
  | .con _ ts => Finset.univ.biUnion fun i => (ts i).fv

def subst (φ : V → Ty V K arity) : Ty V K arity → Ty V K arity
  | .var a => φ a
  | .arrow t u => .arrow (t.subst φ) (u.subst φ)
  | .con k ts => .con k fun i => (ts i).subst φ

/-- Definition 8: 'monotype' means a *closed* type in the source. -/
def IsMonotype (t : Ty V K arity) : Prop := t.fv = ∅
/-- The smaller type grammar of §3.7, p.76. Predicates still use the full algebra. -/
def ConstraintForm : Ty V K arity → Prop
  | .var _ => True
  | .arrow t u => ConstraintForm t ∧ ConstraintForm u
  | .con _ _ => False
end Ty

abbrev Assignment (V : Type u) (K : Type v) (arity : K → Nat) := V → Ty V K arity

namespace Assignment
variable {V : Type u} {K : Type v} {arity : K → Nat}
def id : Assignment V K arity := Ty.var
def domain (φ : Assignment V K arity) : Set V := {a | φ a ≠ .var a}
def codomain (φ : Assignment V K arity) : Set V := {b | ∃ a ∈ φ.domain, b ∈ (φ a).fv}
def comp (ψ φ : Assignment V K arity) : Assignment V K arity := fun a => (φ a).subst ψ
def restrict (φ : Assignment V K arity) (A : Set V) : Assignment V K arity :=
  fun a => if a ∈ A then φ a else .var a
def without (φ : Assignment V K arity) (A : Set V) : Assignment V K arity := φ.restrict Aᶜ
def single (a : V) (t : Ty V K arity) : Assignment V K arity :=
  fun b => if b = a then t else .var b

/-- Definition 6. Intermediate mappings are NOT silently assumed idempotent. -/
def IsSubstitution (φ : Assignment V K arity) : Prop :=
  φ.domain.Finite ∧ ∀ a, (φ a).subst φ = φ a

def IsRenaming (φ : Assignment V K arity) : Prop :=
  ∃ π : Equiv.Perm V, {a | π a ≠ a}.Finite ∧ φ = fun a => Ty.var (π a)
end Assignment

/-- Primitive predicates; equality and the type-order predicate are distinguished.
    Projection is an operation of the constraint theory, not an interpretation. -/
inductive Predicate (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) where
  | equal : Ty V K arity → Ty V K arity → Predicate V K arity P parity
  | less : Ty V K arity → Ty V K arity → Predicate V K arity P parity
  | atom (p : P) : (Fin (parity p) → Ty V K arity) → Predicate V K arity P parity

abbrev Constraint (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) := Finset (Predicate V K arity P parity)

namespace Predicate
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
def fv : Predicate V K arity P parity → Finset V
  | .equal t u | .less t u => t.fv ∪ u.fv
  | .atom _ ts => Finset.univ.biUnion fun i => (ts i).fv
def subst (φ : Assignment V K arity) : Predicate V K arity P parity → Predicate V K arity P parity
  | .equal t u => .equal (t.subst φ) (u.subst φ)
  | .less t u => .less (t.subst φ) (u.subst φ)
  | .atom p ts => .atom p fun i => (ts i).subst φ
end Predicate

namespace Constraint
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
def subst (φ : Assignment V K arity) (C : Constraint V K arity P parity) : Constraint V K arity P parity :=
  C.image (Predicate.subst φ)
/-- Syntactic occurrence, deliberately distinct from Definition 4's semantic FV. -/
def occurrences (C : Constraint V K arity P parity) : Finset V := C.biUnion Predicate.fv
def eq (t u : Ty V K arity) : Constraint V K arity P parity := {.equal t u}
def le (t u : Ty V K arity) : Constraint V K arity P parity := {.less t u}
def graphOn (φ : Assignment V K arity) (A : Finset V) : Constraint V K arity P parity :=
  A.image fun a => .equal (.var a) (φ a)
end Constraint

/-- Recursive schemes (§3.2); flat schemes used by Figure 3.1 are a subclass. -/
inductive Scheme (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) where
  | type : Ty V K arity → Scheme V K arity P parity
  | all : Finset V → Constraint V K arity P parity → Scheme V K arity P parity →
      Scheme V K arity P parity

namespace Scheme
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
def occurrences : Scheme V K arity P parity → Finset V
  | .type t => t.fv
  | .all A C s => (C.occurrences ∪ s.occurrences) \ A
def Flat : Scheme V K arity P parity → Prop
  | .type _ => True
  | .all _ _ (.type _) => True
  | _ => False
def ConstraintForm : Scheme V K arity P parity → Prop
  | .type t => t.ConstraintForm
  | .all _ _ s => ConstraintForm s

/-- A binder-preserving step of capture-avoiding substitution. Its domain is
    explicit; fresh representatives are provided by `Alpha` below. -/
def subst (φ : Assignment V K arity) : Scheme V K arity P parity → Scheme V K arity P parity
  | .type t => .type (t.subst φ)
  | .all A C s =>
      let ψ := φ.without A
      .all A (C.subst ψ) (s.subst ψ)

def Safe (φ : Assignment V K arity) : Scheme V K arity P parity → Prop
  | .type _ => True
  | .all A _ s => Disjoint (A : Set V) (φ.codomain) ∧ Safe (φ.without A) s

/-- Renaming all names, including bound names, by a permutation. -/
def rename (π : Equiv.Perm V) : Scheme V K arity P parity → Scheme V K arity P parity
  | .type t => .type (t.subst fun a => .var (π a))
  | .all A C s => .all (A.image π) (C.subst fun a => .var (π a)) (s.rename π)

inductive Alpha : Scheme V K arity P parity → Scheme V K arity P parity → Prop
  | refl (s) : Alpha s s
  | symm : Alpha s t → Alpha t s
  | trans : Alpha s t → Alpha t u → Alpha s u
  | congr : Alpha s t → Alpha (.all A C s) (.all A C t)
  | rename (π : Equiv.Perm V) (s : Scheme V K arity P parity)
      (fixes : ∀ a ∈ s.occurrences, π a = a) : Alpha s (s.rename π)

/-- Relational capture avoidance avoids postulating a substitution oracle. -/
def Substitutes (φ : Assignment V K arity) (s t : Scheme V K arity P parity) : Prop :=
  ∃ s', Alpha s s' ∧ Safe φ s' ∧ Alpha (s'.subst φ) t
end Scheme

/-- Constants are distinguished from locally bound term variables (§3.2). -/
inductive Expr (N : Type*) (Const : Type*) where
  | var : N → Expr N Const
  | constant : Const → Expr N Const
  | lam : N → Expr N Const → Expr N Const
  | app : Expr N Const → Expr N Const → Expr N Const
  | letE : N → Expr N Const → Expr N Const → Expr N Const

inductive Expr.Value : Expr N Const → Prop
  | var : Value (.var x)
  | constant : Value (.constant c)
  | lam : Value (.lam x e)

abbrev Environment (N : Type*) (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) := List (N × Scheme V K arity P parity)

namespace Environment
variable {N : Type*} {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
def lookup (Γ : Environment N V K arity P parity) (x : N) : Option (Scheme V K arity P parity) :=
  match Γ with
  | [] => none
  | (y, s) :: Γ => if x = y then some s else lookup Γ x
def WellFormed (Γ : Environment N V K arity P parity) : Prop := (Γ.map Prod.fst).Nodup
def erase (Γ : Environment N V K arity P parity) (x : N) :=
  Γ.filter (fun binding => binding.1 ≠ x)
def extend (Γ : Environment N V K arity P parity) (x : N) (s : Scheme V K arity P parity) :=
  (x, s) :: Γ.erase x
def Substitutes (φ : Assignment V K arity)
    (Γ Δ : Environment N V K arity P parity) : Prop :=
  Γ.WellFormed ∧ Δ.WellFormed ∧ ∀ x,
    (Γ.lookup x = none ↔ Δ.lookup x = none) ∧
    ∀ s t, Γ.lookup x = some s → Δ.lookup x = some t → Scheme.Substitutes φ s t
end Environment
end
end HMX
