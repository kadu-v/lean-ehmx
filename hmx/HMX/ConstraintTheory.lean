import HMX.Syntax

namespace HMX
noncomputable section
local instance constrainttheoryDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance constrainttheoryDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w

inductive TermContext (V : Type u) (K : Type v) (arity : K → Nat) where
  | hole
  | arrowLeft : TermContext V K arity → Ty V K arity → TermContext V K arity
  | arrowRight : Ty V K arity → TermContext V K arity → TermContext V K arity
  | argument (k : K) (i : Fin (arity k)) (ts : Fin (arity k) → Ty V K arity) :
      TermContext V K arity → TermContext V K arity

def TermContext.fill {V K arity} (t : Ty V K arity) : TermContext V K arity → Ty V K arity
  | .hole => t
  | .arrowLeft c u => .arrow (c.fill t) u
  | .arrowRight u c => .arrow u (c.fill t)
  | .argument k i ts c => .con k (Function.update ts i (c.fill t))

/-- Definition 2 is independent of variables, types and projection. -/
structure SimpleTheory (Token : Type*) where
  tokensNonempty : Nonempty Token
  entailsAtom : Finset Token → Token → Prop
  C1 : ∀ C p, p ∈ C → entailsAtom C p
  C2 : ∀ C D q, (∀ p ∈ D, entailsAtom C p) → entailsAtom D q → entailsAtom C q

/-- Definition 3, for an arbitrary token set, before Definition 7 adds terms. -/
structure CylindricSystem (Token : Type v) (V : Type u) extends SimpleTheory Token where
  infiniteVariables : Infinite V
  projectOne : V → Finset Token → Finset Token
  E1 : ∀ a C p, p ∈ projectOne a C → entailsAtom C p
  E2 : ∀ a C D, (∀ p ∈ D, entailsAtom C p) →
    ∀ p ∈ projectOne a D, entailsAtom (projectOne a C) p
  E3 : ∀ a C D,
    (∀ p ∈ projectOne a (C ∪ projectOne a D), entailsAtom (projectOne a C ∪ projectOne a D) p) ∧
    (∀ p ∈ projectOne a C ∪ projectOne a D, entailsAtom (projectOne a (C ∪ projectOne a D)) p)
  E4 : ∀ a b C,
    (∀ p ∈ projectOne a (projectOne b C), entailsAtom (projectOne b (projectOne a C)) p) ∧
    (∀ p ∈ projectOne b (projectOne a C), entailsAtom (projectOne a (projectOne b C)) p)


/-- The term-predicate specialization used by Definition 7. -/
structure CylindricTheory (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) extends CylindricSystem (Predicate V K arity P parity) V

namespace CylindricSystem
variable {Token : Type v} {V : Type u} (X : CylindricSystem Token V)
def Entails (C D : Finset Token) : Prop := ∀ p ∈ D, X.entailsAtom C p
def Equivalent (C D : Finset Token) : Prop := X.Entails C D ∧ X.Entails D C
def project (A : Finset V) (C : Finset Token) := A.toList.foldr X.projectOne C
def fv (C : Finset Token) : Set V := {a | ¬ X.Equivalent (X.projectOne a C) C}
def Satisfiable (C : Finset Token) : Prop :=
  ∃ A : Finset V, (A : Set V) = X.fv C ∧ X.Entails ∅ (X.project A C)
end CylindricSystem

namespace CylindricTheory
variable {V K arity P parity} (X : CylindricTheory V K arity P parity)
def Entails (C D : Constraint V K arity P parity) : Prop := ∀ p ∈ D, X.entailsAtom C p
def Equivalent (C D : Constraint V K arity P parity) : Prop := X.Entails C D ∧ X.Entails D C
def project (A : Finset V) (C : Constraint V K arity P parity) :=
  A.toList.foldr X.projectOne C
/-- Definition 4: projection-invariant variables do NOT belong to FV. -/
def fv (C : Constraint V K arity P parity) : Set V := {a | ¬ X.Equivalent (X.projectOne a C) C}
/-- Definition 5 written with an explicit finite enumeration of fv(C).
    Whether finite support follows from the stated axioms is an audit obligation. -/
def Satisfiable (C : Constraint V K arity P parity) : Prop :=
  ∃ A : Finset V, (A : Set V) = X.fv C ∧ X.Entails ∅ (X.project A C)
end CylindricTheory

/-- Definition 7 as printed, including D4 without a distinct-variable side
    condition. This is a source transcription, not a consistency assertion. -/
structure ConstraintTheory (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) extends CylindricTheory V K arity P parity where
  D1 : ∀ a, toCylindricTheory.Entails ∅ (Constraint.eq (.var a) (.var a))
  D2 : ∀ a b, toCylindricTheory.Entails (Constraint.eq (.var a) (.var b)) (Constraint.eq (.var b) (.var a))
  D3 : ∀ a b c, toCylindricTheory.Entails
    (Constraint.eq (.var a) (.var b) ∪ Constraint.eq (.var b) (.var c)) (Constraint.eq (.var a) (.var c))
  D4 : ∀ a b C, toCylindricTheory.Entails
    (Constraint.eq (.var a) (.var b) ∪ projectOne a (C ∪ Constraint.eq (.var a) (.var b))) C
  D5 : ∀ t u (ctx : TermContext V K arity), toCylindricTheory.Entails
    (Constraint.eq t u) (Constraint.eq (ctx.fill t) (ctx.fill u))
  D6 : ∀ a t (p : Predicate V K arity P parity), a ∉ t.fv →
    toCylindricTheory.Equivalent ({p.subst (Assignment.single a t)})
      (projectOne a ({p} ∪ Constraint.eq (.var a) t))

namespace ConstraintTheory
variable {V K arity P parity} (X : ConstraintTheory V K arity P parity)
abbrev Entails := X.toCylindricTheory.Entails
abbrev Equivalent := X.toCylindricTheory.Equivalent
abbrev project := X.toCylindricTheory.project
abbrev fv := X.toCylindricTheory.fv
abbrev Satisfiable := X.toCylindricTheory.Satisfiable

def schemeFV : Scheme V K arity P parity → Set V
  | .type t => ↑t.fv
  | .all A C s => (X.fv C ∪ schemeFV s) \ ↑A
def envFV (Γ : Environment N V K arity P parity) : Set V :=
  {a | ∃ x s, Γ.lookup x = some s ∧ a ∈ X.schemeFV s}

/-- §3.2: equality of representatives, not literal membership in S. -/
def Admissible (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity) : Prop :=
  ∃ D ∈ S, X.Equivalent C D
def SchemeAdmissible (S : Set (Constraint V K arity P parity)) : Scheme V K arity P parity → Prop
  | .type _ => True
  | .all _ C s => X.Admissible S C ∧ SchemeAdmissible S s
def EnvironmentAdmissible (S : Set (Constraint V K arity P parity))
    (Γ : Environment N V K arity P parity) : Prop :=
  Γ.WellFormed ∧ ∀ x s, Γ.lookup x = some s → X.SchemeAdmissible S s

/-- D17 uses membership in S; representative admissibility stays separate. -/
def ConsistentConstraint (_X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
    (φ : Assignment V K arity) (C : Constraint V K arity P parity) : Prop := C.subst φ ∈ S
def ConsistentScheme (S : Set (Constraint V K arity P parity))
    (φ : Assignment V K arity) : Scheme V K arity P parity → Prop
  | .type _ => True
  | .all A C s => Disjoint (A : Set V) (φ.domain ∪ φ.codomain) ∧
      X.ConsistentConstraint S φ C ∧ ConsistentScheme S φ s
def ConsistentEnvironment (S : Set (Constraint V K arity P parity))
    (φ : Assignment V K arity) (Γ : Environment N V K arity P parity) : Prop :=
  ∀ x s, Γ.lookup x = some s → X.ConsistentScheme S φ s

/-- The four type-order laws of §3.2 (p.30), with variable arguments as printed. -/
structure TypeOrderLaws : Prop where
  refl : ∀ a b, X.Entails (Constraint.eq (.var a) (.var b))
    (Constraint.le (.var a) (.var b) ∪ Constraint.le (.var b) (.var a))
  asym : ∀ a b, X.Entails
    (Constraint.le (.var a) (.var b) ∪ Constraint.le (.var b) (.var a)) (Constraint.eq (.var a) (.var b))
  trans : ∀ a b c, X.Entails
    (Constraint.le (.var a) (.var b) ∪ Constraint.le (.var b) (.var c)) (Constraint.le (.var a) (.var c))
  contra : ∀ a b c d, X.Entails (Constraint.le (.var b) (.var a) ∪ Constraint.le (.var c) (.var d))
    (Constraint.le (.arrow (.var a) (.var c)) (.arrow (.var b) (.var d)))

def SolvedForms (S : Set (Constraint V K arity P parity)) : Prop := ∀ C ∈ S, X.Satisfiable C
def ProjectionClosed (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ A C, C ∈ S → X.project A C ∈ S

/-- The sufficient condition offered on p.45, NOT blanket conjunction closure. -/
def WeakeningCondition (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ A C D C', D ∈ S → C ∪ D ∈ S → C ∪ X.project A D ∈ S → C' ∈ S →
    X.Entails C' (C ∪ X.project A D) → C' ∪ D ∈ S
end ConstraintTheory
end
end HMX
