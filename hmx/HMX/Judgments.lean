import HMX.ConstraintTheory

namespace HMX
noncomputable section
local instance judgmentsDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance judgmentsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- The source identifies constraint representatives and alpha-equivalent schemes
    (§3.2 p.28 and §3.7 p.76). These are not instance comparisons. -/
inductive SchemeRepresentative (X : ConstraintTheory V K arity P parity) :
    Scheme V K arity P parity → Scheme V K arity P parity → Prop where
  | alpha : Scheme.Alpha s t → SchemeRepresentative X s t
  | qualifier : X.Equivalent C D → SchemeRepresentative X s t →
      SchemeRepresentative X (.all A C s) (.all A D t)
  | symm : SchemeRepresentative X s t → SchemeRepresentative X t s
  | trans : SchemeRepresentative X s t → SchemeRepresentative X t u → SchemeRepresentative X s u

def EnvironmentRepresentative (X : ConstraintTheory V K arity P parity)
    (Γ Δ : Environment N V K arity P parity) : Prop :=
  Γ.WellFormed ∧ Δ.WellFormed ∧ ∀ x,
    (Γ.lookup x = none ↔ Δ.lookup x = none) ∧
    ∀ s t, Γ.lookup x = some s → Δ.lookup x = some t → SchemeRepresentative X s t

/-- §3.4.1. A tree is retained so the p.197 solved-derivation proviso can be
    stated separately, without adding it to the three printed rules. -/
inductive Comparison (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (normalized : Bool := false) :
    Constraint V K arity P parity → Scheme V K arity P parity → Scheme V K arity P parity → Type (max u v w) where
  | sub (h : X.Entails C (Constraint.le t u)) : Comparison X S normalized C (.type t) (.type u)
  | right {A : Finset V} (d : Comparison X S normalized (C ∪ D) s t)
      (fresh : Disjoint (A : Set V) (X.schemeFV s ∪ X.fv C)) :
      Comparison X S normalized (C ∪ X.project A D) s (.all A D t)
  | left {A : Finset V} (φ : Assignment V K arity) (finite : φ.IsSubstitution)
      (domain : φ.domain ⊆ (A : Set V))
      (subst : Scheme.Substitutes φ s s')
      (d : Comparison X S normalized C s' t)
      (entails : X.Entails C (D.subst φ))
      (consistent : X.ConsistentScheme S φ s)
      (monoTarget : normalized = true → ∃ u, t = .type u) :
      Comparison X S normalized C (.all A D s) t
  | representatives (d : Comparison X S normalized C s t) (c : X.Equivalent C D)
      (left : SchemeRepresentative X s s') (right : SchemeRepresentative X t t') :
      Comparison X S normalized D s' t'

namespace Comparison
variable {X : ConstraintTheory V K arity P parity} {S : Set (Constraint V K arity P parity)} {normalized : Bool}
def AllSolved : Comparison X S normalized C s t → Prop
  | .sub _ => X.Admissible S C
  | .right d _ => X.Admissible S C ∧ AllSolved d
  | .left _ _ _ _ d _ _ _ => X.Admissible S C ∧ AllSolved d
  | .representatives d _ _ _ => X.Admissible S C ∧ AllSolved d
end Comparison

def Instance (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
    (C : Constraint V K arity P parity) (s t : Scheme V K arity P parity) : Prop :=
  Nonempty (Comparison X S false C s t)
def Instance₂ (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
    (C : Constraint V K arity P parity) (s t : Scheme V K arity P parity) : Prop :=
  Nonempty (Comparison X S true C s t)
def SolvedInstance (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
    (C : Constraint V K arity P parity) (s t : Scheme V K arity P parity) : Prop :=
  ∃ d : Comparison X S false C s t, d.AllSolved
def InstanceEquivalent (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity) (s t : Scheme V K arity P parity) : Prop :=
  Instance X S C s t ∧ Instance X S C t s

def EnvironmentInstance (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity)
    (Γ Δ : Environment N V K arity P parity) : Prop :=
  Γ.WellFormed ∧ Δ.WellFormed ∧ ∀ x,
    (Γ.lookup x = none ↔ Δ.lookup x = none) ∧
    ∀ s t, Γ.lookup x = some s → Δ.lookup x = some t → Instance X S C s t
def ConstrainedEnvironmentInstance (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
    (C D : Constraint V K arity P parity) (Γ Δ : Environment N V K arity P parity) : Prop :=
  EnvironmentInstance X S C Γ Δ ∧ X.Entails C D
def Realizable (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity) (s : Scheme V K arity P parity) : Prop :=
  ∃ t, Instance X S C s (.type t)
def EnvironmentRealizable (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity)
    (Γ : Environment N V K arity P parity) : Prop :=
  ∀ x s, Γ.lookup x = some s → Realizable X S C s

/-- §3.4.3 explicitly offers two alternatives. No closure under all conjunctions. -/
inductive WeakeningPolicy where
  | explicitRule
  | conditionOnSolvedForms

def WeakeningPolicy.Valid (p : WeakeningPolicy) (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity)) : Prop :=
  match p with
  | .explicitRule => True
  | .conditionOnSolvedForms => X.WeakeningCondition S

def JudgmentAdmissible (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity)
    (Γ : Environment N V K arity P parity) (s : Scheme V K arity P parity) : Prop :=
  X.Admissible S C ∧ X.EnvironmentAdmissible S Γ ∧ X.SchemeAdmissible S s

/-- Each constructor enables only rules of the named source presentation. -/
inductive LogicalStyle where
  | ordinary
  | normalized
  | constraintElimination
  | canonical
  | nested

def LogicalJudgmentAdmissible (style : LogicalStyle) (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity)
    (Γ : Environment N V K arity P parity) (s : Scheme V K arity P parity) : Prop :=
  JudgmentAdmissible X S C Γ s ∧
  (style ≠ .nested → s.Flat ∧ ∀ x t, Γ.lookup x = some t → t.Flat) ∧
  (style = .canonical → S = X.Satisfiable ∧ s.ConstraintForm ∧
    ∀ x t, Γ.lookup x = some t → t.ConstraintForm)

/-- Figure 3.1. Ordinary unrestricted let; neither effects nor a value restriction.
    `equ` exposes the source's equivalence-class convention for constraints. -/
inductive LogicalTyping {N Const : Type} (style : LogicalStyle) (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
    (policy : WeakeningPolicy) : Constraint V K arity P parity →
    Environment (N ⊕ Const) V K arity P parity → Expr N Const → Scheme V K arity P parity → Type (max u v w) where
  | var (h : Γ.lookup (.inl x) = some s) (ok : LogicalJudgmentAdmissible style X S C Γ s) :
      LogicalTyping style X S policy C Γ (.var x) s
  | constant (h : Γ.lookup (.inr c) = some s) (ok : LogicalJudgmentAdmissible style X S C Γ s) :
      LogicalTyping style X S policy C Γ (.constant c) s
  | sub (d : LogicalTyping style X S policy C Γ e (.type t)) (h : X.Entails C (Constraint.le t u))
      (ok : LogicalJudgmentAdmissible style X S C Γ (.type u)) : LogicalTyping style X S policy C Γ e (.type u)
  | abs (unbound : Γ.lookup (.inl x) = none) (d : LogicalTyping style X S policy C (Γ.extend (.inl x) (.type t)) e (.type u))
      (ok : LogicalJudgmentAdmissible style X S C Γ (.type (.arrow t u))) :
      LogicalTyping style X S policy C Γ (.lam x e) (.type (.arrow t u))
  | app (f : LogicalTyping style X S policy C Γ e₁ (.type (.arrow t u)))
      (a : LogicalTyping style X S policy C Γ e₂ (.type t)) : LogicalTyping style X S policy C Γ (.app e₁ e₂) (.type u)
  | letE (unbound : Γ.lookup (.inl x) = none) (d : LogicalTyping style X S policy C Γ e s)
      (b : LogicalTyping style X S policy C (Γ.extend (.inl x) s) e' (.type t)) :
      LogicalTyping style X S policy C Γ (.letE x e e') (.type t)
  | forallIntro {A : Finset V} (d : LogicalTyping style X S policy (C ∪ D) Γ e (.type t))
      (fresh : Disjoint (A : Set V) (X.fv C ∪ X.envFV Γ))
      (ok : LogicalJudgmentAdmissible style X S (C ∪ X.project A D) Γ (.all A D (.type t))) :
      LogicalTyping style X S policy (C ∪ X.project A D) Γ e (.all A D (.type t))
  | forallElim (enabled : style = .ordinary ∨ style = .nested) (d : LogicalTyping style X S policy C Γ e (.all A D (.type t)))
      (φ : Assignment V K arity) (finite : φ.IsSubstitution) (domain : φ.domain ⊆ (A : Set V))
      (h : X.Entails C (D.subst φ)) : LogicalTyping style X S policy C Γ e (.type (t.subst φ))
  | equ (d : LogicalTyping style X S policy C Γ e s) (h : X.Equivalent C D)
      (ok : LogicalJudgmentAdmissible style X S D Γ s) : LogicalTyping style X S policy D Γ e s
  | alpha (d : LogicalTyping style X S policy C Γ e s) (h : Scheme.Alpha s t)
      (ok : LogicalJudgmentAdmissible style X S C Γ t) : LogicalTyping style X S policy C Γ e t
  | representatives (d : LogicalTyping style X S policy C Γ e s)
      (env : EnvironmentRepresentative X Γ Δ) (scheme : SchemeRepresentative X s t)
      (ok : LogicalJudgmentAdmissible style X S C Δ t) : LogicalTyping style X S policy C Δ e t
  | weakening (enabled : policy = .explicitRule) (d : LogicalTyping style X S policy C Γ e s)
      (h : ConstrainedEnvironmentInstance X S D C Δ Γ)
      (ok : LogicalJudgmentAdmissible style X S D Δ s) : LogicalTyping style X S policy D Δ e s

  | instVar (enabled : style = .normalized) (lookup : Γ.lookup (.inl x) = some s)
      (i : Instance X S C s (.type t)) (ok : LogicalJudgmentAdmissible style X S C Γ (.type t)) :
      LogicalTyping style X S policy C Γ (.var x) (.type t)
  | instConstant (enabled : style = .normalized) (lookup : Γ.lookup (.inr c) = some s)
      (i : Instance X S C s (.type t)) (ok : LogicalJudgmentAdmissible style X S C Γ (.type t)) :
      LogicalTyping style X S policy C Γ (.constant c) (.type t)
  | constraintElim (enabled : style = .constraintElimination ∨ style = .canonical)
      (d : LogicalTyping style X S policy C Γ e (.all A D (.type t)))
      (h : X.Entails C (X.project A D)) (ok : LogicalJudgmentAdmissible style X S (C ∪ D) Γ (.type t)) :
      LogicalTyping style X S policy (C ∪ D) Γ e (.type t)
  | existsIntro (enabled : style = .canonical) {A : Finset V}
      (d : LogicalTyping style X S policy C Γ e s)
      (fresh : Disjoint (A : Set V) (X.envFV Γ ∪ X.schemeFV s))
      (ok : LogicalJudgmentAdmissible style X S (X.project A C) Γ s) :
      LogicalTyping style X S policy (X.project A C) Γ e s
  | nestedIntro (enabled : style = .nested) {A : Finset V}
      (d : LogicalTyping style X S policy (C ∪ D) Γ e s)
      (fresh : Disjoint (A : Set V) (X.fv C ∪ X.envFV Γ))
      (ok : LogicalJudgmentAdmissible style X S (C ∪ X.project A D) Γ (.all A D s)) :
      LogicalTyping style X S policy (C ∪ X.project A D) Γ e (.all A D s)
  | nestedElim (enabled : style = .nested) {A : Finset V}
      (d : LogicalTyping style X S policy C Γ e (.all A D s))
      (φ : Assignment V K arity) (finite : φ.IsSubstitution) (domain : φ.domain ⊆ (A : Set V))
      (consistent : X.ConsistentScheme S φ s) (h : X.Entails C (D.subst φ))
      (subst : Scheme.Substitutes φ s t) (ok : LogicalJudgmentAdmissible style X S C Γ t) :
      LogicalTyping style X S policy C Γ e t

namespace LogicalTyping
/-- Every left-hand constraint in a derivation, including its root (§3.5.5). -/
def AllConstraints {N Const : Type} {style : LogicalStyle} {X : ConstraintTheory V K arity P parity}
    {S : Set (Constraint V K arity P parity)} {policy : WeakeningPolicy}
    {C : Constraint V K arity P parity} {Γ : Environment (N ⊕ Const) V K arity P parity}
    {e : Expr N Const} {s : Scheme V K arity P parity}
    (Q : Constraint V K arity P parity → Prop) :
    LogicalTyping (N := N) (Const := Const) style X S policy C Γ e s → Prop
  | .var _ _ | .constant _ _ => Q C
  | .sub d _ _ | .abs _ d _ | .forallIntro d _ _ | .equ d _ _ | .alpha d _ _ =>
      Q C ∧ AllConstraints Q d
  | .app d b | .letE _ d b => Q C ∧ AllConstraints Q d ∧ AllConstraints Q b
  | .forallElim _ d _ _ _ _ => Q C ∧ AllConstraints Q d
  | .representatives d _ _ _ | .weakening _ d _ _ => Q C ∧ AllConstraints Q d
  | .instVar _ _ _ _ | .instConstant _ _ _ _ => Q C
  | .constraintElim _ d _ _ | .existsIntro _ d _ _ | .nestedIntro _ d _ _ =>
      Q C ∧ AllConstraints Q d
  | .nestedElim _ d _ _ _ _ _ _ _ => Q C ∧ AllConstraints Q d
end LogicalTyping

def Typing {N Const : Type} (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy)
    (C : Constraint V K arity P parity) (Γ : Environment (N ⊕ Const) V K arity P parity)
    (e : Expr N Const) (s : Scheme V K arity P parity) : Prop :=
  Nonempty (LogicalTyping .ordinary X S policy C Γ e s)
def NormalizedTyping {N Const : Type} (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy)
    (C : Constraint V K arity P parity) (Γ : Environment (N ⊕ Const) V K arity P parity)
    (e : Expr N Const) (s : Scheme V K arity P parity) : Prop :=
  Nonempty (LogicalTyping .normalized X S policy C Γ e s)
def ConstraintEliminationTyping {N Const : Type} (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy)
    (C : Constraint V K arity P parity) (Γ : Environment (N ⊕ Const) V K arity P parity)
    (e : Expr N Const) (s : Scheme V K arity P parity) : Prop :=
  Nonempty (LogicalTyping .constraintElimination X S policy C Γ e s)
def CanonicalTyping {N Const : Type} (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy)
    (C : Constraint V K arity P parity) (Γ : Environment (N ⊕ Const) V K arity P parity)
    (e : Expr N Const) (s : Scheme V K arity P parity) : Prop :=
  Nonempty (LogicalTyping .canonical X S policy C Γ e s)
def NestedTyping {N Const : Type} (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy)
    (C : Constraint V K arity P parity) (Γ : Environment (N ⊕ Const) V K arity P parity)
    (e : Expr N Const) (s : Scheme V K arity P parity) : Prop :=
  Nonempty (LogicalTyping .nested X S policy C Γ e s)

/-- §3.4.4, p.47. Generalization accepts a scheme, not only an unqualified type.
    This is the logical relation; a maximal-variable algorithm is separate. -/
def Generalizes (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
    (C : Constraint V K arity P parity) (Γ : Environment N V K arity P parity)
    (s : Scheme V K arity P parity) (Co : Constraint V K arity P parity) (so : Scheme V K arity P parity) : Prop :=
  ∃ A C₁ C₂, X.Equivalent Co (X.project A C) ∧
    X.Equivalent Co (C₁ ∪ X.project A C₂) ∧ so = Scheme.all A C₂ s ∧
    Disjoint (A : Set V) (X.fv C₁ ∪ X.envFV Γ) ∧
    X.Admissible S C ∧ X.Admissible S Co ∧
    X.EnvironmentAdmissible S Γ ∧ X.SchemeAdmissible S s ∧ X.SchemeAdmissible S so

/-- D18: the first comparison is UNCONDITIONAL. Both sides share X; only S differs.
    Comparison derivations use the constraint presentation when the source scheme
    is outside the target's solved forms. The p.197 proviso is audited separately. -/
def Approximates (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity) (s t : Scheme V K arity P parity) : Prop :=
  X.SchemeAdmissible X.Satisfiable s ∧ X.SchemeAdmissible S t ∧ X.Admissible S C ∧
  Instance X X.Satisfiable ∅ s t ∧
  ∀ u, X.SchemeAdmissible S u → Instance X X.Satisfiable C s u → Instance X S C t u

def EnvironmentApproximates (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity)) (C : Constraint V K arity P parity)
    (Γ Δ : Environment N V K arity P parity) : Prop :=
  Γ.WellFormed ∧ Δ.WellFormed ∧ ∀ x,
    (Γ.lookup x = none ↔ Δ.lookup x = none) ∧
    ∀ s t, Γ.lookup x = some s → Δ.lookup x = some t → Approximates X S C s t
end
end HMX
