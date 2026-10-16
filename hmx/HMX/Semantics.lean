import HMX.Statements
import HMX.SoundnessConditions
import HMX.SemanticDomain

/-! §§2.2.2 and 3.3. The domain and its interpretation are parameters: the
least solution of the recursive domain equation is described by the source but
not constructed here. TermEquations and TypeEquations record the displayed equations; they
contain no soundness or ideal theorem. See audit/ambiguities.json DENOTATION. -/
namespace HMX
noncomputable section
local instance semanticsDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance semanticsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w d
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
variable {N Const : Type} {D : Type d}

/-- Data denoted by V, W, function values, constructors, and [[·]] in the text.
    No result about these data is a field. -/
structure Meaning (N Const : Type) (V : Type u) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) (D : Type d) extends DomainData Const D where
  term : Expr N Const → (N ⊕ Const → D) → D
  type : Ty V K arity → Set D
  scheme : Scheme V K arity P parity → Set D

namespace Meaning
variable (M : Meaning N Const V K arity P parity D)
variable (X : ConstraintTheory V K arity P parity)

def Models (η : N ⊕ Const → D) (Γ : Environment (N ⊕ Const) V K arity P parity) : Prop :=
  X.envFV Γ = ∅ ∧ ∀ x s, Γ.lookup x = some s → η x ∈ M.scheme s

def Coherent : Prop := ∀ t u, t.IsMonotype → u.IsMonotype →
  X.Entails ∅ (Constraint.le t u) → M.type t ⊆ M.type u

/-- pp.34–35, term equations. Constants are names in the initial environment. -/
def TermEquations [PartialOrder D] : Prop :=
  (∀ η x, M.term (.var x) η = η (.inl x)) ∧
  (∀ η c, M.term (.constant c) η = η (.inr c)) ∧
  (∀ η x e, DomainContinuous (fun v => M.term e (Function.update η (.inl x) v)) ∧
    M.term (.lam x e) η = M.functionValue (fun v => M.term e (Function.update η (.inl x) v))) ∧
  (∀ η f a, M.term (.app f a) η =
    match M.functionOf (M.term f η) with
    | some g => if M.term a η ≠ M.wrong then g (M.term a η) else M.wrong
    | none => M.wrong) ∧
  (∀ η x e b, M.term (.letE x e b) η = if M.term e η ≠ M.wrong
    then M.term b (Function.update η (.inl x) (M.term e η)) else M.wrong)

def TypeEquations [PartialOrder D] [OrderBot D]
    (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy)
    (Γ₀ : Environment (N ⊕ Const) V K arity P parity) : Prop :=
  (∀ t u, t.IsMonotype → u.IsMonotype → M.type (.arrow t u) =
    {v | ∃ f, DomainContinuous f ∧ v = M.functionValue f ∧ ∀ x ∈ M.type t, f x ∈ M.type u}) ∧
  (∀ k ts, (Ty.con k ts).IsMonotype → M.type (.con k ts) =
    {v | v = ⊥ ∨ ∃ (c : Const) (us : List (Ty V K arity)) (vs : List D),
      (∀ t ∈ us, t.IsMonotype) ∧ List.Forall₂ (fun t x => x ∈ M.type t) us vs ∧
      Typing X S policy ∅ Γ₀ (.constant c) (.type (us.foldr Ty.arrow (.con k ts))) ∧
      v = M.constructorValue c vs}) ∧
  (∀ t, t.IsMonotype → M.scheme (.type t) = M.type t) ∧
  (∀ A C s, X.schemeFV (.all A C s) = ∅ →
    M.scheme (.all A C s) =
      {v | ∀ φ s', ClosedInstantiation A φ → Scheme.Substitutes φ s s' →
        X.Entails ∅ (C.subst φ) → v ∈ M.scheme s'}) ∧
  (∀ s t, SchemeRepresentative X s t → M.scheme s = M.scheme t)

/-- The setting fixed before Lemma 6, not the conclusion of any soundness result.
The recursive scheme clause applies the displayed intersection one binder at a
 time to the recursive grammar of p.28. Constructor names come from Γ₀. -/
def ModelConditions [PartialOrder D] [OrderBot D]
    (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy)
    (Γ₀ : Environment (N ⊕ Const) V K arity P parity)
    (constructors : Set (Const × Nat)) : Prop :=
  M.toDomainData.LeastSolution constructors ∧ M.TermEquations ∧ M.TypeEquations X S policy Γ₀ ∧
  (∀ c (us : List (Ty V K arity)) k ts, (∀ t ∈ us, t.IsMonotype) → (Ty.con k ts).IsMonotype →
    Typing X S policy ∅ Γ₀ (.constant c) (.type (us.foldr Ty.arrow (.con k ts))) →
    (c, us.length) ∈ constructors)
end Meaning

namespace Statement
variable (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
variable (policy : WeakeningPolicy) (M : Meaning N Const V K arity P parity D)

variable [PartialOrder D] [OrderBot D]
variable (Γ₀ : Environment (N ⊕ Const) V K arity P parity)
variable (constructors : Set (Const × Nat))

/-- All semantic statements refer to the model fixed in §3.3.1. -/
def lemma6 : Prop := LogicalAssumptions X S → M.ModelConditions X S .conditionOnSolvedForms Γ₀ constructors → ∀ s, X.SchemeAdmissible S s → X.schemeFV s = ∅ → DomainIdeal (M.scheme s)
def lemma7 : Prop := LogicalAssumptions X S → M.ModelConditions X S .conditionOnSolvedForms Γ₀ constructors → X.Sound S → ∀ s, X.SchemeAdmissible S s → X.schemeFV s = ∅ → M.wrong ∉ M.scheme s

/-- The two conclusions and substitution/environment premises of Theorem 5.
Shared by its printed version and the unnumbered strengthened restatement. -/
def SemanticSoundnessConclusion : Prop :=
  ∀ C (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s s' φ η,
    Typing X S .conditionOnSolvedForms C Γ e s → φ.IsSubstitution →
    Environment.Substitutes φ Γ Δ → Scheme.Substitutes φ s s' →
    X.envFV Δ = ∅ → X.schemeFV s' = ∅ → X.Entails ∅ (C.subst φ) →
    X.ConsistentEnvironment S φ Γ → M.Models X η Δ →
      M.wrong ∉ M.scheme s' ∧ M.term e η ∈ M.scheme s'


def theorem5 : Prop := M.ModelConditions X S .conditionOnSolvedForms Γ₀ constructors →
  LogicalAssumptions X S → X.Sound S → M.Coherent X → SemanticSoundnessConclusion X S M

/-- pp.37–38: the author's unnumbered restatement for strongly sound systems
with projection-free solved constraints. It is not Lemma 8 on p.39. -/
def strongDenotationalSoundness (presentation : ConstraintPresentation X) : Prop :=
  M.ModelConditions X S .conditionOnSolvedForms Γ₀ constructors →
  LogicalAssumptions X S → X.StrongDenotationalConditions S presentation →
  M.Coherent X → SemanticSoundnessConclusion X S M

def corollary2 : Prop := M.ModelConditions X S .conditionOnSolvedForms Γ₀ constructors → LogicalAssumptions X S → X.Sound S → M.Coherent X →
  ∀ (Γ : Environment (N ⊕ Const) V K arity P parity) e s η,
    Typing X S .conditionOnSolvedForms ∅ Γ e s → X.envFV Γ = ∅ → X.schemeFV s = ∅ →
    M.Models X η Γ → M.term e η ≠ M.wrong

def lemma9 : Prop := LogicalAssumptions X S → M.ModelConditions X S .conditionOnSolvedForms Γ₀ constructors → X.Sound S → M.Coherent X →
  ∀ C s t s' t' φ, φ.IsSubstitution → Scheme.Substitutes φ s s' → Scheme.Substitutes φ t t' →
    X.schemeFV s' = ∅ → X.schemeFV t' = ∅ → X.ConsistentScheme S φ s →
    X.ConsistentScheme S φ t → Instance X S C s t → X.Entails ∅ (C.subst φ) →
      M.scheme s' ⊆ M.scheme t'
end Statement
end
end HMX
