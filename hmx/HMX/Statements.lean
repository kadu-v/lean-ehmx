import HMX.Inference
import HMX.SyntaxDirected
import HMX.EagerInference

/-! Unproved propositions, NOT theorem constants or assumed results.
The numbered source statements and implementation obligations are kept separate.
Draft status and unresolved textual issues are recorded in audit/items.json.
-/
namespace HMX
noncomputable section
local instance statementsDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance statementsDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- The global assumptions of §§3.2 and 3.4.3, made visible at statement boundaries.
    Does NOT contain any conclusion of a numbered theorem. -/
structure CoreAssumptions (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy) : Prop where
  order : X.TypeOrderLaws
  solved : X.SolvedForms S
  weakening : policy.Valid X S

namespace Statement
variable (X : ConstraintTheory V K arity P parity)
variable (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy)
variable (N Const : Type)

def lemma2 : Prop := ∀ a C, X.Satisfiable C ↔ X.Satisfiable (X.projectOne a C)
def lemma3 : Prop := ∀ a b C, b ∉ X.fv C ∪ {a} →
  X.Equivalent (X.projectOne a C) (X.projectOne b (C.subst (Assignment.single a (.var b))))
def lemma4 : Prop := ∀ (φ : Assignment V K arity) (A : Finset V) C,
  φ.IsSubstitution → (A : Set V) = φ.domain →
    X.Equivalent (C.subst φ) (X.project A (Constraint.graphOn φ A ∪ C))
def lemma5 : Prop := ∀ (φ : Assignment V K arity) C D,
  φ.IsSubstitution → X.Entails C D → X.Entails (C.subst φ) (D.subst φ)

def lemma10 : Prop :=
  (∀ C s, X.Admissible S C → X.SchemeAdmissible S s → Instance X S C s s) ∧
  (∀ C D s t, X.Admissible S D → X.Entails D C → Instance X S C s t → Instance X S D s t) ∧
  (∀ C s t u, Instance X S C s t → Instance X S C t u → Instance X S C s u)
def lemma11 : Prop := ∀ C s t, Instance X S C s t ↔ Instance₂ X S C s t

def lemma12 : Prop := CoreAssumptions X S policy →
  ∀ C (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s s' φ,
    Typing X S policy C Γ e s → φ.IsSubstitution → X.ConsistentConstraint S φ C →
    X.ConsistentEnvironment S φ Γ → Environment.Substitutes φ Γ Δ → Scheme.Substitutes φ s s' →
      Typing X S policy (C.subst φ) Δ e s'

/-- Printed Lemma 13 is explicitly said NOT to hold in general. The printed
    conclusion retains C, although the prose describes C'. This is a specimen
    proposition to audit; it is not a theorem or a premise of other statements. -/
def lemma13Printed : Prop := ∀ C C' (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s,
  Typing X S policy C Γ e s → C' ∈ S → ConstrainedEnvironmentInstance X S C' C Δ Γ →
    Typing X S policy C Δ e s

def lemma14 : Prop := CoreAssumptions X S policy →
  ∀ C D (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s s' φ,
    Typing X S policy C Γ e s → φ.IsSubstitution → X.ConsistentEnvironment S φ Γ →
    X.ConsistentScheme S φ s → D ∈ S → X.Entails D (C.subst φ) →
    Environment.Substitutes φ Γ Δ → Scheme.Substitutes φ s s' → Typing X S policy D Δ e s'

def lemma15 : Prop := CoreAssumptions X S policy →
  ∀ C (Γ : Environment (N ⊕ Const) V K arity P parity) e s,
    Typing X S policy C Γ e s ↔ ∃ s', NormalizedTyping X S policy C Γ e s' ∧ InstanceEquivalent X S ∅ s s'
def lemma16 : Prop := CoreAssumptions X S policy →
  ∀ C (Γ : Environment (N ⊕ Const) V K arity P parity) e t,
    SyntaxDirected X S C Γ e t → Typing X S policy C Γ e (.type t)

/-- p.47. The final sigma is not bound by the printed statement; it is an
    explicit parameter here, not identified with sigma-prime. The reversed
    order of the displayed generalization pair is recorded in the audit. -/
def lemma17 (unboundSigma : Scheme V K arity P parity) : Prop := CoreAssumptions X S policy →
  ∀ C' (Γ Γ' : Environment (N ⊕ Const) V K arity P parity) e s',
    NormalizedTyping X S policy C' Γ' e s' → EnvironmentInstance X S C' Γ Γ' →
    EnvironmentRealizable X S C' Γ' →
      (∀ t, s' = .type t → ∃ C, SyntaxDirected X S C Γ e t ∧ X.Entails C' C) ∧
      (∀ A D t, s' = .all A D (.type t) → ∃ C u Co so,
        SyntaxDirected X S C Γ e u ∧ Generalizes X S C Γ (.type u) Co so ∧
        X.Entails C' Co ∧ Instance X S C' so unboundSigma)
def lemma18 : Prop := CoreAssumptions X S policy →
  ∀ C D (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e t,
    SyntaxDirected X S C Γ e t → ConstrainedEnvironmentInstance X S D C Δ Γ →
    X.Admissible S D → SyntaxDirected X S D Δ e t
def lemma19 : Prop := CoreAssumptions X X.Satisfiable policy →
  ∀ C D (Γ : Environment (N ⊕ Const) V K arity P parity) e s,
    CanonicalTyping X X.Satisfiable policy C Γ e s → X.Satisfiable D → X.Entails D C →
      CanonicalTyping X X.Satisfiable policy D Γ e s
def lemma20 : Prop := CoreAssumptions X S policy →
  ∀ C (Γ : Environment (N ⊕ Const) V K arity P parity) e s,
    Typing X S policy C Γ e s ↔ ConstraintEliminationTyping X S policy C Γ e s
def lemma21 : Prop := CoreAssumptions X X.Satisfiable policy →
  ∀ C (Γ : Environment (N ⊕ Const) V K arity P parity) e t a,
    a ∉ X.fv C ∪ X.envFV Γ ∪ (t.fv : Set V) →
    (CanonicalTyping X X.Satisfiable policy C Γ e (.type t) ↔
      CanonicalTyping X X.Satisfiable policy (C ∪ Constraint.eq (.var a) t) Γ e (.type (.var a)))

/-- D18 and Thm7 use Xc and Xt over the SAME constraint theory. -/
def theorem7 : Prop := CoreAssumptions X S policy →
  CoreAssumptions X X.Satisfiable policy →
  X.ProjectionClosed S → X.PrincipalConstraintProperty S →
  ∀ C (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e,
    X.Admissible S C → X.EnvironmentAdmissible S Δ → EnvironmentApproximates X S C Γ Δ →
      (∀ t, Typing X X.Satisfiable policy C Γ e (.type t) → Typing X S policy C Δ e (.type t)) ∧
      (∀ s, Typing X X.Satisfiable policy C Γ e s → Realizable X X.Satisfiable C s →
        ∃ s', Typing X S policy C Δ e s' ∧ Approximates X S C s s')

/-- p.74. The source calls (D,phi) a principal normal form without naming
    its input; that input is explicitly quantified here. -/
def corollary4 : Prop := CoreAssumptions X S policy →
  CoreAssumptions X X.Satisfiable policy → X.ProjectionClosed S →
  X.PrincipalConstraintProperty S →
  ∀ (p n : Problem V K arity P parity) (A : Finset V)
    (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e a,
    p.Principal X S n → (A : Set V) = n.substitution.domain →
    Environment.Substitutes n.substitution Γ Δ →
    Typing X X.Satisfiable policy (n.constraint ∪ Constraint.graphOn n.substitution A) Γ e (.type (.var a)) →
      Typing X S policy n.constraint Δ e (.type (n.substitution a))

/-- Thm8 says typability of programs, rather than preservation of their schemes. -/
def theorem8 : Prop := CoreAssumptions X S policy → CoreAssumptions X X.Satisfiable policy →
  X.PrincipalConstraintProperty S →
  ∀ e : Expr N Const,
    (∃ C Γ s, Typing X X.Satisfiable policy C Γ e s) ↔ (∃ C Γ s, Typing X S policy C Γ e s)

def lemma23 : Prop := ∀ p n m : Problem V K arity P parity,
  p.Principal X S n → p.Principal X S m → n.Equivalent X m

/-- The source prints only equation-freeness here, without nonemptiness or D25.
    These are not silently inserted. See audit issue L25. -/
def lemma25Printed : Prop := X.SolvedForms S → X.EquationFree S → X.Unitary

def lemma26 : Prop := ∀ p q n m : Problem V K arity P parity,
  q.Principal X S n → p.Principal X S m → p.NormalForm X S n → q.NormalForm X S m →
    p.Principal X S n ∧ q.Principal X S m
def lemma27 : Prop := X.PrincipalConstraintProperty S → X.Unitary →
  ∀ p q combined n : Problem V K arity P parity,
    p.IsProblem → q.IsProblem → p.Independent X q → p.Combines X q combined →
    combined.Principal X S n → ∃ p' combined',
      p.Principal X S p' ∧ p'.Combines X q combined' ∧ combined'.NormalForm X S n
def lemma28 : Prop := X.PrincipalConstraintProperty S → X.Unitary →
  ∀ p q p' combined combined' n : Problem V K arity P parity,
    p.IsProblem → q.IsProblem → p.Independent X q → p.Principal X S p' →
    p.Combines X q combined → p'.Combines X q combined' → combined'.Principal X S n →
      combined.NormalForm X S n

def lemma31 (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity) : Prop :=
  CoreAssumptions X S policy → Normalizer.Specification X S normalize → Generalizer.Specification X S gen →
  ∀ ψ C Γ e t, EagerInference X normalize gen ψ C Γ e t → TypingConfiguration X S Γ C (.type t) ψ

def theorem12 (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity) : Prop :=
  CoreAssumptions X S policy → Normalizer.Specification X S normalize → Generalizer.Specification X S gen →
  ∀ ψ C Γ Δ e t, EagerInference X normalize gen ψ C Γ e t → Environment.Substitutes ψ Γ Δ →
    Typing X S policy C Δ e (.type t) ∧ C.subst ψ = C ∧ t.subst ψ = t

/-- The section-level premises of Thm13, stated immediately before it on p.99. -/
def OriginalCompletenessAssumptions : Prop :=
  X.PrincipalConstraintProperty S ∧ X.ProjectionClosed S ∧
    (S = X.Satisfiable ∨ (X.Regular ∧ X.Unitary))
def theorem13 (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity) : Prop :=
  CoreAssumptions X S policy → Normalizer.Specification X S normalize → Generalizer.Specification X S gen →
  OriginalCompletenessAssumptions X S →
  ∀ C φ (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s,
    φ.IsSubstitution → Environment.Substitutes φ Γ Δ → Typing X S policy C Δ e s →
    EnvironmentRealizable X S C Δ → ∃ ψ D t Co so Ψ,
      EagerInference X normalize gen ψ D Γ e t ∧ Environment.Substitutes ψ Γ Ψ ∧
      Generalizes X S D Ψ (.type t) Co so ∧ ConfigurationMoreGeneral X S Γ Co so ψ C s φ

/-- p.100. The closedness hypotheses precede Corollary 5 in the source. -/
def corollary5 (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity) : Prop :=
  CoreAssumptions X S policy → Normalizer.Specification X S normalize →
  Generalizer.Specification X S gen → OriginalCompletenessAssumptions X S →
  ∀ (Γ : Environment (N ⊕ Const) V K arity P parity) e s,
    X.envFV Γ = ∅ → X.schemeFV s = ∅ → Typing X S policy ∅ Γ e s →
    EnvironmentRealizable X S ∅ Γ → ∃ ψ C t so Δ,
      EagerInference X normalize gen ψ C Γ e t ∧ Environment.Substitutes ψ Γ Δ ∧
      Generalizes X S C Δ (.type t) ∅ so ∧ Instance X S ∅ so s

def theorem14 : Prop := CoreAssumptions X X.Satisfiable policy →
  ∀ C (Γ : Environment (N ⊕ Const) V K arity P parity) e a,
    ConstraintInference X C Γ e a → Typing X X.Satisfiable policy C Γ e (.type (.var a))
def theorem15 : Prop := CoreAssumptions X X.Satisfiable policy →
  ∀ C (Γ : Environment (N ⊕ Const) V K arity P parity) e s,
    Typing X X.Satisfiable policy C Γ e s → EnvironmentRealizable X X.Satisfiable C Γ →
      ∃ C' a, ConstraintInference X C' Γ e a ∧ X.Entails C (X.project {a} C') ∧
        Instance X X.Satisfiable C (.all {a} C' (.type (.var a))) s

def ClosedJudgment (C : Constraint V K arity P parity)
    (Γ : Environment (N ⊕ Const) V K arity P parity) (s : Scheme V K arity P parity) : Prop :=
  X.fv C = ∅ ∧ X.envFV Γ = ∅ ∧ X.schemeFV s = ∅
def corollary6 : Prop := CoreAssumptions X X.Satisfiable policy →
  ∀ (Γ : Environment (N ⊕ Const) V K arity P parity) e s,
    ClosedJudgment X N Const ∅ Γ s → Typing X X.Satisfiable policy ∅ Γ e s →
    EnvironmentRealizable X X.Satisfiable ∅ Γ → ∃ C a,
      ConstraintInference X C Γ e a ∧ X.Entails ∅ (X.project {a} C) ∧
        Instance X X.Satisfiable ∅ (.all {a} C (.type (.var a))) s

/-- Thm16 requires projection closure. D28 and unitary unification are NOT
    assumptions in its printed statement. The normalizer contract is global. -/
def theorem16 (normalize : Normalizer V K arity P parity) : Prop :=
  CoreAssumptions X S policy → Normalizer.Specification X S normalize →
  X.PrincipalConstraintProperty S → X.ProjectionClosed S →
  ∀ ψ C (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e t,
    TermInference X normalize ψ C Γ e t → Environment.Substitutes ψ Γ Δ →
      Typing X S policy C Δ e (.type t) ∧ X.Equivalent (C.subst ψ) C ∧ t.subst ψ = t

/-- Thm17: one finite factor κ; its agreement is unconditional on FV(Γ).
    C constrains the scheme comparison and the output constraint entailment only. -/
def theorem17 (normalize : Normalizer V K arity P parity) : Prop :=
  CoreAssumptions X S policy → Normalizer.Specification X S normalize →
  X.PrincipalConstraintProperty S →
  ∀ C φ (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s,
    φ.IsSubstitution → Environment.Substitutes φ Γ Δ → Typing X S policy C Δ e s →
    EnvironmentRealizable X S C Δ →
      ∃ ψ D t Co so κ Ψ so',
        TermInference X normalize ψ D Γ e t ∧ Environment.Substitutes ψ Γ Ψ ∧
        Generalizes X S D Ψ (.type t) Co so ∧ X.Factors (X.envFV Γ) ψ κ φ ∧
        Scheme.Substitutes κ so so' ∧ Instance X S C so' s ∧ X.Entails C (Co.subst κ)

def corollary7 (normalize : Normalizer V K arity P parity) : Prop :=
  CoreAssumptions X S policy → Normalizer.Specification X S normalize →
  X.PrincipalConstraintProperty S →
  ∀ (Γ : Environment (N ⊕ Const) V K arity P parity) e s,
    ClosedJudgment X N Const ∅ Γ s → Typing X S policy ∅ Γ e s → EnvironmentRealizable X S ∅ Γ →
      ∃ ψ D t so Ψ,
        TermInference X normalize ψ D Γ e t ∧ Environment.Substitutes ψ Γ Ψ ∧
        Generalizes X S D Ψ (.type t) ∅ so ∧ Instance X S ∅ so s

/-- D29 quantifies over all typable (Γ,e), rather than merely defining 'a
    principal pair'. It is not assumed by the inference statements. -/
def principalTypeProperty : Prop := ∀ (Γ : Environment (N ⊕ Const) V K arity P parity) e,
  (∃ C' s', Typing X S policy C' Γ e s') → ∃ C s,
    Typing X S policy C Γ e s ∧ ∀ C' s', Typing X S policy C' Γ e s' →
      X.Entails C' C ∧ Instance X S C' s s'
end Statement
end
end HMX
