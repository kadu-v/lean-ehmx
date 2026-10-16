import HMX.Statements

namespace HMX
noncomputable section
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- The Xc case of Appendix C.7.2 uses the identity normalizer, not an
    arbitrary choice of equivalent principal representatives (pp.219–220). -/
def SatisfiabilityNormalizer (X : ConstraintTheory V K arity P parity)
    (normalize : Normalizer V K arity P parity) : Prop :=
  ∀ p, p.IsProblem →
    (X.Satisfiable p.constraint → normalize p = some p) ∧
    (¬ X.Satisfiable p.constraint → normalize p = none)

namespace Statement
variable (X : ConstraintTheory V K arity P parity)
variable (S : Set (Constraint V K arity P parity)) (policy : WeakeningPolicy)
variable (N Const : Type)

/-- The Appendix C.6 restatement on p.201 says PRINCIPAL normal form in
its last conclusion. The body statement on p.91 only says normal form. -/
def lemma27Appendix : Prop := X.SolvedForms S → X.PrincipalConstraintProperty S → X.Unitary →
  ∀ p q combined n : Problem V K arity P parity,
    p.IsProblem → q.IsProblem → p.Independent X q → p.Combines X q combined →
    combined.Principal X S n → ∃ p' combined',
      p.Principal X S p' ∧ p'.Combines X q combined' ∧ combined'.Principal X S n

/-- pp.224–225 print W, although p.107 and the following proof use Wterm.
The printed relation is retained as the W of Figure 4.1, without adding
regularity or unitary unification to this statement. -/
def theorem17Appendix (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity)
    (normalizationCoding : ProblemCoding V K arity P parity) : Prop :=
  Normalizer.Effective normalizationCoding normalize →
  CoreAssumptions X S policy → Normalizer.Specification X S normalize →
  Generalizer.Specification X S gen → X.PrincipalConstraintProperty S →
  ∀ C φ (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s,
    φ.IsSubstitution → Environment.Substitutes φ Γ Δ → Typing X S policy C Δ e s →
    EnvironmentRealizable X S C Δ → ∃ ψ D t Co so κ Ψ so',
      EagerInference X normalize gen ψ D Γ e t ∧ Environment.Substitutes ψ Γ Ψ ∧
      Generalizes X S D Ψ (.type t) Co so ∧ X.Factors (X.envFV Γ) ψ κ φ ∧
      Scheme.Substitutes κ so so' ∧ Instance X S C so' s ∧ X.Entails C (Co.subst κ)

/-- Appendix C.7.1, p.209. Uses the printed generalization relation; the stronger maximality
    used by the proof is recorded in issue GEN-MAX, not added here. -/
def lemma33 : Prop := LogicalAssumptions X S → X.Regular → X.Unitary →
  X.PrincipalConstraintProperty S → X.ProjectionClosed S →
  ∀ C D t t' φ ψ κ (Γ Δ Ψ : Environment (N ⊕ Const) V K arity P parity) Co Do so uo,
    φ.IsSubstitution → ψ.IsSubstitution → X.Factors (X.envFV Γ) ψ κ φ →
    Environment.Substitutes φ Γ Δ → Environment.Substitutes ψ Γ Ψ → X.Entails C (D.subst κ) →
    Generalizes X S C Δ (.type t') Co so →
    Generalizes X S D Ψ (.type t) Do uo → X.Entails Co (Do.subst κ)

/-- Appendix C.7.1, p.210. The comparison of generalized schemes is under
    true. Both generalized outputs use the same witnesses as their constraints. -/
def lemma34 : Prop := LogicalAssumptions X S → X.Regular → X.Unitary →
  X.PrincipalConstraintProperty S → X.ProjectionClosed S →
  ∀ C D t t' φ ψ κ (Γ Δ Ψ : Environment (N ⊕ Const) V K arity P parity) Co Do so uo uo',
    φ.IsSubstitution → ψ.IsSubstitution → X.Factors (X.envFV Γ) ψ κ φ →
    Environment.Substitutes φ Γ Δ → Environment.Substitutes ψ Γ Ψ → X.Entails C (D.subst κ) →
    Instance X S C (.type (t.subst κ)) (.type t') →
    Generalizes X S C Δ (.type t') Co so →
    Generalizes X S D Ψ (.type t) Do uo →
    Scheme.Substitutes κ uo uo' → Instance X S ∅ uo' so

/-- Literal quantified reading of Lemma 35. Symbols omitted from its opening
    list are bound explicitly. This does NOT repair the support reasoning in
    the following proof; the audit therefore keeps this statement unverified. -/
def lemma35Printed (unusedPhiOne : Assignment V K arity) : Prop := LogicalAssumptions X S → X.Regular → X.Unitary →
  X.PrincipalConstraintProperty S → X.ProjectionClosed S → unusedPhiOne.IsSubstitution → ∀ U C₁ C₂ C' (ψ ψ₁ ψ₂ φ κ κ₁ : Assignment V K arity),
  ψ.IsSubstitution → ψ₁.IsSubstitution → ψ₂.IsSubstitution → φ.IsSubstitution →
  C₁.subst ψ₁ = C₁ → X.Entails C' (C₁.subst κ₁) →
  X.SubstitutionLUB ψ₁ ψ₂ ψ → X.Factors U ψ κ φ → X.Factors U ψ₁ κ₁ φ →
  ψ₂.codomain ∩ X.fv C₁ ⊆ U → ψ₁.codomain ∩ X.fv C₂ ⊆ U →
    X.Entails C' (C₁.subst (κ.comp ψ))

/-- Literal quantified reading of Lemma 36, including the unexplained C1,C2.
    No conclusion of this proposition is imported as an assumption elsewhere. -/
def lemma36Printed (unusedPhiOne : Assignment V K arity) : Prop := LogicalAssumptions X S → X.Regular → X.Unitary →
  X.PrincipalConstraintProperty S → X.ProjectionClosed S → unusedPhiOne.IsSubstitution → ∀ U C₁ C₂ C' s s'' s₁ s₂ (ψ ψ₁ ψ₂ φ κ κ₁ : Assignment V K arity),
  ψ.IsSubstitution → ψ₁.IsSubstitution → ψ₂.IsSubstitution → φ.IsSubstitution →
  s.subst ψ₁ = s → Scheme.Substitutes κ₁ s s₁ → Instance X S C' s₁ s'' →
  X.SubstitutionLUB ψ₁ ψ₂ ψ → X.Factors U ψ κ φ → X.Factors U ψ₁ κ₁ φ →
  ψ₂.codomain ∩ X.fv C₁ ⊆ U → ψ₁.codomain ∩ X.fv C₂ ⊆ U →
  Scheme.Substitutes (κ.comp ψ) s s₂ → Instance X S C' s₂ s''

def lemma37 (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity)
    (normalizationCoding : ProblemCoding V K arity P parity) : Prop :=
  Normalizer.Effective normalizationCoding normalize →
  CoreAssumptions X S policy → Normalizer.Specification X S normalize → Generalizer.Specification X S gen →
  X.Regular → X.Unitary → X.PrincipalConstraintProperty S → X.ProjectionClosed S →
  ∀ C' φ (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e t',
    φ.IsSubstitution → Environment.Substitutes φ Γ Δ → SyntaxDirected X S policy C' Δ e t' →
    ∃ ψ C t κ, EagerInference X normalize gen ψ C Γ e t ∧
      X.Factors (X.envFV Γ) ψ κ φ ∧ X.Entails C' (C.subst κ) ∧
      Instance X S C' (.type (t.subst κ)) (.type t')

def theorem25 (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity)
    (normalizationCoding : ProblemCoding V K arity P parity) : Prop :=
  Normalizer.Effective normalizationCoding normalize →
  CoreAssumptions X S policy → Normalizer.Specification X S normalize → Generalizer.Specification X S gen →
  X.Regular → X.Unitary → X.PrincipalConstraintProperty S → X.ProjectionClosed S →
  ∀ C φ (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s,
    φ.IsSubstitution → Environment.Substitutes φ Γ Δ → Typing X S policy C Δ e s →
    EnvironmentRealizable X S C Δ → ∃ ψ D t Co so Ψ κ so',
      EagerInference X normalize gen ψ D Γ e t ∧ Environment.Substitutes ψ Γ Ψ ∧
      Generalizes X S D Ψ (.type t) Co so ∧ X.Factors (X.envFV Γ) ψ κ φ ∧
      X.Entails C (Co.subst κ) ∧ Scheme.Substitutes κ so so' ∧ Instance X S C so' s

def lemma38 : Prop := LogicalAssumptions X X.Satisfiable → X.PrincipalConstraintProperty X.Satisfiable →
  X.ProjectionClosed X.Satisfiable →
  ∀ C D t t' φ κ (Γ Δ : Environment (N ⊕ Const) V K arity P parity) Co Do so uo,
    φ.IsSubstitution → X.Factors (X.envFV Γ) Assignment.id κ φ →
    (∀ a ∈ X.envFV Γ, κ a = φ a) → Environment.Substitutes φ Γ Δ → X.Entails C (D.subst κ) →
    Generalizes X X.Satisfiable C Δ (.type t') Co so →
    Generalizes X X.Satisfiable D Γ (.type t) Do uo → X.Entails Co (Do.subst κ)

def lemma39 : Prop := LogicalAssumptions X X.Satisfiable → X.PrincipalConstraintProperty X.Satisfiable →
  X.ProjectionClosed X.Satisfiable →
  ∀ C D t t' φ κ (Γ Δ : Environment (N ⊕ Const) V K arity P parity) Co Do so uo uo',
    φ.IsSubstitution → X.Factors (X.envFV Γ) Assignment.id κ φ →
    (∀ a ∈ X.envFV Γ, κ a = φ a) → Environment.Substitutes φ Γ Δ → X.Entails C (D.subst κ) →
    Instance X X.Satisfiable C (.type (t.subst κ)) (.type t') →
    Generalizes X X.Satisfiable C Δ (.type t') Co so →
    Generalizes X X.Satisfiable D Γ (.type t) Do uo →
    Scheme.Substitutes κ uo uo' → Instance X X.Satisfiable ∅ uo' so

/-- p.221 as printed: no factor is applied to the constraint or type in
    the last two conclusions. The proof uses a different formula (issue L40). -/
def lemma40 (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity)
    (normalizationCoding : ProblemCoding V K arity P parity) : Prop :=
  Normalizer.Effective normalizationCoding normalize →
  CoreAssumptions X X.Satisfiable policy → X.PrincipalConstraintProperty X.Satisfiable →
  SatisfiabilityNormalizer X normalize →
  Generalizer.Specification X X.Satisfiable gen →
  ∀ C' φ (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e t',
    φ.IsSubstitution → Environment.Substitutes φ Γ Δ → SyntaxDirected X X.Satisfiable policy C' Δ e t' →
    ∃ C t κ, EagerInference X normalize gen Assignment.id C Γ e t ∧
      X.Factors (X.envFV Γ) Assignment.id κ φ ∧ X.Entails C' C ∧
      Instance X X.Satisfiable C' (.type t) (.type t')

def theorem26 (normalize : Normalizer V K arity P parity)
    (gen : Generalizer (N ⊕ Const) V K arity P parity)
    (normalizationCoding : ProblemCoding V K arity P parity) : Prop :=
  Normalizer.Effective normalizationCoding normalize →
  CoreAssumptions X X.Satisfiable policy → X.PrincipalConstraintProperty X.Satisfiable →
  SatisfiabilityNormalizer X normalize →
  Generalizer.Specification X X.Satisfiable gen →
  ∀ C φ (Γ Δ : Environment (N ⊕ Const) V K arity P parity) e s,
    φ.IsSubstitution → Environment.Substitutes φ Γ Δ → Typing X X.Satisfiable policy C Δ e s →
    EnvironmentRealizable X X.Satisfiable C Δ → ∃ D t Co so κ so',
      EagerInference X normalize gen Assignment.id D Γ e t ∧
      Generalizes X X.Satisfiable D Γ (.type t) Co so ∧
      X.Factors (X.envFV Γ) Assignment.id κ φ ∧ X.Entails C (Co.subst κ) ∧
      Scheme.Substitutes κ so so' ∧ Instance X X.Satisfiable C so' s
end Statement
end
end HMX
