import HMX.Statements

/-! Printed variants and rule schemas that must not be silently reconciled. -/
namespace HMX
noncomputable section
local instance sourcevariantsDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
variable {N Const : Type}

namespace Problem
def IsInfimum (X : ConstraintTheory V K arity P parity)
    (A : Set (Problem V K arity P parity)) (p : Problem V K arity P parity) : Prop :=
  p.IsProblem ∧ (∀ q ∈ A, p.MoreGeneral X q) ∧
    ∀ q : Problem V K arity P parity, q.IsProblem → (∀ r ∈ A, q.MoreGeneral X r) → q.MoreGeneral X p

def IsSupremum (X : ConstraintTheory V K arity P parity)
    (A : Set (Problem V K arity P parity)) (p : Problem V K arity P parity) : Prop :=
  p.IsProblem ∧ (∀ q ∈ A, q.MoreGeneral X p) ∧
    ∀ q : Problem V K arity P parity, q.IsProblem → (∀ r ∈ A, r.MoreGeneral X q) → p.MoreGeneral X q

/-- Explicit interpretation of 'complete lower semi-lattice where least upper
bounds exist' (p.87): nonempty infima and bounded suprema, modulo equivalence.
The source gives no separate definition of this phrase; see L22 in the audit. -/
def CompleteLowerSemilattice (X : ConstraintTheory V K arity P parity) : Prop :=
  (∀ A : Set (Problem V K arity P parity), A.Nonempty → (∀ p ∈ A, p.IsProblem) →
    ∃ p, IsInfimum X A p) ∧
  (∀ A : Set (Problem V K arity P parity), (∀ p ∈ A, p.IsProblem) →
    (∃ q, q.IsProblem ∧ ∀ r ∈ A, r.MoreGeneral X q) → ∃ p, IsSupremum X A p)
end Problem

namespace Statement
variable (X : ConstraintTheory V K arity P parity) (S : Set (Constraint V K arity P parity))
def lemma22 : Prop := X.Unitary → Problem.CompleteLowerSemilattice X

/-- p.89 prints psi, not psi-prime, in the conclusion. -/
def lemma24Printed : Prop := X.SolvedForms S → X.SyntacticallyUnique S →
  ∀ p n m : Problem V K arity P parity, p.Principal X S n → p.Principal X S m →
    ∃ π : Assignment V K arity, π.IsRenaming ∧
      m.constraint = n.constraint.subst π ∧ n.substitution = π.comp n.substitution
end Statement

/- Figure 3.3 compares four rules from other systems. They are NOT added to HMX.
`J` is the judgment relation of the system being compared. -/
namespace QuantifierIntroduction
variable (X : ConstraintTheory V K arity P parity)
variable (J : Constraint V K arity P parity → Environment (N ⊕ Const) V K arity P parity →
  Expr N Const → Scheme V K arity P parity → Prop)
def Jones : Prop := ∀ C D Γ e t (A : Finset V),
  J (C ∪ D) Γ e (.type t) → Disjoint (A : Set V) (X.fv C ∪ X.envFV Γ) →
    J C Γ e (.all A D (.type t))
def AikenWimmers : Prop := ∀ C D Γ e t (A : Finset V),
  J (C ∪ D) Γ e (.type t) → X.Satisfiable D →
  Disjoint (A : Set V) (X.fv C ∪ X.envFV Γ) → J C Γ e (.all A D (.type t))
def Smith : Prop := ∀ C D Γ e t (A : Finset V) (φ : Assignment V K arity),
  J (C ∪ D) Γ e (.type t) → φ.IsSubstitution → φ.domain ⊆ (A : Set V) →
  X.Entails C (D.subst φ) → Disjoint (A : Set V) (X.fv C ∪ X.envFV Γ) →
    J C Γ e (.all A D (.type t))
def HOG : Prop := ∀ C D Γ e t (A : Finset V),
  J (C ∪ D) Γ e (.type t) → Disjoint (A : Set V) (X.fv C ∪ X.envFV Γ) →
    J (C ∪ D) Γ e (.all A D (.type t))

/-- The common elimination rule displayed below Figure 3.3, p.50. -/
def Elimination : Prop := ∀ C D Γ e t (A : Finset V) (φ : Assignment V K arity),
  J C Γ e (.all A D (.type t)) → φ.IsSubstitution → φ.domain ⊆ (A : Set V) →
  X.Entails C (D.subst φ) → J C Γ e (.type (t.subst φ))

/-- p.56. The class constraint C alpha is an explicit parameter. -/
def NipkowPrehofer (classConstraint : V → Constraint V K arity P parity) : Prop :=
  ∀ D Γ e s a, J (D ∪ classConstraint a) Γ e s →
    a ∉ X.envFV Γ ∪ X.fv D → J D Γ e (.all {a} (classConstraint a) s)

/-- The single-variable Smith rule printed on p.57, whose side condition
mentions fv(Gamma) only, unlike Figure 3.3. -/
def SmithPage57 : Prop := ∀ C D Γ e s a t,
  J (C ∪ D) Γ e s → a ∉ X.envFV Γ →
  X.Entails C (D.subst (Assignment.single a t)) → J C Γ e (.all {a} D s)

/-- p.58. pi_alpha is the conjunction of overload predicates for alpha. -/
def SystemOStep (overloads : V → Constraint V K arity P parity) : Prop :=
  ∀ C Γ e s a, J (C ∪ overloads a) Γ e s →
    a ∉ X.envFV Γ ∪ X.fv C → J C Γ e (.all {a} (overloads a) s)

/-- p.59: the dependency relation is alpha_i < alpha_j iff alpha_j is NOT
free in the result types of alpha_i and the two variables differ. The final
pi_alpha in the printed conclusion is left as a separate parameter. -/
def SystemOBatch (resultFV : V → Set V)
    (overloads : List V → Constraint V K arity P parity)
    (printedQualifier : Constraint V K arity P parity) : Prop :=
  ∀ C Γ e t (names : List V), J (C ∪ overloads names) Γ e (.type t) →
    Disjoint (names.toFinset : Set V) (X.envFV Γ ∪ X.fv C) →
    (¬ ∃ i j : Fin names.length, j < i ∧
      names[j] ∉ resultFV names[i] ∧ names[i] ≠ names[j]) →
    J C Γ e (.all names.toFinset printedQualifier (.type t))

/-- p.63. The kind syntax belongs to the compared system, not to HMX. -/
def Ohori (Kind : Type*) (kindFV : Kind → Set V)
    (hasKind : V → Kind → Constraint V K arity P parity) : Prop :=
  ∀ C Γ e s a k, J (C ∪ hasKind a k) Γ e s →
    a ∉ X.envFV Γ ∪ X.fv C → a ∉ kindFV k →
    J C Γ e (.all {a} (hasKind a k) s)
end QuantifierIntroduction

/-- p.53: the precise condition described as trivial projection. -/
def ConstraintTheory.TrivialSolvedProjections (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) : Prop :=
  ∀ C, X.Admissible S C → ∀ a ∈ X.fv C, X.Entails ∅ (X.projectOne a C)

namespace SourceRemark
/-- p.21: notation, not an extra law. -/
def remark1 : String :=
  "Constraints are finite conjunctions of tokens; conjunction binds more tightly than projection. Constraints are identified up to entailment equivalence."
/-- p.23: explanation of D1–D6, including the printed D4. -/
def remark2 : String :=
  "D1–D4 are cylindric diagonal conditions; D4 expresses substitution of equals; D5 is congruence; D6 connects syntactic substitution to projection and equality. Substitution acts componentwise on conjunction."
/-- p.93: the representative variant is a prose claim, not a fifth lifting law. -/
def remark3 : String :=
  "Equation-freeness is the only solved-form condition besides implicit satisfiability. Redundant constraints such as exists alpha. alpha=beta are allowed. Lifting still applies with the syntactic uniqueness property of Definition 24."
/-- p.209. -/
def remark6 : String :=
  "The proof of Lemma 33 relies on regularity. For X in Xc a restricted version suffices for complete inference."
/-- p.220: non-regular is intentionally retained, despite Remark 6. -/
def remark7 : String :=
  "Both original lemmas can only be proven for non-regular theories. Both hold for arbitrary theories if psi is identity and phi-prime and phi are syntactically equal on fv(Gamma)."
end SourceRemark
end
end HMX
