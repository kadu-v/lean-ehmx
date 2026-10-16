import EHMX.HMX.TermConstraintTheory

namespace EHMX.HMX

/-- HM(X)'s logical type comparison and EHMX's effect predicates. The
presentation fixes substitution on predicate arguments; none of these fields
chooses a ground interpretation or a solver. -/
structure Theory (T : TypeSyntax) extends TermConstraintTheory T where
  le_refl : ∀ a b, Entails (language.atom (.typeEq a b))
    (and (language.atom (.typeLe a b)) (language.atom (.typeLe b a)))
  le_antisymm : ∀ a b, Entails
    (and (language.atom (.typeLe a b)) (language.atom (.typeLe b a))) (language.atom (.typeEq a b))
  le_trans : ∀ a b c, Entails
    (and (language.atom (.typeLe a b)) (language.atom (.typeLe b c)))
    (language.atom (.typeLe a c))
  /-- Effects are equal; type domains are contravariant. -/
  le_arrow : ∀ a a' b b' e, Entails
    (and (language.atom (.typeLe a' a)) (language.atom (.typeLe b b')))
    (language.atom (.typeLe (T.arrow a e b) (T.arrow a' e b')))
  /-- EHMX analogues of equality and D6 for the effect sort. -/
  effectEq_refl : ∀ e, Entails top (language.atom (.effectEq e e))
  effectEq_symm : ∀ e f, Entails (language.atom (.effectEq e f)) (language.atom (.effectEq f e))
  effectEq_trans : ∀ e f g, Entails
    (and (language.atom (.effectEq e f)) (language.atom (.effectEq f g)))
    (language.atom (.effectEq e g))
  effectEq_congr : ∀ i e f (h : Effect), Entails (language.atom (.effectEq e f))
    (language.atom (.effectEq
      (h.subst (FiniteSubstitution.singleEffect T i e).effects)
      (h.subst (FiniteSubstitution.singleEffect T i f).effects)))
  typeEq_effect_congr : ∀ i e f t, Entails (language.atom (.effectEq e f))
    (language.atom (.typeEq
      ((FiniteSubstitution.singleEffect T i e).apply t)
      ((FiniteSubstitution.singleEffect T i f).apply t)))
  effect_predicate_project : ∀ i e (p : ConstraintAtom T language.predicates), i ∉ e.vars →
    toConstraintTheory.Equivalent (language.atom (p.subst (FiniteSubstitution.singleEffect T i e)))
      (existsNames ⟨∅, {i}⟩ (and (language.atom p) (language.atom (.effectEq (Effect.var i) e))))
  /-- Universal projection is an EHMX operation, dual in order to exists. -/
  forall_elim : ∀ a c, Entails (language.forallNames a c) c
  forall_mono : ∀ a {c d}, Entails c d →
    Entails (language.forallNames a c) (language.forallNames a d)
  forall_adjunction : ∀ a c d, toConstraintTheory.Equivalent (existsNames a c) c →
    (Entails c (language.forallNames a d) ↔ Entails c d)
  forall_support : ∀ a c, (support (language.forallNames a c)).Subset ((support c).diff a)
  effectLe_refl : ∀ e, Entails top (language.atom (.effectLe e e))
  effectLe_trans : ∀ e f g, Entails
    (and (language.atom (.effectLe e f)) (language.atom (.effectLe f g)))
    (language.atom (.effectLe e g))
  effectLe_antisymm : ∀ e f, Entails
    (and (language.atom (.effectLe e f)) (language.atom (.effectLe f e))) (language.atom (.effectEq e f))
  effectEq_le : ∀ e f, Entails (language.atom (.effectEq e f)) (language.atom (.effectLe e f))
  effectLe_empty : ∀ e, Entails top (language.atom (.effectLe ∅ e))
  effectLe_union : ∀ e f g, toConstraintTheory.Equivalent
    (language.atom (.effectLe (e ∪ f) g))
    (and (language.atom (.effectLe e g)) (language.atom (.effectLe f g)))
  effectLe_in_union : ∀ e f, Entails top (language.atom (.effectLe e (e ∪ f)))
  lacks_empty : ∀ op, Entails top (language.atom (.lacks op ∅))
  lacks_union : ∀ op e f, toConstraintTheory.Equivalent
    (language.atom (.lacks op (e ∪ f)))
    (and (language.atom (.lacks op e)) (language.atom (.lacks op f)))
  lacks_singleton : ∀ op other, op ≠ other →
    Entails top (language.atom (.lacks op (Effect.singleton other)))
  lacks_self_unsatisfiable : ∀ op, ¬ toConstraintTheory.Satisfiable
    (language.atom (.lacks op (Effect.singleton op)))

namespace Theory
variable {T : TypeSyntax} (X : Theory T)

abbrev Equivalent := X.toConstraintTheory.Equivalent
abbrev Admissible := X.toConstraintTheory.Admissible
abbrev Satisfiable := X.toConstraintTheory.Satisfiable
noncomputable abbrev freeNames := X.toConstraintTheory.freeNames
abbrev FreeType := X.toConstraintTheory.FreeType
abbrev FreeEffect := X.toConstraintTheory.FreeEffect
abbrev subst := X.language.subst
abbrev eq := X.toTermConstraintTheory.eq
noncomputable abbrev domain (_X : Theory T) (s : FiniteSubstitution T) := s.changedNames
def effectEq (e f : Effect) := X.language.atom (.effectEq e f)
def le (a b : T.Term) := X.language.atom (.typeLe a b)
def effectLe (a b : Effect) := X.language.atom (.effectLe a b)
def lacks (op : Op) (e : Effect) := X.language.atom (.lacks op e)
def clause (rigid witnesses : Names) (c : X.Formula) :=
  X.language.forallNames rigid (X.existsNames witnesses c)
def Avoids (c : X.Formula) (a : Names) : Prop :=
  (∀ i ∈ a.types, ¬ X.FreeType c i) ∧ (∀ i ∈ a.effects, ¬ X.FreeEffect c i)
def conjunction (cs : List X.Formula) : X.Formula := cs.foldr X.and X.top
def split (op : Op) (input rest : Effect) : X.Formula :=
  X.and (X.effectLe rest input)
    (X.and (X.effectLe input (Effect.singleton op ∪ rest)) (X.lacks op rest))

/-- An equivalence-preserving simplifier, not a solver or a typing oracle. -/
structure Simplifier where
  run : X.Formula → X.Formula
  equivalent : ∀ c, X.Equivalent (run c) c

def Simplifier.identity : X.Simplifier := ⟨id, X.toConstraintTheory.equivalent_refl⟩

/-- Definition 26: no new type equalities, stated as logical entailment.
This is not syntactic reflection of variable equality. Effect equalities are
not prohibited by the agreed EHMX extension. -/
def TypeEquationFree (S : X.Formula → Prop) : Prop :=
  ∀ c, S c → ∀ t u, X.Entails c (X.eq t u) → X.Entails X.top (X.eq t u)

/-- Definition 28(iv), on literal representatives in S. -/
def Lifting (S : X.Formula → Prop) : Prop :=
  ∀ a c, S (X.existsNames a c) →
    ∃ θ : Substitution T, θ.changedNames.Subset a ∧ S (X.subst θ c)

/-- The admissible version is stated separately; it is not silently identified
with the literal representative condition in Definition 28(iv). -/
def AdmissibleLifting (S : X.Formula → Prop) : Prop :=
  ∀ a c, X.Admissible S (X.existsNames a c) →
    ∃ θ : Substitution T, θ.changedNames.Subset a ∧ X.Admissible S (X.subst θ c)

def RenamingClosed (S : X.Formula → Prop) : Prop :=
  ∀ c, X.Admissible S c → ∀ p : Renaming,
    X.Admissible S (X.subst (p.asFiniteSubstitution T) c)

/-- Section 3.2. Closure properties are separate conditions, not bundled
into every theorem. In particular there is no conjunction closure. -/
def SolvedForms (S : X.Formula → Prop) : Prop := ∀ c, S c → X.Satisfiable c
abbrev ProjectionClosed (S : X.Formula → Prop) := X.toConstraintTheory.ProjectionClosed S

def AgreesOn (c : X.Formula) (σ θ : FiniteSubstitution T) (u : Names) : Prop :=
  (∀ i ∈ u.types, X.Entails c (X.eq (σ.types i) (θ.types i))) ∧
  (∀ i ∈ u.effects, X.Entails c (X.effectEq (σ.effects i) (θ.effects i)))

/-- Definition 17. S is not assumed closed under all substitutions. -/
def ConsistentConstraint (S : X.Formula → Prop) (σ : Substitution T) (c : X.Formula) :=
  X.Admissible S (X.subst σ c)

end Theory

end EHMX.HMX
