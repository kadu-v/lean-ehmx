import EHMX.HMX.Normalization

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

inductive Scheme (X : Constraints T O) where
  | mono : T.Term → Scheme X
  | qualified : Names → X.Formula → T.Term → Scheme X

def Scheme.support {X : Constraints T O} : Scheme X → Names
  | .mono t => T.support t
  | .qualified a c t => ((X.support c).union (T.support t)).diff a

/-- Logical freshness uses semantic free variables of constraints. Finite
implementation supports may be larger and are not used in this definition. -/
def Scheme.FreeType {X : Constraints T O} : Scheme X → Nat → Prop
  | .mono t, i => i ∈ (T.support t).types
  | .qualified a c t, i => i ∉ a.types ∧
      (X.FreeType c i ∨ i ∈ (T.support t).types)

def Scheme.FreeEffect {X : Constraints T O} : Scheme X → Nat → Prop
  | .mono t, i => i ∈ (T.support t).effects
  | .qualified a c t, i => i ∉ a.effects ∧
      (X.FreeEffect c i ∨ i ∈ (T.support t).effects)

def Scheme.Avoids {X : Constraints T O} (s : Scheme X) (a : Names) : Prop :=
  (∀ i ∈ a.types, ¬ s.FreeType i) ∧ (∀ i ∈ a.effects, ¬ s.FreeEffect i)

def Constraints.Avoids (X : Constraints T O) (c : X.Formula) (a : Names) : Prop :=
  (∀ i ∈ a.types, ¬ X.FreeType c i) ∧ (∀ i ∈ a.effects, ¬ X.FreeEffect c i)

/-- The paper treats schemes modulo changes of bound names. This closure
records that convention explicitly for the named-variable representation. -/
inductive Scheme.AlphaEquivalent (X : Constraints T O) : Scheme X → Scheme X → Prop where
  | refl (s) : AlphaEquivalent X s s
  | symm {s t} : AlphaEquivalent X s t → AlphaEquivalent X t s
  | trans {s t u} : AlphaEquivalent X s t → AlphaEquivalent X t u → AlphaEquivalent X s u
  | rename (p : Renaming) {a c t} :
      (∀ i, (Scheme.qualified (X := X) a c t).FreeType i → p.types i = i) →
      (∀ i, (Scheme.qualified (X := X) a c t).FreeEffect i → p.effects i = i) →
      AlphaEquivalent X (.qualified a c t)
        (.qualified ⟨a.types.image p.types, a.effects.image p.effects⟩
          (X.subst (p.asSubstitution T) c) (T.rename p.types p.effects t))

abbrev Context (X : Constraints T O) := List (Scheme X)

def Context.support {X : Constraints T O} (g : Context X) : Names :=
  g.foldr (fun s a => s.support.union a) Names.empty

/-- HM(X), dissertation §3.4.1, instance rules. In particular this is a derivable
relation on schemes, not the inclusion of sets of ground instances. -/
inductive Instance (X : Constraints T O) : X.Formula → Scheme X → Scheme X → Prop where
  | sub {c a b} : X.Entails c (X.le a b) → Instance X c (.mono a) (.mono b)
  | forallLeft {c a d t t'} (s : Substitution T) :
      s.domain.types ⊆ a.types → s.domain.effects ⊆ a.effects →
      X.Entails c (X.subst s d) →
      Instance X c (.mono (s.apply t)) (.mono t') →
      Instance X c (.qualified a d t) (.mono t')
  | forallRight {c a d t s} :
      X.Avoids c a → s.Avoids a →
      Instance X (X.and c d) s (.mono t) →
      Instance X (X.and c (X.existsNames a d)) s (.qualified a d t)
  | equivalent {c d s t} : X.Equivalent c d → Instance X c s t → Instance X d s t
  | alphaLeft {c s s' t} : Scheme.AlphaEquivalent X s s' →
      Instance X c s' t → Instance X c s t
  | alphaRight {c s t t'} : Scheme.AlphaEquivalent X t t' →
      Instance X c s t → Instance X c s t'

def Scheme.Realizable {X : Constraints T O} (c : X.Formula) (s : Scheme X) : Prop :=
  ∃ t, Instance X c s (.mono t)

def Context.Realizable {X : Constraints T O} (c : X.Formula) (g : Context X) : Prop :=
  ∀ s ∈ g, s.Realizable c

def Scheme.Admissible {X : Constraints T O} (solved : X.Formula → Prop) :
    Scheme X → Prop
  | .mono _ => True
  | .qualified _ c _ => X.Admissible solved c

/-- Constraint-relative repair of dissertation Definition 18. Both comparisons
use the constraint of the typing judgment; an unconditional first comparison
would fail even in the satisfiability-based fragment. -/
def Scheme.Approximates {X : Constraints T O} (solved : X.Formula → Prop)
    (c : X.Formula) (source target : Scheme X) : Prop :=
  target.Admissible solved ∧ Instance X c source target ∧
    ∀ t, t.Admissible solved → Instance X c source t → Instance X c target t

/-- An explicit initial environment is the fifth component of an HM(X)
instance. Type constructors, comparison, constraints, and solved forms are
independent parameters; the operation signature is an effect extension. -/
structure Framework where
  types : TypeDomain
  order : TypeOrder types
  constraints : Constraints types order
  solved : constraints.Formula → Prop
  solved_satisfiable : ∀ c, solved c → constraints.Satisfiable c
  initial : Context constraints
  initial_admissible : ∀ s ∈ initial, s.Admissible solved

/-- Original conditional principal-pair statement. Both outer entailment and
the syntactic instance judgment are essential parts of its conclusion. -/
def PrincipalPair {X : Constraints T O}
    (typing : X.Formula → Context X → Expr → Scheme X → Prop)
    (g : Context X) (e : Expr) (c : X.Formula) (s : Scheme X) : Prop :=
  typing c g e s ∧ ∀ d s', typing d g e s' →
    X.Entails d c ∧ Instance X d s s'

end EHMX.HMX
