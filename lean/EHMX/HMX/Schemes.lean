import EHMX.HMX.Theory

namespace EHMX.HMX
variable {T : TypeSyntax}

/-- Figure 3.1 uses flat qualified schemes (§3.4.5). -/
inductive Scheme (X : Theory T) where
  | mono : T.Term → Scheme X
  | qualified : Names → X.Formula → T.Term → Scheme X

/-- The rule presentation and the chosen solved set are independent parameters. -/
inductive Presentation where
  | term | constraint
  deriving DecidableEq

inductive Fragment where
  | core | handlers
  deriving DecidableEq

def Scheme.InPresentation {X : Theory T} (p : Presentation) : Scheme X → Prop
  | .mono t | .qualified _ _ t => p = .term ∨ T.InConstraintForm t

/-- Storage bounds are used only for allocation. -/
def Scheme.support {X : Theory T} : Scheme X → Names
  | .mono t => T.support t
  | .qualified a c t => ((X.support c).union (T.support t)).diff a

noncomputable def Scheme.freeNames {X : Theory T} : Scheme X → Names
  | .mono t => T.support t
  | .qualified a c t => ((X.freeNames c).union (T.support t)).diff a

def Scheme.Avoids {X : Theory T} (s : Scheme X) (a : Names) : Prop := a.Disjoint s.freeNames

def Scheme.Closed {X : Theory T} (s : Scheme X) : Prop := s.freeNames = Names.empty

def Scheme.Admissible {X : Theory T} (S : X.Formula → Prop) : Scheme X → Prop
  | .mono _ => True
  | .qualified _ c _ => X.Admissible S c

/-- Freshen binders before simultaneous substitution. -/
def Scheme.subst {X : Theory T} (σ : FiniteSubstitution T) : Scheme X → Scheme X
  | .mono t => .mono (σ.apply t)
  | .qualified a c t =>
      let names := (X.support c).union (T.support t)
      let avoid := names.union (σ.imageNames names)
      let lifted := σ.underBinder a avoid
      .qualified (a.freshImage avoid) (X.subst lifted c) (lifted.apply t)

/-- §3.2: schemes are identified up to bound renaming and logical equivalence
of qualifiers. This relation makes those identifications explicit in Lean. -/
inductive Scheme.Equivalent (X : Theory T) : Scheme X → Scheme X → Prop where
  | refl (s) : Equivalent X s s
  | symm {s t} : Equivalent X s t → Equivalent X t s
  | trans {s t u} : Equivalent X s t → Equivalent X t u → Equivalent X s u
  | qualifier {a c d t} : X.Equivalent c d →
      Equivalent X (.qualified a c t) (.qualified a d t)
  | rename (p : Renaming) {a c t} :
      (∀ i ∈ (Scheme.qualified (X := X) a c t).freeNames.types, p.types i = i) →
      (∀ i ∈ (Scheme.qualified (X := X) a c t).freeNames.effects, p.effects i = i) →
      Equivalent X (.qualified a c t)
        (.qualified ⟨a.types.image p.types, a.effects.image p.effects⟩
          (X.subst (p.asFiniteSubstitution T) c) (T.rename p.types p.effects t))

/-- The finite initial constant environment is part of Γ. Local variables use
De Bruijn indices. Each constant has at most one declaration. -/
structure Context (X : Theory T) where
  constants : List (Constant × Scheme X) := []
  locals : List (Scheme X) := []
  uniqueConstants : (constants.map Prod.fst).Nodup

def Context.extend {X : Theory T} (g : Context X) (s : Scheme X) : Context X :=
  { g with locals := s :: g.locals }

def Context.lookupConstant {X : Theory T} (g : Context X) (k : Constant) : Option (Scheme X) :=
  (g.constants.find? (fun entry => entry.1 == k)).map Prod.snd

def Context.schemes {X : Theory T} (g : Context X) : List (Scheme X) :=
  g.constants.map Prod.snd ++ g.locals

def Context.support {X : Theory T} (g : Context X) : Names :=
  g.schemes.foldr (fun s a => s.support.union a) Names.empty

noncomputable def Context.freeNames {X : Theory T} (g : Context X) : Names :=
  g.schemes.foldr (fun s a => s.freeNames.union a) Names.empty

def Context.Closed {X : Theory T} (g : Context X) : Prop := g.freeNames = Names.empty

def Context.Avoids {X : Theory T} (g : Context X) (a : Names) : Prop := a.Disjoint g.freeNames

def Context.Admissible {X : Theory T} (g : Context X) (S : X.Formula → Prop) : Prop :=
  ∀ s ∈ g.schemes, s.Admissible S

def Context.InPresentation {X : Theory T} (g : Context X) (p : Presentation) : Prop :=
  ∀ s ∈ g.schemes, s.InPresentation p

def Context.subst {X : Theory T} (g : Context X) (σ : FiniteSubstitution T) : Context X :=
  ⟨g.constants.map (fun (k,s) => (k, s.subst σ)), g.locals.map (Scheme.subst σ), by
    simpa only [List.map_map, Function.comp_def] using g.uniqueConstants⟩

/-- Pointwise relations preserve the constant names as well as local positions. -/
def Context.Rel {X : Theory T} (R : Scheme X → Scheme X → Prop) (g h : Context X) : Prop :=
  List.Forall₂ (fun x y => x.1 = y.1 ∧ R x.2 y.2) g.constants h.constants ∧
  List.Forall₂ R g.locals h.locals

def Context.Equivalent {X : Theory T} := Context.Rel (Scheme.Equivalent X)

/-- Original relation i, with general targets in forallLeft. The unguarded
forallRight conclusion is the explicitly retained EHMX change. -/
inductive Comparison (X : Theory T) : X.Formula → Scheme X → Scheme X → Type where
  | sub {c a b} : X.Entails c (X.le a b) → Comparison X c (.mono a) (.mono b)
  | forallLeft {c a d t target} (σ : Substitution T) :
      (X.domain σ).Subset a → X.Entails c (X.subst σ d) →
      Comparison X c (.mono (σ.apply t)) target →
      Comparison X c (.qualified a d t) target
  | forallRight {c a d t s} : X.Avoids c a → s.Avoids a →
      Comparison X (X.and c d) s (.mono t) → Comparison X c s (.qualified a d t)
  | equivalent {c d s t} : X.Equivalent c d → Comparison X c s t → Comparison X d s t
  | schemeLeft {c s s' t} : Scheme.Equivalent X s s' →
      Comparison X c s' t → Comparison X c s t
  | schemeRight {c s t t'} : Scheme.Equivalent X t t' →
      Comparison X c s t → Comparison X c s t'

/-- Appendix p.197: every judgment constraint, including C ∧ D, is admissible.
No global conjunction closure is imposed. -/
def Comparison.Valid {X : Theory T} (S : X.Formula → Prop) {c s t}
    (d : Comparison X c s t) : Prop :=
  X.Admissible S c ∧ match d with
    | .sub _ => True
    | .forallLeft _ _ _ d | .forallRight _ _ d => d.Valid S
    | .equivalent _ d | .schemeLeft _ d | .schemeRight _ d => d.Valid S

def Instance (X : Theory T) (c : X.Formula) (s t : Scheme X) : Prop :=
  Nonempty (Comparison X c s t)

def SolvedInstance (X : Theory T) (S : X.Formula → Prop) (c : X.Formula) (s t : Scheme X) : Prop :=
  ∃ d : Comparison X c s t, d.Valid S

/-- Definitions 14 and 15. -/
def Context.Instance {X : Theory T} (c : X.Formula) := Context.Rel (EHMX.HMX.Instance X c)

def Context.ConstrainedInstance {X : Theory T} (c d : X.Formula) (g h : Context X) : Prop :=
  X.Entails c d ∧ Context.Instance c g h

/-- Definition 17; substitution freshens scheme binders. Admissibility includes
logical representatives, in accordance with §3.2. -/
def Scheme.Consistent {X : Theory T} (S : X.Formula → Prop) (σ : Substitution T)
    (s : Scheme X) : Prop := (s.subst σ).Admissible S

def Context.Consistent {X : Theory T} (S : X.Formula → Prop) (σ : Substitution T)
    (g : Context X) : Prop := (g.subst σ).Admissible S

def Scheme.Realizable {X : Theory T} (c : X.Formula) (s : Scheme X) : Prop :=
  ∃ t, Instance X c s (.mono t)

def Context.Realizable {X : Theory T} (c : X.Formula) (g : Context X) : Prop :=
  ∀ s ∈ g.schemes, s.Realizable c

/-- Definition 18: source in Xc, target and C in Xt. The first instance
comparison is under top, independently of the maximality constraint C. -/
def Scheme.Approximates {X : Theory T} (S : X.Formula → Prop)
    (c : X.Formula) (source target : Scheme X) : Prop :=
  source.Admissible X.Satisfiable ∧ target.Admissible S ∧ X.Admissible S c ∧
  Instance X X.top source target ∧
  ∀ u, u.Admissible S → SolvedInstance X S c source u → SolvedInstance X S c target u

def Context.Approximates {X : Theory T} (S : X.Formula → Prop)
    (c : X.Formula) := Context.Rel (Scheme.Approximates S c)

/-- §3.4.4 generalization is a relation. In particular it neither fixes the
maximal binder set nor adds an unprinted C ≡ C₁ ∧ C₂ premise. -/
def Generalizes {X : Theory T} (S : X.Formula → Prop) (c : X.Formula)
    (g : Context X) (t : T.Term) (outer : X.Formula) (result : Scheme X) : Prop :=
  X.Admissible S c ∧ X.Admissible S outer ∧ result.Admissible S ∧
  ∃ a c₁ c₂, X.Equivalent outer (X.existsNames a c) ∧
    X.Equivalent outer (X.and c₁ (X.existsNames a c₂)) ∧
    Scheme.Equivalent X result (.qualified a c₂ t) ∧ X.Avoids c₁ a ∧ g.Avoids a

end EHMX.HMX
