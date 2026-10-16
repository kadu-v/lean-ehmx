import EHMX.HMX.ConstraintTheory
import Mathlib.Data.Fintype.Fin

/-! Predicate arguments and capture-avoiding simultaneous substitution.
Existential constraints are the HM(X) syntax; universal constraints are used
only for EHMX handler clauses. No interpretation of predicates is selected. -/
namespace EHMX.HMX

def Names.shiftTypes (a : Names) (i : Nat) : Nat := a.types.sup id + 1 + i
def Names.shiftEffects (a : Names) (i : Nat) : Nat := a.effects.sup id + 1 + i

def FiniteSubstitution.freshen (T : TypeSyntax) (a : Names)
    (ft fe : Nat → Nat) : FiniteSubstitution T where
  supportBound := a
  types := fun i => if i ∈ a.types then T.var (ft i) else T.var i
  effects := fun i => if i ∈ a.effects then Effect.var (fe i) else Effect.var i
  types_outside := by intro i hi; simp [hi]
  effects_outside := by intro i hi; simp [hi]

def FiniteSubstitution.imageNames {T : TypeSyntax} (s : FiniteSubstitution T)
    (a : Names) : Names :=
  ⟨a.types.biUnion (fun i => (T.support (s.types i)).types),
    a.types.biUnion (fun i => (T.support (s.types i)).effects) ∪
      a.effects.biUnion (fun i => (s.effects i).vars)⟩

/-- Rebind A at fresh names while substituting the other free variables. -/
def FiniteSubstitution.underBinder {T : TypeSyntax} (s : FiniteSubstitution T)
    (a avoid : Names) : FiniteSubstitution T where
  supportBound := s.supportBound.union a
  types := fun i => if i ∈ a.types then T.var (avoid.shiftTypes i) else s.types i
  effects := fun i => if i ∈ a.effects then Effect.var (avoid.shiftEffects i) else s.effects i
  types_outside := by
    intro i hi
    have h := Finset.notMem_union.mp hi
    simp [h.2, s.types_outside i h.1]
  effects_outside := by
    intro i hi
    have h := Finset.notMem_union.mp hi
    simp [h.2, s.effects_outside i h.1]

def Names.freshImage (a avoid : Names) : Names :=
  ⟨a.types.image avoid.shiftTypes, a.effects.image avoid.shiftEffects⟩

/-- Arbitrary predicate symbols with a fixed type/effect arity. -/
structure PredicateSignature where
  Symbol : Type
  typeArity : Symbol → Nat
  effectArity : Symbol → Nat

inductive ConstraintAtom (T : TypeSyntax) (P : PredicateSignature) where
  | predicate (p : P.Symbol) : (Fin (P.typeArity p) → T.Term) →
      (Fin (P.effectArity p) → Effect) → ConstraintAtom T P
  | typeEq : T.Term → T.Term → ConstraintAtom T P
  | typeLe : T.Term → T.Term → ConstraintAtom T P
  | effectEq : Effect → Effect → ConstraintAtom T P
  | effectLe : Effect → Effect → ConstraintAtom T P
  | lacks : Op → Effect → ConstraintAtom T P

def ConstraintAtom.support {T P} : ConstraintAtom T P → Names
  | .predicate _ ts es =>
      ⟨Finset.univ.biUnion (fun i => (T.support (ts i)).types),
        Finset.univ.biUnion (fun i => (T.support (ts i)).effects) ∪
        Finset.univ.biUnion (fun i => (es i).vars)⟩
  | .typeEq t u | .typeLe t u => (T.support t).union (T.support u)
  | .effectEq e f | .effectLe e f => ⟨∅, e.vars ∪ f.vars⟩
  | .lacks _ e => ⟨∅, e.vars⟩

def ConstraintAtom.subst {T P} (s : FiniteSubstitution T) :
    ConstraintAtom T P → ConstraintAtom T P
  | .predicate p ts es => .predicate p (fun i => s.apply (ts i)) (fun i => (es i).subst s.effects)
  | .typeEq t u => .typeEq (s.apply t) (s.apply u)
  | .typeLe t u => .typeLe (s.apply t) (s.apply u)
  | .effectEq e f => .effectEq (e.subst s.effects) (f.subst s.effects)
  | .effectLe e f => .effectLe (e.subst s.effects) (f.subst s.effects)
  | .lacks op e => .lacks op (e.subst s.effects)

inductive ConstraintSyntax (T : TypeSyntax) (P : PredicateSignature) where
  | top : ConstraintSyntax T P
  | atom : ConstraintAtom T P → ConstraintSyntax T P
  | and : ConstraintSyntax T P → ConstraintSyntax T P → ConstraintSyntax T P
  | existsNames : Names → ConstraintSyntax T P → ConstraintSyntax T P
  | forallNames : Names → ConstraintSyntax T P → ConstraintSyntax T P

def ConstraintSyntax.support {T P} : ConstraintSyntax T P → Names
  | .top => Names.empty
  | .atom p => p.support
  | .and c d => c.support.union d.support
  | .existsNames a c | .forallNames a c => c.support.diff a

/-- The recursion is on the original body. The map is changed at binders,
so substituted terms cannot be captured, including under nested quantifiers. -/
def ConstraintSyntax.subst {T P} (s : FiniteSubstitution T) :
    ConstraintSyntax T P → ConstraintSyntax T P
  | .top => .top
  | .atom p => .atom (p.subst s)
  | .and c d => .and (c.subst s) (d.subst s)
  | .existsNames a c =>
      let avoid := c.support.union (s.imageNames c.support)
      .existsNames (a.freshImage avoid) (c.subst (s.underBinder a avoid))
  | .forallNames a c =>
      let avoid := c.support.union (s.imageNames c.support)
      .forallNames (a.freshImage avoid) (c.subst (s.underBinder a avoid))

def ConstraintSyntax.ProjectionFree {T P} : ConstraintSyntax T P → Prop
  | .top | .atom _ => True
  | .and c d => c.ProjectionFree ∧ d.ProjectionFree
  | .existsNames _ _ | .forallNames _ _ => False

/-- A presentation by predicates, conjunction and binders. The logical
formula representation may quotient syntax, but cannot contain extra opaque
constraints without such a representation. -/
structure ConstraintPresentation (T : TypeSyntax) (X : ConstraintTheory) where
  predicates : PredicateSignature
  atom : ConstraintAtom T predicates → X.Formula
  forallNames : Names → X.Formula → X.Formula
  encode : X.Formula → ConstraintSyntax T predicates

def ConstraintPresentation.denote {T X} (L : ConstraintPresentation T X) :
    ConstraintSyntax T L.predicates → X.Formula
  | .top => X.top
  | .atom p => L.atom p
  | .and c d => X.and (L.denote c) (L.denote d)
  | .existsNames a c => X.existsNames a (L.denote c)
  | .forallNames a c => L.forallNames a (L.denote c)

def ConstraintPresentation.subst {T X} (L : ConstraintPresentation T X)
    (s : FiniteSubstitution T) (c : X.Formula) : X.Formula :=
  L.denote ((L.encode c).subst s)

/-- Definition 2: finite sets of constraint tokens. A token can contain a
projection; Definition 27 separately singles out primitive predicate sets. -/
abbrev ConstraintSyntax.TokenSet (T : TypeSyntax) (P : PredicateSignature) :=
  Finset (ConstraintSyntax T P)

noncomputable def ConstraintPresentation.denoteSet {T X} (L : ConstraintPresentation T X)
    (cs : ConstraintSyntax.TokenSet T L.predicates) : X.Formula :=
  cs.toList.foldr (fun c d => X.and (L.denote c) d) X.top

noncomputable def ConstraintPresentation.predicatesSet {T X} (L : ConstraintPresentation T X)
    (ps : Finset (ConstraintAtom T L.predicates)) : X.Formula :=
  ps.toList.foldr (fun p d => X.and (L.atom p) d) X.top

end EHMX.HMX
