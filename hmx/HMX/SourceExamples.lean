import HMX.Judgments
import HMX.Background

/-! Definitions inside the examples in §§3.1–3.2. These are specifications
of the displayed constraints, not constructed instances or proofs. The domains,
constructors and predicate interpretations are explicit parameters. -/
namespace HMX.SourceExample
noncomputable section
local instance sourceExampleDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
variable (X : ConstraintTheory V K arity P parity)

/-- Example 1, p.20: entailment relative to a class of structures and valuations.
Formula interpretation is the supplied first-order-language interpretation. -/
def FirstOrderEntails {Formula Model : Type*} {Valuation : Model → Type*}
    (models : Set Model) (satisfies : (M : Model) → Valuation M → Formula → Prop)
    (C : Finset Formula) (q : Formula) : Prop :=
  ∀ M ∈ models, ∀ η, (∀ p ∈ C, satisfies M η p) → satisfies M η q

/-- Example 2, p.21: projection produces one quantified conjunction token. -/
def FirstOrderProjection {Formula Name : Type*}
    (existsConjunction : Finset Name → Finset Formula → Formula)
    (A : Finset Name) (C : Finset Formula) : Finset Formula :=
  {existsConjunction A C}

/-- Example 1 fixes a countably infinite variable set and a subset of open
formulas. The language, its structures and valuations remain abstract. -/
def FirstOrderSystem {Formula Model Name : Type*} {Valuation : Model → Type*}
    (variableNames : Name ≃ Nat) (openFormula : Formula → Prop) (tokens : Set Formula)
    (models : Set Model) (satisfies : (M : Model) → Valuation M → Formula → Prop)
    (Y : SimpleTheory {p // p ∈ tokens}) : Prop :=
  Function.Bijective variableNames ∧ (∀ p ∈ tokens, openFormula p) ∧
  ∀ C q, Y.entailsAtom C q ↔
    ∀ M ∈ models, ∀ η, (∀ p ∈ C, satisfies M η p.val) → satisfies M η q.val

/-- Example 2: token closure and the actual projection operation, in addition
to the entailment interpretation of Example 1. -/
def FirstOrderCylindricSystem {Formula Model Name : Type*} {Valuation : Model → Type*}
    (variableNames : Name ≃ Nat) (openFormula : Formula → Prop) (tokens : Set Formula)
    (models : Set Model) (satisfies : (M : Model) → Valuation M → Formula → Prop)
    (existsConjunction : Finset Name → Finset Formula → Formula)
    (Y : CylindricSystem {p // p ∈ tokens} Name) : Prop :=
  FirstOrderSystem variableNames openFormula tokens models satisfies Y.toSimpleTheory ∧
  (∀ A C, (∀ p ∈ C, p ∈ tokens) → existsConjunction A C ∈ tokens) ∧
  ∀ a C, (Y.projectOne a C).image Subtype.val =
    FirstOrderProjection existsConjunction {a} (C.image Subtype.val)

/-- The token set of Example 3 consists exactly of pairs of free-algebra
terms. It has no primitive subsumption or other predicate constructor. -/
abbrev EqualityToken (V : Type u) (K : Type v) (arity : K → Nat) :=
  Ty V K arity × Ty V K arity

def EqualityToken.subst (φ : Assignment V K arity) (p : EqualityToken V K arity) :
    EqualityToken V K arity := (p.1.subst φ, p.2.subst φ)

/-- Definition 7 specialized to the equality-only token language of Example 3.
D4 is retained without an extra distinctness condition, just as in the source. -/
def EqualityTermLaws (Y : CylindricSystem (EqualityToken V K arity) V) : Prop :=
  (∀ a, Y.Entails ∅ {(.var a, .var a)}) ∧
  (∀ a b, Y.Entails {(.var a, .var b)} {(.var b, .var a)}) ∧
  (∀ a b c, Y.Entails {(.var a, .var b), (.var b, .var c)} {(.var a, .var c)}) ∧
  (∀ a b C, Y.Entails ({(.var a, .var b)} ∪ Y.projectOne a (C ∪ {(.var a, .var b)})) C) ∧
  (∀ t u (ctx : TermContext V K arity), Y.Entails {(t, u)} {(ctx.fill t, ctx.fill u)}) ∧
  (∀ a t p, a ∉ t.fv →
    Y.Equivalent {p.subst (Assignment.single a t)} (Y.projectOne a ({p} ∪ {(.var a, t)})))

/-- Example 3, p.24. Minimal means least entailment among term systems on
this equality-token language; the source does not construct such a system.
`Ty` is the free syntax, so the last clause states syntactic equality. -/
def Herbrand (Y : CylindricSystem (EqualityToken V K arity) V) : Prop :=
  EqualityTermLaws Y ∧
  (∀ Z : CylindricSystem (EqualityToken V K arity) V, EqualityTermLaws Z →
    ∀ C p, Y.entailsAtom C p → Z.entailsAtom C p) ∧
  ∀ t u, Y.Entails ∅ {(t, u)} ↔ t = u

/-- Example 3's last sentence, as an unproved claim about first-order unifiers. -/
def HerbrandSatisfiability (Y : CylindricSystem (EqualityToken V K arity) V) : Prop :=
  Herbrand Y → ∀ C, Y.Satisfiable C ↔
    ∃ φ : Assignment V K arity, φ.IsSubstitution ∧ ∀ p ∈ C, p.1.subst φ = p.2.subst φ

def equalityConstraints (C : Finset (EqualityToken V K arity)) :
    Constraint V K arity P parity := C.image fun p => .equal p.1 p.2

/-- Relates the equality-only system to the common HMX presentation, where
the distinguished subsumption token is an abbreviation for equality.
Coverage is up to the constraint equivalence of p.28, not new predicates. -/
def HerbrandPresentation (Y : CylindricSystem (EqualityToken V K arity) V) : Prop :=
  Herbrand Y ∧
  (∀ C D, X.Entails (equalityConstraints C) (equalityConstraints D) ↔ Y.Entails C D) ∧
  (∀ a C, X.Equivalent (X.projectOne a (equalityConstraints C))
    (equalityConstraints (Y.projectOne a C))) ∧
  ∀ C, ∃ D, X.Equivalent C (equalityConstraints D)

/-- Example 4: the dimension sort is open (`extra`); meter and second are
distinct syntax constructors. Equality modulo DIM is specified separately. -/
inductive Dimension (V : Type u) (Extra : Type v) (extraArity : Extra → Nat) where
  | var : V → Dimension V Extra extraArity
  | inverse : Dimension V Extra extraArity → Dimension V Extra extraArity
  | product : Dimension V Extra extraArity → Dimension V Extra extraArity → Dimension V Extra extraArity
  | one
  | meter
  | second
  | extra (k : Extra) : (Fin (extraArity k) → Dimension V Extra extraArity) → Dimension V Extra extraArity

/-- Example 5: unlike dimensions, the displayed index grammar is closed. -/
inductive Index (V : Type u) where
  | var : V → Index V
  | plus : Index V → Index V → Index V
  | zero
  | one

/-- The type sort in Examples 4 and 5: variables, the sort injection, arrows. -/
inductive SortedType (V : Type u) (AuxSort : Type v) where
  | var : V → SortedType V AuxSort
  | inject : AuxSort → SortedType V AuxSort
  | arrow : SortedType V AuxSort → SortedType V AuxSort → SortedType V AuxSort

def SortedType.encode (inject : AuxSort → Ty V K arity) : SortedType V AuxSort → Ty V K arity
  | .var a => .var a
  | .inject d => inject d
  | .arrow t u => .arrow (t.encode inject) (u.encode inject)

/-- A signature interpretation, kept separate from a quotient by DIM/INDEX
equations. The sort's variables are names from the same variable signature. -/
structure SortedEncoding (AuxSort : Type*) (V : Type u) (K : Type v) (arity : K → Nat) where
  term : AuxSort → Ty V K arity
  inject : AuxSort → Ty V K arity

/-- DIM1–DIM4, p.25. Dim is the dimension sort, distinct from the type sort. -/
def DimensionLaws (Dim : Type*) (dimVar : V → Dim) (inverse : Dim → Dim)
    (product : Dim → Dim → Dim) (one : Dim)
    (equality : Dim → Dim → Constraint V K arity P parity) : Prop :=
  (∀ a b, X.Entails ∅ (equality (product (dimVar a) (dimVar b))
    (product (dimVar b) (dimVar a)))) ∧
  (∀ a b c, X.Entails ∅ (equality (product (dimVar a) (product (dimVar b) (dimVar c)))
    (product (product (dimVar a) (dimVar b)) (dimVar c)))) ∧
  (∀ a, X.Entails ∅ (equality (product (dimVar a) one) (dimVar a))) ∧
  (∀ a, X.Entails ∅ (equality (product (dimVar a) (inverse (dimVar a))) one))

/-- INDEX1–INDEX3, pp.25–26. No unprinted arithmetic axiom is added. -/
def IndexLaws (Index : Type*) (plus : Index → Index → Index) (zero one : Index)
    (equality : Index → Index → Constraint V K arity P parity) : Prop :=
  X.Entails ∅ (equality (plus one zero) one) ∧
  (∀ i j, X.Entails ∅ (equality (plus i j) (plus j i))) ∧
  (∀ i j k, X.Entails ∅ (equality (plus (plus i j) k) (plus i (plus j k))))

/-- SUB1–SUB3, p.26. The subtype predicate need not be HM(X)'s subsumption. -/
def SubtypeLaws (subtype : Ty V K arity → Ty V K arity → Constraint V K arity P parity) : Prop :=
  (∀ a b, X.Equivalent (Constraint.eq (.var a) (.var b))
    (subtype (.var a) (.var b) ∪ subtype (.var b) (.var a))) ∧
  (∀ C a a' b b', X.Entails C (subtype (.var a') (.var a)) →
    X.Entails C (subtype (.var b) (.var b')) →
    X.Entails C (subtype (.arrow (.var a) (.var b)) (.arrow (.var a') (.var b')))) ∧
  (∀ C a b c, X.Entails C (subtype (.var a) (.var b)) →
    X.Entails C (subtype (.var b) (.var c)) → X.Entails C (subtype (.var a) (.var c)))

/-- SUB4–SUB6, p.27, on the ordered record fields required on p.26. -/
def RecordSubtypeLaws (Label : Type*) (ordered : List (Label × Ty V K arity) → Prop)
    (record : List (Label × Ty V K arity) → Ty V K arity)
    (intType floatType : Ty V K arity)
    (subtype : Ty V K arity → Ty V K arity → Constraint V K arity P parity) : Prop :=
  X.Entails ∅ (subtype intType floatType) ∧
  (∀ fields rest, ordered (fields ++ rest) → ordered fields →
    X.Entails ∅ (subtype (record (fields ++ rest)) (record fields))) ∧
  (∀ C fields fields', ordered fields → ordered fields' →
    List.Forall₂ (fun p q => p.1 = q.1 ∧ X.Entails C (subtype p.2 q.2)) fields fields' →
    X.Entails C (subtype (record fields) (record fields')))

/-- Examples 7–8, p.31: true-only solved forms and equality subsumption. -/
def EqualityInstance (S : Set (Constraint V K arity P parity)) : Prop :=
  S = {∅} ∧ ∀ C t u, X.Entails C (Constraint.le t u) ↔ X.Entails C (Constraint.eq t u)

/-- Example 9, p.32: satisfiable solved forms and the chosen subtype relation. -/
def SubtypeInstance (S : Set (Constraint V K arity P parity))
    (subtype : Ty V K arity → Ty V K arity → Constraint V K arity P parity) : Prop :=
  S = X.Satisfiable ∧ ∀ C t u, X.Entails C (Constraint.le t u) ↔ X.Entails C (subtype t u)

/-- Example 4: attach DIM1–DIM4 to the actual dimension terms, rather than
an unrelated predicate supplied as an arbitrary `equality` function. -/
def DIM {Extra : Type v} {extraArity : Extra → Nat}
    (encoding : SortedEncoding (Dimension V Extra extraArity) V K arity) : Prop :=
  Function.Injective encoding.term ∧
  (∀ a, encoding.term (.var a) = .var a) ∧
  Function.Injective (SortedType.encode encoding.inject) ∧
  DimensionLaws X (Dimension V Extra extraArity) Dimension.var Dimension.inverse
    Dimension.product Dimension.one (fun d e => Constraint.eq (encoding.term d) (encoding.term e))

/-- Example 5: the three displayed INDEX laws, with no unprinted arithmetic
axioms, on the closed index grammar and its injection into types. -/
def INDEX (encoding : SortedEncoding (Index V) V K arity) : Prop :=
  Function.Injective encoding.term ∧
  (∀ a, encoding.term (.var a) = .var a) ∧
  Function.Injective (SortedType.encode encoding.inject) ∧
  IndexLaws X (Index V) Index.plus Index.zero Index.one
    (fun i j => Constraint.eq (encoding.term i) (encoding.term j))

/-- Presence in the initial environment, modulo the source's representatives.
This is a declaration requirement, not a typing theorem about the primitive. -/
def InitialBinding (Γ₀ : Environment Name V K arity P parity) (name : Name)
    (s : Scheme V K arity P parity) : Prop :=
  Γ₀.WellFormed ∧ ∃ t, Γ₀.lookup name = some t ∧ SchemeRepresentative X t s

/-- Example 7, including the equality primitive in footnote 2 on p.31. -/
def HerbrandInstance (Y : CylindricSystem (EqualityToken V K arity) V)
    (S : Set (Constraint V K arity P parity))
    (Γ₀ : Environment Name V K arity P parity) (eqName : Name)
    (boolType : Ty V K arity) (a : V) : Prop :=
  HerbrandPresentation X Y ∧ EqualityInstance X S ∧
  InitialBinding X Γ₀ eqName (.all {a} ∅
    (.type (.arrow (.var a) (.arrow (.var a) boolType))))

/-- Example 8: the specified DIM theory, solved forms and div declaration.
Both quantified variables occur in the displayed type of div. -/
def DimensionInstance {Extra : Type v} {extraArity : Extra → Nat}
    (encoding : SortedEncoding (Dimension V Extra extraArity) V K arity)
    (S : Set (Constraint V K arity P parity))
    (Γ₀ : Environment Name V K arity P parity) (divName : Name) (a b : V) : Prop :=
  DIM X encoding ∧ EqualityInstance X S ∧ a ≠ b ∧
  InitialBinding X Γ₀ divName (.all {a, b} ∅ (.type
    (.arrow (encoding.inject (.var a)) (.arrow (encoding.inject (.var b))
      (encoding.inject (.product (.var a) (.inverse (.var b))))))))

/-- Example 6's record syntax is ordered by a supplied relation on labels.
The empty record and repeated labels are not silently excluded. -/
def OrderedFields (labelLE : Label → Label → Prop) (fields : List (Label × Ty V K arity)) : Prop :=
  fields.Pairwise (fun p q => labelLE p.1 q.1)

def RecordConstructorType (record : List (Label × Ty V K arity) → Ty V K arity)
    (fields : List (Label × Ty V K arity)) : Ty V K arity :=
  (fields.map Prod.snd).foldr Ty.arrow (record fields)

/-- p.38 describes the additional syntax needed for the recursive subtype
application: top, bottom and a binding recursive constructor. No unfold law
or regular-tree model is supplied by that paragraph or assumed here. -/
inductive RecursiveSubtypeType (V : Type u) (K : Type v) (arity : K → Nat) (Label : Type*) where
  | var : V → RecursiveSubtypeType V K arity Label
  | arrow : RecursiveSubtypeType V K arity Label → RecursiveSubtypeType V K arity Label →
      RecursiveSubtypeType V K arity Label
  | con (k : K) : (Fin (arity k) → RecursiveSubtypeType V K arity Label) → RecursiveSubtypeType V K arity Label
  | record : List (Label × RecursiveSubtypeType V K arity Label) → RecursiveSubtypeType V K arity Label
  | top
  | bottom
  | mu : V → RecursiveSubtypeType V K arity Label → RecursiveSubtypeType V K arity Label

/-- Example 9's record/selection declarations are type schemes whose fresh
variables are all generalized. `recordsInProgram` supplies the finite program's
record shapes; `labelsInProgram` supplies its field labels. -/
def RecordInitialEnvironment (labelLE : Label → Label → Prop)
    (record : List (Label × Ty V K arity) → Ty V K arity)
    (recordsInProgram : Set (List Label)) (labelsInProgram : Set Label)
    (makeRecord : List Label → Name) (selectField : Label → Name)
    (Γ₀ : Environment Name V K arity P parity) : Prop :=
  (∀ labels ∈ recordsInProgram, ∀ names : List V,
    names.length = labels.length → names.Nodup →
    let fields := labels.zip (names.map Ty.var)
    OrderedFields labelLE fields →
      InitialBinding X Γ₀ (makeRecord labels)
        (.all names.toFinset ∅ (.type (RecordConstructorType record fields)))) ∧
  (∀ label ∈ labelsInProgram, ∀ a,
    InitialBinding X Γ₀ (selectField label)
      (.all {a} ∅ (.type (.arrow (record [(label, .var a)]) (.var a)))))

/-- Example 9 specifies SC (SUB1–SUB6), not an arbitrary subtype relation. -/
def RecordInstance (labelLE : Label → Label → Prop)
    (record : List (Label × Ty V K arity) → Ty V K arity)
    (intType floatType : Ty V K arity)
    (subtype : Ty V K arity → Ty V K arity → Constraint V K arity P parity)
    (recordsInProgram : Set (List Label)) (labelsInProgram : Set Label)
    (makeRecord : List Label → Name) (selectField : Label → Name)
    (S : Set (Constraint V K arity P parity))
    (Γ₀ : Environment Name V K arity P parity) : Prop :=
  SubtypeLaws X subtype ∧
  RecordSubtypeLaws X Label (OrderedFields labelLE) record intType floatType subtype ∧
  SubtypeInstance X S subtype ∧
  RecordInitialEnvironment X labelLE record recordsInProgram labelsInProgram makeRecord selectField Γ₀
end
end HMX.SourceExample
