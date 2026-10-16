import HMX.SourceExamples
import HMX.SourceVariants

/-! The definitions and assumptions in Examples 10–18 (§3.5).
These are the displayed programs and type annotations of the compared systems,
not new HMX typing rules. Surface operations are named primitives, as in p.28.
Types and predicates of those applications remain explicit parameters. -/
namespace HMX.SourceExample.Comparison
noncomputable section
local instance comparisonExamplesDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
universe v w
variable {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}
abbrev Term := Expr String String
abbrev TypeTerm (K : Type v) (arity : K → Nat) := Ty String K arity

def call (name : String) (args : List Term) : Term :=
  args.foldl Expr.app (.constant name)
def apply (name : String) (args : List Term) : Term :=
  args.foldl Expr.app (.var name)
def alpha : TypeTerm K arity := .var "alpha"
def beta : TypeTerm K arity := .var "beta"

/-- The application-specific types of Examples 10–18. No arithmetic, class
instances or subtyping laws are asserted just by supplying these operations. -/
structure Vocabulary (K : Type v) (arity : K → Nat) where
  intType : TypeTerm K arity
  boolType : TypeTerm K arity
  charType : TypeTerm K arity
  stringType : TypeTerm K arity
  unitType : TypeTerm K arity
  listType : TypeTerm K arity → TypeTerm K arity
  comparable : TypeTerm K arity → TypeTerm K arity
  record : List (String × TypeTerm K arity) → TypeTerm K arity
  pairType : TypeTerm K arity → TypeTerm K arity → TypeTerm K arity

variable (X : ConstraintTheory String K arity P parity) (vocab : Vocabulary K arity)

/-- p.51: Comparable alpha = {less : alpha -> Bool}, the List subclass,
and Nil's polymorphic declaration. This assumption precedes Example 10. -/
def ComparableAssumptions
    (subtype : TypeTerm K arity → TypeTerm K arity → Constraint String K arity P parity)
    (Γ₀ : Environment (String ⊕ String) String K arity P parity) : Prop :=
  (∀ t, vocab.comparable t = vocab.record [("less", .arrow t vocab.boolType)]) ∧
  (∀ t, X.Entails ∅ (subtype (vocab.listType t) (vocab.comparable (vocab.listType t)))) ∧
  InitialBinding X Γ₀ (.inr "Nil")
    (.all {"alpha"} ∅ (.type (vocab.listType alpha)))

/-- p.54: the separate scenario with precisely the two listed instances. -/
def ClosedComparableAssumptions
    (subtype : TypeTerm K arity → TypeTerm K arity → Constraint String K arity P parity)
    (declaredInstances : Set (TypeTerm K arity × TypeTerm K arity)) : Prop :=
  declaredInstances = {(vocab.intType, vocab.intType), (vocab.charType, vocab.charType)} ∧
  ∀ entry ∈ declaredInstances, X.Entails ∅ (subtype entry.1 (vocab.comparable entry.2))

def example10 : Term :=
  .letE "f" (.lam "x" (call "if" [call ".less" [.var "x", .constant "true"],
    .var "x", .constant "Nil"])) (.constant "1")
def example10FunctionType
    (subtype : TypeTerm K arity → TypeTerm K arity → Constraint String K arity P parity) :=
  Scheme.all {"alpha"} (subtype (vocab.listType alpha) (vocab.comparable vocab.boolType))
    (.type (.arrow (vocab.listType alpha) (vocab.listType alpha)))

def example11 : Term :=
  .letE "y" (call ".less" [.constant "Nil", .constant "true"]) (.constant "1")
/-- Example 11 prints Comparable alpha, not Comparable Bool. -/
def example11ValueType
    (subtype : TypeTerm K arity → TypeTerm K arity → Constraint String K arity P parity) :=
  Scheme.all {"alpha"} (subtype (vocab.listType alpha) (vocab.comparable alpha)) (.type vocab.boolType)

def example12 : Term :=
  .letE "f" (.lam "x" (.letE "y" (call ".less" [.constant "Nil", .var "x"])
    (.constant "1"))) (apply "f" [.constant "true"])
def example12FunctionType :=
  Scheme.all (P := P) (parity := parity) {"beta"} ∅ (.type (.arrow beta vocab.intType))
def example12ValueType
    (subtype : TypeTerm K arity → TypeTerm K arity → Constraint String K arity P parity) :=
  Scheme.all {"alpha"} (subtype (vocab.listType alpha) (vocab.comparable beta)) (.type vocab.boolType)

def example13 : Term :=
  .letE "f" (.lam "x" (.letE "g" (.lam "y" (call ".less" [.var "y", .var "x"]))
    (.constant "1"))) (.constant "1")
def example13FunctionType := example12FunctionType (P := P) (parity := parity) vocab

/-- pp.56–58: Eq's method, the open-world projection equation, and the
alternative closed-world Int instance are distinct specifications. -/
def EqualityClassMethod
    (eqClass : TypeTerm K arity → Constraint String K arity P parity)
    (Γ₀ : Environment (String ⊕ String) String K arity P parity) : Prop :=
  InitialBinding X Γ₀ (.inr "eq") (.all {"alpha"} (eqClass alpha)
    (.type (.arrow alpha (.arrow alpha vocab.boolType))))
def OpenEqualityClass (eqClass : TypeTerm K arity → Constraint String K arity P parity) : Prop :=
  ∀ a, X.Equivalent (X.projectOne a (eqClass (.var a))) ∅
def IntegerEqualityInstance (eqClass : TypeTerm K arity → Constraint String K arity P parity) : Prop :=
  X.Entails ∅ (eqClass vocab.intType)

/-- p.58: pi_alpha is a conjunction of overload predicates, not a free
constraint unrelated to the identifiers and result types. -/
def OverloadQualifier
    (overload : String → TypeTerm K arity → Constraint String K arity P parity)
    (a : String) (methods : List (String × TypeTerm K arity)) : Constraint String K arity P parity :=
  methods.foldr (fun entry C => overload entry.1 (.arrow (.var a) entry.2) ∪ C) ∅
def OpenOverloading
    (overload : String → TypeTerm K arity → Constraint String K arity P parity) : Prop :=
  ∀ o a t, X.Equivalent (X.projectOne a (overload o (.arrow (.var a) t))) ∅

/-- pp.59–60 assume a non-overloaded equality primitive for Example 14. -/
def OverloadingInitialEnvironment
    (Γ₀ : Environment (String ⊕ String) String K arity P parity) : Prop :=
  InitialBinding X Γ₀ (.inr "eq") (.all {"alpha"} ∅
    (.type (.arrow alpha (.arrow alpha vocab.boolType))))
def example14 : Term :=
  .lam "x" (.letE "g" (.lam "y" (call "eq" [call "o" [.var "x"], .var "y"])) (.constant "1"))
def example14SystemOType
    (overload : String → TypeTerm K arity → Constraint String K arity P parity) :=
  Scheme.all {"beta"} ∅ (.all {"alpha"} (overload "o" (.arrow alpha beta))
    (.type (.arrow alpha vocab.intType)))
def example14HMXType
    (overload : String → TypeTerm K arity → Constraint String K arity P parity) :=
  Scheme.all {"alpha"} (X.project {"beta"} (overload "o" (.arrow alpha beta)))
    (.type (.arrow alpha vocab.intType))
def example14LocalType
    (overload : String → TypeTerm K arity → Constraint String K arity P parity) :=
  Scheme.all {"beta"} (overload "o" (.arrow alpha beta)) (.type (.arrow beta vocab.boolType))
def example14SystemOLocalType : Scheme String K arity P parity :=
  .type (.arrow beta vocab.boolType)

/-- Examples 15 and 16 display the same program, with annotations in 16. -/
def example15 : Term :=
  .lam "x" (.letE "g" (.lam "y" (call ";" [call "print" [.var "x", .constant "Header Information"],
    call "print" [.var "x", .var "y"]])) (call "," [apply "g" [.constant "1"], apply "g" [.constant "true"]]))
def example16 : Term := example15
/-- The printed result is Int, even though the body is a pair. Keep it. -/
def example16Type
    (overload : String → TypeTerm K arity → Constraint String K arity P parity) :=
  Scheme.all {"alpha"}
    (overload "print" (.arrow alpha (.arrow vocab.stringType vocab.unitType)) ∪
     overload "print" (.arrow alpha (.arrow vocab.intType vocab.unitType)) ∪
     overload "print" (.arrow alpha (.arrow vocab.boolType vocab.unitType)))
    (.type (.arrow alpha vocab.intType))
def example16LocalType
    (overload : String → TypeTerm K arity → Constraint String K arity P parity) :=
  Scheme.all {"beta"} (overload "print" (.arrow alpha (.arrow beta vocab.unitType)))
    (.type (.arrow beta vocab.unitType))

/-- pp.62–63: universal and record kinds and the stated record selector type. -/
inductive Kind (K : Type v) (arity : K → Nat) where
  | universal
  | record : String → TypeTerm K arity → Kind K arity
def Kind.fv : Kind K arity → Set String
  | .universal => ∅
  | .record _ t => t.fv
def RecordSelectorType
    (hasKind : TypeTerm K arity → Kind K arity → Constraint String K arity P parity)
    (label : String) :=
  Scheme.all {"alpha", "beta"}
    (hasKind beta .universal ∪ hasKind alpha (.record label beta))
    (.type (.arrow alpha beta))

def example17 : Term :=
  .lam "x" (.letE "g" (.lam "y" (call ";" [call ".print" [.var "x", .constant "Header Information"],
    call ".print" [.var "x", .var "y"]])) (call "," [apply "g" [.constant "1"], apply "g" [.constant "true"]]))
def example17Type
    (hasKind : TypeTerm K arity → Kind K arity → Constraint String K arity P parity) :=
  Scheme.all {"alpha"}
    (hasKind alpha (.record "print" (.arrow vocab.stringType vocab.unitType)) ∪
     hasKind alpha (.record "print" (.arrow vocab.intType vocab.unitType)) ∪
     hasKind alpha (.record "print" (.arrow vocab.boolType vocab.unitType)))
    (.type (.arrow alpha (vocab.pairType vocab.unitType vocab.unitType)))
def example17LocalType
    (hasKind : TypeTerm K arity → Kind K arity → Constraint String K arity P parity) :=
  Scheme.all {"beta"} (hasKind alpha (.record "print" (.arrow beta vocab.unitType)) ∪
    hasKind beta .universal) (.type (.arrow beta vocab.unitType))

/-- p.64 omits the label in {{String -> ()}}. Supply only that missing
label as a parameter, preserving the printed String -> () field type. -/
def example17IntermediateConstraint
    (hasKind : TypeTerm K arity → Kind K arity → Constraint String K arity P parity)
    (unprintedLabel : String) : Constraint String K arity P parity :=
  hasKind alpha (.record "print" (.arrow beta vocab.unitType)) ∪
  hasKind alpha (.record unprintedLabel (.arrow vocab.stringType vocab.unitType)) ∪ hasKind beta .universal

/-- p.67: the middle argument ranges over field identifiers, a separate sort.
The three-argument predicate is explicit; no arbitrary type can be a label. -/
structure FirstClassLabels (Label : Type*) (K : Type v) (arity : K → Nat)
    (P : Type w) (parity : P → Nat) where
  labelVar : String → Label
  type : Label → TypeTerm K arity
  variableType : ∀ a, type (labelVar a) = .var a
  hasField : TypeTerm K arity → Label → TypeTerm K arity → Constraint String K arity P parity

def example18 : Term :=
  .lam "x" (.letE "g" (.lam "print" (.lam "y" (call ".select" [.var "x", .var "print", .var "y"])))
    (call "," [apply "g" [.constant "print_int", .constant "1"],
      apply "g" [.constant "print_bool", .constant "true"]]))
def example18Type (labels : FirstClassLabels Label K arity P parity) (printInt printBool : Label) :=
  Scheme.all {"alpha"}
    (labels.hasField alpha printInt (.arrow vocab.intType vocab.unitType) ∪
     labels.hasField alpha printBool (.arrow vocab.boolType vocab.unitType))
    (.type (.arrow alpha (vocab.pairType vocab.unitType vocab.unitType)))
def example18LocalType (labels : FirstClassLabels Label K arity P parity) :=
  Scheme.all {"print", "beta"} (labels.hasField alpha (labels.labelVar "print") (.arrow beta vocab.unitType))
    (.type (.arrow (labels.type (labels.labelVar "print")) (.arrow beta vocab.unitType)))

/-- pp.61,64: presence is required, but no type for these primitives is
printed there. Their schemes stay explicit parameters, not invented defaults. -/
def IOInitialEnvironment (Γ₀ : Environment (String ⊕ String) String K arity P parity)
    (sequencing pairing : Scheme String K arity P parity) : Prop :=
  InitialBinding X Γ₀ (.inr ";") sequencing ∧ InitialBinding X Γ₀ (.inr ",") pairing

/-- §3.6.1, pp.70–71: List's index sort is Index, with homogeneous Int
elements. The initial environment is the displayed four-entry environment. -/
def IndexedListEnvironment (list : Index String → TypeTerm K arity) :
    Environment (String ⊕ String) String K arity P parity :=
  [(.inr "l1", .type (list .one)),
   (.inr "l2", .type (list (.plus .one .one))),
   (.inr "remove", .all {"n", "m"} ∅ (.type
     (.arrow (list (.plus (.var "n") (.var "m")))
       (.arrow (list (.var "n")) (list (.var "m")))))),
   (.inr "pair", .all {"t1", "t2"} ∅ (.type
     (.arrow (.var "t1") (.arrow (.var "t2") (vocab.pairType (.var "t1") (.var "t2"))))))]

def indexedListProgram : Term :=
  .lam "x" (.letE "y" (call "remove" [.var "x"])
    (call "pair" [apply "y" [.constant "l1"], apply "y" [.constant "l2"]]))

/-- p.72's displayed constraint, with separate fresh n',m',n'',m''. -/
def IndexedListConstraint (index : Index String → TypeTerm K arity) :
    Constraint String K arity P parity :=
  Constraint.eq alpha (index (.plus (.var "n'") (.var "m'"))) ∪
  Constraint.eq (index (.var "n'")) (index .one) ∪
  Constraint.eq (index (.var "m'")) beta ∪
  Constraint.eq alpha (index (.plus (.var "n''") (.var "m''"))) ∪
  Constraint.eq (index (.var "n''")) (index (.plus .one .one)) ∪
  Constraint.eq (index (.var "m''")) (.var "gamma")

/-- §4.1 uses mass M and time T. They are not the meter m and second s
constants of Example 4; the rest of this open grammar has the same shape. -/
inductive KennedyDimension (Extra : Type v) (extraArity : Extra → Nat) where
  | var : String → KennedyDimension Extra extraArity
  | inverse : KennedyDimension Extra extraArity → KennedyDimension Extra extraArity
  | product : KennedyDimension Extra extraArity → KennedyDimension Extra extraArity → KennedyDimension Extra extraArity
  | one
  | mass
  | time
  | extra (k : Extra) : (Fin (extraArity k) → KennedyDimension Extra extraArity) → KennedyDimension Extra extraArity

/-- p.82's div type differs from Example 8; both versions are retained. -/
def KennedyEnvironment {Extra : Type v} {extraArity : Extra → Nat}
    (dim : KennedyDimension Extra extraArity → TypeTerm K arity) :
    Environment (String ⊕ String) String K arity P parity :=
  [(.inr "kg", .type (dim .mass)), (.inr "s", .type (dim .time)),
   (.inr "div", .all {"d1", "d2"} ∅ (.type
     (.arrow (dim (.product (.var "d1") (.var "d2")))
       (.arrow (dim (.var "d1")) (dim (.var "d2")))))),
   (.inr "pair", .all {"t1", "t2"} ∅ (.type
     (.arrow (.var "t1") (.arrow (.var "t2") (vocab.pairType (.var "t1") (.var "t2"))))))]

def kennedyProgram : Term :=
  .lam "x" (.letE "y" (call "div" [.var "x"])
    (call "pair" [apply "y" [.constant "kg"], apply "y" [.constant "s"]]))
def KennedyType {Extra : Type v} {extraArity : Extra → Nat}
    (dim : KennedyDimension Extra extraArity → TypeTerm K arity) : Scheme String K arity P parity :=
  .all {"d1", "d2"} ∅ (.type (.arrow (dim (.product (.var "d1") (.var "d2")))
    (vocab.pairType (dim (.product (.inverse .mass) (.product (.var "d1") (.var "d2"))))
      (dim (.product (.inverse .time) (.product (.var "d1") (.var "d2")))))))

/-- Link the overload syntax on p.58 to its stepwise introduction rule. -/
def SystemOStepSpecification
    (overload : String → TypeTerm K arity → Constraint String K arity P parity)
    (methods : String → List (String × TypeTerm K arity))
    (J : Constraint String K arity P parity → Environment (String ⊕ String) String K arity P parity →
      Term → Scheme String K arity P parity → Prop) : Prop :=
  QuantifierIntroduction.SystemOStep X J (fun a => OverloadQualifier overload a (methods a))

/-- p.59's matrix, including its unindexed alpha in the last row. -/
def OverloadMatrix
    (overload : String → TypeTerm K arity → Constraint String K arity P parity)
    (methods : String → List (String × TypeTerm K arity))
    (unindexedAlpha : String) (names : List String) : Constraint String K arity P parity :=
  (names.zipIdx).foldr (fun row C =>
    OverloadQualifier overload
      (if row.2 + 1 = names.length then unindexedAlpha else row.1) (methods row.1) ∪ C) ∅

/-- The result-type dependencies and the premise's pi are defined from the
same overload matrix. The conclusion's pi_alpha remains a separate printed
symbol, as recorded in SYSTEM-O; it is not silently set to pi_alpha-bar. -/
def SystemOBatchSpecification
    (overload : String → TypeTerm K arity → Constraint String K arity P parity)
    (methods : String → List (String × TypeTerm K arity))
    (unindexedAlpha : String) (printedQualifier : Constraint String K arity P parity)
    (J : Constraint String K arity P parity → Environment (String ⊕ String) String K arity P parity →
      Term → Scheme String K arity P parity → Prop) : Prop :=
  QuantifierIntroduction.SystemOBatch X J
    (fun a => {b | ∃ method ∈ methods a, b ∈ method.2.fv})
    (OverloadMatrix overload methods unindexedAlpha) printedQualifier

/-- Link p.63's abstract rule to its two kind constructors and their FV. -/
def OhoriSpecification
    (hasKind : TypeTerm K arity → Kind K arity → Constraint String K arity P parity)
    (J : Constraint String K arity P parity → Environment (String ⊕ String) String K arity P parity →
      Term → Scheme String K arity P parity → Prop) : Prop :=
  QuantifierIntroduction.Ohori X J (Kind K arity) Kind.fv (fun a k => hasKind (.var a) k)

end
end HMX.SourceExample.Comparison
