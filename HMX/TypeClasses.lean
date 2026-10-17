import HMX.LocallyNameless.Correspondence
import Mathlib.Data.List.OfFn

/-! A new fixed-model instance of ATTAPL, inspired by Sulzmann §3.2 and §3.5.2.
This is not a transcription of a numbered theorem, nor an open-world semantics.
Constructor codes: arrow = 0, Int = 1, Bool = 2, list = 3, extras = 4 + index.
Class names and method identifiers live in separate namespaces. -/
namespace HMX.TypeClasses

structure InstanceRule where
  className : Nat
  constructor : Nat
  premises : List (Nat × Nat)
  deriving DecidableEq

structure ClassEnv where
  extraArities : List Nat
  classes : Finset Nat
  supers : List (Nat × Nat)
  instances : List InstanceRule

def arity (extras : List Nat) : Nat → Nat
  | 0 => 2
  | 1 | 2 => 0
  | 3 => 1
  | n + 4 => (extras[n]?).getD 0

def InstanceRule.WF (E : ClassEnv) (r : InstanceRule) : Prop :=
  r.className ∈ E.classes ∧ r.constructor < 4 + E.extraArities.length ∧
  ∀ p ∈ r.premises, p.1 ∈ E.classes ∧ p.2 < arity E.extraArities r.constructor

def ClassEnv.WF (E : ClassEnv) : Prop :=
  (∀ p ∈ E.supers, p.1 ∈ E.classes ∧ p.2 ∈ E.classes) ∧
  ∀ r ∈ E.instances, r.WF E

/-- Every inhabitant is a finite, closed, arity-correct type tree. -/
inductive Ground (extras : List Nat) where
  | int
  | bool
  | arrow : Ground extras → Ground extras → Ground extras
  | list : Ground extras → Ground extras
  | extra (i : Fin extras.length) (args : Fin (extras.get i) → Ground extras)

def Ground.tag : Ground extras → Nat
  | .int => 1
  | .bool => 2
  | .arrow _ _ => 0
  | .list _ => 3
  | .extra i _ => i.val + 4

def Ground.arguments : Ground extras → List (Ground extras)
  | .int | .bool => []
  | .arrow a b => [a,b]
  | .list a => [a]
  | .extra _ args => List.ofFn args

/-- The fallback only totalizes interpretation on undeclared or wrong-arity inputs. -/
def construct (extras : List Nat) : Nat → List (Ground extras) → Ground extras
  | 0, [a,b] => .arrow a b
  | 1, [] => .int
  | 2, [] => .bool
  | 3, [a] => .list a
  | n + 4, vs =>
      if h : n < extras.length then
        if hl : vs.length = extras.get ⟨n,h⟩ then .extra ⟨n,h⟩ (fun i => vs.get (Fin.cast hl.symm i)) else .int
      else .int
  | _, _ => .int

/-- Least closure of the declared instance and superclass rules. No inhabitedness field. -/
inductive Member (E : ClassEnv) : Nat → Ground E.extraArities → Prop where
  | instanceRule (r : InstanceRule) (vs : List (Ground E.extraArities)) :
      r ∈ E.instances → vs.length = arity E.extraArities r.constructor →
      (∀ p ∈ r.premises, Member E p.1 ((vs[p.2]?).getD .int)) →
      Member E r.className (construct E.extraArities r.constructor vs)
  | superclass (c d : Nat) (v : Ground E.extraArities) :
      (c,d) ∈ E.supers → Member E c v → Member E d v

def signature (E : ClassEnv) : Signature where
  kinds := {0}
  directions := Set.univ
  constructors := {f | f < 4 + E.extraArities.length}
  parameters := fun f => (List.range (arity E.extraArities f)).map (fun i => (i,0))
  result := fun _ => 0
  predicates := ↑E.classes
  predicateKinds := fun _ => [0]

abbrev model (E : ClassEnv) : Model where
  Carrier := Ground E.extraArities
  kind := fun _ => 0
  constructor := construct E.extraArities
  predicate := fun c vs => ∃ v, vs = [v] ∧ Member E c v
  below := fun _ a b => a = b

def classAtom (c : Nat) (T : Ty) : Constraint := .atom (.other c) [T]

def instanceContext (r : InstanceRule) (ts : List Ty) : Constraint :=
  (r.premises.map (fun p => classAtom p.1 ((ts[p.2]?).getD (.con 1 [])))).foldr
    Constraint.conj .truth

/-- Methods use ordinary qualified schemes; no dictionary or method law is added. -/
def methodScheme (c : Nat) (X : TVar) (T : Ty) : Scheme :=
  .all {X} (classAtom c (.var X)) T

def fixedModelRequirements (E : ClassEnv) : Prop := (model E).Requirements (signature E)
def fixedArrowLaw (E : ClassEnv) : Prop := ArrowLaw (signature E) (model E)
def fixedIsolation (E : ClassEnv) : Prop :=
  Isolation (signature E) (model E) (signature E).constructors

def fixedFramework (E : ClassEnv) : Prop :=
  Framework (signature E) (model E) (signature E).constructors

def classAtomMeaning (E : ClassEnv) : Prop :=
  ∀ c T ρ ι, (classAtom c T).Holds (signature E) (model E) ρ ι ↔
    Member E c (T.eval (model E) ρ)

def superclassEntailment (E : ClassEnv) : Prop :=
  ∀ c d, (c,d) ∈ E.supers → ∀ T,
    Entails (signature E) (model E) (classAtom c T) (classAtom d T)

def instanceEntailment (E : ClassEnv) : Prop :=
  E.WF → ∀ r, r ∈ E.instances → ∀ ts, ts.length = arity E.extraArities r.constructor →
    Entails (signature E) (model E) (instanceContext r ts) (classAtom r.className (.con r.constructor ts))

/-- Specializations discharge Framework internally and keep the named scope conditions. -/
def namedSoundness (E : ClassEnv) : Prop :=
  ∀ Γ t T, Γ.WF (signature E) → Γ.fpi = ∅ → t.fpi ⊆ Γ.dpi →
    T.HasKind (signature E) 0 →
    Typing (signature E) (model E) (infer Γ t T) Γ t (.mono T)

def namedCompleteness (E : ClassEnv) : Prop :=
  ∀ C Γ t T, Entails (signature E) (model E) C Γ.exists_ → C.fpi ∪ Γ.fpi = ∅ →
    Typing (signature E) (model E) C Γ t (.mono T) →
    Entails (signature E) (model E) C (infer Γ t T)

def namedPrincipality (E : ClassEnv) : Prop :=
  ∀ Γ t T, Γ.WF (signature E) → Γ.fpi = ∅ → t.fpi ⊆ Γ.dpi →
    T.HasKind (signature E) 0 →
    PrincipalConstraint (signature E) (model E) Γ t T (infer Γ t T)

end HMX.TypeClasses
