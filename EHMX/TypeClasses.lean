import HMX.TypeClasses
import EHMX.Semantics

/-! HMX と宣言を共有する EHM(X) の固定型クラスモデル。
所属は宣言の最小閉包であり、探索器や辞書変換は仮定しない。 -/
namespace EHMX.TypeClasses

abbrev ClassEnv := HMX.TypeClasses.ClassEnv
abbrev InstanceRule := HMX.TypeClasses.InstanceRule
abbrev arity := HMX.TypeClasses.arity

inductive GroundType (extras : List Nat) where
  | int
  | bool
  | arrow : GroundType extras → Finset Op → GroundType extras → GroundType extras
  | list : GroundType extras → GroundType extras
  | extra (i : Fin extras.length) (args : Fin (extras.get i) → GroundType extras)

/-- Only arrows vary: all other type trees are compared by equality. -/
inductive GroundType.Below : GroundType extras → GroundType extras → Prop where
  | int : Below .int .int
  | bool : Below .bool .bool
  | list (a) : Below (.list a) (.list a)
  | extra (i) (args) : Below (.extra i args) (.extra i args)
  | arrow : Below a' a → ε ⊆ ε' → Below b b' →
      Below (.arrow a ε b) (.arrow a' ε' b')

def GroundType.tag : GroundType extras → Nat
  | .int => 1
  | .bool => 2
  | .arrow _ _ _ => 0
  | .list _ => 3
  | .extra i _ => i.val + 4

def GroundType.arguments : GroundType extras → List (GroundType extras)
  | .int | .bool => []
  | .arrow a _ b => [a,b]
  | .list a => [a]
  | .extra _ args => List.ofFn args

/-- The effect parameter is used only at an arrow head. Invalid applications return Int. -/
def construct (extras : List Nat) (ε : Finset Op) : Nat → List (GroundType extras) → GroundType extras
  | 0, [a,b] => .arrow a ε b
  | 1, [] => .int
  | 2, [] => .bool
  | 3, [a] => .list a
  | n + 4, vs =>
      if h : n < extras.length then
        if hl : vs.length = extras.get ⟨n,h⟩ then .extra ⟨n,h⟩ (fun i => vs.get (Fin.cast hl.symm i)) else .int
      else .int
  | _, _ => .int

/-- Rules inspect input/result arguments at arrow heads, never their latent effect. -/
inductive Member (E : ClassEnv) : Nat → GroundType E.extraArities → Prop where
  | instanceRule (r : InstanceRule) (vs : List (GroundType E.extraArities)) (ε : Finset Op) :
      r ∈ E.instances → vs.length = arity E.extraArities r.constructor →
      (∀ p ∈ r.premises, Member E p.1 ((vs[p.2]?).getD .int)) →
      Member E r.className (construct E.extraArities ε r.constructor vs)
  | superclass (c d : Nat) (v : GroundType E.extraArities) :
      (c,d) ∈ E.supers → Member E c v → Member E d v

inductive Ground (extras : List Nat) where
  | type : GroundType extras → Ground extras
  | effect : Finset Op → Ground extras

def kind : Ground extras → Kind
  | .type _ => 0
  | .effect _ => 1

def Ground.asType : Ground extras → GroundType extras
  | .type t => t
  | .effect _ => .int

def constructor (extras : List Nat) : Symbol → List (Ground extras) → Ground extras
  | .arrow, [.type a, .effect ε, .type b] => .type (.arrow a ε b)
  | .empty, [] => .effect ∅
  | .operation op, [] => .effect {op}
  | .union, [.effect ε, .effect η] => .effect (ε ∪ η)
  | .other 0, _ => .type .int
  | .other (n+1), vs => .type (if vs.all (fun v => kind v == 0) then
      construct extras ∅ (n+1) (vs.map Ground.asType) else .int)
  | _, _ => .type .int

def below : Kind → Ground extras → Ground extras → Prop
  | 0, .type a, .type b => a.Below b
  | 1, .effect ε, .effect η => ε ⊆ η
  | _, _, _ => False

def effects : Ground extras → Set Op
  | .effect ε => ↑ε
  | .type _ => ∅

def signature (E : ClassEnv) : Signature where
  kinds := {0,1}
  constructors := {f | 0 < f ∧ f < 4 + E.extraArities.length}
  parameters := fun f => List.replicate (arity E.extraArities f) 0
  result := fun _ => 0
  predicates := ↑E.classes
  predicateKinds := fun _ => [0]

abbrev model (E : ClassEnv) : Model where
  Carrier := Ground E.extraArities
  default := .type .int
  kind := kind
  constructor := constructor E.extraArities
  predicate := fun c vs => ∃ v, vs = [.type v] ∧ Member E c v
  below := below
  effects := effects

def classAtom (c : Nat) (T : Ty) : Constraint := .atom (.other c) [T]

def instanceContext (r : InstanceRule) (ts : List Ty) : Constraint :=
  (r.premises.map (fun p => classAtom p.1 ((ts[p.2]?).getD (.con (.other 1) [])))).foldr
    Constraint.conj .truth

/-- Arrow code 0 is translated to the dedicated effectful constructor. -/
def instanceHead (r : InstanceRule) (ts : List Ty) (ε : Effect) : Ty :=
  if r.constructor = 0 then .arrow ((ts[0]?).getD (.con (.other 1) [])) ε
    ((ts[1]?).getD (.con (.other 1) [])) else .con (.other r.constructor) ts

/-- Embed HMX trees, putting an empty latent effect at every arrow. -/
def embed : HMX.TypeClasses.Ground extras → GroundType extras
  | .int => .int
  | .bool => .bool
  | .arrow a b => .arrow (embed a) ∅ (embed b)
  | .list a => .list (embed a)
  | .extra i args => .extra i (fun j => embed (args j))

/-- Used only for the comparison theorem; Member itself retains full effectful trees. -/
def erase : GroundType extras → HMX.TypeClasses.Ground extras
  | .int => .int
  | .bool => .bool
  | .arrow a _ b => .arrow (erase a) (erase b)
  | .list a => .list (erase a)
  | .extra i args => .extra i (fun j => erase (args j))

end EHMX.TypeClasses
