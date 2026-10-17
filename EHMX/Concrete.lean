import EHMX.Proofs.Kind
import Mathlib.Data.Set.Finite.Basic

/-! 抽象モデルの非空な具体例。基底型と効果付き関数型、有限集合効果。
モデルの妥当性と EHMX の型安全性は別の命題である。 -/
namespace EHMX.Concrete

inductive GroundType where
  | base : Nat → GroundType
  | arrow : GroundType → Finset Op → GroundType → GroundType
  deriving DecidableEq

inductive GroundType.Below : GroundType → GroundType → Prop where
  | base (n) : Below (.base n) (.base n)
  | arrow : Below a' a → ε ⊆ ε' → Below b b' →
      Below (.arrow a ε b) (.arrow a' ε' b')

theorem groundRefl (T : GroundType) : T.Below T := by
  induction T with
  | base n => exact .base n
  | arrow a ε b ihA ihB => exact .arrow ihA (fun _ h => h) ihB

theorem groundTrans (h : GroundType.Below a b) (h' : GroundType.Below b c) :
    GroundType.Below a c := by
  induction b generalizing a c with
  | base n => cases h; cases h'; exact .base n
  | arrow a ε b ihA ihB =>
      cases h with
      | arrow ha hε hb =>
          cases h' with
          | arrow ha' hε' hb' =>
              exact .arrow (ihA ha' ha) (fun _ h => hε' (hε h)) (ihB hb hb')

theorem groundAntisymm (h : GroundType.Below a b) (h' : GroundType.Below b a) : a = b := by
  induction b generalizing a with
  | base n => cases h; rfl
  | arrow a ε b ihA ihB =>
      cases h with
      | arrow ha hε hb =>
          cases h' with
          | arrow ha' hε' hb' =>
              have hA := ihA ha' ha
              have hB := ihB hb hb'
              have hE := Finset.Subset.antisymm hε hε'
              subst_vars
              rfl

inductive Ground where
  | type : GroundType → Ground
  | effect : Finset Op → Ground
  deriving DecidableEq

def kind : Ground → Kind
  | .type _ => 0
  | .effect _ => 1

def constructor : Symbol → List Ground → Ground
  | .arrow, [.type a, .effect ε, .type b] => .type (.arrow a ε b)
  | .empty, _ => .effect ∅
  | .operation op, _ => .effect {op}
  | .union, [.effect ε, .effect η] => .effect (ε ∪ η)
  | .other n, _ => .type (.base n)
  | _, _ => .type (.base 0)

def below : Kind → Ground → Ground → Prop
  | 0, .type a, .type b => a.Below b
  | 1, .effect ε, .effect η => ε ⊆ η
  | _, _, _ => False

def effects : Ground → Set Op
  | .effect ε => ↑ε
  | .type _ => ∅

def signature : Signature where
  kinds := {0,1}
  constructors := Set.univ
  parameters := fun _ => []
  result := fun _ => 0
  predicates := ∅
  predicateKinds := fun _ => []

def model : Model where
  Carrier := Ground
  default := .type (.base 0)
  kind := kind
  constructor := constructor
  predicate := fun _ _ => False
  below := below
  effects := effects

private theorem kindZero (h : kind a = 0) : ∃ T, a = .type T := by
  cases a with
  | type T => exact ⟨T, rfl⟩
  | effect ε => simp [kind] at h

private theorem kindOne (h : kind a = 1) : ∃ ε, a = .effect ε := by
  cases a with
  | type T => simp [kind] at h
  | effect ε => exact ⟨ε, rfl⟩

private theorem constructorKind (f : Symbol)
    (h : KindValues model (f.parameters signature) vs) :
    kind (constructor f vs) = f.result signature := by
  cases f with
  | empty => rfl
  | operation op => rfl
  | other n => rfl
  | arrow =>
      cases h with
      | cons ha h =>
          cases h with
          | cons hε h =>
              cases h with
              | cons hb h =>
                  cases h
                  obtain ⟨a, rfl⟩ := kindZero ha
                  obtain ⟨ε, rfl⟩ := kindOne hε
                  obtain ⟨b, rfl⟩ := kindZero hb
                  rfl
  | union =>
      cases h with
      | cons hε h =>
          cases h with
          | cons hη h =>
              cases h
              obtain ⟨ε, rfl⟩ := kindOne hε
              obtain ⟨η, rfl⟩ := kindOne hη
              rfl

theorem framework : EffectFramework signature model where
  signature := by simp [Signature.WF, signature]
  inhabited := by
    intro k hk
    rcases (show k = 0 ∨ k = 1 from hk) with rfl | rfl
    · exact ⟨.type (.base 0), rfl⟩
    · exact ⟨.effect ∅, rfl⟩
  constructorKind := fun f _ _ h => constructorKind f h
  belowRefl := by
    intro k _ a ha
    cases a with
    | type T => cases ha; exact groundRefl T
    | effect ε => cases ha; exact fun _ h => h
  belowTrans := by
    intro k _ a b c ha hb hc hab hbc
    cases a with
    | type T =>
        cases ha
        obtain ⟨U, rfl⟩ := kindZero hb
        obtain ⟨V, rfl⟩ := kindZero hc
        exact groundTrans hab hbc
    | effect ε =>
        cases ha
        obtain ⟨η, rfl⟩ := kindOne hb
        obtain ⟨ζ, rfl⟩ := kindOne hc
        exact fun _ h => hbc (hab h)
  belowAntisymm := by
    intro k _ a b ha hb hab hba
    cases a with
    | type T =>
        cases ha
        obtain ⟨U, rfl⟩ := kindZero hb
        exact congrArg Ground.type (groundAntisymm hab hba)
    | effect ε =>
        cases ha
        obtain ⟨η, rfl⟩ := kindOne hb
        exact congrArg Ground.effect (Finset.Subset.antisymm hab hba)
  effectOrder := by
    intro a b ha hb
    obtain ⟨ε, rfl⟩ := kindOne ha
    obtain ⟨η, rfl⟩ := kindOne hb
    rfl
  emptyEffect := by ext; simp [model, constructor, effects]
  effectsFinite := by
    intro a ha
    obtain ⟨ε, rfl⟩ := kindOne ha
    exact ε.finite_toSet
  singletonEffect := fun _ => by ext; simp [model, constructor, effects]
  unionEffect := by
    intro a b ha hb
    obtain ⟨ε, rfl⟩ := kindOne ha
    obtain ⟨η, rfl⟩ := kindOne hb
    ext; simp [model, constructor, effects]
  arrowOrder := by
    intro a ε b a' ε' b' ha hε hb ha' hε' hb'
    obtain ⟨A, rfl⟩ := kindZero ha
    obtain ⟨E, rfl⟩ := kindOne hε
    obtain ⟨B, rfl⟩ := kindZero hb
    obtain ⟨A', rfl⟩ := kindZero ha'
    obtain ⟨E', rfl⟩ := kindOne hε'
    obtain ⟨B', rfl⟩ := kindZero hb'
    constructor
    · intro h; cases h with | arrow ha he hb => exact ⟨ha,he,hb⟩
    · rintro ⟨ha,he,hb⟩; exact .arrow ha he hb

theorem arrowSeparated : ArrowSeparated signature model := by
  intro f _ _ vs a ε b _ ha hε hb h
  obtain ⟨A, rfl⟩ := kindZero ha
  obtain ⟨E, rfl⟩ := kindOne hε
  obtain ⟨B, rfl⟩ := kindZero hb
  cases h

end EHMX.Concrete
