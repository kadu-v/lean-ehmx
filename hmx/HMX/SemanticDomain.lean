import Mathlib.Order.Bounds.Basic
import Mathlib.Data.List.Forall2

/-! The abstract domain assumed on pp.11 and 34. No domain is constructed.
The sum is read as a sum with a common bottom, and leastness as existence of
continuous embedding/projection pairs into other solutions. These explicit
domain-theoretic readings are recorded in the source audit. -/
namespace HMX
universe d e

def DomainIdeal {D : Type d} [PartialOrder D] (I : Set D) : Prop :=
  I.Nonempty ∧ (∀ x ∈ I, ∀ y, y ≤ x → y ∈ I) ∧
  ∀ A : Set D, A.Nonempty → DirectedOn (· ≤ ·) A → A ⊆ I →
    ∀ x, IsLUB A x → x ∈ I

def DomainMapContinuous {D : Type d} {E : Type e} [PartialOrder D] [PartialOrder E]
    (f : D → E) : Prop :=
  Monotone f ∧ ∀ A : Set D, A.Nonempty → DirectedOn (· ≤ ·) A →
    ∀ x, IsLUB A x → IsLUB (f '' A) (f x)

abbrev DomainContinuous {D : Type d} [PartialOrder D] (f : D → D) : Prop :=
  DomainMapContinuous f

structure DomainData (Const : Type) (D : Type d) where
  wrong : D
  functionValue : (D → D) → D
  functionOf : D → Option (D → D)
  constructorValue : Const → List D → D

namespace DomainData
variable {Const : Type} {D : Type d} {E : Type e}
variable [PartialOrder D] [OrderBot D] [PartialOrder E] [OrderBot E]

/-- The alternatives and their order in the displayed recursive domain equation.
`constructors` lists the names and arities in its last summand. It is empty
for the equation printed on p.11. No assertion about denotations of types occurs. -/
def IsSolution (M : DomainData Const D) (constructors : Set (Const × Nat)) : Prop :=
  (∀ A : Set D, A.Nonempty → DirectedOn (· ≤ ·) A → ∃ x, IsLUB A x) ∧
  M.wrong ≠ ⊥ ∧
  (∀ v f, M.functionOf v = some f ↔ DomainContinuous f ∧ v = M.functionValue f) ∧
  (∀ f, DomainContinuous f → M.functionValue f ≠ M.wrong) ∧
  M.functionValue (fun _ => ⊥) = ⊥ ∧
  (∀ f g, DomainContinuous f → DomainContinuous g →
    (M.functionValue f ≤ M.functionValue g ↔ ∀ x, f x ≤ g x)) ∧
  (∀ c vs, (c, vs.length) ∈ constructors →
    M.constructorValue c vs ≠ ⊥ ∧ M.constructorValue c vs ≠ M.wrong ∧
    M.functionOf (M.constructorValue c vs) = none) ∧
  (∀ c vs k ws, (c, vs.length) ∈ constructors → (k, ws.length) ∈ constructors →
    (M.constructorValue c vs ≤ M.constructorValue k ws ↔ c = k ∧ List.Forall₂ (· ≤ ·) vs ws)) ∧
  (∀ v, v = ⊥ ∨ v = M.wrong ∨
    (∃ f, DomainContinuous f ∧ v = M.functionValue f) ∨
    ∃ c vs, (c, vs.length) ∈ constructors ∧ v = M.constructorValue c vs) ∧
  (∀ v, v ≤ M.wrong ↔ v = ⊥ ∨ v = M.wrong) ∧
  (∀ v, M.wrong ≤ v ↔ v = M.wrong) ∧
  (∀ c vs f, (c, vs.length) ∈ constructors → DomainContinuous f →
    ¬ M.constructorValue c vs ≤ M.functionValue f) ∧
  (∀ c vs f, (c, vs.length) ∈ constructors → DomainContinuous f →
    (M.functionValue f ≤ M.constructorValue c vs ↔ M.functionValue f = ⊥))

/-- The standard embedding/projection reading of the order on solutions.
The maps preserve the summands of the same recursive equation. -/
def Embeds (M : DomainData Const D) (M' : DomainData Const E)
    (constructors : Set (Const × Nat)) : Prop :=
  ∃ (embed : D → E) (project : E → D),
    DomainMapContinuous embed ∧ DomainMapContinuous project ∧
    (∀ x, project (embed x) = x) ∧ (∀ y, embed (project y) ≤ y) ∧
    embed ⊥ = ⊥ ∧ project ⊥ = ⊥ ∧ embed M.wrong = M'.wrong ∧
    (∀ f, DomainContinuous f →
      embed (M.functionValue f) = M'.functionValue (fun y => embed (f (project y)))) ∧
    (∀ c vs, (c, vs.length) ∈ constructors →
      embed (M.constructorValue c vs) = M'.constructorValue c (vs.map embed))

/-- An abstract least solution, not a construction or an existence claim.
The comparison ranges over all carriers in the same universe. -/
def LeastSolution (M : DomainData Const D) (constructors : Set (Const × Nat)) : Prop :=
  M.IsSolution constructors ∧
    ∀ (E : Type d) (ord : PartialOrder E) (bot : OrderBot E) (M' : DomainData Const E),
      @IsSolution Const E ord bot M' constructors →
      @Embeds Const D E _ _ ord bot M M' constructors
end DomainData
end HMX
