import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Fold

namespace EHMX

abbrev Op := Nat

/-- ε ::= ∅ | {op} | μ | ε ∪ ε の集合正規形。 -/
structure Effect where
  labels : Finset Op
  vars : Finset Nat
  deriving DecidableEq

namespace Effect

/-- ∅ は操作も変数も含まない。 -/
def empty : Effect := ⟨∅, ∅⟩

/-- {op} は操作を一つだけ含む。 -/
def singleton (op : Op) : Effect := ⟨{op}, ∅⟩

/-- μ は効果変数を一つだけ含む。 -/
def var (μ : Nat) : Effect := ⟨∅, {μ}⟩

/-- 効果和は両成分の集合和である。 -/
def union (ε η : Effect) : Effect :=
  ⟨ε.labels ∪ η.labels, ε.vars ∪ η.vars⟩

instance : EmptyCollection Effect := ⟨empty⟩
instance : Union Effect := ⟨union⟩

@[simp] theorem labels_empty : (∅ : Effect).labels = ∅ := rfl
@[simp] theorem vars_empty : (∅ : Effect).vars = ∅ := rfl
@[simp] theorem labels_singleton (op : Op) :
    (singleton op).labels = {op} := rfl
@[simp] theorem vars_singleton (op : Op) :
    (singleton op).vars = ∅ := rfl
@[simp] theorem labels_union (ε η : Effect) :
    (ε ∪ η).labels = ε.labels ∪ η.labels := rfl
@[simp] theorem vars_union (ε η : Effect) :
    (ε ∪ η).vars = ε.vars ∪ η.vars := rfl

/-- Iρ(ε) は各効果変数を有限操作集合として解釈した結果。 -/
def eval (ρ : Nat → Finset Op) (ε : Effect) : Finset Op :=
  ε.labels ∪ ε.vars.biUnion ρ

theorem eval_support (ε : Effect) (v w : Nat → Finset Op)
    (h : ∀ i ∈ ε.vars, v i = w i) : ε.eval v = ε.eval w := by
  unfold Effect.eval
  congr 1
  exact Finset.biUnion_congr rfl h

/-- ε ⊑ η は各成分の集合包含である。 -/
def Subset (ε η : Effect) : Prop :=
  ε.labels ⊆ η.labels ∧ ε.vars ⊆ η.vars

instance : HasSubset Effect := ⟨Subset⟩

/-- 効果の空集合は和集合の左単位元である。 -/
theorem empty_union (ε : Effect) : empty ∪ ε = ε := by
  cases ε with
  | mk labels vars =>
      change Effect.mk (∅ ∪ labels) (∅ ∪ vars) = _
      simp

/-- 型・効果変数の同時改名のうち効果側。 -/
def rename (ρ : Nat → Nat) (ε : Effect) : Effect :=
  ⟨ε.labels, ε.vars.image ρ⟩

end Effect

def Effect.subst (θ : Nat → Effect) (ε : Effect) : Effect :=
  ⟨ε.labels ∪ ε.vars.biUnion (fun i => (θ i).labels),
    ε.vars.biUnion (fun i => (θ i).vars)⟩

theorem Effect.subst_eq_self (ε : Effect) (θ : Nat → Effect)
    (h : ∀ i ∈ ε.vars, θ i = Effect.var i) : ε.subst θ = ε := by
  have labels : ε.vars.biUnion (fun i => (θ i).labels) = ∅ := by
    ext j
    simp only [Finset.mem_biUnion, Finset.notMem_empty, iff_false]
    rintro ⟨i, hi, hj⟩
    simp [h i hi, Effect.var] at hj
  have vars : ε.vars.biUnion (fun i => (θ i).vars) = ε.vars := by
    calc
      _ = ε.vars.biUnion (fun i => (Effect.var i).vars) :=
        Finset.biUnion_congr rfl (fun i hi => congrArg Effect.vars (h i hi))
      _ = ε.vars := by simp [Effect.var]
  cases ε
  simp_all [Effect.subst]

theorem Effect.eval_subst (ε : Effect) (θ : Nat → Effect)
    (ρ : Nat → Finset Op) :
    (ε.subst θ).eval ρ = ε.eval (fun i => (θ i).eval ρ) := by
  ext op
  simp [Effect.subst, Effect.eval, Finset.mem_biUnion,
    Finset.mem_union]
  aesop

end EHMX
