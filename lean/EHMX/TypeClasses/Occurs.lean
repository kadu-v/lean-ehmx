import EHMX.TypeClasses.Types
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace EHMX.TypeClasses

def Ground.nodes {K} : Ground K → Nat
  | .base _ => 1
  | .arr a _ b => 1 + a.nodes + b.nodes
  | .con _ args => 1 + ∑ i, (args i).nodes

theorem Ty.nodes_le {K} (t : Ty K) (i : Nat) (v) (h : i ∈ t.types) :
    (v.types i).nodes ≤ (t.eval v).nodes := by
  induction t with
  | var j => simp only [Ty.types, Finset.mem_singleton] at h; subst j; rfl
  | base b => simp [Ty.types] at h
  | arr a e b ha hb =>
    simp only [Ty.types, Finset.mem_union] at h
    simp only [Ty.eval, Ground.nodes]
    rcases h with h | h
    · have := ha h; omega
    · have := hb h; omega
  | con k args ih =>
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp h
    have bound := Finset.single_le_sum (fun (x : Fin (K.arity k)) _ => Nat.zero_le ((args x).eval v).nodes)
      (Finset.mem_univ j)
    have := ih j hj
    simp only [Ty.eval, Ground.nodes]
    omega

theorem Ty.nodes_lt {K} (t : Ty K) (i : Nat) (v) (h : i ∈ t.types) (ne : t ≠ .var i) :
    (v.types i).nodes < (t.eval v).nodes := by
  cases t with
  | var j => simp only [Ty.types, Finset.mem_singleton] at h; exact False.elim (ne (h ▸ rfl))
  | base b => simp [Ty.types] at h
  | arr a e b =>
    simp only [Ty.types, Finset.mem_union] at h
    simp only [Ty.eval, Ground.nodes]
    rcases h with h | h
    · have := a.nodes_le i v h; omega
    · have := b.nodes_le i v h; omega
  | con k args =>
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp h
    have bound := Finset.single_le_sum (fun (x : Fin (K.arity k)) _ => Nat.zero_le ((args x).eval v).nodes)
      (Finset.mem_univ j)
    have := (args j).nodes_le i v hj
    simp only [Ty.eval, Ground.nodes]
    omega

theorem Ty.occurs_impossible {K} (t : Ty K) (i : Nat) (h : i ∈ t.types) (ne : t ≠ .var i) (v) :
    v.types i ≠ t.eval v := by
  intro eq
  have := t.nodes_lt i v h ne
  rw [eq] at this
  exact Nat.lt_irrefl _ this

end EHMX.TypeClasses
