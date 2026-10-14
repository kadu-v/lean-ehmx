import EHMX.TypeClasses.Classes
import Mathlib.Data.Finset.Card

namespace EHMX.TypeClasses

abbrev State {K} (E : ClassEnv K) := Finset (Fin E.count)

def transition {K} (E : ClassEnv K) (k : Fin K.count)
    (args : Fin (K.arity k) → State E) : State E :=
  Finset.univ.filter (fun c => (match E.rules c k with
    | none => false
    | some req => decide (∀ i, req i ⊆ args i) : Bool) = true)

theorem classes_con {K} (E : ClassEnv K) (k args) :
    (Ground.con k args).classes E = transition E k (fun i => (args i).classes E) := by
  ext c
  cases h : E.rules c k <;> simp [Ground.classes, transition, h]

def seed {K} (E : ClassEnv K) : Finset (State E) :=
  {∅} ∪ E.bases.image (fun p => (Ground.base p.2).classes E)

def step {K} (E : ClassEnv K) (states : Finset (State E)) : Finset (State E) :=
  states ∪ seed E ∪ Finset.univ.biUnion (fun k : Fin K.count =>
    (Finset.univ.filter (fun args : Fin (K.arity k) → State E => ∀ i, args i ∈ states)).image
      (transition E k))

theorem subset_step {K} (E : ClassEnv K) (s) : s ⊆ step E s := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

/-- Saturation terminates by the number of states not yet discovered.
The bound comes from the finite class set, not an arbitrary search fuel. -/
def close {K} (E : ClassEnv K) (s : Finset (State E)) : Finset (State E) :=
  if _h : step E s ⊆ s then s else close E (step E s)
termination_by Fintype.card (State E) - s.card
decreasing_by
  have lt : s.card < (step E s).card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨subset_step E s, fun eq => _h (eq ▸ Finset.Subset.refl _)⟩)
  have bound := Finset.card_le_univ (s := step E s)
  omega

theorem close_contains {K} (E : ClassEnv K) (s) : s ⊆ close E s := by
  fun_induction close E s with
  | case1 s h => exact Finset.Subset.refl _
  | case2 s h ih =>
    exact (subset_step E s).trans ih

theorem close_closed {K} (E : ClassEnv K) (s) : step E (close E s) ⊆ close E s := by
  fun_induction close E s with
  | case1 s h => exact h
  | case2 s h ih => exact ih

def Reachable {K} (E : ClassEnv K) (q : State E) : Prop := ∃ t : Ground K, t.classes E = q

theorem seed_sound {K} (E : ClassEnv K) : ∀ q ∈ seed E, Reachable E q := by
  intro q h
  obtain h | h := Finset.mem_union.mp h
  · have eq : q = ∅ := Finset.mem_singleton.mp h
    exact ⟨.arr (.base .int) ∅ (.base .int), eq.symm⟩
  · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp h
    exact ⟨.base p.2, rfl⟩

theorem step_sound {K} (E : ClassEnv K) (s)
    (hs : ∀ q ∈ s, Reachable E q) : ∀ q ∈ step E s, Reachable E q := by
  classical
  intro q h
  obtain h | h := Finset.mem_union.mp h
  · obtain h | h := Finset.mem_union.mp h
    · exact hs q h
    · exact seed_sound E q h
  · obtain ⟨k, _, h⟩ := Finset.mem_biUnion.mp h
    obtain ⟨args, ha, rfl⟩ := Finset.mem_image.mp h
    have witnesses : ∀ i, ∃ t : Ground K, t.classes E = args i :=
      fun i => hs _ ((Finset.mem_filter.mp ha).2 i)
    choose trees ht using witnesses
    refine ⟨.con k trees, ?_⟩
    simp only [classes_con]
    congr 1
    funext i
    exact ht i

theorem close_sound {K} (E : ClassEnv K) (s)
    (hs : ∀ q ∈ s, Reachable E q) : ∀ q ∈ close E s, Reachable E q := by
  fun_induction close E s with
  | case1 s h => exact hs
  | case2 s h ih =>
    exact ih (step_sound E s hs)

theorem classes_in_closed {K} (E : ClassEnv K) (s : Finset (State E))
    (closed : step E s ⊆ s) (t : Ground K) : t.classes E ∈ s := by
  have seeded : seed E ⊆ s := fun _ h => closed (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  induction t with
  | base b =>
    by_cases h : ∃ c, (c, b) ∈ E.bases
    · obtain ⟨c, hc⟩ := h
      exact seeded (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(c, b), hc, rfl⟩))
    · have eq : (Ground.base b).classes E = ∅ := by
        ext c
        simp only [Ground.classes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hc
        exact h ⟨c, hc⟩
      rw [eq]
      exact seeded (Finset.mem_union_left _ (Finset.mem_singleton_self _))
  | arr a e b ha hb =>
    exact seeded (Finset.mem_union_left _ (Finset.mem_singleton_self _))
  | con k args ih =>
    apply closed
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, Finset.mem_image.mpr ⟨fun i => (args i).classes E, ?_, (classes_con E k args).symm⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ih⟩

def reachable {K} (E : ClassEnv K) : Finset (State E) := close E ∅

theorem reachable_iff {K} (E : ClassEnv K) (q) : q ∈ reachable E ↔ Reachable E q := by
  constructor
  · exact close_sound E ∅ (by simp) q
  · rintro ⟨t, rfl⟩
    exact classes_in_closed E _ (close_closed E ∅) t

/-- Joint satisfiability of predicates on the same type, not separate witnesses. -/
def inhabited {K} (E : ClassEnv K) (required : State E) : Bool :=
  decide (∃ q ∈ reachable E, required ⊆ q)

theorem inhabited_iff {K} (E : ClassEnv K) (required) :
    inhabited E required = true ↔ ∃ t : Ground K, required ⊆ t.classes E := by
  simp only [inhabited, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨t, rfl⟩ := (reachable_iff E q).mp hq
    exact ⟨t, h⟩
  · rintro ⟨t, ht⟩
    exact ⟨t.classes E, (reachable_iff E _).mpr ⟨t, rfl⟩, ht⟩

end EHMX.TypeClasses
