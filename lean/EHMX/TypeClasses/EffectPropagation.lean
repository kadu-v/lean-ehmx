import EHMX.TypeClasses.EffectSolver

namespace EHMX.TypeClasses

abbrev EffectState := Finset (Nat × Op)
def EffectState.valuation (q : EffectState) (i : Nat) : Finset Op :=
  (q.filter (fun p => p.1 = i)).image Prod.snd

@[simp] theorem EffectState.mem_valuation (q : EffectState) (i op) :
    op ∈ q.valuation i ↔ (i, op) ∈ q := by
  simp [valuation]

theorem Effect.eval_mono (e : Effect) {v w : Nat → Finset Op}
    (h : ∀ i, v i ⊆ w i) : e.eval v ⊆ e.eval w := by
  intro op ho
  simp only [Effect.eval, Finset.mem_union, Finset.mem_biUnion] at *
  rcases ho with ho | ⟨i, hi, ho⟩
  · exact Or.inl ho
  · exact Or.inr ⟨i, hi, h i ho⟩

def EffectAtom.allows (q : EffectState) (i : Nat) (op : Op) : EffectAtom → Prop
  | .le a b => i ∈ a.vars → op ∈ b.eval q.valuation
  | .lacks o a => i ∈ a.vars → op ≠ o
instance (q i op a) : Decidable (EffectAtom.allows q i op a) := by
  cases a <;> unfold EffectAtom.allows <;> infer_instance

def prune (cs : List EffectAtom) (q : EffectState) : EffectState :=
  q.filter (fun p => ∀ a ∈ cs, a.allows q p.1 p.2)

theorem prune_subset (cs q) : prune cs q ⊆ q := Finset.filter_subset _ _

def propagate (cs : List EffectAtom) (q : EffectState) : EffectState :=
  if prune cs q = q then q else propagate cs (prune cs q)
termination_by q.card
decreasing_by
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨prune_subset _ _, by assumption⟩

theorem propagate_fixed (cs q) : prune cs (propagate cs q) = propagate cs q := by
  fun_induction propagate cs q with
  | case1 q h => exact h
  | case2 q h ih => exact ih

theorem prune_upper (cs q) (v : Nat → Finset Op)
    (hv : ∀ a ∈ cs, a.Holds v) (upper : ∀ i, v i ⊆ q.valuation i) :
    ∀ i, v i ⊆ (prune cs q).valuation i := by
  intro i op ho
  rw [EffectState.mem_valuation, prune, Finset.mem_filter]
  refine ⟨(EffectState.mem_valuation q i op).mp (upper i ho), ?_⟩
  intro a ha
  cases a with
  | le a b =>
    intro hi
    apply Effect.eval_mono b upper
    apply hv (.le a b) ha
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, ho⟩)
  | lacks o a =>
    intro hi eq
    change op = o at eq
    subst op
    exact hv (.lacks o a) ha (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, ho⟩))

theorem propagate_upper (cs q) (v : Nat → Finset Op)
    (hv : ∀ a ∈ cs, a.Holds v) (upper : ∀ i, v i ⊆ q.valuation i) :
    ∀ i, v i ⊆ (propagate cs q).valuation i := by
  fun_induction propagate cs q with
  | case1 => exact upper
  | case2 q h ih => exact ih (prune_upper cs q v hv upper)

def initialEffects (cs : List EffectAtom) : EffectState :=
  (effectVars cs) ×ˢ (effectLabels cs)

theorem bounded_model (cs : List EffectAtom) (v : Nat → Finset Op)
    (hv : ∀ a ∈ cs, a.Holds v) :
    ∃ w, (∀ a ∈ cs, a.Holds w) ∧ ∀ i, w i ⊆ (initialEffects cs).valuation i := by
  let w := fun i => if i ∈ effectVars cs then v i ∩ effectLabels cs else ∅
  refine ⟨w, ?_, ?_⟩
  · intro a ha
    have trim := a.holds_trim (effectLabels cs) v
      (fun _ hx => Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr ha, hx⟩) (hv a ha)
    apply (a.holds_support _ w ?_).mp trim
    intro i hi
    have mem : i ∈ effectVars cs := Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr ha, hi⟩
    simp [w, mem]
  · intro i op ho
    simp only [w] at ho
    split at ho
    · simp_all [initialEffects]
    · simp at ho

theorem fixed_satisfies (cs q) (fixed : prune cs q = q) (v : Nat → Finset Op)
    (hv : ∀ a ∈ cs, a.Holds v) (upper : ∀ i, v i ⊆ q.valuation i) :
    ∀ a ∈ cs, a.Holds q.valuation := by
  intro a ha
  have allows i op (hp : (i, op) ∈ q) : a.allows q i op := by
    rw [← fixed] at hp
    exact (Finset.mem_filter.mp hp).2 a ha
  cases a with
  | le a b =>
    intro op ho
    rcases Finset.mem_union.mp ho with hl | hr
    · apply Effect.eval_mono b upper
      exact hv (.le a b) ha (Finset.mem_union_left _ hl)
    · obtain ⟨i, hi, ho⟩ := Finset.mem_biUnion.mp hr
      exact allows i op ((EffectState.mem_valuation q i op).mp ho) hi
  | lacks o a =>
    intro ho
    rcases Finset.mem_union.mp ho with hl | hr
    · exact hv (.lacks o a) ha (Finset.mem_union_left _ hl)
    · obtain ⟨i, hi, ho⟩ := Finset.mem_biUnion.mp hr
      exact allows i o ((EffectState.mem_valuation q i o).mp ho) hi rfl

def propagationSat (cs : List EffectAtom) : Bool :=
  decide (∀ a ∈ cs, a.Holds (propagate cs (initialEffects cs)).valuation)

theorem propagationSat_iff (cs) :
    propagationSat cs = true ↔ ∃ v, ∀ a ∈ cs, EffectAtom.Holds v a := by
  simp only [propagationSat, decide_eq_true_eq]
  constructor
  · intro h; exact ⟨_, h⟩
  · rintro ⟨v, hv⟩
    obtain ⟨w, hw, upper⟩ := bounded_model cs v hv
    exact fixed_satisfies cs _ (propagate_fixed cs _) w hw (propagate_upper cs _ w hw upper)

theorem propagation_eq_enumeration (cs) : propagationSat cs = effectSat cs := by
  apply Bool.eq_iff_iff.mpr
  exact (propagationSat_iff cs).trans (effectSat_iff cs).symm

end EHMX.TypeClasses
