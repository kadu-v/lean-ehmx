import EHMX.HMX.GroundTyping

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

/-- A finite upper bound on the variables introduced by assigned images. -/
def Substitution.range (σ : Substitution T) : Names :=
  ⟨σ.domain.types.biUnion (fun i => (T.support (σ.types i)).types),
   (σ.domain.types.biUnion (fun i => (T.support (σ.types i)).effects)) ∪
     σ.domain.effects.biUnion (fun i => (σ.effects i).vars)⟩

theorem Substitution.type_support_subset (σ : Substitution T) (u : Names)
    {i : Nat} (hi : i ∈ u.types) : (T.support (σ.types i)).Subset (u.union σ.range) := by
  by_cases hd : i ∈ σ.domain.types
  · constructor
    · intro j hj
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hd, hj⟩)
    · intro j hj
      exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_biUnion.mpr ⟨i, hd, hj⟩))
  · simp only [σ.types_outside i hd, T.support_var]
    exact ⟨by simpa [Names.union] using Finset.mem_union_left σ.range.types hi, by simp⟩

theorem Substitution.effect_support_subset (σ : Substitution T) (u : Names)
    {i : Nat} (hi : i ∈ u.effects) : (σ.effects i).vars ⊆ (u.union σ.range).effects := by
  by_cases hd : i ∈ σ.domain.effects
  · intro j hj
    exact Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨i, hd, hj⟩))
  · simpa [σ.effects_outside i hd, Effect.var, Names.union] using
      (show {i} ⊆ u.effects ∪ σ.range.effects from by simpa using Finset.mem_union_left _ hi)

/-- Bound variables are sent to new variables; the free variables receive σ.
The same simultaneous substitution is applied to qualifier and type. -/
def Substitution.underBinder (σ : Substitution T) (a : Names)
    (ft fe : Nat → Nat) : Substitution T where
  domain := a.union σ.domain
  types := fun i => if i ∈ a.types then T.var (ft i) else σ.types i
  effects := fun i => if i ∈ a.effects then Effect.var (fe i) else σ.effects i
  types_outside := by
    intro i hi
    obtain ⟨ha, hs⟩ := Finset.notMem_union.mp hi
    simp [ha, σ.types_outside i hs]
  effects_outside := by
    intro i hi
    obtain ⟨ha, hs⟩ := Finset.notMem_union.mp hi
    simp [ha, σ.effects_outside i hs]

def Scheme.substAvoid {X : Constraints T O} (σ : Substitution T)
    (a : Names) (c : X.Formula) (t : T.Term) : Names :=
  ((X.support c).union (T.support t)).union (σ.range.union (σ.domain.union a))

/-- Computable capture-avoiding substitution. Freshness uses a finite support
bound; no choice of a ground type or satisfiability decision occurs here. -/
def Scheme.subst {X : Constraints T O} (σ : Substitution T) : Scheme X → Scheme X
  | .mono t => .mono (σ.apply t)
  | .qualified a c t =>
    let avoid := Scheme.substAvoid σ a c t
    let η := σ.underBinder a avoid.shiftTypes avoid.shiftEffects
    .qualified ⟨a.types.image avoid.shiftTypes, a.effects.image avoid.shiftEffects⟩
      (X.subst η c) (η.apply t)

def Context.subst {X : Constraints T O} (σ : Substitution T) (g : Context X) : Context X :=
  g.map (Scheme.subst σ)

private theorem underBinder_agrees {X : Constraints T O} (σ : Substitution T)
    (a : Names) (c : X.Formula) (t : T.Term) (v w : Valuation T.Value)
    (hw : w.AgreeOutside v
      ⟨a.types.image (Scheme.substAvoid σ a c t).shiftTypes,
       a.effects.image (Scheme.substAvoid σ a c t).shiftEffects⟩) :
    let avoid := Scheme.substAvoid σ a c t
    let η := σ.underBinder a avoid.shiftTypes avoid.shiftEffects
    ∀ z : Valuation T.Value,
      (∀ i ∈ a.types, z.types i = w.types (avoid.shiftTypes i)) →
      (∀ i ∈ a.effects, z.effects i = w.effects (avoid.shiftEffects i)) →
      z.AgreeOutside (σ.pullback v) a →
      (η.pullback w).AgreeOn z ((X.support c).union (T.support t)) := by
  dsimp only
  let u := (X.support c).union (T.support t)
  let avoid := Scheme.substAvoid σ a c t
  let b : Names := ⟨a.types.image avoid.shiftTypes, a.effects.image avoid.shiftEffects⟩
  have fresh : b.Disjoint avoid :=
    ⟨avoid.shiftTypes_disjoint a, avoid.shiftEffects_disjoint a⟩
  have includes : (u.union σ.range).Subset avoid := by
    constructor <;> intro i hi
    · rcases Finset.mem_union.mp hi with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
    · rcases Finset.mem_union.mp hi with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
  intro z ht he hz
  constructor
  · intro i hi
    by_cases ha : i ∈ a.types
    · simpa [Substitution.pullback, Substitution.underBinder, ha, T.eval_var]
        using (ht i ha).symm
    · have support := (σ.type_support_subset u hi).trans includes
      have same : T.eval w (σ.types i) = T.eval v (σ.types i) := by
        apply T.eval_support
        exact ⟨fun j hj => hw.1 j (fun hb => Finset.disjoint_left.mp fresh.1 hb (support.1 hj)),
          fun j hj => hw.2 j (fun hb => Finset.disjoint_left.mp fresh.2 hb (support.2 hj))⟩
      simpa [Substitution.pullback, Substitution.underBinder, ha] using
        same.trans (hz.1 i ha).symm
  · intro i hi
    by_cases ha : i ∈ a.effects
    · simpa [Substitution.pullback, Substitution.underBinder, ha, Effect.eval, Effect.var]
        using (he i ha).symm
    · have support := (σ.effect_support_subset u hi).trans includes.2
      have same := Effect.eval_support (σ.effects i) w.effects v.effects
        (fun j hj => hw.2 j (fun hb => Finset.disjoint_left.mp fresh.2 hb (support hj)))
      simpa [Substitution.pullback, Substitution.underBinder, ha] using
        same.trans (hz.2 i ha).symm

theorem Scheme.groundInstance_subst {X : Constraints T O} (σ : Substitution T)
    (s : Scheme X) (v : Valuation T.Value) (value : T.Value) :
    (s.subst σ).GroundInstance v value ↔ s.GroundInstance (σ.pullback v) value := by
  cases s with
  | mono t => exact (congrArg (fun x => O.le x value) (σ.eval_apply v t)).to_iff
  | qualified a c t =>
    let avoid := Scheme.substAvoid σ a c t
    let b : Names := ⟨a.types.image avoid.shiftTypes, a.effects.image avoid.shiftEffects⟩
    let η := σ.underBinder a avoid.shiftTypes avoid.shiftEffects
    change (∃ w, w.AgreeOutside v b ∧ X.holds (X.subst η c) w ∧
      O.le (T.eval w (η.apply t)) value) ↔ _
    constructor
    · rintro ⟨w, hw, hc, ht⟩
      let z := (σ.pullback v).patch
        ⟨w.types ∘ avoid.shiftTypes, w.effects ∘ avoid.shiftEffects⟩ a
      have hz : z.AgreeOutside (σ.pullback v) a := Valuation.patch_agreeOutside _ _ _
      have same := underBinder_agrees σ a c t v w hw z
        (by intro i hi; simp [z, Valuation.patch, hi, avoid])
        (by intro i hi; simp [z, Valuation.patch, hi, avoid]) hz
      refine ⟨z, hz, ?_, ?_⟩
      · exact (X.holds_support c _ _ (same.mono (Names.subset_union_left _ _))).mp
          ((X.holds_subst _ _ _).mp hc)
      · rw [Substitution.eval_apply,
          T.eval_support _ z t (same.mono (Names.subset_union_right _ _))] at ht
        exact ht
    · rintro ⟨z, hz, hc, ht⟩
      let w := v.assignImages z a avoid.shiftTypes avoid.shiftEffects
      have hw : w.AgreeOutside v b := by
        constructor
        · intro i hi
          exact (v.assignImages_agree z a avoid.shiftTypes avoid.shiftEffects ⟨{i}, ∅⟩
            (by simpa [b] using hi) (by simp)).1 i (by simp)
        · intro i hi
          exact (v.assignImages_agree z a avoid.shiftTypes avoid.shiftEffects ⟨∅, {i}⟩
            (by simp) (by simpa [b] using hi)).2 i (by simp)
      have same := underBinder_agrees σ a c t v w hw z
        (fun i hi => (v.assignImages_types z a _ _ avoid.shiftTypes_injective.injOn i hi).symm)
        (fun i hi => (v.assignImages_effects z a _ _ avoid.shiftEffects_injective.injOn i hi).symm) hz
      refine ⟨w, hw, (X.holds_subst _ _ _).mpr ?_, ?_⟩
      · exact (X.holds_support c _ _ (same.mono (Names.subset_union_left _ _))).mpr hc
      · rw [Substitution.eval_apply, T.eval_support _ z t (same.mono (Names.subset_union_right _ _))]
        exact ht

theorem Context.ground_subst {X : Constraints T O} (σ : Substitution T)
    (g : Context X) (v : Valuation T.Value) :
    (g.subst σ).ground v = g.ground (σ.pullback v) := by
  simp only [Context.subst, Context.ground, List.map_map]
  apply List.map_congr_left
  intro s _
  funext value
  exact propext (s.groundInstance_subst σ v value)

/-- Renaming a bound scheme before substitution does not change its meaning. -/
theorem Scheme.AlphaEquivalent.groundInstance_subst_iff {X : Constraints T O}
    {s t : Scheme X} (h : Scheme.AlphaEquivalent X s t) (σ : Substitution T)
    (v : Valuation T.Value) (value : T.Value) :
    (s.subst σ).GroundInstance v value ↔ (t.subst σ).GroundInstance v value := by
  rw [s.groundInstance_subst, t.groundInstance_subst]
  exact h.groundInstance_iff _ _

theorem Scheme.groundInstance_subst_compose {X : Constraints T O}
    (σ θ : Substitution T) (s : Scheme X) (v : Valuation T.Value) (value : T.Value) :
    ((s.subst σ).subst θ).GroundInstance v value ↔
      (s.subst (θ.compose σ)).GroundInstance v value := by
  simp only [Scheme.groundInstance_subst, Substitution.compose_pullback]

private def Substitution.boundInstance (σ θ : Substitution T) (a avoid : Names) :
    Substitution T where
  domain := ⟨a.types.image avoid.shiftTypes, a.effects.image avoid.shiftEffects⟩
  types := fun j => if j ∈ a.types.image avoid.shiftTypes then
    σ.apply (θ.types (j - (avoid.types.sup id + 1))) else T.var j
  effects := fun j => if j ∈ a.effects.image avoid.shiftEffects then
    (θ.effects (j - (avoid.effects.sup id + 1))).subst σ.effects else Effect.var j
  types_outside := by intro i hi; simp [hi]
  effects_outside := by intro i hi; simp [hi]

/-- Transport a syntactic monomorphic instance using one finite substitution.
This is stronger than merely transporting sets of ground instances. -/
theorem Instance.subst_mono {X : Constraints T O} {c : X.Formula}
    {s : Scheme X} {t : T.Term} (h : Instance X c s (.mono t)) (σ : Substitution T) :
    Instance X (X.subst σ c) (s.subst σ) (.mono (σ.apply t)) := by
  cases s with
  | mono u =>
    apply Instance.sub
    intro v hv
    have original := h.groundInstance ((X.holds_subst _ _ _).mp hv) (O.refl _)
    exact (X.holds_le _ _ _).mpr (by
      simpa only [Scheme.GroundInstance, Substitution.eval_apply] using original)
  | qualified a d u =>
    obtain ⟨θ, hθ, hd, ht⟩ := Instance.qualified_mono_iff.mp h
    let avoid := Scheme.substAvoid σ a d u
    let b : Names := ⟨a.types.image avoid.shiftTypes, a.effects.image avoid.shiftEffects⟩
    let η := σ.underBinder a avoid.shiftTypes avoid.shiftEffects
    let ψ := σ.boundInstance θ a avoid
    have same (v : Valuation T.Value) :
        (η.pullback (ψ.pullback v)).AgreeOn (θ.pullback (σ.pullback v))
          ((X.support d).union (T.support u)) := by
      apply underBinder_agrees σ a d u v (ψ.pullback v) (ψ.pullback_outside v)
      · intro i hi
        simp [ψ, Substitution.boundInstance, Substitution.pullback,
          Names.shiftTypes, Substitution.eval_apply, avoid, hi]
      · intro i hi
        simp [ψ, Substitution.boundInstance, Substitution.pullback,
          Names.shiftEffects, Effect.eval_subst, avoid, hi]
      · exact ⟨fun i hi => (θ.pullback_outside _).1 i (fun hm => hi (hθ.1 hm)),
          fun i hi => (θ.pullback_outside _).2 i (fun hm => hi (hθ.2 hm))⟩
    apply Instance.forallLeft ψ (by exact fun _ h => h) (by exact fun _ h => h)
    · intro v hv
      apply (X.holds_subst _ _ _).mpr
      apply (X.holds_subst _ _ _).mpr
      apply (X.holds_support d _ _ ((same v).mono (Names.subset_union_left _ _))).mpr
      exact (X.holds_subst _ _ _).mp (hd _ ((X.holds_subst _ _ _).mp hv))
    · apply Instance.sub
      intro v hv
      apply (X.holds_le _ _ _).mpr
      have H := (X.holds_le _ _ _).mp (ht _ ((X.holds_subst _ _ _).mp hv))
      change O.le (T.eval v (ψ.apply (η.apply u))) (T.eval v (σ.apply t))
      rw [Substitution.eval_apply, Substitution.eval_apply,
        T.eval_support _ _ u ((same v).mono (Names.subset_union_right _ _))]
      simpa only [Substitution.eval_apply] using H

theorem Scheme.Realizable.subst {X : Constraints T O} {s : Scheme X} {c : X.Formula}
    (h : s.Realizable c) (σ : Substitution T) : (s.subst σ).Realizable (X.subst σ c) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨σ.apply t, ht.subst_mono σ⟩

theorem Context.Realizable.subst {X : Constraints T O} {g : Context X} {c : X.Formula}
    (h : g.Realizable c) (σ : Substitution T) : (g.subst σ).Realizable (X.subst σ c) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact (h t ht).subst σ

theorem Scheme.admissible_of_groundInstance {X : Constraints T O}
    {s : Scheme X} {v : Valuation T.Value} {t : T.Value}
    (h : s.GroundInstance v t) : s.Admissible X.Satisfiable := by
  cases s with
  | mono => trivial
  | qualified a c u =>
    obtain ⟨w, _, hc, _⟩ := h
    exact (X.admissible_satisfiable_iff c).mpr ⟨w, hc⟩

theorem Scheme.Realizable.admissible_subst {X : Constraints T O}
    {s : Scheme X} {c : X.Formula} (h : s.Realizable c) (σ : Substitution T)
    (hc : X.Satisfiable (X.subst σ c)) : (s.subst σ).Admissible X.Satisfiable := by
  obtain ⟨v, hv⟩ := hc
  obtain ⟨t, ht⟩ := (h.subst σ).groundInstance hv
  exact Scheme.admissible_of_groundInstance ht

theorem Context.Realizable.admissible_subst {X : Constraints T O}
    {g : Context X} {c : X.Formula} (h : g.Realizable c) (σ : Substitution T)
    (hc : X.Satisfiable (X.subst σ c)) : (g.subst σ).Admissible X.Satisfiable := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact (h t ht).admissible_subst σ hc

end EHMX.HMX
