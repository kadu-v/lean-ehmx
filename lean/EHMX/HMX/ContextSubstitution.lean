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

/-- Substituted schemes have the same uniform monotype instances when the
substitutions agree on the original scheme's free names. The witness is
transported between the two fresh binders; ground-instance inclusion alone
would not establish this statement. -/
theorem Instance.subst_mono_congr {X : Constraints T O} {s : Scheme X}
    (σ τ : Substitution T)
    (ht : ∀ v i, s.FreeType i → (σ.pullback v).types i = (τ.pullback v).types i)
    (he : ∀ v i, s.FreeEffect i → (σ.pullback v).effects i = (τ.pullback v).effects i)
    {c : X.Formula} {target : T.Term}
    (h : Instance X c (s.subst σ) (.mono target)) :
    Instance X c (s.subst τ) (.mono target) := by
  cases s with
  | mono t =>
      apply Instance.sub
      intro v hv
      have original := h.groundInstance hv (O.refl _)
      change O.le (T.eval v (σ.apply t)) (T.eval v target) at original
      apply (X.holds_le _ _ _).mpr
      rw [Substitution.eval_apply, ← T.eval_support (σ.pullback v) (τ.pullback v) t ⟨ht v, he v⟩]
      simpa only [Substitution.eval_apply] using original
  | qualified a d t =>
      let fs := Scheme.substAvoid σ a d t
      let ft := Scheme.substAvoid τ a d t
      let bs : Names := ⟨a.types.image fs.shiftTypes, a.effects.image fs.shiftEffects⟩
      let bt : Names := ⟨a.types.image ft.shiftTypes, a.effects.image ft.shiftEffects⟩
      let ηs := σ.underBinder a fs.shiftTypes fs.shiftEffects
      let ηt := τ.underBinder a ft.shiftTypes ft.shiftEffects
      obtain ⟨θ, hθ, hd, hu⟩ := Instance.qualified_mono_iff.mp h
      change θ.domain.Subset bs at hθ
      let ψ : Substitution T := {
        domain := bt
        types := fun j => if j ∈ bt.types then
          θ.types (fs.shiftTypes (j - (ft.types.sup id + 1))) else T.var j
        effects := fun j => if j ∈ bt.effects then
          θ.effects (fs.shiftEffects (j - (ft.effects.sup id + 1))) else Effect.var j
        types_outside := by intro i hi; simp [hi]
        effects_outside := by intro i hi; simp [hi] }
      have outsideS (v : Valuation T.Value) : (θ.pullback v).AgreeOutside v bs :=
        ⟨fun i hi => (θ.pullback_outside v).1 i (fun h => hi (hθ.1 h)),
         fun i hi => (θ.pullback_outside v).2 i (fun h => hi (hθ.2 h))⟩
      have compare (v : Valuation T.Value) :
          (X.holds d (ηs.pullback (θ.pullback v)) ↔
            X.holds d (ηt.pullback (ψ.pullback v))) ∧
          T.eval (ηs.pullback (θ.pullback v)) t =
            T.eval (ηt.pullback (ψ.pullback v)) t := by
        let values : Valuation T.Value :=
          ⟨fun i => (θ.pullback v).types (fs.shiftTypes i),
           fun i => (θ.pullback v).effects (fs.shiftEffects i)⟩
        let z := (σ.pullback v).patch values a
        let w := (τ.pullback v).patch values a
        have hs := underBinder_agrees σ a d t v (θ.pullback v) (outsideS v) z
          (by intro i hi; simp [z, Valuation.patch, hi, values, fs])
          (by intro i hi; simp [z, Valuation.patch, hi, values, fs])
          (Valuation.patch_agreeOutside _ _ _)
        have ht' := underBinder_agrees τ a d t v (ψ.pullback v) (ψ.pullback_outside v) w
          (by
            intro i hi
            have hb : ft.shiftTypes i ∈ bt.types := Finset.mem_image.mpr ⟨i, hi, rfl⟩
            simp only [w, Valuation.patch, hi, ite_true, values]
            change T.eval v (θ.types (fs.shiftTypes i)) =
              T.eval v (ψ.types (ft.shiftTypes i))
            dsimp only [ψ]
            rw [ite_eq_left hb]
            simp only [Names.shiftTypes, Nat.add_sub_cancel_left])
          (by
            intro i hi
            have hb : ft.shiftEffects i ∈ bt.effects := Finset.mem_image.mpr ⟨i, hi, rfl⟩
            simp only [w, Valuation.patch, hi, ite_true, values]
            change (θ.effects (fs.shiftEffects i)).eval v.effects =
              (ψ.effects (ft.shiftEffects i)).eval v.effects
            dsimp only [ψ]
            rw [ite_eq_left hb]
            simp only [Names.shiftEffects, Nat.add_sub_cancel_left])
          (Valuation.patch_agreeOutside _ _ _)
        have types (i : Nat) (hi : X.FreeType d i ∨ i ∈ (T.support t).types) :
            z.types i = w.types i := by
          by_cases ha : i ∈ a.types
          · simp [z, w, Valuation.patch, ha]
          · simpa [z, w, Valuation.patch, ha] using ht v i ⟨ha, hi⟩
        have effects (i : Nat) (hi : X.FreeEffect d i ∨ i ∈ (T.support t).effects) :
            z.effects i = w.effects i := by
          by_cases ha : i ∈ a.effects
          · simp [z, w, Valuation.patch, ha]
          · simpa [z, w, Valuation.patch, ha] using he v i ⟨ha, hi⟩
        constructor
        · exact (X.holds_support d _ _ (hs.mono (Names.subset_union_left _ _))).trans
            ((X.holds_semanticSupport d z w (fun i hi => types i (.inl hi))
              (fun i hi => effects i (.inl hi))).trans
                (X.holds_support d _ _ (ht'.mono (Names.subset_union_left _ _))).symm)
        · exact (T.eval_support _ _ t (hs.mono (Names.subset_union_right _ _))).trans
            ((T.eval_support z w t ⟨fun i hi => types i (.inr hi),
              fun i hi => effects i (.inr hi)⟩).trans
                (T.eval_support _ _ t (ht'.mono (Names.subset_union_right _ _))).symm)
      apply Instance.forallLeft ψ (by exact fun _ h => h) (by exact fun _ h => h)
      · intro v hv
        apply (X.holds_subst _ _ _).mpr
        apply (X.holds_subst _ _ _).mpr
        exact (compare v).1.mp ((X.holds_subst _ _ _).mp
          ((X.holds_subst _ _ _).mp (hd v hv)))
      · apply Instance.sub
        intro v hv
        apply (X.holds_le _ _ _).mpr
        have old := (X.holds_le _ _ _).mp (hu v hv)
        change O.le (T.eval v (θ.apply (ηs.apply t))) (T.eval v target) at old
        change O.le (T.eval v (ψ.apply (ηt.apply t))) (T.eval v target)
        simpa only [Substitution.eval_apply, ← (compare v).2] using old

/-- Override precisely the locally bound variables, leaving the outer finite
substitution unchanged. Images are simultaneous, not recursively substituted. -/
def Substitution.override (σ θ : Substitution T) (a : Names) : Substitution T where
  domain := a.union σ.domain
  types := fun i => if i ∈ a.types then θ.types i else σ.types i
  effects := fun i => if i ∈ a.effects then θ.effects i else σ.effects i
  types_outside := by
    intro i hi
    obtain ⟨ha, hs⟩ := Finset.notMem_union.mp hi
    simp [ha, σ.types_outside i hs]
  effects_outside := by
    intro i hi
    obtain ⟨ha, hs⟩ := Finset.notMem_union.mp hi
    simp [ha, σ.effects_outside i hs]

theorem Substitution.override_outside (σ θ : Substitution T) (a : Names)
    (v : Valuation T.Value) :
    ((σ.override θ a).pullback v).AgreeOutside (σ.pullback v) a := by
  constructor <;> intro i hi <;> simp [override, Substitution.pullback, hi]

/-- A monotype instance after capture-avoiding substitution is represented by
one finite extension of the outer substitution. This exposes the original
binder, independently of the fresh names chosen by `Scheme.subst`. -/
theorem Instance.subst_qualified_mono_iff {X : Constraints T O}
    (σ : Substitution T) {c d : X.Formula} {a : Names} {t u : T.Term} :
    Instance X c ((Scheme.qualified a d t).subst σ) (.mono u) ↔
      ∃ η : Substitution T,
        (∀ v, (η.pullback v).AgreeOutside (σ.pullback v) a) ∧
        X.Entails c (X.subst η d) ∧ X.Entails c (X.le (η.apply t) u) := by
  let avoid := Scheme.substAvoid σ a d t
  let b : Names := ⟨a.types.image avoid.shiftTypes, a.effects.image avoid.shiftEffects⟩
  let κ := σ.underBinder a avoid.shiftTypes avoid.shiftEffects
  constructor
  · intro h
    obtain ⟨θ, hθ, hd, ht⟩ := Instance.qualified_mono_iff.mp h
    let ζ : Substitution T := {
      domain := a
      types := fun i => if i ∈ a.types then θ.types (avoid.shiftTypes i) else T.var i
      effects := fun i => if i ∈ a.effects then θ.effects (avoid.shiftEffects i) else Effect.var i
      types_outside := by intro i hi; simp [hi]
      effects_outside := by intro i hi; simp [hi] }
    let η := σ.override ζ a
    have same (v : Valuation T.Value) :
        (κ.pullback (θ.pullback v)).AgreeOn (η.pullback v)
          ((X.support d).union (T.support t)) := by
      apply underBinder_agrees σ a d t v (θ.pullback v)
        ⟨fun i hi => (θ.pullback_outside v).1 i (fun h => hi (hθ.1 h)),
         fun i hi => (θ.pullback_outside v).2 i (fun h => hi (hθ.2 h))⟩
      · intro i hi; simp [η, Substitution.override, ζ, Substitution.pullback, hi, avoid]
      · intro i hi; simp [η, Substitution.override, ζ, Substitution.pullback, hi, avoid]
      · exact σ.override_outside ζ a v
    refine ⟨η, σ.override_outside ζ a, ?_, ?_⟩
    · intro v hv
      apply (X.holds_subst _ _ _).mpr
      exact (X.holds_support d _ _ ((same v).mono (Names.subset_union_left _ _))).mp
        ((X.holds_subst _ _ _).mp ((X.holds_subst _ _ _).mp (hd v hv)))
    · intro v hv
      apply (X.holds_le _ _ _).mpr
      have old := (X.holds_le _ _ _).mp (ht v hv)
      change O.le (T.eval v (θ.apply (κ.apply t))) (T.eval v u) at old
      simpa only [Substitution.eval_apply,
        T.eval_support _ _ t ((same v).mono (Names.subset_union_right _ _))] using old
  · rintro ⟨η, outside, hd, ht⟩
    let θ : Substitution T := {
      domain := b
      types := fun j => if j ∈ b.types then
        η.types (j - (avoid.types.sup id + 1)) else T.var j
      effects := fun j => if j ∈ b.effects then
        η.effects (j - (avoid.effects.sup id + 1)) else Effect.var j
      types_outside := by intro i hi; simp [hi]
      effects_outside := by intro i hi; simp [hi] }
    have same (v : Valuation T.Value) :
        (κ.pullback (θ.pullback v)).AgreeOn (η.pullback v)
          ((X.support d).union (T.support t)) := by
      apply underBinder_agrees σ a d t v (θ.pullback v) (θ.pullback_outside v)
      · intro i hi
        have hb : avoid.shiftTypes i ∈ b.types := Finset.mem_image.mpr ⟨i, hi, rfl⟩
        change T.eval v (η.types i) = T.eval v (θ.types (avoid.shiftTypes i))
        dsimp only [θ]
        rw [ite_eq_left hb]
        simp only [Names.shiftTypes, Nat.add_sub_cancel_left]
      · intro i hi
        have hb : avoid.shiftEffects i ∈ b.effects := Finset.mem_image.mpr ⟨i, hi, rfl⟩
        change (η.effects i).eval v.effects = (θ.effects (avoid.shiftEffects i)).eval v.effects
        dsimp only [θ]
        rw [ite_eq_left hb]
        simp only [Names.shiftEffects, Nat.add_sub_cancel_left]
      · exact outside v
    apply Instance.forallLeft θ (fun _ h => h) (fun _ h => h)
    · intro v hv
      apply (X.holds_subst _ _ _).mpr
      apply (X.holds_subst _ _ _).mpr
      exact (X.holds_support d _ _ ((same v).mono (Names.subset_union_left _ _))).mpr
        ((X.holds_subst _ _ _).mp (hd v hv))
    · apply Instance.sub
      intro v hv
      apply (X.holds_le _ _ _).mpr
      change O.le (T.eval v (θ.apply (κ.apply t))) (T.eval v u)
      simpa only [Substitution.eval_apply,
        T.eval_support _ _ t ((same v).mono (Names.subset_union_right _ _))] using
        (X.holds_le _ _ _).mp (ht v hv)

private theorem qualified_rename_subst_mono_iff {X : Constraints T O}
    (σ : Substitution T) (p : Renaming) {a : Names} {d c : X.Formula} {t u : T.Term}
    (ht : ∀ i, (Scheme.qualified (X := X) a d t).FreeType i → p.types i = i)
    (he : ∀ i, (Scheme.qualified (X := X) a d t).FreeEffect i → p.effects i = i) :
    Instance X c ((Scheme.qualified a d t).subst σ) (.mono u) ↔
      Instance X c ((Scheme.qualified
        ⟨a.types.image p.types, a.effects.image p.effects⟩
        (X.subst (p.asSubstitution T) d) (T.rename p.types p.effects t)).subst σ) (.mono u) := by
  let b : Names := ⟨a.types.image p.types, a.effects.image p.effects⟩
  have compare (η ζ : Substitution T)
      (hT : ∀ v i, X.FreeType d i ∨ i ∈ (T.support t).types →
        (η.pullback v).types i = (ζ.pullback v).types (p.types i))
      (hE : ∀ v i, X.FreeEffect d i ∨ i ∈ (T.support t).effects →
        (η.pullback v).effects i = (ζ.pullback v).effects (p.effects i)) :
      (X.Entails c (X.subst η d) ↔
        X.Entails c (X.subst ζ (X.subst (p.asSubstitution T) d))) ∧
      (X.Entails c (X.le (η.apply t) u) ↔
        X.Entails c (X.le (ζ.apply (T.rename p.types p.effects t)) u)) := by
    have hc (v : Valuation T.Value) := X.holds_semanticSupport d
      (η.pullback v) ((p.asSubstitution T).pullback (ζ.pullback v))
      (fun i hi => by simpa [Substitution.pullback, Renaming.asSubstitution, T.eval_var] using hT v i (.inl hi))
      (fun i hi => by simpa [Substitution.pullback, Renaming.asSubstitution, Effect.eval, Effect.var] using hE v i (.inl hi))
    have hv (v : Valuation T.Value) : T.eval v (η.apply t) =
        T.eval v (ζ.apply (T.rename p.types p.effects t)) := by
      rw [Substitution.eval_apply, Substitution.eval_apply, T.eval_rename]
      exact T.eval_support _ _ t ⟨fun i hi => hT v i (.inr hi), fun i hi => hE v i (.inr hi)⟩
    constructor
    · constructor <;> intro h v hvc
      · exact (X.holds_subst _ _ _).mpr ((X.holds_subst _ _ _).mpr
          ((hc v).mp ((X.holds_subst _ _ _).mp (h v hvc))))
      · exact (X.holds_subst _ _ _).mpr ((hc v).mpr
          ((X.holds_subst _ _ _).mp ((X.holds_subst _ _ _).mp (h v hvc))))
    · constructor <;> intro h v hvc
      · exact (X.holds_le _ _ _).mpr ((hv v) ▸ (X.holds_le _ _ _).mp (h v hvc))
      · exact (X.holds_le _ _ _).mpr ((hv v).symm ▸ (X.holds_le _ _ _).mp (h v hvc))
  rw [Instance.subst_qualified_mono_iff, Instance.subst_qualified_mono_iff]
  constructor
  · rintro ⟨η, outside, hd, hu⟩
    let θ : Substitution T := {
      domain := b
      types := fun i => if i ∈ b.types then η.types (p.types.symm i) else T.var i
      effects := fun i => if i ∈ b.effects then η.effects (p.effects.symm i) else Effect.var i
      types_outside := by intro i hi; simp [hi]
      effects_outside := by intro i hi; simp [hi] }
    let ζ := σ.override θ b
    have hT (v : Valuation T.Value) (i : Nat)
        (hi : X.FreeType d i ∨ i ∈ (T.support t).types) :
        (η.pullback v).types i = (ζ.pullback v).types (p.types i) := by
      by_cases ha : i ∈ a.types
      · have hb : p.types i ∈ b.types := Finset.mem_image.mpr ⟨i, ha, rfl⟩
        simp [ζ, Substitution.override, θ, Substitution.pullback, hb]
      · have hb : p.types i ∉ b.types := by simpa [b] using ha
        simp only [ζ, Substitution.override, Substitution.pullback, ite_eq_right hb]
        simpa only [ht i ⟨ha, hi⟩, Substitution.pullback] using (outside v).1 i ha
    have hE (v : Valuation T.Value) (i : Nat)
        (hi : X.FreeEffect d i ∨ i ∈ (T.support t).effects) :
        (η.pullback v).effects i = (ζ.pullback v).effects (p.effects i) := by
      by_cases ha : i ∈ a.effects
      · have hb : p.effects i ∈ b.effects := Finset.mem_image.mpr ⟨i, ha, rfl⟩
        simp [ζ, Substitution.override, θ, Substitution.pullback, hb]
      · have hb : p.effects i ∉ b.effects := by simpa [b] using ha
        simp only [ζ, Substitution.override, Substitution.pullback, ite_eq_right hb]
        simpa only [he i ⟨ha, hi⟩, Substitution.pullback] using (outside v).2 i ha
    exact ⟨ζ, σ.override_outside θ b, (compare η ζ hT hE).1.mp hd, (compare η ζ hT hE).2.mp hu⟩
  · rintro ⟨ζ, outside, hd, hu⟩
    let θ : Substitution T := {
      domain := a
      types := fun i => if i ∈ a.types then ζ.types (p.types i) else T.var i
      effects := fun i => if i ∈ a.effects then ζ.effects (p.effects i) else Effect.var i
      types_outside := by intro i hi; simp [hi]
      effects_outside := by intro i hi; simp [hi] }
    let η := σ.override θ a
    have hT (v : Valuation T.Value) (i : Nat)
        (hi : X.FreeType d i ∨ i ∈ (T.support t).types) :
        (η.pullback v).types i = (ζ.pullback v).types (p.types i) := by
      by_cases ha : i ∈ a.types
      · simp [η, Substitution.override, θ, Substitution.pullback, ha]
      · have hb : p.types i ∉ b.types := by simpa [b] using ha
        simpa [η, Substitution.override, Substitution.pullback, ha, ht i ⟨ha, hi⟩] using ((outside v).1 (p.types i) hb).symm
    have hE (v : Valuation T.Value) (i : Nat)
        (hi : X.FreeEffect d i ∨ i ∈ (T.support t).effects) :
        (η.pullback v).effects i = (ζ.pullback v).effects (p.effects i) := by
      by_cases ha : i ∈ a.effects
      · simp [η, Substitution.override, θ, Substitution.pullback, ha]
      · have hb : p.effects i ∉ b.effects := by simpa [b] using ha
        simpa [η, Substitution.override, Substitution.pullback, ha, he i ⟨ha, hi⟩] using ((outside v).2 (p.effects i) hb).symm
    exact ⟨η, σ.override_outside θ a, (compare η ζ hT hE).1.mpr hd, (compare η ζ hT hE).2.mpr hu⟩

theorem Scheme.AlphaEquivalent.subst_mono_iff {X : Constraints T O} {s t : Scheme X}
    (h : Scheme.AlphaEquivalent X s t) (σ : Substitution T) (c : X.Formula) (u : T.Term) :
    Instance X c (s.subst σ) (.mono u) ↔ Instance X c (t.subst σ) (.mono u) := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | rename p ht he => exact qualified_rename_subst_mono_iff σ p ht he

private theorem Instance.subst_trans_mono_under {X : Constraints T O}
    {c : X.Formula} {s t : Scheme X} (h : Instance X c s t)
    (σ : Substitution T) {d : X.Formula} {u : T.Term}
    (hd : X.Entails d (X.subst σ c))
    (k : Instance X d (t.subst σ) (.mono u)) :
    Instance X d (s.subst σ) (.mono u) := by
  induction h generalizing σ d u with
  | sub he => exact (((Instance.sub he).subst_mono σ).weaken hd).trans k
  | forallLeft θ ht he hq premise =>
      exact (((Instance.forallLeft θ ht he hq premise).subst_mono σ).weaken hd).trans k
  | @forallRight c a q v s freshC freshS premise ih =>
      obtain ⟨η, outside, hq, hu⟩ := (Instance.subst_qualified_mono_iff σ).mp k
      have hcq : X.Entails d (X.subst η (X.and c q)) := by
        intro w hw
        apply (X.holds_subst _ _ _).mpr
        apply (X.holds_and _ _ _).mpr
        exact ⟨(X.holds_agreeOutside freshC (outside w)).mpr
          ((X.holds_and _ _ _).mp ((X.holds_subst _ _ _).mp (hd w hw))).1,
          (X.holds_subst _ _ _).mp (hq w hw)⟩
      have hi := ih η hcq (Instance.sub hu)
      exact hi.subst_mono_congr η σ
        (fun w i hf => (outside w).1 i (fun ha => freshS.1 i ha hf))
        (fun w i hf => (outside w).2 i (fun ha => freshS.2 i ha hf))
  | equivalent eq _ ih =>
      apply ih σ _ k
      intro v hv
      exact (X.holds_subst _ _ _).mpr (eq.2 _ ((X.holds_subst _ _ _).mp (hd v hv)))
  | alphaLeft eq _ ih => exact (eq.subst_mono_iff σ d u).mpr (ih σ hd k)
  | alphaRight eq _ ih => exact ih σ hd ((eq.subst_mono_iff σ d u).mpr k)

/-- Capture-avoiding substitution preserves the syntactic instance relation
for arbitrary qualified targets, with no solver or ground-representation
assumption. One finite witness is retained throughout each comparison. -/
theorem Instance.subst {X : Constraints T O} {c : X.Formula} {s t : Scheme X}
    (h : Instance X c s t) (σ : Substitution T) :
    Instance X (X.subst σ c) (s.subst σ) (t.subst σ) := by
  apply Instance.of_mono_targets
  · intro v hv
    obtain ⟨u, hu⟩ := h.target_nonempty ((X.holds_subst _ _ _).mp hv)
    exact ⟨u, (t.groundInstance_subst σ v u).mpr hu⟩
  · intro d u hd hu
    exact h.subst_trans_mono_under σ hd hu

/-- A finite bound on the free names after substitution. This uses syntactic
support only as an upper bound and makes no converse assumption. -/
theorem Scheme.subst_avoids {X : Constraints T O} (s : Scheme X) (σ : Substitution T)
    (a : Names) (fresh : a.Disjoint (s.support.union σ.range)) :
    (s.subst σ).Avoids a := by
  have typeImage {i : Nat} (hi : i ∈ s.support.types) :
      a.Disjoint (T.support (σ.types i)) := fresh.mono_right (σ.type_support_subset _ hi)
  have effectImage {i : Nat} (hi : i ∈ s.support.effects) :
      Disjoint a.effects (σ.effects i).vars := by
    exact fresh.2.mono_right (σ.effect_support_subset _ hi)
  cases s with
  | mono t =>
      have h := T.support_subst_avoids σ.types σ.effects t a
        (fun _ hi => typeImage hi) (fun _ hi => effectImage hi)
      exact ⟨fun _ hi hf => Finset.disjoint_left.mp h.1 hi hf,
        fun _ hi hf => Finset.disjoint_left.mp h.2 hi hf⟩
  | qualified b d t =>
      let avoid := Scheme.substAvoid σ b d t
      let renamed : Names := ⟨b.types.image avoid.shiftTypes, b.effects.image avoid.shiftEffects⟩
      let η := σ.underBinder b avoid.shiftTypes avoid.shiftEffects
      let remaining := a.diff renamed
      have ht {i : Nat} (hi : i ∈ ((X.support d).union (T.support t)).types) :
          remaining.Disjoint (T.support (η.types i)) := by
        by_cases hb : i ∈ b.types
        · have hm : avoid.shiftTypes i ∈ renamed.types := Finset.mem_image.mpr ⟨i, hb, rfl⟩
          simpa [η, Substitution.underBinder, hb, T.support_var, Names.Disjoint,
            remaining, Names.diff] using (fun (_ : avoid.shiftTypes i ∈ a.types) => hm)
        · have h := typeImage (Finset.mem_sdiff.mpr ⟨hi, hb⟩)
          simpa [η, Substitution.underBinder, hb] using
            (show remaining.Disjoint (T.support (σ.types i)) from
              ⟨h.1.mono_left Finset.sdiff_subset, h.2.mono_left Finset.sdiff_subset⟩)
      have he {i : Nat} (hi : i ∈ ((X.support d).union (T.support t)).effects) :
          Disjoint remaining.effects (η.effects i).vars := by
        by_cases hb : i ∈ b.effects
        · have hm : avoid.shiftEffects i ∈ renamed.effects := Finset.mem_image.mpr ⟨i, hb, rfl⟩
          simpa [η, Substitution.underBinder, hb, Effect.var, remaining, Names.diff] using
            (fun (_ : avoid.shiftEffects i ∈ a.effects) => hm)
        · simpa [η, Substitution.underBinder, hb] using
            (effectImage (Finset.mem_sdiff.mpr ⟨hi, hb⟩)).mono_left
              (show remaining.effects ⊆ a.effects from Finset.sdiff_subset)
      have hc : X.Avoids (X.subst η d) remaining := by
        apply X.avoids_of_transport
        intro v w same hv
        apply (X.holds_subst _ _ _).mpr
        apply (X.holds_support d (η.pullback v) (η.pullback w) ?_).mp
          ((X.holds_subst _ _ _).mp hv)
        constructor
        · intro i hi
          exact T.eval_support v w (η.types i)
            ⟨fun j hj => same.1 j (fun ha => Finset.disjoint_left.mp (ht (Finset.mem_union_left _ hi)).1 ha hj),
             fun j hj => same.2 j (fun ha => Finset.disjoint_left.mp (ht (Finset.mem_union_left _ hi)).2 ha hj)⟩
        · intro i hi
          exact Effect.eval_support (η.effects i) v.effects w.effects
            (fun j hj => same.2 j (fun ha => Finset.disjoint_left.mp (he (Finset.mem_union_left _ hi)) ha hj))
      have ht' := T.support_subst_avoids η.types η.effects t remaining
        (fun _ hi => ht (Finset.mem_union_right _ hi))
        (fun _ hi => he (Finset.mem_union_right _ hi))
      constructor
      · intro i hi hfree
        have hr : i ∈ remaining.types := Finset.mem_sdiff.mpr ⟨hi, hfree.1⟩
        rcases hfree.2 with h | h
        · exact hc.1 i hr h
        · exact Finset.disjoint_left.mp ht'.1 hr h
      · intro i hi hfree
        have hr : i ∈ remaining.effects := Finset.mem_sdiff.mpr ⟨hi, hfree.1⟩
        rcases hfree.2 with h | h
        · exact hc.2 i hr h
        · exact Finset.disjoint_left.mp ht'.2 hr h

theorem Context.subst_avoids {X : Constraints T O} (g : Context X) (σ : Substitution T)
    (a : Names) (fresh : a.Disjoint (g.support.union σ.range)) :
    (g.subst σ).Avoids a := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  apply t.subst_avoids σ a
  apply fresh.mono_right
  have member : t.support.Subset g.support := by
    clear fresh hs
    induction g with
    | nil => cases ht
    | cons head tail ih =>
        rcases List.mem_cons.mp ht with rfl | hm
        · exact Names.subset_union_left _ _
        · exact (ih hm).trans (Names.subset_union_right _ _)
  exact (member.trans (Names.subset_union_left _ _)).union (Names.subset_union_right _ _)

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

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

def Substitution.restrictTo (σ : Substitution T) (a : Names) : Substitution T where
  domain := a
  types := fun i => if i ∈ a.types then σ.types i else T.var i
  effects := fun i => if i ∈ a.effects then σ.effects i else Effect.var i
  types_outside := by intro i hi; simp [hi]
  effects_outside := by intro i hi; simp [hi]

theorem Substitution.restrict_agrees {σ : Substitution T} {a u : Names}
    (protect : σ.domain.Disjoint (u.diff a)) (v : Valuation T.Value) :
    ((Substitution.restrictTo σ a).pullback v).AgreeOn (σ.pullback v) u := by
  constructor
  · intro i hi
    by_cases ha : i ∈ a.types
    · simp [Substitution.restrictTo, Substitution.pullback, ha]
    · have hd : i ∉ σ.domain.types := fun hd =>
        Finset.disjoint_left.mp protect.1 hd (Finset.mem_sdiff.mpr ⟨hi, ha⟩)
      simp [Substitution.restrictTo, Substitution.pullback, ha, σ.types_outside i hd]
  · intro i hi
    by_cases ha : i ∈ a.effects
    · simp [Substitution.restrictTo, Substitution.pullback, ha]
    · have hd : i ∉ σ.domain.effects := fun hd =>
        Finset.disjoint_left.mp protect.2 hd (Finset.mem_sdiff.mpr ⟨hi, ha⟩)
      simp [Substitution.restrictTo, Substitution.pullback, ha, σ.effects_outside i hd]

theorem Instance.subst_congr {s : Scheme X} (σ τ : Substitution T)
    (ht : ∀ v i, s.FreeType i → (σ.pullback v).types i = (τ.pullback v).types i)
    (he : ∀ v i, s.FreeEffect i → (σ.pullback v).effects i = (τ.pullback v).effects i)
    {c : X.Formula} {u : Scheme X} (h : Instance X c (s.subst σ) u) :
    Instance X c (s.subst τ) u := by
  apply Instance.of_mono_targets (fun _ hv => h.target_nonempty hv)
  intro d t hd inst
  exact ((h.weaken hd).trans inst).subst_mono_congr σ τ ht he

theorem Substitution.identity_apply (t : T.Term) : (Substitution.identity T).apply t = t :=
  T.subst_eq_self _ _ t (fun _ _ => rfl) (fun _ _ => rfl)

theorem Instance.subst_identity_mono_iff {c : X.Formula} (s : Scheme X) (u : T.Term) :
    Instance X c (s.subst (Substitution.identity T)) (.mono u) ↔
      Instance X c s (.mono u) := by
  constructor
  · intro h
    cases s with
    | mono t =>
      change Instance X c (.mono ((Substitution.identity T).apply t)) (.mono u) at h
      rwa [Substitution.identity_apply] at h
    | qualified a d t =>
      obtain ⟨η, outside, hd, ht⟩ := Instance.subst_qualified_mono_iff
        (Substitution.identity T) |>.mp h
      let κ := Substitution.restrictTo η a
      have same (v : Valuation T.Value) : κ.pullback v = η.pullback v := by
        apply congrArg₂ Valuation.mk
        · funext i
          by_cases hi : i ∈ a.types
          · simp [κ, Substitution.restrictTo, hi]
          · have out := (outside v).1 i hi
            simpa [κ, Substitution.restrictTo, Substitution.pullback, hi,
              Substitution.identity, T.eval_var] using out.symm
        · funext i
          by_cases hi : i ∈ a.effects
          · simp [κ, Substitution.restrictTo, hi]
          · have out := (outside v).2 i hi
            simpa [κ, Substitution.restrictTo, Substitution.pullback, hi,
              Substitution.identity, Effect.eval, Effect.var] using out.symm
      apply Instance.forallLeft κ (Finset.Subset.refl _) (Finset.Subset.refl _)
      · intro v hv
        apply (X.holds_subst _ _ _).mpr
        rw [same]
        exact (X.holds_subst _ _ _).mp (hd v hv)
      · apply Instance.sub
        intro v hv
        apply (X.holds_le _ _ _).mpr
        have old := (X.holds_le _ _ _).mp (ht v hv)
        simpa only [Substitution.eval_apply, same] using old
  · intro h
    have result := h.subst_mono (Substitution.identity T)
    rw [Substitution.identity_apply] at result
    refine Instance.equivalent ?_ result
    constructor <;> intro v hv
    · simpa only [X.holds_subst, Substitution.identity_pullback] using hv
    · simpa only [X.holds_subst, Substitution.identity_pullback] using hv

theorem Instance.subst_identity_iff {c : X.Formula} (s target : Scheme X) :
    Instance X c (s.subst (Substitution.identity T)) target ↔
      Instance X c s target := by
  constructor
  · intro h
    apply Instance.of_mono_targets (fun _ hv => h.target_nonempty hv)
    intro d u hd hu
    exact (Instance.subst_identity_mono_iff s u).mp ((h.weaken hd).trans hu)
  · intro h
    apply Instance.of_mono_targets (fun _ hv => h.target_nonempty hv)
    intro d u hd hu
    exact (Instance.subst_identity_mono_iff s u).mpr ((h.weaken hd).trans hu)


end EHMX.HMX
