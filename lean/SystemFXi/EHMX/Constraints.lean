import SystemFXi.EHMX.Syntax
import Mathlib.Data.Finset.Sort

namespace SystemFXi.EHMX

/-- Updating the same bound type name preserves agreement on a constraint's
support when the free names outside that binder already agree. -/
private theorem agree_type_update {X : Domain} (c : Constraint X)
    (v w : Valuation) (i : Nat) (t : GroundTy)
    (h : ∀ j ∈ c.fvTypes.erase i, v.types j = w.types j) :
    ∀ j ∈ c.fvTypes,
      (Function.update v.types i t) j = (Function.update w.types i t) j := by
  intro j hj
  by_cases hji : j = i
  · subst j; simp
  · simp [Function.update, hji, h j (Finset.mem_erase.mpr ⟨hji, hj⟩)]

private theorem agree_effect_update {X : Domain} (c : Constraint X)
    (v w : Valuation) (i : Nat) (ε : Finset Op)
    (h : ∀ j ∈ c.fvEffects.erase i, v.effects j = w.effects j) :
    ∀ j ∈ c.fvEffects,
      (Function.update v.effects i ε) j = (Function.update w.effects i ε) j := by
  intro j hj
  by_cases hji : j = i
  · subst j; simp
  · simp [Function.update, hji, h j (Finset.mem_erase.mpr ⟨hji, hj⟩)]

/-- The syntactic free-variable sets of the combined constraint domain bound
all semantic dependencies, provided X obeys the same HM(X) support law. -/
theorem Constraint.holds_support {X : Domain} (hX : LawfulSupport X)
    (c : Constraint X) (v w : Valuation)
    (ht : ∀ i ∈ c.fvTypes, v.types i = w.types i)
    (he : ∀ i ∈ c.fvEffects, v.effects i = w.effects i) :
    c.holds v ↔ c.holds w := by
  revert ht he
  induction c generalizing v w with
  | top => intros; rfl
  | and c d ihc ihd =>
      intro ht he
      have htc : ∀ i ∈ c.fvTypes, v.types i = w.types i := by
        intro i hi; exact ht i (by simp [Constraint.fvTypes, hi])
      have htd : ∀ i ∈ d.fvTypes, v.types i = w.types i := by
        intro i hi; exact ht i (by simp [Constraint.fvTypes, hi])
      have hec : ∀ i ∈ c.fvEffects, v.effects i = w.effects i := by
        intro i hi; exact he i (by simp [Constraint.fvEffects, hi])
      have hed : ∀ i ∈ d.fvEffects, v.effects i = w.effects i := by
        intro i hi; exact he i (by simp [Constraint.fvEffects, hi])
      simpa [Constraint.holds] using
        and_congr (ihc v w htc hec) (ihd v w htd hed)
  | typeEq a b =>
      intro ht he
      have ha : a.eval v = a.eval w := Ty.eval_support a v w
        (by intro i hi; exact ht i (by simp [Constraint.fvTypes, hi]))
        (by intro i hi; exact he i (by simp [Constraint.fvEffects, hi]))
      have hb : b.eval v = b.eval w := Ty.eval_support b v w
        (by intro i hi; exact ht i (by simp [Constraint.fvTypes, hi]))
        (by intro i hi; exact he i (by simp [Constraint.fvEffects, hi]))
      simp only [Constraint.holds, ha, hb]
  | effectLe ε η =>
      intro _ he
      have hε := Effect.eval_support ε v w (by
        intro i hi; exact he i (by simp [Constraint.fvEffects, hi]))
      have hη := Effect.eval_support η v w (by
        intro i hi; exact he i (by simp [Constraint.fvEffects, hi]))
      simp only [Constraint.holds, hε, hη]
  | lacks op ε =>
      intro _ he
      have hε := Effect.eval_support ε v w (by
        intro i hi; exact he i (by simp [Constraint.fvEffects, hi]))
      simp only [Constraint.holds, hε]
  | predicate p =>
      intro ht he
      exact hX.holds_support p v w ht he
  | allTy i c ih =>
      intro ht he
      constructor <;> intro h t
      · exact (ih {v with types := Function.update v.types i t}
          {w with types := Function.update w.types i t}
          (agree_type_update c v w i t ht) he).mp (h t)
      · exact (ih {w with types := Function.update w.types i t}
          {v with types := Function.update v.types i t}
          (agree_type_update c w v i t
          (by intro j hj; exact (ht j hj).symm))
          (by intro j hj; exact (he j hj).symm)).mp (h t)
  | allEff i c ih =>
      intro ht he
      constructor <;> intro h ε
      · exact (ih {v with effects := Function.update v.effects i ε}
          {w with effects := Function.update w.effects i ε}
          ht (agree_effect_update c v w i ε he)).mp (h ε)
      · exact (ih {w with effects := Function.update w.effects i ε}
          {v with effects := Function.update v.effects i ε}
          (by intro j hj; exact (ht j hj).symm)
          (agree_effect_update c w v i ε
            (by intro j hj; exact (he j hj).symm))).mp (h ε)
  | exTy i c ih =>
      intro ht he
      constructor
      · rintro ⟨t, h⟩
        exact ⟨t, (ih {v with types := Function.update v.types i t}
          {w with types := Function.update w.types i t}
          (agree_type_update c v w i t ht) he).mp h⟩
      · rintro ⟨t, h⟩
        exact ⟨t, (ih {w with types := Function.update w.types i t}
          {v with types := Function.update v.types i t}
          (agree_type_update c w v i t
          (by intro j hj; exact (ht j hj).symm))
          (by intro j hj; exact (he j hj).symm)).mp h⟩
  | exEff i c ih =>
      intro ht he
      constructor
      · rintro ⟨ε, h⟩
        exact ⟨ε, (ih {v with effects := Function.update v.effects i ε}
          {w with effects := Function.update w.effects i ε}
          ht (agree_effect_update c v w i ε he)).mp h⟩
      · rintro ⟨ε, h⟩
        exact ⟨ε, (ih {w with effects := Function.update w.effects i ε}
          {v with effects := Function.update v.effects i ε}
          (by intro j hj; exact (ht j hj).symm)
          (agree_effect_update c w v i ε
            (by intro j hj; exact (he j hj).symm))).mp h⟩

private theorem pullback_update_type (v : Valuation)
    (ρ η : Nat → Nat) (hρ : Function.Injective ρ)
    (i : Nat) (t : GroundTy) :
    ({v with types := Function.update v.types (ρ i) t}.pullback ρ η) =
      {(v.pullback ρ η) with types := Function.update (v.types ∘ ρ) i t} := by
  have hfun : (fun j => Function.update v.types (ρ i) t (ρ j)) =
      Function.update (v.types ∘ ρ) i t := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · have hne : ρ j ≠ ρ i := fun h => hji (hρ h)
      simp [Function.update, hji, hne]
  change (⟨fun j => Function.update v.types (ρ i) t (ρ j),
    v.effects ∘ η⟩ : Valuation) =
      ⟨Function.update (v.types ∘ ρ) i t, v.effects ∘ η⟩
  exact congrArg (fun f => (⟨f, v.effects ∘ η⟩ : Valuation)) hfun

private theorem pullback_update_effect (v : Valuation)
    (ρ η : Nat → Nat) (hη : Function.Injective η)
    (i : Nat) (ε : Finset Op) :
    ({v with effects := Function.update v.effects (η i) ε}.pullback ρ η) =
      {(v.pullback ρ η) with effects := Function.update (v.effects ∘ η) i ε} := by
  have hfun : (fun j => Function.update v.effects (η i) ε (η j)) =
      Function.update (v.effects ∘ η) i ε := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · have hne : η j ≠ η i := fun h => hji (hη h)
      simp [Function.update, hji, hne]
  change (⟨v.types ∘ ρ,
    fun j => Function.update v.effects (η i) ε (η j)⟩ : Valuation) =
      ⟨v.types ∘ ρ, Function.update (v.effects ∘ η) i ε⟩
  exact congrArg (fun f => (⟨v.types ∘ ρ, f⟩ : Valuation)) hfun

/-- Renaming commutes with all four constraint quantifiers when both maps are
injective. The law for the added predicates is exactly `LawfulRename X`. -/
theorem Constraint.holds_rename_injective {X : Domain}
    (hX : LawfulRename X) (c : Constraint X)
    (ρ η : Nat → Nat) (hρ : Function.Injective ρ)
    (hη : Function.Injective η) (v : Valuation) :
    (c.rename ρ η).holds v ↔ c.holds (v.pullback ρ η) := by
  induction c generalizing v with
  | top => rfl
  | and c d ihc ihd =>
      simp [Constraint.rename, Constraint.holds,
        ihc v, ihd v]
  | typeEq a b =>
      simp [Constraint.rename, Constraint.holds, Ty.eval_rename]
  | effectLe ε ζ =>
      simp [Constraint.rename, Constraint.holds, Effect.eval_rename,
        Valuation.pullback]
  | lacks op ε =>
      simp [Constraint.rename, Constraint.holds, Effect.eval_rename,
        Valuation.pullback]
  | predicate p =>
      exact hX.holds_rename ρ η p v
  | allTy i c ih =>
      simp only [Constraint.rename, Constraint.holds]
      constructor <;> intro h t
      · have h' := (ih _).mp (h t)
        rw [pullback_update_type v ρ η hρ i t] at h'
        simpa [Valuation.pullback] using h'
      · apply (ih _).mpr
        rw [pullback_update_type v ρ η hρ i t]
        simpa [Valuation.pullback] using h t
  | allEff i c ih =>
      simp only [Constraint.rename, Constraint.holds]
      constructor <;> intro h ε
      · have h' := (ih _).mp (h ε)
        rw [pullback_update_effect v ρ η hη i ε] at h'
        simpa [Valuation.pullback] using h'
      · apply (ih _).mpr
        rw [pullback_update_effect v ρ η hη i ε]
        simpa [Valuation.pullback] using h ε
  | exTy i c ih =>
      simp only [Constraint.rename, Constraint.holds]
      constructor
      · rintro ⟨t, h⟩
        refine ⟨t, ?_⟩
        have h' := (ih _).mp h
        rw [pullback_update_type v ρ η hρ i t] at h'
        simpa [Valuation.pullback] using h'
      · rintro ⟨t, h⟩
        refine ⟨t, (ih _).mpr ?_⟩
        rw [pullback_update_type v ρ η hρ i t]
        simpa [Valuation.pullback] using h
  | exEff i c ih =>
      simp only [Constraint.rename, Constraint.holds]
      constructor
      · rintro ⟨ε, h⟩
        refine ⟨ε, ?_⟩
        have h' := (ih _).mp h
        rw [pullback_update_effect v ρ η hη i ε] at h'
        simpa [Valuation.pullback] using h'
      · rintro ⟨ε, h⟩
        refine ⟨ε, (ih _).mpr ?_⟩
        rw [pullback_update_effect v ρ η hη i ε]
        simpa [Valuation.pullback] using h

def Constraint.usedTypes {X : Domain} (c : Constraint X) : Finset Nat :=
  c.fvTypes ∪ c.boundTypes

def Constraint.usedEffects {X : Domain} (c : Constraint X) : Finset Nat :=
  c.fvEffects ∪ c.boundEffects

theorem Constraint.usedTypes_and {X : Domain}
    (c d : Constraint X) :
    (Constraint.and c d).usedTypes = c.usedTypes ∪ d.usedTypes := by
  ext i
  simp [Constraint.usedTypes, Constraint.fvTypes,
    Constraint.boundTypes]
  aesop

theorem Constraint.usedEffects_and {X : Domain}
    (c d : Constraint X) :
    (Constraint.and c d).usedEffects = c.usedEffects ∪ d.usedEffects := by
  ext i
  simp [Constraint.usedEffects, Constraint.fvEffects,
    Constraint.boundEffects]
  aesop

private theorem usedTypes_allTy {X : Domain} (i : Nat) (c : Constraint X) :
    c.usedTypes ⊆ (Constraint.allTy i c).usedTypes := by
  intro j hj
  rcases Finset.mem_union.mp hj with hf | hb
  · by_cases hji : j = i
    · subst j
      simp [Constraint.usedTypes, Constraint.boundTypes]
    · simp [Constraint.usedTypes, Constraint.fvTypes, Constraint.boundTypes,
        Finset.mem_erase, hji, hf]
  · simp [Constraint.usedTypes, Constraint.boundTypes, hb]

/-- Renaming cannot introduce a semantically relevant free name outside the
images of names already used by the constraint. Internal binders are included
because a non-injective rename may expose them as free occurrences. -/
theorem Constraint.fvTypes_rename_subset {X : Domain}
    (hX : LawfulFVRename X) (c : Constraint X)
    (ρ η : Nat → Nat) :
    (c.rename ρ η).fvTypes ⊆ c.usedTypes.image ρ := by
  induction c with
  | top => simp [Constraint.rename, Constraint.fvTypes]
  | and c d ihc ihd =>
      intro i hi
      simp only [Constraint.rename, Constraint.fvTypes,
        Finset.mem_union] at hi
      rcases hi with hc | hd
      · rcases Finset.mem_image.mp (ihc hc) with ⟨j, hj, rfl⟩
        apply Finset.mem_image.mpr
        refine ⟨j, ?_, rfl⟩
        simp [Constraint.usedTypes, Constraint.fvTypes,
          Constraint.boundTypes] at hj ⊢
        aesop
      · rcases Finset.mem_image.mp (ihd hd) with ⟨j, hj, rfl⟩
        apply Finset.mem_image.mpr
        refine ⟨j, ?_, rfl⟩
        simp [Constraint.usedTypes, Constraint.fvTypes,
          Constraint.boundTypes] at hj ⊢
        aesop
  | typeEq a b =>
      simp [Constraint.rename, Constraint.fvTypes, Constraint.usedTypes,
        Constraint.boundTypes, Ty.fvTypes_rename, Finset.image_union]
  | effectLe ε ζ =>
      simp [Constraint.rename, Constraint.fvTypes]
  | lacks op ε =>
      simp [Constraint.rename, Constraint.fvTypes]
  | predicate p =>
      simpa [Constraint.rename, Constraint.fvTypes,
        Constraint.usedTypes, Constraint.boundTypes] using hX.types ρ η p
  | allTy i c ih =>
      intro j hj
      have hc : j ∈ (c.rename ρ η).fvTypes := by
        exact (Finset.mem_erase.mp
          (by simpa [Constraint.rename, Constraint.fvTypes] using hj)).2
      have hsub := ih hc
      rcases Finset.mem_image.mp hsub with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr
        ⟨k, usedTypes_allTy i c hk, rfl⟩
  | allEff i c ih =>
      intro j hj
      have hc : j ∈ (c.rename ρ η).fvTypes := by
        simpa [Constraint.rename, Constraint.fvTypes] using hj
      rcases Finset.mem_image.mp (ih hc) with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr
        ⟨k, by simpa [Constraint.usedTypes, Constraint.fvTypes,
          Constraint.boundTypes] using hk, rfl⟩
  | exTy i c ih =>
      intro j hj
      have hc : j ∈ (c.rename ρ η).fvTypes := by
        exact (Finset.mem_erase.mp
          (by simpa [Constraint.rename, Constraint.fvTypes] using hj)).2
      rcases Finset.mem_image.mp (ih hc) with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr
        ⟨k, usedTypes_allTy i c hk, rfl⟩
  | exEff i c ih =>
      intro j hj
      have hc : j ∈ (c.rename ρ η).fvTypes := by
        simpa [Constraint.rename, Constraint.fvTypes] using hj
      rcases Finset.mem_image.mp (ih hc) with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr
        ⟨k, by simpa [Constraint.usedTypes, Constraint.fvTypes,
          Constraint.boundTypes] using hk, rfl⟩

/-- Only collisions involving a quantified name can change the meaning of a
renamed constraint. Free names may be merged by ordinary instantiation. -/
def Constraint.RenameSafe {X : Domain} (c : Constraint X)
    (ρ η : Nat → Nat) : Prop :=
  (∀ i ∈ c.boundTypes, ∀ j ∈ c.usedTypes,
    i ≠ j → ρ i ≠ ρ j) ∧
  (∀ i ∈ c.boundEffects, ∀ j ∈ c.usedEffects,
    i ≠ j → η i ≠ η j)

private theorem usedEffects_allEff {X : Domain} (i : Nat) (c : Constraint X) :
    c.usedEffects ⊆ (Constraint.allEff i c).usedEffects := by
  intro j hj
  rcases Finset.mem_union.mp hj with hf | hb
  · by_cases hji : j = i
    · subst j
      simp [Constraint.usedEffects, Constraint.boundEffects]
    · simp [Constraint.usedEffects, Constraint.fvEffects, Constraint.boundEffects,
        Finset.mem_erase, hji, hf]
  · simp [Constraint.usedEffects, Constraint.boundEffects, hb]

theorem Constraint.fvEffects_rename_subset {X : Domain}
    (hX : LawfulFVRename X) (c : Constraint X)
    (ρ η : Nat → Nat) :
    (c.rename ρ η).fvEffects ⊆ c.usedEffects.image η := by
  induction c with
  | top => simp [Constraint.rename, Constraint.fvEffects]
  | and c d ihc ihd =>
      intro i hi
      simp only [Constraint.rename, Constraint.fvEffects,
        Finset.mem_union] at hi
      rcases hi with hc | hd
      · rcases Finset.mem_image.mp (ihc hc) with ⟨j, hj, rfl⟩
        apply Finset.mem_image.mpr
        refine ⟨j, ?_, rfl⟩
        simp [Constraint.usedEffects, Constraint.fvEffects,
          Constraint.boundEffects] at hj ⊢
        aesop
      · rcases Finset.mem_image.mp (ihd hd) with ⟨j, hj, rfl⟩
        apply Finset.mem_image.mpr
        refine ⟨j, ?_, rfl⟩
        simp [Constraint.usedEffects, Constraint.fvEffects,
          Constraint.boundEffects] at hj ⊢
        aesop
  | typeEq a b =>
      simp [Constraint.rename, Constraint.fvEffects,
        Constraint.usedEffects, Constraint.boundEffects,
        Ty.fvEffects_rename, Finset.image_union]
  | effectLe ε ζ =>
      simp [Constraint.rename, Constraint.fvEffects,
        Constraint.usedEffects, Constraint.boundEffects,
        Poly.Effect.rename, Finset.image_union]
  | lacks op ε =>
      simp [Constraint.rename, Constraint.fvEffects,
        Constraint.usedEffects, Constraint.boundEffects,
        Poly.Effect.rename]
  | predicate p =>
      simpa [Constraint.rename, Constraint.fvEffects,
        Constraint.usedEffects, Constraint.boundEffects] using hX.effects ρ η p
  | allTy i c ih =>
      intro j hj
      have hc : j ∈ (c.rename ρ η).fvEffects := by
        simpa [Constraint.rename, Constraint.fvEffects] using hj
      rcases Finset.mem_image.mp (ih hc) with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr
        ⟨k, by simpa [Constraint.usedEffects, Constraint.fvEffects,
          Constraint.boundEffects] using hk, rfl⟩
  | allEff i c ih =>
      intro j hj
      have hc : j ∈ (c.rename ρ η).fvEffects := by
        exact (Finset.mem_erase.mp
          (by simpa [Constraint.rename, Constraint.fvEffects] using hj)).2
      rcases Finset.mem_image.mp (ih hc) with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr
        ⟨k, usedEffects_allEff i c hk, rfl⟩

  | exTy i c ih =>
      intro j hj
      have hc : j ∈ (c.rename ρ η).fvEffects := by
        simpa [Constraint.rename, Constraint.fvEffects] using hj
      rcases Finset.mem_image.mp (ih hc) with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr
        ⟨k, by simpa [Constraint.usedEffects, Constraint.fvEffects,
          Constraint.boundEffects] using hk, rfl⟩
  | exEff i c ih =>
      intro j hj
      have hc : j ∈ (c.rename ρ η).fvEffects := by
        exact (Finset.mem_erase.mp
          (by simpa [Constraint.rename, Constraint.fvEffects] using hj)).2
      rcases Finset.mem_image.mp (ih hc) with ⟨k, hk, rfl⟩
      exact Finset.mem_image.mpr
        ⟨k, usedEffects_allEff i c hk, rfl⟩

theorem Constraint.boundTypes_rename {X : Domain}
    (c : Constraint X) (ρ η : Nat → Nat) :
    (c.rename ρ η).boundTypes = c.boundTypes.image ρ := by
  induction c <;>
    simp [Constraint.rename, Constraint.boundTypes, *,
      Finset.image_union, Finset.image_insert]

theorem Constraint.boundEffects_rename {X : Domain}
    (c : Constraint X) (ρ η : Nat → Nat) :
    (c.rename ρ η).boundEffects = c.boundEffects.image η := by
  induction c <;>
    simp [Constraint.rename, Constraint.boundEffects, *,
      Finset.image_union, Finset.image_insert]

theorem Constraint.usedTypes_rename_subset {X : Domain}
    (hX : LawfulFVRename X) (c : Constraint X)
    (ρ η : Nat → Nat) :
    (c.rename ρ η).usedTypes ⊆ c.usedTypes.image ρ := by
  intro i hi
  rcases Finset.mem_union.mp hi with hf | hb
  · exact c.fvTypes_rename_subset hX ρ η hf
  · rw [Constraint.boundTypes_rename] at hb
    rcases Finset.mem_image.mp hb with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_union_right _ hj, rfl⟩

theorem Constraint.usedEffects_rename_subset {X : Domain}
    (hX : LawfulFVRename X) (c : Constraint X)
    (ρ η : Nat → Nat) :
    (c.rename ρ η).usedEffects ⊆ c.usedEffects.image η := by
  intro i hi
  rcases Finset.mem_union.mp hi with hf | hb
  · exact c.fvEffects_rename_subset hX ρ η hf
  · rw [Constraint.boundEffects_rename] at hb
    rcases Finset.mem_image.mp hb with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_union_right _ hj, rfl⟩

private theorem Constraint.RenameSafe.of_sub {X : Domain}
    {c d : Constraint X} {ρ η : Nat → Nat}
    (h : c.RenameSafe ρ η)
    (hbt : d.boundTypes ⊆ c.boundTypes)
    (hbe : d.boundEffects ⊆ c.boundEffects)
    (hut : d.usedTypes ⊆ c.usedTypes)
    (hue : d.usedEffects ⊆ c.usedEffects) :
    d.RenameSafe ρ η := by
  constructor
  · intro i hi j hj hij
    exact h.1 i (hbt hi) j (hut hj) hij
  · intro i hi j hj hij
    exact h.2 i (hbe hi) j (hue hj) hij

private theorem Constraint.RenameSafe.and_left {X : Domain}
    {c d : Constraint X} {ρ η : Nat → Nat}
    (h : (Constraint.and c d).RenameSafe ρ η) :
    c.RenameSafe ρ η := by
  apply h.of_sub
  all_goals
    intro j hj
    simp only [Constraint.usedTypes, Constraint.usedEffects,
      Constraint.boundTypes, Constraint.boundEffects,
      Constraint.fvTypes, Constraint.fvEffects,
      Finset.mem_union] at hj ⊢
    aesop

private theorem Constraint.RenameSafe.and_right {X : Domain}
    {c d : Constraint X} {ρ η : Nat → Nat}
    (h : (Constraint.and c d).RenameSafe ρ η) :
    d.RenameSafe ρ η := by
  apply h.of_sub
  all_goals
    intro j hj
    simp only [Constraint.usedTypes, Constraint.usedEffects,
      Constraint.boundTypes, Constraint.boundEffects,
      Constraint.fvTypes, Constraint.fvEffects,
      Finset.mem_union] at hj ⊢
    aesop

private theorem Constraint.RenameSafe.allTy_inner {X : Domain}
    {i : Nat} {c : Constraint X} {ρ η : Nat → Nat}
    (h : (Constraint.allTy i c).RenameSafe ρ η) :
    c.RenameSafe ρ η := by
  apply h.of_sub
  · intro j hj
    simp [Constraint.boundTypes, hj]
  · intro j hj
    simpa [Constraint.boundEffects] using hj
  · exact usedTypes_allTy i c
  · intro j hj
    simpa [Constraint.usedEffects, Constraint.fvEffects,
      Constraint.boundEffects] using hj

private theorem Constraint.RenameSafe.allEff_inner {X : Domain}
    {i : Nat} {c : Constraint X} {ρ η : Nat → Nat}
    (h : (Constraint.allEff i c).RenameSafe ρ η) :
    c.RenameSafe ρ η := by
  apply h.of_sub
  · intro j hj
    simpa [Constraint.boundTypes] using hj
  · intro j hj
    simp [Constraint.boundEffects, hj]
  · intro j hj
    simpa [Constraint.usedTypes, Constraint.fvTypes,
      Constraint.boundTypes] using hj
  · exact usedEffects_allEff i c

private theorem Constraint.update_type_pullback_holds_iff {X : Domain}
    (hX : LawfulSupport X) (c : Constraint X)
    (ρ η : Nat → Nat) (i : Nat)
    (hρ : ∀ j ∈ c.fvTypes, j ≠ i → ρ j ≠ ρ i)
    (v : Valuation) (t : GroundTy) :
    c.holds ({v with types := Function.update v.types (ρ i) t}.pullback ρ η) ↔
      c.holds ⟨Function.update (v.types ∘ ρ) i t,
        v.effects ∘ η⟩ := by
  apply Constraint.holds_support hX
  · intro j hj
    by_cases hji : j = i
    · subst j
      simp [Valuation.pullback, Function.update]
    · have hne := hρ j hj hji
      simp [Valuation.pullback, Function.update, hji, hne]
  · intro j _
    rfl

private theorem Constraint.update_effect_pullback_holds_iff {X : Domain}
    (hX : LawfulSupport X) (c : Constraint X)
    (ρ η : Nat → Nat) (i : Nat)
    (hη : ∀ j ∈ c.fvEffects, j ≠ i → η j ≠ η i)
    (v : Valuation) (ε : Finset Op) :
    c.holds ({v with effects := Function.update v.effects (η i) ε}.pullback ρ η) ↔
      c.holds ⟨v.types ∘ ρ,
        Function.update (v.effects ∘ η) i ε⟩ := by
  apply Constraint.holds_support hX
  · intro j _
    rfl
  · intro j hj
    by_cases hji : j = i
    · subst j
      simp [Valuation.pullback, Function.update]
    · have hne := hη j hj hji
      simp [Valuation.pullback, Function.update, hji, hne]

/-- The form needed for fresh instantiation: injectivity is required only
between a quantified name and names occurring in this finite constraint. -/
theorem Constraint.holds_rename_safe {X : Domain}
    (hRename : LawfulRename X) (hSupport : LawfulSupport X)
    (c : Constraint X) (ρ η : Nat → Nat) (v : Valuation)
    (hsafe : c.RenameSafe ρ η) :
    (c.rename ρ η).holds v ↔ c.holds (v.pullback ρ η) := by
  revert hsafe
  induction c generalizing v with
  | top => intro _; rfl
  | and c d ihc ihd =>
      intro hsafe
      simp [Constraint.rename, Constraint.holds,
        ihc v hsafe.and_left, ihd v hsafe.and_right]
  | typeEq a b =>
      intro _
      simp [Constraint.rename, Constraint.holds, Ty.eval_rename]
  | effectLe ε ζ =>
      intro _
      simp [Constraint.rename, Constraint.holds, Effect.eval_rename,
        Valuation.pullback]
  | lacks op ε =>
      intro _
      simp [Constraint.rename, Constraint.holds, Effect.eval_rename,
        Valuation.pullback]
  | predicate p =>
      intro _
      exact hRename.holds_rename ρ η p v
  | allTy i c ih =>
      intro hsafe
      have hs := hsafe.allTy_inner
      have hcoll : ∀ j ∈ c.fvTypes, j ≠ i → ρ j ≠ ρ i := by
        intro j hj hji
        exact hsafe.1 i (by simp [Constraint.boundTypes]) j
          (usedTypes_allTy i c (Finset.mem_union_left _ hj))
          (Ne.symm hji) |>.symm
      simp only [Constraint.rename, Constraint.holds]
      constructor <;> intro h t
      · have hc := (ih _ hs).mp (h t)
        have heq := (Constraint.update_type_pullback_holds_iff
          hSupport c ρ η i hcoll v t).mp hc
        simpa [Valuation.pullback] using heq
      · apply (ih _ hs).mpr
        apply (Constraint.update_type_pullback_holds_iff
          hSupport c ρ η i hcoll v t).mpr
        simpa [Valuation.pullback] using h t
  | allEff i c ih =>
      intro hsafe
      have hs := hsafe.allEff_inner
      have hcoll : ∀ j ∈ c.fvEffects, j ≠ i → η j ≠ η i := by
        intro j hj hji
        exact hsafe.2 i (by simp [Constraint.boundEffects]) j
          (usedEffects_allEff i c (Finset.mem_union_left _ hj))
          (Ne.symm hji) |>.symm
      simp only [Constraint.rename, Constraint.holds]
      constructor <;> intro h ε
      · have hc := (ih _ hs).mp (h ε)
        have heq := (Constraint.update_effect_pullback_holds_iff
          hSupport c ρ η i hcoll v ε).mp hc
        simpa [Valuation.pullback] using heq
      · apply (ih _ hs).mpr
        apply (Constraint.update_effect_pullback_holds_iff
          hSupport c ρ η i hcoll v ε).mpr
        simpa [Valuation.pullback] using h ε
  | exTy i c ih =>
      intro hsafe
      have hs : c.RenameSafe ρ η := by
        apply Constraint.RenameSafe.allTy_inner
        exact hsafe
      have hcoll : ∀ j ∈ c.fvTypes, j ≠ i → ρ j ≠ ρ i := by
        intro j hj hji
        exact hsafe.1 i (by simp [Constraint.boundTypes]) j
          (usedTypes_allTy i c (Finset.mem_union_left _ hj))
          (Ne.symm hji) |>.symm
      simp only [Constraint.rename, Constraint.holds]
      constructor
      · rintro ⟨t, h⟩
        refine ⟨t, ?_⟩
        have hc := (ih _ hs).mp h
        have heq := (Constraint.update_type_pullback_holds_iff
          hSupport c ρ η i hcoll v t).mp hc
        simpa [Valuation.pullback] using heq
      · rintro ⟨t, h⟩
        refine ⟨t, (ih _ hs).mpr ?_⟩
        apply (Constraint.update_type_pullback_holds_iff
          hSupport c ρ η i hcoll v t).mpr
        simpa [Valuation.pullback] using h
  | exEff i c ih =>
      intro hsafe
      have hs : c.RenameSafe ρ η := by
        apply Constraint.RenameSafe.allEff_inner
        exact hsafe
      have hcoll : ∀ j ∈ c.fvEffects, j ≠ i → η j ≠ η i := by
        intro j hj hji
        exact hsafe.2 i (by simp [Constraint.boundEffects]) j
          (usedEffects_allEff i c (Finset.mem_union_left _ hj))
          (Ne.symm hji) |>.symm
      simp only [Constraint.rename, Constraint.holds]
      constructor
      · rintro ⟨ε, h⟩
        refine ⟨ε, ?_⟩
        have hc := (ih _ hs).mp h
        have heq := (Constraint.update_effect_pullback_holds_iff
          hSupport c ρ η i hcoll v ε).mp hc
        simpa [Valuation.pullback] using heq
      · rintro ⟨ε, h⟩
        refine ⟨ε, (ih _ hs).mpr ?_⟩
        apply (Constraint.update_effect_pullback_holds_iff
          hSupport c ρ η i hcoll v ε).mpr
        simpa [Valuation.pullback] using h

theorem Effect.eval_union (ρ : Nat → Finset Op) (ε η : Effect) :
    (ε ∪ η).eval ρ = ε.eval ρ ∪ η.eval ρ := by
  ext op
  simp only [Poly.Effect.eval, Poly.Effect.labels_union, Poly.Effect.vars_union,
    Finset.mem_union, Finset.mem_biUnion]
  aesop

private theorem eval_singleton (ρ : Nat → Finset Op) (op : Op) :
    (Poly.Effect.singleton op).eval ρ = {op} := by
  simp [Poly.Effect.eval, Poly.Effect.singleton]

/-- The three primitive constraints characterize exact removal of one operation. -/
theorem Constraint.split_iff {X : Domain} (ρ : Valuation)
    (op : Op) (ε δ : Effect) :
    (Constraint.split (X := X) op ε δ).holds ρ ↔
      δ.eval ρ.effects = ε.eval ρ.effects \ {op} := by
  rw [Constraint.split]
  change (δ.eval ρ.effects ⊆ ε.eval ρ.effects ∧
      ε.eval ρ.effects ⊆ (Poly.Effect.singleton op ∪ δ).eval ρ.effects ∧
      op ∉ δ.eval ρ.effects) ↔ _
  rw [Effect.eval_union, eval_singleton]
  constructor
  · rintro ⟨hde, hed, hnot⟩
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨hde hx, by
        intro heq
        subst x
        exact hnot hx⟩
    · rintro ⟨hx, hneq⟩
      rcases Finset.mem_union.mp (hed hx) with hop | hδ
      · exact False.elim (hneq (Finset.mem_singleton.mp hop))
      · exact hδ
  · intro heq
    constructor
    · intro x hx
      rw [heq] at hx
      exact (Finset.mem_sdiff.mp hx).1
    constructor
    · intro x hx
      by_cases hxo : x = op
      · subst x
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self op))
      · apply Finset.mem_union.mpr
        right
        rw [heq]
        exact Finset.mem_sdiff.mpr ⟨hx, by simpa using hxo⟩
    · intro hop
      rw [heq] at hop
      exact (Finset.mem_sdiff.mp hop).2 (Finset.mem_singleton_self op)

/-- Closing a clause constraint over a rigid type variable still implies its
instance at the current valuation. -/
theorem Constraint.allTy_current {X : Domain} (i : Nat) (c : Constraint X) :
    (Constraint.allTy i c).Entails c := by
  intro ρ h
  have hi := h (ρ.types i)
  simpa [Constraint.holds] using hi

theorem Constraint.allEff_current {X : Domain} (i : Nat) (c : Constraint X) :
    (Constraint.allEff i c).Entails c := by
  intro ρ h
  have hi := h (ρ.effects i)
  simpa [Constraint.holds] using hi

def Constraint.closeTypes {X : Domain} (vars : List Nat) (c : Constraint X) :
    Constraint X := vars.foldr Constraint.allTy c

def Constraint.closeEffects {X : Domain} (vars : List Nat) (c : Constraint X) :
    Constraint X := vars.foldr Constraint.allEff c

def Constraint.close {X : Domain} (types effects : Finset Nat)
    (c : Constraint X) : Constraint X :=
  Constraint.closeTypes (types.sort (· ≤ ·))
    (Constraint.closeEffects (effects.sort (· ≤ ·)) c)

theorem Constraint.usedTypes_allTy_eq {X : Domain}
    (i : Nat) (c : Constraint X) :
    (Constraint.allTy i c).usedTypes = insert i c.usedTypes := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [Constraint.usedTypes, Constraint.boundTypes]
  · simp [Constraint.usedTypes, Constraint.fvTypes,
      Constraint.boundTypes, Finset.mem_erase, hji]

theorem Constraint.usedEffects_allEff_eq {X : Domain}
    (i : Nat) (c : Constraint X) :
    (Constraint.allEff i c).usedEffects =
      insert i c.usedEffects := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [Constraint.usedEffects, Constraint.boundEffects]
  · simp [Constraint.usedEffects, Constraint.fvEffects,
      Constraint.boundEffects, Finset.mem_erase, hji]

theorem Constraint.usedTypes_allEff_eq {X : Domain}
    (i : Nat) (c : Constraint X) :
    (Constraint.allEff i c).usedTypes = c.usedTypes := rfl

theorem Constraint.usedEffects_allTy_eq {X : Domain}
    (i : Nat) (c : Constraint X) :
    (Constraint.allTy i c).usedEffects = c.usedEffects := rfl

theorem Constraint.closeTypes_usedTypes {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.closeTypes vars c).usedTypes =
      c.usedTypes ∪ vars.toFinset := by
  induction vars with
  | nil => simp [Constraint.closeTypes]
  | cons i rest ih =>
      change (Constraint.allTy i
        (Constraint.closeTypes rest c)).usedTypes = _
      rw [Constraint.usedTypes_allTy_eq, ih]
      ext j
      simp [List.toFinset_cons]

theorem Constraint.closeEffects_usedEffects {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.closeEffects vars c).usedEffects =
      c.usedEffects ∪ vars.toFinset := by
  induction vars with
  | nil => simp [Constraint.closeEffects]
  | cons i rest ih =>
      change (Constraint.allEff i
        (Constraint.closeEffects rest c)).usedEffects = _
      rw [Constraint.usedEffects_allEff_eq, ih]
      ext j
      simp [List.toFinset_cons]

theorem Constraint.closeTypes_usedEffects {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.closeTypes vars c).usedEffects =
      c.usedEffects := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      simpa [Constraint.closeTypes,
        Constraint.usedEffects_allTy_eq] using ih

theorem Constraint.closeEffects_usedTypes {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.closeEffects vars c).usedTypes =
      c.usedTypes := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      simpa [Constraint.closeEffects,
        Constraint.usedTypes_allEff_eq] using ih

theorem Constraint.close_usedTypes {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) :
    (Constraint.close types effects c).usedTypes =
      c.usedTypes ∪ types := by
  simp [Constraint.close, Constraint.closeTypes_usedTypes,
    Constraint.closeEffects_usedTypes]

theorem Constraint.close_usedEffects {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) :
    (Constraint.close types effects c).usedEffects =
      c.usedEffects ∪ effects := by
  simp [Constraint.close, Constraint.closeTypes_usedEffects,
    Constraint.closeEffects_usedEffects]

/-- Existentially hide only the names generated while checking a clause. -/
def Constraint.projectTypes {X : Domain} (vars : List Nat) (c : Constraint X) :
    Constraint X := vars.foldr Constraint.exTy c

def Constraint.projectEffects {X : Domain} (vars : List Nat) (c : Constraint X) :
    Constraint X := vars.foldr Constraint.exEff c

def Constraint.project {X : Domain} (types effects : Finset Nat)
    (c : Constraint X) : Constraint X :=
  Constraint.projectTypes (types.sort (· ≤ ·))
    (Constraint.projectEffects (effects.sort (· ≤ ·)) c)

theorem Constraint.projectTypes_usedTypes_subset {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.projectTypes vars c).usedTypes ⊆
      c.usedTypes ∪ vars.toFinset := by
  induction vars with
  | nil => simp [Constraint.projectTypes]
  | cons i rest ih =>
      intro j hj
      change j ∈ (Constraint.exTy i
        (Constraint.projectTypes rest c)).usedTypes at hj
      simp only [Constraint.usedTypes, Constraint.fvTypes,
        Constraint.boundTypes, Finset.mem_union] at hj
      simp only [List.toFinset_cons, Finset.mem_union,
        Finset.mem_insert]
      rcases hj with hf | hbound
      · have hinner : j ∈ (Constraint.projectTypes rest c).usedTypes :=
          Finset.mem_union_left _ (Finset.mem_erase.mp hf).2
        rcases Finset.mem_union.mp (ih hinner) with hc | hr
        · exact Or.inl hc
        · exact Or.inr (Or.inr hr)
      · rcases Finset.mem_insert.mp hbound with rfl | hinner
        · exact Or.inr (Or.inl rfl)
        · have hused : j ∈ (Constraint.projectTypes rest c).usedTypes :=
            Finset.mem_union_right _ hinner
          rcases Finset.mem_union.mp (ih hused) with hc | hr
          · exact Or.inl hc
          · exact Or.inr (Or.inr hr)

theorem Constraint.projectEffects_usedEffects_subset {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.projectEffects vars c).usedEffects ⊆
      c.usedEffects ∪ vars.toFinset := by
  induction vars with
  | nil => simp [Constraint.projectEffects]
  | cons i rest ih =>
      intro j hj
      change j ∈ (Constraint.exEff i
        (Constraint.projectEffects rest c)).usedEffects at hj
      simp only [Constraint.usedEffects, Constraint.fvEffects,
        Constraint.boundEffects, Finset.mem_union] at hj
      simp only [List.toFinset_cons, Finset.mem_union,
        Finset.mem_insert]
      rcases hj with hf | hbound
      · have hinner : j ∈ (Constraint.projectEffects rest c).usedEffects :=
          Finset.mem_union_left _ (Finset.mem_erase.mp hf).2
        rcases Finset.mem_union.mp (ih hinner) with hc | hr
        · exact Or.inl hc
        · exact Or.inr (Or.inr hr)
      · rcases Finset.mem_insert.mp hbound with rfl | hinner
        · exact Or.inr (Or.inl rfl)
        · have hused : j ∈ (Constraint.projectEffects rest c).usedEffects :=
            Finset.mem_union_right _ hinner
          rcases Finset.mem_union.mp (ih hused) with hc | hr
          · exact Or.inl hc
          · exact Or.inr (Or.inr hr)

theorem Constraint.projectTypes_usedEffects {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.projectTypes vars c).usedEffects = c.usedEffects := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      simpa [Constraint.projectTypes, Constraint.usedEffects,
        Constraint.fvEffects, Constraint.boundEffects] using ih

theorem Constraint.projectEffects_usedTypes {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.projectEffects vars c).usedTypes = c.usedTypes := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      simpa [Constraint.projectEffects, Constraint.usedTypes,
        Constraint.fvTypes, Constraint.boundTypes] using ih

theorem Constraint.project_usedTypes_subset {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) :
    (Constraint.project types effects c).usedTypes ⊆
      c.usedTypes ∪ types := by
  simpa [Constraint.project, Constraint.projectEffects_usedTypes] using
    (Constraint.projectTypes_usedTypes_subset
      (types.sort (· ≤ ·))
      (Constraint.projectEffects (effects.sort (· ≤ ·)) c))

theorem Constraint.project_usedEffects_subset {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) :
    (Constraint.project types effects c).usedEffects ⊆
      c.usedEffects ∪ effects := by
  intro i hi
  rw [Constraint.project, Constraint.projectTypes_usedEffects] at hi
  simpa using (Constraint.projectEffects_usedEffects_subset
    (effects.sort (· ≤ ·)) c) hi

/-- HM(X)'s residual obligation after generalizing a value. -/
def Scheme.residual {X : Domain} (Γ : Context X)
    (c : Constraint X) (τ : Ty) : Constraint X :=
  let σ := Scheme.generalize Γ c τ
  Constraint.project σ.typeVars σ.effectVars c

theorem Constraint.projectTypes_fvTypes {X : Domain} (vars : List Nat)
    (c : Constraint X) :
    (Constraint.projectTypes vars c).fvTypes = c.fvTypes \ vars.toFinset := by
  induction vars with
  | nil => simp [Constraint.projectTypes]
  | cons i rest ih =>
      change (Constraint.projectTypes rest c).fvTypes.erase i = _
      rw [ih]
      ext j
      simp [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_erase,
        and_left_comm]

theorem Constraint.projectEffects_fvEffects {X : Domain} (vars : List Nat)
    (c : Constraint X) :
    (Constraint.projectEffects vars c).fvEffects =
      c.fvEffects \ vars.toFinset := by
  induction vars with
  | nil => simp [Constraint.projectEffects]
  | cons i rest ih =>
      change (Constraint.projectEffects rest c).fvEffects.erase i = _
      rw [ih]
      ext j
      simp [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_erase,
        and_left_comm]

theorem Constraint.projectTypes_fvEffects {X : Domain} (vars : List Nat)
    (c : Constraint X) :
    (Constraint.projectTypes vars c).fvEffects = c.fvEffects := by
  induction vars with
  | nil => rfl
  | cons i rest ih => simpa [Constraint.projectTypes, Constraint.fvEffects] using ih

theorem Constraint.projectEffects_fvTypes {X : Domain} (vars : List Nat)
    (c : Constraint X) :
    (Constraint.projectEffects vars c).fvTypes = c.fvTypes := by
  induction vars with
  | nil => rfl
  | cons i rest ih => simpa [Constraint.projectEffects, Constraint.fvTypes] using ih

theorem Constraint.project_fvTypes {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) :
    (Constraint.project types effects c).fvTypes = c.fvTypes \ types := by
  simp [Constraint.project, Constraint.projectTypes_fvTypes,
    Constraint.projectEffects_fvTypes]

theorem Constraint.project_fvEffects {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) :
    (Constraint.project types effects c).fvEffects =
      c.fvEffects \ effects := by
  simp [Constraint.project, Constraint.projectTypes_fvEffects,
    Constraint.projectEffects_fvEffects]

/-- The residual contains no free names outside the environment. -/
theorem Scheme.residual_fv_context {X : Domain} (Γ : Context X)
    (c : Constraint X) (τ : Ty) :
    (Scheme.residual Γ c τ).fvTypes ⊆ Γ.fvTypes ∧
      (Scheme.residual Γ c τ).fvEffects ⊆ Γ.fvEffects := by
  constructor
  · intro i hi
    rw [Scheme.residual, Constraint.project_fvTypes] at hi
    simp [Scheme.generalize] at hi
    exact hi.2 (Or.inr hi.1)
  · intro i hi
    rw [Scheme.residual, Constraint.project_fvEffects] at hi
    simp [Scheme.generalize] at hi
    exact hi.2 (Or.inr hi.1)

theorem Constraint.exTy_current {X : Domain} (i : Nat) (c : Constraint X) :
    c.Entails (.exTy i c) := by
  intro ρ h
  exact ⟨ρ.types i, by simpa [Constraint.holds] using h⟩

theorem Constraint.exEff_current {X : Domain} (i : Nat) (c : Constraint X) :
    c.Entails (.exEff i c) := by
  intro ρ h
  exact ⟨ρ.effects i, by simpa [Constraint.holds] using h⟩

theorem Constraint.projectTypes_current {X : Domain} (vars : List Nat)
    (c : Constraint X) : c.Entails (Constraint.projectTypes vars c) := by
  induction vars with
  | nil => exact Constraint.entails_refl c
  | cons i rest ih =>
      exact Constraint.entails_trans ih
        (Constraint.exTy_current i (Constraint.projectTypes rest c))

theorem Constraint.projectEffects_current {X : Domain} (vars : List Nat)
    (c : Constraint X) : c.Entails (Constraint.projectEffects vars c) := by
  induction vars with
  | nil => exact Constraint.entails_refl c
  | cons i rest ih =>
      exact Constraint.entails_trans ih
        (Constraint.exEff_current i (Constraint.projectEffects rest c))

theorem Constraint.project_current {X : Domain} (types effects : Finset Nat)
    (c : Constraint X) : c.Entails (Constraint.project types effects c) := by
  exact Constraint.entails_trans
    (Constraint.projectEffects_current (effects.sort (· ≤ ·)) c)
    (Constraint.projectTypes_current (types.sort (· ≤ ·)) _)

/-- Projection is exactly existential choice of values at its bound names. -/
theorem Constraint.projectTypes_holds_iff {X : Domain} (vars : List Nat)
    (c : Constraint X) (ρ : Valuation) :
    (Constraint.projectTypes vars c).holds ρ ↔
      ∃ f : Nat → GroundTy,
        (∀ i, i ∉ vars → f i = ρ.types i) ∧
        c.holds {ρ with types := f} := by
  induction vars generalizing ρ with
  | nil =>
      constructor
      · intro h
        exact ⟨ρ.types, by simp, h⟩
      · rintro ⟨f, hf, h⟩
        have heq : f = ρ.types := funext (fun i => hf i (by simp))
        simpa [heq, Constraint.projectTypes] using h
  | cons i rest ih =>
      constructor
      · rintro ⟨t, h⟩
        rcases (ih {ρ with types := Function.update ρ.types i t}).mp h with
          ⟨f, hf, hc⟩
        refine ⟨f, ?_, hc⟩
        intro j hj
        simp only [List.mem_cons, not_or] at hj
        have hji : j ≠ i := hj.1
        have hjr : j ∉ rest := hj.2
        simpa [Function.update, hji] using hf j hjr
      · rintro ⟨f, hf, hc⟩
        refine ⟨f i, (ih {ρ with types := Function.update ρ.types i (f i)}).mpr ?_⟩
        refine ⟨f, ?_, hc⟩
        intro j hjr
        by_cases hji : j = i
        · subst j; simp
        · have hj : j ∉ i :: rest := by simp [hji, hjr]
          simpa [Function.update, hji] using hf j hj

theorem Constraint.projectEffects_holds_iff {X : Domain} (vars : List Nat)
    (c : Constraint X) (ρ : Valuation) :
    (Constraint.projectEffects vars c).holds ρ ↔
      ∃ f : Nat → Finset Op,
        (∀ i, i ∉ vars → f i = ρ.effects i) ∧
        c.holds {ρ with effects := f} := by
  induction vars generalizing ρ with
  | nil =>
      constructor
      · intro h
        exact ⟨ρ.effects, by simp, h⟩
      · rintro ⟨f, hf, h⟩
        have heq : f = ρ.effects := funext (fun i => hf i (by simp))
        simpa [heq, Constraint.projectEffects] using h
  | cons i rest ih =>
      constructor
      · rintro ⟨ε, h⟩
        rcases (ih {ρ with effects := Function.update ρ.effects i ε}).mp h with
          ⟨f, hf, hc⟩
        refine ⟨f, ?_, hc⟩
        intro j hj
        simp only [List.mem_cons, not_or] at hj
        have hji : j ≠ i := hj.1
        have hjr : j ∉ rest := hj.2
        simpa [Function.update, hji] using hf j hjr
      · rintro ⟨f, hf, hc⟩
        refine ⟨f i, (ih {ρ with effects := Function.update ρ.effects i (f i)}).mpr ?_⟩
        refine ⟨f, ?_, hc⟩
        intro j hjr
        by_cases hji : j = i
        · subst j; simp
        · have hj : j ∉ i :: rest := by simp [hji, hjr]
          simpa [Function.update, hji] using hf j hj

theorem Constraint.project_holds_iff {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) (ρ : Valuation) :
    (Constraint.project types effects c).holds ρ ↔
      ∃ ft : Nat → GroundTy, ∃ fe : Nat → Finset Op,
        (∀ i, i ∉ types → ft i = ρ.types i) ∧
        (∀ i, i ∉ effects → fe i = ρ.effects i) ∧
        c.holds ⟨ft, fe⟩ := by
  unfold Constraint.project
  rw [Constraint.projectTypes_holds_iff]
  constructor
  · rintro ⟨ft, hft, hproject⟩
    rcases (Constraint.projectEffects_holds_iff
      (effects.sort (· ≤ ·)) c {ρ with types := ft}).mp hproject with
      ⟨fe, hfe, hc⟩
    refine ⟨ft, fe, ?_, ?_, hc⟩
    · intro i hi
      exact hft i (by simpa using hi)
    · intro i hi
      exact hfe i (by simpa using hi)

  · rintro ⟨ft, fe, hft, hfe, hc⟩
    refine ⟨ft, ?_, ?_⟩
    · intro i hi
      exact hft i (by simpa using hi)
    · apply (Constraint.projectEffects_holds_iff
        (effects.sort (· ≤ ·)) c {ρ with types := ft}).mpr
      refine ⟨fe, ?_, hc⟩
      intro i hi
      exact hfe i (by simpa using hi)

theorem Constraint.project_mono {X : Domain}
    (types effects : Finset Nat) {c d : Constraint X}
    (h : c.Entails d) :
    (Constraint.project types effects c).Entails
      (Constraint.project types effects d) := by
  intro ρ hc
  rcases (Constraint.project_holds_iff types effects c ρ).mp hc with
    ⟨ft, fe, hft, hfe, hc'⟩
  apply (Constraint.project_holds_iff types effects d ρ).mpr
  exact ⟨ft, fe, hft, hfe, h ⟨ft, fe⟩ hc'⟩

/-- The residual left by HM(X) generalization says that the value's
constraint has a witness for its generalized type and effect variables. -/
theorem Scheme.residual_holds_iff {X : Domain} (Γ : Context X)
    (c : Constraint X) (τ : Ty) (ρ : Valuation) :
    (Scheme.residual Γ c τ).holds ρ ↔
      ∃ ft : Nat → GroundTy, ∃ fe : Nat → Finset Op,
        (∀ i, i ∉ (Scheme.generalize Γ c τ).typeVars →
          ft i = ρ.types i) ∧
        (∀ i, i ∉ (Scheme.generalize Γ c τ).effectVars →
          fe i = ρ.effects i) ∧
        c.holds ⟨ft, fe⟩ := by
  exact Constraint.project_holds_iff _ _ c ρ

theorem Scheme.residual_current {X : Domain} (Γ : Context X)
    (c : Constraint X) (τ : Ty) :
    c.Entails (Scheme.residual Γ c τ) := by
  exact Constraint.project_current _ _ c

theorem Constraint.closeTypes_holds_iff {X : Domain} (vars : List Nat)
    (c : Constraint X) (ρ : Valuation) :
    (Constraint.closeTypes vars c).holds ρ ↔
      ∀ f : Nat → GroundTy,
        (∀ i, i ∉ vars → f i = ρ.types i) →
        c.holds {ρ with types := f} := by
  induction vars generalizing ρ with
  | nil =>
      constructor
      · intro h f hf
        have heq : f = ρ.types := funext (fun i => hf i (by simp))
        simpa [heq, Constraint.closeTypes] using h
      · intro h
        exact h ρ.types (by simp)
  | cons i rest ih =>
      constructor
      · intro h f hf
        have hrest : (Constraint.closeTypes rest c).holds
            {ρ with types := Function.update ρ.types i (f i)} := h (f i)
        apply (ih {ρ with types := Function.update ρ.types i (f i)}).mp hrest f
        intro j hjr
        by_cases hji : j = i
        · subst j; simp
        · have hj : j ∉ i :: rest := by simp [hji, hjr]
          simpa [Function.update, hji] using hf j hj
      · intro h t
        apply (ih {ρ with types := Function.update ρ.types i t}).mpr
        intro f hf
        apply h f
        intro j hj
        simp only [List.mem_cons, not_or] at hj
        have hji : j ≠ i := hj.1
        have hjr : j ∉ rest := hj.2
        simpa [Function.update, hji] using hf j hjr

theorem Constraint.closeEffects_holds_iff {X : Domain} (vars : List Nat)
    (c : Constraint X) (ρ : Valuation) :
    (Constraint.closeEffects vars c).holds ρ ↔
      ∀ f : Nat → Finset Op,
        (∀ i, i ∉ vars → f i = ρ.effects i) →
        c.holds {ρ with effects := f} := by
  induction vars generalizing ρ with
  | nil =>
      constructor
      · intro h f hf
        have heq : f = ρ.effects := funext (fun i => hf i (by simp))
        simpa [heq, Constraint.closeEffects] using h
      · intro h
        exact h ρ.effects (by simp)
  | cons i rest ih =>
      constructor
      · intro h f hf
        have hrest : (Constraint.closeEffects rest c).holds
            {ρ with effects := Function.update ρ.effects i (f i)} := h (f i)
        apply (ih {ρ with effects := Function.update ρ.effects i (f i)}).mp hrest f
        intro j hjr
        by_cases hji : j = i
        · subst j; simp
        · have hj : j ∉ i :: rest := by simp [hji, hjr]
          simpa [Function.update, hji] using hf j hj
      · intro h ε
        apply (ih {ρ with effects := Function.update ρ.effects i ε}).mpr
        intro f hf
        apply h f
        intro j hj
        simp only [List.mem_cons, not_or] at hj
        have hji : j ≠ i := hj.1
        have hjr : j ∉ rest := hj.2
        simpa [Function.update, hji] using hf j hjr

theorem Constraint.close_holds_iff {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) (ρ : Valuation) :
    (Constraint.close types effects c).holds ρ ↔
      ∀ ft : Nat → GroundTy, ∀ fe : Nat → Finset Op,
        (∀ i, i ∉ types → ft i = ρ.types i) →
        (∀ i, i ∉ effects → fe i = ρ.effects i) →
        c.holds ⟨ft, fe⟩ := by
  unfold Constraint.close
  rw [Constraint.closeTypes_holds_iff]
  constructor
  · intro h ft fe hft hfe
    have hproject := h ft (by intro i hi; exact hft i (by simpa using hi))
    exact (Constraint.closeEffects_holds_iff
      (effects.sort (· ≤ ·)) c {ρ with types := ft}).mp hproject fe
      (by intro i hi; exact hfe i (by simpa using hi))
  · intro h ft hft
    apply (Constraint.closeEffects_holds_iff
      (effects.sort (· ≤ ·)) c {ρ with types := ft}).mpr
    intro fe hfe
    exact h ft fe
      (by intro i hi; exact hft i (by simpa using hi))
      (by intro i hi; exact hfe i (by simpa using hi))

theorem Constraint.close_mono {X : Domain}
    (types effects : Finset Nat) {c d : Constraint X}
    (h : c.Entails d) :
    (Constraint.close types effects c).Entails
      (Constraint.close types effects d) := by
  intro ρ hc
  apply (Constraint.close_holds_iff types effects d ρ).mpr
  intro ft fe hft hfe
  exact h ⟨ft, fe⟩
    ((Constraint.close_holds_iff types effects c ρ).mp hc
      ft fe hft hfe)

/-- The exact `∀ operation variables. ∃ clause-local variables` order used
by the handler rule. -/
theorem Constraint.close_project_holds_iff {X : Domain}
    (boundTypes boundEffects localTypes localEffects : Finset Nat)
    (c : Constraint X) (ρ : Valuation) :
    (Constraint.close boundTypes boundEffects
      (Constraint.project localTypes localEffects c)).holds ρ ↔
    ∀ bt : Nat → GroundTy, ∀ be : Nat → Finset Op,
      (∀ i, i ∉ boundTypes → bt i = ρ.types i) →
      (∀ i, i ∉ boundEffects → be i = ρ.effects i) →
      ∃ lt : Nat → GroundTy, ∃ le : Nat → Finset Op,
        (∀ i, i ∉ localTypes → lt i = bt i) ∧
        (∀ i, i ∉ localEffects → le i = be i) ∧
        c.holds ⟨lt, le⟩ := by
  rw [Constraint.close_holds_iff]
  simp only [Constraint.project_holds_iff]

theorem Constraint.closeTypes_current {X : Domain} (vars : List Nat)
    (c : Constraint X) : (Constraint.closeTypes vars c).Entails c := by
  induction vars with
  | nil => exact Constraint.entails_refl c
  | cons i rest ih =>
      exact Constraint.entails_trans (Constraint.allTy_current i _ ) ih

theorem Constraint.closeEffects_current {X : Domain} (vars : List Nat)
    (c : Constraint X) : (Constraint.closeEffects vars c).Entails c := by
  induction vars with
  | nil => exact Constraint.entails_refl c
  | cons i rest ih =>
      exact Constraint.entails_trans (Constraint.allEff_current i _) ih

theorem Constraint.close_current {X : Domain} (types effects : Finset Nat)
    (c : Constraint X) : (Constraint.close types effects c).Entails c := by
  exact Constraint.entails_trans
    (Constraint.closeTypes_current (types.sort (· ≤ ·)) _)
    (Constraint.closeEffects_current (effects.sort (· ≤ ·)) c)

/-- A rigid operation type variable cannot equal an independent fixed type
variable at every instantiation. -/
theorem Constraint.rigid_var_eq_unsat {X : Domain} (i j : Nat)
    (hij : i ≠ j) (ρ : Valuation) :
    ¬ (Constraint.allTy (X := X) i (.typeEq (.var i) (.var j))).holds ρ := by
  intro h
  have h0 := h (.atom 0)
  have h1 := h (.atom 1)
  have hji : j ≠ i := Ne.symm hij
  simp [Constraint.holds, Ty.eval, hji] at h0 h1
  have h01 := h0.trans h1.symm
  cases h01

end SystemFXi.EHMX
