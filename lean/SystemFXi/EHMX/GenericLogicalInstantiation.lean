import SystemFXi.EHMX.GenericInference
import Mathlib.Data.Finset.Sort

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

theorem Scheme.renameBound_fresh {X : ConstraintSystem} (σ : Scheme X)
    (typeBase effectBase : Nat)
    (ht : ∀ i ∈ σ.typeVars, i < typeBase)
    (he : ∀ i ∈ σ.effectVars, i < effectBase) :
    σ.FreshRename (renameBound σ.typeVars typeBase)
      (renameBound σ.effectVars effectBase) := by
  constructor
  · intro i hi hmem
    have hlt := ht _ hmem
    simp [renameBound, hi] at hlt
    omega
  · intro i hi hmem
    have hlt := he _ hmem
    simp [renameBound, hi] at hlt
    omega

theorem typeLinks_iff (X : ConstraintSystem) (names : List Nat)
    (fresh : Nat → Nat) (v : Valuation) :
    X.holds (typeLinks X names fresh) v ↔
      ∀ i ∈ names, v.types i = v.types (fresh i) := by
  induction names with
  | nil => simp [typeLinks, X.trivial_iff]
  | cons i rest ih =>
      change X.holds (X.combine (X.equalType (.var i) (.var (fresh i)))
        (typeLinks X rest fresh)) v ↔ ∀ j ∈ i :: rest,
          v.types j = v.types (fresh j)
      rw [X.combine_iff, X.equalType_iff, ih]
      simp only [Ty.eval, List.mem_cons]
      constructor
      · rintro ⟨hi, hr⟩ j hj
        rcases hj with rfl | hj
        · exact hi
        · exact hr j hj
      · intro h
        exact ⟨h i (by simp), fun j hj => h j (by simp [hj])⟩

theorem effectLinks_iff (X : ConstraintSystem) (names : List Nat)
    (fresh : Nat → Nat) (v : Valuation) :
    X.holds (effectLinks X names fresh) v ↔
      ∀ i ∈ names, v.effects i = v.effects (fresh i) := by
  induction names with
  | nil => simp [effectLinks, X.trivial_iff]
  | cons i rest ih =>
      change X.holds (X.combine
        (X.equalEffect (Poly.Effect.var i) (Poly.Effect.var (fresh i)))
        (effectLinks X rest fresh)) v ↔ ∀ j ∈ i :: rest,
          v.effects j = v.effects (fresh j)
      rw [X.combine_iff, X.equalEffect_iff, ih]
      simp only [Poly.Effect.eval, Poly.Effect.var, Finset.singleton_biUnion,
        Finset.empty_union, List.mem_cons]
      constructor
      · rintro ⟨hi, hr⟩ j hj
        rcases hj with rfl | hj
        · exact hi
        · exact hr j hj
      · intro h
        exact ⟨h i (by simp), fun j hj => h j (by simp [hj])⟩

/-- The projected instantiation has precisely the witnesses expected by the
qualified scheme. Fresh names must lie outside the quantified old names. -/
theorem Scheme.instantiateProjected_iff {X : ConstraintSystem}
    (σ : Scheme X) (ft fe : Nat → Nat) (v : Valuation)
    (hfreshT : ∀ i ∈ σ.typeVars, ft i ∉ σ.typeVars)
    (hfreshE : ∀ i ∈ σ.effectVars, fe i ∉ σ.effectVars) :
    X.holds (σ.instantiateProjected ft fe).2 v ↔
      ∃ wt : Nat → GroundTy, ∃ we : Nat → Finset Op,
        (∀ i, i ∉ σ.typeVars → wt i = v.types i) ∧
        (∀ i, i ∉ σ.effectVars → we i = v.effects i) ∧
        X.holds σ.condition ⟨wt, we⟩ ∧
        (∀ i ∈ σ.typeVars, wt i = v.types (ft i)) ∧
        (∀ i ∈ σ.effectVars, we i = v.effects (fe i)) := by
  change X.holds (X.project σ.typeVars σ.effectVars
    (X.combine σ.condition
      (X.combine (typeLinks X (σ.typeVars.sort (· ≤ ·)) ft)
        (effectLinks X (σ.effectVars.sort (· ≤ ·)) fe)))) v ↔ _
  unfold ConstraintSystem.project
  rw [X.projection_iff]
  constructor
  · rintro ⟨wt, we, hwt, hwe, hc⟩
    have hc' := (X.combine_iff _ _ _).1 hc
    have hlinks := (X.combine_iff _ _ _).1 hc'.2
    refine ⟨wt, we, hwt, hwe, hc'.1, ?_, ?_⟩
    · intro i hi
      have heq := (typeLinks_iff X _ ft ⟨wt, we⟩).1 hlinks.1
        i (by simpa using hi)
      exact heq.trans (hwt (ft i) (hfreshT i hi))
    · intro i hi
      have heq := (effectLinks_iff X _ fe ⟨wt, we⟩).1 hlinks.2
        i (by simpa using hi)
      exact heq.trans (hwe (fe i) (hfreshE i hi))
  · rintro ⟨wt, we, hwt, hwe, hc, ht, he⟩
    refine ⟨wt, we, hwt, hwe,
      (X.combine_iff _ _ _).2 ⟨hc,
        (X.combine_iff _ _ _).2 ⟨?_, ?_⟩⟩⟩
    · apply (typeLinks_iff X _ ft ⟨wt, we⟩).2
      intro i hi
      have him : i ∈ σ.typeVars := by simpa using hi
      exact (ht i him).trans (hwt (ft i) (hfreshT i him)).symm
    · apply (effectLinks_iff X _ fe ⟨wt, we⟩).2
      intro i hi
      have him : i ∈ σ.effectVars := by simpa using hi
      exact (he i him).trans (hwe (fe i) (hfreshE i him)).symm

/-- Projection-based instantiation realizes a qualified ground instance
without any law about the formula's internally bound names. -/
theorem Scheme.instantiateProjected_groundInstance {X : ConstraintSystem}
    (σ : Scheme X) (ft fe : Nat → Nat)
    (hadm : σ.AdmissibleRename ft fe)
    (hfreshT : ∀ i ∈ σ.typeVars, ft i ∉ σ.typeVars)
    (hfreshE : ∀ i ∈ σ.effectVars, fe i ∉ σ.effectVars)
    (v : Valuation)
    (hC : X.holds (σ.instantiateProjected ft fe).2 v) :
    σ.GroundInstance v ((σ.instantiateProjected ft fe).1.eval v) := by
  obtain ⟨wt, we, hwt, hwe, hc, ht, he⟩ :=
    (σ.instantiateProjected_iff ft fe v hfreshT hfreshE).mp hC
  have hpbT : wt = v.types ∘ ft := by
    funext i
    by_cases hi : i ∈ σ.typeVars
    · exact ht i hi
    · exact (hwt i hi).trans (congrArg v.types (hadm.1 i hi)).symm
  have hpbE : we = v.effects ∘ fe := by
    funext i
    by_cases hi : i ∈ σ.effectVars
    · exact he i hi
    · exact (hwe i hi).trans (congrArg v.effects (hadm.2 i hi)).symm
  refine ⟨wt, we, hwt, hwe, hc, ?_⟩
  simp [Scheme.instantiateProjected, Ty.eval_rename,
    Valuation.pullback, hpbT, hpbE]

/-- A ground instance can be placed at arbitrary distinct fresh names.
Only the free names of the opaque X formula need to be protected. -/
theorem Scheme.groundInstance_realizable_projected {X : ConstraintSystem}
    (σ : Scheme X) (ρ η : Nat → Nat)
    (hadm : σ.AdmissibleRename ρ η)
    (hinjT : Set.InjOn ρ σ.typeVars)
    (hinjE : Set.InjOn η σ.effectVars)
    (hfreshT : ∀ i ∈ σ.typeVars, ρ i ∉ σ.typeVars)
    (hfreshE : ∀ i ∈ σ.effectVars, η i ∉ σ.effectVars)
    (fixedTypes fixedEffects : Finset Nat)
    (hfreeT : σ.freeTypes ⊆ fixedTypes)
    (hfreeE : σ.freeEffects ⊆ fixedEffects)
    (hdisjT : (σ.typeVars.image ρ) ∩ fixedTypes = ∅)
    (hdisjE : (σ.effectVars.image η) ∩ fixedEffects = ∅)
    (v : Valuation) (t : GroundTy)
    (hinst : σ.GroundInstance v t) :
    ∃ w : Valuation,
      (∀ i ∈ fixedTypes, w.types i = v.types i) ∧
      (∀ i ∈ fixedEffects, w.effects i = v.effects i) ∧
      X.holds (σ.instantiateProjected ρ η).2 w ∧
      (σ.instantiateProjected ρ η).1.eval w = t := by
  classical
  rcases hinst with ⟨ft, fe, hft, hfe, hc, ht⟩
  let w : Valuation :=
    ⟨assignImage σ.typeVars ρ ft v.types,
      assignImage σ.effectVars η fe v.effects⟩
  have hfixedT : ∀ i ∈ fixedTypes, w.types i = v.types i := by
    intro i hi
    apply assignImage_not_mem
    intro himg
    have hm : i ∈ (σ.typeVars.image ρ) ∩ fixedTypes :=
      Finset.mem_inter.mpr ⟨himg, hi⟩
    rw [hdisjT] at hm
    simp at hm
  have hfixedE : ∀ i ∈ fixedEffects, w.effects i = v.effects i := by
    intro i hi
    apply assignImage_not_mem
    intro himg
    have hm : i ∈ (σ.effectVars.image η) ∩ fixedEffects :=
      Finset.mem_inter.mpr ⟨himg, hi⟩
    rw [hdisjE] at hm
    simp at hm
  have hagreeT : ∀ i ∈ σ.result.fvTypes ∪ X.freeTypes σ.condition,
      ft i = (w.pullback ρ η).types i := by
    intro i hi
    by_cases hb : i ∈ σ.typeVars
    · simp [Valuation.pullback, w,
        assignImage_mem σ.typeVars ρ hinjT ft v.types i hb]
    · have hf : i ∈ σ.freeTypes := Finset.mem_sdiff.mpr ⟨hi, hb⟩
      have hfix := hfixedT i (hfreeT hf)
      have hbase := hft i hb
      simp [Valuation.pullback, hadm.1 i hb, hfix, hbase]
  have hagreeE : ∀ i ∈ σ.result.fvEffects ∪ X.freeEffects σ.condition,
      fe i = (w.pullback ρ η).effects i := by
    intro i hi
    by_cases hb : i ∈ σ.effectVars
    · simp [Valuation.pullback, w,
        assignImage_mem σ.effectVars η hinjE fe v.effects i hb]
    · have hf : i ∈ σ.freeEffects := Finset.mem_sdiff.mpr ⟨hi, hb⟩
      have hfix := hfixedE i (hfreeE hf)
      have hbase := hfe i hb
      simp [Valuation.pullback, hadm.2 i hb, hfix, hbase]
  have hcondition : X.holds σ.condition (w.pullback ρ η) :=
    (X.free_support σ.condition ⟨ft, fe⟩ (w.pullback ρ η)
      (fun i hi => hagreeT i (Finset.mem_union_right _ hi))
      (fun i hi => hagreeE i (Finset.mem_union_right _ hi))).mp hc
  have hresult : σ.result.eval (w.pullback ρ η) = t := by
    have heq := Ty.eval_support σ.result ⟨ft, fe⟩
      (w.pullback ρ η)
      (fun i hi => hagreeT i (Finset.mem_union_left _ hi))
      (fun i hi => hagreeE i (Finset.mem_union_left _ hi))
    exact heq.symm.trans ht
  refine ⟨w, hfixedT, hfixedE, ?_, ?_⟩
  · apply (σ.instantiateProjected_iff ρ η w hfreshT hfreshE).2
    refine ⟨(w.pullback ρ η).types, (w.pullback ρ η).effects,
      ?_, ?_, hcondition, ?_, ?_⟩
    · intro i hi
      simp [Valuation.pullback, hadm.1 i hi]
    · intro i hi
      simp [Valuation.pullback, hadm.2 i hi]
    · intro i _
      rfl
    · intro i _
      rfl
  · simpa [Scheme.instantiateProjected, Ty.eval_rename] using hresult

theorem typeLinks_freeTypes {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (names : List Nat) (fresh : Nat → Nat) :
    ∀ j ∈ X.freeTypes (typeLinks X names fresh),
      ∃ i ∈ names, j = i ∨ j = fresh i := by
  induction names with
  | nil =>
      intro j hj
      simp [typeLinks, hAtom.trivial_types] at hj
  | cons i rest ih =>
      intro j hj
      have hsplit := hFV.combine_types _ _ (by
        simpa [typeLinks] using hj)
      rcases Finset.mem_union.mp hsplit with heq | hrest
      · have h := hAtom.equalType_types _ _ heq
        simp [Ty.fvTypes] at h
        exact ⟨i, by simp, h⟩
      · rcases ih j hrest with ⟨k, hk, heq⟩
        exact ⟨k, by simp [hk], heq⟩

theorem typeLinks_freeEffects {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (names : List Nat) (fresh : Nat → Nat) :
    X.freeEffects (typeLinks X names fresh) = ∅ := by
  induction names with
  | nil => simpa [typeLinks] using hAtom.trivial_effects
  | cons i rest ih =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hsplit := hFV.combine_effects _ _ (by
        simpa [typeLinks] using hj)
      rcases Finset.mem_union.mp hsplit with heq | hrest
      · have h := hAtom.equalType_effects _ _ heq
        simp [Ty.fvEffects] at h
      · change j ∈ X.freeEffects (typeLinks X rest fresh) at hrest
        rw [ih] at hrest
        simp at hrest

theorem effectLinks_freeTypes {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (names : List Nat) (fresh : Nat → Nat) :
    X.freeTypes (effectLinks X names fresh) = ∅ := by
  induction names with
  | nil => simpa [effectLinks] using hAtom.trivial_types
  | cons i rest ih =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hsplit := hFV.combine_types _ _ (by
        simpa [effectLinks] using hj)
      rcases Finset.mem_union.mp hsplit with heq | hrest
      · have hparts := hFV.combine_types _ _ (by
          simpa [ConstraintSystem.equalEffect] using heq)
        rcases Finset.mem_union.mp hparts with ha | hb
        · rw [hAtom.includedEffect_types] at ha
          simp at ha
        · rw [hAtom.includedEffect_types] at hb
          simp at hb
      · change j ∈ X.freeTypes (effectLinks X rest fresh) at hrest
        rw [ih] at hrest
        simp at hrest

theorem effectLinks_freeEffects {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (names : List Nat) (fresh : Nat → Nat) :
    ∀ j ∈ X.freeEffects (effectLinks X names fresh),
      ∃ i ∈ names, j = i ∨ j = fresh i := by
  induction names with
  | nil =>
      intro j hj
      simp [effectLinks, hAtom.trivial_effects] at hj
  | cons i rest ih =>
      intro j hj
      have hsplit := hFV.combine_effects _ _ (by
        simpa [effectLinks] using hj)
      rcases Finset.mem_union.mp hsplit with heq | hrest
      · have hparts := hFV.combine_effects _ _ (by
          simpa [ConstraintSystem.equalEffect] using heq)
        rcases Finset.mem_union.mp hparts with ha | hb
        · have h := hAtom.includedEffect_effects _ _ ha
          simp [Poly.Effect.var] at h
          exact ⟨i, by simp, h⟩
        · have h := hAtom.includedEffect_effects _ _ hb
          simp [Poly.Effect.var] at h
          exact ⟨i, by simp, h.symm⟩
      · rcases ih j hrest with ⟨k, hk, heq⟩
        exact ⟨k, by simp [hk], heq⟩

/-- Projection removes the old quantified names; the instantiated formula
can depend only on the scheme's free names and their fresh replacements. -/
theorem Scheme.instantiateProjected_freeTypes {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (σ : Scheme X) (ft fe : Nat → Nat) :
    X.freeTypes (σ.instantiateProjected ft fe).2 ⊆
      σ.freeTypes ∪ σ.typeVars.image ft := by
  intro j hj
  have hproj := hFV.project_types σ.typeVars σ.effectVars
    (X.combine σ.condition
      (X.combine (typeLinks X (σ.typeVars.sort (· ≤ ·)) ft)
        (effectLinks X (σ.effectVars.sort (· ≤ ·)) fe)))
  have h : j ∈ X.freeTypes (X.combine σ.condition
      (X.combine (typeLinks X (σ.typeVars.sort (· ≤ ·)) ft)
        (effectLinks X (σ.effectVars.sort (· ≤ ·)) fe))) ∧
      j ∉ σ.typeVars := Finset.mem_sdiff.mp (hproj (by
        simpa [Scheme.instantiateProjected] using hj))
  have hs := hFV.combine_types _ _ h.1
  rcases Finset.mem_union.mp hs with hc | hlinks
  · exact Finset.mem_union_left _
      (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _ hc, h.2⟩)
  · have hs' := hFV.combine_types _ _ hlinks
    rcases Finset.mem_union.mp hs' with ht | he
    · rcases typeLinks_freeTypes hFV hAtom _ ft j ht with
        ⟨i, hi, hji⟩
      have hib : i ∈ σ.typeVars := by simpa using hi
      rcases hji with rfl | hji
      · exact False.elim (h.2 hib)
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, hib, hji.symm⟩)
    · have he' := effectLinks_freeTypes hFV hAtom
        (σ.effectVars.sort (· ≤ ·)) fe
      rw [he'] at he
      simp at he

theorem Scheme.instantiateProjected_freeEffects {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (σ : Scheme X) (ft fe : Nat → Nat) :
    X.freeEffects (σ.instantiateProjected ft fe).2 ⊆
      σ.freeEffects ∪ σ.effectVars.image fe := by
  intro j hj
  have hproj := hFV.project_effects σ.typeVars σ.effectVars
    (X.combine σ.condition
      (X.combine (typeLinks X (σ.typeVars.sort (· ≤ ·)) ft)
        (effectLinks X (σ.effectVars.sort (· ≤ ·)) fe)))
  have h : j ∈ X.freeEffects (X.combine σ.condition
      (X.combine (typeLinks X (σ.typeVars.sort (· ≤ ·)) ft)
        (effectLinks X (σ.effectVars.sort (· ≤ ·)) fe))) ∧
      j ∉ σ.effectVars := Finset.mem_sdiff.mp (hproj (by
        simpa [Scheme.instantiateProjected] using hj))
  have hs := hFV.combine_effects _ _ h.1
  rcases Finset.mem_union.mp hs with hc | hlinks
  · exact Finset.mem_union_left _
      (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _ hc, h.2⟩)
  · have hs' := hFV.combine_effects _ _ hlinks
    rcases Finset.mem_union.mp hs' with ht | he
    · have ht' := typeLinks_freeEffects hFV hAtom
        (σ.typeVars.sort (· ≤ ·)) ft
      rw [ht'] at ht
      simp at ht
    · rcases effectLinks_freeEffects hFV hAtom _ fe j he with
        ⟨i, hi, hji⟩
      have hib : i ∈ σ.effectVars := by simpa using hi
      rcases hji with rfl | hji
      · exact False.elim (h.2 hib)
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, hib, hji.symm⟩)

theorem Scheme.instantiateProjected_supportTypes {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (σ : Scheme X) (ft fe : Nat → Nat)
    (hadm : σ.AdmissibleRename ft fe) :
    (σ.instantiateProjected ft fe).1.fvTypes ∪
      X.freeTypes (σ.instantiateProjected ft fe).2 ⊆
      σ.freeTypes ∪ σ.typeVars.image ft := by
  intro j hj
  rcases Finset.mem_union.mp hj with hty | hc
  · change j ∈ (σ.result.rename ft fe).fvTypes at hty
    rw [Ty.fvTypes_rename] at hty
    rcases Finset.mem_image.mp hty with ⟨i, hi, rfl⟩
    by_cases hb : i ∈ σ.typeVars
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, hb, rfl⟩)
    · have hf : i ∈ σ.freeTypes :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_left _ hi, hb⟩
      simpa [hadm.1 i hb] using
        (Finset.mem_union_left (σ.typeVars.image ft) hf)
  · exact σ.instantiateProjected_freeTypes hFV hAtom ft fe hc

theorem Scheme.instantiateProjected_supportEffects {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (σ : Scheme X) (ft fe : Nat → Nat)
    (hadm : σ.AdmissibleRename ft fe) :
    (σ.instantiateProjected ft fe).1.fvEffects ∪
      X.freeEffects (σ.instantiateProjected ft fe).2 ⊆
      σ.freeEffects ∪ σ.effectVars.image fe := by
  intro j hj
  rcases Finset.mem_union.mp hj with hty | hc
  · change j ∈ (σ.result.rename ft fe).fvEffects at hty
    rw [Ty.fvEffects_rename] at hty
    rcases Finset.mem_image.mp hty with ⟨i, hi, rfl⟩
    by_cases hb : i ∈ σ.effectVars
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨i, hb, rfl⟩)
    · have hf : i ∈ σ.freeEffects :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_left _ hi, hb⟩
      simpa [hadm.2 i hb] using
        (Finset.mem_union_left (σ.effectVars.image fe) hf)
  · exact σ.instantiateProjected_freeEffects hFV hAtom ft fe hc

end SystemFXi.EHMX.Generic
