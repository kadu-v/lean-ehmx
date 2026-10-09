import SystemFXi.EHMX.GenericEffectFresh

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

private theorem foldl_union_eq {α : Type}
    (f : α → Finset Nat) (xs : List α) (acc : Finset Nat) :
    xs.foldl (fun names x => names ∪ f x) acc =
      acc ∪ xs.foldl (fun names x => names ∪ f x) ∅ := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
      simp only [List.foldl_cons]
      rw [ih (acc ∪ f x), ih (∅ ∪ f x)]
      simp [Finset.union_assoc]

theorem Context.freeTypes_cons {X : ConstraintSystem}
    (σ : Scheme X) (Γ : Context X) :
    Context.freeTypes (σ :: Γ) = σ.freeTypes ∪ Γ.freeTypes := by
  simp only [Context.freeTypes, List.foldl_cons]
  rw [foldl_union_eq]
  simp

theorem Context.freeEffects_cons {X : ConstraintSystem}
    (σ : Scheme X) (Γ : Context X) :
    Context.freeEffects (σ :: Γ) = σ.freeEffects ∪ Γ.freeEffects := by
  simp only [Context.freeEffects, List.foldl_cons]
  rw [foldl_union_eq]
  simp

/-- If old names in the generated return clause come from its context, they
predate the rigid operation parameters. -/
theorem Output.return_old_below_body {X : ConstraintSystem}
    (hAtom : X.LawfulGeneratedFV)
    (Γ : Context X) (rb rr : Output X) (sr : Supply)
    (hΓT : ∀ i ∈ Γ.freeTypes, i < rb.next.types)
    (hΓE : ∀ i ∈ Γ.freeEffects, i < rb.next.effects)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hrOriginT : ∀ i ∈ rr.supportTypes,
      i < sr.types → i ∈ Context.freeTypes (Scheme.mono rb.ty :: Γ))
    (hrOriginE : ∀ i ∈ rr.supportEffects,
      i < sr.effects → i ∈ Context.freeEffects (Scheme.mono rb.ty :: Γ)) :
    (∀ i ∈ rr.supportTypes, i < sr.types → i < rb.next.types) ∧
    (∀ i ∈ rr.supportEffects, i < sr.effects → i < rb.next.effects) := by
  constructor
  · intro i hi hsmall
    have h := hrOriginT i hi hsmall
    rw [Context.freeTypes_cons] at h
    rcases Finset.mem_union.mp h with hty | hΓ
    · exact hbT i (by
        simp [Scheme.mono, Scheme.freeTypes,
          Output.supportTypes, hAtom.trivial_types] at hty ⊢
        aesop)
    · exact hΓT i hΓ
  · intro i hi hsmall
    have h := hrOriginE i hi hsmall
    rw [Context.freeEffects_cons] at h
    rcases Finset.mem_union.mp h with hty | hΓ
    · exact hbE i (by
        simp [Scheme.mono, Scheme.freeEffects,
          Output.supportEffects, hAtom.trivial_effects] at hty ⊢
        aesop)
    · exact hΓE i hΓ

/-- Generalization leaves only names already free in the environment. -/
theorem Scheme.generalize_free_subset_context {X : ConstraintSystem}
    (Γ : Context X) (c : X.Formula) (τ : Ty) :
    (Scheme.generalize Γ c τ).freeTypes ⊆ Γ.freeTypes ∧
    (Scheme.generalize Γ c τ).freeEffects ⊆ Γ.freeEffects := by
  constructor
  · intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨hused, hnot⟩
    by_contra hΓ
    exact hnot (by simpa [Scheme.generalize] using
      (Finset.mem_sdiff.mpr ⟨hused, hΓ⟩))
  · intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨hused, hnot⟩
    by_contra hΓ
    exact hnot (by simpa [Scheme.generalize] using
      (Finset.mem_sdiff.mpr ⟨hused, hΓ⟩))

/-- Projection removes old quantified type names. Any name in an
instantiated result below the starting supply was already free in the scheme. -/
theorem Scheme.instantiateProjected_oldTypes
    {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (σ : Scheme X) (s : Supply) (i : Nat)
    (hi : i ∈ (σ.instantiateProjected
      (renameBound σ.typeVars s.types)
      (renameBound σ.effectVars s.effects)).1.fvTypes ∪
      X.freeTypes (σ.instantiateProjected
        (renameBound σ.typeVars s.types)
        (renameBound σ.effectVars s.effects)).2)
    (hsmall : i < s.types) :
    i ∈ σ.freeTypes := by
  have hadm : σ.AdmissibleRename
      (renameBound σ.typeVars s.types)
      (renameBound σ.effectVars s.effects) :=
    ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩
  have h := σ.instantiateProjected_supportTypes hFV hAtom
    _ _ hadm hi
  rcases Finset.mem_union.mp h with hfree | hnew
  · exact hfree
  · rcases Finset.mem_image.mp hnew with ⟨j, hj, rfl⟩
    simp [renameBound, hj] at hsmall
    omega

/-- The corresponding bound for effect names. -/
theorem Scheme.instantiateProjected_oldEffects
    {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (σ : Scheme X) (s : Supply) (i : Nat)
    (hi : i ∈ (σ.instantiateProjected
      (renameBound σ.typeVars s.types)
      (renameBound σ.effectVars s.effects)).1.fvEffects ∪
      X.freeEffects (σ.instantiateProjected
        (renameBound σ.typeVars s.types)
        (renameBound σ.effectVars s.effects)).2)
    (hsmall : i < s.effects) :
    i ∈ σ.freeEffects := by
  have hadm : σ.AdmissibleRename
      (renameBound σ.typeVars s.types)
      (renameBound σ.effectVars s.effects) :=
    ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩
  have h := σ.instantiateProjected_supportEffects hFV hAtom
    _ _ hadm hi
  rcases Finset.mem_union.mp h with hfree | hnew
  · exact hfree
  · rcases Finset.mem_image.mp hnew with ⟨j, hj, rfl⟩
    simp [renameBound, hj] at hsmall
    omega

/-- The variable branch preserves the origin of every old free name. -/
theorem generate_variable_old_support
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (Γ : Context X) (i : Nat) (s : Supply) (r : Output X)
    (hr : generate sig X Γ (.var i) s = some r) :
    (∀ j ∈ r.supportTypes, j < s.types → j ∈ Γ.freeTypes) ∧
    (∀ j ∈ r.supportEffects, j < s.effects → j ∈ Γ.freeEffects) := by
  cases hσ : Γ[i]? with
  | none => simp [generate, hσ] at hr
  | some σ =>
      by_cases hfresh : σ.FreshRename
          (renameBound σ.typeVars s.types)
          (renameBound σ.effectVars s.effects)
      · simp [generate, hσ, hfresh] at hr
        cases hr
        have hmem : σ ∈ Γ := List.mem_of_getElem? hσ
        constructor
        · intro j hj hsmall
          have hfree := σ.instantiateProjected_oldTypes hFV hAtom
            s j (by simpa [Output.supportTypes] using hj) hsmall
          exact Context.freeTypes_of_mem Γ σ hmem hfree
        · intro j hj hsmall
          have hfree := σ.instantiateProjected_oldEffects hFV hAtom
            s j (by simpa [Output.supportEffects] using hj) hsmall
          exact Context.freeEffects_of_mem Γ σ hmem hfree
      · simp [generate, hσ, hfresh] at hr

/-- The handler constructor cannot introduce an old free name when its three
generated subresults have already been accounted for. -/
theorem Output.handler_old_support
    {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (Γ : Context X) (op : Op) (decl : OpDecl)
    (s sb : Supply) (rb rr rc : Output X)
    (localTypes localEffects : Finset Nat)
    (hnewT : s.types ≤ sb.types)
    (hnewE : s.effects ≤ sb.effects)
    (hbT : ∀ i ∈ rb.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (hbE : ∀ i ∈ rb.supportEffects, i < s.effects → i ∈ Γ.freeEffects)
    (hrT : ∀ i ∈ rr.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (hrE : ∀ i ∈ rr.supportEffects, i < s.effects → i ∈ Γ.freeEffects)
    (hcT : ∀ i ∈ rc.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (hcE : ∀ i ∈ rc.supportEffects, i < s.effects → i ∈ Γ.freeEffects) :
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    let C := handlerCondition X op decl rb.condition rr.condition
      rc.condition rr.ty rc.ty a rb.effect rr.effect rc.effect
      δ χ localTypes localEffects
    let r : Output X := ⟨a, χ, C, rc.next⟩
    (∀ i ∈ r.supportTypes, i < s.types → i ∈ Γ.freeTypes) ∧
    (∀ i ∈ r.supportEffects, i < s.effects → i ∈ Γ.freeEffects) := by
  dsimp
  constructor
  · intro i hi hsmall
    rcases Finset.mem_union.mp hi with hty | hcond
    · simp [Ty.fvTypes] at hty
      omega
    have h := handlerCondition_freeTypes hFV hAtom op decl
      rb.condition rr.condition rc.condition rr.ty rc.ty
      (.var sb.types) rb.effect rr.effect rc.effect
      (Poly.Effect.var sb.effects)
      (Poly.Effect.var (sb.effects + 1))
      localTypes localEffects hcond
    simp only [Finset.mem_union, Ty.fvTypes,
      Finset.mem_singleton] at h
    rcases h with ((((hCin | hCr) | hCo) | hτr) | hτo) | ha
    · exact hbT i (Finset.mem_union_right _ hCin) hsmall
    · exact hrT i (Finset.mem_union_right _ hCr) hsmall
    · exact hcT i (Finset.mem_union_right _ hCo) hsmall
    · exact hrT i (Finset.mem_union_left _ hτr) hsmall
    · exact hcT i (Finset.mem_union_left _ hτo) hsmall
    · omega
  · intro i hi hsmall
    simp only [Output.supportEffects, Ty.fvEffects,
      Poly.Effect.var, Finset.mem_union,
      Finset.mem_singleton] at hi
    rcases hi with hχ | hcond
    · simp at hχ
      omega
    have h := handlerCondition_freeEffects hFV hAtom op decl
      rb.condition rr.condition rc.condition rr.ty rc.ty
      (.var sb.types) rb.effect rr.effect rc.effect
      (Poly.Effect.var sb.effects)
      (Poly.Effect.var (sb.effects + 1))
      localTypes localEffects hcond
    simp only [Finset.mem_union, Ty.fvEffects,
      Poly.Effect.var, Finset.mem_singleton] at h
    rcases h with ((((((((((hCin | hCr) | hCo) | hτr) | hτo) | ha) |
      hεin) | hεr) | hεo) | hδ) | hχ)
    · exact hbE i (by simp [Output.supportEffects, hCin]) hsmall
    · exact hrE i (by simp [Output.supportEffects, hCr]) hsmall
    · exact hcE i (by simp [Output.supportEffects, hCo]) hsmall
    · exact hrE i (by simp [Output.supportEffects, hτr]) hsmall
    · exact hcE i (by simp [Output.supportEffects, hτo]) hsmall
    · simp at ha
    · exact hbE i (by simp [Output.supportEffects, hεin]) hsmall
    · exact hrE i (by simp [Output.supportEffects, hεr]) hsmall
    · exact hcE i (by simp [Output.supportEffects, hεo]) hsmall
    · omega
    · omega

end SystemFXi.EHMX.Generic
