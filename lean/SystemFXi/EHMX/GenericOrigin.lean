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

/-- Free names in an application come from its subresults or its two fresh
result names. -/
theorem Output.app_support_sources {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (rf rx : Output X) :
    let b := Ty.var rx.next.types
    let η := Poly.Effect.var rx.next.effects
    let r : Output X :=
      ⟨b, rf.effect ∪ rx.effect ∪ η,
        X.combine (X.combine rf.condition rx.condition)
          (X.equalType rf.ty (.arr rx.ty η b)),
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩
    (r.supportTypes ⊆
      insert rx.next.types (rf.supportTypes ∪ rx.supportTypes)) ∧
    (r.supportEffects ⊆
      insert rx.next.effects (rf.supportEffects ∪ rx.supportEffects)) := by
  dsimp
  constructor
  · intro i hi
    simp only [Output.supportTypes, Ty.fvTypes, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    rcases hi with rfl | hcon
    · exact Or.inl rfl
    · have hsplit := hFV.combine_types _ _ hcon
      rcases Finset.mem_union.mp hsplit with hleft | heq
      · rcases Finset.mem_union.mp (hFV.combine_types _ _ hleft) with
          hf | hx
        · exact Or.inr (Or.inl (Or.inr hf))
        · exact Or.inr (Or.inr (Or.inr hx))
      · have hty := hAtom.equalType_types _ _ heq
        simp [Ty.fvTypes] at hty
        rcases hty with hnew | hf | hx
        · exact Or.inl hnew
        · exact Or.inr (Or.inl (Or.inl hf))
        · exact Or.inr (Or.inr (Or.inl hx))
  · intro i hi
    have hbase := hFV.combine_effects
      (X.combine rf.condition rx.condition)
      (X.equalType rf.ty
        (.arr rx.ty (Poly.Effect.var rx.next.effects)
          (.var rx.next.types)))
    have hinner := hFV.combine_effects rf.condition rx.condition
    have heq := hAtom.equalType_effects rf.ty
      (.arr rx.ty (Poly.Effect.var rx.next.effects)
        (.var rx.next.types))
    simp [Output.supportEffects, Ty.fvEffects,
      Poly.Effect.vars_union, Poly.Effect.var] at hi ⊢
    rcases hi with hnew | hf | hx | hc
    · exact Or.inl hnew
    · exact Or.inr (Or.inr (Or.inl hf))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))
    · rcases Finset.mem_union.mp (hbase hc) with hinnerM | heqM
      · rcases Finset.mem_union.mp (hinner hinnerM) with hfC | hxC
        · exact Or.inr (Or.inr (Or.inr (Or.inl hfC)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hxC)))))
      · have ht := heq heqM
        simp [Ty.fvEffects] at ht
        rcases ht with hfTy | hxTy | hnew
        · exact Or.inr (Or.inl hfTy)
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxTy))))
        · exact Or.inl (by simpa [Poly.Effect.var] using hnew)

theorem Output.app_old_support {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (Γ : Context X) (s : Supply) (rf rx : Output X)
    (hnext : s.types ≤ rx.next.types ∧
      s.effects ≤ rx.next.effects)
    (hfT : ∀ i ∈ rf.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (hfE : ∀ i ∈ rf.supportEffects, i < s.effects → i ∈ Γ.freeEffects)
    (hxT : ∀ i ∈ rx.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (hxE : ∀ i ∈ rx.supportEffects, i < s.effects → i ∈ Γ.freeEffects) :
    let b := Ty.var rx.next.types
    let η := Poly.Effect.var rx.next.effects
    let r : Output X :=
      ⟨b, rf.effect ∪ rx.effect ∪ η,
        X.combine (X.combine rf.condition rx.condition)
          (X.equalType rf.ty (.arr rx.ty η b)),
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩
    (∀ i ∈ r.supportTypes, i < s.types → i ∈ Γ.freeTypes) ∧
    (∀ i ∈ r.supportEffects, i < s.effects → i ∈ Γ.freeEffects) := by
  dsimp
  have hsrc := Output.app_support_sources hFV hAtom rf rx
  constructor
  · intro i hi hsmall
    rcases Finset.mem_insert.mp (hsrc.1 hi) with hnew | hrest
    · omega
    rcases Finset.mem_union.mp hrest with hf | hx
    · exact hfT i hf hsmall
    · exact hxT i hx hsmall
  · intro i hi hsmall
    rcases Finset.mem_insert.mp (hsrc.2 hi) with hnew | hrest
    · omega
    rcases Finset.mem_union.mp hrest with hf | hx
    · exact hfE i hf hsmall
    · exact hxE i hx hsmall

theorem Output.lam_old_support {X : ConstraintSystem}
    (Γ : Context X) (s : Supply) (rb : Output X)
    (hbT : ∀ i ∈ rb.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (hbE : ∀ i ∈ rb.supportEffects, i < s.effects → i ∈ Γ.freeEffects) :
    let r : Output X :=
      ⟨.arr (.var s.types) rb.effect rb.ty, ∅,
        rb.condition, rb.next⟩
    (∀ i ∈ r.supportTypes, i < s.types → i ∈ Γ.freeTypes) ∧
    (∀ i ∈ r.supportEffects, i < s.effects → i ∈ Γ.freeEffects) := by
  dsimp
  constructor
  · intro i hi hsmall
    have hsub : i = s.types ∨ i ∈ rb.supportTypes := by
      simp [Output.supportTypes, Ty.fvTypes] at hi ⊢
      aesop
    rcases hsub with hnew | hbody
    · omega
    · exact hbT i hbody hsmall
  · intro i hi hsmall
    have hbody : i ∈ rb.supportEffects := by
      simp [Output.supportEffects, Ty.fvEffects] at hi ⊢
      aesop
    exact hbE i hbody hsmall

theorem Output.letVal_old_support {X : ConstraintSystem}
    (hFV : X.LawfulFV) (Γ : Context X)
    (s : Supply) (r₁ r₂ : Output X)
    (h₂T : ∀ i ∈ r₂.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (h₂E : ∀ i ∈ r₂.supportEffects, i < s.effects → i ∈ Γ.freeEffects) :
    let r : Output X :=
      ⟨r₂.ty, r₂.effect,
        X.combine (Scheme.residual Γ r₁.condition r₁.ty)
          r₂.condition, r₂.next⟩
    (∀ i ∈ r.supportTypes, i < s.types → i ∈ Γ.freeTypes) ∧
    (∀ i ∈ r.supportEffects, i < s.effects → i ∈ Γ.freeEffects) := by
  dsimp
  have hres := Scheme.residual_free_context hFV Γ r₁.condition r₁.ty
  constructor
  · intro i hi hsmall
    rcases Finset.mem_union.mp hi with hty | hcond
    · exact h₂T i (Finset.mem_union_left _ hty) hsmall
    rcases Finset.mem_union.mp (hFV.combine_types _ _ hcond) with
      hleft | hright
    · exact hres.1 hleft
    · exact h₂T i (Finset.mem_union_right _ hright) hsmall
  · intro i hi hsmall
    simp only [Output.supportEffects] at hi
    rcases Finset.mem_union.mp hi with htyeff | hcond
    · exact h₂E i (Finset.mem_union_left _ htyeff) hsmall
    rcases Finset.mem_union.mp (hFV.combine_effects _ _ hcond) with
      hleft | hright
    · exact hres.2 hleft
    · exact h₂E i (Finset.mem_union_right _ hright) hsmall

theorem Output.letMono_old_support {X : ConstraintSystem}
    (hFV : X.LawfulFV) (Γ : Context X)
    (s : Supply) (r₁ r₂ : Output X)
    (h₁T : ∀ i ∈ r₁.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (h₁E : ∀ i ∈ r₁.supportEffects, i < s.effects → i ∈ Γ.freeEffects)
    (h₂T : ∀ i ∈ r₂.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (h₂E : ∀ i ∈ r₂.supportEffects, i < s.effects → i ∈ Γ.freeEffects) :
    let r : Output X :=
      ⟨r₂.ty, r₁.effect ∪ r₂.effect,
        X.combine r₁.condition r₂.condition, r₂.next⟩
    (∀ i ∈ r.supportTypes, i < s.types → i ∈ Γ.freeTypes) ∧
    (∀ i ∈ r.supportEffects, i < s.effects → i ∈ Γ.freeEffects) := by
  dsimp
  constructor
  · intro i hi hsmall
    rcases Finset.mem_union.mp hi with hty | hcond
    · exact h₂T i (Finset.mem_union_left _ hty) hsmall
    rcases Finset.mem_union.mp (hFV.combine_types _ _ hcond) with
      hleft | hright
    · exact h₁T i (Finset.mem_union_right _ hleft) hsmall
    · exact h₂T i (Finset.mem_union_right _ hright) hsmall
  · intro i hi hsmall
    have hsplit := hFV.combine_effects r₁.condition r₂.condition
    simp only [Output.supportEffects, Poly.Effect.vars_union,
      Finset.mem_union] at hi
    rcases hi with (hty | heff) | hcond
    · exact h₂E i (by simp [Output.supportEffects, hty]) hsmall
    · rcases heff with heff₁ | heff₂
      · exact h₁E i (by simp [Output.supportEffects, heff₁]) hsmall
      · exact h₂E i (by simp [Output.supportEffects, heff₂]) hsmall
    · rcases Finset.mem_union.mp (hsplit hcond) with hc₁ | hc₂
      · exact h₁E i (by simp [Output.supportEffects, hc₁]) hsmall
      · exact h₂E i (by simp [Output.supportEffects, hc₂]) hsmall

theorem Output.perform_old_support {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (Γ : Context X) (s : Supply) (op : Op)
    (raw : OpDecl) (hclosed : raw.Closed) (re : Output X)
    (heT : ∀ i ∈ re.supportTypes, i < s.types → i ∈ Γ.freeTypes)
    (heE : ∀ i ∈ re.supportEffects, i < s.effects → i ∈ Γ.freeEffects) :
    let ft := renameBound raw.typeVars s.types
    let fe := renameBound raw.effectVars s.effects
    let decl := raw.alphaRename ft fe
    let r : Output X :=
      ⟨decl.output, Poly.Effect.singleton op ∪ re.effect,
        X.combine re.condition (X.equalType re.ty decl.input),
        re.next⟩
    (∀ i ∈ r.supportTypes, i < s.types → i ∈ Γ.freeTypes) ∧
    (∀ i ∈ r.supportEffects, i < s.effects → i ∈ Γ.freeEffects) := by
  dsimp
  let ft := renameBound raw.typeVars s.types
  let fe := renameBound raw.effectVars s.effects
  let decl := raw.alphaRename ft fe
  have hinterval := raw.closed_alphaRename_used_interval hclosed s
  have hdeclT : ∀ i ∈ decl.usedTypes, s.types < i := by
    intro i hi
    exact (hinterval.1 i hi).1
  have hdeclE : ∀ i ∈ decl.usedEffects, s.effects < i := by
    intro i hi
    exact (hinterval.2 i hi).1
  constructor
  · intro i hi hsmall
    have hsource : i ∈ re.supportTypes ∨ i ∈ decl.usedTypes := by
      rcases Finset.mem_union.mp hi with hout | hcond
      · change i ∈ decl.output.fvTypes at hout
        exact Or.inr (by simp [OpDecl.usedTypes, hout])
      rcases Finset.mem_union.mp (hFV.combine_types _ _ hcond) with
        hc | heq
      · exact Or.inl (Finset.mem_union_right _ hc)
      · have ht := hAtom.equalType_types re.ty decl.input heq
        rcases Finset.mem_union.mp ht with hty | hin
        · exact Or.inl (Finset.mem_union_left _ hty)
        · exact Or.inr (by simp [OpDecl.usedTypes, hin])
    rcases hsource with harg | hdecl
    · exact heT i harg hsmall
    · have := hdeclT i hdecl
      omega
  · intro i hi hsmall
    have hsource : i ∈ re.supportEffects ∨ i ∈ decl.usedEffects := by
      rcases Finset.mem_union.mp hi with hbefore | hcond
      · rcases Finset.mem_union.mp hbefore with hout | heff
        · change i ∈ decl.output.fvEffects at hout
          exact Or.inr (by simp [OpDecl.usedEffects, hout])
        · have heff' : i ∈ re.effect.vars := by
            simpa [Poly.Effect.vars_union] using heff
          exact Or.inl (by simp [Output.supportEffects, heff'])
      · rcases Finset.mem_union.mp (hFV.combine_effects _ _ hcond) with
          hc | heq
        · exact Or.inl (by simp [Output.supportEffects, hc])
        · have ht := hAtom.equalType_effects re.ty decl.input heq
          rcases Finset.mem_union.mp ht with hty | hin
          · exact Or.inl (by simp [Output.supportEffects, hty])
          · exact Or.inr (by simp [OpDecl.usedEffects, hin])
    rcases hsource with harg | hdecl
    · exact heE i harg hsmall
    · have := hdeclE i hdecl
      omega

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
