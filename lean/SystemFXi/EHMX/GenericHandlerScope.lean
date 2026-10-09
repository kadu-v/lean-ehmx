import SystemFXi.EHMX.GenericOriginInduction

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

/-- The operation clause contributes free type names to the outer handler
constraint only after its rigid and local names have been removed. -/
theorem handlerCondition_freeTypes_refined {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (op : Op) (decl : OpDecl)
    (Cin Cr Co : X.Formula) (τr τo a : Ty)
    (εin εr εo δ χ : Effect) (lt le : Finset Nat)
    (i : Nat)
    (hi : i ∈ X.freeTypes
      (handlerCondition X op decl Cin Cr Co τr τo a
        εin εr εo δ χ lt le)) :
    i ∈ X.freeTypes Cin ∨ i ∈ X.freeTypes Cr ∨
    i ∈ τr.fvTypes ∨ i ∈ a.fvTypes ∨
    ((i ∈ X.freeTypes Co ∨ i ∈ τo.fvTypes) ∧
      i ∉ decl.typeVars ∪ lt) := by
  unfold handlerCondition at hi
  rcases Finset.mem_union.mp (hFV.combine_types _ _ hi) with
    hstart | hrest
  · rcases Finset.mem_union.mp (hFV.combine_types _ _ hstart) with
      hc | hr
    · exact Or.inl hc
    · exact Or.inr (Or.inl hr)
  · rcases Finset.mem_union.mp (hFV.combine_types _ _ hrest) with
      heq | htail
    · have h := hAtom.equalType_types τr a heq
      rcases Finset.mem_union.mp h with hτ | ha
      · exact Or.inr (Or.inr (Or.inl hτ))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · rcases Finset.mem_union.mp (hFV.combine_types _ _ htail) with
        hclause | heffects
      · have hclause' := hFV.handler_types decl.typeVars
          decl.effectVars lt le
          (X.combine Co
            (X.combine (X.equalType τo a)
              (X.includedEffect εo χ))) hclause
        have ⟨hinner, hnot⟩ := Finset.mem_sdiff.mp hclause'
        rcases Finset.mem_union.mp (hFV.combine_types _ _ hinner) with
          hco | hmore
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            ⟨Or.inl hco, hnot⟩)))
        · rcases Finset.mem_union.mp (hFV.combine_types _ _ hmore) with
            heq | heff
          · have ht := hAtom.equalType_types τo a heq
            rcases Finset.mem_union.mp ht with hτ | ha
            · exact Or.inr (Or.inr (Or.inr (Or.inr
                ⟨Or.inr hτ, hnot⟩)))
            · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
          · rw [hAtom.includedEffect_types] at heff
            simp at heff
      · rcases Finset.mem_union.mp (hFV.combine_types _ _ heffects) with
          hsplit | hmore
        · rw [ConstraintSystem.split_freeTypes hFV hAtom op εin δ] at hsplit
          simp at hsplit
        · rcases Finset.mem_union.mp (hFV.combine_types _ _ hmore) with
            hδ | hε
          · rw [hAtom.includedEffect_types] at hδ
            simp at hδ
          · rw [hAtom.includedEffect_types] at hε
            simp at hε

/-- The corresponding effect-name bound. -/
theorem handlerCondition_freeEffects_refined {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (op : Op) (decl : OpDecl)
    (Cin Cr Co : X.Formula) (τr τo a : Ty)
    (εin εr εo δ χ : Effect) (lt le : Finset Nat)
    (i : Nat)
    (hi : i ∈ X.freeEffects
      (handlerCondition X op decl Cin Cr Co τr τo a
        εin εr εo δ χ lt le)) :
    i ∈ X.freeEffects Cin ∨ i ∈ X.freeEffects Cr ∨
    i ∈ τr.fvEffects ∨ i ∈ a.fvEffects ∨
    i ∈ εin.vars ∨ i ∈ εr.vars ∨ i ∈ δ.vars ∨ i ∈ χ.vars ∨
    ((i ∈ X.freeEffects Co ∨ i ∈ τo.fvEffects ∨
      i ∈ εo.vars) ∧ i ∉ decl.effectVars ∪ le) := by
  unfold handlerCondition at hi
  rcases Finset.mem_union.mp (hFV.combine_effects _ _ hi) with
    hstart | hrest
  · rcases Finset.mem_union.mp (hFV.combine_effects _ _ hstart) with
      hc | hr
    · aesop
    · aesop
  · rcases Finset.mem_union.mp (hFV.combine_effects _ _ hrest) with
      heq | htail
    · have h := hAtom.equalType_effects τr a heq
      rcases Finset.mem_union.mp h with hτ | ha <;> aesop
    · rcases Finset.mem_union.mp (hFV.combine_effects _ _ htail) with
        hclause | heffects
      · have hclause' := hFV.handler_effects decl.typeVars
          decl.effectVars lt le
          (X.combine Co
            (X.combine (X.equalType τo a)
              (X.includedEffect εo χ))) hclause
        have ⟨hinner, hnot⟩ := Finset.mem_sdiff.mp hclause'
        rcases Finset.mem_union.mp (hFV.combine_effects _ _ hinner) with
          hco | hmore
        · aesop
        · rcases Finset.mem_union.mp (hFV.combine_effects _ _ hmore) with
            heq | heff
          · have ht := hAtom.equalType_effects τo a heq
            rcases Finset.mem_union.mp ht with hτ | ha <;> aesop
          · have ht := hAtom.includedEffect_effects εo χ heff
            rcases Finset.mem_union.mp ht with hεo | hχ <;> aesop
      · rcases Finset.mem_union.mp (hFV.combine_effects _ _ heffects) with
          hsplit | hmore
        · have h := ConstraintSystem.split_freeEffects hFV hAtom
            op εin δ hsplit
          rcases Finset.mem_union.mp h with hεin | hδ <;> aesop
        · rcases Finset.mem_union.mp (hFV.combine_effects _ _ hmore) with
            hδχ | hεrχ
          · have h := hAtom.includedEffect_effects δ χ hδχ
            rcases Finset.mem_union.mp h with hδ | hχ <;> aesop
          · have h := hAtom.includedEffect_effects εr χ hεrχ
            rcases Finset.mem_union.mp h with hεr | hχ <;> aesop

/-- Local clause names disappear from the outer handler constraint. -/
theorem generated_handler_outer_fv_below {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (op : Op) (decl : OpDecl) (sb : Supply)
    (rb rr rc : Output X)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hrT : ∀ i ∈ rr.supportTypes, i < rr.next.types)
    (hrE : ∀ i ∈ rr.supportEffects, i < rr.next.effects)
    (hcT : ∀ i ∈ rc.supportTypes, i < rc.next.types)
    (hcE : ∀ i ∈ rc.supportEffects, i < rc.next.effects)
    (hnextB : rb.next.types ≤ rr.next.types ∧
      rb.next.effects ≤ rr.next.effects)
    (ha : sb.types < rr.next.types)
    (_hδ : sb.effects < rr.next.effects)
    (hχ : sb.effects + 1 < rr.next.effects) :
    let lt := Finset.range rc.next.types \ Finset.range rr.next.types
    let le := Finset.range rc.next.effects \ Finset.range rr.next.effects
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    let C := handlerCondition X op decl
      rb.condition rr.condition rc.condition rr.ty rc.ty a
      rb.effect rr.effect rc.effect δ χ lt le
    (∀ i ∈ X.freeTypes C, i < rr.next.types) ∧
    (∀ i ∈ X.freeEffects C, i < rr.next.effects) := by
  dsimp
  let lt := Finset.range rc.next.types \ Finset.range rr.next.types
  let le := Finset.range rc.next.effects \ Finset.range rr.next.effects
  let a := Ty.var sb.types
  let δ := Poly.Effect.var sb.effects
  let χ := Poly.Effect.var (sb.effects + 1)
  constructor
  · intro i hi
    have h := handlerCondition_freeTypes_refined hFV hAtom
      op decl rb.condition rr.condition rc.condition
      rr.ty rc.ty a rb.effect rr.effect rc.effect δ χ lt le
      i hi
    rcases h with hCin | hCr | hτr | ha' | ⟨hcl, hnot⟩
    · exact lt_of_lt_of_le
        (hbT i (Finset.mem_union_right _ hCin)) hnextB.1
    · exact hrT i (Finset.mem_union_right _ hCr)
    · exact hrT i (Finset.mem_union_left _ hτr)
    · simp [a, Ty.fvTypes] at ha'
      omega
    · have hrc : i < rc.next.types := by
        rcases hcl with hCo | hτo
        · exact hcT i (Finset.mem_union_right _ hCo)
        · exact hcT i (Finset.mem_union_left _ hτo)
      by_contra hbad
      have hloc : i ∈ lt := by
        simp [lt]
        omega
      exact hnot (Finset.mem_union_right _ hloc)
  · intro i hi
    have h := handlerCondition_freeEffects_refined hFV hAtom
      op decl rb.condition rr.condition rc.condition
      rr.ty rc.ty a rb.effect rr.effect rc.effect δ χ lt le
      i hi
    rcases h with hCin | hCr | hτr | ha' | hεin | hεr | hδ' |
      hχ' | ⟨hcl, hnot⟩
    · exact lt_of_lt_of_le
        (hbE i (by simp [Output.supportEffects, hCin])) hnextB.2
    · exact hrE i (by simp [Output.supportEffects, hCr])
    · exact hrE i (by simp [Output.supportEffects, hτr])
    · simp [a, Ty.fvEffects] at ha'
    · exact lt_of_lt_of_le
        (hbE i (by simp [Output.supportEffects, hεin])) hnextB.2
    · exact hrE i (by simp [Output.supportEffects, hεr])
    · simp [δ, Poly.Effect.var] at hδ'
      omega
    · simp [χ, Poly.Effect.var] at hχ'
      omega
    · have hrc : i < rc.next.effects := by
        rcases hcl with hCo | hτo | hεo
        · exact hcE i (by simp [Output.supportEffects, hCo])
        · exact hcE i (by simp [Output.supportEffects, hτo])
        · exact hcE i (by simp [Output.supportEffects, hεo])
      by_contra hbad
      have hloc : i ∈ le := by
        simp [le]
        omega
      exact hnot (Finset.mem_union_right _ hloc)

/-- Rigid operation variables are absent from the outer handler condition. -/
theorem generated_handler_binders_avoid_outer {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (op : Op) (raw : OpDecl) (hc : raw.Closed)
    (rb rr rc : Output X) (lt le : Finset Nat)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hrOldT : ∀ i ∈ rr.supportTypes,
      i < (rb.next.advance raw.typeVars raw.effectVars).types + 1 →
      i < rb.next.types)
    (hrOldE : ∀ i ∈ rr.supportEffects,
      i < (rb.next.advance raw.typeVars raw.effectVars).effects + 2 →
      i < rb.next.effects) :
    let ρ := renameBound raw.typeVars rb.next.types
    let η := renameBound raw.effectVars rb.next.effects
    let decl := raw.alphaRename ρ η
    let sb := rb.next.advance raw.typeVars raw.effectVars
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    let C := handlerCondition X op decl rb.condition rr.condition
      rc.condition rr.ty rc.ty a rb.effect rr.effect rc.effect
      δ χ lt le
    Disjoint decl.typeVars (X.freeTypes C) ∧
    Disjoint decl.effectVars (X.freeEffects C) := by
  dsimp
  let ρ := renameBound raw.typeVars rb.next.types
  let η := renameBound raw.effectVars rb.next.effects
  let decl := raw.alphaRename ρ η
  let sb := rb.next.advance raw.typeVars raw.effectVars
  let a := Ty.var sb.types
  let δ := Poly.Effect.var sb.effects
  let χ := Poly.Effect.var (sb.effects + 1)
  have hinterval := raw.closed_alphaRename_used_interval hc rb.next
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hbind hfree
    have hused : i ∈ decl.usedTypes := by
      change i ∈ decl.typeVars at hbind
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hbind)
    have ⟨hlow, hhigh⟩ := hinterval.1 i hused
    have h := handlerCondition_freeTypes_refined hFV hAtom op decl
      rb.condition rr.condition rc.condition rr.ty rc.ty a
      rb.effect rr.effect rc.effect δ χ lt le i hfree
    rcases h with hCin | hCr | hτr | ha | ⟨_, hnot⟩
    · have := hbT i (Finset.mem_union_right _ hCin)
      omega
    · have := hrOldT i (Finset.mem_union_right _ hCr) (by
        omega)
      omega
    · have := hrOldT i (Finset.mem_union_left _ hτr) (by
        omega)
      omega
    · simp [a, Ty.fvTypes] at ha
      change i = (rb.next.advance raw.typeVars raw.effectVars).types at ha
      omega
    · exact hnot (Finset.mem_union_left _ hbind)
  · apply Finset.disjoint_left.mpr
    intro i hbind hfree
    have hused : i ∈ decl.usedEffects := by
      change i ∈ decl.effectVars at hbind
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hbind)
    have ⟨hlow, hhigh⟩ := hinterval.2 i hused
    have h := handlerCondition_freeEffects_refined hFV hAtom op decl
      rb.condition rr.condition rc.condition rr.ty rc.ty a
      rb.effect rr.effect rc.effect δ χ lt le i hfree
    rcases h with hCin | hCr | hτr | ha | hεin | hεr | hδ | hχ |
      ⟨_, hnot⟩
    · have := hbE i (by simp [Output.supportEffects, hCin])
      omega
    · have := hrOldE i (by simp [Output.supportEffects, hCr]) (by
        omega)
      omega
    · have := hrOldE i (by simp [Output.supportEffects, hτr]) (by
        omega)
      omega
    · simp [a, Ty.fvEffects] at ha
    · have := hbE i (by simp [Output.supportEffects, hεin])
      omega
    · have := hrOldE i (by simp [Output.supportEffects, hεr]) (by
        omega)
      omega
    · simp [δ, Poly.Effect.var] at hδ
      change i = (rb.next.advance raw.typeVars raw.effectVars).effects at hδ
      omega
    · simp [χ, Poly.Effect.var] at hχ
      change i = (rb.next.advance raw.typeVars raw.effectVars).effects + 1 at hχ
      omega
    · exact hnot (Finset.mem_union_left _ hbind)

theorem generated_clauseScope_of_bounds {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (Γ : Context X) (op : Op) (raw : OpDecl) (hc : raw.Closed)
    (rb rr rc : Output X)
    (hΓT : ∀ i ∈ Γ.freeTypes, i < rr.next.types)
    (hΓE : ∀ i ∈ Γ.freeEffects, i < rr.next.effects)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hrT : ∀ i ∈ rr.supportTypes, i < rr.next.types)
    (hrE : ∀ i ∈ rr.supportEffects, i < rr.next.effects)
    (hcT : ∀ i ∈ rc.supportTypes, i < rc.next.types)
    (hcE : ∀ i ∈ rc.supportEffects, i < rc.next.effects)
    (hrOldT : ∀ i ∈ rr.supportTypes,
      i < (rb.next.advance raw.typeVars raw.effectVars).types + 1 →
      i < rb.next.types)
    (hrOldE : ∀ i ∈ rr.supportEffects,
      i < (rb.next.advance raw.typeVars raw.effectVars).effects + 2 →
      i < rb.next.effects)
    (hnextB : rb.next.types ≤ rr.next.types ∧
      rb.next.effects ≤ rr.next.effects)
    (ha : (rb.next.advance raw.typeVars raw.effectVars).types <
      rr.next.types)
    (hχ : (rb.next.advance raw.typeVars raw.effectVars).effects + 1 <
      rr.next.effects) :
    let ρ := renameBound raw.typeVars rb.next.types
    let η := renameBound raw.effectVars rb.next.effects
    let decl := raw.alphaRename ρ η
    let sb := rb.next.advance raw.typeVars raw.effectVars
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    let localTypes :=
      Finset.range rc.next.types \ Finset.range rr.next.types
    let localEffects :=
      Finset.range rc.next.effects \ Finset.range rr.next.effects
    let C := handlerCondition X op decl
      rb.condition rr.condition rc.condition rr.ty rc.ty a
      rb.effect rr.effect rc.effect δ χ localTypes localEffects
    Generic.OpDecl.ClauseScope decl Γ C rb.ty a rb.effect rr.effect δ χ
      localTypes localEffects := by
  dsimp
  let ρ := renameBound raw.typeVars rb.next.types
  let η := renameBound raw.effectVars rb.next.effects
  let decl := raw.alphaRename ρ η
  let sb := rb.next.advance raw.typeVars raw.effectVars
  let a := Ty.var sb.types
  let δ := Poly.Effect.var sb.effects
  let χ := Poly.Effect.var (sb.effects + 1)
  let localTypes := Finset.range rc.next.types \
    Finset.range rr.next.types
  let localEffects := Finset.range rc.next.effects \
    Finset.range rr.next.effects
  let C := handlerCondition X op decl
    rb.condition rr.condition rc.condition rr.ty rc.ty a
    rb.effect rr.effect rc.effect δ χ localTypes localEffects
  have hbind := generated_handler_binders_avoid_outer hFV hAtom op raw hc
    rb rr rc localTypes localEffects hbT hbE hrOldT hrOldE
  have houter := generated_handler_outer_fv_below hFV hAtom op decl sb
    rb rr rc hbT hbE hrT hrE hcT hcE hnextB ha
    (by
      change (rb.next.advance raw.typeVars raw.effectVars).effects <
        rr.next.effects
      omega) hχ
  have hdecl := raw.closed_alphaRename_used_interval hc rb.next
  constructor
  · exact hbind.1
  constructor
  · exact hbind.2
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hlocal hfixed
    have hlow : rr.next.types ≤ i := by
      have hn := (Finset.mem_sdiff.mp hlocal).2
      simpa [localTypes] using hn
    simp only [Finset.mem_union] at hfixed
    rcases hfixed with ((((((hΓ | hC) | hτin) | ha') |
      hdeclVar) | hinput) | houtput)
    · have := hΓT i hΓ; omega
    · have := houter.1 i hC; omega
    · have := hbT i (Finset.mem_union_left _ hτin)
      omega
    · simp [Ty.fvTypes] at ha'
      omega
    · have hu : i ∈ decl.usedTypes := by
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ hdeclVar)
      have := (hdecl.1 i hu).2
      omega
    · have hu : i ∈ decl.usedTypes := by
        exact Finset.mem_union_left _
          (Finset.mem_union_right _ hinput)
      have := (hdecl.1 i hu).2
      omega
    · have hu : i ∈ decl.usedTypes := by
        exact Finset.mem_union_right _ houtput
      have := (hdecl.1 i hu).2
      omega
  · apply Finset.disjoint_left.mpr
    intro i hlocal hfixed
    have hlow : rr.next.effects ≤ i := by
      have hn := (Finset.mem_sdiff.mp hlocal).2
      simpa [localEffects] using hn
    simp only [Finset.mem_union] at hfixed
    have hΓ : i ∈ Γ.freeEffects → False := by
      intro h; have := hΓE i h; omega
    have hC : i ∈ X.freeEffects C → False := by
      intro h; have := houter.2 i h; omega
    have hty : i ∈ rb.ty.fvEffects → False := by
      intro h
      have := hbE i (by simp [Output.supportEffects, h])
      omega
    have hεin : i ∈ rb.effect.vars → False := by
      intro h
      have := hbE i (by simp [Output.supportEffects, h])
      omega
    have hεr : i ∈ rr.effect.vars → False := by
      intro h
      have := hrE i (by simp [Output.supportEffects, h])
      omega
    have hdeclBelow : ∀ j ∈ decl.usedEffects,
        j < rr.next.effects := by
      intro j hj
      have := (hdecl.2 j hj).2
      omega
    have hdeclVar : i ∈ decl.effectVars → False := by
      intro h
      have := hdeclBelow i (Finset.mem_union_left _
        (Finset.mem_union_left _ h))
      omega
    have hinput : i ∈ decl.input.fvEffects → False := by
      intro h
      have := hdeclBelow i (Finset.mem_union_left _
        (Finset.mem_union_right _ h))
      omega
    have houtput : i ∈ decl.output.fvEffects → False := by
      intro h
      have := hdeclBelow i (Finset.mem_union_right _ h)
      omega
    simp only [Ty.fvEffects, Poly.Effect.var,
      Finset.mem_singleton] at hfixed
    rcases hfixed with (((((((((hΓ' | hC') | hty') | ha') |
      hεin') | hεr') | hδ') | hχ') | hdecl') | hin') | hout'
    · exact hΓ hΓ'
    · exact hC hC'
    · exact hty hty'
    · simp at ha'
    · exact hεin hεin'
    · exact hεr hεr'
    · omega
    · omega
    · exact hdeclVar hdecl'
    · exact hinput hin'
    · exact houtput hout'


end SystemFXi.EHMX.Generic
