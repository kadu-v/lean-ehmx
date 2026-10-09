import SystemFXi.EHMX.GenericSupport

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

theorem generate_effect_fresh {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (h : generate sig X Γ e s = some r) :
    ∀ i ∈ r.effect.vars, s.effects ≤ i := by
  fun_induction generate sig X Γ e s generalizing r with
  | case1 Γ i s =>
      cases hσ : Γ[i]? with
      | none => simp [hσ] at h
      | some σ =>
          by_cases hs : σ.FreshRename
              (renameBound σ.typeVars s.types)
              (renameBound σ.effectVars s.effects)
          · simp [hσ, hs] at h
            cases h
            simp
          · simp [hσ, hs] at h
  | case2 Γ n s => cases h; simp
  | case3 Γ b s => cases h; simp
  | case4 Γ body s a ih =>
      cases hr : generate sig X (Scheme.mono a :: Γ) body
          {s with types := s.types + 1} with
      | none => simp [hr] at h
      | some rb =>
          simp [hr] at h
          cases h
          simp
  | case5 Γ f x s ihf ihx =>
      cases hf : generate sig X Γ f s with
      | none => simp [hf] at h
      | some rf =>
          cases hx : generate sig X Γ x rf.next with
          | none => simp [hf, hx] at h
          | some rx =>
              simp [hf, hx] at h
              cases h
              intro i hi
              simp only [Poly.Effect.vars_union, Poly.Effect.var,
                Finset.mem_union, Finset.mem_singleton] at hi
              rcases hi with (hfi | hxi) | hη
              · exact ihf hf i hfi
              · exact (generate_next_mono hf).2.trans
                  (ihx rf hx i hxi)
              · subst i
                exact (generate_next_mono hf).2.trans
                  (generate_next_mono hx).2
  | case6 Γ e₁ e₂ s ihBound ihVal ihMono =>
      cases h₁ : generate sig X Γ e₁ s with
      | none => simp [h₁] at h
      | some r₁ =>
          cases hv : e₁.isValue with
          | true =>
              cases h₂ : generate sig X
                  (Scheme.generalize Γ r₁.condition r₁.ty :: Γ)
                  e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  intro i hi
                  exact (generate_next_mono h₁).2.trans
                    (ihVal r₁ h₂ i hi)
          | false =>
              cases h₂ : generate sig X
                  (Scheme.mono r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  intro i hi
                  simp [Poly.Effect.vars_union] at hi
                  rcases hi with hfirst | hsecond
                  · exact ihBound h₁ i hfirst
                  · exact (generate_next_mono h₁).2.trans
                      (ihMono r₁ h₂ i hsecond)
  | case7 Γ op e s ih =>
      cases hd : sig op with
      | none => simp [hd] at h
      | some decl =>
          cases he : generate sig X Γ e
              (s.advance decl.typeVars decl.effectVars) with
          | none => simp [hd, he] at h
          | some re =>
              simp [hd, he] at h
              cases h
              intro i hi
              simp [Poly.Effect.vars_union] at hi
              exact (Nat.le_of_lt
                (s.advance_mono decl.typeVars decl.effectVars).2).trans
                (ih decl he i hi)
  | case8 Γ body op ret clause s ihBody ihRet ihClause =>
      cases hd : sig op with
      | none => simp [hd] at h
      | some raw =>
          cases hb : generate sig X Γ body s with
          | none => simp [hd, hb] at h
          | some rb =>
              let ρ := renameBound raw.typeVars rb.next.types
              let η := renameBound raw.effectVars rb.next.effects
              let decl := raw.alphaRename ρ η
              let sb := rb.next.advance raw.typeVars raw.effectVars
              let a := Ty.var sb.types
              let δ := Poly.Effect.var sb.effects
              let χ := Poly.Effect.var (sb.effects + 1)
              let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
              cases hr : generate sig X
                  (Scheme.mono rb.ty :: Γ) ret sr with
              | none => simp [hd, hb, hr, sb, sr] at h
              | some rr =>
                  cases hc : generate sig X
                      (Scheme.mono (.arr decl.output χ a) ::
                        Scheme.mono decl.input :: Γ) clause rr.next with
                  | none =>
                      simp [hd, hb, hr, hc, ρ, η, decl, sb, a, χ, sr] at h
                  | some rc =>
                      let localTypes :=
                        Finset.range rc.next.types \ Finset.range rr.next.types
                      let localEffects :=
                        Finset.range rc.next.effects \ Finset.range rr.next.effects
                      let C := handlerCondition X op decl
                        rb.condition rr.condition rc.condition
                        rr.ty rc.ty a rb.effect rr.effect rc.effect
                        δ χ localTypes localEffects
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hs : Generic.OpDecl.HandlerScope decl Γ rb.ty a
                            rb.effect rr.effect δ χ
                        · by_cases hcs : Generic.OpDecl.ClauseScope decl Γ C rb.ty a
                              rb.effect rr.effect δ χ
                              localTypes localEffects
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at h
                            cases h
                            intro i hi
                            simp [Poly.Effect.var] at hi
                            subst i
                            have hm := generate_next_mono hb
                            have ha := rb.next.advance_mono
                              raw.typeVars raw.effectVars
                            omega
                          · simp [hd, hb, hr, hc, hsafe, hs,
                              ρ, η, decl, sb, a, δ, χ, sr] at h
                            exact False.elim (hcs h.1)
                        · simp [hd, hb, hr, hc, hsafe, hs,
                            ρ, η, decl, sb, a, δ, χ, sr] at h
                      · simp [hd, hb, hr, hsafe, ρ, η, sb, sr] at h


theorem generated_handlerScope
    {sig : Signature} {X : ConstraintSystem}
    (Γ : Context X) (ops : Finset Op) (s : Supply)
    (raw : OpDecl) (rb rr : Output X)
    (hb : BoundedInputs sig X Γ ops s)
    (hmono : s.types ≤ rb.next.types ∧
      s.effects ≤ rb.next.effects)
    (hboundT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hboundE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hretFresh : ∀ i ∈ rr.effect.vars,
      (rb.next.advance raw.typeVars raw.effectVars).effects + 2 ≤ i) :
    let ρ := renameBound raw.typeVars rb.next.types
    let η := renameBound raw.effectVars rb.next.effects
    let decl := raw.alphaRename ρ η
    let sb := rb.next.advance raw.typeVars raw.effectVars
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    Generic.OpDecl.HandlerScope decl Γ rb.ty a rb.effect rr.effect δ χ := by
  dsimp
  constructor
  · rw [Finset.disjoint_left]
    intro i hi hother
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    have hlow : rb.next.types <
        renameBound raw.typeVars rb.next.types j := by
      simp [renameBound, hj]
      omega
    have hup : renameBound raw.typeVars rb.next.types j <
        (rb.next.advance raw.typeVars raw.effectVars).types :=
      (rb.next.advance_above_renamed raw.typeVars raw.effectVars).1 j hj
    simp only [Finset.mem_union, Ty.fvTypes] at hother
    rcases hother with (hΓ | hτ) | ha
    · exact (not_lt_of_ge (hmono.1.trans
        (Nat.le_of_lt hlow)))
        ((hb.context_free_below).1 _ hΓ)
    · have ht := hboundT _ (Finset.mem_union_left _ hτ)
      omega
    · simp at ha
      omega
  · rw [Finset.disjoint_left]
    intro i hi hother
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    have hlow : rb.next.effects <
        renameBound raw.effectVars rb.next.effects j := by
      simp [renameBound, hj]
      omega
    have hup : renameBound raw.effectVars rb.next.effects j <
        (rb.next.advance raw.typeVars raw.effectVars).effects :=
      (rb.next.advance_above_renamed raw.typeVars raw.effectVars).2 j hj
    simp only [Finset.mem_union, Ty.fvEffects] at hother
    rcases hother with ((((((hΓ | hτ) | ha) | hεin) | hεr) | hδ) | hχ)
    · have ht := (hb.context_free_below).2 _ hΓ
      omega
    · have ht := hboundE _ (by
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ hτ))
      omega
    · simp at ha
    · have ht := hboundE _ (by
        exact Finset.mem_union_left _
          (Finset.mem_union_right _ hεin))
      omega
    · have ht := hretFresh _ hεr
      omega
    · simp [Poly.Effect.var] at hδ
      omega
    · simp [Poly.Effect.var] at hχ
      omega


theorem generated_handlerScope_of_runs
    {sig : Signature} {X : ConstraintSystem}
    (Γ : Context X) (ops : Finset Op) (s : Supply)
    (raw : OpDecl) (body ret : Expr) (rb rr : Output X)
    (hb : BoundedInputs sig X Γ ops s)
    (hbody : generate sig X Γ body s = some rb)
    (hboundT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hboundE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hret : generate sig X (Scheme.mono rb.ty :: Γ) ret
      ⟨(rb.next.advance raw.typeVars raw.effectVars).types + 1,
        (rb.next.advance raw.typeVars raw.effectVars).effects + 2⟩ =
      some rr) :
    let ρ := renameBound raw.typeVars rb.next.types
    let η := renameBound raw.effectVars rb.next.effects
    let decl := raw.alphaRename ρ η
    let sb := rb.next.advance raw.typeVars raw.effectVars
    Generic.OpDecl.HandlerScope decl Γ rb.ty (.var sb.types) rb.effect rr.effect
      (Poly.Effect.var sb.effects)
      (Poly.Effect.var (sb.effects + 1)) := by
  exact generated_handlerScope Γ ops s raw rb rr hb
    (generate_next_mono hbody) hboundT hboundE
    (generate_effect_fresh hret)


end SystemFXi.EHMX.Generic
