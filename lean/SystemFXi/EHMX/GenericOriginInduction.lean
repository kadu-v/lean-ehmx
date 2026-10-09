import SystemFXi.EHMX.GenericOrigin

set_option maxHeartbeats 1000000

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

theorem generate_support_origin {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed)
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (hrun : generate sig X Γ e s = some r) :
    (∀ i ∈ r.supportTypes, i < s.types → i ∈ Γ.freeTypes) ∧
    (∀ i ∈ r.supportEffects, i < s.effects → i ∈ Γ.freeEffects) := by
  fun_induction generate sig X Γ e s generalizing r with
  | case1 Γ i s =>
      change generate sig X Γ (.var i) s = some r at hrun
      exact generate_variable_old_support (sig := sig)
        hFV hAtom Γ i s r hrun
  | case2 Γ n s =>
      cases hrun
      constructor <;> intro i hi <;>
        simp [Output.supportTypes, Output.supportEffects,
          Ty.fvTypes, Ty.fvEffects,
          hAtom.trivial_types, hAtom.trivial_effects] at hi
  | case3 Γ b s =>
      cases hrun
      constructor <;> intro i hi <;>
        simp [Output.supportTypes, Output.supportEffects,
          Ty.fvTypes, Ty.fvEffects,
          hAtom.trivial_types, hAtom.trivial_effects] at hi
  | case4 Γ body s a ih =>
      cases hr : generate sig X (Scheme.mono a :: Γ) body
          {s with types := s.types + 1} with
      | none => simp [hr] at hrun
      | some rb =>
          simp [hr] at hrun
          cases hrun
          have hchild := ih hr
          apply Output.lam_old_support Γ s rb
          · intro i hi hsmall
            have hctx := hchild.1 i hi (by dsimp; omega)
            rw [Context.freeTypes_cons] at hctx
            rcases Finset.mem_union.mp hctx with hmono | hΓ
            · simp [Scheme.mono, Scheme.freeTypes,
                hAtom.trivial_types, a, Ty.fvTypes] at hmono
              omega
            · exact hΓ
          · intro i hi hsmall
            have hctx := hchild.2 i hi (by dsimp; omega)
            rw [Context.freeEffects_cons] at hctx
            rcases Finset.mem_union.mp hctx with hmono | hΓ
            · simp [Scheme.mono, Scheme.freeEffects,
                hAtom.trivial_effects, a, Ty.fvEffects] at hmono
            · exact hΓ
  | case5 Γ f x s ihf ihx =>
      cases hf : generate sig X Γ f s with
      | none => simp [hf] at hrun
      | some rf =>
          cases hx : generate sig X Γ x rf.next with
          | none => simp [hf, hx] at hrun
          | some rx =>
              simp [hf, hx] at hrun
              cases hrun
              have hmF := generate_next_mono hf
              have hmX := generate_next_mono hx
              have hfirst := ihf hf
              have hsecond := ihx rf hx
              apply Output.app_old_support hFV hAtom Γ s rf rx
                ⟨hmF.1.trans hmX.1, hmF.2.trans hmX.2⟩
                hfirst.1 hfirst.2
              · intro i hi hsmall
                exact hsecond.1 i hi (lt_of_lt_of_le hsmall hmF.1)
              · intro i hi hsmall
                exact hsecond.2 i hi (lt_of_lt_of_le hsmall hmF.2)
  | case6 Γ e₁ e₂ s ihBound ihVal ihMono =>
      cases h₁ : generate sig X Γ e₁ s with
      | none => simp [h₁] at hrun
      | some r₁ =>
          have hm := generate_next_mono h₁
          have hfirst := ihBound h₁
          cases hv : e₁.isValue with
          | true =>
              cases h₂ : generate sig X
                  (Scheme.generalize Γ r₁.condition r₁.ty :: Γ)
                  e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at hrun
              | some r₂ =>
                  simp [h₁, hv, h₂] at hrun
                  cases hrun
                  have hsecond := ihVal r₁ h₂
                  have hgen := Scheme.generalize_free_subset_context
                    Γ r₁.condition r₁.ty
                  apply Output.letVal_old_support hFV Γ s r₁ r₂
                  · intro i hi hsmall
                    have hctx := hsecond.1 i hi
                      (lt_of_lt_of_le hsmall hm.1)
                    rw [Context.freeTypes_cons] at hctx
                    rcases Finset.mem_union.mp hctx with hσ | hΓ
                    · exact hgen.1 hσ
                    · exact hΓ
                  · intro i hi hsmall
                    have hctx := hsecond.2 i hi
                      (lt_of_lt_of_le hsmall hm.2)
                    rw [Context.freeEffects_cons] at hctx
                    rcases Finset.mem_union.mp hctx with hσ | hΓ
                    · exact hgen.2 hσ
                    · exact hΓ
          | false =>
              cases h₂ : generate sig X
                  (Scheme.mono r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at hrun
              | some r₂ =>
                  simp [h₁, hv, h₂] at hrun
                  cases hrun
                  have hsecond := ihMono r₁ h₂
                  apply Output.letMono_old_support hFV Γ s r₁ r₂
                    hfirst.1 hfirst.2
                  · intro i hi hsmall
                    have hctx := hsecond.1 i hi
                      (lt_of_lt_of_le hsmall hm.1)
                    rw [Context.freeTypes_cons] at hctx
                    rcases Finset.mem_union.mp hctx with hσ | hΓ
                    · have hty : i ∈ r₁.ty.fvTypes := by
                        simpa [Scheme.mono, Scheme.freeTypes,
                          hAtom.trivial_types] using hσ
                      exact hfirst.1 i (Finset.mem_union_left _ hty) hsmall
                    · exact hΓ
                  · intro i hi hsmall
                    have hctx := hsecond.2 i hi
                      (lt_of_lt_of_le hsmall hm.2)
                    rw [Context.freeEffects_cons] at hctx
                    rcases Finset.mem_union.mp hctx with hσ | hΓ
                    · have hty : i ∈ r₁.ty.fvEffects := by
                        simpa [Scheme.mono, Scheme.freeEffects,
                          hAtom.trivial_effects] using hσ
                      exact hfirst.2 i (by
                        simp [Output.supportEffects, hty]) hsmall
                    · exact hΓ
  | case7 Γ op e s ih =>
      cases hd : sig op with
      | none => simp [hd] at hrun
      | some raw =>
          let sa := s.advance raw.typeVars raw.effectVars
          cases he : generate sig X Γ e sa with
          | none => simp [hd, he, sa] at hrun
          | some re =>
              simp [hd, he, sa] at hrun
              cases hrun
              have hm := s.advance_mono raw.typeVars raw.effectVars
              have hchild := ih raw he
              apply Output.perform_old_support hFV hAtom Γ s op raw
                (hClosed op raw hd) re
              · intro i hi hsmall
                exact hchild.1 i hi (lt_of_lt_of_le hsmall
                  (Nat.le_of_lt hm.1))
              · intro i hi hsmall
                exact hchild.2 i hi (lt_of_lt_of_le hsmall
                  (Nat.le_of_lt hm.2))
  | case8 Γ body op ret clause s ihBody ihRet ihClause =>
      cases hd : sig op with
      | none => simp [hd] at hrun
      | some raw =>
          cases hb : generate sig X Γ body s with
          | none => simp [hd, hb] at hrun
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
              | none => simp [hd, hb, hr, sb, sr] at hrun
              | some rr =>
                  cases hc : generate sig X
                      (Scheme.mono (.arr decl.output χ a) ::
                        Scheme.mono decl.input :: Γ)
                      clause rr.next with
                  | none =>
                      simp [hd, hb, hr, hc, ρ, η, decl,
                        sb, a, χ, sr] at hrun
                  | some rc =>
                      let localTypes := Finset.range rc.next.types \
                        Finset.range rr.next.types
                      let localEffects := Finset.range rc.next.effects \
                        Finset.range rr.next.effects
                      let C := handlerCondition X op decl
                        rb.condition rr.condition rc.condition
                        rr.ty rc.ty a rb.effect rr.effect rc.effect
                        δ χ localTypes localEffects
                      have hfirst := ihBody hb
                      have hsecond := ihRet raw rb hr
                      have hthird := ihClause raw rb rr hc
                      have hmBody := generate_next_mono hb
                      have hmRet := generate_next_mono hr
                      have ha := rb.next.advance_mono
                        raw.typeVars raw.effectVars
                      have hsrT : s.types ≤ sr.types := by
                        dsimp [sr, sb]
                        omega
                      have hsrE : s.effects ≤ sr.effects := by
                        dsimp [sr, sb]
                        omega
                      have hrrT : s.types ≤ rr.next.types := by
                        exact hsrT.trans hmRet.1
                      have hrrE : s.effects ≤ rr.next.effects := by
                        exact hsrE.trans hmRet.2
                      have hretT : ∀ i ∈ rr.supportTypes,
                          i < s.types → i ∈ Γ.freeTypes := by
                        intro i hi hsmall
                        have hctx := hsecond.1 i hi
                          (lt_of_lt_of_le hsmall hsrT)
                        rw [Context.freeTypes_cons] at hctx
                        rcases Finset.mem_union.mp hctx with hmono | hΓ
                        · have hty : i ∈ rb.ty.fvTypes := by
                            simpa [Scheme.mono, Scheme.freeTypes,
                              hAtom.trivial_types] using hmono
                          exact hfirst.1 i
                            (Finset.mem_union_left _ hty) hsmall
                        · exact hΓ
                      have hretE : ∀ i ∈ rr.supportEffects,
                          i < s.effects → i ∈ Γ.freeEffects := by
                        intro i hi hsmall
                        have hctx := hsecond.2 i hi
                          (lt_of_lt_of_le hsmall hsrE)
                        rw [Context.freeEffects_cons] at hctx
                        rcases Finset.mem_union.mp hctx with hmono | hΓ
                        · have hty : i ∈ rb.ty.fvEffects := by
                            simpa [Scheme.mono, Scheme.freeEffects,
                              hAtom.trivial_effects] using hmono
                          exact hfirst.2 i
                            (by simp [Output.supportEffects, hty]) hsmall
                        · exact hΓ
                      have hraw := hClosed op raw hd
                      have hinterval :=
                        raw.closed_alphaRename_used_interval hraw rb.next
                      have hclauseT : ∀ i ∈ rc.supportTypes,
                          i < s.types → i ∈ Γ.freeTypes := by
                        intro i hi hsmall
                        have hctx := hthird.1 i hi
                          (lt_of_lt_of_le hsmall hrrT)
                        rw [Context.freeTypes_cons,
                          Context.freeTypes_cons] at hctx
                        rcases Finset.mem_union.mp hctx with hk | hrest
                        · have hk' : i ∈ (Ty.arr decl.output χ a).fvTypes := by
                            simpa [Scheme.mono, Scheme.freeTypes,
                              hAtom.trivial_types] using hk
                          simp [Ty.fvTypes] at hk'
                          rcases hk' with hout | hnew
                          · have hused : i ∈ decl.usedTypes := by
                              simp [OpDecl.usedTypes, hout]
                            have hgt := (hinterval.1 i hused).1
                            omega
                          · simp [a, Ty.fvTypes] at hnew
                            dsimp [sb] at hnew
                            omega
                        · rcases Finset.mem_union.mp hrest with hx | hΓ
                          · have hx' : i ∈ decl.input.fvTypes := by
                              simpa [Scheme.mono, Scheme.freeTypes,
                                hAtom.trivial_types] using hx
                            have hused : i ∈ decl.usedTypes := by
                              simp [OpDecl.usedTypes, hx']
                            have hgt := (hinterval.1 i hused).1
                            omega
                          · exact hΓ
                      have hclauseE : ∀ i ∈ rc.supportEffects,
                          i < s.effects → i ∈ Γ.freeEffects := by
                        intro i hi hsmall
                        have hctx := hthird.2 i hi
                          (lt_of_lt_of_le hsmall hrrE)
                        rw [Context.freeEffects_cons,
                          Context.freeEffects_cons] at hctx
                        rcases Finset.mem_union.mp hctx with hk | hrest
                        · have hk' : i ∈ (Ty.arr decl.output χ a).fvEffects := by
                            simpa [Scheme.mono, Scheme.freeEffects,
                              hAtom.trivial_effects] using hk
                          simp [Ty.fvEffects, a] at hk'
                          rcases hk' with hout | hnew
                          · have hused : i ∈ decl.usedEffects := by
                              simp [OpDecl.usedEffects, hout]
                            have hgt := (hinterval.2 i hused).1
                            omega
                          · simp [χ, Poly.Effect.var, sb] at hnew
                            omega
                        · rcases Finset.mem_union.mp hrest with hx | hΓ
                          · have hx' : i ∈ decl.input.fvEffects := by
                              simpa [Scheme.mono, Scheme.freeEffects,
                                hAtom.trivial_effects] using hx
                            have hused : i ∈ decl.usedEffects := by
                              simp [OpDecl.usedEffects, hx']
                            have hgt := (hinterval.2 i hused).1
                            omega
                          · exact hΓ
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hs : Generic.OpDecl.HandlerScope decl Γ
                            rb.ty a rb.effect rr.effect δ χ
                        · by_cases hcs : Generic.OpDecl.ClauseScope decl Γ C
                              rb.ty a rb.effect rr.effect δ χ
                              localTypes localEffects
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at hrun
                            cases hrun
                            exact Output.handler_old_support hFV hAtom
                              Γ op decl s sb rb rr rc
                              localTypes localEffects
                              (by dsimp [sb]; omega)
                              (by dsimp [sb]; omega)
                              hfirst.1 hfirst.2 hretT hretE
                              hclauseT hclauseE
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at hrun
                        · simp [hd, hb, hr, hsafe, hs,
                            ρ, η, decl, sb, a, δ, χ, sr] at hrun
                      · simp [hd, hb, hr, hsafe,
                          ρ, η, sb, sr] at hrun

theorem generated_return_old_support
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed)
    (Γ : Context X) (raw : OpDecl) (rb rr : Output X)
    (ret : Expr)
    (hΓT : ∀ i ∈ Γ.freeTypes, i < rb.next.types)
    (hΓE : ∀ i ∈ Γ.freeEffects, i < rb.next.effects)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hr : generate sig X (Scheme.mono rb.ty :: Γ) ret
      ⟨(rb.next.advance raw.typeVars raw.effectVars).types + 1,
        (rb.next.advance raw.typeVars raw.effectVars).effects + 2⟩ =
      some rr) :
    (∀ i ∈ rr.supportTypes,
      i < (rb.next.advance raw.typeVars raw.effectVars).types + 1 →
      i < rb.next.types) ∧
    (∀ i ∈ rr.supportEffects,
      i < (rb.next.advance raw.typeVars raw.effectVars).effects + 2 →
      i < rb.next.effects) := by
  have h := generate_support_origin hFV hAtom hClosed hr
  exact Output.return_old_below_body hAtom Γ rb rr
    ⟨(rb.next.advance raw.typeVars raw.effectVars).types + 1,
      (rb.next.advance raw.typeVars raw.effectVars).effects + 2⟩
    hΓT hΓE hbT hbE h.1 h.2

end SystemFXi.EHMX.Generic
