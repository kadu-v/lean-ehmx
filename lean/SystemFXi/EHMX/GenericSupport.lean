import SystemFXi.EHMX.GenericCompleteness

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

/-- Every successful run stays within its final supply. -/
theorem generate_support_below {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (hrun : generate sig X Γ e s = some r) :
    ∀ ops : Finset Op, e.ops ⊆ ops →
      BoundedInputs sig X Γ ops s →
      (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  fun_induction generate sig X Γ e s generalizing r with
  | case1 Γ i s =>
      intro ops hops hb
      cases hσ : Γ[i]? with
      | none => simp [hσ] at hrun
      | some σ =>
          by_cases hfresh : σ.FreshRename
              (renameBound σ.typeVars s.types)
              (renameBound σ.effectVars s.effects)
          · simp [hσ, hfresh] at hrun
            cases hrun
            have hmem : σ ∈ Γ := List.mem_of_getElem? hσ
            exact Output.variable_support_below hFV hAtom σ s
              (hb.contextTypes σ hmem)
              (hb.contextEffects σ hmem)
          · simp [hσ, hfresh] at hrun
  | case2 Γ n s =>
      intro ops hops hb
      cases hrun
      constructor <;> intro i hi <;>
        simp [Output.supportTypes, Output.supportEffects,
          Ty.fvTypes, Ty.fvEffects,
          hAtom.trivial_types, hAtom.trivial_effects] at hi
  | case3 Γ b s =>
      intro ops hops hb
      cases hrun
      constructor <;> intro i hi <;>
        simp [Output.supportTypes, Output.supportEffects,
          Ty.fvTypes, Ty.fvEffects,
          hAtom.trivial_types, hAtom.trivial_effects] at hi
  | case4 Γ body s a ih =>
      intro ops hops hb
      cases hr : generate sig X (Scheme.mono a :: Γ) body
          {s with types := s.types + 1} with
      | none => simp [hr] at hrun
      | some rb =>
          simp [hr] at hrun
          cases hrun
          have hbodyOps : body.ops ⊆ ops := by
            intro op hop
            exact hops (by simpa [Expr.ops] using hop)
          have hbase : BoundedInputs sig X Γ ops
              {s with types := s.types + 1} :=
            hb.mono (by dsimp; omega)
          have hchild : BoundedInputs sig X
              (Scheme.mono a :: Γ) ops
              {s with types := s.types + 1} := by
            apply hbase.consMono hAtom a
            · intro i hi
              simp [a, Ty.fvTypes] at hi
              dsimp
              omega
            · intro i hi
              simp [a, Ty.fvEffects] at hi
          have hsup := ih hr ops hbodyOps hchild
          have hm := generate_next_mono hr
          have hnext : s.types < rb.next.types := by
            dsimp at hm
            omega
          exact Output.lam_support_below s rb
            hsup.1 hsup.2 hnext
  | case5 Γ f x s ihf ihx =>
      intro ops hops hb
      cases hf : generate sig X Γ f s with
      | none => simp [hf] at hrun
      | some rf =>
          cases hx : generate sig X Γ x rf.next with
          | none => simp [hf, hx] at hrun
          | some rx =>
              simp [hf, hx] at hrun
              cases hrun
              have hfOps : f.ops ⊆ ops := by
                intro op hop
                exact hops (by simp [Expr.ops, hop])
              have hxOps : x.ops ⊆ ops := by
                intro op hop
                exact hops (by simp [Expr.ops, hop])
              have hsf := ihf hf ops hfOps hb
              have hmx := generate_next_mono hf
              have hsx := ihx rf hx ops hxOps (hb.mono hmx)
              have hnext := generate_next_mono hx
              exact Output.app_support_below hFV hAtom rf rx
                hsf.1 hsf.2 hsx.1 hsx.2 hnext
  | case6 Γ e₁ e₂ s ihBound ihVal ihMono =>
      intro ops hops hb
      cases h₁ : generate sig X Γ e₁ s with
      | none => simp [h₁] at hrun
      | some r₁ =>
          have hfirstOps : e₁.ops ⊆ ops := by
            intro op hop
            exact hops (by simp [Expr.ops, hop])
          have hbodyOps : e₂.ops ⊆ ops := by
            intro op hop
            exact hops (by simp [Expr.ops, hop])
          have hs₁ := ihBound h₁ ops hfirstOps hb
          have hbase := hb.mono (generate_next_mono h₁)
          cases hv : e₁.isValue with
          | true =>
              cases h₂ : generate sig X
                  (Scheme.generalize Γ r₁.condition r₁.ty :: Γ)
                  e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at hrun
              | some r₂ =>
                  simp [h₁, hv, h₂] at hrun
                  cases hrun
                  have hctx := hbase.consGeneralize
                    r₁.condition r₁.ty
                    (by simpa [Output.supportTypes] using hs₁.1)
                    (by
                      intro i hi
                      exact hs₁.2 i (by
                        simp [Output.supportEffects] at hi ⊢
                        aesop))
                  have hs₂ := ihVal r₁ h₂ ops hbodyOps hctx
                  exact Output.letVal_support_below hFV Γ r₁ r₂
                    hs₁.1 hs₁.2 hs₂.1 hs₂.2
                    (generate_next_mono h₂)
          | false =>
              cases h₂ : generate sig X
                  (Scheme.mono r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at hrun
              | some r₂ =>
                  simp [h₁, hv, h₂] at hrun
                  cases hrun
                  have hctx := hbase.consMono hAtom r₁.ty
                    (fun i hi => hs₁.1 i
                      (Finset.mem_union_left _ hi))
                    (fun i hi => hs₁.2 i
                      (by simp [Output.supportEffects, hi]))
                  have hs₂ := ihMono r₁ h₂ ops hbodyOps hctx
                  exact Output.letMono_support_below hFV r₁ r₂
                    hs₁.1 hs₁.2 hs₂.1 hs₂.2
                    (generate_next_mono h₂)
  | case7 Γ op e s ih =>
      intro ops hops hb
      cases hd : sig op with
      | none => simp [hd] at hrun
      | some decl =>
          cases he : generate sig X Γ e
              (s.advance decl.typeVars decl.effectVars) with
          | none => simp [hd, he] at hrun
          | some re =>
              simp [hd, he] at hrun
              cases hrun
              have hop : op ∈ ops := hops (by simp [Expr.ops])
              have hchildOps : e.ops ⊆ ops := by
                intro op' hop'
                exact hops (by simp [Expr.ops, hop'])
              have hdecl := hb.signature op hop decl hd
              have hchild := hb.mono ⟨
                Nat.le_of_lt (s.advance_mono
                  decl.typeVars decl.effectVars).1,
                Nat.le_of_lt (s.advance_mono
                  decl.typeVars decl.effectVars).2⟩
              have hsup := ih decl he ops hchildOps hchild
              exact Output.perform_support_below hFV hAtom
                s decl op re hdecl.1 hdecl.2 hsup.1 hsup.2
                (generate_next_mono he)
  | case8 Γ body op ret clause s ihBody ihRet ihClause =>
      intro ops hops hb
      cases hd : sig op with
      | none => simp [hd] at hrun
      | some raw =>
          cases hbody : generate sig X Γ body s with
          | none => simp [hd, hbody] at hrun
          | some rb =>
              let ρ := renameBound raw.typeVars rb.next.types
              let η := renameBound raw.effectVars rb.next.effects
              let decl := raw.alphaRename ρ η
              let sb := rb.next.advance raw.typeVars raw.effectVars
              let a := Ty.var sb.types
              let δ := Poly.Effect.var sb.effects
              let χ := Poly.Effect.var (sb.effects + 1)
              let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
              cases hret : generate sig X
                  (Scheme.mono rb.ty :: Γ) ret sr with
              | none => simp [hd, hbody, hret, sb, sr] at hrun
              | some rr =>
                  cases hclause : generate sig X
                      (Scheme.mono (.arr decl.output χ a) ::
                        Scheme.mono decl.input :: Γ) clause rr.next with
                  | none =>
                      simp [hd, hbody, hret, hclause,
                        ρ, η, decl, sb, a, χ, sr] at hrun
                  | some rc =>
                      let localTypes := Finset.range rc.next.types \
                        Finset.range rr.next.types
                      let localEffects := Finset.range rc.next.effects \
                        Finset.range rr.next.effects
                      let C := handlerCondition X op decl
                        rb.condition rr.condition rc.condition
                        rr.ty rc.ty a rb.effect rr.effect rc.effect
                        δ χ localTypes localEffects
                      have hop : op ∈ ops := hops (by simp [Expr.ops])
                      have hbodyOps : body.ops ⊆ ops := by
                        intro op' h
                        exact hops (by simp [Expr.ops, h])
                      have hretOps : ret.ops ⊆ ops := by
                        intro op' h
                        exact hops (by simp [Expr.ops, h])
                      have hclauseOps : clause.ops ⊆ ops := by
                        intro op' h
                        exact hops (by simp [Expr.ops, h])
                      have hsb := ihBody hbody ops hbodyOps hb
                      have hmBody := generate_next_mono hbody
                      have hbase := hb.mono hmBody
                      have hraw := hbase.signature op hop raw hd
                      have hdecl := OpDecl.alphaRename_used_below_advance
                        raw rb.next hraw.1 hraw.2
                      have hadvance := rb.next.advance_mono
                        raw.typeVars raw.effectVars
                      have hrbSr :
                          rb.next.types ≤ sr.types ∧
                          rb.next.effects ≤ sr.effects := by
                        dsimp [sr, sb]
                        omega
                      have hretBase := hbase.mono hrbSr
                      have hretCtx := hretBase.consMono hAtom rb.ty
                        (fun i hi => lt_of_lt_of_le
                          (hsb.1 i (Finset.mem_union_left _ hi))
                          hrbSr.1)
                        (fun i hi => lt_of_lt_of_le
                          (hsb.2 i (by simp [Output.supportEffects, hi]))
                          hrbSr.2)
                      have hsret := ihRet raw rb hret ops hretOps hretCtx
                      have hmRet := generate_next_mono hret
                      have hsbRr :
                          sb.types ≤ rr.next.types ∧
                          sb.effects ≤ rr.next.effects := by
                        dsimp [sr, sb] at hmRet ⊢
                        omega
                      have hclauseBase : BoundedInputs sig X Γ ops rr.next :=
                        hbase.mono ⟨hrbSr.1.trans hmRet.1,
                          hrbSr.2.trans hmRet.2⟩
                      have hdeclT : ∀ i ∈ decl.usedTypes,
                          i < rr.next.types := by
                        intro i hi
                        exact lt_of_lt_of_le (hdecl.1 i hi) hsbRr.1
                      have hdeclE : ∀ i ∈ decl.usedEffects,
                          i < rr.next.effects := by
                        intro i hi
                        exact lt_of_lt_of_le (hdecl.2 i hi) hsbRr.2
                      have hinputT : ∀ i ∈ decl.input.fvTypes,
                          i < rr.next.types := by
                        intro i hi
                        exact hdeclT i (by simp [OpDecl.usedTypes, hi])
                      have hinputE : ∀ i ∈ decl.input.fvEffects,
                          i < rr.next.effects := by
                        intro i hi
                        exact hdeclE i (by simp [OpDecl.usedEffects, hi])
                      have houtputT : ∀ i ∈ decl.output.fvTypes,
                          i < rr.next.types := by
                        intro i hi
                        exact hdeclT i (by simp [OpDecl.usedTypes, hi])
                      have houtputE : ∀ i ∈ decl.output.fvEffects,
                          i < rr.next.effects := by
                        intro i hi
                        exact hdeclE i (by simp [OpDecl.usedEffects, hi])
                      have hclauseCtx₁ := hclauseBase.consMono hAtom
                        decl.input hinputT hinputE
                      have hclauseCtx := hclauseCtx₁.consMono hAtom
                        (.arr decl.output χ a)
                        (by
                          intro i hi
                          simp [Ty.fvTypes] at hi
                          rcases hi with hout | ha
                          · exact houtputT i hout
                          · simp [a, Ty.fvTypes] at ha
                            have hh := hmRet.1
                            dsimp [sr] at hh
                            omega)
                        (by
                          intro i hi
                          simp [Ty.fvEffects, χ, a,
                            Poly.Effect.var] at hi
                          rcases hi with hχ | hout
                          · have hh := hmRet.2
                            dsimp [sr] at hh
                            omega
                          · exact houtputE i hout)
                      have hsclause := ihClause raw rb rr hclause
                        ops hclauseOps hclauseCtx
                      have hmClause := generate_next_mono hclause
                      have hnextB :
                          rb.next.types ≤ rc.next.types ∧
                          rb.next.effects ≤ rc.next.effects :=
                        ⟨(hrbSr.1.trans hmRet.1).trans hmClause.1,
                          (hrbSr.2.trans hmRet.2).trans hmClause.2⟩
                      have hnextR := hmClause
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hscope : Generic.OpDecl.HandlerScope decl Γ
                          rb.ty a rb.effect rr.effect δ χ
                        · by_cases hclauseScope : Generic.OpDecl.ClauseScope decl Γ C
                            rb.ty a rb.effect rr.effect δ χ
                            localTypes localEffects
                          · simp [hd, hbody, hret, hclause,
                              hsafe, hscope, hclauseScope,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at hrun
                            cases hrun
                            apply Output.handler_support_below hFV hAtom
                              op decl sb rb rr rc
                              localTypes localEffects
                              hsb.1 hsb.2 hsret.1 hsret.2
                              hsclause.1 hsclause.2 hnextB hnextR
                            · dsimp [sr, sb] at hmRet ⊢
                              omega
                            · dsimp [sr, sb] at hmRet ⊢
                              omega
                            · dsimp [sr, sb] at hmRet ⊢
                              omega
                          · simp [hd, hbody, hret, hclause,
                              hsafe, hscope, hclauseScope,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at hrun
                        · simp [hd, hbody, hret, hclause,
                            hsafe, hscope,
                            ρ, η, decl, sb, a, δ, χ, sr] at hrun
                      · simp [hd, hbody, hret,
                          hsafe, ρ, η, sb, sr] at hrun

theorem generateFresh_support_below {sig : Signature}
    {X : ConstraintSystem} (hFV : X.LawfulFV)
    (hAtom : X.LawfulGeneratedFV)
    (Γ : Context X) (e : Expr) (s : Supply) (r : Output X)
    (h : generateFresh sig X Γ e s = some r) :
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  exact generate_support_below hFV hAtom h e.ops
    (by intro i hi; exact hi)
    (BoundedInputs.seed Γ e s)

end SystemFXi.EHMX.Generic
