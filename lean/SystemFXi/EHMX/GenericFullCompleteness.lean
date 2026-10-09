import SystemFXi.EHMX.GenericHandlerSuccess
import SystemFXi.EHMX.GenericHandlerBridge

set_option maxHeartbeats 1000000

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

theorem Typing.generate_complete
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed)
    {C : X.Formula} {Γd : Context X}
    {e : Expr} {τ : Ty} {ε : Effect}
    (h : Typing sig X C Γd e τ ε) :
    ∀ (Γg : Context X) (ops : Finset Op) (s : Supply),
      Γg.length = Γd.length →
      e.ops ⊆ ops →
      BoundedInputs sig X Γg ops s →
      ∃ r : Output X,
        generate sig X Γg e s = some r ∧
        r.CoversAt Γg Γd C s τ ε := by
  induction h with
  | var hlookup hadm hfresh hent =>
      intro Γg ops s hlen hops hb
      obtain ⟨σg, hlookupG⟩ :=
        Context.lookup_of_length_eq Γg _ _ hlen _ hlookup
      exact generate_var_coversAt hlookupG hlookup
        _ _ hadm hfresh _ hent ops s hb
  | int n =>
      intro Γg ops s hlen hops hb
      refine ⟨⟨.base .int, ∅, X.trivial, s⟩,
        by simp [generate], ?_⟩
      intro vg vd hctx hC
      exact ⟨vg, (fun _ _ => rfl), (fun _ _ => rfl),
        (X.trivial_iff vg).2 trivial, rfl, rfl⟩
  | bool b =>
      intro Γg ops s hlen hops hb
      refine ⟨⟨.base .bool, ∅, X.trivial, s⟩,
        by simp [generate], ?_⟩
      intro vg vd hctx hC
      exact ⟨vg, (fun _ _ => rfl), (fun _ _ => rfl),
        (X.trivial_iff vg).2 trivial, rfl, rfl⟩
  | lam _ ih =>
      intro Γg ops s hlen hops hb
      let aG := Ty.var s.types
      let sb : Supply := {s with types := s.types + 1}
      have hbodyOps : _ := hops
      have hbase : BoundedInputs sig X Γg ops sb :=
        hb.mono (by dsimp [sb]; omega)
      have hchild : BoundedInputs sig X
          (Scheme.mono aG :: Γg) ops sb := by
        apply hbase.consMono hAtom aG
        · intro i hi
          simp [aG, Ty.fvTypes] at hi
          dsimp [sb]
          omega
        · intro i hi
          simp [aG, Ty.fvEffects] at hi
      rcases ih (Scheme.mono aG :: Γg) ops sb
          (by simp [hlen]) hbodyOps hchild with
        ⟨rb, hr, hcov⟩
      refine ⟨⟨.arr aG rb.effect rb.ty, ∅,
        rb.condition, rb.next⟩, ?_, ?_⟩
      · simp [generate, aG, sb, hr]
      · exact Output.CoversAt.lam Γg _ _ ops s rb
          _ _ _ hb hcov
  | app _ _ ihf ihx =>
      intro Γg ops s hlen hops hb
      rcases ihf Γg ops s hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb with
        ⟨rf, hrf, hcovF⟩
      have hstart := generate_next_mono hrf
      have hbX := hb.mono hstart
      rcases ihx Γg ops rf.next hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hbX with
        ⟨rx, hrx, hcovX⟩
      have hfBound := generate_support_below hFV hAtom
        hrf ops (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb
      have hxBound := generate_support_below hFV hAtom
        hrx ops (by intro op hop; exact hops (by simp [Expr.ops, hop])) hbX
      have hnext := generate_next_mono hrx
      refine ⟨⟨.var rx.next.types,
        rf.effect ∪ rx.effect ∪ Poly.Effect.var rx.next.effects,
        X.combine (X.combine rf.condition rx.condition)
          (X.equalType rf.ty
            (.arr rx.ty (Poly.Effect.var rx.next.effects)
              (.var rx.next.types))),
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩,
        ?_, ?_⟩
      · simp [generate, hrf, hrx]
      · exact Output.CoversAt.app Γg _ _ ops s rf rx
          _ _ _ _ _ hb hfBound hxBound hstart hnext
          hcovF hcovX
  | perform =>
      rename_i cPerf ctxPerf op raw ρd ηd ePerf effPerf hsig hadm hbody ih
      intro Γg ops s hlen hops hb
      have hop : op ∈ ops := hops (by simp [Expr.ops])
      let sa := s.advance raw.typeVars raw.effectVars
      have hchild : BoundedInputs sig X Γg ops sa :=
        hb.mono ⟨Nat.le_of_lt (s.advance_mono
          raw.typeVars raw.effectVars).1,
          Nat.le_of_lt (s.advance_mono
          raw.typeVars raw.effectVars).2⟩
      rcases ih Γg ops sa hlen
          (by intro op' hop'; exact hops (by simp [Expr.ops, hop']))
          hchild with ⟨re, hr, hcov⟩
      refine ⟨⟨raw.output.rename
          (renameBound raw.typeVars s.types)
          (renameBound raw.effectVars s.effects),
          Poly.Effect.singleton op ∪ re.effect,
          X.combine re.condition
            (X.equalType re.ty (raw.input.rename
              (renameBound raw.typeVars s.types)
              (renameBound raw.effectVars s.effects))),
          re.next⟩, ?_, ?_⟩
      · simp [generate, hsig, hr, sa]
      · exact Output.CoversAt.perform Γg _ _ ops s
          op raw _ _ re _ hb hop hsig (hClosed op raw hsig)
          hadm hcov
  | letVal hv _ _ ih₁ ih₂ =>
      intro Γg ops s hlen hops hb
      rcases ih₁ Γg ops s hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb with
        ⟨r₁, hr₁, hcov₁⟩
      have hstart := generate_next_mono hr₁
      have h₁Bound := generate_support_below hFV hAtom
        hr₁ ops (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb
      have hctx := (hb.mono hstart).consGeneralize
        r₁.condition r₁.ty
        (by simpa [Output.supportTypes] using h₁Bound.1)
        (by
          intro i hi
          exact h₁Bound.2 i (by
            simp [Output.supportEffects] at hi ⊢
            aesop))
      rcases ih₂
          (Scheme.generalize Γg r₁.condition r₁.ty :: Γg)
          ops r₁.next (by simp [hlen])
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hctx with
        ⟨r₂, hr₂, hcov₂⟩
      refine ⟨⟨r₂.ty, r₂.effect,
        X.combine (Scheme.residual Γg r₁.condition r₁.ty)
          r₂.condition, r₂.next⟩, ?_, ?_⟩
      · simp [generate, hr₁, Expr.isValue_iff.mpr hv, hr₂]
      · exact Output.CoversAt.letVal hFV Γg _ _ _
          ops s r₁ r₂ _ _ _ hb hstart hcov₁ hcov₂
  | letMono hnv _ _ ih₁ ih₂ =>
      intro Γg ops s hlen hops hb
      rcases ih₁ Γg ops s hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb with
        ⟨r₁, hr₁, hcov₁⟩
      have hstart := generate_next_mono hr₁
      have h₁Bound := generate_support_below hFV hAtom
        hr₁ ops (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb
      have hctx := (hb.mono hstart).consMono hAtom r₁.ty
        (fun i hi => h₁Bound.1 i (Finset.mem_union_left _ hi))
        (fun i hi => h₁Bound.2 i
          (by simp [Output.supportEffects, hi]))
      rcases ih₂ (Scheme.mono r₁.ty :: Γg)
          ops r₁.next (by simp [hlen])
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hctx with
        ⟨r₂, hr₂, hcov₂⟩
      refine ⟨⟨r₂.ty, r₁.effect ∪ r₂.effect,
        X.combine r₁.condition r₂.condition, r₂.next⟩,
        ?_, ?_⟩
      · simp [generate, hr₁, Expr.isValue_iff, hnv, hr₂]
      · exact Output.CoversAt.letMono Γg _ _ ops s
          r₁ r₂ _ _ _ _ hb h₁Bound hstart hcov₁ hcov₂
  | @handle C D Γ body op ret clause raw decl ρd ηd τin aD τo
      εin εr εo δd χd localTd localEd hsig hadm hsafe hren
      hscope hclscope hbody hret hclause hproj hsplit
      hδ hε ihb ihr ihc =>
      subst decl
      intro Γg ops s hlen hops hb
      have hbodyOps : body.ops ⊆ ops := by
        intro op' hop'
        exact hops (by simp [Expr.ops, hop'])
      have hretOps : ret.ops ⊆ ops := by
        intro op' hop'
        exact hops (by simp [Expr.ops, hop'])
      have hclauseOps : clause.ops ⊆ ops := by
        intro op' hop'
        exact hops (by simp [Expr.ops, hop'])
      rcases ihb Γg ops s hlen hbodyOps hb with
        ⟨rb, hrunB, hcovB⟩
      have hbBound := generate_support_below hFV hAtom hrunB
        ops hbodyOps hb
      have hmB := generate_next_mono hrunB
      let ρg := renameBound raw.typeVars rb.next.types
      let ηg := renameBound raw.effectVars rb.next.effects
      let declg := raw.alphaRename ρg ηg
      let sb := rb.next.advance raw.typeVars raw.effectVars
      let aG := Ty.var sb.types
      let δg := Poly.Effect.var sb.effects
      let χg := Poly.Effect.var (sb.effects + 1)
      let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
      have hraw := hClosed op raw hsig
      have hbaseR : BoundedInputs sig X Γg ops sr := by
        apply hb.mono
        have h := rb.next.advance_mono raw.typeVars raw.effectVars
        dsimp [sr, sb]
        omega
      have hretCtx : BoundedInputs sig X
          (Scheme.mono rb.ty :: Γg) ops sr := by
        apply hbaseR.consMono hAtom rb.ty
        · intro i hi
          have h := hbBound.1 i (Finset.mem_union_left _ hi)
          have ha := rb.next.advance_mono
            raw.typeVars raw.effectVars
          dsimp [sr, sb]
          omega
        · intro i hi
          have h := hbBound.2 i (by
            simp [Output.supportEffects, hi])
          have ha := rb.next.advance_mono
            raw.typeVars raw.effectVars
          dsimp [sr, sb]
          omega
      rcases ihr (Scheme.mono rb.ty :: Γg) ops sr
          (by simp [hlen]) hretOps hretCtx with
        ⟨rr, hrunR, hcovR⟩
      have hrBound := generate_support_below hFV hAtom hrunR
        ops hretOps hretCtx
      have hmR := generate_next_mono hrunR
      have hinterval := raw.closed_alphaRename_used_interval
        hraw rb.next
      have hbaseC : BoundedInputs sig X Γg ops rr.next := by
        apply hb.mono
        have ha := rb.next.advance_mono
          raw.typeVars raw.effectVars
        dsimp [sr, sb] at hmR
        omega
      have hinputT : ∀ i ∈ declg.input.fvTypes,
          i < rr.next.types := by
        intro i hi
        have h := (hinterval.1 i (by
          exact Finset.mem_union_left _
            (Finset.mem_union_right _ hi))).2
        dsimp [sr, sb] at hmR
        omega
      have hinputE : ∀ i ∈ declg.input.fvEffects,
          i < rr.next.effects := by
        intro i hi
        have h := (hinterval.2 i (by
          exact Finset.mem_union_left _
            (Finset.mem_union_right _ hi))).2
        dsimp [sr, sb] at hmR
        omega
      have houtputT : ∀ i ∈ declg.output.fvTypes,
          i < rr.next.types := by
        intro i hi
        have h := (hinterval.1 i (by
          exact Finset.mem_union_right _ hi)).2
        dsimp [sr, sb] at hmR
        omega
      have houtputE : ∀ i ∈ declg.output.fvEffects,
          i < rr.next.effects := by
        intro i hi
        have h := (hinterval.2 i (by
          exact Finset.mem_union_right _ hi)).2
        dsimp [sr, sb] at hmR
        omega
      have hclauseCtx : BoundedInputs sig X
          (Scheme.mono (.arr declg.output χg aG) ::
            Scheme.mono declg.input :: Γg) ops rr.next := by
        apply (hbaseC.consMono hAtom declg.input hinputT hinputE).consMono hAtom
          (.arr declg.output χg aG)
        · intro i hi
          simp [Ty.fvTypes] at hi
          rcases hi with hout | ha
          · exact houtputT i hout
          · simp [aG, Ty.fvTypes, sb] at ha
            dsimp [sr, sb] at hmR
            omega
        · intro i hi
          simp [Ty.fvEffects, χg, aG,
            Poly.Effect.var] at hi
          rcases hi with hχ | hout
          · dsimp [sr, sb] at hmR
            simp [sb] at hχ
            omega
          · exact houtputE i hout
      rcases ihc
          (Scheme.mono (.arr declg.output χg aG) ::
            Scheme.mono declg.input :: Γg)
          ops rr.next (by simp [hlen])
          hclauseOps hclauseCtx with
        ⟨rc, hrunC, hcovC⟩
      have hcBound := generate_support_below hFV hAtom hrunC
        ops hclauseOps hclauseCtx
      obtain ⟨r, hrun⟩ := generate_handle_of_runs
        hFV hAtom hClosed Γg body ret clause op raw s rb rr rc ops
        hb hsig hrunB hrunR hrunC hbBound hrBound hcBound
      refine ⟨r, hrun, ?_⟩
      simp [generate, hsig, hrunB, hrunR, hrunC,
        ρg, ηg, declg, sb, aG, χg, sr] at hrun
      rcases hrun with ⟨_, _, _, heq⟩
      cases heq
      intro vg vd hctx hC
      rcases hcovB vg vd hctx hC with
        ⟨wb, hbFixT, hbFixE, hbC, hbTy, hbEff⟩
      let v0 := wb.assignAt sb (aD.eval vd)
        (δd.eval vd.effects)
      let v1 : Valuation :=
        ⟨v0.types, Function.update v0.effects
          (sb.effects + 1) (χd.eval vd.effects)⟩
      have hadvance := rb.next.advance_mono
        raw.typeVars raw.effectVars
      have h0fixed := Valuation.assignAt_preserves_below
        wb sb (aD.eval vd) (δd.eval vd.effects)
      have hbelowBTypes : ∀ i, i < rb.next.types →
          wb.types i = v1.types i := by
        intro i hi
        exact h0fixed.1 i (by dsimp [sb] at *; omega)
      have hbelowBEffects : ∀ i, i < rb.next.effects →
          wb.effects i = v1.effects i := by
        intro i hi
        have hne : i ≠ sb.effects + 1 := by
          dsimp [sb] at *
          omega
        have h0 := h0fixed.2 i (by dsimp [sb] at *; omega)
        change wb.effects i = v0.effects i at h0
        simpa [v1, Function.update, hne] using h0
      have hframeB := rb.semantic_frame_of_below wb v1
        hbBound.1 hbBound.2 hbelowBTypes hbelowBEffects
      have hctxV1 : Γg.MoreGeneralAt Γ v1 vd := by
        apply Context.moreGeneralAt_below           Γg Γ ops s hb vg v1 vd hctx
        · intro i hi
          exact (hbFixT i hi).trans
            (hbelowBTypes i (by omega))
        · intro i hi
          exact (hbFixE i hi).trans
            (hbelowBEffects i (by omega))
      have hmonoTop :
          (Scheme.mono (X := X) rb.ty).MoreGeneralAt
            (Scheme.mono τin) v1 vd := by
        apply (Scheme.mono_moreGeneralAt_iff rb.ty τin v1 vd).mpr
        exact hframeB.2.1.symm.trans hbTy
      have hctxRet : Context.MoreGeneralAt
          (Scheme.mono rb.ty :: Γg)
            (Scheme.mono τin :: Γ) v1 vd := by
        apply List.Forall₂.cons
        · exact hmonoTop
        · exact hctxV1
      rcases hcovR v1 vd hctxRet hC with
        ⟨wr, hrFixT, hrFixE, hrC, hrTy, hrEff⟩
      have hbelowBWTypes : ∀ i, i < rb.next.types →
          wb.types i = wr.types i := by
        intro i hi
        exact (hbelowBTypes i hi).trans
          (hrFixT i (by
            have h := hadvance.1
            dsimp [sr, sb]
            omega))
      have hbelowBWEffects : ∀ i, i < rb.next.effects →
          wb.effects i = wr.effects i := by
        intro i hi
        exact (hbelowBEffects i hi).trans
          (hrFixE i (by
            have h := hadvance.2
            dsimp [sr, sb]
            omega))
      have hframeBW := rb.semantic_frame_of_below wb wr
        hbBound.1 hbBound.2 hbelowBWTypes hbelowBWEffects
      have haWr : aG.eval wr = aD.eval vd := by
        have hkeep := hrFixT sb.types (by dsimp [sr]; omega)
        have hset : v1.types sb.types = aD.eval vd := by
          simp [v1, v0, SystemFXi.EHMX.Valuation.assignAt, sb]
        simp [aG, Ty.eval]
        exact hkeep.symm.trans hset
      have hδWr : δg.eval wr.effects = δd.eval vd.effects := by
        have hkeep := hrFixE sb.effects (by dsimp [sr]; omega)
        have hset : v1.effects sb.effects =
            δd.eval vd.effects := by
          simp [v1, v0, SystemFXi.EHMX.Valuation.assignAt,
            Function.update, sb]
        simp [δg, Poly.Effect.eval, Poly.Effect.var]
        exact hkeep.symm.trans hset
      have hχWr : χg.eval wr.effects = χd.eval vd.effects := by
        have hkeep := hrFixE (sb.effects + 1)
          (by dsimp [sr]; omega)
        have hset : v1.effects (sb.effects + 1) =
            χd.eval vd.effects := by
          simp [v1, Function.update]
        simp [χg, Poly.Effect.eval, Poly.Effect.var]
        exact hkeep.symm.trans hset
      have hsplitG :
          X.holds (X.split op rb.effect δg) wr := by
        apply (X.split_iff op rb.effect δg wr).mpr
        simp only [Effect.eval_union]
        rw [hδWr, hframeBW.2.2.symm, hbEff]
        simpa [Effect.eval_union, Poly.Effect.eval,
          Poly.Effect.singleton] using
          (X.split_iff op εin δd vd).mp (hsplit vd hC)
      have hδG :
          X.holds (X.includedEffect δg χg) wr := by
        apply (X.includedEffect_iff δg χg wr).2
        rw [hδWr, hχWr]
        exact (X.includedEffect_iff δd χd vd).1 (hδ vd hC)
      have hεG :
          X.holds (X.includedEffect rr.effect χg) wr := by
        apply (X.includedEffect_iff rr.effect χg wr).2
        rw [hrEff, hχWr]
        exact (X.includedEffect_iff εr χd vd).1 (hε vd hC)
      have hτG :
          X.holds (X.equalType rr.ty aG) wr := by
        apply (X.equalType_iff rr.ty aG wr).2
        exact hrTy.trans haWr.symm
      let localT :=
        Finset.range rc.next.types \ Finset.range rr.next.types
      let localE :=
        Finset.range rc.next.effects \ Finset.range rr.next.effects
      have hprojG :
          X.holds (X.handlerClause declg.typeVars declg.effectVars
            localT localE
              (X.combine rc.condition
                (X.combine (X.equalType rc.ty aG)
                  (X.includedEffect rc.effect χg)))) wr := by
        apply (X.handlerClause_iff
          declg.typeVars declg.effectVars localT localE
          (X.combine rc.condition
            (X.combine (X.equalType rc.ty aG)
              (X.includedEffect rc.effect χg))) wr).mpr
        intro bt be hbt hbe
        let bg : Valuation := ⟨bt, be⟩
        have hbgT : ∀ i, i ∉ declg.typeVars →
            bg.types i = wr.types i := hbt
        have hbgE : ∀ i, i ∉ declg.effectVars →
            bg.effects i = wr.effects i := hbe
        rcases raw.closed_rename_reverse hraw ρg ηg ρd ηd
            hsafe bg vd with
          ⟨vdB, hdBT, hdBE, hinputAlign, houtputAlign⟩
        have hprojD := hproj vd hC
        rcases (X.handlerClause_iff
          (raw.alphaRename ρd ηd).typeVars
          (raw.alphaRename ρd ηd).effectVars
          localTd localEd
          (X.combine D (X.combine (X.equalType τo aD)
            (X.includedEffect εo χd))) vd).mp hprojD
          vdB.types vdB.effects hdBT hdBE with
          ⟨lt, le, hlocalDT, hlocalDE, hDall⟩
        let vdL : Valuation := ⟨lt, le⟩
        have hDall' := (X.combine_iff _ _ vdL).1 hDall
        have hD : X.holds D vdL := hDall'.1
        have hmore := (X.combine_iff _ _ vdL).1 hDall'.2
        have hτclause : τo.eval vdL = aD.eval vdL :=
          (X.equalType_iff _ _ vdL).1 hmore.1
        have hεclause : εo.eval vdL.effects ⊆
            χd.eval vdL.effects :=
          (X.includedEffect_iff _ _ vdL).1 hmore.2
        have hbgBelowT : ∀ i, i < s.types →
            vg.types i = bg.types i := by
          intro i hi
          have hnot : i ∉ declg.typeVars := by
            intro hm
            have hu : i ∈ declg.usedTypes :=
              Finset.mem_union_left _
                (Finset.mem_union_left _ hm)
            have hgt := (hinterval.1 i hu).1
            omega
          exact (hbFixT i hi).trans
            ((hbelowBWTypes i (by omega)).trans
              (hbgT i hnot).symm)
        have hbgBelowE : ∀ i, i < s.effects →
            vg.effects i = bg.effects i := by
          intro i hi
          have hnot : i ∉ declg.effectVars := by
            intro hm
            have hu : i ∈ declg.usedEffects :=
              Finset.mem_union_left _
                (Finset.mem_union_left _ hm)
            have hgt := (hinterval.2 i hu).1
            omega
          exact (hbFixE i hi).trans
            ((hbelowBWEffects i (by omega)).trans
              (hbgE i hnot).symm)
        have hctxBG : Γg.MoreGeneralAt Γ bg vd :=
          Context.moreGeneralAt_below Γg Γ
            ops s hb vg bg vd hctx hbgBelowT hbgBelowE
        have hstableDT : ∀ i ∈ Γ.freeTypes ∪ aD.fvTypes,
            vd.types i = vdL.types i := by
          intro i hi
          have hnB : i ∉ (raw.alphaRename ρd ηd).typeVars := by
            intro hmem
            have hm : i ∈ (raw.alphaRename ρd ηd).typeVars ∩
                (Γ.freeTypes ∪ τin.fvTypes ∪ aD.fvTypes) := by
              apply Finset.mem_inter.mpr
              constructor
              · exact hmem
              · rcases Finset.mem_union.mp hi with hΓ | ha
                · simp [hΓ]
                · simp [ha]
            exact (Finset.disjoint_left.mp hscope.1)
              (Finset.mem_inter.mp hm).1 (Finset.mem_inter.mp hm).2
          have hnL : i ∉ localTd := by
            intro hmem
            have hm : i ∈ localTd ∩
                (Γ.freeTypes ∪ X.freeTypes C ∪ τin.fvTypes ∪
                  aD.fvTypes ∪
                  (raw.alphaRename ρd ηd).typeVars ∪
                  (raw.alphaRename ρd ηd).input.fvTypes ∪
                  (raw.alphaRename ρd ηd).output.fvTypes) := by
              apply Finset.mem_inter.mpr
              constructor
              · exact hmem
              · rcases Finset.mem_union.mp hi with hΓ | ha
                · simp [hΓ]
                · simp [ha]
            exact (Finset.disjoint_left.mp hclscope.2.2.1)
              (Finset.mem_inter.mp hm).1 (Finset.mem_inter.mp hm).2
          exact (hdBT i hnB).symm.trans
            (hlocalDT i hnL).symm
        have hstableDE :
            ∀ i ∈ Γ.freeEffects ∪ aD.fvEffects ∪ χd.vars,
              vd.effects i = vdL.effects i := by
          intro i hi
          have hnB : i ∉ (raw.alphaRename ρd ηd).effectVars := by
            intro hmem
            have hm : i ∈ (raw.alphaRename ρd ηd).effectVars ∩
                (Γ.freeEffects ∪ τin.fvEffects ∪ aD.fvEffects ∪
                  εin.vars ∪ εr.vars ∪ δd.vars ∪ χd.vars) := by
              apply Finset.mem_inter.mpr
              constructor
              · exact hmem
              · rcases Finset.mem_union.mp hi with hΓa | hχ
                · rcases Finset.mem_union.mp hΓa with hΓ | ha
                  · simp [hΓ]
                  · simp [ha]
                · simp [hχ]
            exact (Finset.disjoint_left.mp hscope.2)
              (Finset.mem_inter.mp hm).1 (Finset.mem_inter.mp hm).2
          have hnL : i ∉ localEd := by
            intro hmem
            have hm : i ∈ localEd ∩
                (Γ.freeEffects ∪ X.freeEffects C ∪ τin.fvEffects ∪
                  aD.fvEffects ∪ εin.vars ∪ εr.vars ∪
                  δd.vars ∪ χd.vars ∪
                  (raw.alphaRename ρd ηd).effectVars ∪
                  (raw.alphaRename ρd ηd).input.fvEffects ∪
                  (raw.alphaRename ρd ηd).output.fvEffects) := by
              apply Finset.mem_inter.mpr
              constructor
              · exact hmem
              · rcases Finset.mem_union.mp hi with hΓa | hχ
                · rcases Finset.mem_union.mp hΓa with hΓ | ha
                  · simp [hΓ]
                  · simp [ha]
                · simp [hχ]
            exact (Finset.disjoint_left.mp hclscope.2.2.2)
              (Finset.mem_inter.mp hm).1 (Finset.mem_inter.mp hm).2
          exact (hdBE i hnB).symm.trans
            (hlocalDE i hnL).symm
        have hctxD : Γg.MoreGeneralAt Γ bg vdL := by
          apply Context.moreGeneralAt_support             Γg Γ bg bg vd vdL hctxBG
          · intro σ hσ i hi; rfl
          · intro σ hσ i hi; rfl
          · intro σ hσ i hi
            exact hstableDT i (Finset.mem_union_left _
              (Generic.Context.freeTypes_of_mem Γ σ hσ hi))
          · intro σ hσ i hi
            exact hstableDE i (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Generic.Context.freeEffects_of_mem Γ σ hσ hi)))
        have hlocalOpT : ∀ i ∈
            (raw.alphaRename ρd ηd).input.fvTypes ∪
              (raw.alphaRename ρd ηd).output.fvTypes,
            vdB.types i = vdL.types i := by
          intro i hi
          apply (hlocalDT i ?_).symm
          intro hmem
          have hm : i ∈ localTd ∩
              (Γ.freeTypes ∪ X.freeTypes C ∪ τin.fvTypes ∪
                aD.fvTypes ∪
                (raw.alphaRename ρd ηd).typeVars ∪
                (raw.alphaRename ρd ηd).input.fvTypes ∪
                (raw.alphaRename ρd ηd).output.fvTypes) := by
            apply Finset.mem_inter.mpr
            constructor
            · exact hmem
            · rcases Finset.mem_union.mp hi with hin | hout
              · simp [hin]
              · simp [hout]
          exact (Finset.disjoint_left.mp hclscope.2.2.1)
            (Finset.mem_inter.mp hm).1 (Finset.mem_inter.mp hm).2
        have hlocalOpE : ∀ i ∈
            (raw.alphaRename ρd ηd).input.fvEffects ∪
              (raw.alphaRename ρd ηd).output.fvEffects,
            vdB.effects i = vdL.effects i := by
          intro i hi
          apply (hlocalDE i ?_).symm
          intro hmem
          have hm : i ∈ localEd ∩
              (Γ.freeEffects ∪ X.freeEffects C ∪ τin.fvEffects ∪
                aD.fvEffects ∪ εin.vars ∪ εr.vars ∪
                δd.vars ∪ χd.vars ∪
                (raw.alphaRename ρd ηd).effectVars ∪
                (raw.alphaRename ρd ηd).input.fvEffects ∪
                (raw.alphaRename ρd ηd).output.fvEffects) := by
            apply Finset.mem_inter.mpr
            constructor
            · exact hmem
            · rcases Finset.mem_union.mp hi with hin | hout
              · simp [hin]
              · simp [hout]
          exact (Finset.disjoint_left.mp hclscope.2.2.2)
            (Finset.mem_inter.mp hm).1 (Finset.mem_inter.mp hm).2
        have hinputLocal :
            (raw.alphaRename ρd ηd).input.eval vdB =
              (raw.alphaRename ρd ηd).input.eval vdL := by
          apply Ty.eval_support
          · intro i hi
            exact hlocalOpT i (Finset.mem_union_left _ hi)
          · intro i hi
            exact hlocalOpE i (Finset.mem_union_left _ hi)
        have houtputLocal :
            (raw.alphaRename ρd ηd).output.eval vdB =
              (raw.alphaRename ρd ηd).output.eval vdL := by
          apply Ty.eval_support
          · intro i hi
            exact hlocalOpT i (Finset.mem_union_right _ hi)
          · intro i hi
            exact hlocalOpE i (Finset.mem_union_right _ hi)
        have haDStable : aD.eval vd = aD.eval vdL := by
          apply Ty.eval_support
          · intro i hi
            exact hstableDT i (Finset.mem_union_right _ hi)
          · intro i hi
            exact hstableDE i (Finset.mem_union_left _
              (Finset.mem_union_right _ hi))
        have hχDStable : χd.eval vd.effects =
            χd.eval vdL.effects := by
          apply Effect.eval_support
          intro i hi
          exact hstableDE i (Finset.mem_union_right _ hi)
        have haBG : aG.eval bg = aD.eval vdL := by
          have hnot : sb.types ∉ declg.typeVars := by
            intro hm
            have hu : sb.types ∈ declg.usedTypes :=
              Finset.mem_union_left _
                (Finset.mem_union_left _ hm)
            have hh := (hinterval.1 _ hu).2
            dsimp [sb] at hh
            omega
          have hfix := hbgT sb.types hnot
          simp [aG, Ty.eval]
          exact hfix.trans (haWr.trans haDStable)
        have hχBG : χg.eval bg.effects =
            χd.eval vdL.effects := by
          have hnot : sb.effects + 1 ∉ declg.effectVars := by
            intro hm
            have hu : sb.effects + 1 ∈ declg.usedEffects :=
              Finset.mem_union_left _
                (Finset.mem_union_left _ hm)
            have hh := (hinterval.2 _ hu).2
            dsimp [sb] at hh
            omega
          have hfix := hbgE (sb.effects + 1) hnot
          have hvar : χg.eval bg.effects = χg.eval wr.effects := by
            simpa [χg, Poly.Effect.eval, Poly.Effect.var] using hfix
          exact hvar.trans (hχWr.trans hχDStable)
        have hinputEq : declg.input.eval bg =
            (raw.alphaRename ρd ηd).input.eval vdL :=
          hinputAlign.trans hinputLocal
        have houtputEq : declg.output.eval bg =
            (raw.alphaRename ρd ηd).output.eval vdL :=
          houtputAlign.trans houtputLocal
        have hkEq : (Ty.arr declg.output χg aG).eval bg =
            (Ty.arr (raw.alphaRename ρd ηd).output χd aD).eval vdL := by
          simp [Ty.eval, houtputEq, hχBG, haBG]
        have hctxClause : Context.MoreGeneralAt
            (Scheme.mono (.arr declg.output χg aG) ::
              Scheme.mono declg.input :: Γg)
            (Scheme.mono (.arr (raw.alphaRename ρd ηd).output χd aD) ::
              Scheme.mono (raw.alphaRename ρd ηd).input :: Γ)
            bg vdL := by
          apply List.Forall₂.cons
          · exact (Scheme.mono_moreGeneralAt_iff _ _ bg vdL).mpr hkEq
          · apply List.Forall₂.cons
            · exact (Scheme.mono_moreGeneralAt_iff _ _ bg vdL).mpr
                hinputEq
            · exact hctxD
        have haBelowT : ∀ i ∈ aG.fvTypes,
            i < rr.next.types := by
          intro i hi
          simp [aG, Ty.fvTypes] at hi
          subst i
          change (rb.next.advance raw.typeVars raw.effectVars).types <
            rr.next.types
          dsimp [sr, sb] at hmR
          omega
        have haBelowE : ∀ i ∈ aG.fvEffects,
            i < rr.next.effects := by
          intro i hi
          simp [aG, Ty.fvEffects] at hi
        have hχBelow : ∀ i ∈ χg.vars,
            i < rr.next.effects := by
          intro i hi
          simp [χg, Poly.Effect.var, sb] at hi
          dsimp [sr, sb] at hmR
          omega
        have htarget : τo.eval vdL = aG.eval bg :=
          hτclause.trans haBG.symm
        have heffect : εo.eval vdL.effects ⊆
            χg.eval bg.effects := by
          rw [hχBG]
          exact hεclause
        have hprojectG := Output.CoversAt.project_clause
                    (Scheme.mono (.arr declg.output χg aG) ::
            Scheme.mono declg.input :: Γg)
          (Scheme.mono (.arr (raw.alphaRename ρd ηd).output χd aD) ::
            Scheme.mono (raw.alphaRename ρd ηd).input :: Γ)
          D rr.next rc τo aG εo χg
          hcBound.1 hcBound.2 haBelowT haBelowE hχBelow
          hcovC bg vdL hctxClause hD htarget heffect
        exact (X.projection_iff localT localE
          (X.combine rc.condition
            (X.combine (X.equalType rc.ty aG)
              (X.includedEffect rc.effect χg))) bg).mp hprojectG
      refine ⟨wr, ?_, ?_, ?_, haWr, hχWr⟩
      · intro i hi
        exact (hbFixT i hi).trans
          (hbelowBWTypes i (by omega))
      · intro i hi
        exact (hbFixE i hi).trans
          (hbelowBWEffects i (by omega))
      · simp only [handlerCondition, X.combine_iff]
        exact ⟨⟨hframeBW.1.mp hbC, hrC⟩,
          hτG, hprojG, hsplitG, hδG, hεG⟩
  | conv _ hconv ih =>
      intro Γg ops s hlen hops hb
      obtain ⟨r, hr, hcov⟩ := ih Γg ops s hlen hops hb
      exact ⟨r, hr, Output.CoversAt.conv _ _ _ _ _ _ _ _ hcov hconv⟩
  | weaken _ hent ih =>
      intro Γg ops s hlen hops hb
      obtain ⟨r, hr, hcov⟩ := ih Γg ops s hlen hops hb
      exact ⟨r, hr, Output.CoversAt.weaken _ _ _ _ _ _ _ _ hcov hent⟩


/-- The executable result is principal for every declarative typing of a
expression. The comparison quantifies over all typings, not only
the derivation used to establish that generation succeeds. -/
theorem Typing.generateFresh_principal
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed)
    (Γ : Context X) (e : Expr) (s : Supply)
    {C₀ : X.Formula} {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀) :
    ∃ r : Output X,
      generateFresh sig X Γ e s = some r ∧
      Typing sig X r.condition Γ e r.ty r.effect ∧
      ∀ (C : X.Formula) (τ : Ty) (ε : Effect),
        Typing sig X C Γ e τ ε →
        r.MoreGeneralThan Γ C τ ε := by
  let seed := Supply.seed s sig Γ e
  have hb : BoundedInputs sig X Γ e.ops seed :=
    BoundedInputs.seed Γ e s
  have hbelow := hb.context_free_below
  obtain ⟨r, hr, _⟩ :=
    h₀.generate_complete hFV hAtom hClosed
      Γ e.ops seed rfl (Finset.Subset.rfl) hb
  refine ⟨r, hr, generateFresh_sound hr, ?_⟩
  intro C τ ε ht v hv
  obtain ⟨r', hr', hcov⟩ :=
    ht.generate_complete hFV hAtom hClosed
      Γ e.ops seed rfl (Finset.Subset.rfl) hb
  rw [hr] at hr'
  cases hr'
  rcases hcov v v (Context.moreGeneralAt_refl Γ v) hv with
    ⟨w, hfixedT, hfixedE, hC, hty, heff⟩
  exact ⟨w,
    (fun i hi => (hfixedT i (hbelow.1 i hi)).symm),
    (fun i hi => (hfixedE i (hbelow.2 i hi)).symm),
    hC, hty, heff⟩

/-- HM(X)-style solved principal computation scheme for the full language, assuming a principal normalizer for the chosen constraint system. -/
theorem Typing.infer_principal_scheme
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed)
    (N : X.PrincipalNormalizer)
    (hTrue : ∃ R, N.solved R ∧ ∀ v, X.holds R v)
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (s : Supply)
    {C₀ : X.Formula} {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀)
    (v : Valuation) (hv : X.holds C₀ v) :
    ∃ (r : Output X) (n : X.NormalForm)
      (σo : X.ComputationScheme),
      generateFresh sig X Γ e s = some r ∧
      N.normalize r.canonicalCondition = some n ∧
      σo = ComputationScheme.generalize Γ n.residual
        (NormalForm.reconstruct n r.canonical).ty
        (NormalForm.reconstruct n r.canonical).effect ∧
      ComputationScheme.freeTypes σo = ∅ ∧
      ComputationScheme.freeEffects σo = ∅ ∧
      ComputationSchemeTyping sig X Γ e σo ∧
      (∀ σ' : X.ComputationScheme,
        ComputationSchemeTyping sig X Γ e σ' →
        σo.Subsumes σ') ∧
      ∃ ρ t η, σo.GroundInstance ρ t η := by
  obtain ⟨r, hr, _, hmono⟩ :=
    h₀.generateFresh_principal hFV hAtom hClosed
      Γ e s
  obtain ⟨n, σo, hn, hσ, hft, hfe, htyping, hprincipal, hreal⟩ :=
    ComputationSchemeTyping.infer_principal_scheme_exists_of_mono
      N hTrue Γ hΓClosed e s r hr hmono C₀ τ₀ ε₀ h₀ v hv
  exact ⟨r, n, σo, hr, hn, hσ, hft, hfe,
    htyping, hprincipal, hreal⟩


end SystemFXi.EHMX.Generic
