import SystemFXi.EHMX.GenericHandlerScope

set_option maxHeartbeats 1000000

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

theorem generate_handle_of_runs
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV) (hClosed : sig.Closed)
    (Γ : Context X) (body ret clause : Expr) (op : Op)
    (raw : OpDecl) (s : Supply)
    (rb rr rc : Output X)
    (ops : Finset Op)
    (hb : BoundedInputs sig X Γ ops s)
    (hd : sig op = some raw)
    (hbody : generate sig X Γ body s = some rb)
    (hret : generate sig X (Scheme.mono rb.ty :: Γ) ret
      ⟨(rb.next.advance raw.typeVars raw.effectVars).types + 1,
        (rb.next.advance raw.typeVars raw.effectVars).effects + 2⟩ =
      some rr)
    (hclause : generate sig X
      (Scheme.mono
          (.arr (raw.alphaRename
            (renameBound raw.typeVars rb.next.types)
            (renameBound raw.effectVars rb.next.effects)).output
            (Poly.Effect.var
              ((rb.next.advance raw.typeVars raw.effectVars).effects + 1))
            (.var (rb.next.advance raw.typeVars raw.effectVars).types)) ::
        Scheme.mono (raw.alphaRename
          (renameBound raw.typeVars rb.next.types)
          (renameBound raw.effectVars rb.next.effects)).input :: Γ)
      clause rr.next = some rc)
    (hbBound : (∀ i ∈ rb.supportTypes, i < rb.next.types) ∧
      (∀ i ∈ rb.supportEffects, i < rb.next.effects))
    (hrBound : (∀ i ∈ rr.supportTypes, i < rr.next.types) ∧
      (∀ i ∈ rr.supportEffects, i < rr.next.effects))
    (hcBound : (∀ i ∈ rc.supportTypes, i < rc.next.types) ∧
      (∀ i ∈ rc.supportEffects, i < rc.next.effects)) :
    ∃ r : Output X,
      generate sig X Γ (.handle body op ret clause) s = some r := by
  let ρ := renameBound raw.typeVars rb.next.types
  let η := renameBound raw.effectVars rb.next.effects
  let decl := raw.alphaRename ρ η
  let sb := rb.next.advance raw.typeVars raw.effectVars
  let a := Ty.var sb.types
  let δ := Poly.Effect.var sb.effects
  let χ := Poly.Effect.var (sb.effects + 1)
  let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
  let localTypes :=
    Finset.range rc.next.types \ Finset.range rr.next.types
  let localEffects :=
    Finset.range rc.next.effects \ Finset.range rr.next.effects
  let C := handlerCondition X op decl
    rb.condition rr.condition rc.condition rr.ty rc.ty a
    rb.effect rr.effect rc.effect δ χ localTypes localEffects
  have hmB := generate_next_mono hbody
  have hmR := generate_next_mono hret
  have hmC := generate_next_mono hclause
  have hraw := hClosed op raw hd
  have hsafe : raw.AlphaSafe ρ η := by
    apply raw.renameBound_alphaSafe
    · intro i hi
      exact False.elim
        ((Finset.mem_sdiff.mp hi).2
          (hraw.1 (Finset.mem_sdiff.mp hi).1))
    · intro i hi
      exact False.elim
        ((Finset.mem_sdiff.mp hi).2
          (hraw.2 (Finset.mem_sdiff.mp hi).1))
  have hscope : Generic.OpDecl.HandlerScope decl Γ rb.ty a
      rb.effect rr.effect δ χ := by
    exact generated_handlerScope_of_runs Γ ops s raw body ret rb rr
      hb hbody hbBound.1 hbBound.2 hret
  have hΓT : ∀ i ∈ Γ.freeTypes, i < rr.next.types := by
    intro i hi
    have h := (hb.context_free_below).1 i hi
    have ha := rb.next.advance_mono raw.typeVars raw.effectVars
    dsimp [sr, sb] at hmR
    omega
  have hΓE : ∀ i ∈ Γ.freeEffects, i < rr.next.effects := by
    intro i hi
    have h := (hb.context_free_below).2 i hi
    have ha := rb.next.advance_mono raw.typeVars raw.effectVars
    dsimp [sr, sb] at hmR
    omega
  have hretOld := generated_return_old_support hFV hAtom hClosed
    Γ raw rb rr ret
    (by
      intro i hi
      have h := (hb.context_free_below).1 i hi
      omega)
    (by
      intro i hi
      have h := (hb.context_free_below).2 i hi
      omega)
    hbBound.1 hbBound.2 hret
  have hnextB : rb.next.types ≤ rr.next.types ∧
      rb.next.effects ≤ rr.next.effects := by
    have ha := rb.next.advance_mono raw.typeVars raw.effectVars
    dsimp [sr, sb] at hmR
    omega
  have ha : sb.types < rr.next.types := by
    change (rb.next.advance raw.typeVars raw.effectVars).types <
      rr.next.types
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      (by simpa [sr, sb] using hmR.1)
  have hχ : sb.effects + 1 < rr.next.effects := by
    change (rb.next.advance raw.typeVars raw.effectVars).effects + 1 <
      rr.next.effects
    have hm := hmR.2
    dsimp [sr, sb] at hm
    omega
  have hclscope : Generic.OpDecl.ClauseScope decl Γ C rb.ty a
      rb.effect rr.effect δ χ localTypes localEffects := by
    exact generated_clauseScope_of_bounds hFV hAtom Γ op raw hraw rb rr rc
      hΓT hΓE hbBound.1 hbBound.2 hrBound.1 hrBound.2
      hcBound.1 hcBound.2 hretOld.1 hretOld.2
      hnextB ha hχ
  refine ⟨⟨a, χ, C, rc.next⟩, ?_⟩
  simp [generate, hd, hbody, hret, hclause,
    hsafe, hscope, hclscope,
    ρ, η, decl, sb, a, δ, χ,
    localTypes, localEffects, C]


end SystemFXi.EHMX.Generic
