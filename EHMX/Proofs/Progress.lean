import EHMX.Goals
import EHMX.Proofs.Typing

namespace EHMX

theorem unionKinds (h : Ty.HasKind S Δ (.union ε η) 1) :
    Ty.HasKind S Δ ε 1 ∧ Ty.HasKind S Δ η 1 := by
  cases h with
  | con _ hs => cases hs with | cons hε hs => cases hs with | cons hη _ => exact ⟨hε,hη⟩

theorem effectsUnion (hF : EffectFramework S M) (hρ : Assignment.Valid S M ρ)
    (hbs : KindValues M Δ bs) (h : Ty.HasKind S Δ (.union ε η) 1) :
    M.effects ((Ty.union ε η).eval M ρ bs) =
      M.effects (ε.eval M ρ bs) ∪ M.effects (η.eval M ρ bs) := by
  simp only [Ty.union, Ty.eval, List.map_cons, List.map_nil]
  exact hF.unionEffect _ _ (evalKind hF hρ hbs (unionKinds h).1)
    (evalKind hF hρ hbs (unionKinds h).2)

theorem effectsSingleton (hF : EffectFramework S M) (op : Op) :
    M.effects ((Ty.singleton op).eval M ρ bs) = {op} := by
  simpa only [Ty.singleton, Ty.eval, List.map_nil] using hF.singletonEffect op

theorem typingClosed (ht : Typing S M sig Δ C {} e T ε) : e.Closed := by
  have hs := (typingWF ht).2.2.2.1
  exact ⟨hs.1, Finset.subset_empty.mp hs.2⟩

/-- Closed typed terms either reduce, are values, or expose an operation in the
interpreted effect. This theorem does not assume preservation. -/
theorem progressGeneral (hF : EffectFramework S M)
    (hρ : Assignment.Valid S M ρ) (hι : GroundEnv.Valid ι)
    (ht : Typing S M sig Δ C Γ e T ε) :
    Γ = {} → ∀ bs, KindValues M Δ bs → C.Holds M ρ bs ι →
    Value e ∨ (∃ e', Step e e') ∨ ∃ op, Unhandled e op ∧ op ∈ M.effects (ε.eval M ρ bs) := by
  induction ht with
  | @var Δ C Γ x T s hw hl _ =>
      intro hΓ bs hbs hC
      subst hΓ
      cases x <;> simp [Env.lookup] at hl
  | lam => intro _ _ _ _; exact Or.inl rfl
  | @app Δ C Γ f x B εf εx η A hw hf hx ihf ihx =>
      intro hΓ bs hbs hC
      have hε := hw.2.2.2.2.2
      have hout := effectsUnion hF hρ hbs hε
      have hin := effectsUnion hF hρ hbs (unionKinds hε).1
      rcases ihf hΓ bs hbs hC with hvf | ⟨f', hf'⟩ | ⟨op, ⟨E, v, he, hv, hop⟩, hm⟩
      · rcases ihx hΓ bs hbs hC with hvx | ⟨x', hx'⟩ | ⟨op, ⟨E, v, he, hv, hop⟩, hm⟩
        · obtain ⟨body, hbody⟩ := closedValueLambda (typingClosed (hΓ ▸ hf)) hvf
          subst hbody
          exact Or.inr (Or.inl ⟨_, .beta hvx⟩)
        · exact Or.inr (Or.inl ⟨_, .context (E := .appArg _ hvf .hole) hx'⟩)
        · refine Or.inr (Or.inr ⟨op, ⟨.appArg _ hvf E, v, ?_, hv, hop⟩, ?_⟩)
          · simp [EvalCtx.plug, he]
          · rw [hout, hin]; exact Or.inl (Or.inr hm)
      · exact Or.inr (Or.inl ⟨_, .context (E := .appFun .hole _) hf'⟩)
      · refine Or.inr (Or.inr ⟨op, ⟨.appFun E x, v, ?_, hv, hop⟩, ?_⟩)
        · simp [EvalCtx.plug, he]
        · rw [hout, hin]; exact Or.inl (Or.inl hm)
  | @letMono Δ C Γ rhs body B εrhs εbody A hw hr hb ihr ihb =>
      intro hΓ bs hbs hC
      rcases ihr hΓ bs hbs hC with hv | ⟨rhs', hs⟩ | ⟨op, ⟨E, v, he, hv, hop⟩, hm⟩
      · exact Or.inr (Or.inl ⟨_, .letValue hv⟩)
      · exact Or.inr (Or.inl ⟨_, .context (E := .letRhs .hole _) hs⟩)
      · refine Or.inr (Or.inr ⟨op, ⟨.letRhs E body, v, ?_, hv, hop⟩, ?_⟩)
        · simp [EvalCtx.plug, he]
        · rw [effectsUnion hF hρ hbs hw.2.2.2.2.2]; exact Or.inl hm
  | letPoly _ hv => intro _ _ _ _; exact Or.inr (Or.inl ⟨_, .letValue hv⟩)
  | @perform Δ C Γ op arg decl args ε hw _ _ ha ih =>
      intro hΓ bs hbs hC
      have hout := effectsUnion hF hρ hbs hw.2.2.2.2.2
      rcases ih hΓ bs hbs hC with hv | ⟨arg', hs⟩ | ⟨op', ⟨E, v, he, hv, hop⟩, hm⟩
      · refine Or.inr (Or.inr ⟨_, ⟨.hole, _, rfl, hv, by simp [EvalCtx.handled]⟩, ?_⟩)
        rw [hout, effectsSingleton hF]; exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨_, .context (E := .perform _ .hole) hs⟩)
      · refine Or.inr (Or.inr ⟨op', ⟨.perform op E, v, ?_, hv, hop⟩, ?_⟩)
        · simp [EvalCtx.plug, he]
        · rw [hout]; exact Or.inr hm
  | @handle Δ C Γ body op ret clause B εout decl A εin hw hs hb hle hr hc ihb ihr ihc =>
      intro hΓ bs hbs hC
      rcases ihb hΓ bs hbs hC with hv | ⟨body', hstep⟩ | ⟨op', ⟨E, v, he, hv, hop⟩, hm⟩
      · exact Or.inr (Or.inl ⟨_, .returnValue hv⟩)
      · exact Or.inr (Or.inl ⟨_, .context (E := .handle .hole op ret clause) hstep⟩)
      · by_cases heq : op' = op
        · subst heq; subst he
          exact Or.inr (Or.inl ⟨_, .operation hv hop⟩)
        · refine Or.inr (Or.inr ⟨op', ⟨.handle E op ret clause, v, ?_, hv, ?_⟩, ?_⟩)
          · simp [EvalCtx.plug, he]
          · simp [EvalCtx.handled, heq, hop]
          · have h := hle ρ bs ι hρ hbs hι hC
            have hm' := (hF.effectOrder _ _ h.1 h.2.1).mp h.2.2 hm
            rw [effectsUnion hF hρ hbs (unionKind (singletonKind op) hw.2.2.2.2.2),
              effectsSingleton hF] at hm'
            exact hm'.resolve_left heq
  | sub hw hd hT hε ih =>
      intro hΓ bs hbs hC
      rcases ih hΓ bs hbs hC with hv | hs | ⟨op, hop, hm⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl hs)
      · have h := hε ρ bs ι hρ hbs hι hC
        exact Or.inr (Or.inr ⟨op, hop, (hF.effectOrder _ _ h.1 h.2.1).mp h.2.2 hm⟩)
  | strengthen hw hd he ih =>
      intro hΓ bs hbs hC
      exact ih hΓ bs hbs (he ρ bs ι hρ hbs hι hC)
  | exists_ hw hd ih =>
      intro hΓ bs hbs hC
      obtain ⟨vs, hvs, hC'⟩ := hC
      have hr := ih (by simp [hΓ, Env.shift]) (vs ++ bs) (List.rel_append hvs hbs) hC'
      have hn := hvs.length_eq
      simpa only [← hn, evalShift] using hr

theorem progressEffectSafety (S : Signature) (M : Model) (sig : OpSignature) :
    ProgressGoal S M sig := by
  intro hA C e T ε ht ρ ι hρ hι hC
  exact progressGeneral hA.1.1 hρ hι ht rfl [] .nil hC

/-- 空効果での一状態の進行性。到達状態の保証は Preservation.lean の emptyEffectSafety で導く。 -/
theorem emptyEffectProgress (hF : EffectFramework S M)
    (hsat : Satisfiable S M [] C) (ht : Typing S M sig [] C {} e T .empty) :
    Value e ∨ ∃ e', Step e e' := by
  obtain ⟨_, ρ, bs, ι, hρ, hbs, hι, hC⟩ := hsat
  cases hbs
  rcases progressGeneral hF hρ hι ht rfl [] .nil hC with hv | hs | ⟨op, _, hm⟩
  · exact Or.inl hv
  · exact Or.inr hs
  · simp only [Ty.empty, Ty.eval, List.map_nil, hF.emptyEffect, Set.mem_empty_iff_false] at hm

end EHMX
