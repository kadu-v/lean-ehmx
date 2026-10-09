import SystemFXi.EHMX.GenericSupport

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

/-- The fragment that still includes polymorphic let but no handler. -/
def HandlerFree : Expr → Prop
  | .var _ | .int _ | .bool _ => True
  | .lam body => HandlerFree body
  | .app f x | .letE f x => HandlerFree f ∧ HandlerFree x
  | .perform _ e => HandlerFree e
  | .handle _ _ _ _ => False

theorem Typing.generate_complete_handlerFree
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed)
    {C : X.Formula} {Γd : Context X}
    {e : Expr} {τ : Ty} {ε : Effect}
    (h : Typing sig X C Γd e τ ε) :
    HandlerFree e →
    ∀ (Γg : Context X) (ops : Finset Op) (s : Supply),
      Γg.length = Γd.length →
      e.ops ⊆ ops →
      BoundedInputs sig X Γg ops s →
      ∃ r : Output X,
        generate sig X Γg e s = some r ∧
        r.CoversAt Γg Γd C s τ ε := by
  induction h with
  | var hlookup hadm hfresh hent =>
      intro hfree Γg ops s hlen hops hb
      obtain ⟨σg, hlookupG⟩ :=
        Context.lookup_of_length_eq Γg _ _ hlen _ hlookup
      exact generate_var_coversAt hlookupG hlookup
        _ _ hadm hfresh _ hent ops s hb
  | int n =>
      intro hfree Γg ops s hlen hops hb
      refine ⟨⟨.base .int, ∅, X.trivial, s⟩,
        by simp [generate], ?_⟩
      intro vg vd hctx hC
      exact ⟨vg, (fun _ _ => rfl), (fun _ _ => rfl),
        (X.trivial_iff vg).2 trivial, rfl, rfl⟩
  | bool b =>
      intro hfree Γg ops s hlen hops hb
      refine ⟨⟨.base .bool, ∅, X.trivial, s⟩,
        by simp [generate], ?_⟩
      intro vg vd hctx hC
      exact ⟨vg, (fun _ _ => rfl), (fun _ _ => rfl),
        (X.trivial_iff vg).2 trivial, rfl, rfl⟩
  | lam _ ih =>
      intro hfree Γg ops s hlen hops hb
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
      rcases ih hfree (Scheme.mono aG :: Γg) ops sb
          (by simp [hlen]) hbodyOps hchild with
        ⟨rb, hr, hcov⟩
      refine ⟨⟨.arr aG rb.effect rb.ty, ∅,
        rb.condition, rb.next⟩, ?_, ?_⟩
      · simp [generate, aG, sb, hr]
      · exact Output.CoversAt.lam Γg _ _ ops s rb
          _ _ _ hb hcov
  | app _ _ ihf ihx =>
      intro hfree Γg ops s hlen hops hb
      rcases hfree with ⟨hff, hfx⟩
      rcases ihf hff Γg ops s hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb with
        ⟨rf, hrf, hcovF⟩
      have hstart := generate_next_mono hrf
      have hbX := hb.mono hstart
      rcases ihx hfx Γg ops rf.next hlen
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
      intro hfree Γg ops s hlen hops hb
      have hop : op ∈ ops := hops (by simp [Expr.ops])
      let sa := s.advance raw.typeVars raw.effectVars
      have hchild : BoundedInputs sig X Γg ops sa :=
        hb.mono ⟨Nat.le_of_lt (s.advance_mono
          raw.typeVars raw.effectVars).1,
          Nat.le_of_lt (s.advance_mono
          raw.typeVars raw.effectVars).2⟩
      rcases ih hfree Γg ops sa hlen
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
      intro hfree Γg ops s hlen hops hb
      rcases hfree with ⟨hf₁, hf₂⟩
      rcases ih₁ hf₁ Γg ops s hlen
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
      rcases ih₂ hf₂
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
      intro hfree Γg ops s hlen hops hb
      rcases hfree with ⟨hf₁, hf₂⟩
      rcases ih₁ hf₁ Γg ops s hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb with
        ⟨r₁, hr₁, hcov₁⟩
      have hstart := generate_next_mono hr₁
      have h₁Bound := generate_support_below hFV hAtom
        hr₁ ops (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb
      have hctx := (hb.mono hstart).consMono hAtom r₁.ty
        (fun i hi => h₁Bound.1 i (Finset.mem_union_left _ hi))
        (fun i hi => h₁Bound.2 i
          (by simp [Output.supportEffects, hi]))
      rcases ih₂ hf₂ (Scheme.mono r₁.ty :: Γg)
          ops r₁.next (by simp [hlen])
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hctx with
        ⟨r₂, hr₂, hcov₂⟩
      refine ⟨⟨r₂.ty, r₁.effect ∪ r₂.effect,
        X.combine r₁.condition r₂.condition, r₂.next⟩,
        ?_, ?_⟩
      · simp [generate, hr₁, Expr.isValue_iff, hnv, hr₂]
      · exact Output.CoversAt.letMono Γg _ _ ops s
          r₁ r₂ _ _ _ _ hb h₁Bound hstart hcov₁ hcov₂
  | handle =>
      intro hfree
      simp [HandlerFree] at hfree
  | conv _ hconv ih =>
      intro hfree Γg ops s hlen hops hb
      obtain ⟨r, hr, hcov⟩ := ih hfree Γg ops s hlen hops hb
      exact ⟨r, hr, Output.CoversAt.conv _ _ _ _ _ _ _ _ hcov hconv⟩
  | weaken _ hent ih =>
      intro hfree Γg ops s hlen hops hb
      obtain ⟨r, hr, hcov⟩ := ih hfree Γg ops s hlen hops hb
      exact ⟨r, hr, Output.CoversAt.weaken _ _ _ _ _ _ _ _ hcov hent⟩

/-- The executable result is principal for every declarative typing of a
handler-free expression. The comparison quantifies over all typings, not only
the derivation used to establish that generation succeeds. -/
theorem Typing.generateFresh_principal_handlerFree
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed)
    (Γ : Context X) (e : Expr) (s : Supply)
    (hfree : HandlerFree e)
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
    h₀.generate_complete_handlerFree hFV hAtom hClosed
      hfree Γ e.ops seed rfl (Finset.Subset.rfl) hb
  refine ⟨r, hr, generateFresh_sound hr, ?_⟩
  intro C τ ε ht v hv
  obtain ⟨r', hr', hcov⟩ :=
    ht.generate_complete_handlerFree hFV hAtom hClosed
      hfree Γ e.ops seed rfl (Finset.Subset.rfl) hb
  rw [hr] at hr'
  cases hr'
  rcases hcov v v (Context.moreGeneralAt_refl Γ v) hv with
    ⟨w, hfixedT, hfixedE, hC, hty, heff⟩
  exact ⟨w,
    (fun i hi => (hfixedT i (hbelow.1 i hi)).symm),
    (fun i hi => (hfixedE i (hbelow.2 i hi)).symm),
    hC, hty, heff⟩

/-- HM(X)-style solved principal computation scheme for the handler-free
fragment, assuming a principal normalizer for the chosen constraint system. -/
theorem Typing.infer_principal_scheme_handlerFree
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed)
    (N : X.PrincipalNormalizer)
    (hTrue : ∃ R, N.solved R ∧ ∀ v, X.holds R v)
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (s : Supply) (hfree : HandlerFree e)
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
    h₀.generateFresh_principal_handlerFree hFV hAtom hClosed
      Γ e s hfree
  obtain ⟨n, σo, hn, hσ, hft, hfe, htyping, hprincipal, hreal⟩ :=
    ComputationSchemeTyping.infer_principal_scheme_exists_of_mono
      N hTrue Γ hΓClosed e s r hr hmono C₀ τ₀ ε₀ h₀ v hv
  exact ⟨r, n, σo, hr, hn, hσ, hft, hfe,
    htyping, hprincipal, hreal⟩

end SystemFXi.EHMX.Generic
