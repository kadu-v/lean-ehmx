import EHMX.Proofs.GenerationProperties
import EHMX.Proofs.Typing

namespace EHMX

/-- A scoped variable has an actual environment binding, even with shadowing. -/
theorem scopedLookup (he : Expr.Scoped Γ (.ident x)) : ∃ s, Γ.lookup x = some s := by
  cases x with
  | bound i =>
      have hi : i < Γ.bound.length := he.1
      exact ⟨Γ.bound[i], List.getElem?_eq_getElem hi⟩
  | free x =>
      have hx : x ∈ Γ.dpi := he.2 (by simp [Expr.fv])
      obtain ⟨p, hp, hpx⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      have hn : Γ.free.reverse.find? (fun p => p.1 == x) ≠ none := by
        intro hn
        have hh := List.find?_eq_none.mp hn p (List.mem_reverse.mpr hp)
        exact hh (by simpa using hpx)
      cases hs : Γ.free.reverse.find? (fun p => p.1 == x) with
      | none => exact False.elim (hn hs)
      | some p => exact ⟨p.2, by simp [Env.lookup, hs]⟩

/-- The environment-prefixed variable constraint is exactly a scheme instance
and the empty-effect bound, together with environment feasibility. -/
theorem inferenceVariableConstraint (hF : EffectFramework S M)
    (hΓ : Env.WF S Δ Γ) (hl : Γ.lookup x = some s) (hT : Ty.HasKind S Δ T 0) :
    Equivalent S M Δ (infer sig Γ (.ident x) T ε)
      (.conj Γ.exists_ (.conj (s.instanceConstraint T) (.le 1 .empty ε))) := by
  have hs := lookupWF hΓ hl
  have heq : ∀ ρ bs ι, Assignment.Valid S M ρ → KindValues M Δ bs →
      ((infer sig Γ (.ident x) T ε).Holds M ρ bs ι ↔
        (Constraint.conj Γ.exists_ (.conj (s.instanceConstraint T) (.le 1 .empty ε))).Holds M ρ bs ι) := by
    intro ρ bs ι hρ hbs
    rw [infer, envLetInHolds]
    change (_ ∧ T.eval M ρ bs ∈ (Γ.interpret M ρ bs ι).lookup x ∧ _) ↔ _
    rw [envInterpretLookup hΓ hl]
    exact and_congr_right (fun _ => and_congr
      (instanceConstraintHolds hF hs.1 hT hρ hbs ι).symm Iff.rfl)
  exact ⟨fun ρ bs ι hρ hbs _ h => (heq ρ bs ι hρ hbs).mp h,
    fun ρ bs ι hρ hbs _ h => (heq ρ bs ι hρ hbs).mpr h⟩

/-- The variable case of inference soundness, with the stronger outer constraint
needed by structural induction. -/
theorem inferenceVariable (hF : EffectFramework S M)
    (hw : JudgmentWF S Δ C Γ (.ident x) T ε)
    (he : Entails S M Δ C (infer sig Γ (.ident x) T ε)) :
    Typing S M sig Δ C Γ (.ident x) T ε := by
  obtain ⟨s, hl⟩ := scopedLookup hw.2.2.2.1
  have hp := entailsTrans he (inferenceVariableConstraint hF hw.2.2.1 hl hw.2.2.2.2.1).1
  have hv : Typing S M sig Δ C Γ (.ident x) T .empty :=
    .var (judgmentEmptyEffect hF.signature hw) hl
      (fun ρ bs ι hρ hbs hι h => (hp ρ bs ι hρ hbs hι h).2.1)
  exact .sub hw hv (leRefl hF hF.signature.1 hw.2.2.2.2.1)
    (fun ρ bs ι hρ hbs hι h => (hp ρ bs ι hρ hbs hι h).2.2)

/-- The `var` rule's completeness obligation. Feasibility is supplied at each
valuation, so this also fits induction beneath `strengthen`. -/
theorem variableCompletenessHolds (hF : EffectFramework S M)
    (hΓ : Env.WF S Δ Γ) (hl : Γ.lookup x = some s) (hT : Ty.HasKind S Δ T 0)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs) (hι : GroundEnv.Valid ι)
    (hΓe : Γ.exists_.Holds M ρ bs ι) (hi : (s.instanceConstraint T).Holds M ρ bs ι) :
    (infer sig Γ (.ident x) T .empty).Holds M ρ bs ι := by
  apply (inferenceVariableConstraint hF hΓ hl hT).2 ρ bs ι hρ hbs hι
  exact ⟨hΓe, hi, leRefl hF hF.signature.2.1 (emptyKind hF.signature)
    ρ bs ι hρ hbs hι (C := .truth) trivial⟩

/-- The `sub` completeness obligation after adding the environment. -/
theorem inferenceMonotone (hF : EffectFramework S M) (hΓ : Env.WF S Δ Γ)
    (hgen : Entails S M Δ C (infer sig Γ e T ε))
    (hTU : Entails S M Δ C (.le 0 T U)) (hεη : Entails S M Δ C (.le 1 ε η)) :
    Entails S M Δ C (infer sig Γ e U η) := by
  intro ρ bs ι hρ hbs hι hC
  obtain ⟨hΓe, hg⟩ := (envLetInHolds Γ _ ρ bs ι).mp (hgen ρ bs ι hρ hbs hι hC)
  apply (envLetInHolds Γ _ ρ bs ι).mpr
  exact ⟨hΓe, generationMonotone hF e (envInterpretValid hF hΓ hρ hbs hι)
    (by exact hTU ρ bs ι hρ hbs hι hC) (by exact hεη ρ bs ι hρ hbs hι hC) hg⟩

/-- All fresh existential variables remain inside the typing derivation.
The continuation is the proof obligation for the corresponding syntax rule. -/
theorem inferenceExistsCase (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ e T ε) (hd : e.Declared sig)
    (he : Entails S M Δ C (infer sig Γ e T ε))
    (hgen : generate sig e T ε = .exists_ ks D)
    (hbody : JudgmentWF S (ks ++ Δ) ((Γ.shift ks.length).letIn D)
      (Γ.shift ks.length) e (T.shift ks.length 0) (ε.shift ks.length 0) →
      Typing S M sig (ks ++ Δ) ((Γ.shift ks.length).letIn D)
        (Γ.shift ks.length) e (T.shift ks.length 0) (ε.shift ks.length 0)) :
    Typing S M sig Δ C Γ e T ε := by
  have hg := generationWF hF.signature hsig hw.2.2.2.1.1 hw.2.2.2.2.1 hw.2.2.2.2.2
  rw [hgen] at hg
  have hscope := generationScope (T := T) (ε := ε) hd
  rw [hgen] at hscope
  change D.fpi = e.fv at hscope
  have hΓ := envShiftWF hw.2.2.1 ks
  have hD : ((Γ.shift ks.length).letIn D).WF S (ks ++ Δ) 0 :=
    envLetInWF hΓ (by simpa [Env.shift] using hg.2)
  have hf : ((Γ.shift ks.length).letIn D).fpi = ∅ := by
    rw [envLetInFpi hΓ]
    apply Finset.sdiff_eq_empty_iff_subset.mpr
    simpa only [Constraint.fpi, Env.dpi, Env.shift, List.map_map, Function.comp_def,
      hscope] using hw.2.2.2.1.2
  have hsc : e.Scoped (Γ.shift ks.length) := by
    simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def] using hw.2.2.2.1
  have ht := hbody ⟨hD, hf, hΓ, hsc, kindShift hw.2.2.2.2.1 ks,
    kindShift hw.2.2.2.2.2 ks⟩
  have hex := Typing.exists_ (sig := sig)
    (Γ := Γ) (e := e) (T := T) (ε := ε) ⟨⟨hg.1, hD⟩, hf, hw.2.2⟩ ht
  apply Typing.strengthen hw hex
  intro ρ bs ι hρ hbs hι hC
  apply (envLetInExists hw.2.2.1 ks D ρ bs ι).mp
  simpa only [infer, hgen] using he ρ bs ι hρ hbs hι hC


/-- Value-let soundness uses the closed generated scheme. Both induction
hypotheses are for strict subterms and are generalized over typing contexts. -/
theorem inferenceValueLet (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.letE rhs body) T ε)
    (hd : rhs.Declared sig) (hv : Value rhs)
    (he : Entails S M Δ C (infer sig Γ (.letE rhs body) T ε))
    (ihr : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ rhs T ε →
      Entails S M Δ C (infer sig Γ rhs T ε) → Typing S M sig Δ C Γ rhs T ε)
    (ihb : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ body T ε →
      Entails S M Δ C (infer sig Γ body T ε) → Typing S M sig Δ C Γ body T ε) :
    Typing S M sig Δ C Γ (.letE rhs body) T ε := by
  have hr : rhs.Scoped Γ := ⟨hw.2.2.2.1.1.1,
    fun x hx => hw.2.2.2.1.2 (Finset.mem_union_left _ hx)⟩
  let s := generatedScheme sig Γ rhs
  let D := infer sig (Γ.shift 1) rhs (.bound 0) .empty
  have hsw : s.WF S Δ 0 := generatedSchemeWF hF.signature hsig hw.2.2.1 hr
  have hsf : s.fpi = ∅ := generatedSchemeScope hw.2.2.1 hr hd
  have hDf : D.fpi = ∅ := hsf
  have hp : Env.WF S Δ (Γ.push s) := by
    refine ⟨hw.2.2.1.1, ?_⟩
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact ⟨hsw, hsf⟩
    · exact hw.2.2.1.2 t ht
  have hbsc : body.Scoped (Γ.push s) := by
    refine ⟨?_, fun x hx => hw.2.2.2.1.2 (Finset.mem_union_right _ hx)⟩
    simpa [Env.push] using hw.2.2.2.1.1.2
  have heBody : Entails S M Δ C (infer sig (Γ.push s) body T ε) :=
    entailsTrans he (valueLetGeneration hF.signature hsig hw.2.2.1 hr hd hv).1
  have htBody := ihb Δ C (Γ.push s) T ε
    ⟨hw.1, hw.2.1, hp, hbsc, hw.2.2.2.2⟩ heBody
  have hrsc : rhs.Scoped (Γ.shift 1) := by
    simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def] using hr
  have hright := ihr ([0] ++ Δ) (.conj (C.shift 1 0) D) (Γ.shift 1) (.bound 0) .empty
    ⟨⟨constraintShiftWF hw.1 [0], hsw.2.1⟩,
      by simp only [Constraint.fpi, constraintShiftFpi, hw.2.1, hDf, Finset.empty_union],
      envShiftWF hw.2.2.1 [0], hrsc, .bound rfl hF.signature.1, emptyKind hF.signature⟩
    (fun _ _ _ _ _ _ h => h.2)
  apply Typing.letPoly (ks := [0]) (D := D) (A := .bound 0) hw hv hright _ htBody
  intro ρ bs ι hρ hbs hι hC
  have hpe := ((envLetInHolds _ _ _ _ _).mp (heBody ρ bs ι hρ hbs hι hC)).1
  exact ((envPushExists hsw hsf ρ bs ι).mp hpe).2

end EHMX
