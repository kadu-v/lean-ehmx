import EHMX.Proofs.Weakening
import EHMX.Proofs.SchemeInstantiation
import EHMX.Proofs.EvaluationContext
import EHMX.Goals

/-!
使用先は β・let・return と操作節の同時代入。
型付けの帰納仮定では、結論の制約を任意の強い制約へ変更できるようにする。
HMX.LN.Proofs.alternateTransform の制約強化に対応する構成。
スキームの値の具体化は型文脈の変更と制約強化の両方に対して保持する。
-/
namespace EHMX

theorem exprShiftAdd (e : Expr) (n m d : Nat) :
    (e.shift n d).shift m d = e.shift (n + m) d := by
  induction e generalizing d with
  | ident x =>
      cases x with
      | free x => rfl
      | bound i =>
          by_cases h : i < d
          · simp [Expr.shift, h]
          · have hn : ¬ i + n < d := by omega
            simp [Expr.shift, h, hn, Nat.add_assoc]
  | _ => simp_all [Expr.shift]

theorem typingWeakeningBlock (ht : Typing S M sig Δ C Γ e T ε)
    (hs : ∀ s ∈ pre, s.WF S Δ 0 ∧ s.fpi = ∅) :
    Typing S M sig Δ C {Γ with bound := pre ++ Γ.bound} (e.shift pre.length 0) T ε := by
  induction pre with
  | nil =>
      have hz : ∀ (e : Expr) d, e.shift 0 d = e := by
        intro e; induction e <;> intros <;> simp_all [Expr.shift]
        case ident x d => cases x <;> simp [Expr.shift]
      simpa [hz] using ht
  | cons s pre ih =>
      have h := typingWeakening (ih (fun t ht => hs t (by simp [ht]))) (hs s (by simp))
      simpa only [exprShiftAdd, List.length_cons, List.cons_append, Env.push] using h

theorem exprOpenOneLC (he : Expr.LCAt (d + 1 + n) e) (hv : Expr.LCAt n v) :
    (e.openAt d [v]).LCAt (d + n) := by
  induction e generalizing d with
  | ident x =>
      cases x with
      | free x => trivial
      | bound i =>
          simp only [Expr.openAt]
          by_cases hi : i < d
          · simp only [hi, ↓reduceIte, Expr.LCAt]; omega
          · simp only [hi, ↓reduceIte]
            by_cases heq : i = d
            · subst i
              simpa [Nat.add_comm] using exprShiftLC hv d 0
            · have hn : i - d ≠ 0 := by omega
              simp only [List.getElem?_singleton, hn, ↓reduceIte, List.length_singleton,
                Expr.LCAt]
              simp only [Expr.LCAt] at he
              omega
  | lam body ih =>
      have h := ih (d := d + 1) (by
        simpa only [Expr.LCAt, Nat.add_right_comm] using he)
      simpa only [Expr.openAt, Expr.LCAt, Nat.add_right_comm] using h
  | app f x ihf ihx => exact ⟨ihf he.1, ihx he.2⟩
  | letE rhs body ihr ihb =>
      refine ⟨ihr he.1, ?_⟩
      have h := ihb (d := d + 1) (by simpa only [Nat.add_right_comm] using he.2)
      simpa only [Nat.add_right_comm] using h
  | perform op arg ih => exact ih he
  | handle body op ret clause ihb ihr ihc =>
      refine ⟨ihb he.1, ?_, ?_⟩
      · have h := ihr (d := d + 1) (by simpa only [Nat.add_right_comm] using he.2.1)
        simpa only [Nat.add_right_comm] using h
      · have h := ihc (d := d + 2) (by simpa only [Nat.add_right_comm] using he.2.2)
        simpa only [Nat.add_right_comm] using h

theorem exprOpenOneFv {e v : Expr} (he : e.fv ⊆ xs) (hv : v.fv ⊆ xs) (d : Nat) :
    (e.openAt d [v]).fv ⊆ xs := by
  induction e generalizing d with
  | ident x =>
      cases x with
      | free x => exact he
      | bound i =>
          simp only [Expr.openAt]
          split
          · exact Finset.empty_subset _
          · split
            · rename_i u hu
              have huv : u = v := by simpa using (List.mem_singleton.mp (List.mem_of_getElem? hu))
              subst u; simpa only [exprShiftFv] using hv
            · exact Finset.empty_subset _
  | lam body ih => exact ih he _
  | app f x ihf ihx =>
      exact Finset.union_subset (ihf (Finset.union_subset_iff.mp he).1 _)
        (ihx (Finset.union_subset_iff.mp he).2 _)
  | letE rhs body ihr ihb =>
      exact Finset.union_subset (ihr (Finset.union_subset_iff.mp he).1 _)
        (ihb (Finset.union_subset_iff.mp he).2 _)
  | perform op arg ih => exact ih he _
  | handle body op ret clause ihb ihr ihc =>
      exact Finset.union_subset
        (Finset.union_subset (ihb (Finset.union_subset_iff.mp (Finset.union_subset_iff.mp he).1).1 _)
          (ihr (Finset.union_subset_iff.mp (Finset.union_subset_iff.mp he).1).2 _))
        (ihc (Finset.union_subset_iff.mp he).2 _)

def Env.removeAfter (Γ : Env) (pre post : List Scheme) : Env :=
  {Γ with bound := pre ++ post}

theorem envRemoveWF (h : Env.WF S Δ Γ) (hΓ : Γ.bound = pre ++ s :: post) :
    Env.WF S Δ (Γ.removeAfter pre post) := by
  refine ⟨h.1, ?_⟩
  intro t ht
  apply h.2 t
  rw [hΓ]
  rcases List.mem_append.mp ht with ht | ht
  · exact List.mem_append_left _ ht
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)

theorem judgmentOpenOne (hw : JudgmentWF S Δ C Γ e T ε)
    (hΓ : Γ.bound = pre ++ s :: post)
    (hv : v.Scoped {Γ with bound := post})
    (hD : Constraint.WF S Δ 0 D) (hDf : D.fpi = ∅) :
    JudgmentWF S Δ D (Γ.removeAfter pre post) (e.openAt pre.length [v]) T ε := by
  refine ⟨hD, hDf, envRemoveWF hw.2.2.1 hΓ, ⟨?_, ?_⟩, hw.2.2.2.2⟩
  · have he : e.LCAt (pre.length + 1 + post.length) := by
      simpa [hΓ, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hw.2.2.2.1.1
    simpa [Env.removeAfter] using exprOpenOneLC he hv.1
  · exact exprOpenOneFv hw.2.2.2.1.2 hv.2 _

/-- A replacement value supports every use of its scheme after type/effect
substitution and constraint strengthening. This is a local substitution premise,
not a model assumption or a safety axiom. -/
def RealizesScheme (S : Signature) (M : Model) (sig : OpSignature)
    (Δ : List Kind) (C : Constraint) (Γ : Env) (s : Scheme) (v : Expr) : Prop :=
  ∀ Δ' σ, BoundSubst.Valid S Δ Δ' σ → ∀ E T,
    E.WF S Δ' 0 → E.fpi = ∅ → Entails S M Δ' E (C.substBound σ) →
    T.HasKind S Δ' 0 → Entails S M Δ' E ((s.substBound σ).instanceConstraint T) →
    Typing S M sig Δ' E (Γ.substBound σ) v T .empty

theorem BoundSubst.validComp (hσ : BoundSubst.Valid S Δ Δ' σ)
    (hτ : BoundSubst.Valid S Δ' Δ'' τ) :
    BoundSubst.Valid S Δ Δ'' (fun i => (σ i).substBound τ) := by
  intro i k hi
  rcases hσ i k hi with ⟨j, hj, hk⟩ | hk
  · simpa only [hj, Ty.substBound] using hτ j k hk
  · exact Or.inr (kindSubstBound hk hτ)

theorem envSubstBoundComp (Γ : Env) (σ τ : BoundSubst) :
    (Γ.substBound σ).substBound τ = Γ.substBound (fun i => (σ i).substBound τ) := by
  cases Γ
  simp only [Env.substBound, List.map_map, Function.comp_def, substBoundComp.2]

theorem envShiftSubstBound (Γ : Env) (n : Nat) :
    Γ.shift n = Γ.substBound (fun i => .bound (i + n)) := by
  cases Γ
  simp only [Env.shift, Env.substBound, shiftSubstBound.2, Nat.not_lt_zero, ↓reduceIte]
  congr 1
  apply List.map_congr_left
  intro s _
  simpa only [Nat.not_lt_zero, ↓reduceIte] using shiftSubstBound.2 s n 0

theorem realizesSchemeShift (hF : EffectFramework S M)
    (hr : RealizesScheme S M sig Δ C Γ s v)
    (hC : Constraint.WF S Δ 0 C) (hD : Constraint.WF S (ks ++ Δ) 0 D)
    (he : Entails S M (ks ++ Δ) D (C.shift ks.length 0)) :
    RealizesScheme S M sig (ks ++ Δ) D (Γ.shift ks.length) (s.shift ks.length 0) v := by
  intro Δ' τ hτ E T hE hEf hED hT hinst
  have he' := entailsTrans hED (entailsSubstBound hF hτ hD (constraintShiftWF hC ks) he)
  have h := hr Δ' (fun i => (.bound (i + ks.length) : Ty).substBound τ)
    (BoundSubst.validComp (BoundSubst.validShift ks) hτ) E T hE hEf
  simp only [shiftSubstBound.1, shiftSubstBound.2, substBoundComp.1,
    substBoundComp.2, Nat.not_lt_zero, ↓reduceIte] at he' hinst
  have hv := h he' hT hinst
  simpa only [envShiftSubstBound, envSubstBoundComp] using hv

/-- Generalized typing supplies the portable scheme premise without selecting
syntactic representatives for the model's existential witnesses. -/
theorem generalizedValueRealizes (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (ht : Typing S M sig (ks ++ Δ) (.conj (C.shift ks.length 0) D)
      (Γ.shift ks.length) v A .empty)
    (hks : ∀ k ∈ ks, k ∈ S.kinds) (hC : Constraint.WF S Δ 0 C)
    (hΓ : Env.WF S Δ Γ) : RealizesScheme S M sig Δ C Γ (.all ks D A) v := by
  intro Δ' σ hσ E T hE hEf hEC hT hinst
  have ht' := typingTypeEffectSubstitution hF hsig ht _ (σ.lift ks.length)
    (BoundSubst.validLift hσ ks)
  simp only [Constraint.substBound, constraintShiftLiftSubst, envShiftLiftSubst,
    Ty.empty, Ty.substBound, List.map_nil] at ht'
  have hvscope : v.Scoped (Γ.substBound σ) := by
    simpa [Expr.Scoped, Env.substBound, Env.shift, Env.dpi, List.map_map, Function.comp_def]
      using (typingWF ht).2.2.2.1
  exact schemeValueInstantiation hF ht' hks
    ⟨hE, hEf, envSubstBoundWF hΓ hσ, hvscope, hT, emptyKind hF.signature⟩
    ((substBoundWF S).1 _ _ _ hC _ _ hσ) hEC hinst

@[simp] theorem envSubstBoundId (Γ : Env) : Γ.substBound Ty.bound = Γ := by
  cases Γ
  simp only [Env.substBound]
  simp [show Scheme.substBound Ty.bound = id from funext substBoundId.2]

theorem RealizesScheme.use (hr : RealizesScheme S M sig Δ D Γ s v)
    (hD : Constraint.WF S Δ 0 D) (hDf : D.fpi = ∅) (hT : Ty.HasKind S Δ T 0)
    (hi : Entails S M Δ D (s.instanceConstraint T)) :
    Typing S M sig Δ D Γ v T .empty := by
  have hvalid : BoundSubst.Valid S Δ Δ Ty.bound := fun i _ hi => Or.inl ⟨i, rfl, hi⟩
  have h := hr Δ Ty.bound hvalid D T hD hDf
  simp only [substBoundId.1, substBoundId.2, envSubstBoundId] at h
  exact h entailsRefl hT hi

theorem lookupRemoveBound {Γ : Env} (hΓ : Γ.bound = pre ++ s :: post) (hne : i ≠ pre.length) :
    (Γ.removeAfter pre post).lookup (.bound (if i < pre.length then i else i - 1)) =
      Γ.lookup (.bound i) := by
  simp only [Env.lookup, Env.removeAfter, hΓ]
  by_cases hi : i < pre.length
  · simp [hi, List.getElem?_append]
  · have hn : ¬ i - 1 < pre.length := by omega
    have he : i - pre.length = (i - 1 - pre.length) + 1 := by omega
    simp [hi, hn, List.getElem?_append, he]

theorem openBoundNe (hne : i ≠ d) :
    (Expr.ident (.bound i)).openAt d [v] =
      .ident (.bound (if i < d then i else i - 1)) := by
  simp only [Expr.openAt]
  by_cases hi : i < d
  · simp [hi]
  · have hn : i - d ≠ 0 := by omega
    simp [hi, hn]

/-- The stronger constraint D is generalized before induction. In the exists_
branch, substitution is finished under D.shift ∧ C, then existentially hidden. -/
theorem typingValueSubstitutionAux (hF : EffectFramework S M)
    (ht : Typing S M sig Δ C Γ e T ε) :
    ∀ D pre post s v, Γ.bound = pre ++ s :: post →
      D.WF S Δ 0 → D.fpi = ∅ → Entails S M Δ D C → Value v →
      v.Scoped {Γ with bound := post} →
      RealizesScheme S M sig Δ D {Γ with bound := post} s v →
      Typing S M sig Δ D (Γ.removeAfter pre post) (e.openAt pre.length [v]) T ε := by
  induction ht with
  | @var Δ C Γ x T t hw hl hi =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      have hi' := entailsTrans hDC hi
      have hw' := judgmentOpenOne hw hΓ hscope hD hDf
      cases x with
      | free x => exact .var hw' hl hi'
      | bound i =>
          by_cases heq : i = pre.length
          · subst i
            have hst : s = t := by simpa [Env.lookup, hΓ] using hl
            subst t
            have ht' := RealizesScheme.use hr hD hDf hw.2.2.2.2.1 hi'
            have hb := typingWeakeningBlock (pre := pre) ht' (fun t ht =>
              hw.2.2.1.2 t (by rw [hΓ]; exact List.mem_append_left _ ht))
            simpa [Expr.openAt, Env.removeAfter] using hb
          · rw [openBoundNe heq] at hw' ⊢
            exact .var hw' ((lookupRemoveBound hΓ heq).trans hl) hi'
  | @lam Δ C Γ body A ε B hw hb ih =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      have hb' := ih D (.mono A :: pre) post s v (by simp [Env.push, hΓ])
        hD hDf hDC hv hscope hr
      exact .lam (judgmentOpenOne hw hΓ hscope hD hDf) hb'
  | app hw hf hx ihf ihx =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      exact .app (judgmentOpenOne hw hΓ hscope hD hDf)
        (ihf _ _ _ _ _ hΓ hD hDf hDC hv hscope hr)
        (ihx _ _ _ _ _ hΓ hD hDf hDC hv hscope hr)
  | @letMono Δ C Γ rhs body B εrhs εbody A hw ht hb iht ihb =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      have hb' := ihb D (.mono A :: pre) post s v (by simp [Env.push, hΓ])
        hD hDf hDC hv hscope hr
      exact .letMono (judgmentOpenOne hw hΓ hscope hD hDf)
        (iht _ _ _ _ _ hΓ hD hDf hDC hv hscope hr) hb'
  | @letPoly Δ C Γ rhs body B ε ks K A hw hval ht he hb iht ihb =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      let E : Constraint := .conj (D.shift ks.length 0) K
      have hE : E.WF S (ks ++ Δ) 0 := ⟨constraintShiftWF hD ks, (typingWF ht).1.2⟩
      have hEf : E.fpi = ∅ := by
        have hkf := (Finset.union_eq_empty.mp (typingWF ht).2.1).2
        simp [E, Constraint.fpi, constraintShiftFpi, hDf, hkf]
      have hEC : Entails S M (ks ++ Δ) E (.conj (C.shift ks.length 0) K) := by
        intro ρ bs ι hρ hbs hι h
        exact ⟨entailsShift hF ks hD hw.1 hDC _ _ _ hρ hbs hι h.1, h.2⟩
      have hr' := realizesSchemeShift hF hr hD hE
        (show Entails S M (ks ++ Δ) E (D.shift ks.length 0) from fun _ _ _ _ _ _ h => h.1)
      have ht' := iht E (pre.map (Scheme.shift ks.length 0))
        (post.map (Scheme.shift ks.length 0)) (s.shift ks.length 0) v
        (by simp [Env.shift, hΓ]) hE hEf hEC hv
        (by simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def] using hscope)
        (by simpa [Env.shift] using hr')
      have hb' := ihb D (.all ks K A :: pre) post s v (by simp [Env.push, hΓ])
        hD hDf hDC hv hscope hr
      apply Typing.letPoly (judgmentOpenOne hw hΓ hscope hD hDf)
        (valueOpening hval (by simpa using hv) _) ?_ (entailsTrans hDC he) hb'
      simpa [Env.removeAfter, Env.shift, E] using ht'
  | perform hw hs ha ht ih =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      exact .perform (judgmentOpenOne hw hΓ hscope hD hDf) hs ha
        (ih _ _ _ _ _ hΓ hD hDf hDC hv hscope hr)
  | @handle Δ C Γ body op ret clause B εout decl A εin hw hs hb he ht hc ihb iht ihc =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      have ht' := iht D (.mono A :: pre) post s v (by simp [Env.push, hΓ])
        hD hDf hDC hv hscope hr
      have hD' := constraintShiftWF hD decl.kinds
      have hDf' := (constraintShiftFpi D decl.kinds.length 0).trans hDf
      have hr' := realizesSchemeShift hF hr hD hD'
        (entailsRefl (S := S) (M := M))
      have hc' := ihc (D.shift decl.kinds.length 0)
        (.mono (.arrow decl.output (εout.shift decl.kinds.length 0) (B.shift decl.kinds.length 0)) ::
          .mono decl.input :: pre.map (Scheme.shift decl.kinds.length 0))
        (post.map (Scheme.shift decl.kinds.length 0)) (s.shift decl.kinds.length 0) v
        (by simp [Env.push, Env.shift, hΓ]) hD' hDf'
        (entailsShift hF decl.kinds hD hw.1 hDC) hv
        (by simpa [Expr.Scoped, Env.shift, Env.push, Env.dpi, List.map_map, Function.comp_def] using hscope)
        (by simpa [Env.shift, Env.push] using hr')
      exact .handle (judgmentOpenOne hw hΓ hscope hD hDf) hs
        (ihb _ _ _ _ _ hΓ hD hDf hDC hv hscope hr) (entailsTrans hDC he) ht'
        (by simpa [Env.removeAfter, Env.shift, Env.push] using hc')
  | sub hw ht hT hε ih =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      exact .sub (judgmentOpenOne hw hΓ hscope hD hDf)
        (ih _ _ _ _ _ hΓ hD hDf hDC hv hscope hr) (entailsTrans hDC hT) (entailsTrans hDC hε)
  | strengthen hw ht he ih =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      exact ih _ _ _ _ _ hΓ hD hDf (entailsTrans hDC he) hv hscope hr
  | @exists_ Δ ks C Γ e T ε hw ht ih =>
      intro D pre post s v hΓ hD hDf hDC hv hscope hr
      let E : Constraint := .conj (D.shift ks.length 0) C
      have hE : E.WF S (ks ++ Δ) 0 := ⟨constraintShiftWF hD ks, (typingWF ht).1⟩
      have hEf : E.fpi = ∅ := by
        simp [E, Constraint.fpi, constraintShiftFpi, hDf, (typingWF ht).2.1]
      have hr' := realizesSchemeShift hF hr hD hE
        (show Entails S M (ks ++ Δ) E (D.shift ks.length 0) from fun _ _ _ _ _ _ h => h.1)
      have ht' := ih E (pre.map (Scheme.shift ks.length 0))
        (post.map (Scheme.shift ks.length 0)) (s.shift ks.length 0) v
        (by simp [Env.shift, hΓ]) hE hEf
        (fun _ _ _ _ _ _ h => h.2) hv
        (by simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def] using hscope)
        (by simpa [Env.shift] using hr')
      have hw' := judgmentOpenOne hw hΓ hscope hD hDf
      have hex : Typing S M sig Δ (.exists_ ks E) (Γ.removeAfter pre post)
          (e.openAt pre.length [v]) T ε := by
        apply Typing.exists_ ⟨⟨hw.1.1, hE⟩, hEf, hw'.2.2⟩
        simpa [Env.shift, Env.removeAfter] using ht'
      apply Typing.strengthen hw' hex
      intro ρ bs ι hρ hbs hι hDholds
      obtain ⟨vs, hvs, hC⟩ := hDC _ _ _ hρ hbs hι hDholds
      refine ⟨vs, hvs, ?_, hC⟩
      have hlen := hvs.length_eq
      simpa only [← hlen] using (constraintShiftHolds hD ρ bs vs ι).mpr hDholds

/-- Full polymorphic-let substitution obligation, with the existing Goal type. -/
theorem schemeValueSubstitution (S : Signature) (M : Model) (sig : OpSignature) :
    SchemeValueSubstitutionGoal S M sig := by
  intro hA Δ C Γ v body ks D A T ε hv ht _ hb
  have hbw := typingWF hb
  have hsw := lookupWF hbw.2.2.1 (x := .bound 0) rfl
  have hΓ : Γ.WF S Δ := by
    refine ⟨hbw.2.2.1.1, ?_⟩
    intro s hs
    exact hbw.2.2.1.2 s (List.mem_cons_of_mem _ hs)
  have hr := generalizedValueRealizes hA.1 hA.2 ht hsw.1.1 hbw.1 hΓ
  have hscope : v.Scoped Γ := by
    simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def]
      using (typingWF ht).2.2.2.1
  exact typingValueSubstitutionAux hA.1 hb C [] Γ.bound (.all ks D A) v rfl
    hbw.1 hbw.2.1 entailsRefl hv hscope hr

@[simp] theorem constraintShiftZero (C : Constraint) (d : Nat) : C.shift 0 d = C := by
  rw [shiftSubstBound.1]
  simp only [Nat.add_zero, ite_self, substBoundId.1]

@[simp] theorem envShiftZero (Γ : Env) : Γ.shift 0 = Γ := by
  rw [envShiftSubstBound]
  simp only [Nat.add_zero, envSubstBoundId]

/-- Monomorphic substitution used by beta and handler return. -/
theorem valueSubstitution (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hv : Value v) (ht : Typing S M sig Δ C Γ v A .empty)
    (hb : Typing S M sig Δ C (Γ.push (.mono A)) body T ε) :
    Typing S M sig Δ C Γ (body.openAt 0 [v]) T ε := by
  apply schemeValueSubstitution S M sig ⟨hF, hsig⟩ Δ C Γ v body [] .truth A T ε hv
  · have hw := typingWF ht
    simpa only [List.nil_append, List.length_nil, constraintShiftZero, envShiftZero] using
      Typing.strengthen (C := C) (D := .conj C .truth)
        ⟨⟨hw.1, trivial⟩, by simpa [Constraint.fpi] using hw.2.1, hw.2.2⟩ ht
        (fun _ _ _ _ _ _ h => h.1)
  · exact fun _ _ _ _ _ _ _ => ⟨[], .nil, trivial⟩
  · exact hb

end EHMX
