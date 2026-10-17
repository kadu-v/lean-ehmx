import HMX.LocallyNameless.Proofs.NamedRepresentatives

namespace HMX.Proofs

open LN.Proofs

/-- Only alpha conversion and equivalent qualifications of the same monotype
are admitted here. This is a derived relation, not a new typing rule. -/
inductive SchemeConversion (S : Signature) (M : Model) : Scheme → Scheme → Prop where
  | alpha : s.WF S → r.WF S → s.fpi = ∅ → r.fpi = ∅ → s.Alpha r → SchemeConversion S M s r
  | qualification : (∀ X ∈ A, X.1 ∈ S.kinds) → D.WF S → E.WF S → T.HasKind S 0 →
      D.fpi = ∅ → E.fpi = ∅ → D.fv = E.fv → Equivalent S M D E →
      SchemeConversion S M (.all A D T) (.all A E T)
  | symm : SchemeConversion S M s r → SchemeConversion S M r s
  | trans : SchemeConversion S M s r → SchemeConversion S M r u → SchemeConversion S M s u

def EnvConversion (S : Signature) (M : Model) (Γ Δ : Env) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ SchemeConversion S M p.2 q.2) Γ Δ

theorem schemeConversionProperties (h : SchemeConversion S M s r) :
    s.WF S ∧ r.WF S ∧ s.fpi = ∅ ∧ r.fpi = ∅ ∧ s.fv = r.fv := by
  induction h with
  | @alpha s r hs hr hsf hrf ha =>
    exact ⟨hs,hr,hsf,hrf,(encodingFreeVariables.2.2 _).1.symm.trans
      ((schemeBinderEqFv (encodingAlpha.2.2 _ _ ha)).trans (encodingFreeVariables.2.2 _).1)⟩
  | qualification hk hD hE hT hDf hEf heq he =>
    exact ⟨⟨hk,hD,hT⟩,⟨hk,hE,hT⟩,hDf,hEf,by simp only [Scheme.fv,heq]⟩
  | symm h ih => exact ⟨ih.2.1,ih.1,ih.2.2.2.1,ih.2.2.1,ih.2.2.2.2.symm⟩
  | trans h g ih ij => exact ⟨ih.1,ij.2.1,ih.2.2.1,ij.2.2.2.1,ih.2.2.2.2.trans ij.2.2.2.2⟩

theorem schemeConversionTyping (hM : M.Requirements S) (h : SchemeConversion S M s r) :
    Typing S M C Γ t s ↔ Typing S M C Γ t r := by
  induction h with
  | @alpha s r hs hr hsf hrf ha =>
    exact ⟨fun h => typingSchemeAlpha h hr hrf ha,
      fun h => typingSchemeAlpha h hs hsf (schemeAlphaSymmetric ha)⟩
  | qualification hk hD hE hT hDf hEf hv he =>
    exact ⟨fun h => typingQualificationConversion hM h hE hEf he,
      fun h => typingQualificationConversion hM h hD hDf ⟨he.2,he.1⟩⟩
  | symm h ih => exact ih.symm
  | trans h g ih ij => exact ih.trans ij

theorem schemeConversionExists (hM : M.Requirements S) (h : SchemeConversion S M s r) :
    Equivalent S M s.exists_ r.exists_ := by
  induction h with
  | @alpha s r hs hr hsf hrf ha =>
    have hb := encodingAlpha.2.2 _ _ ha
    have he : ∀ ρ ι, ρ.Valid S M → ι.Valid M →
        (s.exists_.Holds S M ρ ι ↔ r.exists_.Holds S M ρ ι) := by
      intro ρ ι hρ hι
      have hs' := encodingSchemeWF s hs [] []
      have hr' := encodingSchemeWF r hr [] []
      have hse : s.exists_.WF S := by cases s; exact ⟨hs.1,hs.2.1⟩
      have hre : r.exists_.WF S := by cases r; exact ⟨hr.1,hr.2.1⟩
      have es := (encodingSemantics S M hM ρ ι hρ hι).1 s.exists_ hse
      have er := (encodingSemantics S M hM ρ ι hρ hι).1 r.exists_ hre
      rw [encodingSchemeExists] at es er
      apply es.symm.trans
      apply Iff.trans ?_ er
      rw [schemeExistsNonempty S M hM ρ ι hρ _ hs',schemeExistsNonempty S M hM ρ ι hρ _ hr']
      have eq := schemeBinderEq S M ρ ι _ _ hb (fun _ => ρ (0,0)) (fun _ => ∅)
      change (LN.ofScheme [] [] s).denote S M ρ ι = (LN.ofScheme [] [] r).denote S M ρ ι at eq
      rw [eq]
    exact ⟨fun ρ ι hρ hι hh => (he ρ ι hρ hι).mp hh,fun ρ ι hρ hι hh => (he ρ ι hρ hι).mpr hh⟩
  | qualification hk hD hE hT hDf hEf hv he =>
    constructor
    · rintro ρ ι hρ hι ⟨σ,hσ,ha,hh⟩; exact ⟨σ,hσ,ha,he.1 σ ι hσ hι hh⟩
    · rintro ρ ι hρ hι ⟨σ,hσ,ha,hh⟩; exact ⟨σ,hσ,ha,he.2 σ ι hσ hι hh⟩
  | symm h ih => exact ⟨ih.2,ih.1⟩
  | trans h g ih ij => exact ⟨fun ρ ι hρ hι hh => ij.1 ρ ι hρ hι (ih.1 ρ ι hρ hι hh),
      fun ρ ι hρ hι hh => ih.2 ρ ι hρ hι (ij.2 ρ ι hρ hι hh)⟩

theorem envConversionProperties (h : EnvConversion S M Γ Δ) :
    Γ.WF S ∧ Δ.WF S ∧ Γ.fpi = ∅ ∧ Δ.fpi = ∅ ∧ Γ.fv = Δ.fv := by
  induction h with
  | nil => exact ⟨by simp [Env.WF],by simp [Env.WF],rfl,rfl,rfl⟩
  | @cons p q Γ Δ hp ht ih =>
    have hs := schemeConversionProperties hp.2
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · exact hs.1
      · exact ih.1 r hr
    · intro r hr; rcases List.mem_cons.mp hr with rfl | hr
      · exact hs.2.1
      · exact ih.2.1 r hr
    · change p.2.fpi ∪ Env.fpi Γ = ∅; rw [hs.2.2.1,ih.2.2.1,Finset.union_self]
    · change q.2.fpi ∪ Env.fpi Δ = ∅; rw [hs.2.2.2.1,ih.2.2.2.1,Finset.union_self]
    · exact congrArg₂ (· ∪ ·) hs.2.2.2.2 ih.2.2.2.2

theorem envConversionLookupRel (h : EnvConversion S M Γ Δ) (x : Id) :
    Option.Rel (SchemeConversion S M) (lookup Γ x) (lookup Δ x) := by
  induction h with
  | nil => exact .none
  | @cons p q Γ Δ hp ht ih =>
    rw [lookupCons,lookupCons]
    generalize lookup Γ x = a at ih ⊢
    generalize lookup Δ x = b at ih ⊢
    cases ih with
    | some h => exact .some h
    | none =>
      rw [← hp.1]
      by_cases hx : x = p.1
      · simp only [hx,↓reduceIte]; exact .some hp.2
      · simp only [hx,↓reduceIte]; exact .none

theorem envConversionLookup (h : EnvConversion S M Γ Δ) (hl : lookup Γ x = some s) :
    ∃ r, lookup Δ x = some r ∧ SchemeConversion S M s r := by
  have hr := envConversionLookupRel h x
  rw [hl] at hr
  generalize lookup Δ x = b at hr ⊢
  cases hr with
  | some h => exact ⟨_,rfl,h⟩

theorem envConversionAppend (h : EnvConversion S M Γ Δ) (s : Scheme)
    (hs : s.WF S) (hsf : s.fpi = ∅) (x : Id) :
    EnvConversion S M (Γ ++ [(x,s)]) (Δ ++ [(x,s)]) :=
  List.rel_append h (.cons ⟨rfl,.alpha hs hs hsf hsf (schemeAlphaReflexive s)⟩ .nil)

theorem namedEnvFpiMember (Γ : Env) (p : Id × Scheme) (hp : p ∈ Γ) : p.2.fpi ⊆ Γ.fpi := by
  intro x hx
  exact (memUnionFold (fun p : Id × Scheme => p.2.fpi) Γ x).mpr ⟨p,hp,hx⟩

theorem envAlphaConversion (h : Env.Alpha Γ Δ) (hΓ : Γ.WF S) (hΔ : Δ.WF S)
    (hΓf : Γ.fpi = ∅) (hΔf : Δ.fpi = ∅) : EnvConversion S M Γ Δ := by
  induction h with
  | nil => exact .nil
  | @cons p q Γ Δ hp ht ih =>
    have hpf : p.2.fpi = ∅ := Finset.union_eq_empty.mp hΓf |>.1
    have hqf : q.2.fpi = ∅ := Finset.union_eq_empty.mp hΔf |>.1
    exact .cons ⟨hp.1,.alpha (hΓ p (by simp)) (hΔ q (by simp)) hpf hqf hp.2⟩
      (ih (fun r hr => hΓ r (List.mem_cons_of_mem p hr))
        (fun r hr => hΔ r (List.mem_cons_of_mem q hr))
        (Finset.union_eq_empty.mp hΓf).2 (Finset.union_eq_empty.mp hΔf).2)

theorem envConversionTrans (h : EnvConversion S M Γ Δ) (g : EnvConversion S M Δ Ξ) :
    EnvConversion S M Γ Ξ := by
  induction h generalizing Ξ with
  | nil => cases g; exact .nil
  | cons hp ht ih =>
    cases g with
    | cons gp gt => exact .cons ⟨hp.1.trans gp.1,.trans hp.2 gp.2⟩ (ih gt)

theorem judgmentEnvConversion (h : JudgmentWF S C Γ s) (hc : EnvConversion S M Γ Δ) :
    JudgmentWF S C Δ s := by
  have hp := envConversionProperties hc
  exact ⟨h.1,hp.2.1,h.2.2.1,h.2.2.2.1,hp.2.2.2.1,h.2.2.2.2.2⟩

theorem derivationEnvConversion (hM : M.Requirements S) (hd : Derivation S M C Γ t s d) :
    ∀ Δ, EnvConversion S M Γ Δ → Typing S M C Δ t s := by
  induction hd with
  | @var C Γ s x hw hl hr =>
    intro Δ hΔ
    obtain ⟨r,hlr,hsr⟩ := envConversionLookup hΔ hl
    have hp := schemeConversionProperties hsr
    have he := judgmentEnvConversion hw hΔ
    have hv : Typing S M C Δ (.ident x) r :=
      ⟨_,.var ⟨he.1,he.2.1,hp.2.1,he.2.2.2.1,he.2.2.2.2.1,hp.2.2.2.1⟩ hlr
        (fun ρ ι hρ hι hh => (schemeConversionExists hM hsr).1 ρ ι hρ hι (hr ρ ι hρ hι hh))⟩
    exact (schemeConversionTyping hM hsr).mpr hv
  | @abs C Γ T U t d z hw hd ih =>
    intro Δ hΔ
    have hs := (derivationWF hd).2.1 (Id.var z,.mono T) (List.mem_append_right _ (by simp))
    obtain ⟨d',hd'⟩ := ih _ (envConversionAppend hΔ (.mono T) hs rfl (.var z))
    exact ⟨_,.abs (judgmentEnvConversion hw hΔ) hd'⟩
  | app hw ht hu iht ihu =>
    intro Δ hΔ
    obtain ⟨d',ht'⟩ := iht Δ hΔ
    obtain ⟨e',hu'⟩ := ihu Δ hΔ
    exact ⟨_,.app (judgmentEnvConversion hw hΔ) ht' hu'⟩
  | @letE C Γ T t s d u e z hw ht hu iht ihu =>
    intro Δ hΔ
    obtain ⟨d',ht'⟩ := iht Δ hΔ
    have hs := derivationWF ht
    obtain ⟨e',hu'⟩ := ihu _ (envConversionAppend hΔ s hs.2.2.1 hs.2.2.2.2.2 (.var z))
    exact ⟨_,.letE (judgmentEnvConversion hw hΔ) ht' hu'⟩
  | gen hw hd hf ih =>
    intro Δ hΔ
    obtain ⟨d',hd'⟩ := ih Δ hΔ
    exact ⟨_,.gen (judgmentEnvConversion hw hΔ) hd' (by rw [← (envConversionProperties hΔ).2.2.2.2]; exact hf)⟩
  | inst hw hd ih =>
    intro Δ hΔ
    obtain ⟨d',hd'⟩ := ih Δ hΔ
    exact ⟨_,.inst (judgmentEnvConversion hw hΔ) hd'⟩
  | sub hw hd hr ih =>
    intro Δ hΔ
    obtain ⟨d',hd'⟩ := ih Δ hΔ
    exact ⟨_,.sub (judgmentEnvConversion hw hΔ) hd' hr⟩
  | exists_ hw hd hf ih =>
    intro Δ hΔ
    obtain ⟨d',hd'⟩ := ih Δ hΔ
    exact ⟨_,.exists_ (judgmentEnvConversion hw hΔ) hd' (by rw [← (envConversionProperties hΔ).2.2.2.2]; exact hf)⟩
  | @convert D Δ s' C Γ t s d t' hw hd hc hΓ ht hs ih =>
    intro Ξ hΞ
    have hw' := derivationWF hd
    have hp := ih Ξ (envConversionTrans
      (envAlphaConversion hΓ hw'.2.1 hw.2.1 hw'.2.2.2.2.1 hw.2.2.2.2.1) hΞ)
    exact ⟨_,.convert (judgmentEnvConversion hw hΞ) hp.choose_spec hc (envAlphaReflexive Ξ) ht hs⟩

theorem typingEnvConversion (hM : M.Requirements S) (h : Typing S M C Γ t s)
    (hc : EnvConversion S M Γ Δ) : Typing S M C Δ t s :=
  derivationEnvConversion hM h.choose_spec Δ hc

end HMX.Proofs
