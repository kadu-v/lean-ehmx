import HMX.LocallyNameless.Proofs.BindingTransport

namespace HMX.Proofs

theorem derivationWF (h : Derivation S M C Γ t s d) : JudgmentWF S C Γ s := by
  cases h <;> assumption

end HMX.Proofs

namespace HMX.LN.Proofs

theorem encodingMappedJudgment (h : HMX.JudgmentWF S C Γ s) (t : HMX.Expr)
    (f : Id → Id) (Δ : Env) (hΔ : Δ.WF S) (hΔf : Δ.fpi = ∅) :
    JudgmentWF S (ofConstraint [] [] C) Δ (exprMapIds f (ofExpr [] t)) (ofScheme [] [] s) := by
  have hw := (encodingJudgmentWF C Γ t s).mpr h
  exact ⟨hw.1,hΔ,exprMapIdsLC f _ 0 hw.2.2.1,hw.2.2.2.1,
    hw.2.2.2.2.1,hΔf,hw.2.2.2.2.2.2⟩

theorem envFvAppend (Γ Δ : Env) : (Γ ++ Δ).fv = Γ.fv ∪ Δ.fv := by
  induction Γ with
  | nil => simp [Env.fv]
  | cons p Γ ih => simpa only [List.cons_append, envFvCons, ih] using
      (Finset.union_assoc p.2.fv (Env.fv Γ) Δ.fv).symm

theorem envFpiAppend (Γ Δ : Env) : (Γ ++ Δ).fpi = Γ.fpi ∪ Δ.fpi := by
  induction Γ with
  | nil => simp [Env.fpi]
  | cons p Γ ih => simpa only [List.cons_append, envFpiCons, ih] using
      (Finset.union_assoc p.2.fpi (Env.fpi Γ) Δ.fpi).symm

theorem encodingExtendWF (Δ : Env) (hΔ : Δ.WF S) (hΔf : Δ.fpi = ∅)
    (s : HMX.Scheme) (hs : s.WF S) (hsf : s.fpi = ∅) (z : Nat) :
    Env.WF S (Δ ++ [(Id.var z,ofScheme [] [] s)]) ∧
      Env.fpi (Δ ++ [(Id.var z,ofScheme [] [] s)]) = ∅ := by
  constructor
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hΔ p hp
    · have he := List.mem_singleton.mp hp
      subst p
      exact encodingSchemeWF s hs [] []
  · rw [envFpiAppend, hΔf]
    simp [Env.fpi, (encodingFreeVariables.2.2 s).2, hsf]

theorem encodingExtendFv (Γ : HMX.Env) (Δ : Env) (hv : Δ.fv ⊆ Γ.fv)
    (s : HMX.Scheme) (z w : Nat) :
    Env.fv (Δ ++ [(Id.var w,ofScheme [] [] s)]) ⊆ HMX.Env.fv (Γ ++ [(Id.var z,s)]) := by
  rw [← encodingEnvFv (Γ ++ _), encodingEnvAppend, envFvAppend, envFvAppend,
    encodingEnvFv Γ]
  exact Finset.union_subset_union hv (by simp [ofEnv, Env.fv])

theorem encodingExtendLookup (Γ : HMX.Env) (Δ : Env) (f : Id → Id)
    (hl : ∀ x s, lookup Γ x = some s →
      ∃ r, lookup Δ (f x) = some r ∧ r.BinderEq (ofScheme [] [] s))
    (s : HMX.Scheme) (z w : Nat) (hw : Id.var w ∉ Δ.dpi) :
    ∀ x r, lookup (Γ ++ [(Id.var z,s)]) x = some r →
      ∃ u, lookup (Δ ++ [(Id.var w,ofScheme [] [] s)]) (Function.update f (Id.var z) (Id.var w) x) = some u ∧
        u.BinderEq (ofScheme [] [] r) := by
  intro x r hx
  rw [lookupAppendOne] at hx
  by_cases hz : Id.var z = x
  · subst x
    simp only [↓reduceIte, Option.some.injEq] at hx
    subst r
    exact ⟨_,by simp [lookupAppendOne],.refl⟩
  · simp only [hz, ↓reduceIte] at hx
    obtain ⟨u,hu,hr⟩ := hl x r hx
    have hwf : Id.var w ≠ f x := by
      intro he
      apply hw
      rw [he]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,lookupMember Δ (f x) u hu,rfl⟩)
    exact ⟨u,by simp [lookupAppendOne, Ne.symm hz, hwf, hu],hr⟩

theorem boundNamesFinset (A : Vars) : (boundNames A).toFinset = A := by
  ext X; simp [boundNamesMem]

theorem encodingArrow (T U : HMX.Ty) :
    ofTy [] (.arrow T U) = .arrow (ofTy [] T) (ofTy [] U) := by
  simp [ofTy, HMX.Ty.arrow, Ty.arrow]

theorem encodingConj (C D : HMX.Constraint) :
    ofConstraint [] [] (.conj C D) = .conj (ofConstraint [] [] C) (ofConstraint [] [] D) := rfl

/-- The target context may rename and shadow identifiers, but every observable
source lookup is preserved up to binder conversion. No context feasibility is needed. -/
theorem encodingDerivationMap (hM : M.Requirements S)
    (hd : HMX.Derivation S M C Γ t s d) :
    ∀ (f : Id → Id) (Δ : Env), Δ.WF S → Δ.fpi = ∅ → Δ.fv ⊆ Γ.fv →
      (∀ x s, lookup Γ x = some s →
        ∃ r, lookup Δ (f x) = some r ∧ r.BinderEq (ofScheme [] [] s)) →
      Derivation S M (ofConstraint [] [] C) Δ
        (exprMapIds f (ofExpr [] t)) (ofScheme [] [] s) d := by
  induction hd with
  | @var C Γ s x hw hl hr =>
    intro f Δ hΔ hΔf hv hlookup
    obtain ⟨r,hlr,hs⟩ := hlookup x s hl
    have he := encodingMappedJudgment hw (.ident x) f Δ hΔ hΔf
    have hrw := hΔ _ (lookupMember Δ (f x) r hlr)
    have hrf : r.fpi = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have hy' : y ∈ Δ.fpi := (memUnionFold (fun p : Id × Scheme => p.2.fpi) Δ y).mpr
        ⟨_,lookupMember Δ (f x) r hlr,hy⟩
      simp [hΔf] at hy'
    have hvw : JudgmentWF S (ofConstraint [] [] C) Δ (.ident (.free (f x))) r :=
      ⟨he.1,hΔ,trivial,hrw,he.2.2.2.2.1,hΔf,hrf⟩
    have hr' : Entails S M (ofConstraint [] [] C) (ofScheme [] [] s).exists_ := by
      rw [← encodingSchemeExists]
      exact (encodingEntails hM hw.1 (by cases s; exact ⟨hw.2.2.1.1,hw.2.2.1.2.1⟩)).mpr hr
    have hrr : Entails S M (ofConstraint [] [] C) r.exists_ := by
      intro ρ ι hρ hι hh
      have hn := (schemeExistsNonempty S M hM ρ ι hρ _ he.2.2.2.1).mp (hr' ρ ι hρ hι hh)
      apply (schemeExistsNonempty S M hM ρ ι hρ r hrw).mpr
      have eq := schemeBinderEq S M ρ ι r _ hs (fun _ => ρ (0,0)) (fun _ => ∅)
      change r.denote S M ρ ι = (ofScheme [] [] s).denote S M ρ ι at eq
      rw [eq]; exact hn
    exact .convert he (.var hvw hlr hrr) ⟨fun _ _ _ _ h => h,fun _ _ _ _ h => h⟩ (envBinderEqRefl _) hs
  | @abs C Γ T U t d z hw hd ih =>
    intro f Δ hΔ hΔf hv hl
    have he := encodingMappedJudgment hw (.lam z t) f Δ hΔ hΔf
    simp only [encodingMono,encodingArrow,ofExpr,exprMapIds] at he ⊢
    apply Derivation.abs (Δ.dpi.image idNumber) he
    intro w hw
    have hw' : Id.var w ∉ Δ.dpi := fun h => hw (Finset.mem_image.mpr ⟨.var w,h,rfl⟩)
    have hs : (HMX.Scheme.mono T).WF S := by
      exact (HMX.Proofs.derivationWF hd).2.1 (Id.var z,HMX.Scheme.mono T) (List.mem_append_right _ (by simp))
    have hx := encodingExtendWF Δ hΔ hΔf (.mono T) hs rfl w
    have hp := ih (Function.update f (Id.var z) (Id.var w)) _ hx.1 hx.2
      (encodingExtendFv Γ Δ hv (.mono T) z w) (encodingExtendLookup Γ Δ f hl (.mono T) z w hw')
    simpa only [encodingMono,encodingExprOpenMap t [] z (Id.var w) f,List.length_nil,List.nil_append] using hp
  | @app C Γ U t T d u e hw ht hu iht ihu =>
    intro f Δ hΔ hΔf hv hl
    have he := encodingMappedJudgment hw (.app t u) f Δ hΔ hΔf
    have hp := iht f Δ hΔ hΔf hv hl
    have hq := ihu f Δ hΔ hΔf hv hl
    simp only [encodingMono,encodingArrow] at he hp hq ⊢
    exact .app he hp hq
  | @letE C Γ T t s d u e z hw ht hu iht ihu =>
    intro f Δ hΔ hΔf hv hl
    have he := encodingMappedJudgment hw (.letE z t u) f Δ hΔ hΔf
    simp only [encodingMono,ofExpr,exprMapIds] at he ⊢
    apply Derivation.letE (Δ.dpi.image idNumber) he (iht f Δ hΔ hΔf hv hl)
    intro w hw
    have hw' : Id.var w ∉ Δ.dpi := fun h => hw (Finset.mem_image.mpr ⟨.var w,h,rfl⟩)
    have hsw := HMX.Proofs.derivationWF ht
    have hx := encodingExtendWF Δ hΔ hΔf s hsw.2.2.1 hsw.2.2.2.2.2 w
    have hp := ihu (Function.update f (Id.var z) (Id.var w)) _ hx.1 hx.2
      (encodingExtendFv Γ Δ hv s z w) (encodingExtendLookup Γ Δ f hl s z w hw')
    simpa only [encodingMono,encodingExprOpenMap u [] z (Id.var w) f,List.length_nil,List.nil_append] using hp
  | @gen C A D Γ T t d hw hd hf ih =>
    intro f Δ hΔ hΔf hv hl
    have he := encodingMappedJudgment hw t f Δ hΔ hΔf
    have hp := ih f Δ hΔ hΔf hv hl
    simp only [encodingGeneralize,encodingConj,encodingExists,encodingMono] at he hp ⊢
    apply Derivation.gen he (boundNamesNodup A) ?_ hp
    rw [boundNamesFinset, (encodingFreeVariables.2.1 C).1]
    exact hf.mono_right (Finset.union_subset_union Finset.Subset.rfl hv)
  | @inst C D Γ T t A d hw hd ih =>
    intro f Δ hΔ hΔf hv hl
    have he := encodingMappedJudgment hw t f Δ hΔ hΔf
    have hp := ih f Δ hΔ hΔf hv hl
    simp only [encodingGeneralize,encodingMono,ofConstraint] at he hp ⊢
    exact .inst he (boundNamesNodup A) hp
  | @sub C Γ U t T d hw hd hr ih =>
    intro f Δ hΔ hΔf hv hl
    have he := encodingMappedJudgment hw t f Δ hΔ hΔf
    have hp := ih f Δ hΔ hΔf hv hl
    simp only [encodingMono] at he hp ⊢
    apply Derivation.sub he hp
    intro ρ ι hρ hι hh
    apply (encodingSubtypeHolds S M ρ ι 0 T U).mpr
    exact hr ρ ι hρ hι (((encodingSemantics S M hM ρ ι hρ hι).1 C hw.1).mp hh)
  | @exists_ A C Γ s t d hw hd hf ih =>
    intro f Δ hΔ hΔf hv hl
    have he := encodingMappedJudgment hw t f Δ hΔ hΔf
    rw [encodingExists] at he ⊢
    apply Derivation.exists_ he (boundNamesNodup A) ?_ ?_ (ih f Δ hΔ hΔf hv hl)
    · intro X hx; exact hw.1.1 X ((boundNamesMem A X).mp hx)
    · rw [boundNamesFinset,(encodingFreeVariables.2.2 s).1]
      exact hf.mono_right (Finset.union_subset_union hv Finset.Subset.rfl)
  | @convert D Δ s' C Γ t s d t' hw hd hc hΓ ht hs ih =>
    intro f Ξ hΞ hΞf hv hl
    have hΓ' := encodingEnvAlpha hΓ
    have hv' : Ξ.fv ⊆ Γ.fv := by
      rw [← encodingEnvFv Γ,envBinderEqFv hΓ',encodingEnvFv Δ]; exact hv
    have hl' : ∀ x s, lookup Γ x = some s →
        ∃ r, lookup Ξ (f x) = some r ∧ r.BinderEq (ofScheme [] [] s) := by
      intro x u hu
      have hu' : lookup (ofEnv Γ) x = some (ofScheme [] [] u) := by rw [encodingEnvLookup,hu]; rfl
      obtain ⟨v,hv,heq⟩ := envBinderEqLookup hΓ' hu'
      rw [encodingEnvLookup] at hv
      obtain ⟨v',hv',rfl⟩ := Option.map_eq_some_iff.mp hv
      obtain ⟨r,hr,heq'⟩ := hl x v' hv'
      exact ⟨r,hr,.trans heq' (.symm heq)⟩
    have hp := ih f Ξ hΞ hΞf hv' hl'
    rw [encodingAlpha.1 t t' |>.mp ht] at hp
    exact .convert (encodingMappedJudgment hw t' f Ξ hΞ hΞf) hp
      ((encodingEquivalent hM (HMX.Proofs.derivationWF hd).1 hw.1).mpr hc)
      (envBinderEqRefl _) (encodingAlpha.2.2 s s' hs)

theorem encodingDerivation (hM : M.Requirements S) (hd : HMX.Derivation S M C Γ t s d) :
    Derivation S M (ofConstraint [] [] C) (ofEnv Γ) (ofExpr [] t) (ofScheme [] [] s) d := by
  have hw := HMX.Proofs.derivationWF hd
  have hp := encodingDerivationMap hM hd id (ofEnv Γ) ((encodingEnvWF Γ).mpr hw.2.1)
    ((encodingEnvFpi Γ).trans hw.2.2.2.2.1) (by rw [encodingEnvFv]) (by
      intro x r hr
      exact ⟨ofScheme [] [] r,by simp only [encodingEnvLookup,id_eq,hr,Option.map_some],.refl⟩)
  simpa only [exprMapIdsIdentity] using hp

theorem encodingTyping (hM : M.Requirements S) (h : HMX.Typing S M C Γ t s) :
    Typing S M (ofConstraint [] [] C) (ofEnv Γ) (ofExpr [] t) (ofScheme [] [] s) :=
  ⟨_,encodingDerivation hM h.choose_spec⟩

end HMX.LN.Proofs
