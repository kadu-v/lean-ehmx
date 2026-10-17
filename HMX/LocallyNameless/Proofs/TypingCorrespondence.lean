import HMX.LocallyNameless.Proofs.DecodingSupport

namespace HMX.LN.Proofs

/-- The induction permits semantic representatives of intermediate qualifications.
It never requires the ambient environment to be realizable. -/
theorem decodingDerivation (hM : M.Requirements S) (hd : Derivation S M C Γ t s d) :
    ∀ C' Γ' s', ConstraintRepresentation S M C C' → EnvRepresentation S M Γ Γ' →
      SchemeRepresentation S M s s' →
      ∃ t' : HMX.Expr, ofExpr [] t' = t ∧ HMX.Typing S M C' Γ' t' s' := by
  induction hd with
  | @var C Γ x s hw hl hr =>
    intro C' Γ' s' hc hΓ hs
    obtain ⟨r,hlr,hsr⟩ := envRepresentationLookup hΓ hl
    have hp : HMX.Typing S M C' Γ' (.ident x) r :=
      ⟨_,.var (decodingJudgment hw hc hΓ hsr) hlr (fun ρ ι hρ hι hh =>
        (schemeRepresentationExistsHolds hsr ρ ι hρ).mpr (hr ρ ι hρ hι ((hc.2.2.2 ρ ι hρ).mp hh)))⟩
    exact ⟨.ident x,rfl,(HMX.Proofs.schemeConversionTyping hM
      (equalSchemeRepresentations hM hsr hs rfl hw.2.2.2.2.2.2)).mp hp⟩
  | @abs C Γ t T U d L hw hd ih =>
    intro C' Γ' s' hc hΓ hs
    obtain ⟨z,hz⟩ := Finset.exists_notMem (L ∪ t.fpi.image idNumber)
    have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
    have hzt : Id.var z ∉ t.fpi := fun h => hz (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨.var z,h,rfl⟩))
    have hb := derivationWF (hd z hzL)
    have hT : T.HasKind S [] 0 :=
      (hb.2.1 (Id.var z,.mono T) (List.mem_append_right _ (by simp))).2.2
    have hU := hb.2.2.2.1.2.2
    have hTr := schemeRepresentationMono T hT (M := M)
    have hUr := schemeRepresentationMono U hU (M := M)
    obtain ⟨u,hu,hpu⟩ := ih z hzL C' _ _ hc (envRepresentationAppend hΓ hTr (.var z)) hUr
    have hAr := schemeRepresentationMono (.arrow T U) hw.2.2.2.1.2.2 (M := M)
    have hpw := decodingJudgment hw hc hΓ hAr
    rw [namedTyArrow] at hpw
    have hp : HMX.Typing S M C' Γ' (.lam z u) (.mono (namedTy (.arrow T U))) := by
      rw [namedTyArrow]
      exact ⟨_,.abs hpw hpu.choose_spec⟩
    exact ⟨.lam z u,decodingLam t u z hzt hu,
      decodingFinish hM hc hc hAr hs hw.2.2.2.2.1 hw.2.2.2.2.2.2 hp⟩
  | @app C Γ t u U T d e hw ht hu iht ihu =>
    intro C' Γ' s' hc hΓ hs
    have hT := (derivationWF hu).2.2.2.1.2.2
    have hA := (derivationWF ht).2.2.2.1.2.2
    have hU := hw.2.2.2.1.2.2
    have hUr := schemeRepresentationMono U hU (M := M)
    obtain ⟨t',ht',hpt⟩ := iht C' Γ' _ hc hΓ (schemeRepresentationMono _ hA)
    obtain ⟨u',hu',hpu⟩ := ihu C' Γ' _ hc hΓ (schemeRepresentationMono T hT)
    rw [namedTyArrow] at hpt
    have hp : HMX.Typing S M C' Γ' (.app t' u') (.mono (namedTy U)) :=
      ⟨_,.app (decodingJudgment hw hc hΓ hUr) hpt.choose_spec hpu.choose_spec⟩
    exact ⟨.app t' u',congrArg₂ Expr.app ht' hu',
      decodingFinish hM hc hc hUr hs hw.2.2.2.2.1 hw.2.2.2.2.2.2 hp⟩
  | @letE C Γ t u T s d e L hw ht hu iht ihu =>
    intro C' Γ' s' hc hΓ hs
    obtain ⟨r,hr⟩ := schemeRepresentationExists s (derivationWF ht).2.2.2.1 (M := M)
    obtain ⟨t',ht',hpt⟩ := iht C' Γ' r hc hΓ hr
    obtain ⟨z,hz⟩ := Finset.exists_notMem (L ∪ u.fpi.image idNumber)
    have hzL : z ∉ L := fun h => hz (Finset.mem_union_left _ h)
    have hzu : Id.var z ∉ u.fpi := fun h => hz (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨.var z,h,rfl⟩))
    have hTr := schemeRepresentationMono T hw.2.2.2.1.2.2 (M := M)
    obtain ⟨u',hu',hpu⟩ := ihu z hzL C' _ _ hc (envRepresentationAppend hΓ hr (.var z)) hTr
    have hp : HMX.Typing S M C' Γ' (.letE z t' u') (.mono (namedTy T)) :=
      ⟨_,.letE (decodingJudgment hw hc hΓ hTr) hpt.choose_spec hpu.choose_spec⟩
    refine ⟨.letE z t' u',?_,decodingFinish hM hc hc hTr hs hw.2.2.2.2.1 hw.2.2.2.2.2.2 hp⟩
    have he := Expr.lam.inj (decodingLam u u' z hzu hu')
    exact congrArg₂ Expr.letE ht' he
  | @gen C Γ t xs D T d hw hn hf hd ih =>
    intro K Γ' s' hK hΓ hs
    have hb := derivationWF hd
    have hT := hb.2.2.2.1.2.2
    have hk := (generalizeWFReflect S xs D T hw.2.2.2.1).1
    obtain ⟨C',hC⟩ := namedConstraintRepresentative C hb.1.1 (M := M)
    obtain ⟨D',hD⟩ := namedConstraintRepresentative D hb.1.2 (M := M)
    have hTr := schemeRepresentationMono T hT (M := M)
    have hsr : SchemeRepresentation S M (Scheme.generalize xs D T) (.all xs.toFinset D' (namedTy T)) :=
      ⟨xs,D,T,D',namedTy T,hn,hk,hb.1.2,hT,hD,namedTyEncoding T (tyKindLC T S [] 0 hT),rfl,rfl⟩
    have hCD := constraintRepresentationConj hC hD
    have hCE := constraintRepresentationConj hC (constraintRepresentationExists hD hb.1.2 xs hk)
    obtain ⟨t',ht',hpt⟩ := ih _ Γ' _ hCD hΓ hTr
    have hfresh : Disjoint xs.toFinset (C'.fv ∪ Γ'.fv) := by
      rw [hC.2.1,(envRepresentationProperties hΓ).2.1]; exact hf
    have hp : HMX.Typing S M (.conj C' (.exists_ xs.toFinset D')) Γ' t'
        (.all xs.toFinset D' (namedTy T)) :=
      ⟨_,.gen (decodingJudgment hw hCE hΓ hsr) hpt.choose_spec hfresh⟩
    exact ⟨t',ht',decodingFinish hM hCE hK hsr hs hw.2.2.2.2.1 hw.2.2.2.2.2.2 hp⟩
  | @inst C D Γ t T xs d hw hn hd ih =>
    intro K Γ' s' hK hΓ hs
    have hb := derivationWF hd
    have hg := generalizeWFReflect S xs D T hb.2.2.2.1
    obtain ⟨C',hC⟩ := namedConstraintRepresentative C hb.1 (M := M)
    obtain ⟨D',hD⟩ := namedConstraintRepresentative D hg.2.1 (M := M)
    have hsr : SchemeRepresentation S M (Scheme.generalize xs D T) (.all xs.toFinset D' (namedTy T)) :=
      ⟨xs,D,T,D',namedTy T,hn,hg.1,hg.2.1,hg.2.2,hD,namedTyEncoding T (tyKindLC T S [] 0 hg.2.2),rfl,rfl⟩
    obtain ⟨t',ht',hpt⟩ := ih C' Γ' _ hC hΓ hsr
    have hTr := schemeRepresentationMono T hg.2.2 (M := M)
    have hCD := constraintRepresentationConj hC hD
    have hp : HMX.Typing S M (.conj C' D') Γ' t' (.mono (namedTy T)) :=
      ⟨_,.inst (decodingJudgment hw hCD hΓ hTr) hpt.choose_spec⟩
    exact ⟨t',ht',decodingFinish hM hCD hK hTr hs hw.2.2.2.2.1 hw.2.2.2.2.2.2 hp⟩
  | @sub C Γ t U T d hw hd hr ih =>
    intro C' Γ' s' hc hΓ hs
    have hT := (derivationWF hd).2.2.2.1.2.2
    have hU := hw.2.2.2.1.2.2
    have hUr := schemeRepresentationMono U hU (M := M)
    obtain ⟨t',ht',hpt⟩ := ih C' Γ' _ hc hΓ (schemeRepresentationMono T hT)
    have he : HMX.Entails S M C' (.le 0 (namedTy T) (namedTy U)) := by
      intro ρ ι hρ hι hh
      have hb := hr ρ ι hρ hι ((hc.2.2.2 ρ ι hρ).mp hh)
      have heq := encodingSubtypeHolds S M ρ ι 0 (namedTy T) (namedTy U)
      rw [namedTyEncoding T (tyKindLC T S [] 0 hT),namedTyEncoding U (tyKindLC U S [] 0 hU)] at heq
      exact heq.mp hb
    have hp : HMX.Typing S M C' Γ' t' (.mono (namedTy U)) :=
      ⟨_,.sub (decodingJudgment hw hc hΓ hUr) hpt.choose_spec he⟩
    exact ⟨t',ht',decodingFinish hM hc hc hUr hs hw.2.2.2.2.1 hw.2.2.2.2.2.2 hp⟩
  | @exists_ Γ t s xs C d hw hn hk hf hd ih =>
    intro K Γ' s' hK hΓ hs
    obtain ⟨C',hC⟩ := namedConstraintRepresentative C (derivationWF hd).1 (M := M)
    obtain ⟨t',ht',hpt⟩ := ih C' Γ' s' hC hΓ hs
    have hEx := constraintRepresentationExists hC (derivationWF hd).1 xs hk
    have hfresh : Disjoint xs.toFinset (Γ'.fv ∪ s'.fv) := by
      rw [(envRepresentationProperties hΓ).2.1,(schemeRepresentationProperties hs).2.2.1]; exact hf
    have hp : HMX.Typing S M (.exists_ xs.toFinset C') Γ' t' s' :=
      ⟨_,.exists_ (decodingJudgment hw hEx hΓ hs) hpt.choose_spec hfresh⟩
    exact ⟨t',ht',decodingFinish hM hEx hK hs hs hw.2.2.2.2.1 hw.2.2.2.2.2.2 hp⟩
  | @convert D Δ t r C Γ s d hw hd hc hΓ hs ih =>
    intro D' Δ' r' hD hΔ hr
    have hb := derivationWF hd
    obtain ⟨C',hC⟩ := namedConstraintRepresentative C hb.1 (M := M)
    obtain ⟨Γ',hΓ',henv⟩ := envRepresentationBinderEq hM hΓ hΔ hb.2.2.2.2.2.1
    obtain ⟨s',hs'⟩ := schemeRepresentationExists s hb.2.2.2.1 (M := M)
    obtain ⟨t',ht',hpt⟩ := ih C' Γ' s' hC hΓ' hs'
    have hp := HMX.Proofs.typingEnvConversion hM hpt henv
    have hq := HMX.Proofs.typingConstraintEquivalent hp hD.1 (hD.2.2.1.trans hw.2.2.2.2.1)
      ⟨fun ρ ι hρ hι hh => (hD.2.2.2 ρ ι hρ).mpr (hc.1 ρ ι hρ hι ((hC.2.2.2 ρ ι hρ).mp hh)),
        fun ρ ι hρ hι hh => (hC.2.2.2 ρ ι hρ).mpr (hc.2 ρ ι hρ hι ((hD.2.2.2 ρ ι hρ).mp hh))⟩
    exact ⟨t',ht',(HMX.Proofs.schemeConversionTyping hM
      (binderEqSchemeRepresentations hM hs s' r' hs' hr hb.2.2.2.2.2.2)).mp hq⟩

theorem decodingTyping (hM : M.Requirements S)
    (h : Typing S M (ofConstraint [] [] C) (ofEnv Γ) (ofExpr [] t) (ofScheme [] [] s)) :
    HMX.Typing S M C Γ t s := by
  have hw := (encodingJudgmentWF C Γ t s).mp (derivationWF h.choose_spec)
  obtain ⟨u,hu,hp⟩ := decodingDerivation hM h.choose_spec C Γ s
    (encodingConstraintRepresentation C hw.1) (encodingEnvRepresentation Γ hw.2.1)
    (encodingSchemeRepresentation s hw.2.2.1)
  exact ⟨_,.convert hw hp.choose_spec ⟨fun _ _ _ _ h => h,fun _ _ _ _ h => h⟩
    (HMX.Proofs.envAlphaReflexive Γ) ((encodingAlpha.1 u t).mpr hu) (HMX.Proofs.schemeAlphaReflexive s)⟩

theorem typingCorrespondence (S : Signature) (M : Model) (I : Set Nat) :
    HMX.LN.typingCorrespondence S M I := by
  intro hF C Γ t s
  exact ⟨encodingTyping hF.1,decodingTyping hF.1⟩

end HMX.LN.Proofs
