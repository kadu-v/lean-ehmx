import HMX.LocallyNameless.Proofs.InferenceSupport

namespace HMX.LN.Proofs

/-- Scheme inclusion compares the declared scheme with the closed generated scheme;
C-LetDup then restores the unprefixed scheme used by Figure 10-9. -/
theorem completenessLet (hF : Framework S M I) (C D : Constraint) (Γ : Env)
    (t u : Expr) (T U : Ty) (xs : List TVar) (L : Finset Nat)
    (hw : JudgmentWF S (.conj C (D.existsNames xs)) Γ (.letE t u) (.mono U))
    (htw : JudgmentWF S (.conj C D) Γ t (.mono T)) (hts : t.fpi ⊆ Γ.dpi)
    (hn : xs.Nodup) (hf : Disjoint xs.toFinset (C.fv ∪ Γ.fv))
    (hgen : Entails S M (.conj C D) (infer Γ t T))
    (hbody : ∀ z, z ∉ L → Entails S M (.conj C (D.existsNames xs))
      (infer (Γ ++ [(.var z,Scheme.generalize xs D T)])
        (Expr.openAt 0 (.ident (.free (.var z))) u) U)) :
    Entails S M (.conj C (D.existsNames xs)) (infer Γ (.letE t u) U) := by
  have hΓ := hw.2.1
  have hΓf := hw.2.2.2.2.2.1
  have hC := htw.1.1
  have hD := htw.1.2
  have hT := htw.2.2.2.1.2.2
  have hU := hw.2.2.2.1.2.2
  have hCf := (Finset.union_eq_empty.mp htw.2.2.2.2.1).1
  have hk := (existsNamesWFReflect S xs D hw.1.2).1
  obtain ⟨X,hX,hXF⟩ := freshSameKind 0 (C.fv ∪ Γ.fv ∪ D.fv ∪ T.fv ∪ U.fv)
  have hxF : X ∉ C.fv ∪ Γ.fv ∪ D.fv ∪ T.fv := fun hm => hXF (Finset.mem_union_left _ hm)
  have hxΓ : X ∉ Γ.fv := fun hm => hxF (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  have hxU : X ∉ U.fv := fun hm => hXF (Finset.mem_union_right _ hm)
  let s := closedGeneratedScheme Γ t X
  let σ := Scheme.generalize xs D T
  have hs := closedGenerationWF S hF.1.1 Γ t X hΓ hΓf htw.2.2.1 hts hX hxΓ
  have hσ : σ.WF S [] 0 := generalizeWF S xs D T 0 hk hD hT
  have hi := generalizedLetComparison S M I hF C Γ t xs D T X hC hD hT hΓ hΓf
    htw.2.2.1 hn hk hf hX hxF hgen
  obtain ⟨z,hz⟩ := Finset.exists_notMem (L ∪ u.fpi.image idNumber)
  have hzL : z ∉ L := fun hm => hz (Finset.mem_union_left _ hm)
  have hzu : Id.var z ∉ u.fpi := fun hm => hz (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨.var z,hm,rfl⟩))
  let B := generate (Expr.openAt 0 (.ident (.free (.var z))) u) U
  have hBo := exprOpenNameLC u z 0 hw.2.2.1.2
  have hB : B.WF S [] 0 := generationWF S hF.1.1 0 _ U hBo hU
  have hEq : infer Γ (.letE t u) U =
      (Γ ++ [(Id.var z,Scheme.generalize [X] (generate t (.free X)) (.free X))]).letIn B := by
    rw [infer,generateLetFresh t u U X hX hxU,letInSnoc,generateLetNameScheme u z U _ hzu]
  have hdup := letDup S M hF.1 Γ (.var z) [X] (generate t (.free X)) (.free X) B
    hΓ hΓf (by simp) (by simp [hxΓ])
    (hEq ▸ inferWF hF.1.1 hΓ hw.2.2.1 hU)
    (inferWF hF.1.1 (envSnocWF Γ (.var z) s hΓ hs.1) hBo hU)
  intro ρ ι hρ hι hh
  rw [hEq]
  apply hdup.2 ρ ι hρ hι
  have hb := hbody z hzL ρ ι hρ hι hh
  change ((Γ ++ [(Id.var z,σ)]).letIn B).Holds S M ρ ι at hb
  rw [letInSnoc] at hb ⊢
  obtain ⟨hr,hb⟩ := (letInReady S M ρ Γ ι _).mp hb
  apply (letInReady S M ρ Γ ι _).mpr
  refine ⟨hr,?_⟩
  exact letSchemeMonotonicity S M hF.1 C (.var z) σ s B hC hσ hs.1 hB hi
    ρ (extendEnv S M ρ Γ ι) hρ (extendEnvValid S M hF.1 ρ Γ ι hρ hΓ hι)
    ⟨(closedHoldsExtend hF.1 Γ C hΓ hC hCf ρ ι hρ hι).mpr hh.1,hb⟩

/-- Completeness for Figure 10-8. Feasibility is introduced after induction so
that each premise can supply the environment required by its own judgment. -/
theorem alternateInferenceCompleteness (hF : Framework S M I)
    (hd : AlternateTyping S M C Γ t T) :
    Entails S M C Γ.exists_ → Entails S M C (infer Γ t T) := by
  induction hd with
  | @varInst C D Γ x T xs hw hn hl =>
      intro hΓe
      have hT := hw.2.2.2.1.2.2
      have hs := hw.2.1 _ (lookupMember Γ x _ hl)
      have hp := generalizeWFReflect S xs D T hs
      have hlookup := prefixLookup S M hF.1 Γ x _ T hw.2.1 hw.2.2.2.2.2.1 hl
        (inferWF hF.1.1 hw.2.1 hw.2.2.1 hT)
        ⟨envExistsWF Γ hw.2.1,instanceConstraintWF hF.1.1 _ T hs hT⟩
      intro ρ ι hρ hι hh
      apply hlookup.2 ρ ι hρ hι
      refine ⟨hΓe ρ ι hρ hι hh,?_⟩
      apply (instanceConstraintHolds S M hF.1 ρ ι _ T hρ hs hT).mpr
      exact generalizeSelfMember xs hp.1 D T hp.2.1 hT ρ ι hρ hh.2 _
        ⟨evalKind S M hF.1 ρ hρ T 0 hT,
          ((leHolds S M ρ ι 0 T T).mp (subRefl S M hF.1 T 0 hT ρ ι hρ hι trivial)).2.2⟩
  | @abs C Γ t T U L hw hd ih =>
      intro hΓe
      obtain ⟨z,hz⟩ := Finset.exists_notMem (L ∪ t.fpi.image idNumber)
      have hzL : z ∉ L := fun hm => hz (Finset.mem_union_left _ hm)
      have hzt : Id.var z ∉ t.fpi := fun hm => hz (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨.var z,hm,rfl⟩))
      have hbw := alternateWF (hd z hzL)
      have hT := hbw.2.1 (.var z,.mono T) (by simp)
      have hTk : T.HasKind S [] 0 := hT.2.2
      have hU := hbw.2.2.2.1.2.2
      have hb := ih z hzL (envSnocRealizable hF.1 C Γ (.var z) (.mono T) hw.2.1 hT rfl hΓe
        (fun ρ ι _ _ _ => monoExists S M ρ ι T))
      have he := lemma10_4_7 S M I hF t z T U hw.2.2.1 hzt hTk hU
      intro ρ ι hρ hι hh
      apply prefixEntails hF.1 Γ hw.2.1 _ _ he.2 ρ ι hρ hι
      have hh' := hb ρ ι hρ hι hh
      change ((Γ ++ [(Id.var z,Scheme.mono T)]).letIn _).Holds S M ρ ι at hh'
      rw [letInSnoc] at hh'
      exact hh'
  | @app C Γ t u U T hw ht hu iht ihu =>
      intro hΓe
      have htw := alternateWF ht
      have huw := alternateWF hu
      have hT := huw.2.2.2.1.2.2
      have hU := hw.2.2.2.1.2.2
      have hgt := generationWF S hF.1.1 0 t _ htw.2.2.1 htw.2.2.2.1.2.2
      have hgu := generationWF S hF.1.1 0 u _ huw.2.2.1 hT
      have hp := prefixConjunction S M hF.1 Γ (generate t (.arrow T U)) (generate u T)
        (letInWF S Γ _ hw.2.1 ⟨hgt,hgu⟩)
        ⟨inferWF hF.1.1 hw.2.1 htw.2.2.1 htw.2.2.2.1.2.2,inferWF hF.1.1 hw.2.1 huw.2.2.1 hT⟩
      intro ρ ι hρ hι hh
      exact prefixEntails hF.1 Γ hw.2.1 _ _
        (generateApplicationEntails hF t u T U htw.2.2.1 huw.2.2.1 hT hU) ρ ι hρ hι
        (hp.2 ρ ι hρ hι ⟨iht hΓe ρ ι hρ hι hh,ihu hΓe ρ ι hρ hι hh⟩)
  | @letGen C Γ t u U D T xs L hw hn hf ht hu iht ihu =>
      intro hΓe
      have htw := alternateWF ht
      have hk := (existsNamesWFReflect S xs D hw.1.2).1
      have hT := htw.2.2.2.1.2.2
      have hs := generalizeWF S xs D T 0 hk htw.1.2 hT
      have hsf : (Scheme.generalize xs D T).fpi = ∅ := by
        rw [generalizeFpi]; exact (Finset.union_eq_empty.mp htw.2.2.2.2.1).2
      have hinitReady : Entails S M (.conj C D) Γ.exists_ := by
        intro ρ ι hρ hι hh
        exact hΓe ρ ι hρ hι ⟨hh.1,existsNamesIntro xs D hk htw.1.2 ρ ι hρ hι hh.2⟩
      obtain ⟨d,hd⟩ := alternateToTyping ht
      apply completenessLet hF C D Γ t u T U xs L hw htw (derivationScope hd) hn hf (iht hinitReady)
      intro z hz
      exact ihu z hz (envSnocRealizable hF.1 (.conj C (D.existsNames xs)) Γ (.var z) _
        hw.2.1 hs hsf hΓe (fun _ _ _ _ hh => hh.2))
  | @sub C Γ t U T hw hd hle ih =>
      intro hΓe
      have hdw := alternateWF hd
      have hT := hdw.2.2.2.1.2.2
      have hU := hw.2.2.2.1.2.2
      have hp := prefixLeRight S M Γ (generate t T) 0 T U
      intro ρ ι hρ hι hh
      exact prefixEntails hF.1 Γ hw.2.1 _ _ (lemma10_4_5 S M I hF t T U hw.2.2.1 hT hU)
        ρ ι hρ hι (hp.2 ρ ι hρ hι ⟨ih hΓe ρ ι hρ hι hh,hle ρ ι hρ hι hh⟩)
  | @exists_ Γ t T xs C hw hn hk hf hd ih =>
      intro hΓe
      have hdw := alternateWF hd
      have hT := hw.2.2.2.1.2.2
      have hgen := generationWF S hF.1.1 0 t T hw.2.2.1 hT
      have hGI := inferWF hF.1.1 hw.2.1 hw.2.2.1 hT
      have hinner := ih (fun ρ ι hρ hι hh => hΓe ρ ι hρ hι
        (existsNamesIntro xs C hk hdw.1 ρ ι hρ hι hh))
      have hquant := prefixExists S M hF.1 Γ xs (generate t T) hn
        (hf.mono_right Finset.subset_union_left)
        (letInWF S Γ _ hw.2.1 (existsNamesWF S xs _ 0 hk hgen))
        (existsNamesWF S xs _ 0 hk hGI)
      have hunused := existsUnusedLaw S M hF.1 xs (generate t T)
        ((hf.mono_right Finset.subset_union_right).mono_right (generationFreeVariables t T).1)
        (existsNamesWF S xs _ 0 hk hgen) hgen
      intro ρ ι hρ hι hh
      obtain ⟨vs,hvs,hc⟩ := (existsNamesHolds S M ρ ι xs C hdw.1).mp hh
      have hq := (existsNamesHolds S M ρ ι xs (infer Γ t T) hGI).mpr
        ⟨vs,hvs,hinner _ ι (assignBlockValid S M ρ xs vs hρ hvs) hι hc⟩
      exact prefixEntails hF.1 Γ hw.2.1 _ _ hunused.1 ρ ι hρ hι (hquant.2 ρ ι hρ hι hq)
  | @convert D Δ t T C Γ hw hd he hΓ ih =>
      intro hΔe
      have hdw := alternateWF hd
      have hΓe : Entails S M C Γ.exists_ := by
        intro ρ ι hρ hι hh
        have hp := envBinderSemantics hF.1 Γ Δ hΓ hdw.2.1 hw.2.1 ρ ι hρ hι
        exact (envExistsHolds S M ρ ι Γ).mpr (hp.2.mpr
          ((envExistsHolds S M ρ ι Δ).mp (hΔe ρ ι hρ hι (he.1 ρ ι hρ hι hh))))
      intro ρ ι hρ hι hh
      exact (prefixBinderEquivalent hF.1 Γ Δ hΓ hdw.2.1 hw.2.1 (generate t T)).1
        ρ ι hρ hι (ih hΓe ρ ι hρ hι (he.2 ρ ι hρ hι hh))

/-- ATTAPL 10.4.8 (Completeness), filling in the proof omitted on p.434.
The public proposition and its environment-feasibility hypothesis are unchanged. -/
theorem theorem10_4_8_completeness (S : Signature) (M : Model) (I : Set Nat) :
    HMX.LN.theorem10_4_8_completeness S M I := by
  intro hF C Γ t T hΓe _ hd
  exact alternateInferenceCompleteness hF ((theorem10_3_4 S M I hF C Γ t T).mpr hd) hΓe

end HMX.LN.Proofs
