import HMX.LocallyNameless.Proofs.GenerationProperties

namespace HMX.LN.Proofs

theorem generalizedInstanceExists (hM : M.Requirements S) (xs : List TVar) (D : Constraint) (A T : Ty)
    (hs : (Scheme.generalize xs D A).WF S [] 0) (hT : T.HasKind S [] 0)
    (hf : Disjoint xs.toFinset T.fv) :
    Equivalent S M ((Scheme.generalize xs D A).instanceConstraint T)
      ((Constraint.conj D (.le 0 A T)).existsNames xs) := by
  have hw := generalizeWFReflect S xs D A hs
  have hC : (Constraint.conj D (.le 0 A T)).WF S [] 0 :=
    ⟨hw.2.1,⟨hM.1.1,.cons hw.2.2 (.cons hT .nil)⟩⟩
  have hTc := tyKindLC T S [] 0 hT
  constructor
  · intro ρ ι hρ hι hh
    obtain ⟨hk,vs,hvs,hD,hAT⟩ := (generalizeDenote S M ρ ι xs D A hw.2.1 hw.2.2 _).mp
      ((instanceConstraintHolds S M hM ρ ι _ T hρ hs hT).mp hh)
    have hρ' := assignBlockValid S M ρ xs vs hρ hvs
    apply (existsNamesHolds S M ρ ι xs _ hC).mpr
    refine ⟨vs,hvs,hD,?_⟩
    apply (leHolds S M _ ι 0 A T).mpr
    rw [tyEvalAssignBlock M ρ xs vs T hTc hf]
    exact ⟨evalKind S M hM _ hρ' A 0 hw.2.2,hk,hAT⟩
  · intro ρ ι hρ hι hh
    obtain ⟨vs,hvs,hD,hAT⟩ := (existsNamesHolds S M ρ ι xs _ hC).mp hh
    have hp := (leHolds S M _ ι 0 A T).mp hAT
    rw [tyEvalAssignBlock M ρ xs vs T hTc hf] at hp
    apply (instanceConstraintHolds S M hM ρ ι _ T hρ hs hT).mpr
    exact (generalizeDenote S M ρ ι xs D A hw.2.1 hw.2.2 _).mpr ⟨hp.2.1,vs,hvs,hD,hp.2.2⟩

theorem prefixEntails (hM : M.Requirements S) (Γ : Env) (hΓ : Γ.WF S)
    (C D : Constraint) (h : Entails S M C D) : Entails S M (Γ.letIn C) (Γ.letIn D) := by
  intro ρ ι hρ hι hh
  obtain ⟨hr,hc⟩ := (letInReady S M ρ Γ ι C).mp hh
  exact (letInReady S M ρ Γ ι D).mpr
    ⟨hr,h ρ (extendEnv S M ρ Γ ι) hρ (extendEnvValid S M hM ρ Γ ι hρ hΓ hι) hc⟩

theorem prefixLeRight (S : Signature) (M : Model) (Γ : Env) (C : Constraint) (k : Nat) (T U : Ty) :
    Equivalent S M (Γ.letIn (.conj C (.le k T U))) (.conj (Γ.letIn C) (.le k T U)) := by
  constructor
  · intro ρ ι hρ hι hh
    obtain ⟨hr,hc,hle⟩ := (letInReady S M ρ Γ ι _).mp hh
    exact ⟨(letInReady S M ρ Γ ι C).mpr ⟨hr,hc⟩,
      (leHolds S M ρ ι k T U).mpr ((leHolds S M ρ _ k T U).mp hle)⟩
  · intro ρ ι hρ hι hh
    obtain ⟨hr,hc⟩ := (letInReady S M ρ Γ ι C).mp hh.1
    exact (letInReady S M ρ Γ ι _).mpr
      ⟨hr,hc,(leHolds S M ρ _ k T U).mpr ((leHolds S M ρ ι k T U).mp hh.2)⟩

theorem closedGeneratedSchemeWF (S : Signature) (hS : S.Valid) (Γ : Env) (t : Expr) (X : TVar)
    (hΓ : Γ.WF S) (ht : t.LCAt 0) (hX : X.1 = 0) : (closedGeneratedScheme Γ t X).WF S [] 0 := by
  have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hS.1)
  exact generalizeWF S [X] (infer Γ t (.free X)) (.free X) 0 (by simp [hX,hS.1])
    (letInWF S Γ _ hΓ (generationWF S hS 0 t _ ht hXk)) hXk

theorem closedGeneratedSchemeFv (Γ : Env) (t : Expr) (X : TVar) :
    (closedGeneratedScheme Γ t X).fv ⊆ Γ.fv := by
  unfold closedGeneratedScheme
  rw [generalizeFv]
  intro Y hy
  obtain ⟨hy,hn⟩ := Finset.mem_sdiff.mp hy
  have hYX : Y ≠ X := by simpa using hn
  rcases Finset.mem_union.mp hy with hy | hy
  · change Y ∈ (Γ.letIn (generate t (.free X))).fv at hy
    rw [letInFv] at hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hy
    · have hyX := (generationFreeVariables t (.free X)).1 hy
      exact False.elim (hYX (by simpa [Ty.fv] using hyX))
  · exact False.elim (hYX (by simpa [Ty.fv] using hy))

theorem generatedInstance (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.generatedInstance S M I := by
  intro hF Γ t X T hΓ hΓf ht hX hf hT
  have hxΓ : X ∉ Γ.fv := fun he => hf (Finset.mem_union_left _ he)
  have hxT : X ∉ T.fv := fun he => hf (Finset.mem_union_right _ he)
  have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
  let C := Constraint.conj (generate t (.free X)) (.le 0 (.free X) T)
  let D := Constraint.conj (infer Γ t (.free X)) (.le 0 (.free X) T)
  have hC : C.WF S [] 0 := ⟨generationWF S hF.1.1 0 t _ ht hXk,⟨hF.1.1.1,.cons hXk (.cons hT .nil)⟩⟩
  have hD : D.WF S [] 0 := ⟨letInWF S Γ _ hΓ hC.1,hC.2⟩
  have hs := closedGeneratedSchemeWF S hF.1.1 Γ t X hΓ ht hX
  have hfirst := generalizedInstanceExists hF.1 [X] (infer Γ t (.free X)) (.free X) T hs hT (by simp [hxT])
  have hprefix := prefixLeRight S M Γ (generate t (.free X)) 0 (.free X) T
  have hquant := constraintCongruence S M hF.1 (.exists_ [X] .hole)
    (Γ.letIn C) D (letInWF S Γ C hΓ hC) hD
    (existsNamesWF S [X] _ 0 (by simp [hX,hF.1.1.1]) (letInWF S Γ C hΓ hC))
    (existsNamesWF S [X] D 0 (by simp [hX,hF.1.1.1]) hD) hprefix.1
  have hquant' := constraintCongruence S M hF.1 (.exists_ [X] .hole)
    D (Γ.letIn C) hD (letInWF S Γ C hΓ hC)
    (existsNamesWF S [X] D 0 (by simp [hX,hF.1.1.1]) hD)
    (existsNamesWF S [X] _ 0 (by simp [hX,hF.1.1.1]) (letInWF S Γ C hΓ hC)) hprefix.2
  have hswap := prefixExists S M hF.1 Γ [X] C (by simp) (by simp [hxΓ])
    (letInWF S Γ _ hΓ (existsNamesWF S [X] C 0 (by simp [hX,hF.1.1.1]) hC))
    (existsNamesWF S [X] _ 0 (by simp [hX,hF.1.1.1]) (letInWF S Γ C hΓ hC))
  have hlast := lemma10_4_6 S M I hF t X T ht hX hT hxT
  constructor
  · intro ρ ι hρ hι hh
    exact prefixEntails hF.1 Γ hΓ _ _ hlast.1 ρ ι hρ hι
      (hswap.2 ρ ι hρ hι (hquant' ρ ι hρ hι (hfirst.1 ρ ι hρ hι hh)))
  · intro ρ ι hρ hι hh
    exact hfirst.2 ρ ι hρ hι (hquant ρ ι hρ hι
      (hswap.1 ρ ι hρ hι (prefixEntails hF.1 Γ hΓ _ _ hlast.2 ρ ι hρ hι hh)))

theorem generalizedLetComparison (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.generalizedLetComparison S M I := by
  intro hF C Γ t xs D T X hC hD hT hΓ hΓf ht hn hk hf hX hXF hgen
  have hxΓT : X ∉ Γ.fv ∪ T.fv := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact hXF (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ he)))
    · exact hXF (Finset.mem_union_right _ he)
  have hinst := generatedInstance S M I hF Γ t X T hΓ hΓf ht hX hxΓT hT
  have hs := closedGeneratedSchemeWF S hF.1.1 Γ t X hΓ ht hX
  intro ρ ι hρ hι hCρ v hv
  obtain ⟨hvk,vs,hvs,hDρ,hTv⟩ := (generalizeDenote S M ρ ι xs D T hD hT v).mp hv
  let ρ' := assignBlock xs vs ρ
  have hρ' := assignBlockValid S M ρ xs vs hρ hvs
  have hCρ' : C.Holds S M ρ' ι :=
    (holdsAssignBlock S M hF.1 ρ ι xs vs C hρ hι hvs hC (hf.mono_right Finset.subset_union_left)).mpr hCρ
  have hgi := hgen ρ' ι hρ' hι ⟨hCρ',hDρ⟩
  have hmember := (instanceConstraintHolds S M hF.1 ρ' ι _ T hρ' hs hT).mp (hinst.2 ρ' ι hρ' hι hgi)
  have hvalid := schemeDenotationValid S M hF.1 ρ' ι (closedGeneratedScheme Γ t X) (.var 0) hρ' hι hs (.var 0)
  have hmember' : v ∈ (closedGeneratedScheme Γ t X).denote S M ρ' ι := by
    simpa only [↓reduceIte] using hvalid.2 _ v hmember hvk hTv
  have heq := (semanticLocality S M hF.1 ρ' ρ ι ι hρ' hρ hι hι).2 (closedGeneratedScheme Γ t X) hs
    (fun Y hy => assignBlockOutside ρ xs vs Y (fun hm => Finset.disjoint_left.mp hf
      (List.mem_toFinset.mpr hm) (Finset.mem_union_right _ (closedGeneratedSchemeFv Γ t X hy))))
    (fun _ _ => rfl)
  simpa only [heq] using hmember'

end HMX.LN.Proofs
