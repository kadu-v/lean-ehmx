import HMX.LocallyNameless.Proofs.NamedRepresentativeSupport

namespace HMX.LN.Proofs

/- Representatives preserve free names and semantics. In particular, this does
not assert that an arbitrary LN constraint belongs to the image of ofConstraint. -/
mutual
theorem namedConstraintRepresentative (C : Constraint) (hw : C.WF S [] 0) :
    ∃ D : HMX.Constraint, D.WF S ∧ D.fv = C.fv ∧ D.fpi = C.fpi ∧
      ∀ (ρ : Assignment M) (ι : GroundEnv M), ρ.Valid S M →
        (D.Holds S M ρ ι ↔ C.Holds S M ρ ι) := by
  cases C with
  | truth => exact ⟨.truth,trivial,rfl,rfl,fun _ _ _ => Iff.rfl⟩
  | falsity => exact ⟨.falsity,trivial,rfl,rfl,fun _ _ _ => Iff.rfl⟩
  | atom q ts =>
    have ht : ∀ T ∈ ts, T.LCAt 0 := by
      intro T hT
      obtain ⟨k,hk⟩ := forall₂Left hw.2 T hT
      exact tyKindLC T S [] k hk
    refine ⟨.atom q (ts.map namedTy),⟨hw.1,List.forall₂_map_left_iff.mpr
      (hw.2.imp (fun _ _ h => namedTyKind h))⟩,?_,rfl,?_⟩
    · simp only [HMX.Constraint.fv,Constraint.fv,List.map_map,Function.comp_def]
      rw [List.map_congr_left (fun T hT => namedTyFv T (ht T hT))]
    · intro ρ ι hρ
      simp only [HMX.Constraint.Holds,Constraint.Holds,Constraint.holdsAt,List.map_map,Function.comp_def]
      rw [List.map_congr_left (fun T hT => namedTyEval T (ht T hT) ρ)]
      rfl
  | conj C D =>
    obtain ⟨C',hC,hCv,hCf,hCs⟩ := namedConstraintRepresentative C hw.1 (M := M)
    obtain ⟨D',hD,hDv,hDf,hDs⟩ := namedConstraintRepresentative D hw.2 (M := M)
    exact ⟨.conj C' D',⟨hC,hD⟩,congrArg₂ (· ∪ ·) hCv hDv,congrArg₂ (· ∪ ·) hCf hDf,
      fun ρ ι hρ => and_congr (hCs ρ ι hρ) (hDs ρ ι hρ)⟩
  | exists_ ks C =>
    obtain ⟨xs,D,hn,hk,hD,he,hsize⟩ := freshExistsOpening ks C hw
    have hlt : constraintNodes D < constraintNodes (.exists_ ks C) := by simp [constraintNodes,hsize]
    obtain ⟨D',hD',hDv,hDf,hDs⟩ := namedConstraintRepresentative D hD (M := M)
    refine ⟨.exists_ xs.toFinset D',⟨fun X hx => hk X (List.mem_toFinset.mp hx),hD'⟩,?_,?_,?_⟩
    · rw [← he]
      simpa only [HMX.Constraint.fv,Constraint.existsNames,Constraint.fv,Constraint.closeTypes,
        constraintCloseFv] using congrArg (fun F => F \ xs.toFinset) hDv
    · rw [← he]
      exact hDf.trans (existsNamesFpi xs D).symm
    · intro ρ ι hρ
      rw [← he]
      apply (namedExistsList xs hk D' ρ ι hρ).trans
      apply Iff.trans ?_ (existsNamesHolds S M ρ ι xs D hD).symm
      exact exists_congr (fun vs => and_congr_right (fun hvs => hDs _ ι (assignBlockValid S M ρ xs vs hρ hvs)))
  | def_ b s C =>
    obtain ⟨s',hs,hsv,hsf,hss⟩ := namedSchemeRepresentative s hw.1 (M := M)
    obtain ⟨z,hz⟩ := Finset.exists_notMem (C.fpi.image idNumber)
    have hz' : Id.var z ∉ C.fpi := fun h => hz (Finset.mem_image.mpr ⟨.var z,h,rfl⟩)
    let D := C.openId (.var z)
    have hclose : D.closeId (.var z) = C := constraintCloseOpenId C (.var z) 0 hz'
    have hD : D.WF S [] 0 := closeIdWFReflect S (.var z) D [] 0 0 le_rfl (by change (D.closeId (.var z)).WF S [] 1; rw [hclose]; exact hw.2)
    have hlt : constraintNodes D < constraintNodes (.def_ b s C) := by
      simp [D,Constraint.openId,constraintNodesMapIds,constraintNodes]; omega
    obtain ⟨D',hD',hDv,hDf,hDs⟩ := namedConstraintRepresentative D hD (M := M)
    refine ⟨.def_ (.var z) s' D',⟨hs,hD'⟩,?_,?_,?_⟩
    · exact congrArg₂ (· ∪ ·) hsv (hDv.trans (constraintMapIdsFv _ C 0))
    · change s'.fpi ∪ D'.fpi.erase (.var z) = s.fpi ∪ C.fpi
      rw [hsf,hDf,← hclose]
      exact congrArg (s.fpi ∪ ·) (constraintCloseIdFpi (.var z) D 0).symm
    · intro ρ ι hρ
      simp only [HMX.Constraint.Holds,hss ρ ι hρ]
      apply (hDs ρ (updateEnv ι (.var z) (s.denote S M ρ ι)) hρ).trans
      have hc := constraintEvalCloseId S M ρ ι (.var z) (s.denote S M ρ ι) D []
        (fun _ => ρ (0,0)) (fun _ => ∅)
      change (D.closeId (.var z)).holdsAt S M ρ ι _ _ ↔ _ at hc
      rw [hclose] at hc
      simpa only [pushNil,Constraint.Holds,Constraint.holdsAt,Scheme.denote] using hc.symm
  | inst x T =>
    cases x with
    | free x =>
      have ht := tyKindLC T S [] 0 hw.1
      exact ⟨.inst x (namedTy T),namedTyKind hw.1,namedTyFv T ht,rfl,
        fun ρ ι _ => by simp only [HMX.Constraint.Holds,Constraint.Holds,Constraint.holdsAt,namedTyEval T ht]; rfl⟩
    | bound i => exact (Nat.not_lt_zero i hw.2).elim
termination_by constraintNodes C
decreasing_by all_goals simp_all only [constraintNodes] <;> omega

theorem namedSchemeRepresentative (s : Scheme) (hw : s.WF S [] 0) :
    ∃ r : HMX.Scheme, r.WF S ∧ r.fv = s.fv ∧ r.fpi = s.fpi ∧
      ∀ (ρ : Assignment M) (ι : GroundEnv M), ρ.Valid S M →
        r.denote S M ρ ι = s.denote S M ρ ι := by
  obtain ⟨xs,D,T,hn,_,hk,hD,hT,he⟩ := schemeFreshOpening s hw ∅
  have hlt : constraintNodes D < schemeNodes s := by
    rw [← he]
    simp [Scheme.generalize,schemeNodes,Constraint.closeTypes,constraintNodesMapTypes]
  obtain ⟨D',hD',hDv,hDf,hDs⟩ := namedConstraintRepresentative D hD (M := M)
  have ht := tyKindLC T S [] 0 hT
  refine ⟨.all xs.toFinset D' (namedTy T),⟨fun X hx => hk X (List.mem_toFinset.mp hx),hD',namedTyKind hT⟩,?_,?_,?_⟩
  · rw [← he]
    simp only [HMX.Scheme.fv,Scheme.generalize,Scheme.fv,Constraint.closeTypes,
      constraintCloseFv,tyCloseFv,hDv,namedTyFv T ht,Finset.union_sdiff_distrib]
  · rw [← he]; exact hDf.trans (generalizeFpi xs D T).symm
  · intro ρ ι hρ
    rw [← he]
    ext v
    apply (namedGeneralizeList xs hk D' (namedTy T) ρ ι hρ v).trans
    apply Iff.trans ?_ (generalizeDenote S M ρ ι xs D T hD hT v).symm
    apply and_congr Iff.rfl
    apply exists_congr
    intro vs
    apply and_congr_right
    intro hvs
    exact and_congr (hDs _ ι (assignBlockValid S M ρ xs vs hρ hvs)) (by rw [namedTyEval T ht])
termination_by schemeNodes s
decreasing_by exact hlt
end

end HMX.LN.Proofs
