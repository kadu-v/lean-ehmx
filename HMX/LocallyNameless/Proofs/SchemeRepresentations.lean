import HMX.LocallyNameless.Proofs.NamedSchemeAlignment

namespace HMX.LN.Proofs

def ConstraintRepresentation (S : Signature) (M : Model) (C : Constraint) (D : HMX.Constraint) : Prop :=
  D.WF S ∧ D.fv = C.fv ∧ D.fpi = C.fpi ∧
    ∀ (ρ : Assignment M) (ι : GroundEnv M), ρ.Valid S M →
      (D.Holds S M ρ ι ↔ C.Holds S M ρ ι)

/-- The qualification may change semantically, while the opened monotype and
quantifier block retain their structural correspondence. -/
def SchemeRepresentation (S : Signature) (M : Model) (s : Scheme) (r : HMX.Scheme) : Prop :=
  ∃ xs D T E U, xs.Nodup ∧ (∀ X ∈ xs, X.1 ∈ S.kinds) ∧
    D.WF S [] 0 ∧ T.HasKind S [] 0 ∧ ConstraintRepresentation S M D E ∧
    ofTy [] U = T ∧ s = Scheme.generalize xs D T ∧ r = .all xs.toFinset E U

theorem schemeRepresentationProperties (h : SchemeRepresentation S M s r) :
    s.WF S [] 0 ∧ r.WF S ∧ r.fv = s.fv ∧ r.fpi = s.fpi := by
  obtain ⟨xs,D,T,E,U,hn,hk,hD,hT,hE,ht,rfl,rfl⟩ := h
  refine ⟨generalizeWF S xs D T 0 hk hD hT,
    ⟨fun X hx => hk X (List.mem_toFinset.mp hx),hE.1,encodingTyKindReflection U [] (ht.symm ▸ hT)⟩,?_,?_⟩
  · rw [generalizeFv]
    change (E.fv ∪ U.fv) \ xs.toFinset = _
    rw [hE.2.1,← ht,encodingTyFv]
    simp
  · exact hE.2.2.1.trans (generalizeFpi xs D T).symm

theorem schemeRepresentationExists (s : Scheme) (hw : s.WF S [] 0) :
    ∃ r, SchemeRepresentation S M s r := by
  obtain ⟨xs,D,T,hn,hf,hk,hD,hT,he⟩ := schemeFreshOpening s hw ∅
  obtain ⟨E,hE⟩ := namedConstraintRepresentative D hD (M := M)
  exact ⟨.all xs.toFinset E (namedTy T),xs,D,T,E,namedTy T,hn,hk,hD,hT,hE,
    namedTyEncoding T (tyKindLC T S [] 0 hT),he.symm,rfl⟩

theorem encodingConstraintRepresentation (C : HMX.Constraint) (hw : C.WF S) :
    ConstraintRepresentation S M (ofConstraint [] [] C) C := by
  refine ⟨hw,(encodingFreeVariables.2.1 C).1.symm,(encodingFreeVariables.2.1 C).2.symm,?_⟩
  intro ρ ι hρ
  exact (encodingConstraintSem C hw [] [] M ρ ρ ι ι _ _ hρ (fun _ => rfl) (fun _ => rfl)).symm

theorem encodingSchemeRepresentation (s : HMX.Scheme) (hw : s.WF S) :
    SchemeRepresentation S M (ofScheme [] [] s) s := by
  cases s with
  | all A D T =>
    refine ⟨boundNames A,ofConstraint [] [] D,ofTy [] T,D,T,boundNamesNodup A,
      fun X hx => hw.1 X ((boundNamesMem A X).mp hx),encodingConstraintWF D hw.2.1 [] [],
      encodingTyKind hw.2.2 [],encodingConstraintRepresentation D hw.2.1,rfl,encodingGeneralize A D T [],?_⟩
    rw [boundNamesFinset]

theorem equalSchemeRepresentations (_hM : M.Requirements S)
    (h : SchemeRepresentation S M s r) (g : SchemeRepresentation S M t u)
    (he : s = t) (hf : s.fpi = ∅) : HMX.Proofs.SchemeConversion S M r u := by
  obtain ⟨xs,D,T,E,V,hn,hk,hD,hT,hE,hV,rfl,rfl⟩ := h
  obtain ⟨ys,D',T',E',V',hn',hk',hD',hT',hE',hV',rfl,rfl⟩ := g
  obtain ⟨p,q,hpk,hqk,hpq,hDD,hTT,hpf,hqf⟩ := alignGeneralizations xs ys D D' T T' hn hn' he
  have hEw : (HMX.Scheme.all xs.toFinset E V).WF S :=
    ⟨fun X hx => hk X (List.mem_toFinset.mp hx),hE.1,encodingTyKindReflection V [] (hV.symm ▸ hT)⟩
  have hE'w : (HMX.Scheme.all ys.toFinset E' V').WF S :=
    ⟨fun X hx => hk' X (List.mem_toFinset.mp hx),hE'.1,encodingTyKindReflection V' [] (hV'.symm ▸ hT')⟩
  have hv : (HMX.Scheme.all xs.toFinset E V).fv = (Scheme.generalize xs D T).fv :=
    (schemeRepresentationProperties ⟨xs,D,T,E,V,hn,hk,hD,hT,hE,hV,rfl,rfl⟩).2.2.1
  have hv' : (HMX.Scheme.all ys.toFinset E' V').fv = (Scheme.generalize ys D' T').fv :=
    (schemeRepresentationProperties ⟨ys,D',T',E',V',hn',hk',hD',hT',hE',hV',rfl,rfl⟩).2.2.1
  have hEf : E.fpi = ∅ := hE.2.2.1.trans ((generalizeFpi xs D T).symm.trans hf)
  have hE'f : E'.fpi = ∅ := hE'.2.2.1.trans ((generalizeFpi ys D' T').symm.trans (he ▸ hf))
  have ha := HMX.Proofs.namedSchemeRenameAlpha p hpk (.all xs.toFinset E V)
    (fun X hx => hpf X (hv ▸ hx))
  have hb := HMX.Proofs.namedSchemeRenameAlpha q hqk (.all ys.toFinset E' V')
    (fun X hx => hqf X (hv' ▸ hx))
  have hAw := HMX.Proofs.namedSchemeRenameWF p hpk _ hEw
  have hBw := HMX.Proofs.namedSchemeRenameWF q hqk _ hE'w
  have hAf := (HMX.Proofs.namedSchemeRenameFpi p (.all xs.toFinset E V)).trans hEf
  have hBf := (HMX.Proofs.namedSchemeRenameFpi q (.all ys.toFinset E' V')).trans hE'f
  apply HMX.Proofs.SchemeConversion.trans (.alpha hEw hAw hEf hAf ha)
  apply HMX.Proofs.SchemeConversion.trans ?_ (.symm (.alpha hE'w hBw hE'f hBf hb))
  have hvars : xs.toFinset.image p = ys.toFinset.image q := by
    ext X
    have hh := congrArg (fun zs : List TVar => X ∈ zs) hpq
    simpa only [Finset.mem_image,List.mem_toFinset,List.mem_map] using (Iff.of_eq hh)
  have htype : HMX.Proofs.namedTyRename p V = HMX.Proofs.namedTyRename q V' := by
    apply encodingTyInjective
    rw [encodingNamedTyRename,encodingNamedTyRename,hV,hV',hTT]
  have hfv : (HMX.Proofs.namedConstraintRename p E).fv = (HMX.Proofs.namedConstraintRename q E').fv := by
    rw [HMX.Proofs.namedConstraintRenameFv,HMX.Proofs.namedConstraintRenameFv,hE.2.1,hE'.2.1,
      ← constraintRenameFv p D 0,← constraintRenameFv q D' 0]
    exact congrArg Constraint.fv hDD
  have hsem : HMX.Equivalent S M (HMX.Proofs.namedConstraintRename p E) (HMX.Proofs.namedConstraintRename q E') := by
    have eq : ∀ ρ ι, ρ.Valid S M →
        ((HMX.Proofs.namedConstraintRename p E).Holds S M ρ ι ↔
          (HMX.Proofs.namedConstraintRename q E').Holds S M ρ ι) := by
      intro ρ ι hρ
      apply (HMX.Proofs.namedConstraintRenameSem p hpk E ρ ι).trans
      apply (hE.2.2.2 _ ι (HMX.Proofs.renamedAssignmentValid p hpk hρ)).trans
      apply (renameHolds p D hD ρ ι).symm.trans
      rw [hDD]
      apply (renameHolds q D' hD' ρ ι).trans
      apply (hE'.2.2.2 _ ι (HMX.Proofs.renamedAssignmentValid q hqk hρ)).symm.trans
      exact (HMX.Proofs.namedConstraintRenameSem q hqk E' ρ ι).symm
    exact ⟨fun ρ ι hρ _ hh => (eq ρ ι hρ).mp hh,fun ρ ι hρ _ hh => (eq ρ ι hρ).mpr hh⟩
  simp only [HMX.Proofs.namedSchemeRename] at hAw hBw ⊢
  rw [hvars,htype] at hAw ⊢
  exact .qualification hBw.1 hAw.2.1 hBw.2.1 hBw.2.2 hAf hBf hfv hsem

end HMX.LN.Proofs
