import HMX.LocallyNameless.Proofs.GenerationSemantics

namespace HMX.LN.Proofs

/-- The program stack is kept explicit so the induction also applies beneath
lambda and let binders. The expected types remain locally closed. -/
theorem generateCovariantAt (hF : Framework S M I) (t : Expr) (d : Nat) (T U : Ty)
    (ht : t.LCAt d) (hT : T.HasKind S [] 0) (hU : U.HasKind S [] 0)
    (ρ : Assignment M) (ι : GroundEnv M) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier)
    (hρ : ρ.Valid S M) (hι : ι.Valid M)
    (hγ : ∀ i, (∀ a ∈ γ i, M.kind a = 0) ∧
      (∀ a b, a ∈ γ i → M.kind b = 0 → M.below 0 a b → b ∈ γ i))
    (hTU : M.below 0 (T.eval M ρ) (U.eval M ρ))
    (hg : (generate t T).holdsAt S M ρ ι β γ) : (generate t U).holdsAt S M ρ ι β γ := by
  induction t generalizing d T U ρ β γ with
  | ident x =>
      have hTc := tyKindLC T S [] 0 hT
      have hUc := tyKindLC U S [] 0 hU
      have hUk := evalKind S M hF.1 ρ hρ U 0 hU
      cases x with
      | free x =>
          simp only [generate,Constraint.holdsAt,tyEvalAtClosed M ρ β T hTc] at hg
          simp only [generate,Constraint.holdsAt,tyEvalAtClosed M ρ β U hUc]
          exact (hι x).2 _ _ hg hUk hTU
      | bound i =>
          simp only [generate,Constraint.holdsAt,tyEvalAtClosed M ρ β T hTc] at hg
          simp only [generate,Constraint.holdsAt,tyEvalAtClosed M ρ β U hUc]
          exact (hγ i).2 _ _ hg hUk hTU
  | lam t ih =>
      obtain ⟨X,hX,hXF⟩ := freshSameKind 0 (T.fv ∪ U.fv)
      obtain ⟨Y,hY,hYF⟩ := freshSameKind 0 (insert X (T.fv ∪ U.fv))
      have hxT : X ∉ T.fv := fun h => hXF (Finset.mem_union_left _ h)
      have hxU : X ∉ U.fv := fun h => hXF (Finset.mem_union_right _ h)
      have hyT : Y ∉ T.fv := fun h => hYF (by simp [h])
      have hyU : Y ∉ U.fv := fun h => hYF (by simp [h])
      have hxy : X ≠ Y := fun he => hYF (by simp [he])
      have hTc := tyKindLC T S [] 0 hT
      have hUc := tyKindLC U S [] 0 hU
      rw [generateLamFresh t T X Y hTc hX hY hxy hxT hyT] at hg
      rw [generateLamFresh t U X Y hUc hX hY hxy hxU hyU]
      have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
      have hYk : (Ty.free Y).HasKind S [] 0 := by rw [← hY]; exact .free (by rw [hY]; exact hF.1.1.1)
      have hA := arrowKind S hF.1.1 _ _ [] hXk hYk
      have hAw := tyKindLC _ S [] 0 hA
      obtain ⟨vs,hvs,hb,ha⟩ := (existsNamesHoldsAt S M ρ ι β γ [X,Y] _).mp hg
      have hρ' := assignBlockValid S M ρ [X,Y] vs hρ hvs
      have hfT : Disjoint [X,Y].toFinset T.fv := by simp [hxT,hyT]
      have hfU : Disjoint [X,Y].toFinset U.fv := by simp [hxU,hyU]
      have hTU' : M.below 0 (T.eval M (assignBlock [X,Y] vs ρ)) (U.eval M (assignBlock [X,Y] vs ρ)) := by
        rw [tyEvalAssignBlock M ρ [X,Y] vs T hTc hfT,tyEvalAssignBlock M ρ [X,Y] vs U hUc hfU]
        exact hTU
      have ha' := (leHoldsAt S M _ ι β γ 0 _ T hAw hTc).mp ha
      apply (existsNamesHoldsAt S M ρ ι β γ [X,Y] _).mpr
      refine ⟨vs,hvs,hb,?_⟩
      apply (leHoldsAt S M _ ι β γ 0 _ U hAw hUc).mpr
      have hUk := evalKind S M hF.1 _ hρ' U 0 hU
      exact ⟨ha'.1,hUk,hF.1.2.2.2.2.1 0 hF.1.1.1 _ _ _ ha'.1 ha'.2.1 hUk ha'.2.2 hTU'⟩
  | app t u iht ihu =>
      obtain ⟨X,hX,hXF⟩ := freshSameKind 0 (T.fv ∪ U.fv)
      have hxT : X ∉ T.fv := fun h => hXF (Finset.mem_union_left _ h)
      have hxU : X ∉ U.fv := fun h => hXF (Finset.mem_union_right _ h)
      have hTc := tyKindLC T S [] 0 hT
      have hUc := tyKindLC U S [] 0 hU
      rw [generateAppFresh t u T X hTc hX hxT] at hg
      rw [generateAppFresh t u U X hUc hX hxU]
      have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
      have hAT := arrowKind S hF.1.1 _ _ [] hXk hT
      have hAU := arrowKind S hF.1.1 _ _ [] hXk hU
      obtain ⟨vs,hvs,hgt',hgu'⟩ := (existsNamesHoldsAt S M ρ ι β γ [X] _).mp hg
      have hρ' := assignBlockValid S M ρ [X] vs hρ hvs
      have hTU' : M.below 0 (T.eval M (assignBlock [X] vs ρ)) (U.eval M (assignBlock [X] vs ρ)) := by
        rw [tyEvalAssignBlock M ρ [X] vs T hTc (by simp [hxT]),tyEvalAssignBlock M ρ [X] vs U hUc (by simp [hxU])]
        exact hTU
      have hle : (Constraint.le 0 (.arrow (.free X) T) (.arrow (.free X) U)).Holds S M (assignBlock [X] vs ρ) ι := by
        apply (hF.2.1 (.free X) T (.free X) U hXk hT hXk hU).2 _ ι hρ' hι
        exact ⟨subRefl S M hF.1 (.free X) 0 hXk _ ι hρ' hι trivial,
          (leHolds S M _ ι 0 T U).mpr ⟨evalKind S M hF.1 _ hρ' T 0 hT,evalKind S M hF.1 _ hρ' U 0 hU,hTU'⟩⟩
      apply (existsNamesHoldsAt S M ρ ι β γ [X] _).mpr
      exact ⟨vs,hvs,iht d _ _ ht.1 hAT hAU _ β γ hρ' hγ
        ((leHolds S M _ ι 0 _ _).mp hle).2.2 hgt',hgu'⟩
  | letE t u iht ihu =>
      obtain ⟨X,hX,hXF⟩ := freshSameKind 0 (T.fv ∪ U.fv)
      have hxT : X ∉ T.fv := fun h => hXF (Finset.mem_union_left _ h)
      have hxU : X ∉ U.fv := fun h => hXF (Finset.mem_union_right _ h)
      rw [generateLetFresh t u T X hX hxT] at hg
      rw [generateLetFresh t u U X hX hxU]
      have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
      have hs := generalizeWF S [X] (generate t (.free X)) (.free X) d
        (by simp [hX,hF.1.1.1]) (generationWF S hF.1.1 d t _ ht.1 hXk) hXk
      exact ⟨hg.1,ihu (d+1) T U ht.2 hT hU ρ β _ hρ
        (pushGroundValid _ γ (schemeAtValid hF.1 ρ ι β γ _ d hρ hs) hγ) hTU hg.2⟩

theorem lemma10_4_5 (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.lemma10_4_5 S M I := by
  intro hF t T U ht hT hU ρ ι hρ hι hh
  exact generateCovariantAt hF t 0 T U ht hT hU ρ ι _ _ hρ hι
    (by intro i; exact ⟨by simp,by simp⟩) ((leHolds S M ρ ι 0 T U).mp hh.2).2.2 hh.1

theorem lemma10_4_6 (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.lemma10_4_6 S M I := by
  intro hF t X T ht hX hT hf
  have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
  have hgX := generationWF S hF.1.1 0 t (.free X) ht hXk
  have hgT := generationWF S hF.1.1 0 t T ht hT
  have hle : (Constraint.le 0 (.free X) T).WF S [] 0 := ⟨hF.1.1.1,.cons hXk (.cons hT .nil)⟩
  have hTf : Disjoint [X].toFinset T.fv := by simp [hf]
  have hgf : Disjoint [X].toFinset (generate t T).fv :=
    hTf.mono_right (generationFreeVariables t T).1
  have hTc := tyKindLC T S [] 0 hT
  constructor
  · intro ρ ι hρ hι hh
    obtain ⟨vs,hvs,hg,hl⟩ := (existsNamesHolds S M ρ ι [X] (.conj (generate t (.free X)) (.le 0 (.free X) T)) ⟨hgX,hle⟩).mp hh
    have hρ' := assignBlockValid S M ρ [X] vs hρ hvs
    have hresult := lemma10_4_5 S M I hF t (.free X) T ht hXk hT _ ι hρ' hι ⟨hg,hl⟩
    exact (holdsAssignBlock S M hF.1 ρ ι [X] vs (generate t T) hρ hι hvs hgT hgf).mp hresult
  · intro ρ ι hρ hι hh
    let v := T.eval M ρ
    let ρ' := assignBlock [X] [v] ρ
    have hv : M.kind v = 0 := evalKind S M hF.1 ρ hρ T 0 hT
    have hvs : List.Forall₂ (fun w Y => M.kind w = Y.1) [v] [X] := .cons (by simpa [hX] using hv) .nil
    have hρ' := assignBlockValid S M ρ [X] [v] hρ hvs
    have heT : T.eval M ρ' = v := tyEvalAssignBlock M ρ [X] [v] T hTc hTf
    have heX : ρ' X = v := by simp [ρ',assignBlock]
    have hgenT : (generate t T).Holds S M ρ' ι :=
      (holdsAssignBlock S M hF.1 ρ ι [X] [v] (generate t T) hρ hι hvs hgT hgf).mpr hh
    apply (existsNamesHolds S M ρ ι [X] (.conj (generate t (.free X)) (.le 0 (.free X) T)) ⟨hgX,hle⟩).mpr
    refine ⟨[v],hvs,?_,?_⟩
    · exact (generateExpectedRename t T X hTc ρ' ι _ _ (heT.trans heX.symm)).mp hgenT
    · apply (leHolds S M ρ' ι 0 (.free X) T).mpr
      have hxf : (Ty.free X).eval M ρ' = v := by simpa [Ty.eval,Ty.evalAt] using heX
      rw [heT,hxf]
      exact ⟨hv,hv,hF.1.2.2.2.1 0 hF.1.1.1 v hv⟩

theorem lemma10_4_7 (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.lemma10_4_7 S M I := by
  intro hF t z T U ht hz hT hU
  let b := Expr.openAt 0 (.ident (.free (.var z))) t
  have hb : b.LCAt 0 := exprOpenNameLC t z 0 ht
  have hTc := tyKindLC T S [] 0 hT
  have hUc := tyKindLC U S [] 0 hU
  obtain ⟨X,hX,hXF⟩ := freshSameKind 0 (T.fv ∪ U.fv)
  obtain ⟨Y,hY,hYF⟩ := freshSameKind 0 (insert X (T.fv ∪ U.fv))
  have hxT : X ∉ T.fv := fun h => hXF (Finset.mem_union_left _ h)
  have hxU : X ∉ U.fv := fun h => hXF (Finset.mem_union_right _ h)
  have hyT : Y ∉ T.fv := fun h => hYF (by simp [h])
  have hyU : Y ∉ U.fv := fun h => hYF (by simp [h])
  have hxy : X ≠ Y := fun he => hYF (by simp [he])
  have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
  have hYk : (Ty.free Y).HasKind S [] 0 := by rw [← hY]; exact .free (by rw [hY]; exact hF.1.1.1)
  have hAT := arrowKind S hF.1.1 T U [] hT hU
  have hAX := arrowKind S hF.1.1 (.free X) (.free Y) [] hXk hYk
  have hxA : X ∉ (Ty.arrow T U).fv := by simpa [Ty.arrow,Ty.fv] using hXF
  have hyA : Y ∉ (Ty.arrow T U).fv := by
    simp only [Ty.arrow,Ty.fv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,Finset.union_empty]
    exact fun he => hYF (Finset.mem_insert_of_mem he)
  rw [generateLamFresh t (.arrow T U) X Y (tyKindLC _ S [] 0 hAT) hX hY hxy hxA hyA,
    generateLetName t z (.free Y) (.free X) hz]
  let D := generate b (.free Y)
  let B := generate b U
  let L := Constraint.conj (D.letName (.var z) (.mono (.free X))) (.le 0 (.arrow (.free X) (.free Y)) (.arrow T U))
  let R := B.letName (.var z) (.mono T)
  change Equivalent S M (L.existsNames [X,Y]) R
  have hD : D.WF S [] 0 := generationWF S hF.1.1 0 b _ hb hYk
  have hB : B.WF S [] 0 := generationWF S hF.1.1 0 b U hb hU
  have hLX := letNameWF S (.var z) (.mono (.free X)) D (monoWF S _ hXk) hD
  have hL : L.WF S [] 0 := ⟨hLX,⟨hF.1.1.1,.cons hAX (.cons hAT .nil)⟩⟩
  have hR : R.WF S [] 0 := letNameWF S (.var z) (.mono T) B (monoWF S T hT) hB
  have hBfv : B.fv ⊆ U.fv := (generationFreeVariables b U).1
  have hRfv : R.fv ⊆ T.fv ∪ U.fv := by
    rw [letNameFv]
    simpa [Scheme.mono,Scheme.fv,Constraint.fv] using Finset.union_subset_union (Finset.Subset.rfl (s := T.fv)) hBfv
  have hfT : Disjoint [X,Y].toFinset T.fv := by simp [hxT,hyT]
  have hfU : Disjoint [X,Y].toFinset U.fv := by simp [hxU,hyU]
  have hfR : Disjoint [X,Y].toFinset R.fv :=
    (Finset.disjoint_union_right.mpr ⟨hfT,hfU⟩).mono_right hRfv
  have hxB : X ∉ T.fv ∪ B.fv := by
    intro he
    rcases Finset.mem_union.mp he with he | he
    · exact hxT he
    · exact hxU (hBfv he)
  have hLB := letNameWF S (.var z) (.mono (.free X)) B (monoWF S _ hXk) hB
  have hTX : (Constraint.le 0 T (.free X)).WF S [] 0 := ⟨hF.1.1.1,.cons hT (.cons hXk .nil)⟩
  have hSub := letSub S M hF.1 X (.var z) T B hX hxB
    (existsNamesWF S [X] _ 0 (by simp [hX,hF.1.1.1]) ⟨hTX,hLB⟩) hR
  constructor
  · intro ρ ι hρ hι hh
    obtain ⟨vs,hvs,hbody,harr⟩ := (existsNamesHolds S M ρ ι [X,Y] L hL).mp hh
    let ρ' := assignBlock [X,Y] vs ρ
    have hρ' := assignBlockValid S M ρ [X,Y] vs hρ hvs
    have hparts := (hF.2.1 (.free X) (.free Y) T U hXk hYk hT hU).1 ρ' ι hρ' hι harr
    have hbody' := (letNameHolds S M ρ' ι (.var z) (.mono (.free X)) D).mp hbody
    let ι' := updateEnv ι (.var z) ((Scheme.mono (.free X)).denote S M ρ' ι)
    have hι' : ι'.Valid M := schemeDenotationValid S M hF.1 ρ' ι _ (.var z) hρ' hι (monoWF S _ hXk)
    have hleY : (Constraint.le 0 (.free Y) U).Holds S M ρ' ι' :=
      (leHolds S M ρ' ι' 0 (.free Y) U).mpr ((leHolds S M ρ' ι 0 (.free Y) U).mp hparts.2)
    have hEqw : (Constraint.conj D (.le 0 (.free Y) U)).WF S [] 0 :=
      ⟨hD,⟨hF.1.1.1,.cons hYk (.cons hU .nil)⟩⟩
    have heY := existsNamesIntro [Y] (.conj D (.le 0 (.free Y) U)) (by simp [hY,hF.1.1.1]) hEqw
      ρ' ι' hρ' hι' ⟨hbody'.2,hleY⟩
    have hB' : B.Holds S M ρ' ι' := (lemma10_4_6 S M I hF b Y U hb hY hU hyU).1 ρ' ι' hρ' hι' heY
    have hBX : (B.letName (.var z) (.mono (.free X))).Holds S M ρ' ι :=
      (letNameHolds S M ρ' ι (.var z) (.mono (.free X)) B).mpr ⟨hbody'.1,hB'⟩
    have heX := existsNamesIntro [X] (.conj (.le 0 T (.free X)) (B.letName (.var z) (.mono (.free X))))
      (by simp [hX,hF.1.1.1]) ⟨hTX,hLB⟩ ρ' ι hρ' hι ⟨hparts.1,hBX⟩
    exact (holdsAssignBlock S M hF.1 ρ ι [X,Y] vs R hρ hι hvs hR hfR).mp (hSub.1 ρ' ι hρ' hι heX)
  · intro ρ ι hρ hι hh
    let vs := [T.eval M ρ,U.eval M ρ]
    let ρ' := assignBlock [X,Y] vs ρ
    have hvT := evalKind S M hF.1 ρ hρ T 0 hT
    have hvU := evalKind S M hF.1 ρ hρ U 0 hU
    have hvs : List.Forall₂ (fun v Z => M.kind v = Z.1) vs [X,Y] :=
      .cons (by simpa [hX] using hvT) (.cons (by simpa [hY] using hvU) .nil)
    have hρ' := assignBlockValid S M ρ [X,Y] vs hρ hvs
    have heT := tyEvalAssignBlock M ρ [X,Y] vs T hTc hfT
    have heU := tyEvalAssignBlock M ρ [X,Y] vs U hUc hfU
    have heX : (Ty.free X).eval M ρ' = T.eval M ρ' := by
      rw [heT]
      simp [ρ',vs,Ty.eval,Ty.evalAt,assignBlock]
    have heY : (Ty.free Y).eval M ρ' = U.eval M ρ' := by
      rw [heU]
      simp [ρ',vs,Ty.eval,Ty.evalAt,assignBlock,hxy,Ne.symm hxy]
    have hR' : R.Holds S M ρ' ι := (holdsAssignBlock S M hF.1 ρ ι [X,Y] vs R hρ hι hvs hR hfR).mpr hh
    have hsEq : (Scheme.mono T).denote S M ρ' ι = (Scheme.mono (.free X)).denote S M ρ' ι := by
      ext v
      rw [monoDenote,monoDenote,heX]
    have hBX := (letNameDenoteEq S M hF.1 ρ' ι (.var z) (.mono T) (.mono (.free X)) B hρ'
      (monoWF S T hT) (monoWF S _ hXk) hsEq).mp hR'
    have hBX' := (letNameHolds S M ρ' ι (.var z) (.mono (.free X)) B).mp hBX
    apply (existsNamesHolds S M ρ ι [X,Y] L hL).mpr
    refine ⟨vs,hvs,?_,?_⟩
    · apply (letNameHolds S M ρ' ι (.var z) (.mono (.free X)) D).mpr
      refine ⟨hBX'.1,?_⟩
      exact (generateExpectedRename b U Y hUc ρ' _ _ _ (by
        simpa only [Ty.eval,Ty.evalAt] using heY.symm)).mp hBX'.2
    · apply (leHolds S M ρ' ι 0 _ _).mpr
      have heA : (Ty.arrow (.free X) (.free Y)).eval M ρ' = (Ty.arrow T U).eval M ρ' := by
        rw [arrowEval,arrowEval,heX,heY]
      rw [heA]
      have hkA := evalKind S M hF.1 ρ' hρ' _ 0 hAT
      exact ⟨hkA,hkA,hF.1.2.2.2.1 0 hF.1.1.1 _ hkA⟩

end HMX.LN.Proofs
