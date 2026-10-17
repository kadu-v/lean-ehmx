import HMX.LocallyNameless.Proofs.BlockNames

namespace HMX.LN.Proofs

theorem constraintBinderEqFpi (h : Constraint.BinderEq C D) : C.fpi = D.fpi := by
  apply Constraint.BinderEq.rec
    (motive_1 := fun C D _ => C.fpi = D.fpi)
    (motive_2 := fun s r _ => s.fpi = r.fpi)
    rfl (fun _ ih => ih.symm) (fun _ _ ih ij => ih.trans ij)
    (fun _ _ ih ij => congrArg₂ (· ∪ ·) ih ij)
    (by intro ks ls p D C hp h ih; exact (constraintMapTypesFpi _ C 0).symm.trans ih)
    (fun _ _ ih ij => congrArg₂ (· ∪ ·) ih ij)
    rfl (fun _ ih => ih.symm) (fun _ _ ih ij => ih.trans ij)
    (by intro ks ls p D U C T hp hc ht ih; exact (constraintMapTypesFpi _ C 0).symm.trans ih) h

theorem schemeBinderEqFpi (h : Scheme.BinderEq s r) : s.fpi = r.fpi := by
  apply Scheme.BinderEq.rec
    (motive_1 := fun _ _ _ => True) (motive_2 := fun s r _ => s.fpi = r.fpi)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    rfl (fun _ ih => ih.symm) (fun _ _ ih ij => ih.trans ij)
    (by intro ks ls p D U C T hp hc ht _;
        exact (constraintMapTypesFpi _ C 0).symm.trans (constraintBinderEqFpi hc)) h

theorem schemeOpeningWithNames (ks : List Nat) (C : Constraint) (T : Ty)
    (hw : (Scheme.all ks C T).WF S [] 0) (xs : List TVar) (hxs : xs.map Prod.fst = ks)
    (hn : xs.Nodup) (hf : Disjoint xs.toFinset (C.fv ∪ T.fv)) :
    (∀ X ∈ xs, X.1 ∈ S.kinds) ∧ (C.openTypes (xs.map Ty.free)).WF S [] 0 ∧
      (T.openAt 0 (xs.map Ty.free)).HasKind S [] 0 ∧
      Scheme.generalize xs (C.openTypes (xs.map Ty.free)) (T.openAt 0 (xs.map Ty.free)) = .all ks C T := by
  have hk : ∀ X ∈ xs, X.1 ∈ S.kinds := fun X hx => hw.1 _ (hxs ▸ List.mem_map.mpr ⟨X,hx,rfl⟩)
  have hu : List.Forall₂ (Ty.HasKind S []) (xs.map Ty.free) ks := by
    rw [← hxs]
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact List.forall₂_same.mpr (fun X hx => .free (hk X hx))
  refine ⟨hk,typeOpeningWF S ks _ C (by simpa using hw.2.1) hu,
    tyOpenKind S T ks [] _ hu 0 (by simpa using hw.2.2),?_⟩
  simp only [Scheme.generalize,Constraint.closeTypes,Constraint.openTypes,hxs]
  rw [constraintCloseOpen xs C 0 hn (hf.mono_right Finset.subset_union_left),
    tyCloseOpen T 0 xs hn (hf.mono_right Finset.subset_union_right)]

theorem permutedSchemeRepresentations (hM : M.Requirements S)
    (hp : BlockPermutation ks ls p)
    (hc : (C.mapTypes (fun d T => T.renameAt d p) 0).BinderEq D) (ht : T.renameAt 0 p = U)
    (hr : SchemeRepresentation S M (.all ks C T) r) (hs : SchemeRepresentation S M (.all ls D U) s)
    (hf : (Scheme.all ks C T).fpi = ∅) : HMX.Proofs.SchemeConversion S M r s := by
  have hrw := (schemeRepresentationProperties hr).1
  have hsw := (schemeRepresentationProperties hs).1
  obtain ⟨xs,hxs,hxn,hxf⟩ := freshKinds ks ((C.fv ∪ T.fv) ∪ (D.fv ∪ U.fv))
  obtain ⟨ys,hyn,hys,hyset,hi⟩ := permuteBlockNames hp xs hxn hxs
  have hlen : xs.length = ks.length := by simpa using congrArg List.length hxs
  have hylen : ys.length = ls.length := by simpa using congrArg List.length hys
  have hxo := schemeOpeningWithNames ks C T hrw xs hxs hxn (hxf.mono_right Finset.subset_union_left)
  have hyo := schemeOpeningWithNames ls D U hsw ys hys hyn (by rw [hyset]; exact hxf.mono_right Finset.subset_union_right)
  let C' := C.openTypes (xs.map Ty.free)
  let D' := D.openTypes (ys.map Ty.free)
  let T' := T.openAt 0 (xs.map Ty.free)
  let U' := U.openAt 0 (ys.map Ty.free)
  have hcd : C'.BinderEq D' := by
    have hh := constraintBinderEqOpening hc (ys.map Ty.free) (by
      intro V hv; obtain ⟨X,_,rfl⟩ := List.mem_map.mp hv; simp [Ty.LCAt]) 0
    rw [constraintOpenPermutedBlock C hp xs ys hlen hylen hi 0] at hh
    exact hh
  have htu : T' = U' := by
    change T.openAt 0 (xs.map Ty.free) = U.openAt 0 (ys.map Ty.free)
    rw [← ht]
    exact (tyOpenPermutedBlock T hp xs ys hlen hylen hi 0).symm
  obtain ⟨E,hE⟩ := namedConstraintRepresentative C' hxo.2.1 (M := M)
  obtain ⟨F,hF⟩ := namedConstraintRepresentative D' hyo.2.1 (M := M)
  let r' : HMX.Scheme := .all xs.toFinset E (namedTy T')
  let s' : HMX.Scheme := .all ys.toFinset F (namedTy U')
  have hr' : SchemeRepresentation S M (.all ks C T) r' :=
    ⟨xs,C',T',E,namedTy T',hxn,hxo.1,hxo.2.1,hxo.2.2.1,hE,
      namedTyEncoding T' (tyKindLC T' S [] 0 hxo.2.2.1),hxo.2.2.2.symm,rfl⟩
  have hs' : SchemeRepresentation S M (.all ls D U) s' :=
    ⟨ys,D',U',F,namedTy U',hyn,hyo.1,hyo.2.1,hyo.2.2.1,hF,
      namedTyEncoding U' (tyKindLC U' S [] 0 hyo.2.2.1),hyo.2.2.2.symm,rfl⟩
  have hfs : (Scheme.all ls D U).fpi = ∅ := (schemeBinderEqFpi (.all hp hc ht)).symm.trans hf
  apply HMX.Proofs.SchemeConversion.trans (equalSchemeRepresentations hM hr hr' rfl hf)
  apply HMX.Proofs.SchemeConversion.trans ?_ (equalSchemeRepresentations hM hs' hs rfl hfs)
  have hEf : E.fpi = ∅ := hE.2.2.1.trans ((constraintMapTypesFpi _ C 0).trans hf)
  have hFf : F.fpi = ∅ := hF.2.2.1.trans ((constraintMapTypesFpi _ D 0).trans hfs)
  have heq : HMX.Equivalent S M E F := by
    have hsem : ∀ ρ ι, ρ.Valid S M → (E.Holds S M ρ ι ↔ F.Holds S M ρ ι) := by
      intro ρ ι hρ
      exact (hE.2.2.2 ρ ι hρ).trans ((constraintBinderEq S M ρ ι C' D' hcd _ _).trans (hF.2.2.2 ρ ι hρ).symm)
    exact ⟨fun ρ ι hρ _ hh => (hsem ρ ι hρ).mp hh,fun ρ ι hρ _ hh => (hsem ρ ι hρ).mpr hh⟩
  change HMX.Proofs.SchemeConversion S M (.all xs.toFinset E (namedTy T')) (.all ys.toFinset F (namedTy U'))
  rw [hyset,← htu]
  exact .qualification (fun X hx => hxo.1 X (List.mem_toFinset.mp hx)) hE.1 hF.1
    (namedTyKind hxo.2.2.1) hEf hFf (hE.2.1.trans ((constraintBinderEqFv hcd).trans hF.2.1.symm)) heq

theorem binderEqSchemeRepresentations (hM : M.Requirements S) (h : Scheme.BinderEq s t) :
    ∀ r u, SchemeRepresentation S M s r → SchemeRepresentation S M t u → s.fpi = ∅ →
      HMX.Proofs.SchemeConversion S M r u := by
  apply Scheme.BinderEq.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun s t _ => ∀ r u, SchemeRepresentation S M s r → SchemeRepresentation S M t u →
      s.fpi = ∅ → HMX.Proofs.SchemeConversion S M r u)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intro s r u hr hu hf; exact equalSchemeRepresentations hM hr hu rfl hf)
    (by intro s t h ih r u hr hu hf; exact .symm (ih u r hu hr ((schemeBinderEqFpi h).trans hf)))
    (by
      intro s t v h g ih ij r u hr hu hf
      have ht := (schemeBinderEqWF h [] 0).mp (schemeRepresentationProperties hr).1
      obtain ⟨w,hw⟩ := schemeRepresentationExists t ht (M := M)
      exact .trans (ih r w hr hw hf) (ij w u hw hu ((schemeBinderEqFpi h).symm.trans hf)))
    (by intro ks ls p D U C T hp hc ht _ r u hr hu hf;
        exact permutedSchemeRepresentations hM hp hc ht hr hu hf) h

end HMX.LN.Proofs
