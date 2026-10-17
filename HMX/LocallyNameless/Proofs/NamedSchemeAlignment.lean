import HMX.LocallyNameless.Proofs.NamedEnvironmentConversion

namespace HMX.LN.Proofs

theorem disjointBlockPermutation (xs ys : List TVar) (hx : xs.Nodup) (hy : ys.Nodup)
    (hd : Disjoint xs.toFinset ys.toFinset) (hk : List.Forall₂ (fun X Y : TVar => X.1 = Y.1) xs ys) :
    ∃ p : TVar ≃ TVar, (∀ X, (p X).1 = X.1) ∧ xs.map p = ys ∧
      ∀ X, X ∉ xs.toFinset ∪ ys.toFinset → p X = X := by
  induction hk with
  | nil => exact ⟨Equiv.refl _,fun _ => rfl,rfl,fun _ _ => rfl⟩
  | @cons X Y xs ys hXY ht ih =>
    have hx' := List.nodup_cons.mp hx
    have hy' := List.nodup_cons.mp hy
    have hds : Disjoint xs.toFinset ys.toFinset := hd.mono
      (by intro Z hz; simpa only [List.toFinset_cons,Finset.mem_insert] using Or.inr hz)
      (by intro Z hz; simpa only [List.toFinset_cons,Finset.mem_insert] using Or.inr hz)
    obtain ⟨p,hpk,hmap,hfix⟩ := ih hx'.2 hy'.2 hds
    have hXys : X ∉ ys := fun h => Finset.disjoint_left.mp hd
      (List.mem_toFinset.mpr (List.mem_cons_self)) (List.mem_toFinset.mpr (List.mem_cons_of_mem _ h))
    have hYxs : Y ∉ xs := fun h => Finset.disjoint_left.mp hd
      (List.mem_toFinset.mpr (List.mem_cons_of_mem _ h)) (List.mem_toFinset.mpr (List.mem_cons_self))
    have hpY : p Y = Y := hfix Y (by simp [hy'.1,hYxs])
    refine ⟨(Equiv.swap X Y).trans p,fun Z => (hpk _).trans (swapKind X Y hXY Z),?_,?_⟩
    · simp only [List.map_cons,Equiv.trans_apply,Equiv.swap_apply_left,hpY]
      congr 1
      apply Eq.trans ?_ hmap
      exact List.map_congr_left (fun Z hz => by
        have hzX : Z ≠ X := fun h => hx'.1 (h ▸ hz)
        have hzY : Z ≠ Y := fun h => hYxs (h ▸ hz)
        simp [Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hzX hzY])
    · intro Z hZ
      have hzX : Z ≠ X := fun h => hZ (by simp [h])
      have hzY : Z ≠ Y := fun h => hZ (by simp [h])
      have hz : Z ∉ xs.toFinset ∪ ys.toFinset := fun h => hZ (by
        simpa only [List.toFinset_cons,Finset.mem_union,Finset.mem_insert] using
          (show (Z = X ∨ Z ∈ xs.toFinset) ∨ (Z = Y ∨ Z ∈ ys.toFinset) from
            (Finset.mem_union.mp h).elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))))
      simp only [Equiv.trans_apply,Equiv.swap_apply_of_ne_of_ne hzX hzY,hfix Z hz]

theorem generalizeInjective (xs : List TVar) (D E : Constraint) (T U : Ty)
    (h : Scheme.generalize xs D T = Scheme.generalize xs E U) : D = E ∧ T = U := by
  have hh := Scheme.all.inj h
  refine ⟨?_,?_⟩
  · have hc := congrArg (Constraint.openTypes (xs.map Ty.free)) hh.2.1
    simpa only [Constraint.closeTypes,Constraint.openTypes,
      constraintMapTypesInverse _ _ (fun d T => tyOpenClose T d xs)] using hc
  · have ht := congrArg (Ty.openAt 0 (xs.map Ty.free)) hh.2.2
    simpa only [tyOpenClose] using ht

theorem namedTyOfEncoding (T : HMX.Ty) : namedTy (ofTy [] T) = T := by
  cases T with
  | var X => simp [ofTy,namedTy]
  | con f ts =>
    simp only [ofTy,namedTy,List.map_map,Function.comp_def]
    congr 1
    exact (List.map_congr_left (g := id) (fun U _ => namedTyOfEncoding U)).trans (List.map_id ts)
termination_by sizeOf T

theorem encodingTyInjective : Function.Injective (ofTy []) := fun _ _ h => by
  have he := congrArg namedTy h
  simpa only [namedTyOfEncoding] using he

theorem encodingNamedTyRename (p : TVar ≃ TVar) (T : HMX.Ty) :
    ofTy [] (HMX.Proofs.namedTyRename p T) = (ofTy [] T).subst (typeRename p) := by
  cases T with
  | var X => simp [ofTy,HMX.Proofs.namedTyRename,Ty.subst,typeRename]
  | con f ts =>
    simp only [ofTy,HMX.Proofs.namedTyRename,Ty.subst,List.map_map,Function.comp_def]
    congr 1
    exact List.map_congr_left (fun U _ => encodingNamedTyRename p U)
termination_by sizeOf T

end HMX.LN.Proofs

namespace HMX.Proofs

open LN.Proofs

theorem namedTyRenameFv (p : TVar ≃ TVar) (T : Ty) :
    (namedTyRename p T).fv = T.fv.image p := by
  have h := tyRenameFv p (LN.ofTy [] T)
  rw [← encodingNamedTyRename] at h
  simpa only [typeRename,encodingTyFv,List.toFinset_nil,Finset.sdiff_empty] using h

mutual
theorem namedConstraintRenameFv (p : TVar ≃ TVar) (C : Constraint) :
    (namedConstraintRename p C).fv = C.fv.image p := by
  cases C with
  | truth | falsity => simp [namedConstraintRename,Constraint.fv]
  | atom q ts =>
    simp only [namedConstraintRename,Constraint.fv,List.map_map,Function.comp_def,namedTyRenameFv]
    induction ts with
    | nil => simp
    | cons T ts ih => simp only [List.map_cons,List.foldr_cons,ih,Finset.image_union]
  | conj C D => simp only [namedConstraintRename,Constraint.fv,namedConstraintRenameFv,Finset.image_union]
  | exists_ A C => simp only [namedConstraintRename,Constraint.fv,namedConstraintRenameFv,Finset.image_sdiff _ _ p.injective]
  | def_ x s C => simp only [namedConstraintRename,Constraint.fv,namedConstraintRenameFv,namedSchemeRenameFv,Finset.image_union]
  | inst x T => exact namedTyRenameFv p T
theorem namedSchemeRenameFv (p : TVar ≃ TVar) (s : Scheme) :
    (namedSchemeRename p s).fv = s.fv.image p := by
  cases s with
  | all A C T => simp only [namedSchemeRename,Scheme.fv,namedConstraintRenameFv,namedTyRenameFv,
      Finset.image_union,Finset.image_sdiff _ _ p.injective]
end

end HMX.Proofs

namespace HMX.LN.Proofs

/-- Two openings of the same scheme can be renamed to the same fresh block.
The free variables of the closed scheme stay fixed. -/
theorem alignGeneralizations (xs ys : List TVar) (D E : Constraint) (T U : Ty)
    (hx : xs.Nodup) (hy : ys.Nodup)
    (he : Scheme.generalize xs D T = Scheme.generalize ys E U) :
    ∃ p q : TVar ≃ TVar, (∀ X, (p X).1 = X.1) ∧ (∀ X, (q X).1 = X.1) ∧
      xs.map p = ys.map q ∧ D.subst (typeRename p) = E.subst (typeRename q) ∧
      T.subst (typeRename p) = U.subst (typeRename q) ∧
      (∀ X ∈ (Scheme.generalize xs D T).fv, p X = X) ∧
      (∀ X ∈ (Scheme.generalize ys E U).fv, q X = X) := by
  have hk : xs.map Prod.fst = ys.map Prod.fst := (Scheme.all.inj he).1
  let F := (Scheme.generalize xs D T).fv
  obtain ⟨zs,hzks,hzn,hzf⟩ := freshKinds (xs.map Prod.fst) (F ∪ xs.toFinset ∪ ys.toFinset)
  have hdzx : Disjoint xs.toFinset zs.toFinset := (hzf.mono_right
    (fun X hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx))).symm
  have hdzy : Disjoint ys.toFinset zs.toFinset := (hzf.mono_right Finset.subset_union_right).symm
  have hxz : List.Forall₂ (fun X Y : TVar => X.1 = Y.1) xs zs := by
    exact List.forall₂_map_left_iff.mp (List.forall₂_map_right_iff.mp (by rw [hzks]; exact List.forall₂_same.mpr (fun _ _ => rfl)))
  have hyz : List.Forall₂ (fun X Y : TVar => X.1 = Y.1) ys zs := by
    exact List.forall₂_map_left_iff.mp (List.forall₂_map_right_iff.mp (by rw [hzks,hk]; exact List.forall₂_same.mpr (fun _ _ => rfl)))
  obtain ⟨p,hpk,hpx,hpf⟩ := disjointBlockPermutation xs zs hx hzn hdzx hxz
  obtain ⟨q,hqk,hqy,hqf⟩ := disjointBlockPermutation ys zs hy hzn hdzy hyz
  have hpf' : ∀ X ∈ (Scheme.generalize xs D T).fv, p X = X := by
    intro X hx
    apply hpf X
    intro hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact (Finset.mem_sdiff.mp (generalizeFv xs D T ▸ hx)).2 hh
    · exact Finset.disjoint_left.mp hzf hh (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have hqf' : ∀ X ∈ (Scheme.generalize ys E U).fv, q X = X := by
    intro X hx
    apply hqf X
    intro hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact (Finset.mem_sdiff.mp (generalizeFv ys E U ▸ hx)).2 hh
    · exact Finset.disjoint_left.mp hzf hh (Finset.mem_union_left _ (Finset.mem_union_left _ (by change X ∈ (Scheme.generalize xs D T).fv; rw [he]; exact hx)))
  have hp := (renameGeneralize p hpk xs D T).symm.trans (schemeRenameFixed p _ hpf')
  have hq := (renameGeneralize q hqk ys E U).symm.trans (schemeRenameFixed q _ hqf')
  rw [hpx] at hp
  rw [hqy] at hq
  have hab := generalizeInjective zs _ _ _ _ (hp.trans (he.trans hq.symm))
  exact ⟨p,q,hpk,hqk,hpx.trans hqy.symm,hab.1,hab.2,hpf',hqf'⟩

end HMX.LN.Proofs
