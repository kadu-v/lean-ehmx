import HMX.LocallyNameless.Proofs.SchemeRepresentations

namespace HMX.LN.Proofs

theorem tyOpenInnerPermutation (T : Ty) (ks ls : List Nat) (p : Nat → Nat)
    (hp : BlockPermutation ks ls p) (us : List Ty) (hu : ∀ U ∈ us, U.LCAt 0)
    (n d : Nat) (hnd : n + ks.length ≤ d) :
    (T.renameAt n p).openAt d us = (T.openAt d us).renameAt n p := by
  induction T using tyInduction with
  | hf X => simp [Ty.renameAt,Ty.openAt]
  | hb i =>
    by_cases hi : i < n + ks.length
    · have he : (if i < n then i else n + p (i-n)) < d := by
        split
        · omega
        · have hpi := (blockPermutationBound ks ls p hp (i-n)).mp (by omega)
          have hlen := hp.1
          omega
      have hid : i < d := by omega
      simp only [Ty.renameAt,Ty.openAt,he,hid,↓reduceIte]
    · have hin : ¬ i < n := by omega
      have hpi : p (i-n) = i-n := hp.2.2.1 _ (by omega)
      have he : n + p (i-n) = i := by omega
      simp only [Ty.renameAt,hin,↓reduceIte,he,Ty.openAt]
      by_cases hid : i < d
      · simp only [hid,↓reduceIte,Ty.renameAt,hin,he]
      · simp only [hid,↓reduceIte]
        cases hget : us[i-d]? with
        | some U =>
          have hU := hu U (List.mem_of_getElem? hget)
          change U.shift d 0 = (U.shift d 0).renameAt n p
          rw [tyShiftClosed U 0 d hU,tyRenameClosed U p n hU]
        | none =>
          have hlen := List.getElem?_eq_none_iff.mp hget
          have hni : ¬ i-us.length < n := by omega
          have hpi' := hp.2.2.1 (i-us.length-n) (by omega)
          simp only [Ty.renameAt,hni,↓reduceIte,hpi']
          congr 1; omega
  | hc f ts ih =>
    simp only [Ty.renameAt,Ty.openAt,List.map_map,Function.comp_def]
    congr 1
    exact List.map_congr_left (fun U hU => ih U hU)

theorem constraintOpenInnerPermutation (C : Constraint) (ks ls : List Nat) (p : Nat → Nat)
    (hp : BlockPermutation ks ls p) (us : List Ty) (hu : ∀ U ∈ us, U.LCAt 0)
    (n d : Nat) (hnd : n + ks.length ≤ d) :
    (C.mapTypes (fun i T => T.renameAt i p) n).mapTypes (fun i T => T.openAt i us) d =
      (C.mapTypes (fun i T => T.openAt i us) d).mapTypes (fun i T => T.renameAt i p) n := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ n d, n + ks.length ≤ d →
      (C.mapTypes (fun i T => T.renameAt i p) n).mapTypes (fun i T => T.openAt i us) d =
        (C.mapTypes (fun i T => T.openAt i us) d).mapTypes (fun i T => T.renameAt i p) n)
    (motive_2 := fun s => ∀ n d, n + ks.length ≤ d →
      (s.mapTypes (fun i T => T.renameAt i p) n).mapTypes (fun i T => T.openAt i us) d =
        (s.mapTypes (fun i T => T.openAt i us) d).mapTypes (fun i T => T.renameAt i p) n)
    (by intros; rfl) (by intros; rfl)
    (by intro q ts n d hnd; simp only [Constraint.mapTypes,List.map_map,Function.comp_def];
        congr 1; exact List.map_congr_left (fun T _ => tyOpenInnerPermutation T ks ls p hp us hu n d hnd))
    (by intro C D ih ij n d hnd; exact congrArg₂ Constraint.conj (ih n d hnd) (ij n d hnd))
    (by intro bs C ih n d hnd; exact congrArg (Constraint.exists_ bs) (ih _ _ (by omega)))
    (by intro b s C ih ij n d hnd; exact congrArg₂ (Constraint.def_ b) (ih n d hnd) (ij n d hnd))
    (by intro x T n d hnd; exact congrArg (Constraint.inst x) (tyOpenInnerPermutation T ks ls p hp us hu n d hnd))
    (by
      intro bs C T ih n d hnd
      exact congrArg₂ (Scheme.all bs) (ih _ _ (by omega))
        (tyOpenInnerPermutation T ks ls p hp us hu _ _ (by omega))) C n d hnd

theorem constraintBinderEqOpening (h : Constraint.BinderEq C D) (us : List Ty)
    (hu : ∀ U ∈ us, U.LCAt 0) (d : Nat) :
    (C.mapTypes (fun i T => T.openAt i us) d).BinderEq (D.mapTypes (fun i T => T.openAt i us) d) := by
  apply Constraint.BinderEq.rec
    (motive_1 := fun C D _ => ∀ d, (C.mapTypes (fun i T => T.openAt i us) d).BinderEq
      (D.mapTypes (fun i T => T.openAt i us) d))
    (motive_2 := fun s r _ => ∀ d, (s.mapTypes (fun i T => T.openAt i us) d).BinderEq
      (r.mapTypes (fun i T => T.openAt i us) d))
    (by intros; exact .refl)
    (by intro C D h ih d; exact .symm (ih d))
    (by intro C D E h g ih ij d; exact .trans (ih d) (ij d))
    (by intro C C' D D' h g ih ij d; exact .conj (ih d) (ij d))
    (by
      intro ks ls p D C hp h ih d
      simp only [Constraint.mapTypes]
      apply Constraint.BinderEq.exists_ hp
      have hh := ih (d + ks.length)
      rw [constraintOpenInnerPermutation _ ks ls p hp us hu 0 _ (by omega),hp.1] at hh
      simpa only [hp.1] using hh)
    (by intro s r C D b h g ih ij d; exact .def_ (ih d) (ij d))
    (by intros; exact .refl)
    (by intro s r h ih d; exact .symm (ih d))
    (by intro s r u h g ih ij d; exact .trans (ih d) (ij d))
    (by
      intro ks ls p D U C T hp hc ht ih d
      simp only [Scheme.mapTypes]
      apply Scheme.BinderEq.all hp
      · have hh := ih (d + ks.length)
        rw [constraintOpenInnerPermutation _ ks ls p hp us hu 0 _ (by omega),hp.1] at hh
        simpa only [hp.1] using hh
      · rw [← tyOpenInnerPermutation T ks ls p hp us hu 0 _ (by omega),ht,hp.1]) h d

end HMX.LN.Proofs
