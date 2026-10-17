import HMX.LocallyNameless.Proofs.OpeningPermutation

namespace HMX.LN.Proofs

theorem blockPermutationKinds (hp : BlockPermutation ks ls p) (k : Nat) : k ∈ ks ↔ k ∈ ls := by
  constructor
  · intro hk
    obtain ⟨i,hi,hk⟩ := List.mem_iff_getElem.mp hk
    exact List.mem_of_getElem? (hp.2.2.2 i ▸ List.getElem?_eq_some_iff.mpr ⟨hi,hk⟩)
  · intro hk
    obtain ⟨i,hi,hk⟩ := List.mem_iff_getElem.mp hk
    obtain ⟨j,hj⟩ := hp.2.1.2 i
    apply List.mem_of_getElem?
    rw [hp.2.2.2 j,hj]
    exact List.getElem?_eq_some_iff.mpr ⟨hi,hk⟩

theorem blockPermutationLookup (pre tail : List Nat) (hp : BlockPermutation ks ls p) (i : Nat) :
    (pre ++ ks ++ tail)[i]? =
      (pre ++ ls ++ tail)[if i < pre.length then i else pre.length + p (i-pre.length)]? := by
  by_cases hi : i < pre.length
  · simp [List.append_assoc,List.getElem?_append,hi]
  · have hn : pre.length ≤ i := by omega
    by_cases hk : i-pre.length < ks.length
    · have hl := (blockPermutationBound ks ls p hp _).mp hk
      simp only [hi,↓reduceIte,List.append_assoc,List.getElem?_append,
        show ¬ pre.length + p (i-pre.length) < pre.length by omega,↓reduceIte,
        Nat.add_sub_cancel_left,hk,hl]
      exact hp.2.2.2 _
    · have he := hp.2.2.1 (i-pre.length) (by omega)
      simp [List.append_assoc,List.getElem?_append,hi,he,Nat.add_sub_of_le hn,hk,← hp.1]

theorem tyPermutationKind (T : Ty) (pre tail : List Nat) (hp : BlockPermutation ks ls p) :
    (T.renameAt pre.length p).HasKind S (pre ++ ls ++ tail) k ↔
      T.HasKind S (pre ++ ks ++ tail) k := by
  induction T using tyInduction generalizing k with
  | hf X => simp only [Ty.renameAt]; constructor <;> intro h <;> cases h <;> constructor <;> assumption
  | hb i =>
    simp only [Ty.renameAt]
    constructor
    · intro h
      cases h with
      | bound hi hk => exact .bound ((blockPermutationLookup pre tail hp i).trans hi) hk
    · intro h
      cases h with
      | bound hi hk => exact .bound ((blockPermutationLookup pre tail hp i).symm.trans hi) hk
  | hc f ts ih =>
    simp only [Ty.renameAt]
    constructor
    · intro h
      cases h with
      | con hf ht =>
        exact .con hf (forall₂ImplMem (List.forall₂_map_left_iff.mp ht) (fun U hu k hk => (ih U hu).mp hk))
    · intro h
      cases h with
      | con hf ht =>
        exact .con hf (List.forall₂_map_left_iff.mpr (forall₂ImplMem ht (fun U hu k hk => (ih U hu).mpr hk)))

theorem constraintPermutationWF (C : Constraint) (pre tail : List Nat) (hp : BlockPermutation ks ls p) (d : Nat) :
    (C.mapTypes (fun n T => T.renameAt n p) pre.length).WF S (pre ++ ls ++ tail) d ↔
      C.WF S (pre ++ ks ++ tail) d := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ pre d,
      (C.mapTypes (fun n T => T.renameAt n p) pre.length).WF S (pre ++ ls ++ tail) d ↔
        C.WF S (pre ++ ks ++ tail) d)
    (motive_2 := fun s => ∀ pre d,
      (s.mapTypes (fun n T => T.renameAt n p) pre.length).WF S (pre ++ ls ++ tail) d ↔
        s.WF S (pre ++ ks ++ tail) d)
    (by intros; rfl) (by intros; rfl)
    (by
      intro q ts pre d
      apply and_congr Iff.rfl
      constructor
      · intro ht
        exact forall₂ImplMem (List.forall₂_map_left_iff.mp ht) (fun T _ k hk => (tyPermutationKind T pre tail hp).mp hk)
      · intro ht
        exact List.forall₂_map_left_iff.mpr (ht.imp (fun T _ hk => (tyPermutationKind T pre tail hp).mpr hk)))
    (by intro C D ih ij pre d; exact and_congr (ih pre d) (ij pre d))
    (by intro bs C ih pre d; apply and_congr Iff.rfl;
        simpa only [List.length_append,List.append_assoc,Nat.add_comm] using ih (bs ++ pre) d)
    (by intro b s C ih ij pre d; exact and_congr (ih pre d) (ij pre (d+1)))
    (by intro x T pre d; exact and_congr (tyPermutationKind T pre tail hp) Iff.rfl)
    (by
      intro bs C T ih pre d
      apply and_congr Iff.rfl
      apply and_congr
      · simpa only [List.length_append,List.append_assoc,Nat.add_comm] using ih (bs ++ pre) d
      · simpa only [List.length_append,List.append_assoc,Nat.add_comm] using tyPermutationKind T (bs ++ pre) tail hp)
    C pre d

theorem constraintBinderEqWF (h : Constraint.BinderEq C D) : ∀ ks d, C.WF S ks d ↔ D.WF S ks d := by
  apply Constraint.BinderEq.rec
    (motive_1 := fun C D _ => ∀ ks d, C.WF S ks d ↔ D.WF S ks d)
    (motive_2 := fun s r _ => ∀ ks d, s.WF S ks d ↔ r.WF S ks d)
    (by intros; rfl)
    (by intro C D h ih ks d; exact (ih ks d).symm)
    (by intro C D E h g ih ij ks d; exact (ih ks d).trans (ij ks d))
    (by intro C C' D D' h g ih ij ks d; exact and_congr (ih ks d) (ij ks d))
    (by
      intro bs cs p D C hp h ih ks d
      apply and_congr
      · exact forall_congr' (fun k => imp_congr (blockPermutationKinds hp k) Iff.rfl)
      · exact (constraintPermutationWF C [] ks hp d).symm.trans (ih (cs ++ ks) d))
    (by intro s r C D b h g ih ij ks d; exact and_congr (ih ks d) (ij ks (d+1)))
    (by intros; rfl)
    (by intro s r h ih ks d; exact (ih ks d).symm)
    (by intro s r u h g ih ij ks d; exact (ih ks d).trans (ij ks d))
    (by
      intro bs cs p D U C T hp hc ht ih ks d
      apply and_congr
      · exact forall_congr' (fun k => imp_congr (blockPermutationKinds hp k) Iff.rfl)
      · apply and_congr
        · exact (constraintPermutationWF C [] ks hp d).symm.trans (ih (cs ++ ks) d)
        · have hh := (tyPermutationKind (S := S) (k := 0) T [] ks hp).symm
          rw [show T.renameAt [].length p = U from ht] at hh
          exact hh) h

theorem schemeBinderEqWF (h : Scheme.BinderEq s r) : ∀ ks d, s.WF S ks d ↔ r.WF S ks d := by
  apply Scheme.BinderEq.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun s r _ => ∀ ks d, s.WF S ks d ↔ r.WF S ks d)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; rfl)
    (by intro s r h ih ks d; exact (ih ks d).symm)
    (by intro s r u h g ih ij ks d; exact (ih ks d).trans (ij ks d))
    (by
      intro bs cs p D U C T hp hc ht _ ks d
      apply and_congr
      · exact forall_congr' (fun k => imp_congr (blockPermutationKinds hp k) Iff.rfl)
      · apply and_congr
        · exact (constraintPermutationWF C [] ks hp d).symm.trans (constraintBinderEqWF hc (cs ++ ks) d)
        · have hh := (tyPermutationKind (S := S) (k := 0) T [] ks hp).symm
          rw [show T.renameAt [].length p = U from ht] at hh
          exact hh) h

end HMX.LN.Proofs
