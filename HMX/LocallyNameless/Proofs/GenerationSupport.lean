import HMX.LocallyNameless.Proofs.Environment

namespace HMX.LN.Proofs

theorem tyCloseKind (S : Signature) (T : Ty) (bs : List Nat) (xs : List TVar) (k : Nat)
    (h : T.HasKind S bs k) : (T.closeAt bs.length xs).HasKind S (bs ++ xs.map Prod.fst) k := by
  induction T using tyInduction generalizing k with
  | hf X =>
      cases h with
      | free hx =>
          by_cases hm : X ∈ xs
          · simp only [Ty.closeAt, hm, ↓reduceIte]
            apply Ty.HasKind.bound _ hx
            simp [List.getElem?_append, List.getElem?_map, List.getElem?_idxOf hm]
          · simpa [Ty.closeAt, hm] using (Ty.HasKind.free hx : Ty.HasKind S (bs ++ xs.map Prod.fst) (.free X) X.1)
  | hb i =>
      cases h with
      | bound hi hk =>
          have hib := (List.getElem?_eq_some_iff.mp hi).1
          simp only [Ty.closeAt, hib, ↓reduceIte]
          exact .bound (by simpa [List.getElem?_append, hib] using hi) hk
  | hc f ts ih =>
      cases h with
      | con hf hs =>
          simp only [Ty.closeAt]
          apply Ty.HasKind.con hf
          exact List.forall₂_map_left_iff.mpr (forall₂ImplMem hs (fun U hu p hp => ih U hu _ hp))

theorem constraintCloseWF (S : Signature) (xs : List TVar) (C : Constraint) (bs : List Nat)
    (d : Nat) (h : C.WF S bs d) :
    (C.mapTypes (fun n T => T.closeAt n xs) bs.length).WF S (bs ++ xs.map Prod.fst) d := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ bs d, C.WF S bs d → (C.mapTypes (fun n T => T.closeAt n xs) bs.length).WF S (bs ++ xs.map Prod.fst) d)
    (motive_2 := fun s => ∀ bs d, s.WF S bs d → (s.mapTypes (fun n T => T.closeAt n xs) bs.length).WF S (bs ++ xs.map Prod.fst) d)
    (by intros; trivial) (by intros; trivial)
    (by intro p ts bs d h; exact ⟨h.1, List.forall₂_map_left_iff.mpr (List.Forall₂.imp (fun T k hk => tyCloseKind S T bs xs k hk) h.2)⟩)
    (by intro C D ihC ihD bs d h; exact ⟨ihC bs d h.1, ihD bs d h.2⟩)
    (by intro ks C ih bs d h; refine ⟨h.1, ?_⟩; simpa [List.length_append, List.append_assoc, Nat.add_comm] using ih (ks ++ bs) d h.2)
    (by intro b s C ihs ihC bs d h; exact ⟨ihs bs d h.1, ihC bs (d+1) h.2⟩)
    (by intro x T bs d h; exact ⟨tyCloseKind S T bs xs 0 h.1, h.2⟩)
    (by
      intro ks C T ih bs d h
      refine ⟨h.1, ?_, ?_⟩
      · simpa [List.length_append, List.append_assoc, Nat.add_comm] using ih (ks ++ bs) d h.2.1
      · simpa [List.length_append, List.append_assoc, Nat.add_comm] using tyCloseKind S T (ks ++ bs) xs 0 h.2.2) C bs d h

theorem existsNamesWF (S : Signature) (xs : List TVar) (C : Constraint) (d : Nat)
    (hx : ∀ X ∈ xs, X.1 ∈ S.kinds) (hc : C.WF S [] d) : (C.existsNames xs).WF S [] d := by
  refine ⟨?_, ?_⟩
  · intro k hk; obtain ⟨X,hX,rfl⟩ := List.mem_map.mp hk; exact hx X hX
  · simpa [Constraint.closeTypes] using constraintCloseWF S xs C [] d hc

theorem generalizeWF (S : Signature) (xs : List TVar) (C : Constraint) (T : Ty) (d : Nat)
    (hx : ∀ X ∈ xs, X.1 ∈ S.kinds) (hc : C.WF S [] d) (ht : T.HasKind S [] 0) :
    (Scheme.generalize xs C T).WF S [] d := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk; obtain ⟨X,hX,rfl⟩ := List.mem_map.mp hk; exact hx X hX
  · simpa [Constraint.closeTypes] using constraintCloseWF S xs C [] d hc
  · simpa using tyCloseKind S T [] xs 0 ht

theorem arrowKind (S : Signature) (hS : S.Valid) (T U : Ty) (ks : List Nat)
    (ht : T.HasKind S ks 0) (hu : U.HasKind S ks 0) : (Ty.arrow T U).HasKind S ks 0 := by
  rw [← hS.2.2.2.1]
  apply Ty.HasKind.con hS.2.1
  rw [hS.2.2.1]
  exact .cons ht (.cons hu .nil)

theorem letBoundWF (S : Signature) (b : Binder) (s : Scheme) (C : Constraint) (d : Nat)
    (hs : s.WF S [] d) (hc : C.WF S [] (d+1)) : (C.letBound b s).WF S [] d := by
  exact ⟨by cases s; exact ⟨hs.1,hs.2.1⟩, hs,hc⟩

theorem monoWFAt (S : Signature) (T : Ty) (d : Nat) (ht : T.HasKind S [] 0) :
    (Scheme.mono T).WF S [] d := ⟨by simp, trivial, ht⟩

theorem memUnionFold {α β : Type} [DecidableEq β] (f : α → Finset β) (xs : List α) (x : β) :
    x ∈ (xs.map f).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ xs, x ∈ f a := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih, or_and_right, exists_or, eq_comm]

theorem tyCloseFv (T : Ty) (d : Nat) (xs : List TVar) :
    (T.closeAt d xs).fv = T.fv \ xs.toFinset := by
  induction T using tyInduction with
  | hf X =>
      ext Y
      by_cases h : X ∈ xs <;> simp [Ty.closeAt, Ty.fv, h, Finset.mem_sdiff] <;> aesop
  | hb i => simp [Ty.closeAt, Ty.fv]
  | hc f ts ih =>
      ext X
      simp only [Ty.closeAt, Ty.fv, List.map_map, memUnionFold, Function.comp_apply, Finset.mem_sdiff]
      constructor
      · rintro ⟨U,hu,hX⟩
        rw [ih U hu] at hX
        exact ⟨⟨U,hu,(Finset.mem_sdiff.mp hX).1⟩,(Finset.mem_sdiff.mp hX).2⟩
      · rintro ⟨⟨U,hu,hX⟩,hx⟩
        exact ⟨U,hu,by rw [ih U hu]; exact Finset.mem_sdiff.mpr ⟨hX,hx⟩⟩

theorem constraintCloseFv (xs : List TVar) (C : Constraint) (d : Nat) :
    (C.mapTypes (fun n T => T.closeAt n xs) d).fv = C.fv \ xs.toFinset := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, (C.mapTypes (fun n T => T.closeAt n xs) d).fv = C.fv \ xs.toFinset)
    (motive_2 := fun s => ∀ d, (s.mapTypes (fun n T => T.closeAt n xs) d).fv = s.fv \ xs.toFinset)
    (by intros; simp [Constraint.mapTypes, Constraint.fv])
    (by intros; simp [Constraint.mapTypes, Constraint.fv])
    (by
      intro p ts d
      ext X
      simp only [Constraint.mapTypes, Constraint.fv, List.map_map, memUnionFold, Function.comp_apply, tyCloseFv, Finset.mem_sdiff]
      constructor
      · rintro ⟨T,ht,hX,hx⟩; exact ⟨⟨T,ht,hX⟩,hx⟩
      · rintro ⟨⟨T,ht,hX⟩,hx⟩; exact ⟨T,ht,hX,hx⟩)
    (by intro C D ihC ihD d; simp [Constraint.mapTypes, Constraint.fv, ihC, ihD, Finset.union_sdiff_distrib])
    (by intro ks C ih d; exact ih _)
    (by intro b s C ihs ihC d; simp [Constraint.mapTypes, Constraint.fv, ihs, ihC, Finset.union_sdiff_distrib])
    (by intro x T d; exact tyCloseFv T d xs)
    (by intro ks C T ih d; simp [Scheme.mapTypes, Scheme.fv, ih, tyCloseFv, Finset.union_sdiff_distrib]) C d

theorem constraintMapTypesFpi (f : Nat → Ty → Ty) (C : Constraint) (d : Nat) :
    (C.mapTypes f d).fpi = C.fpi := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, (C.mapTypes f d).fpi = C.fpi)
    (motive_2 := fun s => ∀ d, (s.mapTypes f d).fpi = s.fpi)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intro C D ihC ihD d; simp [Constraint.mapTypes, Constraint.fpi, ihC, ihD])
    (by intro ks C ih d; exact ih _)
    (by intro b s C ihs ihC d; simp [Constraint.mapTypes, Constraint.fpi, ihs, ihC])
    (by intro x T d; cases x <;> rfl)
    (by intro ks C T ih d; exact ih _) C d

theorem tyFvMax (T : Ty) (X : TVar) (h : X ∈ T.fv) : X.2 ≤ T.maxIndex := by
  induction T using tyInduction with
  | hf Y => simp only [Ty.fv, Finset.mem_singleton] at h; subst X; simp [Ty.maxIndex]
  | hb i => simp [Ty.fv] at h
  | hc f ts ih =>
      simp only [Ty.fv] at h
      obtain ⟨U,hu,hX⟩ := (memUnionFold Ty.fv ts X).mp h
      have hh := ih U hu hX
      simp only [Ty.maxIndex]
      have hm : ∀ (us : List Ty) (V : Ty), V ∈ us → V.maxIndex ≤ (us.map Ty.maxIndex).foldr max 0 := by
        intro us
        induction us with
        | nil => simp
        | cons W us ih =>
            intro V hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact Nat.le_max_left _ _
            · exact (ih V hv).trans (Nat.le_max_right _ _)
      exact hh.trans (hm ts U hu)

theorem freshNotMem (T : Ty) (n : Nat) : (0, freshIndex T + n) ∉ T.fv := by
  intro h
  have := tyFvMax T _ h
  simp only [freshIndex] at this
  omega

theorem tyCloseUnused (T : Ty) (xs : List TVar) (d : Nat) (hc : T.LCAt 0)
    (hf : Disjoint xs.toFinset T.fv) : T.closeAt d xs = T := by
  induction T using tyInduction with
  | hf X =>
      have hx : X ∉ xs := by simpa [Ty.fv] using hf
      simp [Ty.closeAt, hx]
  | hb i => simp [Ty.LCAt] at hc
  | hc f ts ih =>
      simp only [Ty.closeAt]
      congr 1
      apply (List.map_congr_left (g := id) ?_).trans (List.map_id ts)
      intro U hu
      simp only [Ty.LCAt] at hc
      simp only [Ty.fv] at hf
      exact ih U hu (hc U hu) (Finset.disjoint_left.mpr (fun X hx hX =>
        Finset.disjoint_left.mp hf hx ((memUnionFold Ty.fv ts X).mpr ⟨U,hu,hX⟩)))

theorem tySubstCongr (T : Ty) (θ σ : Subst) (h : ∀ X ∈ T.fv, θ X = σ X) : T.subst θ = T.subst σ := by
  induction T using tyInduction with
  | hf X => simpa only [Ty.subst] using h X (by simp [Ty.fv])
  | hb i => simp [Ty.subst]
  | hc f ts ih =>
      simp only [Ty.subst]
      congr 1
      exact List.map_congr_left (fun U hu => ih U hu (fun X hx => h X (by simpa only [Ty.fv] using (memUnionFold Ty.fv ts X).mpr ⟨U,hu,hx⟩)))

theorem tySubstFvMember (T : Ty) (θ : Subst) (X : TVar) (hx : X ∈ T.fv) :
    (θ X).fv ⊆ (T.subst θ).fv := by
  induction T using tyInduction with
  | hf Y => simp only [Ty.fv, Finset.mem_singleton] at hx; subst X; simp [Ty.subst]
  | hb i => simp [Ty.fv] at hx
  | hc f ts ih =>
      simp only [Ty.fv] at hx
      obtain ⟨U,hu,hx⟩ := (memUnionFold Ty.fv ts X).mp hx
      intro Y hy
      simp only [Ty.subst, Ty.fv, List.map_map, memUnionFold, Function.comp_apply]
      exact ⟨U,hu,ih U hu hx hy⟩

theorem tyCloseSubst (T : Ty) (xs ys : List TVar) (θ σ : Subst) (d : Nat)
    (hlen : xs.length = ys.length)
    (h : ∀ X ∈ T.fv, ((Ty.free X).closeAt d xs).subst θ = (σ X).closeAt d ys) :
    (T.closeAt d xs).subst θ = (T.subst σ).closeAt d ys := by
  induction T using tyInduction with
  | hf X => simpa only [Ty.subst] using h X (by simp [Ty.fv])
  | hb i => simp [Ty.closeAt, Ty.subst, hlen]
  | hc f ts ih =>
      simp only [Ty.closeAt, Ty.subst, List.map_map]
      congr 1
      exact List.map_congr_left (fun U hu => ih U hu (fun X hx => h X (by simpa only [Ty.fv] using (memUnionFold Ty.fv ts X).mpr ⟨U,hu,hx⟩)))

theorem constraintMapTypesConstant (f : Ty → Ty) (C : Constraint) (a b : Nat) :
    C.mapTypes (fun _ => f) a = C.mapTypes (fun _ => f) b := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ a b, C.mapTypes (fun _ => f) a = C.mapTypes (fun _ => f) b)
    (motive_2 := fun s => ∀ a b, s.mapTypes (fun _ => f) a = s.mapTypes (fun _ => f) b)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intro C D ihC ihD a b; exact congrArg₂ Constraint.conj (ihC a b) (ihD a b))
    (by intro ks C ih a b; exact congrArg (Constraint.exists_ ks) (ih _ _))
    (by intro k s C ihs ihC a b; exact congrArg₂ (Constraint.def_ k) (ihs a b) (ihC a b))
    (by intros; rfl)
    (by intro ks C T ih a b; exact congrArg (fun D => Scheme.all ks D (f T)) (ih _ _)) C a b

theorem constraintSubstAt (θ : Subst) (C : Constraint) (d : Nat) :
    C.mapTypes (fun _ T => T.subst θ) d = C.subst θ :=
  constraintMapTypesConstant (Ty.subst θ) C d 0

theorem constraintCloseSubst (C : Constraint) (xs ys : List TVar) (θ σ : Subst) (d : Nat)
    (hlen : xs.length = ys.length)
    (h : ∀ n X, X ∈ C.fv → ((Ty.free X).closeAt n xs).subst θ = (σ X).closeAt n ys) :
    ((C.mapTypes (fun n T => T.closeAt n xs) d).subst θ) =
    (C.subst σ).mapTypes (fun n T => T.closeAt n ys) d := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, (∀ n X, X ∈ C.fv → ((Ty.free X).closeAt n xs).subst θ = (σ X).closeAt n ys) →
      (C.mapTypes (fun n T => T.closeAt n xs) d).subst θ = (C.subst σ).mapTypes (fun n T => T.closeAt n ys) d)
    (motive_2 := fun s => ∀ d, (∀ n X, X ∈ s.fv → ((Ty.free X).closeAt n xs).subst θ = (σ X).closeAt n ys) →
      (s.mapTypes (fun n T => T.closeAt n xs) d).subst θ = (s.subst σ).mapTypes (fun n T => T.closeAt n ys) d)
    (by intros; rfl) (by intros; rfl)
    (by
      intro p ts d hh
      simp only [Constraint.mapTypes, Constraint.subst, List.map_map]
      congr 1
      exact List.map_congr_left (fun T ht => tyCloseSubst T xs ys θ σ d hlen
        (fun X hx => hh d X ((memUnionFold Ty.fv ts X).mpr ⟨T,ht,hx⟩))))
    (by
      intro C D ihC ihD d hh
      change Constraint.conj _ _ = Constraint.conj _ _
      congr 1
      · exact ihC d (fun n X hx => hh n X (Finset.mem_union_left _ hx))
      · exact ihD d (fun n X hx => hh n X (Finset.mem_union_right _ hx)))
    (by intro ks C ih d hh; change Constraint.exists_ ks _ = Constraint.exists_ ks _; congr 1; simpa only [constraintSubstAt] using ih (d+ks.length) hh)
    (by
      intro b s C ihs ihC d hh
      change Constraint.def_ b _ _ = Constraint.def_ b _ _
      congr 1
      · exact ihs d (fun n X hx => hh n X (Finset.mem_union_left _ hx))
      · exact ihC d (fun n X hx => hh n X (Finset.mem_union_right _ hx)))
    (by intro x T d hh; change Constraint.inst x _ = Constraint.inst x _; congr 1; exact tyCloseSubst T xs ys θ σ d hlen (hh d))
    (by
      intro ks C T ih d hh
      change Scheme.all ks _ _ = Scheme.all ks _ _
      congr 1
      · simpa only [constraintSubstAt] using ih (d+ks.length) (fun n X hx => hh n X (Finset.mem_union_left _ hx))
      · exact tyCloseSubst T xs ys θ σ _ hlen (fun X hx => hh _ X (Finset.mem_union_right _ hx))) C d h

theorem substConj (θ : Subst) (C D : Constraint) :
    (Constraint.conj C D).subst θ = .conj (C.subst θ) (D.subst θ) := rfl

theorem substLe (θ : Subst) (k : Nat) (T U : Ty) :
    (Constraint.le k T U).subst θ = .le k (T.subst θ) (U.subst θ) := rfl

theorem substMono (θ : Subst) (T : Ty) : (Scheme.mono T).subst θ = .mono (T.subst θ) := rfl

theorem substLetBound (θ : Subst) (b : Binder) (s : Scheme) (C : Constraint) :
    (C.letBound b s).subst θ = (C.subst θ).letBound b (s.subst θ) := by
  cases s with
  | all ks D T =>
      simp only [Constraint.letBound, Constraint.subst, Constraint.mapTypes, Scheme.exists_, Scheme.subst,
        Scheme.mapTypes]

theorem substExistsRename (C : Constraint) (xs ys : List TVar) (θ σ : Subst)
    (hk : xs.map Prod.fst = ys.map Prod.fst)
    (h : ∀ n X, X ∈ C.fv → ((Ty.free X).closeAt n xs).subst θ = (σ X).closeAt n ys) :
    (C.existsNames xs).subst θ = (C.subst σ).existsNames ys := by
  have hn : xs.length = ys.length := by simpa using congrArg List.length hk
  simp only [Constraint.existsNames, Constraint.subst, Constraint.mapTypes, Constraint.closeTypes,
    Nat.zero_add, hk]
  simp only [constraintSubstAt]
  congr 1
  exact constraintCloseSubst C xs ys θ σ 0 hn h

theorem substGeneralizeRename (C : Constraint) (T : Ty) (xs ys : List TVar) (θ σ : Subst)
    (hk : xs.map Prod.fst = ys.map Prod.fst)
    (h : ∀ n X, X ∈ C.fv ∪ T.fv → ((Ty.free X).closeAt n xs).subst θ = (σ X).closeAt n ys) :
    (Scheme.generalize xs C T).subst θ = Scheme.generalize ys (C.subst σ) (T.subst σ) := by
  have hn : xs.length = ys.length := by simpa using congrArg List.length hk
  simp only [Scheme.generalize, Scheme.subst, Scheme.mapTypes, Constraint.closeTypes, constraintSubstAt,
    List.length_map, Nat.zero_add, hk]
  congr 1
  · exact constraintCloseSubst C xs ys θ σ 0 hn (fun n X hx => h n X (Finset.mem_union_left _ hx))
  · exact tyCloseSubst T xs ys θ σ 0 hn (fun X hx => h 0 X (Finset.mem_union_right _ hx))

def renameOne (θ : Subst) (X Y : TVar) : Subst := fun Z => if Z = X then .free Y else θ Z

def renameTwo (θ : Subst) (X Y U V : TVar) : Subst :=
  fun Z => if Z = X then .free U else if Z = Y then .free V else θ Z

theorem renameOneClosed (θ : Subst) (X Y : TVar) (hθ : ∀ Z, (θ Z).LCAt 0) :
    ∀ Z, (renameOne θ X Y Z).LCAt 0 := by
  intro Z; by_cases h : Z = X <;> simp [renameOne, h, Ty.LCAt, hθ]

theorem renameTwoClosed (θ : Subst) (X Y U V : TVar) (hθ : ∀ Z, (θ Z).LCAt 0) :
    ∀ Z, (renameTwo θ X Y U V Z).LCAt 0 := by
  intro Z
  unfold renameTwo
  split
  · simp [Ty.LCAt]
  · split
    · simp [Ty.LCAt]
    · exact hθ Z

theorem renameOneTarget (θ : Subst) (X Y : TVar) (T : Ty) (hx : X ∉ T.fv) :
    T.subst (renameOne θ X Y) = T.subst θ := by
  apply tySubstCongr
  intro Z hz
  have h : Z ≠ X := fun he => hx (he ▸ hz)
  simp [renameOne, h]

theorem renameTwoTarget (θ : Subst) (X Y U V : TVar) (T : Ty) (hx : X ∉ T.fv) (hy : Y ∉ T.fv) :
    T.subst (renameTwo θ X Y U V) = T.subst θ := by
  apply tySubstCongr
  intro Z hz
  have hX : Z ≠ X := fun he => hx (he ▸ hz)
  have hY : Z ≠ Y := fun he => hy (he ▸ hz)
  simp [renameTwo, hX, hY]

theorem renameOneClose (θ : Subst) (T : Ty) (X Y : TVar) (hθ : ∀ Z, (θ Z).LCAt 0)
    (hy : Y ∉ (T.subst θ).fv) (n : Nat) (Z : TVar) (hz : Z ∈ insert X T.fv) :
    ((Ty.free Z).closeAt n [X]).subst θ = (renameOne θ X Y Z).closeAt n [Y] := by
  by_cases he : Z = X
  · subst Z; simp [Ty.closeAt, Ty.subst, renameOne]
  · have hzT : Z ∈ T.fv := (Finset.mem_insert.mp hz).resolve_left he
    have hY : Y ∉ (θ Z).fv := fun h => hy (tySubstFvMember T θ Z hzT h)
    simp only [Ty.closeAt, List.mem_singleton, he, ↓reduceIte, Ty.subst, renameOne]
    exact (tyCloseUnused (θ Z) [Y] n (hθ Z) (by simpa using hY)).symm

theorem renameTwoClose (θ : Subst) (T : Ty) (X Y U V : TVar) (hθ : ∀ Z, (θ Z).LCAt 0)
    (hxy : X ≠ Y) (huv : U ≠ V) (hu : U ∉ (T.subst θ).fv) (hv : V ∉ (T.subst θ).fv)
    (n : Nat) (Z : TVar) (hz : Z ∈ insert X (insert Y T.fv)) :
    ((Ty.free Z).closeAt n [X,Y]).subst θ = (renameTwo θ X Y U V Z).closeAt n [U,V] := by
  by_cases hx : Z = X
  · subst Z; simp [Ty.closeAt, Ty.subst, renameTwo]
  · by_cases hy : Z = Y
    · subst Z; simp [Ty.closeAt, Ty.subst, renameTwo, Ne.symm hxy, Ne.symm huv, hxy, huv]
    · have hzT : Z ∈ T.fv := ((Finset.mem_insert.mp hz).resolve_left hx |> Finset.mem_insert.mp).resolve_left hy
      have hU : U ∉ (θ Z).fv := fun h => hu (tySubstFvMember T θ Z hzT h)
      have hV : V ∉ (θ Z).fv := fun h => hv (tySubstFvMember T θ Z hzT h)
      simp only [Ty.closeAt, List.mem_cons, List.not_mem_nil, hx, hy, or_self, ↓reduceIte, Ty.subst, renameTwo]
      exact (tyCloseUnused (θ Z) [U,V] n (hθ Z) (by simpa using And.intro hU hV)).symm

theorem constraintMapTypesIds (f : Nat → Ty → Ty) (g : Nat → PVar → PVar)
    (C : Constraint) (a b : Nat) :
    (C.mapTypes f a).mapIds g b = (C.mapIds g b).mapTypes f a := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ a b, (C.mapTypes f a).mapIds g b = (C.mapIds g b).mapTypes f a)
    (motive_2 := fun s => ∀ a b, (s.mapTypes f a).mapIds g b = (s.mapIds g b).mapTypes f a)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; simp_all [Constraint.mapTypes, Constraint.mapIds])
    (by intros; simp_all [Constraint.mapTypes, Constraint.mapIds])
    (by intros; simp_all [Constraint.mapTypes, Constraint.mapIds])
    (by intros; rfl)
    (by intros; simp_all [Scheme.mapTypes, Scheme.mapIds]) C a b

theorem mapIdsExistsNames (g : Nat → PVar → PVar) (C : Constraint) (xs : List TVar) (d : Nat) :
    (C.existsNames xs).mapIds g d = (C.mapIds g d).existsNames xs := by
  simp only [Constraint.existsNames, Constraint.closeTypes, Constraint.mapIds, constraintMapTypesIds]

theorem mapIdsGeneralize (g : Nat → PVar → PVar) (C : Constraint) (T : Ty) (xs : List TVar) (d : Nat) :
    (Scheme.generalize xs C T).mapIds g d = Scheme.generalize xs (C.mapIds g d) T := by
  simp only [Scheme.generalize, Scheme.mapIds, Constraint.closeTypes, constraintMapTypesIds]

theorem mapIdsLetBound (g : Nat → PVar → PVar) (C : Constraint) (s : Scheme) (b : Binder) (d : Nat) :
    (C.letBound b s).mapIds g d = (C.mapIds g (d+1)).letBound b (s.mapIds g d) := by
  cases s; rfl

theorem tySubstIdentity (T : Ty) : T.subst Ty.free = T := by
  induction T using tyInduction with
  | hf X => simp [Ty.subst]
  | hb i => simp [Ty.subst]
  | hc f ts ih =>
      simp only [Ty.subst]
      congr 1
      exact (List.map_congr_left (g := id) (fun U hu => ih U hu)).trans (List.map_id ts)

theorem constraintSubstIdentity (C : Constraint) : C.subst Ty.free = C := by
  have h : ∀ (C : Constraint) d, C.mapTypes (fun _ T => T.subst Ty.free) d = C := by
    intro C
    apply Constraint.rec
      (motive_1 := fun C => ∀ d, C.mapTypes (fun _ T => T.subst Ty.free) d = C)
      (motive_2 := fun s => ∀ d, s.mapTypes (fun _ T => T.subst Ty.free) d = s)
      (by intros; rfl) (by intros; rfl)
      (by intro p ts d; simp [Constraint.mapTypes, tySubstIdentity])
      (by intros; simp_all [Constraint.mapTypes])
      (by intros; simp_all [Constraint.mapTypes])
      (by intros; simp_all [Constraint.mapTypes])
      (by intros; simp [Constraint.mapTypes, tySubstIdentity])
      (by intros; simp_all [Scheme.mapTypes, tySubstIdentity]) C
  exact h C 0

theorem constraintCloseIdWF (S : Signature) (x : Id) (C : Constraint) (ks : List Nat)
    (n d : Nat) (hn : n ≤ d) (hc : C.WF S ks d) :
    (C.mapIds (fun n v => v.closeAt n x) n).WF S ks (d+1) := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ ks n d, n ≤ d → C.WF S ks d → (C.mapIds (fun n v => v.closeAt n x) n).WF S ks (d+1))
    (motive_2 := fun s => ∀ ks n d, n ≤ d → s.WF S ks d → (s.mapIds (fun n v => v.closeAt n x) n).WF S ks (d+1))
    (by intros; trivial) (by intros; trivial)
    (by intro p ts ks n d hn hc; exact hc)
    (by intro C D ihC ihD ks n d hn hc; exact ⟨ihC ks n d hn hc.1, ihD ks n d hn hc.2⟩)
    (by intro bs C ih ks n d hn hc; exact ⟨hc.1, ih (bs ++ ks) n d hn hc.2⟩)
    (by intro b s C ihs ihC ks n d hn hc; exact ⟨ihs ks n d hn hc.1, ihC ks (n+1) (d+1) (by omega) hc.2⟩)
    (by
      intro v T ks n d hn hc
      cases v with
      | free y =>
          by_cases hy : y = x
          · exact ⟨hc.1, by simpa [PVar.closeAt, hy] using Nat.lt_succ_of_le hn⟩
          · exact ⟨hc.1, by simp [PVar.closeAt, hy]⟩
      | bound i =>
          refine ⟨hc.1, ?_⟩
          have hi := hc.2
          simp only [PVar.closeAt]
          split <;> omega)
    (by intro bs C T ih ks n d hn hs; exact ⟨hs.1, ih (bs ++ ks) n d hn hs.2.1, hs.2.2⟩) C ks n d hn hc

theorem constraintMapIdsFv (f : Nat → PVar → PVar) (C : Constraint) (d : Nat) :
    (C.mapIds f d).fv = C.fv := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, (C.mapIds f d).fv = C.fv)
    (motive_2 := fun s => ∀ d, (s.mapIds f d).fv = s.fv)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intros; simp_all [Constraint.mapIds, Constraint.fv])
    (by intros; simp_all [Constraint.mapIds, Constraint.fv])
    (by intros; simp_all [Constraint.mapIds, Constraint.fv])
    (by intros; rfl)
    (by intros; simp_all [Scheme.mapIds, Scheme.fv]) C d

theorem constraintCloseIdFpi (x : Id) (C : Constraint) (d : Nat) :
    (C.mapIds (fun n v => v.closeAt n x) d).fpi = C.fpi.erase x := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, (C.mapIds (fun n v => v.closeAt n x) d).fpi = C.fpi.erase x)
    (motive_2 := fun s => ∀ d, (s.mapIds (fun n v => v.closeAt n x) d).fpi = s.fpi.erase x)
    (by intros; simp [Constraint.mapIds, Constraint.fpi])
    (by intros; simp [Constraint.mapIds, Constraint.fpi])
    (by intros; simp [Constraint.mapIds, Constraint.fpi])
    (by intro C D ihC ihD d; simp only [Constraint.mapIds, Constraint.fpi, ihC, ihD]; ext y; simp only [Finset.mem_union, Finset.mem_erase]; tauto)
    (by intro ks C ih d; exact ih d)
    (by intro b s C ihs ihC d; simp only [Constraint.mapIds, Constraint.fpi, ihs, ihC]; ext y; simp only [Finset.mem_union, Finset.mem_erase]; tauto)
    (by
      intro v T d
      cases v with
      | free y =>
          by_cases hy : y = x
          · simp [Constraint.mapIds, PVar.closeAt, Constraint.fpi, hy]
          · simp [Constraint.mapIds, PVar.closeAt, Constraint.fpi, hy, Ne.symm hy]
      | bound i => simp [Constraint.mapIds, PVar.closeAt, Constraint.fpi])
    (by intro ks C T ih d; exact ih d) C d

theorem letInWF (S : Signature) (Γ : Env) (C : Constraint) (hΓ : Γ.WF S) (hc : C.WF S [] 0) :
    (Γ.letIn C).WF S [] 0 := by
  induction Γ with
  | nil => exact hc
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      have hs := hΓ (x,s) (by simp)
      have hh := ih (fun p hp => hΓ p (by simp [hp]))
      exact ⟨schemeExistsWF S s hs, hs, constraintCloseIdWF S x (Env.letIn Γ C) [] 0 0 (by omega) hh⟩

theorem letInFv (Γ : Env) (C : Constraint) : (Γ.letIn C).fv = Γ.fv ∪ C.fv := by
  induction Γ with
  | nil => simp [Env.letIn, Env.fv]
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      have hs : s.exists_.fv ⊆ s.fv := schemeExistsFv s
      change (Constraint.letName x s (Env.letIn Γ C)).fv = _
      simp only [Constraint.letName, Constraint.define, Constraint.fv, Constraint.closeId,
        constraintMapIdsFv, ih, envFvCons]
      rw [← Finset.union_assoc, Finset.union_eq_right.mpr hs, Finset.union_assoc]

theorem letInFpi (Γ : Env) (C : Constraint) (hf : Γ.fpi = ∅) :
    (Γ.letIn C).fpi = C.fpi \ Γ.dpi := by
  induction Γ with
  | nil => simp [Env.letIn, Env.dpi]
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      have hh : s.fpi = ∅ ∧ Env.fpi Γ = ∅ := by simpa only [envFpiCons, Finset.union_eq_empty] using hf
      change (Constraint.letName x s (Env.letIn Γ C)).fpi = _
      simp only [Constraint.letName, Constraint.define, Constraint.fpi, Constraint.closeId,
        constraintCloseIdFpi, schemeExistsFpi, hh.1, Finset.empty_union, ih hh.2]
      ext y
      simp [Env.dpi, Finset.mem_sdiff, Finset.mem_erase]
      tauto

end HMX.LN.Proofs
