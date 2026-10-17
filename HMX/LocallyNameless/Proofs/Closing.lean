import HMX.LocallyNameless.Proofs.Permutations

namespace HMX.LN.Proofs

/-- Closing uses the first occurrence of a name, including in duplicate blocks. -/
def assignBlock (xs : List TVar) (vs : List M.Carrier) (ρ : Assignment M) : Assignment M :=
  fun X => if X ∈ xs then (vs[xs.idxOf X]?).getD (ρ X) else ρ X

theorem pushNil (β : Nat → α) : push [] β = β := by
  funext i
  simp [push]

theorem pushBelow (vs : List α) (β : Nat → α) (i : Nat) (hi : i < vs.length) :
    push vs β i = vs[i] := by simp [push, List.getElem?_eq_getElem hi]

theorem pushAbove (vs : List α) (β : Nat → α) (i : Nat) (hi : vs.length ≤ i) :
    push vs β i = β (i-vs.length) := by simp [push, List.getElem?_eq_none hi]

theorem pushAppend (vs ws : List α) (β : Nat → α) : push (vs ++ ws) β = push vs (push ws β) := by
  funext i
  by_cases hi : i < vs.length
  · simp [push, List.getElem?_append, hi]
  · simp [push, List.getElem?_append, hi, Nat.sub_sub]

theorem tyEvalClose (M : Model) (ρ : Assignment M) (xs : List TVar) (vs pre : List M.Carrier)
    (hlen : vs.length = xs.length) (β : Nat → M.Carrier) (T : Ty) :
    (T.closeAt pre.length xs).evalAt M ρ (push pre (push vs β)) =
      T.evalAt M (assignBlock xs vs ρ) (push pre β) := by
  induction T using tyInduction with
  | hf X =>
      by_cases hx : X ∈ xs
      · have hi : xs.idxOf X < vs.length := by simpa [hlen] using List.idxOf_lt_length_iff.mpr hx
        simp only [Ty.closeAt, hx, ↓reduceIte, Ty.evalAt, assignBlock]
        rw [pushAbove pre _ _ (by omega)]
        simp [push, List.getElem?_eq_getElem hi]
      · simp [Ty.closeAt, hx, Ty.evalAt, assignBlock]
  | hb i =>
      by_cases hi : i < pre.length
      · simp [Ty.closeAt, Ty.evalAt, hi, pushBelow pre _ i hi]
      · have hpre : pre.length ≤ i := by omega
        simp only [Ty.closeAt, hi, ↓reduceIte, Ty.evalAt]
        rw [pushAbove pre _ _ (by omega), pushAbove vs _ _ (by omega), pushAbove pre _ _ hpre]
        congr 1
        omega
  | hc f ts ih =>
      simp only [Ty.closeAt, Ty.evalAt, List.map_map]
      congr 1
      exact List.map_congr_left (fun U hu => ih U hu)

theorem constraintEvalClose (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (xs : List TVar) (vs : List M.Carrier) (hlen : vs.length = xs.length)
    (C : Constraint) (pre : List M.Carrier) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) :
    (C.mapTypes (fun d T => T.closeAt d xs) pre.length).holdsAt S M ρ ι (push pre (push vs β)) γ ↔
      C.holdsAt S M (assignBlock xs vs ρ) ι (push pre β) γ := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ pre β γ,
      (C.mapTypes (fun d T => T.closeAt d xs) pre.length).holdsAt S M ρ ι (push pre (push vs β)) γ ↔
        C.holdsAt S M (assignBlock xs vs ρ) ι (push pre β) γ)
    (motive_2 := fun s => ∀ pre β γ,
      (s.mapTypes (fun d T => T.closeAt d xs) pre.length).denoteAt S M ρ ι (push pre (push vs β)) γ =
        s.denoteAt S M (assignBlock xs vs ρ) ι (push pre β) γ)
    (by intros; rfl) (by intros; rfl)
    (by
      intro p ts pre β γ
      simp only [Constraint.mapTypes, Constraint.holdsAt, List.map_map]
      have he := List.map_congr_left (fun T (_ : T ∈ ts) => tyEvalClose M ρ xs vs pre hlen β T)
      simpa only [Function.comp_def] using congrArg (fun ts => p.eval M ts) he |>.to_iff)
    (by intro C D ihC ihD pre β γ; exact and_congr (ihC pre β γ) (ihD pre β γ))
    (by
      intro ks C ih pre β γ
      simp only [Constraint.mapTypes, Constraint.holdsAt]
      apply exists_congr
      intro ws
      apply and_congr_right
      intro hw
      simpa [List.length_append, hw.length_eq, Nat.add_comm, pushAppend] using ih (ws ++ pre) β γ)
    (by
      intro b s C ihs ihC pre β γ
      simp only [Constraint.mapTypes, Constraint.holdsAt]
      rw [ihs pre β γ]
      exact ihC pre β _)
    (by intro x T pre β γ; cases x <;> simp only [Constraint.mapTypes, Constraint.holdsAt] <;> rw [tyEvalClose M ρ xs vs pre hlen β T])
    (by
      intro ks C T ih pre β γ
      ext v
      simp only [Scheme.mapTypes, Scheme.denoteAt, Set.mem_ofPred_eq]
      apply and_congr Iff.rfl
      apply exists_congr
      intro ws
      apply and_congr_right
      intro hw
      have ht := tyEvalClose M ρ xs vs (ws ++ pre) hlen β T
      simp only [List.length_append, hw.length_eq, pushAppend] at ht
      rw [Nat.add_comm ks.length pre.length] at ht
      rw [ht]
      apply and_congr _ Iff.rfl
      simpa [List.length_append, hw.length_eq, Nat.add_comm, pushAppend] using ih (ws ++ pre) β γ) C pre β γ

def updateEnv (ι : GroundEnv M) (x : Id) (A : Set M.Carrier) : GroundEnv M :=
  fun y => if y = x then A else ι y

theorem constraintEvalCloseId (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (x : Id) (A : Set M.Carrier) (C : Constraint) (pre : List (Set M.Carrier))
    (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) :
    (C.mapIds (fun d v => v.closeAt d x) pre.length).holdsAt S M ρ ι β (push pre (push [A] γ)) ↔
      C.holdsAt S M ρ (updateEnv ι x A) β (push pre γ) := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ pre β γ,
      (C.mapIds (fun d v => v.closeAt d x) pre.length).holdsAt S M ρ ι β (push pre (push [A] γ)) ↔
        C.holdsAt S M ρ (updateEnv ι x A) β (push pre γ))
    (motive_2 := fun s => ∀ pre β γ,
      (s.mapIds (fun d v => v.closeAt d x) pre.length).denoteAt S M ρ ι β (push pre (push [A] γ)) =
        s.denoteAt S M ρ (updateEnv ι x A) β (push pre γ))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by intro C D ihC ihD pre β γ; exact and_congr (ihC pre β γ) (ihD pre β γ))
    (by
      intro ks C ih pre β γ
      exact exists_congr (fun vs => and_congr Iff.rfl (ih pre (push vs β) γ)))
    (by
      intro b s C ihs ihC pre β γ
      simp only [Constraint.mapIds, Constraint.holdsAt]
      rw [ihs pre β γ]
      simpa only [List.length_append, List.length_singleton, Nat.add_comm, pushAppend] using ihC ([s.denoteAt S M ρ (updateEnv ι x A) β (push pre γ)] ++ pre) β γ)
    (by
      intro v T pre β γ
      cases v with
      | free y =>
          by_cases hy : y = x
          · simp [Constraint.mapIds, PVar.closeAt, hy, Constraint.holdsAt, updateEnv, push]
          · simp [Constraint.mapIds, PVar.closeAt, hy, Constraint.holdsAt, updateEnv]
      | bound i =>
          by_cases hi : i < pre.length
          · simp [Constraint.mapIds, PVar.closeAt, hi, Constraint.holdsAt, pushBelow pre _ i hi]
          · simp only [Constraint.mapIds, PVar.closeAt, hi, ↓reduceIte, Constraint.holdsAt]
            rw [pushAbove pre _ _ (by omega), pushAbove [A] _ _ (by simp; omega), pushAbove pre _ _ (by omega)]
            have he : i+1-pre.length-[A].length = i-pre.length := by simp; omega
            rw [he])
    (by
      intro ks C T ih pre β γ
      ext v
      simp only [Scheme.mapIds, Scheme.denoteAt, Set.mem_ofPred_eq]
      exact and_congr Iff.rfl (exists_congr (fun vs => and_congr Iff.rfl
        (and_congr (ih pre (push vs β) γ) Iff.rfl)))) C pre β γ

theorem holdsClosed (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (C : Constraint) (hC : C.WF S [] 0) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) :
    C.holdsAt S M ρ ι β γ ↔ C.Holds S M ρ ι :=
  constraintStacks S M ρ ι C [] 0 hC _ _ _ _ (by simp) (by simp)

theorem denoteClosed (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (s : Scheme) (hs : s.WF S [] 0) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) :
    s.denoteAt S M ρ ι β γ = s.denote S M ρ ι := by
  cases s with
  | all ks C T =>
      simp only [Scheme.WF, List.append_nil] at hs
      ext v
      simp only [Scheme.denoteAt, Scheme.denote, Set.mem_ofPred_eq]
      apply and_congr Iff.rfl
      apply exists_congr
      intro vs
      apply and_congr_right
      intro hvs
      have hp : ∀ i, i < ks.length → push vs β i = push vs (fun _ => ρ (0,0)) i := by
        intro i hi
        apply pushAgreement vs _ _ 0 (by simp) i
        simpa [hvs.length_eq] using hi
      rw [tyEvalStacks M ρ _ _ T ks.length (tyKindLC T S ks 0 hs.2.2) hp]
      exact and_congr (constraintStacks S M ρ ι C ks 0 hs.2.1 _ _ _ _ hp (by simp)) Iff.rfl

theorem assignBlockValid (S : Signature) (M : Model) (ρ : Assignment M) (xs : List TVar)
    (vs : List M.Carrier) (hρ : ρ.Valid S M)
    (hv : List.Forall₂ (fun v X => M.kind v = X.1) vs xs) : (assignBlock xs vs ρ).Valid S M := by
  intro X hx
  by_cases hm : X ∈ xs
  · obtain ⟨v, hget, hk⟩ := forall₂Lookup hv (xs.idxOf X) X (List.getElem?_idxOf hm)
    simpa [assignBlock, hm, hget] using hk
  · simpa [assignBlock, hm] using hρ X hx

theorem freeBlockKinds (S : Signature) (xs : List TVar) (h : ∀ X ∈ xs, X.1 ∈ S.kinds) :
    List.Forall₂ (Ty.HasKind S []) (xs.map Ty.free) (xs.map Prod.fst) := by
  induction xs with
  | nil => exact .nil
  | cons X xs ih => exact .cons (.free (h X (by simp))) (ih (fun X hx => h X (by simp [hx])))

theorem closeTypesWFReflect (S : Signature) (xs : List TVar) (C : Constraint)
    (hx : ∀ X ∈ xs, X.1 ∈ S.kinds) (hc : (C.closeTypes xs).WF S (xs.map Prod.fst) 0) : C.WF S [] 0 := by
  have h := typeOpeningWF S (xs.map Prod.fst) (xs.map Ty.free) (C.closeTypes xs) hc (freeBlockKinds S xs hx)
  have he : (C.closeTypes xs).openTypes (xs.map Ty.free) = C :=
    constraintMapTypesInverse _ _ (fun d T => tyOpenClose T d xs) C 0
  exact he ▸ h

theorem closeTyKindReflect (S : Signature) (xs : List TVar) (T : Ty) (k : Nat)
    (hx : ∀ X ∈ xs, X.1 ∈ S.kinds) (ht : (T.closeAt 0 xs).HasKind S (xs.map Prod.fst) k) : T.HasKind S [] k := by
  have h := tyOpenKind S (T.closeAt 0 xs) (xs.map Prod.fst) [] (xs.map Ty.free) (freeBlockKinds S xs hx) k ht
  simpa only [List.length_nil, tyOpenClose] using h

theorem closeIdWFReflect (S : Signature) (x : Id) (C : Constraint) (ks : List Nat) (n d : Nat)
    (hn : n ≤ d) (hc : (C.mapIds (fun n v => v.closeAt n x) n).WF S ks (d+1)) : C.WF S ks d := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ ks n d, n ≤ d → (C.mapIds (fun n v => v.closeAt n x) n).WF S ks (d+1) → C.WF S ks d)
    (motive_2 := fun s => ∀ ks n d, n ≤ d → (s.mapIds (fun n v => v.closeAt n x) n).WF S ks (d+1) → s.WF S ks d)
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
          · exact ⟨hc.1, trivial⟩
          · exact ⟨hc.1, trivial⟩
      | bound i =>
          refine ⟨hc.1, ?_⟩
          have hi := hc.2
          simp only [PVar.closeAt] at hi
          split at hi <;> omega)
    (by intro bs C T ih ks n d hn hs; exact ⟨hs.1, ih (bs ++ ks) n d hn hs.2.1, hs.2.2⟩) C ks n d hn hc

theorem existsNamesWFReflect (S : Signature) (xs : List TVar) (C : Constraint)
    (h : (C.existsNames xs).WF S [] 0) : (∀ X ∈ xs, X.1 ∈ S.kinds) ∧ C.WF S [] 0 := by
  have hx : ∀ X ∈ xs, X.1 ∈ S.kinds := fun X hX => h.1 X.1 (List.mem_map.mpr ⟨X, hX, rfl⟩)
  exact ⟨hx, closeTypesWFReflect S xs C hx (by simpa using h.2)⟩

theorem generalizeWFReflect (S : Signature) (xs : List TVar) (C : Constraint) (T : Ty)
    (h : (Scheme.generalize xs C T).WF S [] 0) :
    (∀ X ∈ xs, X.1 ∈ S.kinds) ∧ C.WF S [] 0 ∧ T.HasKind S [] 0 := by
  have hx : ∀ X ∈ xs, X.1 ∈ S.kinds := fun X hX => h.1 X.1 (List.mem_map.mpr ⟨X, hX, rfl⟩)
  exact ⟨hx, closeTypesWFReflect S xs C hx (by simpa using h.2.1), closeTyKindReflect S xs T 0 hx (by simpa using h.2.2)⟩

theorem defineWFReflect (S : Signature) (x : Id) (s : Scheme) (C : Constraint)
    (h : (C.define x s).WF S [] 0) : s.WF S [] 0 ∧ C.WF S [] 0 :=
  ⟨h.1, closeIdWFReflect S x C [] 0 0 (Nat.le_refl _) h.2⟩

theorem existsNamesHolds (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (xs : List TVar) (C : Constraint) (hc : C.WF S [] 0) :
    (C.existsNames xs).Holds S M ρ ι ↔ ∃ vs,
      List.Forall₂ (fun v X => M.kind v = X.1) vs xs ∧ C.Holds S M (assignBlock xs vs ρ) ι := by
  simp only [Constraint.existsNames, Constraint.Holds, Constraint.holdsAt]
  apply exists_congr
  intro vs
  rw [List.forall₂_map_right_iff]
  apply and_congr_right
  intro hv
  have he := constraintEvalClose S M ρ ι xs vs hv.length_eq C [] (fun _ => ρ (0,0)) (fun _ => ∅)
  simp only [List.length_nil, pushNil] at he
  exact he.trans (holdsClosed S M _ ι C hc _ _)

theorem generalizeDenote (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (xs : List TVar) (C : Constraint) (T : Ty) (hc : C.WF S [] 0) (ht : T.HasKind S [] 0) (v : M.Carrier) :
    v ∈ (Scheme.generalize xs C T).denote S M ρ ι ↔ M.kind v = 0 ∧ ∃ vs,
      List.Forall₂ (fun w X => M.kind w = X.1) vs xs ∧
      C.Holds S M (assignBlock xs vs ρ) ι ∧ M.below 0 (T.eval M (assignBlock xs vs ρ)) v := by
  simp only [Scheme.generalize, Scheme.denote, Scheme.denoteAt, Set.mem_ofPred_eq]
  apply and_congr Iff.rfl
  apply exists_congr
  intro vs
  rw [List.forall₂_map_right_iff]
  apply and_congr_right
  intro hv
  have he := constraintEvalClose S M ρ ι xs vs hv.length_eq C [] (fun _ => ρ (0,0)) (fun _ => ∅)
  have hT := tyEvalClose M ρ xs vs [] hv.length_eq (fun _ => ρ (0,0)) T
  simp only [List.length_nil, pushNil] at he hT
  rw [hT, tyEvalStacks M _ _ _ T 0 (tyKindLC T S [] 0 ht) (by simp)]
  exact and_congr (he.trans (holdsClosed S M _ ι C hc _ _)) Iff.rfl

theorem defineHolds (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (x : Id) (s : Scheme) (C : Constraint) :
    (C.define x s).Holds S M ρ ι ↔ C.Holds S M ρ (updateEnv ι x (s.denote S M ρ ι)) := by
  have he := constraintEvalCloseId S M ρ ι x (s.denote S M ρ ι) C [] (fun _ => ρ (0,0)) (fun _ => ∅)
  simpa [Constraint.define, Constraint.Holds, Constraint.holdsAt, Constraint.closeId, Scheme.denote, pushNil] using he

theorem letNameHolds (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (x : Id) (s : Scheme) (C : Constraint) :
    (C.letName x s).Holds S M ρ ι ↔ s.exists_.Holds S M ρ ι ∧ C.Holds S M ρ (updateEnv ι x (s.denote S M ρ ι)) :=
  and_congr Iff.rfl (defineHolds S M ρ ι x s C)

theorem assignBlockSelf (ρ : Assignment M) (xs : List TVar) : assignBlock xs (xs.map ρ) ρ = ρ := by
  funext X
  by_cases hx : X ∈ xs
  · simp [assignBlock, hx, List.getElem?_map, List.getElem?_idxOf hx]
  · simp [assignBlock, hx]

theorem assignmentBlockKinds (S : Signature) (M : Model) (ρ : Assignment M) (xs : List TVar)
    (hρ : ρ.Valid S M) (hx : ∀ X ∈ xs, X.1 ∈ S.kinds) :
    List.Forall₂ (fun v X => M.kind v = X.1) (xs.map ρ) xs := by
  apply List.forall₂_map_left_iff.mpr
  exact List.forall₂_same.mpr (fun X hX => hρ X (hx X hX))

theorem assignBlockOutside (ρ : Assignment M) (xs : List TVar) (vs : List M.Carrier) (X : TVar)
    (hx : X ∉ xs) : assignBlock xs vs ρ X = ρ X := by simp [assignBlock, hx]

theorem holdsAssignBlock (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (ι : GroundEnv M) (xs : List TVar) (vs : List M.Carrier) (C : Constraint)
    (hρ : ρ.Valid S M) (hι : ι.Valid M) (hv : List.Forall₂ (fun v X => M.kind v = X.1) vs xs)
    (hc : C.WF S [] 0) (hf : Disjoint xs.toFinset C.fv) :
    C.Holds S M (assignBlock xs vs ρ) ι ↔ C.Holds S M ρ ι := by
  apply (semanticLocality S M hM _ ρ ι ι (assignBlockValid S M ρ xs vs hρ hv) hρ hι hι).1 C hc
  · intro X hX
    apply assignBlockOutside
    intro hm
    exact Finset.disjoint_left.mp hf (by simpa using hm) hX
  · intros; rfl

theorem tyEvalAssignBlock (M : Model) (ρ : Assignment M) (xs : List TVar) (vs : List M.Carrier)
    (T : Ty) (ht : T.LCAt 0) (hf : Disjoint xs.toFinset T.fv) :
    T.eval M (assignBlock xs vs ρ) = T.eval M ρ := by
  apply (tyEvalLocality M _ ρ _ T ?_).trans
  · exact tyEvalStacks M ρ _ _ T 0 ht (by simp)
  · intro X hX
    apply assignBlockOutside
    intro hm
    exact Finset.disjoint_left.mp hf (by simpa using hm) hX

theorem tyKindDeclared (S : Signature) (hS : S.Valid) (T : Ty) (ks : List Nat) (k : Nat)
    (ht : T.HasKind S ks k) : k ∈ S.kinds := by
  cases ht with
  | free hx => exact hx
  | bound _ hk => exact hk
  | con hf _ => exact (hS.2.2.2.2.2.1 _ hf).1

theorem evalKind (S : Signature) (M : Model) (hM : M.Requirements S) (ρ : Assignment M)
    (hρ : ρ.Valid S M) (T : Ty) (k : Nat) (ht : T.HasKind S [] k) : M.kind (T.eval M ρ) = k :=
  evaluationKind S M hM ρ _ [] T k hρ (by simp) ht

theorem leHolds (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M) (k : Nat) (T U : Ty) :
    (Constraint.le k T U).Holds S M ρ ι ↔
      M.kind (T.eval M ρ) = k ∧ M.kind (U.eval M ρ) = k ∧ M.below k (T.eval M ρ) (U.eval M ρ) := by
  simp [Constraint.le, Constraint.Holds, Constraint.holdsAt, Predicate.eval, Ty.eval]

theorem eqHolds (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M) (k : Nat) (T U : Ty) :
    (Constraint.eq k T U).Holds S M ρ ι ↔
      M.kind (T.eval M ρ) = k ∧ M.kind (U.eval M ρ) = k ∧ T.eval M ρ = U.eval M ρ := by
  simp [Constraint.eq, Constraint.Holds, Constraint.holdsAt, Predicate.eval, Ty.eval]

theorem letNameWFReflect (S : Signature) (x : Id) (s : Scheme) (C : Constraint)
    (h : (C.letName x s).WF S [] 0) : s.WF S [] 0 ∧ C.WF S [] 0 :=
  defineWFReflect S x s C h.2

theorem monoWF (S : Signature) (T : Ty) (ht : T.HasKind S [] 0) : (Scheme.mono T).WF S [] 0 :=
  ⟨by simp, trivial, ht⟩

theorem monoExists (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M) (T : Ty) :
    (Scheme.mono T).exists_.Holds S M ρ ι := ⟨[], .nil, trivial⟩

theorem monoDenote (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M) (T : Ty) (v : M.Carrier) :
    v ∈ (Scheme.mono T).denote S M ρ ι ↔ M.kind v = 0 ∧ M.below 0 (T.eval M ρ) v := by
  simp [Scheme.mono, Scheme.denote, Scheme.denoteAt, Constraint.holdsAt, List.forall₂_nil_right_iff, pushNil, Ty.eval]

theorem schemeExistsNonempty (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (ι : GroundEnv M) (hρ : ρ.Valid S M) (s : Scheme) (hs : s.WF S [] 0) :
    s.exists_.Holds S M ρ ι ↔ (s.denote S M ρ ι).Nonempty := by
  cases s with
  | all ks C T =>
      simp only [Scheme.WF, List.append_nil] at hs
      constructor
      · rintro ⟨vs, hv, hc⟩
        let v := T.evalAt M ρ (push vs (fun _ => ρ (0,0)))
        have hk : M.kind v = 0 := evaluationKind S M hM ρ _ ks T 0 hρ (pushKinds M vs ks hv _) hs.2.2
        exact ⟨v, hk, vs, hv, hc, hM.2.2.2.1 0 hM.1.1 v hk⟩
      · rintro ⟨v, _, vs, hv, hc, _⟩
        exact ⟨vs, hv, hc⟩

end HMX.LN.Proofs
