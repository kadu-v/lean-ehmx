import HMX.LocallyNameless.Proofs.Semantics

namespace HMX.LN.Proofs

theorem blockPermutationBound (ks ls : List Nat) (p : Nat → Nat)
    (h : BlockPermutation ks ls p) (i : Nat) : i < ks.length ↔ p i < ls.length := by
  have he : (ks[i]? = none) ↔ (ls[p i]? = none) := by rw [h.2.2.2 i]
  simp only [List.getElem?_eq_none_iff] at he
  omega

theorem blockPermutationInverse (ks ls : List Nat) (e : Nat ≃ Nat)
    (h : BlockPermutation ks ls e) : BlockPermutation ls ks e.symm := by
  have hlen := h.1
  refine ⟨h.1.symm, e.symm.bijective, ?_, ?_⟩
  · intro i hi
    apply e.injective
    simpa using (h.2.2.1 i (by omega)).symm
  · intro i
    simpa using (h.2.2.2 (e.symm i)).symm

/-- Permute the finite witness block while keeping the outer stack unchanged. -/
theorem permuteWitness (M : Model) (ks ls : List Nat) (e : Nat ≃ Nat)
    (h : BlockPermutation ks ls e) (vs : List M.Carrier)
    (hv : List.Forall₂ (fun v k => M.kind v = k) vs ks) (β : Nat → M.Carrier) :
    ∃ ws, List.Forall₂ (fun w k => M.kind w = k) ws ls ∧
      ∀ i, push vs β i = push ws β (e i) := by
  have hlen := h.1
  let ws := List.ofFn (fun j : Fin ls.length => push vs β (e.symm j))
  have hwlen : ws.length = ls.length := List.length_ofFn
  refine ⟨ws, ?_, ?_⟩
  · apply List.forall₂_iff_get.mpr
    refine ⟨hwlen, ?_⟩
    intro i hi hj
    simp only [List.get_eq_getElem, ws, List.getElem_ofFn]
    apply pushKinds M vs ks hv β (e.symm i) _
    rw [h.2.2.2, e.apply_symm_apply]
    exact List.getElem?_eq_getElem hj
  · intro i
    by_cases hi : i < ks.length
    · have he : e i < ls.length := (blockPermutationBound ks ls e h i).mp hi
      simp [push, ws, he]
    · have he : e i = i := h.2.2.1 i (by omega)
      have hi' : ¬ i < ls.length := by omega
      simp [push, ws, he, hi', hv.length_eq, h.1]

/-- Renaming below depth d corresponds to reindexing the evaluation stack. -/
theorem tyEvalRename (M : Model) (ρ : Assignment M) (β β' : Nat → M.Carrier)
    (p : Nat → Nat) (d : Nat) (T : Ty)
    (h : ∀ i, β i = β' (if i < d then i else d + p (i-d))) :
    (T.renameAt d p).evalAt M ρ β' = T.evalAt M ρ β := by
  induction T using tyInduction with
  | hf X => simp [Ty.renameAt, Ty.evalAt]
  | hb i => simpa [Ty.renameAt, Ty.evalAt] using (h i).symm
  | hc f ts ih =>
      simp only [Ty.renameAt, Ty.evalAt, List.map_map]
      congr 1
      exact List.map_congr_left (fun U hu => ih U hu)

/-- Entering another binder block shifts both the depth and the related stacks. -/
theorem pushRename (vs : List α) (β β' : Nat → α) (p : Nat → Nat) (d : Nat)
    (h : ∀ i, β i = β' (if i < d then i else d + p (i-d))) (i : Nat) :
    push vs β i = push vs β' (if i < d + vs.length then i else d + vs.length + p (i-(d+vs.length))) := by
  by_cases hi : i < vs.length
  · have hid : i < d + vs.length := by omega
    simp only [hid, ↓reduceIte, push]
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
  · have hn : vs[i]? = none := List.getElem?_eq_none (by omega)
    by_cases hid : i < d + vs.length
    · have hd : i-vs.length < d := by omega
      simpa [push, hid, hn, hd] using h (i-vs.length)
    · have hd : ¬ i-vs.length < d := by omega
      have hn' : vs[d+vs.length+p (i-(d+vs.length))]? = none :=
        List.getElem?_eq_none (by omega)
      have he : d+vs.length+p (i-(d+vs.length))-vs.length = d+p ((i-vs.length)-d) := by
        have ha : i-(d+vs.length) = i-vs.length-d := by omega
        rw [ha]
        omega
      simpa [push, hid, hn, hn', hd, he] using h (i-vs.length)

theorem constraintEvalRename (S : Signature) (M : Model) (ρ : Assignment M)
    (ι : GroundEnv M) (p : Nat → Nat) (C : Constraint) (d : Nat)
    (β β' : Nat → M.Carrier) (γ : Nat → Set M.Carrier)
    (h : ∀ i, β i = β' (if i < d then i else d + p (i-d))) :
    (C.mapTypes (fun n T => T.renameAt n p) d).holdsAt S M ρ ι β' γ ↔
      C.holdsAt S M ρ ι β γ := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d β β' γ,
      (∀ i, β i = β' (if i < d then i else d + p (i-d))) →
      ((C.mapTypes (fun n T => T.renameAt n p) d).holdsAt S M ρ ι β' γ ↔
        C.holdsAt S M ρ ι β γ))
    (motive_2 := fun s => ∀ d β β' γ,
      (∀ i, β i = β' (if i < d then i else d + p (i-d))) →
      (s.mapTypes (fun n T => T.renameAt n p) d).denoteAt S M ρ ι β' γ =
        s.denoteAt S M ρ ι β γ)
    (by intros; rfl) (by intros; rfl)
    (by
      intro q ts d β β' γ h
      simp only [Constraint.mapTypes, Constraint.holdsAt, List.map_map]
      have he := List.map_congr_left (fun T (_ : T ∈ ts) => tyEvalRename M ρ β β' p d T h)
      simpa only [Function.comp_def] using congrArg (fun xs => q.eval M xs) he |>.to_iff)
    (by intro C D ihC ihD d β β' γ h; exact and_congr (ihC d β β' γ h) (ihD d β β' γ h))
    (by
      intro ks C ih d β β' γ h
      simp only [Constraint.mapTypes, Constraint.holdsAt]
      apply exists_congr
      intro vs
      apply and_congr_right
      intro hvs
      apply ih (d+ks.length) _ _ γ
      simpa only [hvs.length_eq] using pushRename vs β β' p d h)
    (by
      intro b s C ihs ihC d β β' γ h
      simp only [Constraint.mapTypes, Constraint.holdsAt]
      rw [ihs d β β' γ h]
      exact ihC d β β' _ h)
    (by
      intro x T d β β' γ h
      cases x <;> simp only [Constraint.mapTypes, Constraint.holdsAt] <;>
        rw [tyEvalRename M ρ β β' p d T h])
    (by
      intro ks C T ih d β β' γ h
      ext v
      simp only [Scheme.mapTypes, Scheme.denoteAt, Set.mem_ofPred_eq]
      apply and_congr Iff.rfl
      apply exists_congr
      intro vs
      apply and_congr_right
      intro hvs
      have hp : ∀ i, push vs β i = push vs β' (if i < d+ks.length then i else d+ks.length+p (i-(d+ks.length))) := by
        simpa only [hvs.length_eq] using pushRename vs β β' p d h
      rw [tyEvalRename M ρ _ _ p (d+ks.length) T hp]
      exact and_congr (ih (d+ks.length) _ _ γ hp) Iff.rfl) C d β β' γ h

/-- A type block may be reordered even in raw syntax; outer indices are fixed. -/
theorem existsPermutation (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (ks ls : List Nat) (p : Nat → Nat) (hp : BlockPermutation ks ls p) (C : Constraint)
    (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) :
    (Constraint.exists_ ks C).holdsAt S M ρ ι β γ ↔
      (Constraint.exists_ ls (C.mapTypes (fun d T => T.renameAt d p) 0)).holdsAt S M ρ ι β γ := by
  classical
  let e : Nat ≃ Nat := Equiv.ofBijective p hp.2.1
  have he : BlockPermutation ks ls e := hp
  constructor
  · rintro ⟨vs, hv, hC⟩
    obtain ⟨ws, hw, hh⟩ := permuteWitness M ks ls e he vs hv β
    refine ⟨ws, hw, ?_⟩
    apply (constraintEvalRename S M ρ ι p C 0 _ _ γ (by simpa [e] using hh)).mpr hC
  · rintro ⟨ws, hw, hC⟩
    obtain ⟨vs, hv, hh⟩ := permuteWitness M ls ks e.symm (blockPermutationInverse ks ls e he) ws hw β
    refine ⟨vs, hv, ?_⟩
    apply (constraintEvalRename S M ρ ι p C 0 _ _ γ ?_).mp hC
    intro i
    simpa [e] using (hh (e i)).symm

theorem allPermutation (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (ks ls : List Nat) (p : Nat → Nat) (hp : BlockPermutation ks ls p) (C : Constraint) (T : Ty)
    (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) :
    (Scheme.all ks C T).denoteAt S M ρ ι β γ =
      (Scheme.all ls (C.mapTypes (fun d T => T.renameAt d p) 0) (T.renameAt 0 p)).denoteAt S M ρ ι β γ := by
  classical
  let e : Nat ≃ Nat := Equiv.ofBijective p hp.2.1
  have he : BlockPermutation ks ls e := hp
  ext v
  constructor
  · rintro ⟨hk, vs, hv, hC, hT⟩
    obtain ⟨ws, hw, hh⟩ := permuteWitness M ks ls e he vs hv β
    have hr : ∀ i, push vs β i = push ws β (if i < 0 then i else 0+p (i-0)) := by simpa [e] using hh
    refine ⟨hk, ws, hw, (constraintEvalRename S M ρ ι p C 0 _ _ γ hr).mpr hC, ?_⟩
    simpa only [tyEvalRename M ρ _ _ p 0 T hr] using hT
  · rintro ⟨hk, ws, hw, hC, hT⟩
    obtain ⟨vs, hv, hh⟩ := permuteWitness M ls ks e.symm (blockPermutationInverse ks ls e he) ws hw β
    have hr : ∀ i, push vs β i = push ws β (if i < 0 then i else 0+p (i-0)) := by
      intro i
      simpa [e] using (hh (e i)).symm
    refine ⟨hk, vs, hv, (constraintEvalRename S M ρ ι p C 0 _ _ γ hr).mp hC, ?_⟩
    simpa only [tyEvalRename M ρ _ _ p 0 T hr] using hT

/-- Raw semantics avoids needing WF hypotheses at intermediate transitivity steps. -/
theorem constraintBinderEq (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (C D : Constraint) (h : C.BinderEq D) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) :
    C.holdsAt S M ρ ι β γ ↔ D.holdsAt S M ρ ι β γ := by
  apply Constraint.BinderEq.rec
    (motive_1 := fun C D _ => ∀ β γ, C.holdsAt S M ρ ι β γ ↔ D.holdsAt S M ρ ι β γ)
    (motive_2 := fun s r _ => ∀ β γ, s.denoteAt S M ρ ι β γ = r.denoteAt S M ρ ι β γ)
    (by intros; rfl)
    (by intro C D h ih β γ; exact (ih β γ).symm)
    (by intro C D E h₁ h₂ ih₁ ih₂ β γ; exact (ih₁ β γ).trans (ih₂ β γ))
    (by intro C C' D D' h₁ h₂ ih₁ ih₂ β γ; exact and_congr (ih₁ β γ) (ih₂ β γ))
    (by
      intro ks ls p D C hp h ih β γ
      apply (existsPermutation S M ρ ι ks ls p hp C β γ).trans
      exact exists_congr (fun vs => and_congr Iff.rfl (ih (push vs β) γ)))
    (by
      intro s r C D b hs hC ihs ihC β γ
      simp only [Constraint.holdsAt]
      rw [ihs β γ]
      exact ihC β _)
    (by intros; rfl)
    (by intro s r h ih β γ; exact (ih β γ).symm)
    (by intro s r u h₁ h₂ ih₁ ih₂ β γ; exact (ih₁ β γ).trans (ih₂ β γ))
    (by
      intro ks ls p D U C T hp hC hT ih β γ
      apply (allPermutation S M ρ ι ks ls p hp C T β γ).trans
      rw [hT]
      ext v
      simp only [Scheme.denoteAt, Set.mem_ofPred_eq]
      exact and_congr Iff.rfl (exists_congr (fun vs => and_congr Iff.rfl
        (and_congr (ih (push vs β) γ) Iff.rfl)))) h β γ

theorem schemeBinderEq (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (s r : Scheme) (h : s.BinderEq r) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) :
    s.denoteAt S M ρ ι β γ = r.denoteAt S M ρ ι β γ := by
  apply Scheme.BinderEq.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun s r _ => ∀ β γ, s.denoteAt S M ρ ι β γ = r.denoteAt S M ρ ι β γ)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; rfl)
    (by intro s r h ih β γ; exact (ih β γ).symm)
    (by intro s r u h₁ h₂ ih₁ ih₂ β γ; exact (ih₁ β γ).trans (ih₂ β γ))
    (by
      intro ks ls p D U C T hp hC hT _ β γ
      apply (allPermutation S M ρ ι ks ls p hp C T β γ).trans
      rw [hT]
      ext v
      simp only [Scheme.denoteAt, Set.mem_ofPred_eq]
      exact and_congr Iff.rfl (exists_congr (fun vs => and_congr Iff.rfl
        (and_congr (constraintBinderEq S M ρ ι _ _ hC (push vs β) γ) Iff.rfl)))) h β γ

theorem binderPermutationSemantics (S : Signature) (M : Model) : HMX.LN.binderPermutationSemantics S M := by
  intro _
  constructor
  · intro C D _ _ h
    exact ⟨fun ρ ι _ _ hc => (constraintBinderEq S M ρ ι C D h _ _).mp hc,
      fun ρ ι _ _ hd => (constraintBinderEq S M ρ ι C D h _ _).mpr hd⟩
  · intro s r ρ ι _ _ h _ _
    exact schemeBinderEq S M ρ ι s r h _ _

end HMX.LN.Proofs
