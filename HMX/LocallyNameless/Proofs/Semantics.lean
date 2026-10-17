import HMX.LocallyNameless.Proofs.Substitution

namespace HMX.LN.Proofs

theorem evaluationKind (S : Signature) (M : Model) : HMX.LN.evaluationKind S M := by
  intro hM ρ β ks T k hρ hβ hT
  induction T using tyInduction generalizing k with
  | hf X => simp only [Ty.evalAt]; cases hT with | free hx => exact hρ X hx
  | hb i => simp only [Ty.evalAt]; cases hT with | bound hi _ => exact hβ i _ hi
  | hc f ts ih =>
      cases hT with
      | con hf hs =>
          simp only [Ty.evalAt]
          apply hM.2.2.1 f hf
          exact List.forall₂_map_left_iff.mpr (forall₂ImplMem hs (fun U hu p hp => ih U hu _ hp))

theorem pushKinds (M : Model) (vs : List M.Carrier) (ks : List Nat)
    (h : List.Forall₂ (fun v k => M.kind v = k) vs ks) (β : Nat → M.Carrier)
    (i k : Nat) (hi : ks[i]? = some k) : M.kind (push vs β i) = k := by
  obtain ⟨v, hv, hk⟩ := forall₂Lookup h i k hi
  simpa [push, hv] using hk

theorem schemeDenotationValid (S : Signature) (M : Model) : HMX.LN.schemeDenotationValid S M := by
  intro hM ρ ι s x hρ hι hs y
  by_cases hy : y = x
  · subst y
    simp only [↓reduceIte]
    cases s with
    | all ks C T =>
        simp only [Scheme.WF, List.append_nil] at hs
        constructor
        · intro a ha; exact ha.1
        · intro a b ha hb hab
          rcases ha with ⟨ha, vs, hvs, hC, hTa⟩
          refine ⟨hb, vs, hvs, hC, ?_⟩
          apply hM.2.2.2.2.1 0 hM.1.1 _ a b _ ha hb hTa hab
          exact evaluationKind S M hM ρ (push vs (fun _ => ρ (0,0))) ks T 0 hρ
            (pushKinds M vs ks hvs _) hs.2.2
  · simpa only [hy, ↓reduceIte] using hι y

theorem fvListMember (ts : List Ty) (T : Ty) (hT : T ∈ ts) :
    T.fv ⊆ (ts.map Ty.fv).foldr (· ∪ ·) ∅ := by
  induction ts with
  | nil => simp at hT
  | cons U us ih =>
      rcases List.mem_cons.mp hT with rfl | hT
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih hT) Finset.subset_union_right

theorem tyEvalLocality (M : Model) (ρ ρ' : Assignment M) (β : Nat → M.Carrier)
    (T : Ty) (h : ∀ X ∈ T.fv, ρ X = ρ' X) : T.evalAt M ρ β = T.evalAt M ρ' β := by
  induction T using tyInduction with
  | hf X => simp only [Ty.evalAt]; exact h X (by simp [Ty.fv])
  | hb i => simp [Ty.evalAt]
  | hc f ts ih =>
      simp only [Ty.fv] at h
      simp only [Ty.evalAt]
      congr 1
      exact List.map_congr_left (fun U hU => ih U hU (fun X hX => h X (fvListMember ts U hU hX)))

/-- Locality holds on raw syntax when the bound stacks are kept equal. -/
theorem constraintLocality (S : Signature) (M : Model) (ρ ρ' : Assignment M)
    (ι ι' : GroundEnv M) (C : Constraint) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier)
    (hρ : ∀ X ∈ C.fv, ρ X = ρ' X) (hι : ∀ x ∈ C.fpi, ι x = ι' x) :
    C.holdsAt S M ρ ι β γ ↔ C.holdsAt S M ρ' ι' β γ := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ β γ, (∀ X ∈ C.fv, ρ X = ρ' X) → (∀ x ∈ C.fpi, ι x = ι' x) →
      (C.holdsAt S M ρ ι β γ ↔ C.holdsAt S M ρ' ι' β γ))
    (motive_2 := fun s => ∀ β γ, (∀ X ∈ s.fv, ρ X = ρ' X) → (∀ x ∈ s.fpi, ι x = ι' x) →
      s.denoteAt S M ρ ι β γ = s.denoteAt S M ρ' ι' β γ)
    (by intros; rfl) (by intros; rfl)
    (by
      intro p ts β γ hρ _
      simp only [Constraint.holdsAt]
      have hts : ts.map (Ty.evalAt M ρ β) = ts.map (Ty.evalAt M ρ' β) :=
        List.map_congr_left (fun T hT => tyEvalLocality M ρ ρ' β T (fun X hX => hρ X (fvListMember ts T hT hX)))
      rw [hts])
    (by
      intro C D ihC ihD β γ hρ hι
      simp only [Constraint.fv, Constraint.fpi, Finset.mem_union, or_imp] at hρ hι
      exact and_congr (ihC β γ (fun X => (hρ X).1) (fun x => (hι x).1))
        (ihD β γ (fun X => (hρ X).2) (fun x => (hι x).2)))
    (by
      intro ks C ih β γ hρ hι
      simp only [Constraint.holdsAt]
      exact exists_congr (fun vs => and_congr Iff.rfl (ih (push vs β) γ hρ hι)))
    (by
      intro b s C ihs ihC β γ hρ hι
      simp only [Constraint.fv, Constraint.fpi, Finset.mem_union, or_imp] at hρ hι
      simp only [Constraint.holdsAt]
      rw [ihs β γ (fun X => (hρ X).1) (fun x => (hι x).1)]
      exact ihC β _ (fun X => (hρ X).2) (fun x => (hι x).2))
    (by
      intro x T β γ hρ hι
      cases x with
      | free x =>
          simp only [Constraint.holdsAt]
          rw [tyEvalLocality M ρ ρ' β T hρ, hι x (by simp [Constraint.fpi])]
      | bound i =>
          simp only [Constraint.holdsAt]
          rw [tyEvalLocality M ρ ρ' β T hρ])
    (by
      intro ks C T ih β γ hρ hι
      simp only [Scheme.fv, Finset.mem_union, or_imp] at hρ
      ext v
      simp only [Scheme.denoteAt, Set.mem_ofPred_eq]
      apply and_congr Iff.rfl
      apply exists_congr
      intro vs
      rw [tyEvalLocality M ρ ρ' (push vs β) T (fun X => (hρ X).2)]
      exact and_congr Iff.rfl (and_congr (ih (push vs β) γ (fun X => (hρ X).1) hι) Iff.rfl)) C β γ hρ hι

theorem pushAgreement {α : Type} (vs : List α) (σ σ' : Nat → α) (n : Nat)
    (h : ∀ i, i < n → σ i = σ' i) (i : Nat) (hi : i < vs.length + n) :
    push vs σ i = push vs σ' i := by
  unfold push
  cases hv : vs[i]? with
  | some v => rfl
  | none =>
      simp only [Option.getD_none]
      have hn : vs.length ≤ i := List.getElem?_eq_none_iff.mp hv
      exact h (i-vs.length) (by omega)

theorem tyEvalStacks (M : Model) (ρ : Assignment M) (β β' : Nat → M.Carrier)
    (T : Ty) (n : Nat) (h : T.LCAt n) (hβ : ∀ i, i < n → β i = β' i) :
    T.evalAt M ρ β = T.evalAt M ρ β' := by
  induction T using tyInduction with
  | hf X => simp [Ty.evalAt]
  | hb i => simp only [Ty.evalAt]; exact hβ i (by simpa [Ty.LCAt] using h)
  | hc f ts ih =>
      simp only [Ty.LCAt] at h
      simp only [Ty.evalAt]
      congr 1
      exact List.map_congr_left (fun U hu => ih U hu (h U hu))

theorem constraintStacks (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (C : Constraint) (ks : List Nat) (d : Nat) (hC : C.WF S ks d)
    (β β' : Nat → M.Carrier) (γ γ' : Nat → Set M.Carrier)
    (hβ : ∀ i, i < ks.length → β i = β' i) (hγ : ∀ i, i < d → γ i = γ' i) :
    C.holdsAt S M ρ ι β γ ↔ C.holdsAt S M ρ ι β' γ' := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ ks d, C.WF S ks d → ∀ β β' γ γ',
      (∀ i, i < ks.length → β i = β' i) → (∀ i, i < d → γ i = γ' i) →
      (C.holdsAt S M ρ ι β γ ↔ C.holdsAt S M ρ ι β' γ'))
    (motive_2 := fun s => ∀ ks d, s.WF S ks d → ∀ β β' γ γ',
      (∀ i, i < ks.length → β i = β' i) → (∀ i, i < d → γ i = γ' i) →
      s.denoteAt S M ρ ι β γ = s.denoteAt S M ρ ι β' γ')
    (by intros; rfl) (by intros; rfl)
    (by
      intro p ts ks d hc β β' γ γ' hβ _
      simp only [Constraint.holdsAt]
      have hts : ts.map (Ty.evalAt M ρ β) = ts.map (Ty.evalAt M ρ β') := by
        apply List.map_congr_left
        intro T hT
        obtain ⟨k, hk⟩ := forall₂Left hc.2 T hT
        exact tyEvalStacks M ρ β β' T ks.length (tyKindLC T S ks k hk) hβ
      rw [hts])
    (by
      intro C D ihC ihD ks d hc β β' γ γ' hβ hγ
      exact and_congr (ihC ks d hc.1 β β' γ γ' hβ hγ) (ihD ks d hc.2 β β' γ γ' hβ hγ))
    (by
      intro ns C ih ks d hc β β' γ γ' hβ hγ
      simp only [Constraint.holdsAt]
      apply exists_congr
      intro vs
      apply and_congr_right
      intro hvs
      apply ih (ns ++ ks) d hc.2 _ _ _ _ _ hγ
      intro i hi
      apply pushAgreement vs β β' ks.length hβ i
      simpa [List.length_append, hvs.length_eq] using hi)
    (by
      intro b s C ihs ihC ks d hc β β' γ γ' hβ hγ
      simp only [Constraint.holdsAt]
      rw [ihs ks d hc.1 β β' γ γ' hβ hγ]
      apply ihC ks (d+1) hc.2 _ _ _ _ hβ
      intro i hi
      exact pushAgreement _ γ γ' d hγ i (by simpa [Nat.add_comm] using hi))
    (by
      intro x T ks d hc β β' γ γ' hβ hγ
      cases x with
      | free x =>
          simp only [Constraint.holdsAt]
          rw [tyEvalStacks M ρ β β' T ks.length (tyKindLC T S ks 0 hc.1) hβ]
      | bound i =>
          simp only [Constraint.holdsAt]
          rw [tyEvalStacks M ρ β β' T ks.length (tyKindLC T S ks 0 hc.1) hβ, hγ i hc.2])
    (by
      intro ns C T ih ks d hs β β' γ γ' hβ hγ
      ext v
      simp only [Scheme.denoteAt, Set.mem_ofPred_eq]
      apply and_congr Iff.rfl
      apply exists_congr
      intro vs
      apply and_congr_right
      intro hvs
      have hp : ∀ i, i < (ns ++ ks).length → push vs β i = push vs β' i := by
        intro i hi
        apply pushAgreement vs β β' ks.length hβ i
        simpa [List.length_append, hvs.length_eq] using hi
      rw [tyEvalStacks M ρ (push vs β) (push vs β') T (ns ++ ks).length (tyKindLC T S (ns ++ ks) 0 hs.2.2) hp]
      exact and_congr (ih (ns ++ ks) d hs.2.1 _ _ _ _ hp hγ) Iff.rfl) C ks d hC β β' γ γ' hβ hγ

theorem semanticLocality (S : Signature) (M : Model) : HMX.LN.semanticLocality S M := by
  intro _ ρ ρ' ι ι' _ _ _ _
  constructor
  · intro C hC hρ hι
    unfold Constraint.Holds
    exact (constraintLocality S M ρ ρ' ι ι' C _ _ hρ hι).trans
      (constraintStacks S M ρ' ι' C [] 0 hC _ _ _ _ (by simp) (by simp))
  · intro s hs hρ hι
    cases s with
    | all ks C T =>
        simp only [Scheme.fv, Finset.mem_union, or_imp] at hρ
        simp only [Scheme.WF, List.append_nil] at hs
        ext v
        simp only [Scheme.denote, Scheme.denoteAt, Set.mem_ofPred_eq]
        apply and_congr Iff.rfl
        apply exists_congr
        intro vs
        apply and_congr_right
        intro hvs
        have hp : ∀ i, i < ks.length →
            push vs (fun _ => ρ (0,0)) i = push vs (fun _ => ρ' (0,0)) i := by
          intro i hi
          apply pushAgreement vs _ _ 0 (by simp) i
          simpa [hvs.length_eq] using hi
        have ht := (tyEvalLocality M ρ ρ' (push vs (fun _ => ρ (0,0))) T (fun X => (hρ X).2)).trans
          (tyEvalStacks M ρ' _ _ T ks.length (tyKindLC T S ks 0 hs.2.2) hp)
        rw [ht]
        apply and_congr _ Iff.rfl
        exact (constraintLocality S M ρ ρ' ι ι' C _ _ (fun X => (hρ X).1) hι).trans
          (constraintStacks S M ρ' ι' C ks 0 hs.2.1 _ _ _ _ hp (by simp))

/-- Closed substitution images can be evaluated before entering any binder. -/
theorem tyEvalSubst (M : Model) (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0)
    (ρ : Assignment M) (β : Nat → M.Carrier) (T : Ty) :
    (T.subst θ).evalAt M ρ β = T.evalAt M (fun X => (θ X).eval M ρ) β := by
  induction T using tyInduction with
  | hf X =>
      simp only [Ty.subst, Ty.evalAt, Ty.eval]
      exact tyEvalStacks M ρ _ _ (θ X) 0 (hθ X) (by simp)
  | hb i => simp [Ty.subst, Ty.evalAt]
  | hc f ts ih =>
      simp only [Ty.subst, Ty.evalAt, List.map_map]
      congr 1
      exact List.map_congr_left (fun U hu => ih U hu)

theorem constraintEvalSubst (S : Signature) (M : Model) (θ : Subst)
    (hθ : ∀ X, (θ X).LCAt 0) (ρ : Assignment M) (ι : GroundEnv M)
    (C : Constraint) (n : Nat) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) :
    (C.mapTypes (fun _ T => T.subst θ) n).holdsAt S M ρ ι β γ ↔
      C.holdsAt S M (fun X => (θ X).eval M ρ) ι β γ := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ n β γ,
      (C.mapTypes (fun _ T => T.subst θ) n).holdsAt S M ρ ι β γ ↔
        C.holdsAt S M (fun X => (θ X).eval M ρ) ι β γ)
    (motive_2 := fun s => ∀ n β γ,
      (s.mapTypes (fun _ T => T.subst θ) n).denoteAt S M ρ ι β γ =
        s.denoteAt S M (fun X => (θ X).eval M ρ) ι β γ)
    (by intros; rfl) (by intros; rfl)
    (by
      intro p ts n β γ
      simp only [Constraint.mapTypes, Constraint.holdsAt, List.map_map]
      have he := List.map_congr_left (fun T (_ : T ∈ ts) => tyEvalSubst M θ hθ ρ β T)
      simpa only [Function.comp_def] using congrArg (fun xs => p.eval M xs) he |>.to_iff)
    (by intro C D ihC ihD n β γ; exact and_congr (ihC n β γ) (ihD n β γ))
    (by
      intro ks C ih n β γ
      simp only [Constraint.mapTypes, Constraint.holdsAt]
      exact exists_congr (fun vs => and_congr Iff.rfl (ih (n+ks.length) (push vs β) γ)))
    (by
      intro b s C ihs ihC n β γ
      simp only [Constraint.mapTypes, Constraint.holdsAt]
      rw [ihs n β γ]
      exact ihC n β _)
    (by intro x T n β γ; cases x <;> simp [Constraint.mapTypes, Constraint.holdsAt, tyEvalSubst M θ hθ])
    (by
      intro ks C T ih n β γ
      ext v
      simp only [Scheme.mapTypes, Scheme.denoteAt, Set.mem_ofPred_eq]
      apply and_congr Iff.rfl
      apply exists_congr
      intro vs
      rw [tyEvalSubst M θ hθ]
      exact and_congr Iff.rfl (and_congr (ih (n+ks.length) (push vs β) γ) Iff.rfl)) C n β γ

theorem semanticSubstitution (S : Signature) (M : Model) : HMX.LN.semanticSubstitution S M := by
  intro hM θ ρ ι hθ hρ _
  have hclosed := substImagesClosed S θ hθ
  refine ⟨?_, ?_, ?_⟩
  · intro X hx
    exact evaluationKind S M hM ρ _ [] (θ X) X.1 hρ (by simp) (hθ.2.2 X hx)
  · intro C hC
    exact (constraintEvalSubst S M θ hclosed ρ ι C 0 _ _).trans
      (constraintStacks S M _ ι C [] 0 hC _ _ _ _ (by simp) (by simp))
  · intro s hs
    cases s with
    | all ks C T =>
        simp only [Scheme.WF, List.append_nil] at hs
        ext v
        simp only [Scheme.subst, Scheme.mapTypes, Scheme.denote, Scheme.denoteAt, Set.mem_ofPred_eq]
        apply and_congr Iff.rfl
        apply exists_congr
        intro vs
        apply and_congr_right
        intro hvs
        have hp : ∀ i, i < ks.length →
            push vs (fun _ => ρ (0,0)) i = push vs (fun _ => (θ (0,0)).eval M ρ) i := by
          intro i hi
          apply pushAgreement vs _ _ 0 (by simp) i
          simpa [hvs.length_eq] using hi
        rw [tyEvalSubst M θ hclosed]
        rw [tyEvalStacks M _ _ _ T ks.length (tyKindLC T S ks 0 hs.2.2) hp]
        apply and_congr _ Iff.rfl
        exact (constraintEvalSubst S M θ hclosed ρ ι C _ _ _).trans
          (constraintStacks S M _ ι C ks 0 hs.2.1 _ _ _ _ hp (by simp))

theorem pushSingletonMonotone {α : Type} (A B : Set α) (γ γ' : Nat → Set α)
    (hAB : A ⊆ B) (hγ : ∀ i, γ i ⊆ γ' i) (i : Nat) :
    push [A] γ i ⊆ push [B] γ' i := by
  cases i with
  | zero => simpa [push] using hAB
  | succ i => simpa [push] using hγ i

/-- Both free and bound program environments grow in the same direction. -/
theorem constraintMonotone (S : Signature) (M : Model) (ρ : Assignment M)
    (C : Constraint) (ι ι' : GroundEnv M) (β : Nat → M.Carrier)
    (γ γ' : Nat → Set M.Carrier) (hι : ∀ x, ι x ⊆ ι' x) (hγ : ∀ i, γ i ⊆ γ' i) :
    C.holdsAt S M ρ ι β γ → C.holdsAt S M ρ ι' β γ' := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ ι ι' β γ γ', (∀ x, ι x ⊆ ι' x) → (∀ i, γ i ⊆ γ' i) →
      C.holdsAt S M ρ ι β γ → C.holdsAt S M ρ ι' β γ')
    (motive_2 := fun s => ∀ ι ι' β γ γ', (∀ x, ι x ⊆ ι' x) → (∀ i, γ i ⊆ γ' i) →
      s.denoteAt S M ρ ι β γ ⊆ s.denoteAt S M ρ ι' β γ')
    (by intros; trivial) (by intros; contradiction)
    (by intro p ts ι ι' β γ γ' _ _ hc; exact hc)
    (by intro C D ihC ihD ι ι' β γ γ' hι hγ hc; exact
      ⟨ihC ι ι' β γ γ' hι hγ hc.1, ihD ι ι' β γ γ' hι hγ hc.2⟩)
    (by
      intro ks C ih ι ι' β γ γ' hι hγ hc
      rcases hc with ⟨vs, hv, hc⟩
      exact ⟨vs, hv, ih ι ι' (push vs β) γ γ' hι hγ hc⟩)
    (by
      intro b s C ihs ihC ι ι' β γ γ' hι hγ hc
      exact ihC ι ι' β _ _ hι (pushSingletonMonotone _ _ γ γ' (ihs ι ι' β γ γ' hι hγ) hγ) hc)
    (by
      intro x T ι ι' β γ γ' hι hγ hc
      cases x with
      | free x => exact hι x hc
      | bound i => exact hγ i hc)
    (by
      intro ks C T ih ι ι' β γ γ' hι hγ v hv
      rcases hv with ⟨hk, vs, hvs, hc, ht⟩
      exact ⟨hk, vs, hvs, ih ι ι' (push vs β) γ γ' hι hγ hc, ht⟩) C ι ι' β γ γ' hι hγ

theorem groundEnvironmentMonotonicity (S : Signature) (M : Model) :
    HMX.LN.groundEnvironmentMonotonicity S M := by
  intro _ ρ ι ι' _ _ _ hι
  constructor
  · intro C _ hc
    exact constraintMonotone S M ρ C ι ι' _ _ _ hι (fun _ => Set.Subset.rfl) hc
  · intro s _
    cases s with
    | all ks C T =>
        intro v hv
        rcases hv with ⟨hk, vs, hvs, hc, ht⟩
        exact ⟨hk, vs, hvs, constraintMonotone S M ρ C ι ι' _ _ _ hι (fun _ => Set.Subset.rfl) hc, ht⟩

end HMX.LN.Proofs
