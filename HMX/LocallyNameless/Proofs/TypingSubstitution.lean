import HMX.LocallyNameless.Proofs.Weakening

namespace HMX.LN.Proofs

theorem constraintSubstCongr (θ σ : Subst) (C : Constraint) (n : Nat)
    (h : ∀ X ∈ C.fv, θ X = σ X) :
    C.mapTypes (fun _ T => T.subst θ) n = C.mapTypes (fun _ T => T.subst σ) n := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ n, (∀ X ∈ C.fv, θ X = σ X) →
      C.mapTypes (fun _ T => T.subst θ) n = C.mapTypes (fun _ T => T.subst σ) n)
    (motive_2 := fun s => ∀ n, (∀ X ∈ s.fv, θ X = σ X) →
      s.mapTypes (fun _ T => T.subst θ) n = s.mapTypes (fun _ T => T.subst σ) n)
    (by intros; rfl) (by intros; rfl)
    (by
      intro q ts n hh
      simp only [Constraint.mapTypes]
      congr 1
      exact List.map_congr_left (fun T ht => tySubstCongr T θ σ
        (fun X hx => hh X ((memUnionFold Ty.fv ts X).mpr ⟨T,ht,hx⟩))))
    (by
      intro C D ihC ihD n hh
      exact congrArg₂ Constraint.conj (ihC n (fun X hx => hh X (Finset.mem_union_left _ hx)))
        (ihD n (fun X hx => hh X (Finset.mem_union_right _ hx))))
    (by intro ks C ih n hh; exact congrArg (Constraint.exists_ ks) (ih _ hh))
    (by
      intro b s C ihs ihC n hh
      exact congrArg₂ (Constraint.def_ b) (ihs n (fun X hx => hh X (Finset.mem_union_left _ hx)))
        (ihC n (fun X hx => hh X (Finset.mem_union_right _ hx))))
    (by intro x T n hh; exact congrArg (Constraint.inst x) (tySubstCongr T θ σ hh))
    (by
      intro ks C T ih n hh
      exact congrArg₂ (Scheme.all ks) (ih _ (fun X hx => hh X (Finset.mem_union_left _ hx)))
        (tySubstCongr T θ σ (fun X hx => hh X (Finset.mem_union_right _ hx)))) C n h

theorem schemeSubstCongr (θ σ : Subst) (s : Scheme) (h : ∀ X ∈ s.fv, θ X = σ X) :
    s.subst θ = s.subst σ := by
  cases s with
  | all ks C T =>
      exact congrArg₂ (Scheme.all ks)
        (constraintSubstCongr θ σ C _ (fun X hx => h X (Finset.mem_union_left _ hx)))
        (tySubstCongr T θ σ (fun X hx => h X (Finset.mem_union_right _ hx)))

theorem envSubstCongr (θ σ : Subst) (Γ : Env) (h : ∀ X ∈ Γ.fv, θ X = σ X) :
    Γ.subst θ = Γ.subst σ := by
  induction Γ with
  | nil => rfl
  | cons q Γ ih =>
      have hs := schemeSubstCongr θ σ q.2 (fun X hx => h X (Finset.mem_union_left _ hx))
      have ht := ih (fun X hx => h X (Finset.mem_union_right _ hx))
      simpa only [Env.subst, List.map_cons, hs] using congrArg (List.cons (q.1,q.2.subst σ)) ht

theorem judgmentSubstWF (θ : Subst) (hθ : θ.Valid S) (h : JudgmentWF S C Γ t s) :
    JudgmentWF S (C.subst θ) (Γ.subst θ) t (s.subst θ) := by
  refine ⟨(freeSubstitutionWF S θ hθ).2.1 _ _ _ h.1, ?_, h.2.2.1,
    (freeSubstitutionWF S θ hθ).2.2 _ _ _ h.2.2.2.1, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact (freeSubstitutionWF S θ hθ).2.2 _ _ _ (h.2.1 r hr)
  · exact (constraintMapTypesFpi _ C 0).trans h.2.2.2.2.1
  · exact (envSubstFpi θ Γ).trans h.2.2.2.2.2.1
  · exact (schemeSubstFpi θ s).trans h.2.2.2.2.2.2

theorem entailsSubst (θ : Subst) (hθ : θ.Valid S) (hM : M.Requirements S)
    (C D : Constraint) (hc : C.WF S [] 0) (hd : D.WF S [] 0) (h : Entails S M C D) :
    Entails S M (C.subst θ) (D.subst θ) := by
  intro ρ ι hρ hι he
  have hρ' : Assignment.Valid S M (fun X => (θ X).eval M ρ) := by
    intro X hx
    exact evalKind S M hM ρ hρ (θ X) X.1 (hθ.2.2 X hx)
  have hs := semanticSubstitution S M hM θ ρ ι hθ hρ hι
  exact (hs.2.1 D hd).mpr (h _ ι hρ' hι ((hs.2.1 C hc).mp he))

def substBlock (θ : Subst) (xs : List TVar) (p : TVar ≃ TVar) : Subst :=
  fun X => if X ∈ xs then .free (p X) else θ X

theorem substBlockValid (θ : Subst) (hθ : θ.Valid S) (xs : List TVar)
    (hx : ∀ X ∈ xs, X.1 ∈ S.kinds) (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1) :
    (substBlock θ xs p).Valid S := by
  refine ⟨?_, ?_, ?_⟩
  · apply (hθ.1.union xs.toFinset.finite_toSet).subset
    intro X hX
    by_cases hm : X ∈ xs
    · exact Or.inr (List.mem_toFinset.mpr hm)
    · exact Or.inl (by simpa [substBlock, hm] using hX)
  · intro X hX
    by_cases hm : X ∈ xs
    · exact hx X hm
    · exact hθ.2.1 X (by simpa [substBlock, hm] using hX)
  · intro X hX
    by_cases hm : X ∈ xs
    · simp only [substBlock, hm, ↓reduceIte]
      rw [← hk X] at hX ⊢
      exact .free hX
    · simpa [substBlock, hm] using hθ.2.2 X hX

theorem substBlockClose (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0) (xs : List TVar)
    (p : TVar ≃ TVar) (X : TVar) (hf : Disjoint (xs.map p).toFinset (θ X).fv) (n : Nat) :
    ((Ty.free X).closeAt n xs).subst θ = (substBlock θ xs p X).closeAt n (xs.map p) := by
  by_cases hx : X ∈ xs
  · simp [Ty.closeAt, Ty.subst, substBlock, hx, idxOfMapEquiv]
  · simp only [Ty.closeAt, hx, ↓reduceIte, Ty.subst, substBlock]
    exact (tyCloseUnused (θ X) (xs.map p) n (hθ X) hf).symm

theorem substBlockConstraint (θ : Subst) (xs : List TVar) (p : TVar ≃ TVar)
    (C : Constraint) (hf : Disjoint xs.toFinset C.fv) : C.subst (substBlock θ xs p) = C.subst θ :=
  constraintSubstCongr _ _ C 0 (fun X hx => by
    have hX : X ∉ xs := fun he => Finset.disjoint_left.mp hf (List.mem_toFinset.mpr he) hx
    simp [substBlock, hX])

theorem substBlockEnv (θ : Subst) (xs : List TVar) (p : TVar ≃ TVar)
    (Γ : Env) (hf : Disjoint xs.toFinset Γ.fv) : Γ.subst (substBlock θ xs p) = Γ.subst θ :=
  envSubstCongr _ _ Γ (fun X hx => by
    have hX : X ∉ xs := fun he => Finset.disjoint_left.mp hf (List.mem_toFinset.mpr he) hx
    simp [substBlock, hX])

theorem substBlockTy (θ : Subst) (xs : List TVar) (p : TVar ≃ TVar)
    (T : Ty) (hf : Disjoint xs.toFinset T.fv) : T.subst (substBlock θ xs p) = T.subst θ :=
  tySubstCongr T _ _ (fun X hx => by
    have hX : X ∉ xs := fun he => Finset.disjoint_left.mp hf (List.mem_toFinset.mpr he) hx
    simp [substBlock, hX])

theorem freshSubstBlock (θ : Subst) (xs : List TVar) (V F : Vars) :
    ∃ p : TVar ≃ TVar, (∀ X, (p X).1 = X.1) ∧ Disjoint (xs.map p).toFinset F ∧
      (∀ X ∈ V, Disjoint (xs.map p).toFinset (θ X).fv) := by
  obtain ⟨p,hk,_,hf⟩ := freshTypePermutation xs.toFinset (F ∪ V.biUnion (fun X => (θ X).fv)) ∅ (by simp)
  refine ⟨p,hk,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro Y hy hY
    obtain ⟨X,hX,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact hf X (List.mem_toFinset.mpr hX) (Finset.mem_union_left _ hY)
  · intro X hx
    apply Finset.disjoint_left.mpr
    intro Y hy hY
    obtain ⟨Z,hZ,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact hf Z (List.mem_toFinset.mpr hZ) (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨X,hx,hY⟩))

def blockEquations (θ : Subst) (xs : List TVar) (p : TVar ≃ TVar) : Constraint :=
  (xs.map (fun X => Constraint.eq X.1 (.free (p X)) (θ X))).foldr Constraint.conj .truth

theorem blockEquationsWF (θ : Subst) (hθ : θ.Valid S) (xs : List TVar)
    (hx : ∀ X ∈ xs, X.1 ∈ S.kinds) (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1) :
    (blockEquations θ xs p).WF S [] 0 := by
  induction xs with
  | nil => trivial
  | cons X xs ih =>
      refine ⟨⟨hx X (by simp), .cons ?_ (.cons (hθ.2.2 X (hx X (by simp))) .nil)⟩,
        ih (fun Y hy => hx Y (by simp [hy]))⟩
      rw [← hk X]
      exact .free (by rw [hk]; exact hx X (by simp))

theorem blockEquationsFpi (θ : Subst) (xs : List TVar) (p : TVar ≃ TVar) :
    (blockEquations θ xs p).fpi = ∅ := by
  induction xs with
  | nil => rfl
  | cons X xs ih => simpa [blockEquations, Constraint.eq, Constraint.fpi] using ih

theorem blockEquationsHolds (θ : Subst) (xs : List TVar) (p : TVar ≃ TVar) (ρ : Assignment M) (ι : GroundEnv M) :
    (blockEquations θ xs p).Holds S M ρ ι ↔
      ∀ X ∈ xs, M.kind (ρ (p X)) = X.1 ∧ M.kind ((θ X).eval M ρ) = X.1 ∧ ρ (p X) = (θ X).eval M ρ := by
  induction xs with
  | nil => simp [blockEquations, Constraint.Holds, Constraint.holdsAt]
  | cons X xs ih =>
      change ((Constraint.eq X.1 (.free (p X)) (θ X)).Holds S M ρ ι ∧
        (blockEquations θ xs p).Holds S M ρ ι) ↔ _
      rw [eqHolds, ih]
      simp only [Ty.eval, Ty.evalAt, List.mem_cons, forall_eq_or_imp]

theorem tyEvalSubstClosed (M : Model) (θ : Subst) (hc : ∀ X, (θ X).LCAt 0)
    (ρ : Assignment M) (T : Ty) (ht : T.LCAt 0) :
    (T.subst θ).eval M ρ = T.eval M (fun X => (θ X).eval M ρ) :=
  (tyEvalSubst M θ hc ρ _ T).trans (tyEvalStacks M _ _ _ T 0 ht (by simp))

theorem substEvalAgreement (M : Model) (θ σ : Subst) (hθ : ∀ X, (θ X).LCAt 0)
    (hσ : ∀ X, (σ X).LCAt 0) (ρ ρ' : Assignment M) (T : Ty) (ht : T.LCAt 0)
    (h : ∀ X ∈ T.fv, (σ X).eval M ρ' = (θ X).eval M ρ) :
    (T.subst σ).eval M ρ' = (T.subst θ).eval M ρ := by
  rw [tyEvalSubstClosed M σ hσ ρ' T ht, tyEvalSubstClosed M θ hθ ρ T ht]
  exact (tyEvalLocality M _ _ _ T h).trans (tyEvalStacks M _ _ _ T 0 ht (by simp))

theorem substHoldsAgreement (hM : M.Requirements S) (θ σ : Subst) (hθ : θ.Valid S)
    (hσ : σ.Valid S) (ρ ρ' : Assignment M) (ι : GroundEnv M)
    (hρ : ρ.Valid S M) (hρ' : ρ'.Valid S M) (hι : ι.Valid M) (C : Constraint) (hc : C.WF S [] 0)
    (h : ∀ X ∈ C.fv, (σ X).eval M ρ' = (θ X).eval M ρ) :
    (C.subst σ).Holds S M ρ' ι ↔ (C.subst θ).Holds S M ρ ι := by
  have hs := semanticSubstitution S M hM σ ρ' ι hσ hρ' hι
  have ht := semanticSubstitution S M hM θ ρ ι hθ hρ hι
  exact (hs.2.1 C hc).trans (((semanticLocality S M hM _ _ ι ι hs.1 ht.1 hι hι).1 C hc h
    (fun _ _ => rfl)).trans (ht.2.1 C hc).symm)

theorem blockEquationsAgreement (θ : Subst) (xs : List TVar) (p : TVar ≃ TVar)
    (ρ : Assignment M) (ι : GroundEnv M) (he : (blockEquations θ xs p).Holds S M ρ ι) (X : TVar) :
    (substBlock θ xs p X).eval M ρ = (θ X).eval M ρ := by
  by_cases hx : X ∈ xs
  · simpa [substBlock, hx, Ty.eval, Ty.evalAt] using ((blockEquationsHolds θ xs p ρ ι).mp he X hx).2.2
  · simp [substBlock, hx]

theorem assignBlockMapped (ρ : Assignment M) (xs : List TVar) (p : TVar ≃ TVar)
    (f : TVar → M.Carrier) (X : TVar) (hx : X ∈ xs) :
    assignBlock (xs.map p) (xs.map f) ρ (p X) = f X := by
  simp [assignBlock, hx, idxOfMapEquiv, List.getElem?_map, List.getElem?_idxOf hx]

theorem freshBlockWitness (hM : M.Requirements S) (θ : Subst) (hθ : θ.Valid S) (xs : List TVar)
    (hx : ∀ X ∈ xs, X.1 ∈ S.kinds) (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (ρ : Assignment M) (hρ : ρ.Valid S M) (V : Vars)
    (hf : ∀ X ∈ V ∪ xs.toFinset, Disjoint (xs.map p).toFinset (θ X).fv) :
    let vs := xs.map (fun X => (θ X).eval M ρ)
    let ρ' := assignBlock (xs.map p) vs ρ
    List.Forall₂ (fun v X => M.kind v = X.1) vs (xs.map p) ∧
    (∀ X ∈ V, (substBlock θ xs p X).eval M ρ' = (θ X).eval M ρ) ∧
    (∀ ι : GroundEnv M, (blockEquations θ xs p).Holds S M ρ' ι) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro X hX
    rw [hk]
    exact evalKind S M hM ρ hρ _ _ (hθ.2.2 X (hx X hX))
  · intro X hX
    by_cases hm : X ∈ xs
    · simp only [substBlock, hm, ↓reduceIte, Ty.eval, Ty.evalAt]
      exact assignBlockMapped ρ xs p _ X hm
    · simp only [substBlock, hm, ↓reduceIte]
      exact tyEvalAssignBlock M ρ (xs.map p) _ (θ X) (substImagesClosed S θ hθ X)
        (hf X (Finset.mem_union_left _ hX))
  · intro ι
    apply (blockEquationsHolds θ xs p _ ι).mpr
    intro X hX
    rw [assignBlockMapped ρ xs p _ X hX,
      tyEvalAssignBlock M ρ (xs.map p) _ (θ X) (substImagesClosed S θ hθ X)
        (hf X (Finset.mem_union_right _ (List.mem_toFinset.mpr hX)))]
    have hv := evalKind S M hM ρ hρ _ _ (hθ.2.2 X (hx X hX))
    exact ⟨hv,hv,rfl⟩

theorem alternateVarSubst (hM : M.Requirements S) (θ : Subst) (hθ : θ.Valid S)
    (xs : List TVar) (hn : xs.Nodup) (hkxs : ∀ X ∈ xs, X.1 ∈ S.kinds)
    (D : Constraint) (T : Ty) (hD : D.WF S [] 0) (hT : T.HasKind S [] 0) (hDf : D.fpi = ∅)
    (Γ : Env) (x : Id) (hl : lookup Γ x = some (Scheme.generalize xs D T))
    (he : JudgmentWF S E (Γ.subst θ) (.ident (.free x)) (.mono (T.subst θ)))
    (hED : Entails S M E (D.subst θ)) : AlternateTyping S M E (Γ.subst θ) (.ident (.free x)) (T.subst θ) := by
  obtain ⟨p,hpk,hpF,hpV⟩ := freshSubstBlock θ xs ((D.fv ∪ T.fv) ∪ xs.toFinset)
    (E.fv ∪ (Γ.subst θ).fv ∪ (T.subst θ).fv)
  let ys := xs.map p
  let σ := substBlock θ xs p
  let Q := blockEquations θ xs p
  let K := Constraint.conj (.conj E Q) (D.subst σ)
  have hσ : σ.Valid S := substBlockValid θ hθ xs hkxs p hpk
  have hyk : ∀ Y ∈ ys, Y.1 ∈ S.kinds := by
    intro Y hY
    obtain ⟨X,hX,rfl⟩ := List.mem_map.mp hY
    simpa only [hpk] using hkxs X hX
  have hys : ys.Nodup := hn.map p.injective
  have hTσ := tySubstKind S σ hσ T [] 0 hT
  have hDσ := (freeSubstitutionWF S σ hσ).2.1 [] 0 D hD
  have hQ : Q.WF S [] 0 := blockEquationsWF θ hθ xs hkxs p hpk
  have hK : K.WF S [] 0 := ⟨⟨he.1,hQ⟩,hDσ⟩
  have hKf : K.fpi = ∅ := by
    have hfσ : (D.subst σ).fpi = ∅ := (constraintMapTypesFpi _ D 0).trans hDf
    simp only [K, Constraint.fpi, Q, blockEquationsFpi, he.2.2.2.2.1, hfσ, Finset.union_self]
  have hKW : JudgmentWF S K (Γ.subst θ) (.ident (.free x)) (.mono (T.subst θ)) :=
    judgmentChangeConstraint he hK hKf
  have hv : AlternateTyping S M K (Γ.subst θ) (.ident (.free x)) (T.subst σ) := by
    apply AlternateTyping.varInst (xs := ys)
    · exact ⟨hK,he.2.1,he.2.2.1,monoWF S _ hTσ,hKf,he.2.2.2.2.2.1,rfl⟩
    · exact hys
    · rw [lookupSubst,hl,Option.map_some]
      congr 1
      exact substGeneralizeRename D T xs ys θ σ (typeRenameKinds p hpk xs).symm
        (fun n X hx => substBlockClose θ (substImagesClosed S θ hθ) xs p X
          (hpV X (Finset.mem_union_left _ hx)) n)
  have hs : AlternateTyping S M K (Γ.subst θ) (.ident (.free x)) (T.subst θ) := by
    apply AlternateTyping.sub hKW hv
    intro ρ ι hρ hι hh
    have heval := substEvalAgreement M θ σ (substImagesClosed S θ hθ) (substImagesClosed S σ hσ)
      ρ ρ T (tyKindLC T S [] 0 hT) (fun X _ => blockEquationsAgreement θ xs p ρ ι hh.1.2 X)
    apply (leHolds S M ρ ι 0 _ _).mpr
    rw [heval]
    have ht := evalKind S M hM ρ hρ _ _ (tySubstKind S θ hθ T [] 0 hT)
    exact ⟨ht,ht,hM.2.2.2.1 0 (tyKindDeclared S hM.1 T [] 0 hT) _ ht⟩
  have hyE : Disjoint ys.toFinset E.fv := hpF.mono_right
    (fun X hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have hyΓT : Disjoint ys.toFinset ((Γ.subst θ).fv ∪ (T.subst θ).fv) := by
    apply hpF.mono_right
    intro X hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    · exact Finset.mem_union_right _ hx
  have hexw : JudgmentWF S (K.existsNames ys) (Γ.subst θ) (.ident (.free x)) (.mono (T.subst θ)) :=
    judgmentChangeConstraint he (existsNamesWF S ys K 0 hyk hK) (by rw [existsNamesFpi,hKf])
  apply AlternateTyping.convert he (AlternateTyping.exists_ hexw hys hyk hyΓT hs) ?_ (envBinderEqRefl _)
  constructor
  · intro ρ ι hρ hι hh
    obtain ⟨vs,hvs,hh⟩ := (existsNamesHolds S M ρ ι ys K hK).mp hh
    exact (holdsAssignBlock S M hM ρ ι ys vs E hρ hι hvs he.1 hyE).mp hh.1.1
  · intro ρ ι hρ hι hh
    obtain ⟨hvs,ha,hq⟩ := freshBlockWitness hM θ hθ xs hkxs p hpk ρ hρ (D.fv ∪ T.fv) hpV
    let vs := xs.map (fun X => (θ X).eval M ρ)
    have hρ' := assignBlockValid S M ρ ys vs hρ hvs
    apply (existsNamesHolds S M ρ ι ys K hK).mpr
    refine ⟨vs,hvs,⟨(holdsAssignBlock S M hM ρ ι ys vs E hρ hι hvs he.1 hyE).mpr hh,hq ι⟩,?_⟩
    exact (substHoldsAgreement hM θ σ hθ hσ ρ _ ι hρ hρ' hι D hD
      (fun X hx => ha X (Finset.mem_union_left _ hx))).mpr (hED ρ ι hρ hι hh)

/-- Strengthening the induction hypothesis by both substitution and entailment
allows each quantifier block to choose names fresh for the target judgment. -/
theorem alternateTransform (hM : M.Requirements S) (hd : AlternateTyping S M C Γ t T) :
    ∀ θ : Subst, θ.Valid S → ∀ E, JudgmentWF S E (Γ.subst θ) t (.mono (T.subst θ)) →
      Entails S M E (C.subst θ) → AlternateTyping S M E (Γ.subst θ) t (T.subst θ) := by
  induction hd with
  | @varInst C D Γ x T xs hw hn hl =>
      intro θ hθ E he hEC
      have hsw := hw.2.1 _ (lookupMember Γ x _ hl)
      have hparts := generalizeWFReflect S xs D T hsw
      exact alternateVarSubst hM θ hθ xs hn hparts.1 D T hparts.2.1 hparts.2.2
        (Finset.union_eq_empty.mp hw.2.2.2.2.1).2 Γ x hl he
        (fun ρ ι hρ hι hh => (hEC ρ ι hρ hι hh).2)
  | abs L hw hd ih =>
      intro θ hθ E he hEC
      simp only [Ty.arrow, Ty.subst, List.map_cons, List.map_nil] at he ⊢
      apply AlternateTyping.abs L he
      intro z hz
      have hp := ih z hz θ hθ E
        (judgmentChangeConstraint (judgmentSubstWF θ hθ (alternateWF (hd z hz))) he.1 he.2.2.2.2.1) hEC
      simpa only [Env.subst, List.map_append, List.map_cons, List.map_nil, substMono] using hp
  | app hw ht hu iht ihu =>
      intro θ hθ E he hEC
      have hpt := iht θ hθ E
        (judgmentChangeConstraint (judgmentSubstWF θ hθ (alternateWF ht)) he.1 he.2.2.2.2.1) hEC
      have hpu := ihu θ hθ E
        (judgmentChangeConstraint (judgmentSubstWF θ hθ (alternateWF hu)) he.1 he.2.2.2.2.1) hEC
      apply AlternateTyping.app he _ hpu
      simpa only [Ty.arrow, Ty.subst, List.map_cons, List.map_nil] using hpt
  | @letGen C Γ t u U D T xs L hw hn hf ht hu iht ihu =>
      intro θ hθ E he hEC
      have htw := alternateWF ht
      have hxs := (existsNamesWFReflect S xs D hw.1.2).1
      obtain ⟨p,hpk,hpF,hpV⟩ := freshSubstBlock θ xs (D.fv ∪ T.fv) (E.fv ∪ (Γ.subst θ).fv)
      let ys := xs.map p
      let σ := substBlock θ xs p
      have hσ : σ.Valid S := substBlockValid θ hθ xs hxs p hpk
      have hΓ := substBlockEnv θ xs p Γ (hf.mono_right Finset.subset_union_right)
      have hC := substBlockConstraint θ xs p C (hf.mono_right Finset.subset_union_left)
      have hD : (D.existsNames xs).subst θ = (D.subst σ).existsNames ys :=
        substExistsRename D xs ys θ σ (typeRenameKinds p hpk xs).symm
          (fun n X hx => substBlockClose θ (substImagesClosed S θ hθ) xs p X
            (hpV X (Finset.mem_union_left _ hx)) n)
      have hs : (Scheme.generalize xs D T).subst θ = Scheme.generalize ys (D.subst σ) (T.subst σ) :=
        substGeneralizeRename D T xs ys θ σ (typeRenameKinds p hpk xs).symm
          (fun n X hx => substBlockClose θ (substImagesClosed S θ hθ) xs p X (hpV X hx) n)
      have hDwf := (freeSubstitutionWF S θ hθ).2.1 [] 0 (D.existsNames xs) hw.1.2
      rw [hD] at hDwf
      have hDw := (freeSubstitutionWF S σ hσ).2.1 [] 0 D htw.1.2
      have hDf : (D.subst σ).fpi = ∅ := (constraintMapTypesFpi _ D 0).trans
        (Finset.union_eq_empty.mp htw.2.2.2.2.1).2
      have hED : Entails S M E ((D.subst σ).existsNames ys) := by
        intro ρ ι hρ hι hh
        rw [← hD]
        exact (hEC ρ ι hρ hι hh).2
      have hptw : JudgmentWF S (.conj E (D.subst σ)) (Γ.subst σ) t (.mono (T.subst σ)) :=
        judgmentChangeConstraint (judgmentSubstWF σ hσ htw) ⟨he.1,hDw⟩
          (by simp [Constraint.fpi, he.2.2.2.2.1, hDf])
      have hpt := iht σ hσ (.conj E (D.subst σ)) hptw (by
        rw [substConj,hC]
        exact fun ρ ι hρ hι hh => ⟨(hEC ρ ι hρ hι hh.1).1,hh.2⟩)
      rw [hΓ] at hpt
      have hout : JudgmentWF S (.conj E ((D.subst σ).existsNames ys)) (Γ.subst θ) (.letE t u) (.mono (U.subst θ)) :=
        judgmentChangeConstraint he ⟨he.1,hDwf⟩
          (by simp [Constraint.fpi, existsNamesFpi, he.2.2.2.2.1, hDf])
      have hpu : ∀ z ∉ L, AlternateTyping S M (.conj E ((D.subst σ).existsNames ys))
          ((Γ.subst θ) ++ [(.var z, Scheme.generalize ys (D.subst σ) (T.subst σ))])
          (Expr.openAt 0 (.ident (.free (.var z))) u) (U.subst θ) := by
        intro z hz
        have hp := ihu z hz θ hθ _
          (judgmentChangeConstraint (judgmentSubstWF θ hθ (alternateWF (hu z hz))) hout.1 hout.2.2.2.2.1)
          (fun ρ ι hρ hι hh => hEC ρ ι hρ hι hh.1)
        simpa only [Env.subst, List.map_append, List.map_cons, List.map_nil, hs] using hp
      have hg := AlternateTyping.letGen L hout (hn.map p.injective) hpF hpt hpu
      exact .convert he hg ⟨fun _ _ _ _ hh => hh.1, fun ρ ι hρ hι hh => ⟨hh,hED ρ ι hρ hι hh⟩⟩
        (envBinderEqRefl _)
  | sub hw hd hr ih =>
      intro θ hθ E he hEC
      apply AlternateTyping.sub he
        (ih θ hθ E (judgmentChangeConstraint (judgmentSubstWF θ hθ (alternateWF hd)) he.1 he.2.2.2.2.1) hEC)
      have hlw : (Constraint.le 0 _ _).WF S [] 0 :=
        ⟨hM.1.1,.cons (alternateWF hd).2.2.2.1.2.2 (.cons hw.2.2.2.1.2.2 .nil)⟩
      have hr' := entailsSubst θ hθ hM _ _ hw.1 hlw hr
      exact fun ρ ι hρ hι hh => hr' ρ ι hρ hι (hEC ρ ι hρ hι hh)
  | @exists_ Γ t T xs C hw hn hk hf hd ih =>
      intro θ hθ E he hEC
      obtain ⟨p,hpk,hpF,hpV⟩ := freshSubstBlock θ xs C.fv (E.fv ∪ (Γ.subst θ).fv ∪ (T.subst θ).fv)
      let ys := xs.map p
      let σ := substBlock θ xs p
      have hσ : σ.Valid S := substBlockValid θ hθ xs hk p hpk
      have hΓ := substBlockEnv θ xs p Γ (hf.mono_right Finset.subset_union_left)
      have hT := substBlockTy θ xs p T (hf.mono_right Finset.subset_union_right)
      have hC : (C.existsNames xs).subst θ = (C.subst σ).existsNames ys :=
        substExistsRename C xs ys θ σ (typeRenameKinds p hpk xs).symm
          (fun n X hx => substBlockClose θ (substImagesClosed S θ hθ) xs p X (hpV X hx) n)
      have hw' := judgmentSubstWF σ hσ (alternateWF hd)
      have hpw : JudgmentWF S (.conj E (C.subst σ)) (Γ.subst σ) t (.mono (T.subst σ)) :=
        judgmentChangeConstraint hw' ⟨he.1,hw'.1⟩
          (by simp [Constraint.fpi, he.2.2.2.2.1, hw'.2.2.2.2.1])
      have hp := ih σ hσ _ hpw (fun _ _ _ _ hh => hh.2)
      rw [hΓ,hT] at hp
      have hyk : ∀ Y ∈ ys, Y.1 ∈ S.kinds := by
        intro Y hY; obtain ⟨X,hX,rfl⟩ := List.mem_map.mp hY
        simpa only [hpk] using hk X hX
      have hyE : Disjoint ys.toFinset E.fv := hpF.mono_right
        (fun X hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx))
      have hyΓT : Disjoint ys.toFinset ((Γ.subst θ).fv ∪ (T.subst θ).fv) := by
        apply hpF.mono_right
        intro X hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
        · exact Finset.mem_union_right _ hx
      have hqw : JudgmentWF S ((Constraint.conj E (C.subst σ)).existsNames ys) (Γ.subst θ) t (.mono (T.subst θ)) :=
        judgmentChangeConstraint he (existsNamesWF S ys _ 0 hyk hpw.1)
          (by rw [existsNamesFpi]; exact hpw.2.2.2.2.1)
      have hq := AlternateTyping.exists_ hqw (hn.map p.injective) hyk hyΓT hp
      apply AlternateTyping.convert he hq ?_ (envBinderEqRefl _)
      constructor
      · intro ρ ι hρ hι hh
        obtain ⟨vs,hvs,hh⟩ := (existsNamesHolds S M ρ ι ys _ hpw.1).mp hh
        exact (holdsAssignBlock S M hM ρ ι ys vs E hρ hι hvs he.1 hyE).mp hh.1
      · intro ρ ι hρ hι hh
        have hce : ((C.subst σ).existsNames ys).Holds S M ρ ι := by rw [← hC]; exact hEC ρ ι hρ hι hh
        obtain ⟨vs,hvs,hhC⟩ := (existsNamesHolds S M ρ ι ys _ hw'.1).mp hce
        exact (existsNamesHolds S M ρ ι ys _ hpw.1).mpr
          ⟨vs,hvs,(holdsAssignBlock S M hM ρ ι ys vs E hρ hι hvs he.1 hyE).mpr hh,hhC⟩
  | convert hw hd hc hΓ ih =>
      intro θ hθ E he hEC
      have hew := judgmentChangeConstraint (judgmentSubstWF θ hθ (alternateWF hd)) he.1 he.2.2.2.2.1
      have hp := ih θ hθ E hew (fun ρ ι hρ hι hh =>
        entailsSubst θ hθ hM _ _ hw.1 (alternateWF hd).1 hc.2 ρ ι hρ hι (hEC ρ ι hρ hι hh))
      exact .convert he hp ⟨fun _ _ _ _ hh => hh,fun _ _ _ _ hh => hh⟩
        (envBinderEqSubst θ (substImagesClosed S θ hθ) _ _ hΓ)

theorem substIdentityValid (S : Signature) : Subst.Valid S Ty.free :=
  ⟨by simp, by simp, fun _ hx => .free hx⟩

theorem schemeSubstIdentity (s : Scheme) : s.subst Ty.free = s := by
  cases s with
  | all ks C T =>
      change Scheme.all ks (C.mapTypes (fun _ U => U.subst Ty.free) _) (T.subst Ty.free) = _
      rw [constraintSubstAt, constraintSubstIdentity, tySubstIdentity]

theorem envSubstIdentity (Γ : Env) : Γ.subst Ty.free = Γ := by
  induction Γ with
  | nil => rfl
  | cons q Γ ih => simpa only [Env.subst,List.map_cons,schemeSubstIdentity] using congrArg (List.cons q) ih

theorem alternateWeakening (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.alternateWeakening S M I := by
  intro hF C E Γ t T he hEC hd
  have he' : JudgmentWF S E (Γ.subst Ty.free) t (.mono (T.subst Ty.free)) := by
    simpa only [envSubstIdentity,tySubstIdentity] using he
  have hp := alternateTransform hF.1 hd Ty.free (substIdentityValid S) E he'
    (by simpa only [constraintSubstIdentity] using hEC)
  simpa only [envSubstIdentity,tySubstIdentity] using hp

theorem alternateSubstitution (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.alternateSubstitution S M I := by
  intro hF θ C Γ t T hθ hd
  exact alternateTransform hF.1 hd θ hθ _ (judgmentSubstWF θ hθ (alternateWF hd)) (fun _ _ _ _ hh => hh)

end HMX.LN.Proofs
