import HMX.LocallyNameless.Proofs.GenerationSupport

namespace HMX.LN.Proofs

theorem generationWF (S : Signature) : HMX.LN.generationWF S := by
  intro hS d t T ht hT
  induction t generalizing d T with
  | ident x => cases x <;> exact ⟨hT,ht⟩
  | lam t ih =>
      simp only [generate]
      apply existsNamesWF S _ _ d (by simp [hS.1])
      refine ⟨letBoundWF S _ _ _ d (monoWFAt S _ d (.free hS.1)) (ih (d+1) _ ht (.free hS.1)), ?_⟩
      exact ⟨hS.1, .cons (arrowKind S hS _ _ [] (.free hS.1) (.free hS.1)) (.cons hT .nil)⟩
  | app t u iht ihu =>
      simp only [generate]
      apply existsNamesWF S _ _ d (by simp [hS.1])
      exact ⟨iht d _ ht.1 (arrowKind S hS _ _ [] (.free hS.1) hT), ihu d _ ht.2 (.free hS.1)⟩
  | letE t u iht ihu =>
      simp only [generate]
      apply letBoundWF S _ _ _ d
      · exact generalizeWF S _ _ _ d (by simp [hS.1]) (iht d _ ht.1 (.free hS.1)) (.free hS.1)
      · exact ihu (d+1) T ht.2 hT

theorem generationFreeVariables : HMX.LN.generationFreeVariables := by
  intro t T
  induction t generalizing T with
  | ident x => cases x <;> exact ⟨Finset.Subset.rfl,rfl⟩
  | lam t ih =>
      have hh := ih (.free (0,freshIndex T + 1))
      constructor
      · intro X hx
        simp only [generate, Constraint.existsNames, Constraint.fv, Constraint.closeTypes,
          constraintCloseFv, Constraint.letBound, Scheme.exists_, Scheme.mono, Scheme.fv,
          Constraint.le, Ty.arrow, Ty.fv, List.map_cons, List.map_nil, List.foldr_cons,
          List.foldr_nil, Finset.empty_union, Finset.union_empty, Finset.mem_sdiff,
          Finset.mem_union, Finset.mem_singleton, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_insert, Finset.notMem_empty, or_false, not_or] at hx
        have hsub : X ∈ (generate t (.free (0,freshIndex T+1))).fv → X = (0,freshIndex T+1) :=
          fun h => by simpa [Ty.fv] using hh.1 h
        aesop
      · simpa [generate, Constraint.existsNames, Constraint.closeTypes, constraintMapTypesFpi,
          Constraint.fpi, Constraint.letBound, Scheme.exists_, Scheme.mono, Scheme.fpi,
          Constraint.le, Expr.fpi] using hh.2
  | app t u iht ihu =>
      have ht := iht (.arrow (.free (0,freshIndex T)) T)
      have hu := ihu (.free (0,freshIndex T))
      constructor
      · intro X hx
        simp only [generate, Constraint.existsNames, Constraint.fv, Constraint.closeTypes,
          constraintCloseFv, Finset.mem_sdiff, Finset.mem_union] at hx
        have ht' : X ∈ (generate t (.arrow (.free (0,freshIndex T)) T)).fv → X = (0,freshIndex T) ∨ X ∈ T.fv :=
          fun h => by simpa [Ty.arrow, Ty.fv] using ht.1 h
        have hu' : X ∈ (generate u (.free (0,freshIndex T))).fv → X = (0,freshIndex T) :=
          fun h => by simpa [Ty.fv] using hu.1 h
        simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at hx
        aesop
      · simp [generate, Constraint.existsNames, Constraint.closeTypes, constraintMapTypesFpi,
          Constraint.fpi, Expr.fpi, ht.2, hu.2]
  | letE t u iht ihu =>
      have ht := iht (.free (0,freshIndex T))
      have hu := ihu T
      have hz : (generate t (.free (0,freshIndex T))).fv \ {(0,freshIndex T)} = ∅ := by
        apply Finset.sdiff_eq_empty_iff_subset.mpr
        simpa [Ty.fv] using ht.1
      constructor
      · simpa [generate, Constraint.letBound, Scheme.generalize, Scheme.exists_, Constraint.fv,
          Scheme.fv, Constraint.closeTypes, constraintCloseFv, tyCloseFv, Ty.fv, hz] using hu.1
      · simp [generate, Constraint.letBound, Scheme.generalize, Scheme.exists_, Constraint.fpi,
          Scheme.fpi, Constraint.closeTypes, constraintMapTypesFpi, Expr.fpi, ht.2, hu.2]

theorem generatedLambdaFv (t : Expr) (X Y : TVar) (T : Ty) :
    (Constraint.conj ((generate t (.free Y)).letBound .term (.mono (.free X)))
      (.le 0 (.arrow (.free X) (.free Y)) T)).fv ⊆ insert X (insert Y T.fv) := by
  have h := (generationFreeVariables t (.free Y)).1
  intro Z hz
  have hh : Z ∈ (generate t (.free Y)).fv → Z = Y := fun hm => by simpa [Ty.fv] using h hm
  simp only [Constraint.fv, Constraint.letBound, Scheme.mono, Scheme.exists_, Scheme.fv,
    Constraint.le, Ty.arrow, Ty.fv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
    Finset.empty_union, Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hz
  simp only [Finset.mem_insert]
  aesop

theorem generatedAppFv (t u : Expr) (X : TVar) (T : Ty) :
    (Constraint.conj (generate t (.arrow (.free X) T)) (generate u (.free X))).fv ⊆ insert X T.fv := by
  intro Z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · simpa [Ty.arrow, Ty.fv] using (generationFreeVariables t (.arrow (.free X) T)).1 hz
  · have hh : Z = X := by simpa [Ty.fv] using (generationFreeVariables u (.free X)).1 hz
    simp [hh]

/-- Match the freshly chosen names before closing each block. Fixed block order
gives syntactic equality, from which the registered BinderEq obligation follows. -/
theorem generateSubstEq (t : Expr) (T : Ty) (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0)
    (hT : T.LCAt 0) : (generate t T).subst θ = generate t (T.subst θ) := by
  induction t generalizing T θ with
  | ident x => rfl
  | lam t ih =>
      let X : TVar := (0,freshIndex T)
      let Y : TVar := (0,freshIndex T+1)
      let U : TVar := (0,freshIndex (T.subst θ))
      let V : TVar := (0,freshIndex (T.subst θ)+1)
      let σ := renameTwo θ X Y U V
      have hxy : X ≠ Y := by simp [X,Y]
      have huv : U ≠ V := by simp [U,V]
      have hx : X ∉ T.fv := freshNotMem T 0
      have hy : Y ∉ T.fv := freshNotMem T 1
      have hu : U ∉ (T.subst θ).fv := freshNotMem (T.subst θ) 0
      have hv : V ∉ (T.subst θ).fv := freshNotMem (T.subst θ) 1
      change (Constraint.existsNames [X,Y] _).subst θ = Constraint.existsNames [U,V] _
      rw [substExistsRename _ [X,Y] [U,V] θ σ (by rfl)
        (fun n Z hz => renameTwoClose θ T X Y U V hθ hxy huv hu hv n Z (generatedLambdaFv t X Y T hz))]
      simp only [substConj, substLetBound, substMono, substLe]
      rw [ih _ σ (renameTwoClosed θ X Y U V hθ) (by simp [Ty.LCAt])]
      have he := renameTwoTarget θ X Y U V T hx hy
      simp only [Ty.subst, Ty.arrow, List.map_cons, List.map_nil, σ, renameTwo, ↓reduceIte,
        Ne.symm hxy, he]
      rfl
  | app t u iht ihu =>
      let X : TVar := (0,freshIndex T)
      let Y : TVar := (0,freshIndex (T.subst θ))
      let σ := renameOne θ X Y
      have hx : X ∉ T.fv := freshNotMem T 0
      have hy : Y ∉ (T.subst θ).fv := freshNotMem (T.subst θ) 0
      change (Constraint.existsNames [X] _).subst θ = Constraint.existsNames [Y] _
      rw [substExistsRename _ [X] [Y] θ σ (by rfl)
        (fun n Z hz => renameOneClose θ T X Y hθ hy n Z (generatedAppFv t u X T hz))]
      simp only [substConj]
      rw [iht _ σ (renameOneClosed θ X Y hθ) (by simpa [Ty.arrow, Ty.LCAt] using hT),
        ihu _ σ (renameOneClosed θ X Y hθ) (by simp [Ty.LCAt])]
      have he := renameOneTarget θ X Y T hx
      simp only [Ty.subst, Ty.arrow, List.map_cons, List.map_nil, σ, renameOne, ↓reduceIte, he]
      rfl
  | letE t u iht ihu =>
      let X : TVar := (0,freshIndex T)
      let Y : TVar := (0,freshIndex (T.subst θ))
      let σ := renameOne θ X Y
      have hy : Y ∉ (T.subst θ).fv := freshNotMem (T.subst θ) 0
      change (Constraint.letBound .term (Scheme.generalize [X] _ _) _).subst θ =
        Constraint.letBound .term (Scheme.generalize [Y] _ _) _
      rw [substLetBound, ihu T θ hθ hT]
      rw [substGeneralizeRename _ _ [X] [Y] θ σ (by rfl) (by
        intro n Z hz
        apply renameOneClose θ T X Y hθ hy n Z
        have hs := (generationFreeVariables t (.free X)).1
        have hzX : Z = X := by
          rcases Finset.mem_union.mp hz with hz | hz
          · simpa [Ty.fv] using hs hz
          · simpa [Ty.fv] using hz
        simp [hzX])]
      rw [iht _ σ (renameOneClosed θ X Y hθ) (by simp [Ty.LCAt])]
      simp only [Ty.subst, σ, renameOne, X, Y, ↓reduceIte]

theorem generationSubstitution (S : Signature) : HMX.LN.generationSubstitution S := by
  intro _ θ t T hθ _ hT
  rw [generateSubstEq t T θ (substImagesClosed S θ hθ) (tyKindLC T S [] 0 hT)]
  exact .refl

/-- Opening a term binder commutes with generation at any term depth. -/
theorem generateOpenAt (t : Expr) (T : Ty) (x : Id) (d : Nat) :
    (generate t T).mapIds (fun n v => v.openAt n x) d =
      generate (Expr.openAt d (.ident (.free x)) t) T := by
  induction t generalizing T d with
  | ident v =>
      cases v with
      | free y => rfl
      | bound i =>
          by_cases hi : i = d
          · simp [generate, Expr.openAt, Constraint.mapIds, PVar.openAt, hi, Expr.shift]
          · simp [generate, Expr.openAt, Constraint.mapIds, PVar.openAt, hi]
  | lam t ih =>
      simp only [generate, Expr.openAt, mapIdsExistsNames, Constraint.mapIds, mapIdsLetBound,
        Scheme.mono, Scheme.mapIds, Constraint.le]
      rw [ih]
  | app t u iht ihu =>
      simp only [generate, Expr.openAt, mapIdsExistsNames, Constraint.mapIds, iht, ihu]
  | letE t u iht ihu =>
      simp only [generate, Expr.openAt, mapIdsLetBound, mapIdsGeneralize, iht, ihu]

theorem generationOpening : HMX.LN.generationOpening := by
  intro t z T _ _
  exact generateOpenAt t T (.var z) 0

theorem generateLamFresh (t : Expr) (T : Ty) (X Y : TVar) (_hT : T.LCAt 0)
    (hx : X.1 = 0) (hy : Y.1 = 0) (hxy : X ≠ Y) (hxT : X ∉ T.fv) (hyT : Y ∉ T.fv) :
    generate (.lam t) T = Constraint.existsNames [X,Y] (.conj
      ((generate t (.free Y)).letBound .term (.mono (.free X))) (.le 0 (.arrow (.free X) (.free Y)) T)) := by
  let A : TVar := (0,freshIndex T)
  let B : TVar := (0,freshIndex T+1)
  let σ := renameTwo Ty.free A B X Y
  have hab : A ≠ B := by simp [A,B]
  have hθ : ∀ Z, (Ty.free Z).LCAt 0 := by intro Z; simp [Ty.LCAt]
  have hC := substExistsRename
    (.conj ((generate t (.free B)).letBound .term (.mono (.free A))) (.le 0 (.arrow (.free A) (.free B)) T))
    [A,B] [X,Y] Ty.free σ (by simp [A,B,hx,hy])
    (fun n Z hz => renameTwoClose Ty.free T A B X Y hθ hab hxy
      (by simpa only [tySubstIdentity] using hxT) (by simpa only [tySubstIdentity] using hyT)
      n Z (generatedLambdaFv t A B T hz))
  rw [constraintSubstIdentity] at hC
  change generate (.lam t) T = _ at hC
  rw [hC]
  simp only [substConj, substLetBound, substMono, substLe]
  rw [generateSubstEq t _ σ (renameTwoClosed Ty.free A B X Y hθ) (by simp [Ty.LCAt])]
  have he := renameTwoTarget Ty.free A B X Y T (freshNotMem T 0) (freshNotMem T 1)
  simp only [Ty.subst, Ty.arrow, List.map_cons, List.map_nil, σ, renameTwo, ↓reduceIte,
    Ne.symm hab, he, tySubstIdentity]

theorem generateAppFresh (t u : Expr) (T : Ty) (X : TVar) (hT : T.LCAt 0)
    (hx : X.1 = 0) (hxT : X ∉ T.fv) :
    generate (.app t u) T = Constraint.existsNames [X]
      (.conj (generate t (.arrow (.free X) T)) (generate u (.free X))) := by
  let A : TVar := (0,freshIndex T)
  let σ := renameOne Ty.free A X
  have hθ : ∀ Z, (Ty.free Z).LCAt 0 := by intro Z; simp [Ty.LCAt]
  have hC := substExistsRename (.conj (generate t (.arrow (.free A) T)) (generate u (.free A)))
    [A] [X] Ty.free σ (by simp [A,hx])
    (fun n Z hz => renameOneClose Ty.free T A X hθ (by simpa only [tySubstIdentity] using hxT)
      n Z (generatedAppFv t u A T hz))
  rw [constraintSubstIdentity] at hC
  change generate (.app t u) T = _ at hC
  rw [hC]
  simp only [substConj]
  rw [generateSubstEq t _ σ (renameOneClosed Ty.free A X hθ) (by simpa [Ty.arrow, Ty.LCAt] using hT),
    generateSubstEq u _ σ (renameOneClosed Ty.free A X hθ) (by simp [Ty.LCAt])]
  have he := renameOneTarget Ty.free A X T (freshNotMem T 0)
  simp only [Ty.subst, Ty.arrow, List.map_cons, List.map_nil, σ, renameOne, ↓reduceIte, he, tySubstIdentity]

theorem generateLetFresh (t u : Expr) (T : Ty) (X : TVar)
    (hx : X.1 = 0) (hxT : X ∉ T.fv) :
    generate (.letE t u) T = (generate u T).letBound .term
      (Scheme.generalize [X] (generate t (.free X)) (.free X)) := by
  let A : TVar := (0,freshIndex T)
  let σ := renameOne Ty.free A X
  have hθ : ∀ Z, (Ty.free Z).LCAt 0 := by intro Z; simp [Ty.LCAt]
  have hS := substGeneralizeRename (generate t (.free A)) (.free A) [A] [X] Ty.free σ (by simp [A,hx]) (by
    intro n Z hz
    apply renameOneClose Ty.free T A X hθ (by simpa only [tySubstIdentity] using hxT) n Z
    have hzA : Z = A := by
      rcases Finset.mem_union.mp hz with hz | hz
      · simpa [Ty.fv] using (generationFreeVariables t (.free A)).1 hz
      · simpa [Ty.fv] using hz
    simp [hzA])
  have hsId : (Scheme.generalize [A] (generate t (.free A)) (.free A)).subst Ty.free =
      Scheme.generalize [A] (generate t (.free A)) (.free A) := by
    simp only [Scheme.generalize, Scheme.subst, Scheme.mapTypes]
    rw [constraintSubstAt, constraintSubstIdentity, tySubstIdentity]
  rw [hsId, generateSubstEq t _ σ (renameOneClosed Ty.free A X hθ) (by simp [Ty.LCAt])] at hS
  simp only [Ty.subst, σ, renameOne, ↓reduceIte] at hS
  change (generate u T).letBound .term (Scheme.generalize [A] _ _) = _
  rw [hS]

theorem generationFreshChoices (S : Signature) : HMX.LN.generationFreshChoices S := by
  intro _ t u T X Y _ _ hT hx hy hxy hxT hyT
  have ht := tyKindLC T S [] 0 hT
  rw [generateLamFresh t T X Y ht hx hy hxy hxT hyT,
    generateAppFresh t u T X ht hx hxT, generateLetFresh t u T X hx hxT]
  exact ⟨.refl,.refl,.refl⟩

theorem closedGenerationWF (S : Signature) : HMX.LN.closedGenerationWF S := by
  intro hS Γ t X hΓ hf ht hscope hk _
  have hX : (Ty.free X).HasKind S [] 0 := by simpa only [hk] using Ty.HasKind.free (S := S) (ks := []) (X := X) (by simpa only [hk] using hS.1)
  have hgen := generationWF S hS 0 t (.free X) ht hX
  have hvars := generationFreeVariables t (.free X)
  refine ⟨generalizeWF S [X] (infer Γ t (.free X)) (.free X) 0 (by simpa [hk] using hS.1)
    (letInWF S Γ _ hΓ hgen) hX, ?_, ?_⟩
  · simpa [closedGeneratedScheme, Scheme.generalize, Scheme.fpi, Constraint.closeTypes,
      constraintMapTypesFpi, infer, letInFpi Γ _ hf, hvars.2] using Finset.sdiff_eq_empty_iff_subset.mpr hscope
  · intro Y hy
    simp only [closedGeneratedScheme, Scheme.generalize, Scheme.fv, Constraint.closeTypes,
      constraintCloseFv, tyCloseFv, infer, letInFv, Ty.fv, List.toFinset_cons,
      List.toFinset_nil, insert_empty_eq, Finset.sdiff_self, Finset.union_empty,
      Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton] at hy
    rcases hy.1 with hyΓ | hyt
    · exact hyΓ
    · have he : Y = X := by simpa [Ty.fv] using hvars.1 hyt
      exact (hy.2 he).elim

end HMX.LN.Proofs
