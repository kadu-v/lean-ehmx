import HMX.LocallyNameless.Proofs.Closing

namespace HMX.LN.Proofs

theorem updateEnvMonotone (ι : GroundEnv M) (x : Id) (A B : Set M.Carrier) (h : A ⊆ B) :
    ∀ y, updateEnv ι x A y ⊆ updateEnv ι x B y := by
  intro y
  by_cases hy : y = x
  · simpa [updateEnv, hy] using h
  · simp [updateEnv, hy]

theorem constraintCongruence (S : Signature) (M : Model) : HMX.LN.constraintCongruence S M := by
  intro hM K C D hC hD
  induction K with
  | hole => exact fun _ _ h => h
  | fixed E => exact fun _ _ _ _ _ _ _ h => h
  | conj K L ihK ihL =>
      intro hKC hKD h ρ ι hρ hι he
      exact ⟨ihK hKC.1 hKD.1 h ρ ι hρ hι he.1, ihL hKC.2 hKD.2 h ρ ι hρ hι he.2⟩
  | exists_ xs K ih =>
      intro hKC hKD h ρ ι hρ hι he
      have hwC := (existsNamesWFReflect S xs (K.plug C) hKC).2
      have hwD := (existsNamesWFReflect S xs (K.plug D) hKD).2
      obtain ⟨vs, hv, he⟩ := (existsNamesHolds S M ρ ι xs (K.plug C) hwC).mp he
      apply (existsNamesHolds S M ρ ι xs (K.plug D) hwD).mpr
      exact ⟨vs, hv, ih hwC hwD h _ ι (assignBlockValid S M ρ xs vs hρ hv) hι he⟩
  | define x xs K T L ihK ihL =>
      intro hKC hKD h ρ ι hρ hι he
      have hwC := defineWFReflect S x (Scheme.generalize xs (K.plug C) T) (L.plug C) hKC
      have hwD := defineWFReflect S x (Scheme.generalize xs (K.plug D) T) (L.plug D) hKD
      have hkC := generalizeWFReflect S xs (K.plug C) T hwC.1
      have hkD := generalizeWFReflect S xs (K.plug D) T hwD.1
      have hs : (Scheme.generalize xs (K.plug C) T).denote S M ρ ι ⊆
          (Scheme.generalize xs (K.plug D) T).denote S M ρ ι := by
        intro v hv
        obtain ⟨hk, vs, hvs, he, ht⟩ := (generalizeDenote S M ρ ι xs (K.plug C) T hkC.2.1 hkC.2.2 v).mp hv
        apply (generalizeDenote S M ρ ι xs (K.plug D) T hkD.2.1 hkD.2.2 v).mpr
        exact ⟨hk, vs, hvs, ihK hkC.2.1 hkD.2.1 h _ ι (assignBlockValid S M ρ xs vs hρ hvs) hι he, ht⟩
      have henv : (updateEnv ι x ((Scheme.generalize xs (K.plug C) T).denote S M ρ ι)).Valid M :=
        schemeDenotationValid S M hM ρ ι _ x hρ hι hwC.1
      have he' := (defineHolds S M ρ ι x _ (L.plug C)).mp he
      have hd := ihL hwC.2 hwD.2 h ρ _ hρ henv he'
      apply (defineHolds S M ρ ι x _ (L.plug D)).mpr
      exact constraintMonotone S M ρ (L.plug D) _ _ _ _ _ (updateEnvMonotone ι x _ _ hs) (fun _ => Set.Subset.rfl) hd

theorem andCommLaw (S : Signature) (M : Model) (C D : Constraint) : EquationLaw S M (.conj C D) (.conj D C) := by
  intro _ _
  exact ⟨fun _ _ _ _ h => h.symm, fun _ _ _ _ h => h.symm⟩

theorem andAssocLaw (S : Signature) (M : Model) (C D E : Constraint) :
    EquationLaw S M (.conj (.conj C D) E) (.conj C (.conj D E)) := by
  intro _ _
  exact ⟨fun _ _ _ _ h => ⟨h.1.1, h.1.2, h.2⟩, fun _ _ _ _ h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩

theorem andTrueLaw (S : Signature) (M : Model) (C : Constraint) : EquationLaw S M (.conj C .truth) C := by
  intro _ _
  exact ⟨fun _ _ _ _ h => h.1, fun _ _ _ _ h => ⟨h, trivial⟩⟩

theorem andEntailedLaw (S : Signature) (M : Model) (C D : Constraint) (h : Entails S M C D) :
    EquationLaw S M (.conj C D) C := by
  intro _ _
  exact ⟨fun _ _ _ _ he => he.1, fun ρ ι hρ hι he => ⟨he, h ρ ι hρ hι he⟩⟩

theorem existsUnusedLaw (S : Signature) (M : Model) (hM : M.Requirements S)
    (xs : List TVar) (C : Constraint) (hf : Disjoint xs.toFinset C.fv) : EquationLaw S M (C.existsNames xs) C := by
  intro hW hC
  have hx := (existsNamesWFReflect S xs C hW).1
  constructor
  · intro ρ ι hρ hι he
    obtain ⟨vs, hv, hc⟩ := (existsNamesHolds S M ρ ι xs C hC).mp he
    exact (holdsAssignBlock S M hM ρ ι xs vs C hρ hι hv hC hf).mp hc
  · intro ρ ι hρ _ hc
    apply (existsNamesHolds S M ρ ι xs C hC).mpr
    exact ⟨xs.map ρ, assignmentBlockKinds S M ρ xs hρ hx, by simpa [assignBlockSelf] using hc⟩

theorem existsAndLaw (S : Signature) (M : Model) (hM : M.Requirements S)
    (xs : List TVar) (C D : Constraint) (hf : Disjoint xs.toFinset D.fv) :
    EquationLaw S M (.conj (C.existsNames xs) D) ((Constraint.conj C D).existsNames xs) := by
  intro hL _
  have hc := (existsNamesWFReflect S xs C hL.1).2
  have hd := hL.2
  constructor
  · intro ρ ι hρ hι he
    obtain ⟨vs, hv, hC⟩ := (existsNamesHolds S M ρ ι xs C hc).mp he.1
    apply (existsNamesHolds S M ρ ι xs (.conj C D) ⟨hc, hd⟩).mpr
    exact ⟨vs, hv, hC, (holdsAssignBlock S M hM ρ ι xs vs D hρ hι hv hd hf).mpr he.2⟩
  · intro ρ ι hρ hι he
    obtain ⟨vs, hv, hC, hD⟩ := (existsNamesHolds S M ρ ι xs (.conj C D) ⟨hc, hd⟩).mp he
    exact ⟨(existsNamesHolds S M ρ ι xs C hc).mpr ⟨vs, hv, hC⟩,
      (holdsAssignBlock S M hM ρ ι xs vs D hρ hι hv hd hf).mp hD⟩

theorem subRefl (S : Signature) (M : Model) (hM : M.Requirements S) (T : Ty) (k : Nat)
    (ht : T.HasKind S [] k) : Entails S M .truth (.le k T T) := by
  intro ρ ι hρ _ _
  have hk := evalKind S M hM ρ hρ T k ht
  exact (leHolds S M ρ ι k T T).mpr ⟨hk, hk, hM.2.2.2.1 k (tyKindDeclared S hM.1 T [] k ht) _ hk⟩

theorem subTrans (S : Signature) (M : Model) (hM : M.Requirements S) (T U V : Ty) (k : Nat)
    (ht : T.HasKind S [] k) : Entails S M (.conj (.le k T U) (.le k U V)) (.le k T V) := by
  intro ρ ι _ _ he
  have h₁ := (leHolds S M ρ ι k T U).mp he.1
  have h₂ := (leHolds S M ρ ι k U V).mp he.2
  exact (leHolds S M ρ ι k T V).mpr ⟨h₁.1, h₂.2.1,
    hM.2.2.2.2.1 k (tyKindDeclared S hM.1 T [] k ht) _ _ _ h₁.1 h₁.2.1 h₂.2.1 h₁.2.2 h₂.2.2⟩

theorem nameLaw (S : Signature) (M : Model) (hM : M.Requirements S) (X : TVar) (T : Ty)
    (ht : T.HasKind S [] X.1) (hf : X ∉ T.fv) :
    EquationLaw S M ((Constraint.eq X.1 (.free X) T).existsNames [X]) .truth := by
  intro hW _
  have hc := (existsNamesWFReflect S [X] _ hW).2
  constructor
  · intro ρ ι _ _ _; trivial
  · intro ρ ι hρ _ _
    have hk := evalKind S M hM ρ hρ T X.1 ht
    apply (existsNamesHolds S M ρ ι [X] _ hc).mpr
    refine ⟨[T.eval M ρ], .cons hk .nil, ?_⟩
    apply (eqHolds S M _ ι X.1 (.free X) T).mpr
    have he := tyEvalAssignBlock M ρ [X] [T.eval M ρ] T (tyKindLC T S [] X.1 ht) (by simpa using hf)
    have hX : (Ty.free X).eval M (assignBlock [X] [T.eval M ρ] ρ) = T.eval M ρ := by
      simp [Ty.eval, Ty.evalAt, assignBlock]
    rw [he, hX]
    exact ⟨hk, hk, rfl⟩

theorem basicConstraintLaws (S : Signature) (M : Model) : HMX.LN.basicConstraintLaws S M := by
  intro hM
  exact ⟨andCommLaw S M, andAssocLaw S M, andTrueLaw S M, andEntailedLaw S M,
    fun xs C _ hf => existsUnusedLaw S M hM xs C hf,
    fun xs C D _ hf => existsAndLaw S M hM xs C D hf,
    fun T k ht => subRefl S M hM T k ht,
    fun T U V k ht _ _ => subTrans S M hM T U V k ht, nameLaw S M hM⟩

theorem letSub (S : Signature) (M : Model) : HMX.LN.letSub S M := by
  intro hM X x T C hx hf hL hR
  have hw := (existsNamesWFReflect S [X] _ hL).2
  have hsX := (letNameWFReflect S x (.mono (.free X)) C hw.2).1
  have hr := letNameWFReflect S x (.mono T) C hR
  have ht : T.HasKind S [] 0 := by simpa [Scheme.mono, Scheme.WF, Constraint.WF] using hr.1
  have hfT : Disjoint [X].toFinset T.fv := by simp only [Finset.mem_union, not_or] at hf; simpa using hf.1
  have hfC : Disjoint [X].toFinset C.fv := by simp only [Finset.mem_union, not_or] at hf; simpa using hf.2
  constructor
  · intro ρ ι hρ hι he
    obtain ⟨vs, hv, hle, hlet⟩ := (existsNamesHolds S M ρ ι [X] _ hw).mp he
    let ρ' := assignBlock [X] vs ρ
    have hρ' : ρ'.Valid S M := assignBlockValid S M ρ [X] vs hρ hv
    have hle' := (leHolds S M ρ' ι 0 T (.free X)).mp hle
    have htEq := tyEvalAssignBlock M ρ [X] vs T (tyKindLC T S [] 0 ht) hfT
    have hiX : (updateEnv ι x ((Scheme.mono (.free X)).denote S M ρ' ι)).Valid M :=
      schemeDenotationValid S M hM ρ' ι _ x hρ' hι hsX
    have hb := (letNameHolds S M ρ' ι x _ C).mp hlet |>.2
    have hb' := (holdsAssignBlock S M hM ρ _ [X] vs C hρ hiX hv hr.2 hfC).mp hb
    have hinc : (Scheme.mono (.free X)).denote S M ρ' ι ⊆ (Scheme.mono T).denote S M ρ ι := by
      intro v hv
      have hv' := (monoDenote S M ρ' ι (.free X) v).mp hv
      apply (monoDenote S M ρ ι T v).mpr
      refine ⟨hv'.1, ?_⟩
      rw [← htEq]
      exact hM.2.2.2.2.1 0 hM.1.1 _ _ _ hle'.1 hle'.2.1 hv'.1 hle'.2.2 hv'.2
    apply (letNameHolds S M ρ ι x _ C).mpr
    exact ⟨monoExists S M ρ ι T, constraintMonotone S M ρ C _ _ _ _ _
      (updateEnvMonotone ι x _ _ hinc) (fun _ => Set.Subset.rfl) hb'⟩
  · intro ρ ι hρ hι he
    let v := T.eval M ρ
    let ρ' := assignBlock [X] [v] ρ
    have hk : M.kind v = 0 := evalKind S M hM ρ hρ T 0 ht
    have hv : List.Forall₂ (fun w Y => M.kind w = Y.1) [v] [X] := .cons (by simpa [hx] using hk) .nil
    have htEq := tyEvalAssignBlock M ρ [X] [v] T (tyKindLC T S [] 0 ht) hfT
    have hX : (Ty.free X).eval M ρ' = v := by simp [ρ', Ty.eval, Ty.evalAt, assignBlock]
    have heq : (Scheme.mono (.free X)).denote S M ρ' ι = (Scheme.mono T).denote S M ρ ι := by
      ext w
      rw [monoDenote, monoDenote, hX]
    have hiT : (updateEnv ι x ((Scheme.mono T).denote S M ρ ι)).Valid M :=
      schemeDenotationValid S M hM ρ ι _ x hρ hι hr.1
    have hb := (letNameHolds S M ρ ι x _ C).mp he |>.2
    apply (existsNamesHolds S M ρ ι [X] _ hw).mpr
    refine ⟨[v], hv, ?_, ?_⟩
    · apply (leHolds S M ρ' ι 0 T (.free X)).mpr
      rw [htEq, hX]
      exact ⟨hk, hk, hM.2.2.2.1 0 hM.1.1 v hk⟩
    · apply (letNameHolds S M ρ' ι x _ C).mpr
      refine ⟨monoExists S M ρ' ι (.free X), ?_⟩
      rw [heq]
      exact (holdsAssignBlock S M hM ρ _ [X] [v] C hρ hiT hv hr.2 hfC).mpr hb

end HMX.LN.Proofs
