import HMX.LocallyNameless.Proofs.FrameworkCorrespondence
import HMX.LocallyNameless.Proofs.GenerationCorrespondence
import HMX.LocallyNameless.Proofs.Environment

namespace HMX.LN.Proofs

theorem encodingTyKindReflection (T : HMX.Ty) (xs : List TVar)
    (h : (ofTy xs T).HasKind S (xs.map Prod.fst) k) : T.HasKind S k := by
  cases T with
  | var X =>
    by_cases hx : X ∈ xs
    · simp only [ofTy, hx, ↓reduceIte] at h
      cases h with
      | bound hi hk =>
        have he : X.1 = k := by simpa [List.getElem?_map, List.getElem?_idxOf hx] using hi
        subst k
        exact .var X hk
    · simp only [ofTy, hx, ↓reduceIte] at h
      cases h with
      | free hk => exact .var X hk
  | con f ts =>
    simp only [ofTy] at h
    cases h with
    | con hf ht =>
      apply HMX.Ty.HasKind.con _ _ hf
      have hs := List.forall₂_map_left_iff.mp ht
      exact forall₂ImplMem hs (fun U _ p hp => encodingTyKindReflection U xs hp)
termination_by sizeOf T

mutual
theorem encodingConstraintWFReflection (C : HMX.Constraint) (xs : List TVar) (zs : List Id)
    (h : (ofConstraint xs zs C).WF S (xs.map Prod.fst) zs.length) : C.WF S := by
  cases C with
  | truth => trivial
  | falsity => trivial
  | atom p ts =>
    refine ⟨h.1, ?_⟩
    exact (List.forall₂_map_left_iff.mp h.2).imp (fun T _ ht => encodingTyKindReflection T xs ht)
  | conj C D =>
    exact ⟨encodingConstraintWFReflection C xs zs h.1, encodingConstraintWFReflection D xs zs h.2⟩
  | exists_ A C =>
    refine ⟨?_, encodingConstraintWFReflection C (boundNames A ++ xs) zs (by simpa using h.2)⟩
    intro X hX
    exact h.1 X.1 (List.mem_map.mpr ⟨X, (boundNamesMem A X).mpr hX, rfl⟩)
  | def_ x s C =>
    exact ⟨encodingSchemeWFReflection s xs zs h.1,
      encodingConstraintWFReflection C xs (x :: zs) (by simpa using h.2)⟩
  | inst x T => exact encodingTyKindReflection T xs h.1
theorem encodingSchemeWFReflection (s : HMX.Scheme) (xs : List TVar) (zs : List Id)
    (h : (ofScheme xs zs s).WF S (xs.map Prod.fst) zs.length) : s.WF S := by
  cases s with
  | all A C T =>
    refine ⟨?_, encodingConstraintWFReflection C (boundNames A ++ xs) zs (by simpa using h.2.1),
      encodingTyKindReflection T (boundNames A ++ xs) (by simpa using h.2.2)⟩
    intro X hX
    exact h.1 X.1 (List.mem_map.mpr ⟨X, (boundNamesMem A X).mpr hX, rfl⟩)
end

theorem encodingEnvWF (Γ : HMX.Env) : (ofEnv Γ).WF S ↔ Γ.WF S := by
  constructor
  · intro h p hp
    exact encodingSchemeWFReflection p.2 [] [] (h _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact encodingSchemeWF q.2 (h q hq) [] []

theorem encodingEnvFv (Γ : HMX.Env) : (ofEnv Γ).fv = Γ.fv := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    change (ofScheme [] [] p.2).fv ∪ (ofEnv Γ).fv = p.2.fv ∪ HMX.Env.fv Γ
    rw [(encodingFreeVariables.2.2 p.2).1, ih]

theorem encodingEnvFpi (Γ : HMX.Env) : (ofEnv Γ).fpi = Γ.fpi := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    change (ofScheme [] [] p.2).fpi ∪ (ofEnv Γ).fpi = p.2.fpi ∪ HMX.Env.fpi Γ
    rw [(encodingFreeVariables.2.2 p.2).2, ih]

theorem encodingEnvDpi (Γ : HMX.Env) : (ofEnv Γ).dpi = Γ.dpi := by
  simp [ofEnv, Env.dpi, HMX.Env.dpi, List.map_map, Function.comp_def]

theorem encodingEnvAppend (Γ Δ : HMX.Env) : ofEnv (Γ ++ Δ) = ofEnv Γ ++ ofEnv Δ :=
  List.map_append

theorem encodingDefine (x : Id) (s : HMX.Scheme) (C : HMX.Constraint) :
    ofConstraint [] [] (.def_ x s C) =
      (ofConstraint [] [] C).define x (ofScheme [] [] s) := by
  simp only [ofConstraint, Constraint.define, Constraint.closeId]
  have h := encodingConstraintCloseId C [] [] x
  simp only [List.length_nil, List.nil_append] at h
  rw [h]

theorem encodingDefPrefix (Γ : HMX.Env) (C : HMX.Constraint) :
    ofConstraint [] [] (Γ.defIn C) = (ofEnv Γ).defIn (ofConstraint [] [] C) := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    simp only [HMX.Env.defIn, List.foldr_cons, ofEnv, List.map_cons, Env.defIn]
    rw [encodingDefine]
    exact congrArg (Constraint.define p.1 (ofScheme [] [] p.2)) ih

theorem encodingEnvExistsFold (Γ Δ : HMX.Env) (C : HMX.Constraint) :
    ofConstraint [] []
      (Γ.foldl (fun (acc : HMX.Env × HMX.Constraint) p =>
        (acc.1 ++ [p], .conj acc.2 (acc.1.defIn p.2.exists_))) (Δ, C)).2 =
    ((ofEnv Γ).foldl (fun (acc : Env × Constraint) p =>
        (acc.1 ++ [p], .conj acc.2 (acc.1.defIn p.2.exists_)))
      (ofEnv Δ, ofConstraint [] [] C)).2 := by
  induction Γ generalizing Δ C with
  | nil => rfl
  | cons p Γ ih =>
    simp only [List.foldl_cons, ofEnv, List.map_cons]
    rw [ih]
    simp only [ofEnv, List.map_append, List.map_cons, List.map_nil, ofConstraint,
      encodingDefPrefix, encodingSchemeExists]

theorem encodingEnvExists (Γ : HMX.Env) :
    ofConstraint [] [] Γ.exists_ = (ofEnv Γ).exists_ :=
  encodingEnvExistsFold Γ [] .truth

theorem encodingEnvLookup (Γ : HMX.Env) (x : Id) :
    lookup (ofEnv Γ) x = (lookup Γ x).map (ofScheme [] []) := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    change lookup ((p.1, ofScheme [] [] p.2) :: ofEnv Γ) x = _
    rw [lookupCons, lookupCons, ih]
    cases lookup Γ x <;> simp

theorem encodingEntails {C D : HMX.Constraint} (hM : M.Requirements S) (hC : C.WF S) (hD : D.WF S) :
    Entails S M (ofConstraint [] [] C) (ofConstraint [] [] D) ↔ HMX.Entails S M C D := by
  constructor <;> intro h ρ ι hρ hι hholds
  · have he := (encodingSemantics S M hM ρ ι hρ hι).1
    exact (he D hD).mp (h ρ ι hρ hι ((he C hC).mpr hholds))
  · have he := (encodingSemantics S M hM ρ ι hρ hι).1
    exact (he D hD).mpr (h ρ ι hρ hι ((he C hC).mp hholds))

theorem encodingEquivalent {C D : HMX.Constraint} (hM : M.Requirements S) (hC : C.WF S) (hD : D.WF S) :
    Equivalent S M (ofConstraint [] [] C) (ofConstraint [] [] D) ↔ HMX.Equivalent S M C D :=
  and_congr (encodingEntails hM hC hD) (encodingEntails hM hD hC)

theorem encodingJudgmentWF (C : HMX.Constraint) (Γ : HMX.Env) (t : HMX.Expr)
    (s : HMX.Scheme) :
    JudgmentWF S (ofConstraint [] [] C) (ofEnv Γ) (ofExpr [] t) (ofScheme [] [] s) ↔
      HMX.JudgmentWF S C Γ s := by
  constructor
  · rintro ⟨hC, hΓ, _, hs, hCf, hΓf, hsf⟩
    exact ⟨encodingConstraintWFReflection C [] [] hC, (encodingEnvWF Γ).mp hΓ,
      encodingSchemeWFReflection s [] [] hs,
      (encodingFreeVariables.2.1 C).2.symm.trans hCf,
      (encodingEnvFpi Γ).symm.trans hΓf, (encodingFreeVariables.2.2 s).2.symm.trans hsf⟩
  · rintro ⟨hC, hΓ, hs, hCf, hΓf, hsf⟩
    exact ⟨encodingConstraintWF C hC [] [], (encodingEnvWF Γ).mpr hΓ,
      encodingExprLC t [], encodingSchemeWF s hs [] [],
      (encodingFreeVariables.2.1 C).2.trans hCf, (encodingEnvFpi Γ).trans hΓf,
      (encodingFreeVariables.2.2 s).2.trans hsf⟩

end HMX.LN.Proofs
