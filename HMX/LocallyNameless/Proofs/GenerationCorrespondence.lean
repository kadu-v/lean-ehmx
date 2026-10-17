import HMX.LocallyNameless.Proofs.Encoding

namespace HMX.LN.Proofs

theorem encodingTyClose (T : HMX.Ty) (pre xs : List TVar) :
    (ofTy pre T).closeAt pre.length xs = ofTy (pre ++ xs) T := by
  cases T with
  | var X =>
    by_cases hp : X ∈ pre
    · have hi := List.idxOf_lt_length_iff.mpr hp
      simp [ofTy, hp, Ty.closeAt, List.idxOf_append_of_mem hp, hi]
    · by_cases hx : X ∈ xs <;>
        simp [ofTy, hp, hx, Ty.closeAt, List.idxOf_append_of_notMem hp]
  | con f ts =>
    simp only [ofTy, Ty.closeAt, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun U _ => encodingTyClose U pre xs)
termination_by sizeOf T

mutual
theorem encodingConstraintCloseTypes (C : HMX.Constraint) (pre xs : List TVar) (zs : List Id) :
    (ofConstraint pre zs C).mapTypes (fun d T => T.closeAt d xs) pre.length =
      ofConstraint (pre ++ xs) zs C := by
  cases C with
  | truth => rfl
  | falsity => rfl
  | atom p ts =>
    simp only [ofConstraint, Constraint.mapTypes, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun T _ => encodingTyClose T pre xs)
  | conj C D =>
    simp only [ofConstraint, Constraint.mapTypes]
    rw [encodingConstraintCloseTypes C, encodingConstraintCloseTypes D]
  | exists_ A C =>
    simp only [ofConstraint, Constraint.mapTypes]
    congr 1
    simpa [List.length_append, List.append_assoc, Nat.add_comm] using
      encodingConstraintCloseTypes C (boundNames A ++ pre) xs zs
  | def_ x s C =>
    simp only [ofConstraint, Constraint.mapTypes]
    rw [encodingSchemeCloseTypes s, encodingConstraintCloseTypes C]
  | inst x T =>
    simp only [ofConstraint, Constraint.mapTypes]
    rw [encodingTyClose]
theorem encodingSchemeCloseTypes (s : HMX.Scheme) (pre xs : List TVar) (zs : List Id) :
    (ofScheme pre zs s).mapTypes (fun d T => T.closeAt d xs) pre.length =
      ofScheme (pre ++ xs) zs s := by
  cases s with
  | all A C T =>
    simp only [ofScheme, Scheme.mapTypes]
    congr 1
    · simpa [List.length_append, List.append_assoc, Nat.add_comm] using
        encodingConstraintCloseTypes C (boundNames A ++ pre) xs zs
    · simpa [List.length_append, List.append_assoc, Nat.add_comm] using
        encodingTyClose T (boundNames A ++ pre) xs
end

theorem encodingIdClose (pre : List Id) (x y : Id) :
    (ofId pre y).closeAt pre.length x = ofId (pre ++ [x]) y := by
  by_cases hp : y ∈ pre
  · have hi := List.idxOf_lt_length_iff.mpr hp
    simp [ofId, hp, PVar.closeAt, List.idxOf_append_of_mem hp, hi]
  · by_cases hx : y = x
    · subst y; simp [ofId, hp, PVar.closeAt, List.idxOf_append_of_notMem hp]
    · simp [ofId, hp, hx, PVar.closeAt]

mutual
theorem encodingConstraintCloseId (C : HMX.Constraint) (xs : List TVar) (pre : List Id) (x : Id) :
    (ofConstraint xs pre C).mapIds (fun d v => v.closeAt d x) pre.length =
      ofConstraint xs (pre ++ [x]) C := by
  cases C with
  | truth => rfl
  | falsity => rfl
  | atom p ts => rfl
  | conj C D =>
    simp only [ofConstraint, Constraint.mapIds]
    rw [encodingConstraintCloseId C, encodingConstraintCloseId D]
  | exists_ A C =>
    simp only [ofConstraint, Constraint.mapIds]
    rw [encodingConstraintCloseId C]
  | def_ y s C =>
    simp only [ofConstraint, Constraint.mapIds]
    rw [encodingSchemeCloseId s]
    congr 1
    simpa using encodingConstraintCloseId C xs (y :: pre) x
  | inst y T =>
    simp only [ofConstraint, Constraint.mapIds]
    rw [encodingIdClose]
theorem encodingSchemeCloseId (s : HMX.Scheme) (xs : List TVar) (pre : List Id) (x : Id) :
    (ofScheme xs pre s).mapIds (fun d v => v.closeAt d x) pre.length =
      ofScheme xs (pre ++ [x]) s := by
  cases s with
  | all A C T =>
    simp only [ofScheme, Scheme.mapIds]
    rw [encodingConstraintCloseId C]
end

theorem boundNamesEmpty : boundNames ∅ = [] := by simp [boundNames]

theorem boundNamesSingleton (X : TVar) : boundNames {X} = [X] := by simp [boundNames]

theorem boundNamesFreshPair (n : Nat) : boundNames {(0,n), (0,n+1)} = [(0,n), (0,n+1)] := by
  simp only [boundNames, Finset.map_insert, Finset.map_singleton]
  rw [Finset.sort_insert (· ≤ ·) (by simp [Prod.Lex.toLex_le_toLex]) (by simp)]
  simp

theorem encodingExists (A : Vars) (C : HMX.Constraint) (zs : List Id) :
    ofConstraint [] zs (.exists_ A C) = (ofConstraint [] zs C).existsNames (boundNames A) := by
  simp only [ofConstraint, Constraint.existsNames, Constraint.closeTypes]
  have h := encodingConstraintCloseTypes C [] (boundNames A) zs
  simpa using congrArg (Constraint.exists_ ((boundNames A).map Prod.fst)) h.symm

theorem encodingGeneralize (A : Vars) (C : HMX.Constraint) (T : HMX.Ty) (zs : List Id) :
    ofScheme [] zs (.all A C T) = Scheme.generalize (boundNames A)
      (ofConstraint [] zs C) (ofTy [] T) := by
  simp only [ofScheme, Scheme.generalize, Constraint.closeTypes]
  congr 1
  · simpa using (encodingConstraintCloseTypes C [] (boundNames A) zs).symm
  · simpa using (encodingTyClose T [] (boundNames A)).symm

theorem encodingMono (T : HMX.Ty) (zs : List Id) :
    ofScheme [] zs (.mono T) = .mono (ofTy [] T) := by
  simp [HMX.Scheme.mono, ofScheme, boundNamesEmpty, ofConstraint, Scheme.mono]

theorem encodingSchemeExists (s : HMX.Scheme) (xs : List TVar) (zs : List Id) :
    ofConstraint xs zs s.exists_ = (ofScheme xs zs s).exists_ := by
  cases s; rfl

theorem encodingLet (x : Id) (s : HMX.Scheme) (C : HMX.Constraint) (xs : List TVar) :
    ofConstraint xs [] (.let_ x s C) =
      (ofConstraint xs [] C).letName x (ofScheme xs [] s) := by
  simp only [HMX.Constraint.let_, ofConstraint, Constraint.letName,
    Constraint.define, Constraint.closeId, encodingSchemeExists]
  have h := encodingConstraintCloseId C xs [] x
  simp only [List.length_nil, List.nil_append] at h
  rw [h]

theorem encodingPrefix (Γ : HMX.Env) (C : HMX.Constraint) :
    ofConstraint [] [] (Γ.letIn C) = (ofEnv Γ).letIn (ofConstraint [] [] C) := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    simp only [HMX.Env.letIn, List.foldr_cons, ofEnv, List.map_cons, Env.letIn]
    rw [encodingLet]
    exact congrArg (Constraint.letName p.1 (ofScheme [] [] p.2)) ih

theorem encodingMaxIndex (T : HMX.Ty) : (ofTy [] T).maxIndex = T.maxIndex := by
  cases T with
  | var X => simp [ofTy, Ty.maxIndex, HMX.Ty.maxIndex]
  | con f ts =>
    simp only [ofTy, Ty.maxIndex, HMX.Ty.maxIndex, List.map_map, Function.comp_def]
    rw [List.map_congr_left (fun U (_ : U ∈ ts) => encodingMaxIndex U)]
termination_by sizeOf T

theorem encodingGenerate (t : HMX.Expr) (T : HMX.Ty) (zs : List Id) :
    ofConstraint [] zs (HMX.generate t T) = generate (ofExpr zs t) (ofTy [] T) := by
  induction t generalizing T zs with
  | ident x => rfl
  | lam z t ih =>
    simp only [HMX.generate, ofExpr, generate, freshIndex, encodingMaxIndex,
      HMX.freshIndex, encodingExists, boundNamesFreshPair, ofConstraint,
      HMX.Constraint.let_, encodingSchemeExists, encodingMono]
    simp only [
      ofConstraint, ofTy, List.not_mem_nil, ↓reduceIte, List.map_cons, List.map_nil,
      HMX.Constraint.le, HMX.Ty.arrow, Constraint.le, Ty.arrow,
      Constraint.letBound, Scheme.mono, Scheme.exists_]
    rw [ih]
    simp [ofTy, Binder.ofId]
  | app t u iht ihu =>
    simp only [HMX.generate, ofExpr, generate, freshIndex, encodingMaxIndex,
      HMX.freshIndex, encodingExists, boundNamesSingleton, ofConstraint]
    rw [iht, ihu]
    simp [ofTy, HMX.Ty.arrow, Ty.arrow]
  | letE z t u iht ihu =>
    simp only [HMX.generate, ofExpr, generate, freshIndex, encodingMaxIndex,
      HMX.freshIndex, HMX.Constraint.let_, ofConstraint, encodingSchemeExists,
      encodingGeneralize, boundNamesSingleton, Constraint.letBound]
    rw [iht, ihu]
    simp [ofTy, Binder.ofId]

theorem generationCorrespondence : HMX.LN.generationCorrespondence := by
  intro Γ t T
  rw [HMX.infer, encodingPrefix, encodingGenerate]
  exact .refl

end HMX.LN.Proofs
