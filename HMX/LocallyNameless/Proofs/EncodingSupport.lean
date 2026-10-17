import HMX.LocallyNameless.Correspondence
import HMX.LocallyNameless.Proofs.Closing

namespace HMX.LN.Proofs

theorem boundNamesMem (A : Vars) (X : TVar) : X ∈ boundNames A ↔ X ∈ A := by
  simp [boundNames]

theorem boundNamesNodup (A : Vars) : (boundNames A).Nodup := by
  apply List.Nodup.map _ (Finset.sort_nodup _ _)
  exact ofLex.injective

theorem encodingIdBound (zs : List Id) (x : Id) :
    match ofId zs x with
    | .free _ => True
    | .bound i => i < zs.length := by
  unfold ofId
  by_cases h : x ∈ zs
  · simpa [h] using List.idxOf_lt_length_iff.mpr h
  · simp [h]

theorem encodingExprLC (t : HMX.Expr) (zs : List Id) :
    (ofExpr zs t).LCAt zs.length := by
  induction t generalizing zs with
  | ident x =>
    have h := encodingIdBound zs x
    cases he : ofId zs x <;> simp_all [ofExpr, Expr.LCAt]
  | lam z t ih => simpa [ofExpr, Expr.LCAt] using ih (.var z :: zs)
  | app t u iht ihu => exact ⟨iht zs, ihu zs⟩
  | letE z t u iht ihu =>
    exact ⟨iht zs, by simpa using ihu (.var z :: zs)⟩

theorem encodingTyKind (h : HMX.Ty.HasKind S T k) (xs : List TVar) :
    (ofTy xs T).HasKind S (xs.map Prod.fst) k := by
  cases h with
  | var X hk =>
    simp only [ofTy]
    split
    · apply Ty.HasKind.bound _ hk
      simp [List.getElem?_map, List.getElem?_idxOf ‹_›]
    · exact Ty.HasKind.free hk
  | con f ts hf hts =>
    simp only [ofTy]
    apply Ty.HasKind.con hf
    apply List.forall₂_map_left_iff.mpr
    exact forall₂ImplMem hts (fun U _ p hp => encodingTyKind hp xs)
termination_by sizeOf T

mutual
theorem encodingConstraintWF (C : HMX.Constraint) (h : C.WF S)
    (xs : List TVar) (zs : List Id) :
    (ofConstraint xs zs C).WF S (xs.map Prod.fst) zs.length := by
  cases C with
  | truth => trivial
  | falsity => trivial
  | atom p ts =>
    exact ⟨h.1, List.forall₂_map_left_iff.mpr (h.2.imp fun _ _ hk => encodingTyKind hk xs)⟩
  | conj C D => exact ⟨encodingConstraintWF C h.1 xs zs, encodingConstraintWF D h.2 xs zs⟩
  | exists_ A C =>
    refine ⟨?_, ?_⟩
    · intro k hk
      obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hk
      exact h.1 X ((boundNamesMem A X).mp hX)
    · simpa [List.map_append] using encodingConstraintWF C h.2 (boundNames A ++ xs) zs
  | def_ x s C =>
    exact ⟨encodingSchemeWF s h.1 xs zs,
      by simpa using encodingConstraintWF C h.2 xs (x :: zs)⟩
  | inst x T => exact ⟨encodingTyKind h xs, encodingIdBound zs x⟩
theorem encodingSchemeWF (s : HMX.Scheme) (h : s.WF S)
    (xs : List TVar) (zs : List Id) :
    (ofScheme xs zs s).WF S (xs.map Prod.fst) zs.length := by
  cases s with
  | all A C T =>
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hk
      exact h.1 X ((boundNamesMem A X).mp hX)
    · simpa [List.map_append] using encodingConstraintWF C h.2.1 (boundNames A ++ xs) zs
    · simpa [List.map_append] using encodingTyKind h.2.2 (boundNames A ++ xs)
end

theorem encodingExprFpi (t : HMX.Expr) (zs : List Id) :
    (ofExpr zs t).fpi = t.fpi \ zs.toFinset := by
  induction t generalizing zs with
  | ident x =>
    by_cases h : x ∈ zs <;> ext y <;> simp [ofExpr, ofId, h, Expr.fpi, HMX.Expr.fpi] <;> aesop
  | lam z t ih =>
    rw [ofExpr, Expr.fpi, ih]
    ext x
    simp [HMX.Expr.fpi]
    tauto
  | app t u iht ihu =>
    simp [ofExpr, Expr.fpi, HMX.Expr.fpi, iht, ihu, Finset.union_sdiff_distrib]
  | letE z t u iht ihu =>
    rw [ofExpr, Expr.fpi, iht, ihu]
    ext x
    simp [HMX.Expr.fpi]
    tauto

theorem foldUnionDiff {α β : Type} [DecidableEq β] (ts : List α) (f : α → Finset β)
    (A : Finset β) :
    (ts.map (fun t => f t \ A)).foldr (· ∪ ·) ∅ = (ts.map f).foldr (· ∪ ·) ∅ \ A := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [ih, Finset.union_sdiff_distrib]

theorem encodingTyFv (T : HMX.Ty) (xs : List TVar) :
    (ofTy xs T).fv = T.fv \ xs.toFinset := by
  cases T with
  | var X =>
    by_cases h : X ∈ xs <;> ext Y <;> simp [ofTy, h, Ty.fv, HMX.Ty.fv] <;> aesop
  | con f ts =>
    simp only [ofTy, Ty.fv, HMX.Ty.fv, List.map_map, Function.comp_def]
    have hh : ts.map (fun U => (ofTy xs U).fv) = ts.map (fun U => U.fv \ xs.toFinset) :=
      List.map_congr_left (fun U _ => encodingTyFv U xs)
    rw [hh]
    exact foldUnionDiff ts HMX.Ty.fv xs.toFinset
termination_by sizeOf T

mutual
theorem encodingConstraintVars (C : HMX.Constraint) (xs : List TVar) (zs : List Id) :
    (ofConstraint xs zs C).fv = C.fv \ xs.toFinset ∧
    (ofConstraint xs zs C).fpi = C.fpi \ zs.toFinset := by
  cases C with
  | truth => simp [ofConstraint, Constraint.fv, Constraint.fpi, HMX.Constraint.fv, HMX.Constraint.fpi]
  | falsity => simp [ofConstraint, Constraint.fv, Constraint.fpi, HMX.Constraint.fv, HMX.Constraint.fpi]
  | atom p ts =>
    constructor
    · simp only [ofConstraint, Constraint.fv, HMX.Constraint.fv, List.map_map, Function.comp_def]
      rw [List.map_congr_left (fun U (_ : U ∈ ts) => encodingTyFv U xs)]
      exact foldUnionDiff ts HMX.Ty.fv xs.toFinset
    · simp [ofConstraint, Constraint.fpi, HMX.Constraint.fpi]
  | conj C D =>
    obtain ⟨hc, hc'⟩ := encodingConstraintVars C xs zs
    obtain ⟨hd, hd'⟩ := encodingConstraintVars D xs zs
    simp [ofConstraint, Constraint.fv, Constraint.fpi, HMX.Constraint.fv,
      HMX.Constraint.fpi, hc, hc', hd, hd', Finset.union_sdiff_distrib]
  | exists_ A C =>
    obtain ⟨hc, hc'⟩ := encodingConstraintVars C (boundNames A ++ xs) zs
    constructor
    · simp only [ofConstraint, Constraint.fv, HMX.Constraint.fv]
      rw [hc]
      ext X
      simp [boundNamesMem]
      tauto
    · exact hc'
  | def_ x s C =>
    obtain ⟨hs, hs'⟩ := encodingSchemeVars s xs zs
    obtain ⟨hc, hc'⟩ := encodingConstraintVars C xs (x :: zs)
    constructor
    · simp [ofConstraint, Constraint.fv, HMX.Constraint.fv, hs, hc, Finset.union_sdiff_distrib]
    · simp only [ofConstraint, Constraint.fpi, HMX.Constraint.fpi, hs', hc']
      ext y
      simp
      tauto
  | inst x T =>
    constructor
    · exact encodingTyFv T xs
    · by_cases h : x ∈ zs <;> ext y <;>
        simp [ofConstraint, ofId, h, Constraint.fpi, HMX.Constraint.fpi] <;> aesop
theorem encodingSchemeVars (s : HMX.Scheme) (xs : List TVar) (zs : List Id) :
    (ofScheme xs zs s).fv = s.fv \ xs.toFinset ∧
    (ofScheme xs zs s).fpi = s.fpi \ zs.toFinset := by
  cases s with
  | all A C T =>
    obtain ⟨hc, hc'⟩ := encodingConstraintVars C (boundNames A ++ xs) zs
    constructor
    · simp only [ofScheme, Scheme.fv, HMX.Scheme.fv, hc, encodingTyFv]
      ext X
      simp [boundNamesMem]
      tauto
    · exact hc'
end

/-- The first bound occurrence shadows the free interpretation. -/
def encodingLookup {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (xs : List α)
    (free : α → β) (bound : Nat → β) (x : α) : β :=
  if x ∈ xs then bound (xs.idxOf x) else free x

theorem encodingLookupCons {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (xs : List α)
    (free : α → β) (bound : Nat → β) (x y : α) (v : β) :
    encodingLookup (x :: xs) free (push [v] bound) y =
      if y = x then v else encodingLookup xs free bound y := by
  by_cases h : y = x
  · subst y; simp [encodingLookup, push]
  · by_cases hy : y ∈ xs <;> simp [encodingLookup, h, hy, push, Ne.symm h]

theorem encodingLookupAppend {α β : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (bs xs : List α)
    (free named : α → β) (bound : Nat → β) (vs : List β) (hl : vs.length = bs.length)
    (ha : ∀ x, encodingLookup xs free bound x = named x) (x : α) :
    encodingLookup (bs ++ xs) free (push vs bound) x =
      if x ∈ bs then (vs[bs.idxOf x]?).getD (named x) else named x := by
  by_cases hb : x ∈ bs
  · have hi : bs.idxOf x < vs.length := by simpa [hl] using List.idxOf_lt_length_iff.mpr hb
    simp [encodingLookup, hb, List.idxOf_append_of_mem hb, push, hi]
  · rw [ite_eq_right hb]
    rw [← ha x]
    by_cases hx : x ∈ xs
    · simp [encodingLookup, hb, hx, List.idxOf_append_of_notMem hb,
        pushAbove vs bound _ (by omega : vs.length ≤ bs.length + xs.idxOf x), hl]
    · simp [encodingLookup, hb, hx]

theorem encodingTyEval (T : HMX.Ty) (xs : List TVar) (M : Model)
    (ρ ρ' : Assignment M) (β : Nat → M.Carrier)
    (ha : ∀ X, encodingLookup xs ρ β X = ρ' X) :
    (ofTy xs T).evalAt M ρ β = T.eval M ρ' := by
  cases T with
  | var X =>
    by_cases h : X ∈ xs <;>
      simpa [ofTy, Ty.evalAt, HMX.Ty.eval, encodingLookup, h] using ha X
  | con f ts =>
    simp only [ofTy, Ty.evalAt, HMX.Ty.eval, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun U _ => encodingTyEval U xs M ρ ρ' β ha)
termination_by sizeOf T

theorem encodingBlockAgreement (xs : List TVar) (A : Vars) (M : Model)
    (ρ ρ' : Assignment M) (β : Nat → M.Carrier) (vs : List M.Carrier)
    (hl : vs.length = (boundNames A).length)
    (ha : ∀ X, encodingLookup xs ρ β X = ρ' X) :
    ∀ X, encodingLookup (boundNames A ++ xs) ρ (push vs β) X =
      assignBlock (boundNames A) vs ρ' X := by
  intro X
  simpa only [assignBlock] using encodingLookupAppend (boundNames A) xs ρ ρ' β vs hl ha X

theorem encodingWitnessAgreement (xs : List TVar) (A : Vars) (M : Model)
    (ρ ρ' ρ'' : Assignment M) (β : Nat → M.Carrier)
    (ha : ∀ X, encodingLookup xs ρ β X = ρ' X)
    (he : ρ'.AgreeOutside ρ'' A) :
    ∀ X, encodingLookup (boundNames A ++ xs) ρ (push ((boundNames A).map ρ'') β) X = ρ'' X := by
  intro X
  rw [encodingLookupAppend (boundNames A) xs ρ ρ' β _ (by simp) ha X]
  by_cases h : X ∈ boundNames A
  · simp [h, List.getElem?_map]
  · simp only [h, ↓reduceIte]
    exact he X (by simpa [boundNamesMem] using h)

mutual
theorem encodingConstraintSem (C : HMX.Constraint) (hC : C.WF S)
    (xs : List TVar) (zs : List Id) (M : Model)
    (ρ ρ' : Assignment M) (ι ι' : GroundEnv M) (β : Nat → M.Carrier)
    (γ : Nat → Set M.Carrier) (hρ : ρ'.Valid S M)
    (ha : ∀ X, encodingLookup xs ρ β X = ρ' X)
    (hi : ∀ x, encodingLookup zs ι γ x = ι' x) :
    (ofConstraint xs zs C).holdsAt S M ρ ι β γ ↔ C.Holds S M ρ' ι' := by
  cases C with
  | truth => rfl
  | falsity => rfl
  | atom p ts =>
    simp only [ofConstraint, Constraint.holdsAt, HMX.Constraint.Holds, List.map_map, Function.comp_def]
    rw [List.map_congr_left (fun T (_ : T ∈ ts) => encodingTyEval T xs M ρ ρ' β ha)]
  | conj C D =>
    exact and_congr (encodingConstraintSem C hC.1 xs zs M ρ ρ' ι ι' β γ hρ ha hi)
      (encodingConstraintSem D hC.2 xs zs M ρ ρ' ι ι' β γ hρ ha hi)
  | exists_ A C =>
    constructor
    · rintro ⟨vs, hv, hc⟩
      have hv' := List.forall₂_map_right_iff.mp hv
      have hr := assignBlockValid S M ρ' (boundNames A) vs hρ hv'
      refine ⟨assignBlock (boundNames A) vs ρ', hr, ?_, ?_⟩
      · intro X hX
        simp [assignBlock, boundNamesMem, hX]
      · exact (encodingConstraintSem C hC.2 _ zs M ρ _ ι ι' _ γ hr
          (encodingBlockAgreement xs A M ρ ρ' β vs hv'.length_eq ha) hi).mp hc
    · rintro ⟨ρ'', hr, he, hc⟩
      refine ⟨(boundNames A).map ρ'', ?_, ?_⟩
      · apply List.forall₂_map_right_iff.mpr
        exact assignmentBlockKinds S M ρ'' (boundNames A) hr
          (fun X hX => hC.1 X ((boundNamesMem A X).mp hX))
      · exact (encodingConstraintSem C hC.2 _ zs M ρ ρ'' ι ι' _ γ hr
          (encodingWitnessAgreement xs A M ρ ρ' ρ'' β ha he) hi).mpr hc
  | def_ x s C =>
    have hs := encodingSchemeSem s hC.1 xs zs M ρ ρ' ι ι' β γ hρ ha hi
    simp only [ofConstraint, Constraint.holdsAt, HMX.Constraint.Holds, hs]
    apply encodingConstraintSem C hC.2 xs (x :: zs) M ρ ρ' ι _ β _ hρ ha
    intro y
    rw [encodingLookupCons]
    simp only [hi]
  | inst x T =>
    simp only [ofConstraint, HMX.Constraint.Holds]
    have ht := encodingTyEval T xs M ρ ρ' β ha
    have hx := hi x
    by_cases hm : x ∈ zs <;>
      simpa [ofId, hm, Constraint.holdsAt, ht, encodingLookup] using
        (show (T.eval M ρ' ∈ encodingLookup zs ι γ x) ↔ T.eval M ρ' ∈ ι' x from by rw [hx])
theorem encodingSchemeSem (s : HMX.Scheme) (hs : s.WF S)
    (xs : List TVar) (zs : List Id) (M : Model)
    (ρ ρ' : Assignment M) (ι ι' : GroundEnv M) (β : Nat → M.Carrier)
    (γ : Nat → Set M.Carrier) (hρ : ρ'.Valid S M)
    (ha : ∀ X, encodingLookup xs ρ β X = ρ' X)
    (hi : ∀ x, encodingLookup zs ι γ x = ι' x) :
    (ofScheme xs zs s).denoteAt S M ρ ι β γ = s.denote S M ρ' ι' := by
  cases s with
  | all A C T =>
    ext v
    simp only [ofScheme, Scheme.denoteAt, HMX.Scheme.denote, Set.mem_ofPred_eq]
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨vs, hv, hc, ht⟩
      have hv' := List.forall₂_map_right_iff.mp hv
      have hr := assignBlockValid S M ρ' (boundNames A) vs hρ hv'
      have hb := encodingBlockAgreement xs A M ρ ρ' β vs hv'.length_eq ha
      refine ⟨assignBlock (boundNames A) vs ρ', hr, ?_, ?_, ?_⟩
      · intro X hX
        simp [assignBlock, boundNamesMem, hX]
      · exact (encodingConstraintSem C hs.2.1 _ zs M ρ _ ι ι' _ γ hr hb hi).mp hc
      · simpa only [encodingTyEval T _ M ρ _ _ hb] using ht
    · rintro ⟨ρ'', hr, he, hc, ht⟩
      have hb := encodingWitnessAgreement xs A M ρ ρ' ρ'' β ha he
      refine ⟨(boundNames A).map ρ'', ?_, ?_, ?_⟩
      · apply List.forall₂_map_right_iff.mpr
        exact assignmentBlockKinds S M ρ'' (boundNames A) hr
          (fun X hX => hs.1 X ((boundNamesMem A X).mp hX))
      · exact (encodingConstraintSem C hs.2.1 _ zs M ρ ρ'' ι ι' _ γ hr hb hi).mpr hc
      · simpa only [encodingTyEval T _ M ρ ρ'' _ hb] using ht
end

theorem encodingIdCons (zs : List Id) (x y : Id) :
    ofId (x :: zs) y = if y = x then .bound 0 else
      match ofId zs y with
      | .free z => .free z
      | .bound i => .bound (i + 1) := by
  by_cases h : y = x
  · subst y; simp [ofId]
  · by_cases hy : y ∈ zs <;> simp [ofId, h, hy, Ne.symm h]

theorem encodingBindId (zs ws : List Id) (q : Id → Id → Prop)
    (hq : ∀ x y, q x y ↔ ofId zs x = ofId ws y) (x y u v : Id) :
    bindId q x y u v ↔ ofId (x :: zs) u = ofId (y :: ws) v := by
  simp only [bindId, hq, encodingIdCons]
  by_cases hu : u = x <;> by_cases hv : v = y <;> simp [hu, hv]
  all_goals cases ofId zs u <;> cases ofId ws v <;> simp

theorem encodingExprRelated (t u : HMX.Expr) (zs ws : List Id)
    (q : Id → Id → Prop) (hq : ∀ x y, q x y ↔ ofId zs x = ofId ws y) :
    HMX.Expr.Related q t u ↔ ofExpr zs t = ofExpr ws u := by
  induction t generalizing u zs ws q with
  | ident x =>
    cases u <;> simp only [ofExpr, Expr.ident.injEq, reduceCtorEq]
    · exact ⟨fun h => by cases h; exact (hq _ _).mp ‹_›,
        fun h => .ident ((hq _ _).mpr h)⟩
    all_goals constructor <;> intro h <;> cases h
  | lam x t ih =>
    cases u with
    | lam y u =>
      simp only [ofExpr, Expr.lam.injEq]
      constructor
      · intro h; cases h with
        | lam h => exact (ih _ _ _ _ (encodingBindId zs ws q hq (.var x) (.var y))).mp h
      · intro h
        exact .lam ((ih _ _ _ _ (encodingBindId zs ws q hq (.var x) (.var y))).mpr h)
    | ident y | app u v | letE y u v => constructor <;> intro h <;> cases h
  | app t v iht ihv =>
    cases u with
    | app u w =>
      simp only [ofExpr, Expr.app.injEq]
      constructor
      · intro h; cases h with
        | app h h' => exact ⟨(iht _ _ _ _ hq).mp h, (ihv _ _ _ _ hq).mp h'⟩
      · rintro ⟨h, h'⟩; exact .app ((iht _ _ _ _ hq).mpr h) ((ihv _ _ _ _ hq).mpr h')
    | ident y | lam y u | letE y u v => constructor <;> intro h <;> cases h
  | letE x t v iht ihv =>
    cases u with
    | letE y u w =>
      simp only [ofExpr, Expr.letE.injEq]
      constructor
      · intro h; cases h with
        | letE h h' => exact ⟨(iht _ _ _ _ hq).mp h,
            (ihv _ _ _ _ (encodingBindId zs ws q hq (.var x) (.var y))).mp h'⟩
      · rintro ⟨h, h'⟩
        exact .letE ((iht _ _ _ _ hq).mpr h)
          ((ihv _ _ _ _ (encodingBindId zs ws q hq (.var x) (.var y))).mpr h')
    | ident y | lam y u | app u v => constructor <;> intro h <;> cases h

theorem encodingTyRename (T : HMX.Ty) (pre as bs xs : List TVar) (p : Nat → Nat)
    (hl : as.length = bs.length) (hm : ∀ X, X ∈ as ↔ X ∈ bs)
    (hp : ∀ X ∈ as, p (as.idxOf X) = bs.idxOf X)
    (ho : ∀ i, as.length ≤ i → p i = i) :
    (ofTy (pre ++ as ++ xs) T).renameAt pre.length p = ofTy (pre ++ bs ++ xs) T := by
  cases T with
  | var X =>
    by_cases hpre : X ∈ pre
    · have hi := List.idxOf_lt_length_iff.mpr hpre
      simp [ofTy, hpre, List.idxOf_append_of_mem hpre, Ty.renameAt, hi]
    · by_cases ha : X ∈ as
      · have hb := (hm X).mp ha
        simp [ofTy, hpre, ha, hb, List.idxOf_append_of_mem ha, List.idxOf_append_of_mem hb,
          List.idxOf_append_of_notMem hpre, Ty.renameAt, hp X ha]
      · have hb : X ∉ bs := fun h => ha ((hm X).mpr h)
        by_cases hx : X ∈ xs
        · simp [ofTy, hpre, ha, hb, hx, List.idxOf_append_of_notMem,
            Ty.renameAt, hl, ho (bs.length + xs.idxOf X) (by omega)]
        · simp [ofTy, hpre, ha, hb, hx, Ty.renameAt]
  | con f ts =>
    simp only [ofTy, Ty.renameAt, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun U _ => encodingTyRename U pre as bs xs p hl hm hp ho)
termination_by sizeOf T

mutual
theorem encodingConstraintRename (C : HMX.Constraint) (pre as bs xs : List TVar)
    (zs : List Id) (p : Nat → Nat) (hl : as.length = bs.length)
    (hm : ∀ X, X ∈ as ↔ X ∈ bs) (hp : ∀ X ∈ as, p (as.idxOf X) = bs.idxOf X)
    (ho : ∀ i, as.length ≤ i → p i = i) :
    (ofConstraint (pre ++ as ++ xs) zs C).mapTypes (fun d T => T.renameAt d p) pre.length =
      ofConstraint (pre ++ bs ++ xs) zs C := by
  cases C with
  | truth => rfl
  | falsity => rfl
  | atom q ts =>
    simp only [ofConstraint, Constraint.mapTypes, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun T _ => encodingTyRename T pre as bs xs p hl hm hp ho)
  | conj C D =>
    simp only [ofConstraint, Constraint.mapTypes]
    rw [encodingConstraintRename C pre as bs xs zs p hl hm hp ho,
      encodingConstraintRename D pre as bs xs zs p hl hm hp ho]
  | exists_ A C =>
    simp only [ofConstraint, Constraint.mapTypes]
    congr 1
    simpa [List.append_assoc, List.length_append, Nat.add_comm] using
      encodingConstraintRename C (boundNames A ++ pre) as bs xs zs p hl hm hp ho
  | def_ x s C =>
    simp only [ofConstraint, Constraint.mapTypes]
    rw [encodingSchemeRename s pre as bs xs zs p hl hm hp ho,
      encodingConstraintRename C pre as bs xs (x :: zs) p hl hm hp ho]
  | inst x T =>
    simp only [ofConstraint, Constraint.mapTypes]
    rw [encodingTyRename T pre as bs xs p hl hm hp ho]
theorem encodingSchemeRename (s : HMX.Scheme) (pre as bs xs : List TVar)
    (zs : List Id) (p : Nat → Nat) (hl : as.length = bs.length)
    (hm : ∀ X, X ∈ as ↔ X ∈ bs) (hp : ∀ X ∈ as, p (as.idxOf X) = bs.idxOf X)
    (ho : ∀ i, as.length ≤ i → p i = i) :
    (ofScheme (pre ++ as ++ xs) zs s).mapTypes (fun d T => T.renameAt d p) pre.length =
      ofScheme (pre ++ bs ++ xs) zs s := by
  cases s with
  | all A C T =>
    simp only [ofScheme, Scheme.mapTypes]
    congr 1
    · simpa [List.append_assoc, List.length_append, Nat.add_comm] using
        encodingConstraintRename C (boundNames A ++ pre) as bs xs zs p hl hm hp ho
    · simpa [List.append_assoc, List.length_append, Nat.add_comm] using
        encodingTyRename T (boundNames A ++ pre) as bs xs p hl hm hp ho
end

def encodingPermutation (as bs : List TVar) (i : Nat) : Nat :=
  if h : i < as.length then bs.idxOf as[i] else i

theorem encodingPermutationIndex (as bs : List TVar) (X : TVar) (h : X ∈ as) :
    encodingPermutation as bs (as.idxOf X) = bs.idxOf X := by
  have hi := List.idxOf_lt_length_iff.mpr h
  simp [encodingPermutation, hi, List.getElem_idxOf hi]

theorem encodingPermutationInverse (as bs : List TVar) (ha : as.Nodup)
    (hl : as.length = bs.length) (hm : ∀ X, X ∈ as ↔ X ∈ bs) (i : Nat) :
    encodingPermutation bs as (encodingPermutation as bs i) = i := by
  by_cases hi : i < as.length
  · have hx : as[i] ∈ bs := (hm _).mp (List.getElem_mem hi)
    have he : encodingPermutation as bs i = bs.idxOf as[i] := by simp [encodingPermutation, hi]
    rw [he, encodingPermutationIndex bs as _ hx]
    exact ha.idxOf_getElem i hi
  · have hi' : ¬ i < bs.length := by omega
    simp [encodingPermutation, hi, hi']

theorem encodingPermutationBlock (as bs : List TVar) (ha : as.Nodup) (hb : bs.Nodup)
    (hm : ∀ X, X ∈ as ↔ X ∈ bs) :
    BlockPermutation (as.map Prod.fst) (bs.map Prod.fst) (encodingPermutation as bs) := by
  have he : as.toFinset = bs.toFinset := by ext X; simpa using hm X
  have hl := (List.perm_of_nodup_nodup_toFinset_eq ha hb he).length_eq
  refine ⟨by simpa using hl, ?_, ?_, ?_⟩
  · apply Function.bijective_iff_has_inverse.mpr
    exact ⟨encodingPermutation bs as, encodingPermutationInverse as bs ha hl hm,
      encodingPermutationInverse bs as hb hl.symm (fun X => (hm X).symm)⟩
  · intro i hi
    simp only [List.length_map] at hi
    simp [encodingPermutation, Nat.not_lt.mpr hi]
  · intro i
    by_cases hi : i < as.length
    · have hx : as[i] ∈ bs := (hm _).mp (List.getElem_mem hi)
      simp [encodingPermutation, hi, List.getElem?_map, List.getElem?_idxOf hx]
    · have hi' : ¬ i < bs.length := by omega
      simp [encodingPermutation, hi, List.getElem?_map, List.getElem?_eq_none (by omega : bs.length ≤ i)]

/-- Order the left bound names according to their partners on the right. -/
theorem encodingBindsAlignment (h : Binds r r' A B) :
    ∃ as : List TVar, as.Nodup ∧ as.toFinset = A ∧
      as.map Prod.fst = (boundNames B).map Prod.fst ∧
      (∀ X Y, X ∈ A → Y ∈ B → r' X Y → as.idxOf X = (boundNames B).idxOf Y) := by
  classical
  let f : TVar → TVar := fun Y => if hy : Y ∈ B then (h.2.1 Y hy).choose else Y
  have hf (Y : TVar) (hy : Y ∈ B) : f Y ∈ A ∧ (f Y).1 = Y.1 ∧ r' (f Y) Y := by
    simpa only [f, dite_eq_left hy] using (h.2.1 Y hy).choose_spec.1
  have hfinj : ∀ Y ∈ boundNames B, ∀ Z ∈ boundNames B, f Y = f Z → Y = Z := by
    intro Y hY Z hZ he
    have hy := hf Y ((boundNamesMem B Y).mp hY)
    have hz := hf Z ((boundNamesMem B Z).mp hZ)
    obtain ⟨W, _, hu⟩ := h.1 (f Y) hy.1
    exact (hu Y ⟨(boundNamesMem B Y).mp hY, hy.2⟩).trans
      (hu Z ⟨(boundNamesMem B Z).mp hZ, by simpa only [he] using hz.2⟩).symm
  let as := (boundNames B).map f
  have hn : as.Nodup := List.Nodup.map_on hfinj (boundNamesNodup B)
  refine ⟨as, hn, ?_, ?_, ?_⟩
  · ext X
    simp only [List.mem_toFinset, as, List.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩; exact (hf Y ((boundNamesMem B Y).mp hY)).1
    · intro hX
      obtain ⟨Y, hy, _⟩ := h.1 X hX
      have hfY := hf Y hy.1
      obtain ⟨Z, _, hu⟩ := h.2.1 Y hy.1
      have he := (hu (f Y) hfY).trans (hu X ⟨hX, hy.2⟩).symm
      exact ⟨Y, (boundNamesMem B Y).mpr hy.1, he⟩
  · simp only [as, List.map_map, Function.comp_def]
    exact List.map_congr_left (fun Y hY => (hf Y ((boundNamesMem B Y).mp hY)).2.1)
  · intro X Y hX hY hr
    obtain ⟨Z, _, hu⟩ := h.2.1 Y hY
    have hkind : X.1 = Y.1 := by
      rcases (h.2.2 X Y).mp hr with hb | hb
      · exact hb.2.2.1
      · exact False.elim (hb.1 hX)
    have he : f Y = X := (hu (f Y) (hf Y hY)).trans (hu X ⟨hX, hkind, hr⟩).symm
    have hi := List.idxOf_lt_length_iff.mpr ((boundNamesMem B Y).mpr hY)
    have hg : as[(boundNames B).idxOf Y]'(by simpa [as] using hi) = X := by
      simp [as, List.getElem_idxOf hi, he]
    rw [← hg]
    exact hn.idxOf_getElem _ _

theorem encodingTyAppendOutside (as xs : List TVar) (X : TVar) (h : X ∉ as) :
    ofTy (as ++ xs) (.var X) = (ofTy xs (.var X)).shift as.length 0 := by
  by_cases hx : X ∈ xs <;>
    simp [ofTy, h, hx, List.idxOf_append_of_notMem h, Ty.shift, Nat.add_comm]

theorem encodingBindsTypes (h : Binds r r' A B) (as : List TVar)
    (hm : as.toFinset = A) (hk : as.map Prod.fst = (boundNames B).map Prod.fst)
    (hp : ∀ X Y, X ∈ A → Y ∈ B → r' X Y → as.idxOf X = (boundNames B).idxOf Y)
    (xs ys : List TVar)
    (hr : ∀ X Y, r X Y → ofTy xs (.var X) = ofTy ys (.var Y)) :
    ∀ X Y, r' X Y → ofTy (as ++ xs) (.var X) = ofTy (boundNames B ++ ys) (.var Y) := by
  intro X Y hxy
  rcases (h.2.2 X Y).mp hxy with ⟨hX, hY, _, _⟩ | ⟨hX, hY, hxy'⟩
  · have hx : X ∈ as := by simpa only [← hm, List.mem_toFinset] using hX
    have hy := (boundNamesMem B Y).mpr hY
    simp [ofTy, hx, hy, List.idxOf_append_of_mem hx, List.idxOf_append_of_mem hy, hp X Y hX hY hxy]
  · have hx : X ∉ as := by simpa only [← hm, List.mem_toFinset] using hX
    have hy : Y ∉ boundNames B := by simpa only [boundNamesMem] using hY
    rw [encodingTyAppendOutside as xs X hx, encodingTyAppendOutside _ ys Y hy, hr X Y hxy']
    have hl := congrArg List.length hk
    simp only [List.length_map] at hl
    rw [hl]

theorem encodingTyRelated (h : HMX.Ty.Related r T U) (xs ys : List TVar)
    (hr : ∀ X Y, r X Y → ofTy xs (.var X) = ofTy ys (.var Y)) : ofTy xs T = ofTy ys U := by
  cases h with
  | var h => exact hr _ _ h
  | @con ts us f hs =>
    simp only [ofTy]
    congr 1
    apply List.ext_getElem
    · simpa using hs.length_eq
    · intro i hi hj
      obtain ⟨T, ht, hh⟩ := forall₂Lookup hs i _ (List.getElem?_eq_getElem (by simpa using hj))
      have hi' : i < ts.length := by simpa using hi
      have hte := List.getElem?_eq_getElem hi'
      rw [hte] at ht
      cases Option.some.inj ht
      have hm : ts[i] ∈ ts := List.getElem_mem hi'
      simpa using encodingTyRelated hh xs ys hr
termination_by sizeOf T

theorem encodingBindIdForward (zs ws : List Id) (q : Id → Id → Prop)
    (hq : ∀ x y, q x y → ofId zs x = ofId ws y) (x y u v : Id)
    (h : bindId q x y u v) : ofId (x :: zs) u = ofId (y :: ws) v := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hu, hv, h⟩
  · simp [encodingIdCons]
  · simp only [encodingIdCons, hu, hv, ↓reduceIte, hq u v h]

theorem encodingRelatedTypes (h : List.Forall₂ (HMX.Ty.Related r) ts us) (xs ys : List TVar)
    (hr : ∀ X Y, r X Y → ofTy xs (.var X) = ofTy ys (.var Y)) :
    ts.map (ofTy xs) = us.map (ofTy ys) := by
  rw [← List.forall₂_eq_eq_eq]
  apply List.forall₂_map_left_iff.mpr
  apply List.forall₂_map_right_iff.mpr
  exact h.imp (fun _ _ hh => encodingTyRelated hh xs ys hr)

mutual
theorem encodingConstraintRelated (h : HMX.Constraint.Related r q C D)
    (xs ys : List TVar) (zs ws : List Id)
    (hr : ∀ X Y, r X Y → ofTy xs (.var X) = ofTy ys (.var Y))
    (hq : ∀ x y, q x y → ofId zs x = ofId ws y) :
    (ofConstraint xs zs C).BinderEq (ofConstraint ys ws D) := by
  cases h with
  | truth => exact .refl
  | falsity => exact .refl
  | atom h =>
    simp only [ofConstraint, encodingRelatedTypes h xs ys hr]
    exact .refl
  | conj h h' =>
    exact .conj (encodingConstraintRelated h xs ys zs ws hr hq)
      (encodingConstraintRelated h' xs ys zs ws hr hq)
  | @exists_ r r' A B q C D hb hc =>
    obtain ⟨as, hn, hm, hk, hi⟩ := encodingBindsAlignment hb
    have he : ∀ X, X ∈ boundNames A ↔ X ∈ as := by
      intro X; rw [boundNamesMem, ← hm, List.mem_toFinset]
    have hp := encodingPermutationBlock (boundNames A) as (boundNamesNodup A) hn he
    have hl : (boundNames A).length = as.length := by simpa using hp.1
    have hp' := encodingPermutationIndex (boundNames A) as
    have ho : ∀ i, (boundNames A).length ≤ i → encodingPermutation (boundNames A) as i = i := by
      intro i h; exact hp.2.2.1 i (by simpa using h)
    apply Constraint.BinderEq.exists_ (p := encodingPermutation (boundNames A) as)
    · simpa only [hk] using hp
    · rw [show (ofConstraint (boundNames A ++ xs) zs C).mapTypes
          (fun d T => T.renameAt d (encodingPermutation (boundNames A) as)) 0 =
          ofConstraint (as ++ xs) zs C from
          encodingConstraintRename C [] (boundNames A) as xs zs _ hl he hp' ho]
      exact encodingConstraintRelated hc _ _ zs ws (encodingBindsTypes hb as hm hk hi xs ys hr) hq
  | @def_ x y r q s s' C D hb hs hc =>
    have he : Binder.ofId x = Binder.ofId y := by
      rcases hb with rfl | ⟨a, b, rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩ <;> rfl
    simp only [ofConstraint, he]
    exact .def_ (encodingSchemeRelated hs xs ys zs ws hr hq)
      (encodingConstraintRelated hc xs ys (x :: zs) (y :: ws) hr
        (encodingBindIdForward zs ws q hq x y))
  | inst hx ht =>
    simp only [ofConstraint, hq _ _ hx, encodingTyRelated ht xs ys hr]
    exact .refl
termination_by sizeOf C
theorem encodingSchemeRelated (h : HMX.Scheme.Related r q s u)
    (xs ys : List TVar) (zs ws : List Id)
    (hr : ∀ X Y, r X Y → ofTy xs (.var X) = ofTy ys (.var Y))
    (hq : ∀ x y, q x y → ofId zs x = ofId ws y) :
    (ofScheme xs zs s).BinderEq (ofScheme ys ws u) := by
  cases h with
  | @all r r' A B q C D T U hb hc ht =>
    obtain ⟨as, hn, hm, hk, hi⟩ := encodingBindsAlignment hb
    have he : ∀ X, X ∈ boundNames A ↔ X ∈ as := by
      intro X; rw [boundNamesMem, ← hm, List.mem_toFinset]
    have hp := encodingPermutationBlock (boundNames A) as (boundNamesNodup A) hn he
    have hl : (boundNames A).length = as.length := by simpa using hp.1
    have hp' := encodingPermutationIndex (boundNames A) as
    have ho : ∀ i, (boundNames A).length ≤ i → encodingPermutation (boundNames A) as i = i := by
      intro i h; exact hp.2.2.1 i (by simpa using h)
    apply Scheme.BinderEq.all (p := encodingPermutation (boundNames A) as)
    · simpa only [hk] using hp
    · rw [show (ofConstraint (boundNames A ++ xs) zs C).mapTypes
          (fun d T => T.renameAt d (encodingPermutation (boundNames A) as)) 0 =
          ofConstraint (as ++ xs) zs C from
          encodingConstraintRename C [] (boundNames A) as xs zs _ hl he hp' ho]
      exact encodingConstraintRelated hc _ _ zs ws (encodingBindsTypes hb as hm hk hi xs ys hr) hq
    · rw [show (ofTy (boundNames A ++ xs) T).renameAt 0 (encodingPermutation (boundNames A) as) =
          ofTy (as ++ xs) T from encodingTyRename T [] (boundNames A) as xs _ hl he hp' ho]
      exact encodingTyRelated ht _ _ (encodingBindsTypes hb as hm hk hi xs ys hr)
termination_by sizeOf s
end

end HMX.LN.Proofs
