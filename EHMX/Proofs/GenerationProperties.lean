import EHMX.Proofs.InferenceEnvironment
import EHMX.Proofs.TypeSubstitution

namespace EHMX

/-- Substitution of the outer type/effect context commutes with generation.
Declaration parameters and the fresh binders introduced by generation stay local. -/
theorem generationSubstitution (hsig : OpSignature.WF S sig) (e : Expr)
    (T : Ty) (ε : Effect) (σ : BoundSubst) :
    (generate sig e T ε).substBound σ =
      generate sig e (T.substBound σ) (ε.substBound σ) := by
  induction e generalizing T ε σ with
  | ident x => simp [generate, Constraint.substBound, Constraint.le, Ty.empty, Ty.substBound]
  | lam body ih =>
      simp only [generate, Constraint.substBound, Scheme.substBound, Scheme.mono,
        resultConstraint, Constraint.le, Ty.arrow, Ty.empty, Ty.substBound,
        List.map_cons, List.map_nil, List.length_cons, List.length_nil]
      rw [ih]
      simp [BoundSubst.lift, tyShiftLiftSubst, Ty.substBound]
  | app f x ihf ihx =>
      simp only [generate, Constraint.substBound, Constraint.le,
        List.map_cons, List.map_nil, List.length_cons, List.length_nil]
      rw [ihf, ihx]
      simp [Ty.arrow, Ty.union, Ty.substBound, BoundSubst.lift, tyShiftLiftSubst]
  | letE rhs body ihr ihb =>
      simp only [generate]
      split
      · simp only [Constraint.letBound, Scheme.exists_, Constraint.substBound,
          Scheme.substBound, List.length_cons, List.length_nil]
        rw [ihr, ihb]
        simp [Ty.substBound, BoundSubst.lift, Ty.empty]
      · simp only [Constraint.substBound, Scheme.mono, Scheme.substBound,
          Constraint.le, Ty.substBound, List.map_cons, List.map_nil,
          List.length_cons, List.length_nil]
        rw [ihr, ihb]
        simp [Ty.union, Ty.substBound, BoundSubst.lift, tyShiftLiftSubst]
  | perform op arg ih =>
      simp only [generate]
      split
      · rfl
      · rename_i decl hd
        have hw := hsig op decl hd
        simp only [Constraint.substBound, resultConstraint, Constraint.le, List.map_cons, List.map_nil]
        rw [declarationConditionSubstBound (constraintAppendWF hw.2.2.2.2.2.1 [1]),
          ih, declarationSubstBound (kindAppend hw.2.1 [1]),
          declarationSubstBound (kindAppend hw.2.2.1 [1])]
        simp [Ty.union, Ty.singleton, Ty.substBound, BoundSubst.lift,
          tyShiftLiftSubst]
  | handle body op ret clause ihb ihr ihc =>
      simp only [generate]
      split
      · rfl
      · rename_i decl hd
        have hw := hsig op decl hd
        simp only [Constraint.substBound, Scheme.substBound, Scheme.mono,
          resultConstraint, Constraint.le, Ty.substBound, List.map_cons,
          List.map_nil, List.length_cons, List.length_nil]
        rw [ihb, ihr, ihc]
        simp only [BoundSubst.liftZero, declarationConditionSubstBound hw.2.2.2.2.2.1, declarationSubstBound hw.2.1,
          Ty.arrow, Ty.substBound, List.map_cons, List.map_nil,
          declarationSubstBound hw.2.2.1, tyShiftLiftSubst]
        simp [Ty.union, Ty.singleton, Ty.substBound, BoundSubst.lift]


/-- A valid ground environment is upward closed at every variable, including
missing bound variables (whose interpretation is empty). -/
theorem GroundEnv.lookupUpperSet {ι : GroundEnv M} (hι : ι.Valid) (x : PVar) :
    UpperSet M (ι.lookup x) := by
  cases x with
  | free x => exact hι.1 x
  | bound i =>
      cases hi : ι.bound[i]? with
      | none => simp [GroundEnv.lookup, hi, UpperSet]
      | some s =>
          simpa [GroundEnv.lookup, hi] using hι.2 s (List.mem_of_getElem? hi)

/-- Values can always be generated at the empty evaluation effect. This is about
constraint generation; `valuePure` is its separate typing counterpart. -/
theorem generationValuePure (hF : EffectFramework S M) (hv : Value e)
    (h : (generate sig e T ε).Holds M ρ bs ι) :
    (generate sig e T .empty).Holds M ρ bs ι := by
  have he : M.kind (Ty.empty.eval M ρ bs) = 1 :=
    by simpa only [Ty.empty, Ty.eval, List.map_nil, Symbol.result] using
      hF.constructorKind .empty trivial [] .nil
  have hr : M.below 1 (Ty.empty.eval M ρ bs) (Ty.empty.eval M ρ bs) :=
    hF.belowRefl 1 hF.signature.2.1 _ he
  cases e with
  | ident x => exact ⟨h.1, he, he, hr⟩
  | lam body =>
      obtain ⟨vs, hv, hb, ht, _⟩ := h
      refine ⟨vs, hv, hb, ht, ?_⟩
      have he' : M.kind (Ty.empty.eval M ρ (vs ++ bs)) = 1 :=
        by simpa only [Ty.empty, Ty.eval, List.map_nil, Symbol.result] using
      hF.constructorKind .empty trivial [] .nil
      simpa only [Ty.empty, Ty.shift, List.map_nil] using
        (show (Constraint.le 1 .empty .empty).Holds M ρ (vs ++ bs) ι from
          ⟨he', he', hF.belowRefl 1 hF.signature.2.1 _ he'⟩)
  | app _ _ | letE _ _ | perform _ _ | handle _ _ _ _ => cases hv

/-- Every scheme generated for a binder denotes an upper set. The type of this
scheme is its first bound type variable, so no representability assumption on
semantic witnesses is needed. -/
theorem boundTypeSchemeUpperSet (hF : EffectFramework S M) (D : Constraint)
    (ρ : Assignment M) (bs : List M.Carrier) (ι : GroundEnv M) :
    UpperSet M ((Scheme.all [0] D (.bound 0)).denote M ρ bs ι) := by
  refine ⟨fun _ h => h.1, ?_⟩
  rintro a ⟨ha, vs, hv, hD, hTa⟩ b hb hab
  refine ⟨hb, vs, hv, hD, ?_⟩
  cases hv with
  | cons hv hvnil =>
      cases hvnil
      exact hF.belowTrans 0 hF.signature.1 _ _ _
        (by simpa [Ty.eval] using hv) ha hb hTa hab

/-- Increasing the expected type and evaluation-effect bounds preserves the
generated constraint. Used by the `sub` case of inference completeness. -/
theorem generationMonotone (hF : EffectFramework S M) (e : Expr)
    (hι : GroundEnv.Valid ι)
    (hTU : (Constraint.le 0 T U).Holds M ρ bs ι)
    (hεη : (Constraint.le 1 ε η).Holds M ρ bs ι)
    (h : (generate sig e T ε).Holds M ρ bs ι) :
    (generate sig e U η).Holds M ρ bs ι := by
  induction e generalizing T U ε η bs ι with
  | ident x =>
      exact ⟨(GroundEnv.lookupUpperSet hι x).2 _ h.1 _ hTU.2.1 hTU.2.2,
        ⟨h.2.1, hεη.2.1, hF.belowTrans 1 hF.signature.2.1 _ _ _
          h.2.1 h.2.2.1 hεη.2.1 h.2.2.2 hεη.2.2⟩⟩
  | lam body ih =>
      obtain ⟨vs, hv, hb, ht, he⟩ := h
      have hn := hv.length_eq
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hn
      have ht' : (Constraint.le 0 (T.shift 3 0) (U.shift 3 0)).Holds M ρ (vs ++ bs) ι := by
        simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
          List.map_nil, ← hn, evalShift] using hTU
      have he' : (Constraint.le 1 (ε.shift 3 0) (η.shift 3 0)).Holds M ρ (vs ++ bs) ι := by
        simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
          List.map_nil, ← hn, evalShift] using hεη
      refine ⟨vs, hv, hb, ?_, ?_⟩
      · exact ⟨ht.1, ht'.2.1, hF.belowTrans 0 hF.signature.1 _ _ _ ht.1 ht.2.1
          ht'.2.1 ht.2.2 ht'.2.2⟩
      · exact ⟨he.1, he'.2.1, hF.belowTrans 1 hF.signature.2.1 _ _ _ he.1 he.2.1
          he'.2.1 he.2.2 he'.2.2⟩
  | app f x ihf ihx =>
      obtain ⟨vs, hv, hf, hx, he⟩ := h
      have hn := hv.length_eq
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hn
      have ht' : (Constraint.le 0 (T.shift 4 0) (U.shift 4 0)).Holds M ρ (vs ++ bs) ι := by
        simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
          List.map_nil, ← hn, evalShift] using hTU
      have he' : (Constraint.le 1 (ε.shift 4 0) (η.shift 4 0)).Holds M ρ (vs ++ bs) ι := by
        simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
          List.map_nil, ← hn, evalShift] using hεη
      cases hv with | cons ha hv =>
       cases hv with | cons hη hv =>
        cases hv with | cons hef hv =>
         cases hv with | cons hex hv =>
          cases hv
          refine ⟨_, .cons ha (.cons hη (.cons hef (.cons hex .nil))), ?_, hx, ?_⟩
          · apply ihf hι _ _ hf
            · have ka := hF.constructorKind .arrow trivial _ (.cons ha (.cons hη (.cons ht'.1 .nil)))
              have kb := hF.constructorKind .arrow trivial _ (.cons ha (.cons hη (.cons ht'.2.1 .nil)))
              simp only [Constraint.le, Constraint.Holds, Predicate.eval, Ty.arrow, Ty.eval,
                List.map_cons, List.map_nil, List.cons_append, List.getElem?_cons_zero,
                List.getElem?_cons_succ, Option.getD_some]
              exact ⟨ka, kb, (hF.arrowOrder _ _ _ _ _ _ ha hη ht'.1 ha hη ht'.2.1).mpr
                ⟨hF.belowRefl 0 hF.signature.1 _ ha,
                  hF.belowRefl 1 hF.signature.2.1 _ hη, ht'.2.2⟩⟩
            · simpa [Constraint.le, Constraint.Holds, Predicate.eval, Ty.eval] using
                And.intro hef (And.intro hef (hF.belowRefl 1 hF.signature.2.1 _ hef))
          · exact ⟨he.1, he'.2.1, hF.belowTrans 1 hF.signature.2.1 _ _ _ he.1 he.2.1
              he'.2.1 he.2.2 he'.2.2⟩
  | letE rhs body ihr ihb =>
      simp only [generate] at h ⊢
      split <;> simp only [*] at h
      · exact ⟨h.1, ihb
          (GroundEnv.validPush hι (boundTypeSchemeUpperSet hF _ ρ bs ι)) hTU hεη h.2⟩
      · obtain ⟨vs, hv, hr, hb, he⟩ := h
        have hn := hv.length_eq
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hn
        have ht' : (Constraint.le 0 (T.shift 3 0) (U.shift 3 0)).Holds M ρ (vs ++ bs) ι := by
          simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
            List.map_nil, ← hn, evalShift] using hTU
        have he' : (Constraint.le 1 (ε.shift 3 0) (η.shift 3 0)).Holds M ρ (vs ++ bs) ι := by
          simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
            List.map_nil, ← hn, evalShift] using hεη
        cases hv with | cons ha hv =>
         cases hv with | cons her hv =>
          cases hv with | cons heb hv =>
           cases hv
           refine ⟨_, .cons ha (.cons her (.cons heb .nil)), hr, ?_, ?_⟩
           · simp only [Constraint.Holds] at hb ⊢
             apply ihb (ι := ι.push _) _ (by exact ht') _ hb
             · apply GroundEnv.validPush hι
               refine ⟨fun _ h => h.1, ?_⟩
               rintro a ⟨hka, vs, hv, _, hAa⟩ b hkb hab
               cases hv
               exact ⟨hkb, [], .nil, trivial,
                 hF.belowTrans 0 hF.signature.1 _ _ _ (by simpa [Ty.eval] using ha) hka hkb hAa hab⟩
             · simpa [Constraint.le, Constraint.Holds, Predicate.eval, Ty.eval] using
                 And.intro heb (And.intro heb (hF.belowRefl 1 hF.signature.2.1 _ heb))
           · exact ⟨he.1, he'.2.1, hF.belowTrans 1 hF.signature.2.1 _ _ _ he.1 he.2.1
               he'.2.1 he.2.2 he'.2.2⟩
  | perform op arg ih =>
      simp only [generate] at h ⊢
      split <;> simp only [*] at h
      · exact h
      · rename_i decl hd
        obtain ⟨vs, hv, hp, ha, ht, he⟩ := h
        have hn := hv.length_eq
        simp only [List.length_append, List.length_cons, List.length_nil] at hn
        have ht' : (Constraint.le 0 (T.shift (decl.kinds.length + 1) 0)
            (U.shift (decl.kinds.length + 1) 0)).Holds M ρ (vs ++ bs) ι := by
          simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
            List.map_nil, List.length_append, List.length_cons, List.length_nil, ← hn,
            evalShift] using hTU
        have he' : (Constraint.le 1 (ε.shift (decl.kinds.length + 1) 0)
            (η.shift (decl.kinds.length + 1) 0)).Holds M ρ (vs ++ bs) ι := by
          simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
            List.map_nil, List.length_append, List.length_cons, List.length_nil, ← hn,
            evalShift] using hεη
        exact ⟨vs, hv, hp, ha,
          ⟨ht.1, ht'.2.1, hF.belowTrans 0 hF.signature.1 _ _ _ ht.1 ht.2.1 ht'.2.1 ht.2.2 ht'.2.2⟩,
          ⟨he.1, he'.2.1, hF.belowTrans 1 hF.signature.2.1 _ _ _ he.1 he.2.1 he'.2.1 he.2.2 he'.2.2⟩⟩
  | handle body op ret clause ihb ihr ihc =>
      simp only [generate] at h ⊢
      split <;> simp only [*] at h
      · exact h
      · obtain ⟨vs, hv, hb, hi, hr, hc, ht, he⟩ := h
        have hn := hv.length_eq
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hn
        have ht' : (Constraint.le 0 (T.shift 4 0) (U.shift 4 0)).Holds M ρ (vs ++ bs) ι := by
          simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
            List.map_nil, ← hn, evalShift] using hTU
        have he' : (Constraint.le 1 (ε.shift 4 0) (η.shift 4 0)).Holds M ρ (vs ++ bs) ι := by
          simpa only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons,
            List.map_nil, ← hn, evalShift] using hεη
        exact ⟨vs, hv, hb, hi, hr, hc,
          ⟨ht.1, ht'.2.1, hF.belowTrans 0 hF.signature.1 _ _ _ ht.1 ht.2.1 ht'.2.1 ht.2.2 ht'.2.2⟩,
          ⟨he.1, he'.2.1, hF.belowTrans 1 hF.signature.2.1 _ _ _ he.1 he.2.1 he'.2.1 he.2.2 he'.2.2⟩⟩


/-- Shifting external type/effect variables leaves generation's internal binders
in place. This is used when introducing and eliminating existential witnesses. -/
theorem generationShift (hsig : OpSignature.WF S sig) (e : Expr)
    (T : Ty) (ε : Effect) (n : Nat) :
    (generate sig e T ε).shift n 0 =
      generate sig e (T.shift n 0) (ε.shift n 0) := by
  rw [shiftSubstBound.1, generationSubstitution hsig]
  simp only [tyShiftSubstBound]

theorem generationShiftHolds (hS : S.WF) (hsig : OpSignature.WF S sig)
    (he : Expr.LCAt n e) (hT : Ty.HasKind S Δ T 0) (hε : Ty.HasKind S Δ ε 1)
    (ρ : Assignment M) (bs vs : List M.Carrier) (ι : GroundEnv M) :
    (generate sig e (T.shift vs.length 0) (ε.shift vs.length 0)).Holds M ρ (vs ++ bs) ι ↔
      (generate sig e T ε).Holds M ρ bs ι := by
  rw [← generationShift hsig]
  exact constraintShiftHolds (generationWF hS hsig he hT hε) ρ bs vs ι

/-- The raw generated let scheme is closed by including the outer environment. -/
def generatedScheme (sig : OpSignature) (Γ : Env) (rhs : Expr) : Scheme :=
  .all [0] (infer sig (Γ.shift 1) rhs (.bound 0) .empty) (.bound 0)

theorem generatedSchemeWF (hS : S.WF) (hsig : OpSignature.WF S sig)
    (hΓ : Env.WF S Δ Γ) (he : Expr.Scoped Γ rhs) :
    (generatedScheme sig Γ rhs).WF S Δ 0 := by
  refine ⟨by simp [hS.1], ?_, .bound rfl hS.1⟩
  apply inferWF hS hsig (envShiftWF hΓ [0])
  · simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def] using he
  · exact .bound rfl hS.1
  · exact emptyKind hS

theorem generatedSchemeScope (hsig : OpSignature.WF S sig) (hΓ : Env.WF S Δ Γ) (he : Expr.Scoped Γ rhs)
    (hd : rhs.Declared sig) : (generatedScheme sig Γ rhs).fpi = ∅ := by
  apply inferScope hsig (envShiftWF hΓ [0]) _ hd
  simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def] using he

/-- Closing a generated scheme preserves its interpretation whenever the outer
environment is feasible. This is the value-let case of environment duplication. -/
theorem generatedSchemeDenote (hΓ : Env.WF S Δ Γ)
    (hΓe : Γ.exists_.Holds M ρ bs ι) :
    (generatedScheme sig Γ rhs).denote M ρ bs ι =
      (Scheme.all [0] (generate sig rhs (.bound 0) .empty) (.bound 0)).denote
        M ρ bs (Γ.interpret M ρ bs ι) := by
  ext v
  change (_ ∧ ∃ vs, KindValues M [0] vs ∧ _ ∧ _) ↔
    (_ ∧ ∃ vs, KindValues M [0] vs ∧ _ ∧ _)
  apply and_congr_right
  intro _
  apply exists_congr
  intro vs
  apply and_congr_right
  intro hv
  apply and_congr _ Iff.rfl
  rw [infer, envLetInHolds]
  have hn : vs.length = 1 := hv.length_eq
  have hΓe' : (Γ.shift 1).exists_.Holds M ρ (vs ++ bs) ι := by
    simpa only [hn] using (envExistsShift hΓ ρ bs vs ι).mpr hΓe
  simp only [hΓe', true_and]
  rw [← hn, envInterpretShift hΓ]

theorem generatedSchemeExists (hΓ : Env.WF S Δ Γ)
    (hΓe : Γ.exists_.Holds M ρ bs ι) :
    (generatedScheme sig Γ rhs).exists_.Holds M ρ bs ι ↔
      (Constraint.exists_ [0] (generate sig rhs (.bound 0) .empty)).Holds
        M ρ bs (Γ.interpret M ρ bs ι) := by
  apply exists_congr
  intro vs
  apply and_congr_right
  intro hv
  rw [infer, envLetInHolds]
  have hn : vs.length = 1 := hv.length_eq
  have hΓe' : (Γ.shift 1).exists_.Holds M ρ (vs ++ bs) ι := by
    simpa only [hn] using (envExistsShift hΓ ρ bs vs ι).mpr hΓe
  simp only [hΓe', true_and]
  rw [← hn, envInterpretShift hΓ]

/-- The generated value-let constraint is exactly inference for the body under
its closed generated scheme, including feasibility of that scheme. -/
theorem valueLetGeneration (hS : S.WF) (hsig : OpSignature.WF S sig)
    (hΓ : Env.WF S Δ Γ) (hr : Expr.Scoped Γ rhs) (hd : rhs.Declared sig)
    (hv : Value rhs) :
    Equivalent S M Δ (infer sig Γ (.letE rhs body) T ε)
      (infer sig (Γ.push (generatedScheme sig Γ rhs)) body T ε) := by
  change rhs.isValue = true at hv
  have hs := generatedSchemeWF hS hsig hΓ hr
  have hsf := generatedSchemeScope hsig hΓ hr hd
  have heq : ∀ (ρ : Assignment M) bs ι,
      (infer sig Γ (.letE rhs body) T ε).Holds M ρ bs ι ↔
        (infer sig (Γ.push (generatedScheme sig Γ rhs)) body T ε).Holds M ρ bs ι := by
    intro ρ bs ι
    simp only [infer, generate, hv, ↓reduceIte]
    rw [envLetInHolds, envLetInHolds, envPushExists hs hsf,
      envInterpretPush hs hsf]
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _) ∧ _
    rw [and_assoc]
    apply and_congr_right
    intro hΓe
    rw [generatedSchemeExists hΓ hΓe, generatedSchemeDenote hΓ hΓe]
    rfl
  exact ⟨fun ρ bs ι _ _ _ h => (heq ρ bs ι).mp h,
    fun ρ bs ι _ _ _ h => (heq ρ bs ι).mpr h⟩


/-- Generation observes the expected type and effect only through their semantic
values. The two values remain semantic witnesses, not reified type syntax. -/
theorem generationRebase (hS : S.WF) (hsig : OpSignature.WF S sig)
    (he : Expr.LCAt n e) (T : Ty) (ε : Effect) (ρ : Assignment M)
    (bs : List M.Carrier) (ι : GroundEnv M) :
    (generate sig e T ε).Holds M ρ bs ι ↔
      (generate sig e (.bound 0) (.bound 1)).Holds M ρ
        [T.eval M ρ bs, ε.eval M ρ bs] ι := by
  have hw := generationWF (Δ := [0,1]) hS hsig he
    (Ty.HasKind.bound (i := 0) rfl hS.1) (Ty.HasKind.bound (i := 1) rfl hS.2.1)
  have hr : BoundSubst.Realizes M [0,1] ρ [T.eval M ρ bs, ε.eval M ρ bs]
      bs (BoundSubst.many [T, ε]) := by
    intro i k hi
    cases i with
    | zero => simp [BoundSubst.many]
    | succ i =>
      cases i with
      | zero => simp [BoundSubst.many]
      | succ i => simp at hi
  have h := (substBoundSemantics M).1 _ _ _ hw ρ _ bs _ ι hr
  rw [generationSubstitution hsig] at h
  simpa [Ty.substBound, BoundSubst.many, tyShiftZero] using h

theorem generationEvalCongruence (hS : S.WF) (hsig : OpSignature.WF S sig)
    (he : Expr.LCAt n e) (ρ : Assignment M) (bs bs' : List M.Carrier) (ι : GroundEnv M)
    (hT : T.eval M ρ bs = U.eval M ρ bs') (hε : ε.eval M ρ bs = η.eval M ρ bs') :
    (generate sig e T ε).Holds M ρ bs ι ↔ (generate sig e U η).Holds M ρ bs' ι := by
  rw [generationRebase hS hsig he T ε, generationRebase hS hsig he U η, hT, hε]

/-- Scheme inclusion uses only the right-hand side's induction hypothesis at
valuations satisfying its declaration constraint, never the global completeness
statement. -/
theorem generatedSchemeComparison (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hΓ : Env.WF S Δ Γ) (hr : Expr.Scoped Γ rhs)
    (hA : Ty.HasKind S (ks ++ Δ) A 0)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs) (hι : GroundEnv.Valid ι)
    (hΓe : Γ.exists_.Holds M ρ bs ι)
    (ih : ∀ vs, KindValues M ks vs → D.Holds M ρ (vs ++ bs) ι →
      (infer sig (Γ.shift ks.length) rhs A .empty).Holds M ρ (vs ++ bs) ι) :
    (Scheme.all ks D A).denote M ρ bs ι ⊆ (generatedScheme sig Γ rhs).denote M ρ bs ι := by
  rw [generatedSchemeDenote hΓ hΓe]
  rintro a ⟨ha, vs, hv, hD, hAa⟩
  have hgen := ((envLetInHolds _ _ _ _ _).mp (ih vs hv hD)).2
  simp only [← hv.length_eq, envInterpretShift hΓ] at hgen
  let a₀ := A.eval M ρ (vs ++ bs)
  have ha₀ : M.kind a₀ = 0 := evalKind hF hρ (List.rel_append hv hbs) hA
  let κ := Γ.interpret M ρ bs ι
  have hg₀ : (generate sig rhs (.bound 0) .empty).Holds M ρ [a₀, a] κ := by
    apply (generationEvalCongruence hF.signature hsig hr.1 ρ (vs ++ bs) [a₀, a] κ
      (T := A) (U := .bound 0) (ε := .empty) (η := .empty)
      (by simp [a₀, Ty.eval]) (by simp [Ty.empty, Ty.eval])).mp
    exact hgen
  have hk := hF.constructorKind .empty trivial [] .nil
  have hg₁ : (generate sig rhs (.bound 1) .empty).Holds M ρ [a₀, a] κ := by
    apply generationMonotone hF rhs (envInterpretValid hF hΓ hρ hbs hι) _ _ hg₀
    · simpa [Constraint.le, Constraint.Holds, Predicate.eval, Ty.eval, a₀] using
        And.intro ha₀ (And.intro ha hAa)
    · simpa [Constraint.le, Constraint.Holds, Predicate.eval, Ty.empty, Ty.eval, Symbol.result] using
        And.intro hk (And.intro hk (hF.belowRefl 1 hF.signature.2.1 _ hk))
  refine ⟨ha, [a], .cons ha .nil, ?_, ?_⟩
  · exact (generationEvalCongruence hF.signature hsig hr.1 ρ [a₀, a] ([a] ++ bs) κ
      (T := .bound 1) (U := .bound 0) (ε := .empty) (η := .empty)
      (by simp [Ty.eval]) (by simp [Ty.empty, Ty.eval])).mp hg₁
  · simpa [Ty.eval] using hF.belowRefl 0 hF.signature.1 a ha

end EHMX
