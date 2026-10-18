import EHMX.Proofs.InferenceSoundness
import EHMX.Proofs.Reduction

namespace EHMX

variable {Γ : Env}


/-- Feasibility and nonemptiness coincide for well-kinded schemes. -/
theorem schemeExistsNonempty (hF : EffectFramework S M) (hs : Scheme.WF S Δ n s)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs) :
    s.exists_.Holds M ρ bs ι ↔ (s.denote M ρ bs ι).Nonempty := by
  cases s with
  | all ks D A =>
      constructor
      · rintro ⟨vs, hv, hD⟩
        have ha := evalKind hF hρ (List.rel_append hv hbs) hs.2.2
        exact ⟨A.eval M ρ (vs ++ bs), ha, vs, hv, hD,
          hF.belowRefl 0 hF.signature.1 _ ha⟩
      · rintro ⟨a, ha, vs, hv, hD, _⟩
        exact ⟨vs, hv, hD⟩

theorem monoExists (A : Ty) : (Scheme.mono A).exists_.Holds M ρ bs ι :=
  ⟨[], .nil, trivial⟩

theorem monoDenoteCongruence (h : A.eval M ρ bs = B.eval M ρ bs') :
    (Scheme.mono A).denote M ρ bs ι = (Scheme.mono B).denote M ρ bs' κ := by
  ext a
  simp only [Scheme.mono, Scheme.denote, Set.mem_ofPred_eq, KindValues,
    List.forall₂_nil_right_iff, exists_eq_left, Constraint.Holds, List.nil_append, true_and, h]

theorem inferShiftHolds (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hΓ : Env.WF S Δ Γ) (he : e.Scoped Γ) (hT : Ty.HasKind S Δ T 0)
    (hε : Ty.HasKind S Δ ε 1) (ρ : Assignment M) (bs vs : List M.Carrier) (ι : GroundEnv M) :
    (infer sig (Γ.shift vs.length) e (T.shift vs.length 0) (ε.shift vs.length 0)).Holds M ρ (vs ++ bs) ι ↔
      (infer sig Γ e T ε).Holds M ρ bs ι := by
  rw [infer, ← generationShift hsig, ← envLetInShift]
  exact constraintShiftHolds (inferWF hF.signature hsig hΓ he hT hε) ρ bs vs ι

theorem envPushMonoExists (hA : Ty.HasKind S Δ A 0)
    (h : Γ.exists_.Holds M ρ bs ι) : (Γ.push (.mono A)).exists_.Holds M ρ bs ι :=
  (envPushExists (s := .mono A) ⟨by simp, trivial, hA⟩ rfl ρ bs ι).mpr ⟨h, monoExists A⟩

/-- Body generation under a monomorphic binder, interpreted in the outer environment. -/
theorem inferMonoBody (hA : Ty.HasKind S Δ A 0)
    (h : (infer sig (Γ.push (.mono A)) e T ε).Holds M ρ bs ι) :
    (generate sig e T ε).Holds M ρ bs
      ((Γ.interpret M ρ bs ι).push ((Scheme.mono A).denote M ρ bs ι)) := by
  have hh := ((envLetInHolds _ _ _ _ _).mp h).2
  rwa [envInterpretPush (s := .mono A) ⟨by simp, trivial, hA⟩ rfl] at hh


theorem generationLambdaHolds (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hsc : body.LCAt n) (hA : Ty.HasKind S Δ A 0) (hB : Ty.HasKind S Δ B 0)
    (hε : Ty.HasKind S Δ ε 1) (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs)
    (hg : (generate sig body B ε).Holds M ρ bs (ι.push ((Scheme.mono A).denote M ρ bs κ))) :
    (generate sig (.lam body) (.arrow A ε B) .empty).Holds M ρ bs ι := by
  let vs := [A.eval M ρ bs, ε.eval M ρ bs, B.eval M ρ bs]
  have hv : KindValues M [0,1,0] vs :=
    .cons (evalKind hF hρ hbs hA) (.cons (evalKind hF hρ hbs hε) (.cons (evalKind hF hρ hbs hB) .nil))
  refine ⟨vs, hv, ?_, ?_⟩
  · change (generate sig body (.bound 2) (.bound 1)).Holds M ρ (vs ++ bs)
      (ι.push ((Scheme.mono (.bound 0)).denote M ρ (vs ++ bs) ι))
    rw [monoDenoteCongruence (A := .bound 0) (B := A) (bs' := bs) (κ := κ) (by simp [Ty.eval, vs])]
    exact (generationEvalCongruence hF.signature hsig hsc ρ bs (vs ++ bs) _
      (by simp [vs, Ty.eval]) (by simp [vs, Ty.eval])).mp hg
  · have hAr := evalKind hF hρ hbs (arrowKind hA hε hB)
    have hem := evalKind hF hρ hbs (emptyKind (Δ := Δ) hF.signature)
    have hshift := evalShift (.arrow A ε B) ρ bs vs
    change ((Ty.arrow A ε B).shift 3 0).eval M ρ (vs ++ bs) = _ at hshift
    change (Constraint.le 0 (.arrow (.bound 0) (.bound 1) (.bound 2))
      ((Ty.arrow A ε B).shift 3 0)).Holds M ρ (vs ++ bs) ι ∧ _
    simp only [Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons, List.map_nil, hshift]
    have har : (Constraint.le 0 (.arrow A ε B) (.arrow A ε B)).Holds M ρ bs ι :=
      ⟨hAr, hAr, hF.belowRefl 0 hF.signature.1 _ hAr⟩
    have her : (Constraint.le 1 .empty .empty).Holds M ρ bs ι :=
      ⟨hem, hem, hF.belowRefl 1 hF.signature.2.1 _ hem⟩
    simpa [Ty.arrow, Ty.empty, Ty.shift, Ty.eval, vs, Constraint.le,
      Constraint.Holds, Predicate.eval] using And.intro har her

theorem generationApplicationHolds (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hfs : f.LCAt n) (hxs : x.LCAt n)
    (hA : Ty.HasKind S Δ A 0)
    (hη : Ty.HasKind S Δ η 1) (hf : Ty.HasKind S Δ εf 1) (hx : Ty.HasKind S Δ εx 1)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs)
    (hgf : (generate sig f (.arrow A η B) εf).Holds M ρ bs ι)
    (hgx : (generate sig x A εx).Holds M ρ bs ι) :
    (generate sig (.app f x) B (.union (.union εf εx) η)).Holds M ρ bs ι := by
  let vs := [A.eval M ρ bs, η.eval M ρ bs, εf.eval M ρ bs, εx.eval M ρ bs]
  have hv : KindValues M [0,1,1,1] vs :=
    .cons (evalKind hF hρ hbs hA) (.cons (evalKind hF hρ hbs hη)
      (.cons (evalKind hF hρ hbs hf) (.cons (evalKind hF hρ hbs hx) .nil)))
  have hBshift := evalShift B ρ bs vs
  have hEshift := evalShift (.union (.union εf εx) η) ρ bs vs
  change (B.shift 4 0).eval M ρ (vs ++ bs) = _ at hBshift
  change ((Ty.union (.union εf εx) η).shift 4 0).eval M ρ (vs ++ bs) = _ at hEshift
  refine ⟨vs, hv, ?_, ?_, ?_⟩
  · apply (generationEvalCongruence hF.signature hsig hfs ρ bs (vs ++ bs) _ ?_ ?_).mp hgf
    · simp only [Ty.arrow, Ty.eval, List.map_cons, List.map_nil, hBshift]
      simp [vs]
    · simp [vs, Ty.eval]
  · exact (generationEvalCongruence hF.signature hsig hxs ρ bs (vs ++ bs) _
      (by simp [vs, Ty.eval]) (by simp [vs, Ty.eval])).mp hgx
  · have hrot := effectUnionRotate hF hf hx hη
      (leRefl (C := .truth) hF hF.signature.2.1 (unionKind (unionKind hf hx) hη))
    have hrot' := effectUnionRotate hF hx hη hf hrot
    have hh := hrot' ρ bs (GroundEnv.mk (fun _ => ∅) []) hρ hbs
      ⟨by intro x; exact ⟨by simp, by simp⟩, by simp⟩ trivial
    simp only [Constraint.le, Constraint.Holds, List.map_cons, List.map_nil, Predicate.eval, hEshift]
    simpa [Ty.union, Ty.eval, vs, Constraint.le, Constraint.Holds, Predicate.eval] using hh


theorem generationMonoLetHolds (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hr : rhs.LCAt n) (hb : body.LCAt (n + 1)) (hv : rhs.isValue = false)
    (hA : Ty.HasKind S Δ A 0) (hεr : Ty.HasKind S Δ εr 1) (hεb : Ty.HasKind S Δ εb 1)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs)
    (hgr : (generate sig rhs A εr).Holds M ρ bs ι)
    (hgb : (generate sig body B εb).Holds M ρ bs (ι.push ((Scheme.mono A).denote M ρ bs κ))) :
    (generate sig (.letE rhs body) B (.union εr εb)).Holds M ρ bs ι := by
  let vs := [A.eval M ρ bs, εr.eval M ρ bs, εb.eval M ρ bs]
  have hvs : KindValues M [0,1,1] vs := .cons (evalKind hF hρ hbs hA)
    (.cons (evalKind hF hρ hbs hεr) (.cons (evalKind hF hρ hbs hεb) .nil))
  have hBshift : (B.shift 3 0).eval M ρ (vs ++ bs) = B.eval M ρ bs := evalShift B ρ bs vs
  have hEshift : ((Ty.union εr εb).shift 3 0).eval M ρ (vs ++ bs) =
      (Ty.union εr εb).eval M ρ bs := evalShift _ ρ bs vs
  simp only [generate, hv, Bool.false_eq_true, ↓reduceIte]
  refine ⟨vs, hvs, ?_, ?_, ?_⟩
  · exact (generationEvalCongruence hF.signature hsig hr ρ bs (vs ++ bs) _
      (by simp [vs, Ty.eval]) (by simp [vs, Ty.eval])).mp hgr
  · change (generate sig body (B.shift 3 0) (.bound 2)).Holds M ρ (vs ++ bs)
      (ι.push ((Scheme.mono (.bound 0)).denote M ρ (vs ++ bs) ι))
    rw [monoDenoteCongruence (A := .bound 0) (B := A) (bs' := bs) (κ := κ) (by simp [vs, Ty.eval])]
    exact (generationEvalCongruence hF.signature hsig hb ρ bs (vs ++ bs) _ hBshift.symm
      (by simp [vs, Ty.eval])).mp hgb
  · have hk := evalKind hF hρ hbs (unionKind hεr hεb)
    have hh : (Constraint.le 1 (.union εr εb) (.union εr εb)).Holds M ρ bs ι :=
      ⟨hk, hk, hF.belowRefl 1 hF.signature.2.1 _ hk⟩
    simp only [Constraint.le, Constraint.Holds, List.map_cons, List.map_nil, Predicate.eval, hEshift]
    simpa [Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.eval, vs] using hh

/-- Transfer the body from a declared scheme to the generated scheme, retaining feasibility. -/
theorem valueLetCompletenessHolds (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hΓ : Env.WF S Δ Γ) (hr : rhs.Scoped Γ) (hd : rhs.Declared sig) (hv : Value rhs)
    (hs : (Scheme.all ks D A).WF S Δ 0) (hsf : (Scheme.all ks D A).fpi = ∅)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs) (hι : GroundEnv.Valid ι)
    (hΓe : Γ.exists_.Holds M ρ bs ι)
    (hse : (Scheme.all ks D A).exists_.Holds M ρ bs ι)
    (ih : ∀ vs, KindValues M ks vs → D.Holds M ρ (vs ++ bs) ι →
      (infer sig (Γ.shift ks.length) rhs A .empty).Holds M ρ (vs ++ bs) ι)
    (hwbody : (generate sig body T ε).WF S Δ (Γ.bound.length + 1))
    (hbody : (infer sig (Γ.push (.all ks D A)) body T ε).Holds M ρ bs ι) :
    (infer sig Γ (.letE rhs body) T ε).Holds M ρ bs ι := by
  have hsw := generatedSchemeWF hF.signature hsig hΓ hr
  have hsf' := generatedSchemeScope hsig hΓ hr hd
  have hinc := generatedSchemeComparison hF hsig hΓ hr hs.2.2 hρ hbs hι hΓe ih
  have hreal : (generatedScheme sig Γ rhs).exists_.Holds M ρ bs ι := by
    obtain ⟨a, ha⟩ := (schemeExistsNonempty hF hs hρ hbs).mp hse
    exact (schemeExistsNonempty hF hsw hρ hbs).mpr ⟨a, hinc ha⟩
  apply (valueLetGeneration hF.signature hsig hΓ hr hd hv).2 ρ bs ι hρ hbs hι
  apply (envLetInHolds _ _ _ _ _).mpr
  refine ⟨(envPushExists hsw hsf' ρ bs ι).mpr ⟨hΓe, hreal⟩, ?_⟩
  rw [envInterpretPush hsw hsf']
  have hg := ((envLetInHolds _ _ _ _ _).mp hbody).2
  rw [envInterpretPush hs hsf] at hg
  apply (groundMonotonicity M).1 _ _ _ hwbody _ _ _ _ _ hg
  intro x
  cases x with
  | free x => exact Set.Subset.refl _
  | bound i =>
      cases i with
      | zero => exact hinc
      | succ i => exact Set.Subset.refl _

/-- A declaration reads only the values of its own binders. -/
theorem evalDeclarationAppend (hT : Ty.HasKind S ks T k)
    (hn : vs.length = ks.length) (ρ : Assignment M) (bs : List M.Carrier) :
    T.eval M ρ (vs ++ bs) = T.eval M ρ vs := by
  induction T using tyInduction generalizing k with
  | hf X => simp [Ty.eval]
  | hb i =>
      cases hT with
      | bound hi _ =>
          have hlt : i < vs.length := by rw [hn]; exact (List.getElem?_eq_some_iff.mp hi).1
          simp [Ty.eval, List.getElem?_append, hlt]
  | hc f ts ih =>
      cases hT with
      | con _ hs =>
          simp only [Ty.eval]
          congr 1
          apply List.map_congr_left
          intro T hT
          obtain ⟨k, _, hk⟩ := forall₂MemLeft hs hT
          exact ih T hT hk

theorem evalDeclarationOpen (hT : Ty.HasKind S ks T k)
    (hargs : List.Forall₂ (Ty.HasKind S Δ) args ks) (ρ : Assignment M) (bs : List M.Carrier) :
    (T.openAt 0 args).eval M ρ bs = T.eval M ρ (args.map (Ty.eval M ρ bs)) := by
  rw [tyOpenMany]
  apply evalSubstBound hT
  intro i k hi
  obtain ⟨U, hU, _⟩ := forall₂Lookup hargs hi
  simp [BoundSubst.many, hU, List.getElem?_map]


theorem generationPerformHolds (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hs : sig op = some decl) (hsc : arg.LCAt n)
    (hargs : List.Forall₂ (Ty.HasKind S Δ) args decl.kinds) (hε : Ty.HasKind S Δ ε 1)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs)
    (hp : (decl.condition.substBound (BoundSubst.many args)).Holds M ρ bs ι)
    (hg : (generate sig arg (decl.input.openAt 0 args) ε).Holds M ρ bs ι) :
    (generate sig (.perform op arg) (decl.output.openAt 0 args) (.union (.singleton op) ε)).Holds M ρ bs ι := by
  have hd := hsig op decl hs
  let us := args.map (Ty.eval M ρ bs)
  let vs := us ++ [ε.eval M ρ bs]
  have hu : KindValues M decl.kinds us :=
    List.forall₂_map_left_iff.mpr (forall₂ImplMem hargs (fun _ _ _ hk => evalKind hF hρ hbs hk))
  have hv : KindValues M (decl.kinds ++ [1]) vs :=
    List.rel_append hu (.cons (evalKind hF hρ hbs hε) .nil)
  have hn : vs.length = decl.kinds.length + 1 := by simp [vs, hu.length_eq]
  have hin : decl.input.eval M ρ (vs ++ bs) = (decl.input.openAt 0 args).eval M ρ bs := by
    rw [evalDeclarationOpen hd.2.1 hargs]
    simpa only [vs, List.append_assoc] using evalDeclarationAppend hd.2.1 hu.length_eq ρ ([ε.eval M ρ bs] ++ bs)
  have hout : decl.output.eval M ρ (vs ++ bs) = (decl.output.openAt 0 args).eval M ρ bs := by
    rw [evalDeclarationOpen hd.2.2.1 hargs]
    simpa only [vs, List.append_assoc] using evalDeclarationAppend hd.2.2.1 hu.length_eq ρ ([ε.eval M ρ bs] ++ bs)
  have he : (Ty.bound decl.kinds.length).eval M ρ (vs ++ bs) = ε.eval M ρ bs := by
    simp [Ty.eval, vs, List.append_assoc, ← hu.length_eq]
  have hBshift : ((decl.output.openAt 0 args).shift (decl.kinds.length + 1) 0).eval M ρ (vs ++ bs) =
      (decl.output.openAt 0 args).eval M ρ bs := by simpa only [hn] using evalShift (decl.output.openAt 0 args) ρ bs vs
  have hEshift : ((Ty.union (.singleton op) ε).shift (decl.kinds.length + 1) 0).eval M ρ (vs ++ bs) =
      (Ty.union (.singleton op) ε).eval M ρ bs := by simpa only [hn] using evalShift (.union (.singleton op) ε) ρ bs vs
  simp only [generate, hs]
  have hp' : decl.condition.Holds M ρ (vs ++ bs) ι := by
    simp only [vs, List.append_assoc]
    apply (conditionDeclarationAppend hd.2.2.2.2.2.1 hu.length_eq ρ ([ε.eval M ρ bs] ++ bs) ι).mpr
    exact (conditionDeclarationOpen hd.2.2.2.2.2.1 hargs ρ bs ι).mp hp
  refine ⟨vs, hv, hp', (generationEvalCongruence hF.signature hsig hsc ρ bs (vs ++ bs) _ hin.symm he.symm).mp hg, ?_⟩
  have hkB := evalKind hF hρ hbs (operationInstantiation hd.2.2.1 hargs)
  have hkE := evalKind hF hρ hbs (unionKind (singletonKind op) hε)
  have hreflB : (Constraint.le 0 (decl.output.openAt 0 args) (decl.output.openAt 0 args)).Holds M ρ bs ι :=
    ⟨hkB, hkB, hF.belowRefl 0 hF.signature.1 _ hkB⟩
  have hreflE : (Constraint.le 1 (.union (.singleton op) ε) (.union (.singleton op) ε)).Holds M ρ bs ι :=
    ⟨hkE, hkE, hF.belowRefl 1 hF.signature.2.1 _ hkE⟩
  simp only [resultConstraint, Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons, List.map_nil,
    hout, hBshift, hEshift]
  simpa only [Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.singleton, Ty.eval,
    List.map_cons, List.map_nil, he] using And.intro hreflB hreflE


theorem generationHandleHolds (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hs : sig op = some decl) (hbscope : body.LCAt n) (hrscope : ret.LCAt (n+1))
    (hcscope : clause.LCAt (n+2)) (hA : Ty.HasKind S Δ A 0) (hB : Ty.HasKind S Δ B 0)
    (hi : Ty.HasKind S Δ εin 1) (ho : Ty.HasKind S Δ εout 1)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs)
    (hbody : (generate sig body A εin).Holds M ρ bs ι)
    (he : (Constraint.le 1 εin (.union (.singleton op) εout)).Holds M ρ bs ι)
    (hret : (Constraint.def_ (.mono A) (generate sig ret B εout)).Holds M ρ bs ι)
    (hclause : ∀ us, KindValues M decl.kinds us → decl.condition.Holds M ρ (us ++ bs) ι →
      (Constraint.def_ (.mono decl.input)
        (.def_ (.mono (.arrow decl.output (εout.shift decl.kinds.length 0) (B.shift decl.kinds.length 0)))
          (generate sig clause (B.shift decl.kinds.length 0) (εout.shift decl.kinds.length 0)))).Holds M ρ (us ++ bs) ι) :
    (generate sig (.handle body op ret clause) B εout).Holds M ρ bs ι := by
  have hd := hsig op decl hs
  let vs := [A.eval M ρ bs, εin.eval M ρ bs, B.eval M ρ bs, εout.eval M ρ bs]
  have hv : KindValues M [0,1,0,1] vs := .cons (evalKind hF hρ hbs hA)
    (.cons (evalKind hF hρ hbs hi) (.cons (evalKind hF hρ hbs hB) (.cons (evalKind hF hρ hbs ho) .nil)))
  have hBshift : (B.shift 4 0).eval M ρ (vs ++ bs) = B.eval M ρ bs := evalShift B ρ bs vs
  have hEshift : (εout.shift 4 0).eval M ρ (vs ++ bs) = εout.eval M ρ bs := evalShift εout ρ bs vs
  simp only [generate, hs]
  refine ⟨vs, hv, ?_, ?_, ?_, ?_, ?_⟩
  · exact (generationEvalCongruence hF.signature hsig hbscope ρ bs (vs ++ bs) _
      (by simp [vs, Ty.eval]) (by simp [vs, Ty.eval])).mp hbody
  · simpa [Constraint.le, Constraint.Holds, Predicate.eval, Ty.union, Ty.singleton, Ty.eval, vs] using he
  · change (generate sig ret (.bound 2) (.bound 3)).Holds M ρ (vs ++ bs)
      (ι.push ((Scheme.mono (.bound 0)).denote M ρ (vs ++ bs) ι))
    rw [monoDenoteCongruence (A := .bound 0) (B := A) (bs' := bs) (κ := ι) (by simp [vs, Ty.eval])]
    exact (generationEvalCongruence hF.signature hsig hrscope ρ bs (vs ++ bs) _
      (by simp [vs, Ty.eval]) (by simp [vs, Ty.eval])).mp hret
  · intro us hu hp
    have hBn : ((Ty.bound 2).shift decl.kinds.length 0).eval M ρ (us ++ (vs ++ bs)) = B.eval M ρ bs := by
      calc
        _ = (Ty.bound 2).eval M ρ (vs ++ bs) := by simpa only [hu.length_eq] using evalShift (.bound 2) ρ (vs ++ bs) us
        _ = _ := by simp [vs, Ty.eval]
    have hEn : ((Ty.bound 3).shift decl.kinds.length 0).eval M ρ (us ++ (vs ++ bs)) = εout.eval M ρ bs := by
      calc
        _ = (Ty.bound 3).eval M ρ (vs ++ bs) := by simpa only [hu.length_eq] using evalShift (.bound 3) ρ (vs ++ bs) us
        _ = _ := by simp [vs, Ty.eval]
    have hBo : (B.shift decl.kinds.length 0).eval M ρ (us ++ bs) = B.eval M ρ bs := by
      simpa only [hu.length_eq] using evalShift B ρ bs us
    have hEo : (εout.shift decl.kinds.length 0).eval M ρ (us ++ bs) = εout.eval M ρ bs := by
      simpa only [hu.length_eq] using evalShift εout ρ bs us
    have hinput : decl.input.eval M ρ (us ++ (vs ++ bs)) = decl.input.eval M ρ (us ++ bs) := by
      rw [evalDeclarationAppend hd.2.1 hu.length_eq, evalDeclarationAppend hd.2.1 hu.length_eq]
    have houtput : decl.output.eval M ρ (us ++ (vs ++ bs)) = decl.output.eval M ρ (us ++ bs) := by
      rw [evalDeclarationAppend hd.2.2.1 hu.length_eq, evalDeclarationAppend hd.2.2.1 hu.length_eq]
    have harr : (Ty.arrow decl.output ((Ty.bound 3).shift decl.kinds.length 0)
        ((Ty.bound 2).shift decl.kinds.length 0)).eval M ρ (us ++ (vs ++ bs)) =
        (Ty.arrow decl.output (εout.shift decl.kinds.length 0) (B.shift decl.kinds.length 0)).eval M ρ (us ++ bs) := by
      simp only [Ty.arrow, Ty.eval, List.map_cons, List.map_nil, houtput, hBn, hEn, hBo, hEo]
    change (generate sig clause _ _).Holds M ρ _ ((ι.push _).push _)
    rw [monoDenoteCongruence (κ := ι) hinput, monoDenoteCongruence (κ := ι.push _) harr]
    exact (generationEvalCongruence hF.signature hsig hcscope ρ (us ++ bs) (us ++ (vs ++ bs)) _
      (hBo.trans hBn.symm) (hEo.trans hEn.symm)).mp (hclause us hu ((conditionDeclarationAppend hd.2.2.2.2.2.1 hu.length_eq ρ bs ι).mpr
        ((conditionDeclarationAppend hd.2.2.2.2.2.1 hu.length_eq ρ (vs ++ bs) ι).mp hp)))
  · have hkB := evalKind hF hρ hbs hB
    have hkE := evalKind hF hρ hbs ho
    have hrB : (Constraint.le 0 B B).Holds M ρ bs ι := ⟨hkB, hkB, hF.belowRefl 0 hF.signature.1 _ hkB⟩
    have hrE : (Constraint.le 1 εout εout).Holds M ρ bs ι := ⟨hkE, hkE, hF.belowRefl 1 hF.signature.2.1 _ hkE⟩
    simp only [resultConstraint, Constraint.le, Constraint.Holds, Predicate.eval, List.map_cons, List.map_nil, hBshift, hEshift]
    simpa [Constraint.le, Constraint.Holds, Predicate.eval, Ty.eval, vs] using And.intro hrB hrE


/-- Completeness at each valid valuation; feasibility is an explicit induction premise. -/
theorem typingCompletenessHolds (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (ht : Typing S M sig Δ C Γ e T ε) :
    ∀ ρ bs ι, Assignment.Valid S M ρ → KindValues M Δ bs → GroundEnv.Valid ι →
      C.Holds M ρ bs ι → Γ.exists_.Holds M ρ bs ι →
      (infer sig Γ e T ε).Holds M ρ bs ι := by
  induction ht with
  | var hw hl he =>
      intro ρ bs ι hρ hbs hι hC hΓe
      exact variableCompletenessHolds hF hw.2.2.1 hl hw.2.2.2.2.1 hρ hbs hι hΓe
        (he ρ bs ι hρ hbs hι hC)
  | lam hw hb ih =>
      intro ρ bs ι hρ hbs hι hC hΓe
      have hk := arrowKinds hw.2.2.2.2.1
      have hg := inferMonoBody hk.1 (ih ρ bs ι hρ hbs hι hC (envPushMonoExists hk.1 hΓe))
      exact (envLetInHolds _ _ _ _ _).mpr ⟨hΓe,
        generationLambdaHolds hF hsig (typingWF hb).2.2.2.1.1 hk.1 hk.2.2 hk.2.1 hρ hbs hg⟩
  | app hw hf hx ihf ihx =>
      intro ρ bs ι hρ hbs hι hC hΓe
      have hfw := typingWF hf
      have hxw := typingWF hx
      have hk := arrowKinds hfw.2.2.2.2.1
      exact (envLetInHolds _ _ _ _ _).mpr ⟨hΓe,
        generationApplicationHolds hF hsig hfw.2.2.2.1.1 hxw.2.2.2.1.1 hk.1
          hk.2.1 hfw.2.2.2.2.2 hxw.2.2.2.2.2 hρ hbs
          ((envLetInHolds _ _ _ _ _).mp (ihf ρ bs ι hρ hbs hι hC hΓe)).2
          ((envLetInHolds _ _ _ _ _).mp (ihx ρ bs ι hρ hbs hι hC hΓe)).2⟩
  | @letMono Δ C Γ rhs body B εr εb A hw hr hb ihr ihb =>
      intro ρ bs ι hρ hbs hι hC hΓe
      have hrw := typingWF hr
      have hbw := typingWF hb
      have hA := hrw.2.2.2.2.1
      have hgr := ihr ρ bs ι hρ hbs hι hC hΓe
      have hgb := ihb ρ bs ι hρ hbs hι hC (envPushMonoExists hA hΓe)
      cases hv : rhs.isValue with
      | false =>
          exact (envLetInHolds _ _ _ _ _).mpr ⟨hΓe,
            generationMonoLetHolds hF hsig hrw.2.2.2.1.1 hbw.2.2.2.1.1 hv hA
              hrw.2.2.2.2.2 hbw.2.2.2.2.2 hρ hbs ((envLetInHolds _ _ _ _ _).mp hgr).2
              (inferMonoBody hA hgb)⟩
      | true =>
          have hpure : (infer sig Γ rhs A .empty).Holds M ρ bs ι :=
            (envLetInHolds _ _ _ _ _).mpr ⟨hΓe, generationValuePure hF hv
              ((envLetInHolds _ _ _ _ _).mp hgr).2⟩
          have hlet := valueLetCompletenessHolds hF hsig hw.2.2.1 hrw.2.2.2.1
            (typingDeclared hr) hv (ks := []) (D := .truth) (A := A)
            ⟨by simp, trivial, hA⟩ rfl hρ hbs hι hΓe (monoExists A) (by
              intro vs hvs _
              have heq : vs = [] := List.length_eq_zero_iff.mp hvs.length_eq
              subst vs
              simpa only [List.length_nil, List.nil_append, envShiftZero] using hpure)
              (generationWF hF.signature hsig hbw.2.2.2.1.1 hbw.2.2.2.2.1 hbw.2.2.2.2.2) hgb
          have hg := ((envLetInHolds _ _ _ _ _).mp hlet).2
          exact (envLetInHolds _ _ _ _ _).mpr ⟨hΓe,
            generationMonotone hF _ (envInterpretValid hF hw.2.2.1 hρ hbs hι)
              (leRefl (C := .truth) hF hF.signature.1 hw.2.2.2.2.1 ρ bs ι hρ hbs hι trivial)
              (effectUnionRight hF hrw.2.2.2.2.2 hbw.2.2.2.2.2 ρ bs ι hρ hbs hι hC) hg⟩
  | @letPoly Δ C Γ rhs body B ε ks D A hw hv hr he hb ihr ihb =>
      intro ρ bs ι hρ hbs hι hC hΓe
      have hrw := typingWF hr
      have hsw := (typingWF hb).2.2.1.2 (.all ks D A) (by simp [Env.push])
      have hrs : rhs.Scoped Γ := ⟨hw.2.2.2.1.1.1,
        fun _ h => hw.2.2.2.1.2 (Finset.mem_union_left _ h)⟩
      have hse := he ρ bs ι hρ hbs hι hC
      apply valueLetCompletenessHolds hF hsig hw.2.2.1 hrs (typingDeclared hr) hv
        hsw.1 hsw.2 hρ hbs hι hΓe hse
      · intro vs hvs hD
        apply ihr ρ (vs ++ bs) ι hρ (List.rel_append hvs hbs) hι
        · refine ⟨?_, hD⟩
          simpa only [← hvs.length_eq] using (constraintShiftHolds hw.1 ρ bs vs ι).mpr hC
        · simpa only [← hvs.length_eq] using (envExistsShift hw.2.2.1 ρ bs vs ι).mpr hΓe
      · exact generationWF hF.signature hsig (typingWF hb).2.2.2.1.1
          (typingWF hb).2.2.2.2.1 (typingWF hb).2.2.2.2.2
      · exact ihb ρ bs ι hρ hbs hι hC ((envPushExists hsw.1 hsw.2 ρ bs ι).mpr ⟨hΓe, hse⟩)
  | perform hw hs hargs hp ht ih =>
      intro ρ bs ι hρ hbs hι hC hΓe
      exact (envLetInHolds _ _ _ _ _).mpr ⟨hΓe,
        generationPerformHolds hF hsig hs (typingWF ht).2.2.2.1.1 hargs (typingWF ht).2.2.2.2.2
          hρ hbs ((constraintGroundIndependent
            ((substBoundWF S).1 _ _ _ (constraintAppendWF (hsig _ _ hs).2.2.2.2.2.1 _) _ _
              (BoundSubst.validMany hargs))
            ((substBoundFpi.1 _ _).trans (hsig _ _ hs).2.2.2.2.2.2.1) ρ bs ι _).mp
              (hp ρ bs ι hρ hbs hι hC))
          ((envLetInHolds _ _ _ _ _).mp (ih ρ bs ι hρ hbs hι hC hΓe)).2⟩
  | @handle Δ C Γ body op ret clause B εout decl A εin hw hs hb he hr hc ihb ihr ihc =>
      intro ρ bs ι hρ hbs hι hC hΓe
      have hbw := typingWF hb
      have hA := hbw.2.2.2.2.1
      have hd := hsig op decl hs
      apply (envLetInHolds _ _ _ _ _).mpr
      refine ⟨hΓe, generationHandleHolds hF hsig hs hw.2.2.2.1.1.1 hw.2.2.2.1.1.2.1
        hw.2.2.2.1.1.2.2 hA hw.2.2.2.2.1 hbw.2.2.2.2.2 hw.2.2.2.2.2 hρ hbs
        ((envLetInHolds _ _ _ _ _).mp (ihb ρ bs ι hρ hbs hι hC hΓe)).2
        (he ρ bs ι hρ hbs hι hC) ?_ ?_⟩
      · have hh := (envLetInMono Γ A _).2 ρ bs ι hρ hbs hι
          (ihr ρ bs ι hρ hbs hι hC (envPushMonoExists hA hΓe))
        exact ((envLetInHolds _ _ _ _ _).mp hh).2
      · intro us hu hp
        have hbs' := List.rel_append hu hbs
        have hΓe' : (Γ.shift decl.kinds.length).exists_.Holds M ρ (us ++ bs) ι := by
          simpa only [← hu.length_eq] using (envExistsShift hw.2.2.1 ρ bs us ι).mpr hΓe
        have hC' : (C.shift decl.kinds.length 0).Holds M ρ (us ++ bs) ι := by
          simpa only [← hu.length_eq] using (constraintShiftHolds hw.1 ρ bs us ι).mpr hC
        have hin := kindAppend hd.2.1 Δ
        have hk := arrowKind (kindAppend hd.2.2.1 Δ)
          (kindShift hw.2.2.2.2.2 decl.kinds) (kindShift hw.2.2.2.2.1 decl.kinds)
        have hp' : decl.condition.Holds M ρ (us ++ bs) ι :=
          (constraintGroundIndependent hd.2.2.2.2.2.1 hd.2.2.2.2.2.2.1 ρ (us ++ bs) _ ι).mp hp
        have hg := ihc ρ (us ++ bs) ι hρ hbs' hι ⟨hC', hp'⟩
          (envPushMonoExists hk (envPushMonoExists hin hΓe'))
        have hh := (envLetInMono _ _ _).2 ρ (us ++ bs) ι hρ hbs' hι hg
        have hh' := (envLetInMono _ _ _).2 ρ (us ++ bs) ι hρ hbs' hι hh
        have hgen := ((envLetInHolds _ _ _ _ _).mp hh').2
        simpa only [← hu.length_eq, envInterpretShift hw.2.2.1] using hgen
  | sub hw ht hT hε ih =>
      intro ρ bs ι hρ hbs hι hC hΓe
      have hg := ((envLetInHolds _ _ _ _ _).mp (ih ρ bs ι hρ hbs hι hC hΓe)).2
      exact (envLetInHolds _ _ _ _ _).mpr ⟨hΓe,
        generationMonotone hF _ (envInterpretValid hF hw.2.2.1 hρ hbs hι)
          (hT ρ bs ι hρ hbs hι hC) (hε ρ bs ι hρ hbs hι hC) hg⟩
  | strengthen hw ht he ih =>
      intro ρ bs ι hρ hbs hι hD hΓe
      exact ih ρ bs ι hρ hbs hι (he ρ bs ι hρ hbs hι hD) hΓe
  | exists_ hw ht ih =>
      intro ρ bs ι hρ hbs hι hC hΓe
      obtain ⟨vs, hv, hD⟩ := hC
      have hΓe' := (envExistsShift hw.2.2.1 ρ bs vs ι).mpr hΓe
      have hg := ih ρ (vs ++ bs) ι hρ (List.rel_append hv hbs) hι hD (by
        simpa only [← hv.length_eq] using hΓe')
      apply (inferShiftHolds hF hsig hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2.1 hw.2.2.2.2.2 ρ bs vs ι).mp
      simpa only [← hv.length_eq] using hg

/-- ATTAPL 10.4.8 with explicit environment feasibility, extended to effects and handlers. -/
theorem inferenceCompleteness (S : Signature) (M : Model) (sig : OpSignature) :
    InferenceCompletenessGoal S M sig := by
  intro hA Δ C Γ e T ε _ hΓe ht ρ bs ι hρ hbs hι hC
  exact typingCompletenessHolds hA.1 hA.2 ht ρ bs ι hρ hbs hι hC (hΓe ρ bs ι hρ hbs hι hC)

end EHMX
