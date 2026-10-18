import EHMX.Proofs.InferenceSupport
import EHMX.Goals

namespace EHMX

theorem envPushMonoWF (hΓ : Env.WF S Δ Γ) (hA : Ty.HasKind S Δ A 0) :
    (Γ.push (.mono A)).WF S Δ := by
  refine ⟨hΓ.1, ?_⟩
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ⟨⟨by simp, trivial, hA⟩, rfl⟩
  · exact hΓ.2 s hs

/-- A monomorphic definition requires no additional feasibility assumption. -/
theorem envLetInMono (Γ : Env) (A : Ty) (D : Constraint) :
    Equivalent S M Δ (Γ.letIn (.def_ (.mono A) D)) ((Γ.push (.mono A)).letIn D) := by
  constructor <;> intro ρ bs ι _ _ _ h
  · have hh := (envLetInHolds Γ _ ρ bs ι).mp h
    change (Γ.letIn (.conj (Scheme.mono A).exists_ (.def_ (.mono A) D))).Holds M ρ bs ι
    exact (envLetInHolds Γ _ ρ bs ι).mpr ⟨hh.1, ⟨[], .nil, trivial⟩, hh.2⟩
  · change (Γ.letIn (.conj (Scheme.mono A).exists_ (.def_ (.mono A) D))).Holds M ρ bs ι at h
    have hh := (envLetInHolds Γ _ ρ bs ι).mp h
    exact (envLetInHolds Γ _ ρ bs ι).mpr ⟨hh.1, hh.2.2⟩

theorem inferenceLambda (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.lam body) T ε) (hd : body.Declared sig)
    (he : Entails S M Δ C (infer sig Γ (.lam body) T ε))
    (ih : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ body T ε →
      Entails S M Δ C (infer sig Γ body T ε) → Typing S M sig Δ C Γ body T ε) :
    Typing S M sig Δ C Γ (.lam body) T ε := by
  apply inferenceExistsCase hF hsig hw hd he rfl
  intro hw'
  have ha : Ty.HasKind S ([0,1,0] ++ Δ) (.bound 0) 0 := .bound rfl hF.signature.1
  have hη : Ty.HasKind S ([0,1,0] ++ Δ) (.bound 1) 1 := .bound rfl hF.signature.2.1
  have hb : Ty.HasKind S ([0,1,0] ++ Δ) (.bound 2) 0 := .bound rfl hF.signature.1
  have hsc : body.Scoped ((Γ.shift 3).push (.mono (.bound 0))) := by
    simpa [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push, Env.dpi] using hw'.2.2.2.1
  have ht := ih _ _ _ _ _ ⟨hw'.1, hw'.2.1, envPushMonoWF hw'.2.2.1 ha, hsc, hb, hη⟩
    (entailsTrans (fun ρ bs ι hρ hbs hι h =>
      ((envLetInConjunction _ _ _).1 ρ bs ι hρ hbs hι h).1) (envLetInMono _ _ _).1)
  have hl := Typing.lam (sig := sig)
    ⟨hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, arrowKind ha hη hb, emptyKind hF.signature⟩ ht
  apply Typing.sub hw' hl
  · intro ρ bs ι _ _ _ h
    exact ((envLetInHolds _ _ _ _ _).mp h).2.2.1
  · intro ρ bs ι _ _ _ h
    exact ((envLetInHolds _ _ _ _ _).mp h).2.2.2

/-- Permute the three evaluation effects used by application generation. -/
theorem effectUnionRotate (hF : EffectFramework S M)
    (ha : Ty.HasKind S Δ a 1) (hb : Ty.HasKind S Δ b 1) (hc : Ty.HasKind S Δ c 1)
    (h : Entails S M Δ C (.le 1 (.union (.union a b) c) ε)) :
    Entails S M Δ C (.le 1 (.union (.union b c) a) ε) := by
  intro ρ bs ι hρ hbs hι hC
  have hk : ∀ {T k}, Ty.HasKind S Δ T k → M.kind (T.eval M ρ bs) = k := evalKind hF hρ hbs
  have hh := h ρ bs ι hρ hbs hι hC
  have hab := hk (unionKind ha hb)
  have hbc := hk (unionKind hb hc)
  have hout := hk (unionKind (unionKind hb hc) ha)
  refine ⟨hout, hh.2.1, (hF.effectOrder _ _ hout hh.2.1).mpr ?_⟩
  have hsub := (hF.effectOrder _ _ hh.1 hh.2.1).mp hh.2.2
  simp only [Ty.union, Ty.eval, List.map_cons, List.map_nil] at hab hbc hsub ⊢
  rw [hF.unionEffect _ _ hab (hk hc), hF.unionEffect _ _ (hk ha) (hk hb)] at hsub
  rw [hF.unionEffect _ _ hbc (hk ha), hF.unionEffect _ _ (hk hb) (hk hc)]
  simpa only [Set.union_assoc, Set.union_comm, Set.union_left_comm] using hsub

theorem inferenceApplication (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.app f x) T ε) (hd : (Expr.app f x).Declared sig)
    (he : Entails S M Δ C (infer sig Γ (.app f x) T ε))
    (ihf : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ f T ε →
      Entails S M Δ C (infer sig Γ f T ε) → Typing S M sig Δ C Γ f T ε)
    (ihx : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ x T ε →
      Entails S M Δ C (infer sig Γ x T ε) → Typing S M sig Δ C Γ x T ε) :
    Typing S M sig Δ C Γ (.app f x) T ε := by
  apply inferenceExistsCase hF hsig hw hd he rfl
  intro hw'
  have ha : Ty.HasKind S ([0,1,1,1] ++ Δ) (.bound 0) 0 := .bound rfl hF.signature.1
  have hη : Ty.HasKind S ([0,1,1,1] ++ Δ) (.bound 1) 1 := .bound rfl hF.signature.2.1
  have hf : Ty.HasKind S ([0,1,1,1] ++ Δ) (.bound 2) 1 := .bound rfl hF.signature.2.1
  have hx : Ty.HasKind S ([0,1,1,1] ++ Δ) (.bound 3) 1 := .bound rfl hF.signature.2.1
  have hfs : f.Scoped (Γ.shift 4) := ⟨hw'.2.2.2.1.1.1,
    fun _ h => hw'.2.2.2.1.2 (Finset.mem_union_left _ h)⟩
  have hxs : x.Scoped (Γ.shift 4) := ⟨hw'.2.2.2.1.1.2,
    fun _ h => hw'.2.2.2.1.2 (Finset.mem_union_right _ h)⟩
  have htf := ihf _ _ _ _ _ ⟨hw'.1, hw'.2.1, hw'.2.2.1, hfs,
    arrowKind ha hη hw'.2.2.2.2.1, hf⟩ (by
      intro ρ bs ι _ _ _ h
      have hh := (envLetInHolds _ _ _ _ _).mp h
      exact (envLetInHolds _ _ _ _ _).mpr ⟨hh.1, hh.2.1⟩)
  have htx := ihx _ _ _ _ _ ⟨hw'.1, hw'.2.1, hw'.2.2.1, hxs, ha, hx⟩ (by
      intro ρ bs ι _ _ _ h
      have hh := (envLetInHolds _ _ _ _ _).mp h
      exact (envLetInHolds _ _ _ _ _).mpr ⟨hh.1, hh.2.2.1⟩)
  have ht := Typing.app ⟨hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1,
    hw'.2.2.2.2.1, unionKind (unionKind hf hx) hη⟩ htf htx
  apply Typing.sub hw' ht (leRefl hF hF.signature.1 hw'.2.2.2.2.1)
  apply effectUnionRotate hF hη hf hx
  intro ρ bs ι _ _ _ h
  exact ((envLetInHolds _ _ _ _ _).mp h).2.2.2

theorem inferenceMonoLet (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.letE rhs body) T ε)
    (hd : (Expr.letE rhs body).Declared sig) (hv : rhs.isValue = false)
    (he : Entails S M Δ C (infer sig Γ (.letE rhs body) T ε))
    (ihr : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ rhs T ε →
      Entails S M Δ C (infer sig Γ rhs T ε) → Typing S M sig Δ C Γ rhs T ε)
    (ihb : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ body T ε →
      Entails S M Δ C (infer sig Γ body T ε) → Typing S M sig Δ C Γ body T ε) :
    Typing S M sig Δ C Γ (.letE rhs body) T ε := by
  apply inferenceExistsCase hF hsig hw hd he (by simp only [generate, hv, Bool.false_eq_true, ↓reduceIte]; rfl)
  intro hw'
  have ha : Ty.HasKind S ([0,1,1] ++ Δ) (.bound 0) 0 := .bound rfl hF.signature.1
  have hr : Ty.HasKind S ([0,1,1] ++ Δ) (.bound 1) 1 := .bound rfl hF.signature.2.1
  have hb : Ty.HasKind S ([0,1,1] ++ Δ) (.bound 2) 1 := .bound rfl hF.signature.2.1
  have hrs : rhs.Scoped (Γ.shift 3) := ⟨hw'.2.2.2.1.1.1,
    fun _ h => hw'.2.2.2.1.2 (Finset.mem_union_left _ h)⟩
  have hbs : body.Scoped ((Γ.shift 3).push (.mono (.bound 0))) :=
    ⟨hw'.2.2.2.1.1.2, fun _ h => hw'.2.2.2.1.2 (Finset.mem_union_right _ h)⟩
  have htr := ihr _ _ _ _ _ ⟨hw'.1, hw'.2.1, hw'.2.2.1, hrs, ha, hr⟩ (by
    intro ρ bs ι _ _ _ h
    have hh := (envLetInHolds _ _ _ _ _).mp h
    exact (envLetInHolds _ _ _ _ _).mpr ⟨hh.1, hh.2.1⟩)
  have htb := ihb _ _ _ _ _ ⟨hw'.1, hw'.2.1, envPushMonoWF hw'.2.2.1 ha,
    hbs, hw'.2.2.2.2.1, hb⟩ (by
    apply entailsTrans _ (envLetInMono _ _ _).1
    intro ρ bs ι _ _ _ h
    have hh := (envLetInHolds _ _ _ _ _).mp h
    exact (envLetInHolds _ _ _ _ _).mpr ⟨hh.1, hh.2.2.1⟩)
  have ht := Typing.letMono ⟨hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1,
    hw'.2.2.2.2.1, unionKind hr hb⟩ htr htb
  apply Typing.sub hw' ht (leRefl hF hF.signature.1 hw'.2.2.2.2.1)
  intro ρ bs ι _ _ _ h
  exact ((envLetInHolds _ _ _ _ _).mp h).2.2.2

/-- Opening a declaration by its own bound variables leaves it unchanged. -/
theorem declarationOpenSelf (hT : Ty.HasKind S ks T k) :
    T.openAt 0 ((List.range ks.length).map Ty.bound) = T := by
  induction T using tyInduction generalizing k with
  | hf X => simp [Ty.openAt]
  | hb i =>
      cases hT with
      | bound hi _ =>
          have hlt := (List.getElem?_eq_some_iff.mp hi).1
          simp [Ty.openAt, List.getElem?_map, List.getElem?_range hlt]
  | hc f ts ih =>
      cases hT with
      | con _ hs =>
          simp only [Ty.openAt]
          congr 1
          trans ts.map id
          · apply List.map_congr_left
            intro T hT
            obtain ⟨k, _, hk⟩ := forall₂MemLeft hs hT
            exact ih T hT hk
          · exact List.map_id ts

theorem boundArgumentsKind (hks : ∀ k ∈ ks, k ∈ S.kinds) :
    List.Forall₂ (Ty.HasKind S (ks ++ Δ)) ((List.range ks.length).map Ty.bound) ks := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hi hj
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
  apply Ty.HasKind.bound _ (hks _ (List.getElem_mem hj))
  simp [List.getElem?_append, hj]

theorem inferencePerform (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.perform op arg) T ε)
    (hd : (Expr.perform op arg).Declared sig)
    (he : Entails S M Δ C (infer sig Γ (.perform op arg) T ε))
    (ih : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ arg T ε →
      Entails S M Δ C (infer sig Γ arg T ε) → Typing S M sig Δ C Γ arg T ε) :
    Typing S M sig Δ C Γ (.perform op arg) T ε := by
  cases hs : sig op with
  | none => exact False.elim (hd.1 hs)
  | some decl =>
      have hdecl := hsig op decl hs
      apply inferenceExistsCase hF hsig hw hd he (by simp only [generate, hs]; rfl)
      intro hw'
      have ha : Ty.HasKind S ((decl.kinds ++ [1]) ++ Δ) decl.input 0 := by
        simpa only [List.append_assoc] using kindAppend hdecl.2.1 ([1] ++ Δ)
      have hb : Ty.HasKind S ((decl.kinds ++ [1]) ++ Δ) decl.output 0 := by
        simpa only [List.append_assoc] using kindAppend hdecl.2.2.1 ([1] ++ Δ)
      have hη : Ty.HasKind S ((decl.kinds ++ [1]) ++ Δ) (.bound decl.kinds.length) 1 :=
        .bound (by simp) hF.signature.2.1
      have ht := ih _ _ _ _ _ ⟨hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, ha, hη⟩ (by
        intro ρ bs ι _ _ _ h
        have hh := (envLetInHolds _ _ _ _ _).mp h
        exact (envLetInHolds _ _ _ _ _).mpr ⟨hh.1, hh.2.2.1⟩)
      have hargs := boundArgumentsKind (Δ := [1] ++ Δ) hdecl.1
      rw [← List.append_assoc] at hargs
      have hi := declarationOpenSelf hdecl.2.1
      have ho := declarationOpenSelf hdecl.2.2.1
      have ht' := ht
      nth_rw 2 [← hi] at ht'
      have hwop : JudgmentWF S ((decl.kinds ++ [1]) ++ Δ) _ _ (.perform op arg)
          decl.output (.union (.singleton op) (.bound decl.kinds.length)) :=
        ⟨hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, hb, unionKind (singletonKind op) hη⟩
      nth_rw 2 [← ho] at hwop
      have hop := Typing.perform hwop hs hargs (by
        rw [conditionDeclarationOpenSelf hdecl.2.2.2.2.2.1]
        intro ρ bs ι _ _ _ h
        exact (constraintGroundIndependent
          (by simpa only [List.append_assoc] using constraintAppendWF hdecl.2.2.2.2.2.1 ([1] ++ Δ))
          hdecl.2.2.2.2.2.2.1 ρ bs _ ι).mp ((envLetInHolds _ _ _ _ _).mp h).2.1) ht'
      rw [ho] at hop
      apply Typing.sub hw' hop
      · intro ρ bs ι _ _ _ h
        simpa only [List.length_append, List.length_cons, List.length_nil, Constraint.le, Constraint.Holds] using ((envLetInHolds _ _ _ _ _).mp h).2.2.2.1
      · intro ρ bs ι _ _ _ h
        simpa only [List.length_append, List.length_cons, List.length_nil, Constraint.le, Constraint.Holds] using ((envLetInHolds _ _ _ _ _).mp h).2.2.2.2

/-- A universal premise can be used under the same newly bound variables. -/
theorem entailsForallOpen (hw : Constraint.WF S Δ 0 C)
    (he : Entails S M Δ C (.forall_ ks D)) :
    Entails S M (ks ++ Δ) (C.shift ks.length 0) D := by
  intro ρ bs ι hρ hbs hι hC
  have hv := List.forall₂_take_append bs ks Δ hbs
  have hb := List.forall₂_drop_append bs ks Δ hbs
  have hn := hv.length_eq
  have heq : bs.take ks.length ++ bs.drop ks.length = bs := List.take_append_drop _ _
  have hc : C.Holds M ρ (bs.drop ks.length) ι := by
    apply (constraintShiftHolds hw ρ _ (bs.take ks.length) ι).mp
    simpa only [hn, heq] using hC
  simpa only [heq] using he ρ _ ι hρ hb hι hc _ hv


theorem entailsForallImplicationOpen (hw : Constraint.WF S Δ 0 C)
    (he : Entails S M Δ C (.forall_ ks (.implies P D))) :
    Entails S M (ks ++ Δ) (.conj (C.shift ks.length 0) P) D :=
  fun ρ bs ι hρ hbs hι h => entailsForallOpen hw he ρ bs ι hρ hbs hι h.1 h.2

theorem inferenceHandle (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.handle body op ret clause) T ε)
    (hd : (Expr.handle body op ret clause).Declared sig)
    (he : Entails S M Δ C (infer sig Γ (.handle body op ret clause) T ε))
    (ihb : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ body T ε →
      Entails S M Δ C (infer sig Γ body T ε) → Typing S M sig Δ C Γ body T ε)
    (ihr : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ ret T ε →
      Entails S M Δ C (infer sig Γ ret T ε) → Typing S M sig Δ C Γ ret T ε)
    (ihc : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ clause T ε →
      Entails S M Δ C (infer sig Γ clause T ε) → Typing S M sig Δ C Γ clause T ε) :
    Typing S M sig Δ C Γ (.handle body op ret clause) T ε := by
  cases hs : sig op with
  | none => exact False.elim (hd.1 hs)
  | some decl =>
      have hdecl := hsig op decl hs
      apply inferenceExistsCase hF hsig hw hd he (by simp only [generate, hs]; rfl)
      intro hw'
      have ha : Ty.HasKind S ([0,1,0,1] ++ Δ) (.bound 0) 0 := .bound rfl hF.signature.1
      have hei : Ty.HasKind S ([0,1,0,1] ++ Δ) (.bound 1) 1 := .bound rfl hF.signature.2.1
      have hb : Ty.HasKind S ([0,1,0,1] ++ Δ) (.bound 2) 0 := .bound rfl hF.signature.1
      have heo : Ty.HasKind S ([0,1,0,1] ++ Δ) (.bound 3) 1 := .bound rfl hF.signature.2.1
      have hbs : body.Scoped (Γ.shift 4) := ⟨hw'.2.2.2.1.1.1,
        fun _ h => hw'.2.2.2.1.2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))⟩
      have hrs : ret.Scoped ((Γ.shift 4).push (.mono (.bound 0))) :=
        ⟨hw'.2.2.2.1.1.2.1,
          fun _ h => hw'.2.2.2.1.2 (Finset.mem_union_left _ (Finset.mem_union_right _ h))⟩
      have htb := ihb _ _ _ _ _ ⟨hw'.1, hw'.2.1, hw'.2.2.1, hbs, ha, hei⟩ (by
        intro ρ bs ι _ _ _ h
        have hh := (envLetInHolds _ _ _ _ _).mp h
        exact (envLetInHolds _ _ _ _ _).mpr ⟨hh.1, hh.2.1⟩)
      have htr := ihr _ _ _ _ _ ⟨hw'.1, hw'.2.1, envPushMonoWF hw'.2.2.1 ha, hrs, hb, heo⟩ (by
        apply entailsTrans _ (envLetInMono _ _ _).1
        intro ρ bs ι _ _ _ h
        have hh := (envLetInHolds _ _ _ _ _).mp h
        exact (envLetInHolds _ _ _ _ _).mpr ⟨hh.1, hh.2.2.2.1⟩)
      have hcw := envPushMonoWF (envPushMonoWF (envShiftWF hw'.2.2.1 decl.kinds)
        (kindAppend hdecl.2.1 _))
        (arrowKind (kindAppend hdecl.2.2.1 _) (kindShift heo _) (kindShift hb _))
      have hcs : clause.Scoped (((Γ.shift 4).shift decl.kinds.length |>.push (.mono decl.input)).push
          (.mono (.arrow decl.output ((Ty.bound 3).shift decl.kinds.length 0)
            ((Ty.bound 2).shift decl.kinds.length 0)))) := by
        refine ⟨?_, ?_⟩
        · simpa [Env.push, Env.shift, Nat.add_assoc] using hw'.2.2.2.1.1.2.2
        · intro x hx
          simpa only [Env.dpi, Env.push, Env.shift, List.map_map, Function.comp_def] using
            hw'.2.2.2.1.2 (Finset.mem_union_right _ hx)
      have hpw := constraintAppendWF hdecl.2.2.2.2.2.1 ([0,1,0,1] ++ Δ)
      have hpf := hdecl.2.2.2.2.2.2.1
      have htc := ihc _ (.conj _ decl.condition) _ _ _
        ⟨⟨constraintShiftWF hw'.1 decl.kinds, hpw⟩,
          Finset.union_eq_empty.mpr ⟨(constraintShiftFpi _ _ _).trans hw'.2.1, hpf⟩,
          hcw, hcs, kindShift hb _, kindShift heo _⟩ (by
        apply entailsTrans _ (envLetInMono _ _ _).1
        apply entailsTrans _ (envLetInMono _ _ _).1
        apply entailsForallImplicationOpen hw'.1
        intro ρ bs ι _ _ _ h us hu
        have hh := (envLetInHolds _ _ _ _ _).mp h
        have hg := ((envLetInForall hw'.2.2.1 _ _ ρ bs ι).mp
          ((envLetInHolds _ _ _ _ _).mpr ⟨hh.1, hh.2.2.2.2.1⟩)).2 us hu
        exact ((envLetInImplication hpw hpf _ _ ρ (us ++ bs) ι).mp hg).2)
      have ht := Typing.handle
        ⟨hw'.1, hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, hb, heo⟩ hs htb
        (fun _ _ _ _ _ _ h => ((envLetInHolds _ _ _ _ _).mp h).2.2.1) htr htc
      apply Typing.sub hw' ht
      · intro ρ bs ι _ _ _ h
        exact ((envLetInHolds _ _ _ _ _).mp h).2.2.2.2.2.1
      · intro ρ bs ι _ _ _ h
        exact ((envLetInHolds _ _ _ _ _).mp h).2.2.2.2.2.2

/-- Structural soundness with arbitrary stronger outer constraints. -/
theorem inferenceSoundnessAux (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (e : Expr) : ∀ Δ C Γ T ε, JudgmentWF S Δ C Γ e T ε → e.Declared sig →
      Entails S M Δ C (infer sig Γ e T ε) → Typing S M sig Δ C Γ e T ε := by
  induction e with
  | ident x => intro Δ C Γ T ε hw _ he; exact inferenceVariable hF hw he
  | lam body ih =>
      intro Δ C Γ T ε hw hd he
      exact inferenceLambda hF hsig hw hd he (fun Δ C Γ T ε hw he => ih Δ C Γ T ε hw hd he)
  | app f x ihf ihx =>
      intro Δ C Γ T ε hw hd he
      exact inferenceApplication hF hsig hw hd he
        (fun Δ C Γ T ε hw he => ihf Δ C Γ T ε hw hd.1 he)
        (fun Δ C Γ T ε hw he => ihx Δ C Γ T ε hw hd.2 he)
  | letE rhs body ihr ihb =>
      intro Δ C Γ T ε hw hd he
      have hr := fun Δ C Γ T ε hw he => ihr Δ C Γ T ε hw hd.1 he
      have hb := fun Δ C Γ T ε hw he => ihb Δ C Γ T ε hw hd.2 he
      cases hv : rhs.isValue with
      | true => exact inferenceValueLet hF hsig hw hd.1 hv he hr hb
      | false => exact inferenceMonoLet hF hsig hw hd hv he hr hb
  | perform op arg ih =>
      intro Δ C Γ T ε hw hd he
      exact inferencePerform hF hsig hw hd he (fun Δ C Γ T ε hw he => ih Δ C Γ T ε hw hd.2 he)
  | handle body op ret clause ihb ihr ihc =>
      intro Δ C Γ T ε hw hd he
      exact inferenceHandle hF hsig hw hd he
        (fun Δ C Γ T ε hw he => ihb Δ C Γ T ε hw hd.2.1 he)
        (fun Δ C Γ T ε hw he => ihr Δ C Γ T ε hw hd.2.2.1 he)
        (fun Δ C Γ T ε hw he => ihc Δ C Γ T ε hw hd.2.2.2 he)

/-- ATTAPL 10.4.4 extended with evaluation effects and deep handlers. -/
theorem inferenceSoundness (S : Signature) (M : Model) (sig : OpSignature) :
    InferenceSoundnessGoal S M sig := by
  intro hA Δ Γ e T ε _ hΓ he hd hT hε
  exact inferenceSoundnessAux hA.1 hA.2 e _ _ _ _ _
    (inferJudgmentWF hA.1.signature hA.2 hΓ he hd hT hε) hd entailsRefl

end EHMX
