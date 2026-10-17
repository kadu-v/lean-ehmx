import EHMX.Proofs.TypeSubstitution
import EHMX.Typing

/-!
型・効果代入の使用先は多相 let の各具体化と handler 操作節の具体化。
SystemFXi.Poly.Typing.substKind_preserves (9173a02d9c67eea0b0c665d3319d834e3947518f)
と同じく、帰納仮定は代入先の型文脈と代入全体について一般化する。
EHMX 固有の制約強化では含意も代入し、exists_ / letPoly では外側の
制約と環境を同時に変換する。項には型引数がないので項自体は変化しない。
-/
namespace EHMX

theorem lookupWF (hΓ : Env.WF S Δ Γ) (hl : Γ.lookup x = some s) :
    s.WF S Δ 0 ∧ s.fpi = ∅ := by
  cases x with
  | bound i => exact hΓ.2 s (List.mem_of_getElem? hl)
  | free x =>
      simp only [Env.lookup, Option.map_eq_some_iff] at hl
      obtain ⟨p, hp, he⟩ := hl
      subst s
      exact hΓ.1 p (List.mem_reverse.mp (List.mem_of_find?_eq_some hp))

theorem lookupSubstBound (Γ : Env) (x : PVar) (σ : BoundSubst) :
    (Γ.substBound σ).lookup x = (Γ.lookup x).map (Scheme.substBound σ) := by
  cases x with
  | bound i => simp [Env.lookup, Env.substBound, List.getElem?_map]
  | free x =>
      simp only [Env.lookup, Env.substBound, ← List.map_reverse]
      generalize Γ.free.reverse = ps
      induction ps with
      | nil => rfl
      | cons p ps ih =>
          simp only [List.map_cons, List.find?_cons]
          split <;> simp_all

@[simp] theorem envSubstBoundPush (Γ : Env) (s : Scheme) (σ : BoundSubst) :
    (Γ.push s).substBound σ = (Γ.substBound σ).push (s.substBound σ) := rfl

@[simp] theorem monoSubstBound (T : Ty) (σ : BoundSubst) :
    (Scheme.mono T).substBound σ = .mono (T.substBound σ) := by
  simp [Scheme.mono, Scheme.substBound, Constraint.substBound]

theorem judgmentSubstBound (h : JudgmentWF S Δ C Γ e T ε)
    (hσ : BoundSubst.Valid S Δ Δ' σ) :
    JudgmentWF S Δ' (C.substBound σ) (Γ.substBound σ) e
      (T.substBound σ) (ε.substBound σ) := by
  refine ⟨(substBoundWF S).1 _ _ _ h.1 _ _ hσ,
    (substBoundFpi.1 _ _).trans h.2.1, envSubstBoundWF h.2.2.1 hσ,
    ?_, kindSubstBound h.2.2.2.2.1 hσ, kindSubstBound h.2.2.2.2.2 hσ⟩
  simpa [Expr.Scoped, Env.substBound, Env.dpi, List.map_map, Function.comp_def]
    using h.2.2.2.1

theorem leConstraintWF (hk : k ∈ S.kinds) (hT : Ty.HasKind S Δ T k)
    (hU : Ty.HasKind S Δ U k) : (Constraint.le k T U).WF S Δ n :=
  ⟨hk, .cons hT (.cons hU .nil)⟩

theorem instanceConstraintWF (hS : S.WF) (hs : Scheme.WF S Δ n s)
    (hT : Ty.HasKind S Δ T 0) : (s.instanceConstraint T).WF S Δ n := by
  cases s with
  | all ks C A =>
      exact ⟨hs.1, hs.2.1, leConstraintWF hS.1 hs.2.2 (kindShift hT ks)⟩

/-- No requirement that every entry of Δ be declared is added: `BoundSubst.Valid`
also permits renaming an unused undeclared entry to an entry of the same kind. -/
theorem typingTypeEffectSubstitution (hF : EffectFramework S M)
    (hsig : OpSignature.WF S sig) (ht : Typing S M sig Δ C Γ e T ε) :
    ∀ Δ' σ, BoundSubst.Valid S Δ Δ' σ →
      Typing S M sig Δ' (C.substBound σ) (Γ.substBound σ) e
        (T.substBound σ) (ε.substBound σ) := by
  induction ht with
  | var hw hl he =>
      intro Δ' σ hσ
      have hs := lookupWF hw.2.2.1 hl
      have he' := entailsSubstBound hF hσ hw.1
        (instanceConstraintWF hF.signature hs.1 hw.2.2.2.2.1) he
      rw [instanceSubstBound] at he'
      have hw' := judgmentSubstBound hw hσ
      simp only [Ty.empty, Ty.substBound, List.map_nil] at hw' ⊢
      exact Typing.var hw' (by rw [lookupSubstBound, hl]; rfl) he'
  | lam hw hb ih =>
      intro Δ' σ hσ
      have hb' := ih _ _ hσ
      simp only [envSubstBoundPush, monoSubstBound] at hb'
      have hw' := judgmentSubstBound hw hσ
      simp only [Ty.arrow, Ty.empty, Ty.substBound, List.map_cons, List.map_nil] at hw' ⊢
      exact Typing.lam hw' hb'
  | app hw hf hx ihf ihx =>
      intro Δ' σ hσ
      have hf' := ihf _ _ hσ
      simp only [Ty.arrow, Ty.substBound, List.map_cons, List.map_nil] at hf'
      have hw' := judgmentSubstBound hw hσ
      simp only [Ty.union, Ty.substBound, List.map_cons, List.map_nil] at hw' ⊢
      exact Typing.app hw' hf' (ihx _ _ hσ)
  | letMono hw hr hb ihr ihb =>
      intro Δ' σ hσ
      have hb' := ihb _ _ hσ
      simp only [envSubstBoundPush, monoSubstBound] at hb'
      have hw' := judgmentSubstBound hw hσ
      simp only [Ty.union, Ty.substBound, List.map_cons, List.map_nil] at hw' ⊢
      exact Typing.letMono hw' (ihr _ _ hσ) hb'
  | @letPoly Δ C Γ rhs body B ε ks D A hw hv hr he hb ihr ihb =>
      intro Δ' σ hσ
      have hr' := ihr _ _ (BoundSubst.validLift hσ ks)
      simp only [Constraint.substBound, constraintShiftLiftSubst, envShiftLiftSubst,
        Ty.empty, Ty.substBound, List.map_nil] at hr'
      have hwD : (Constraint.exists_ ks D).WF S Δ 0 :=
        ⟨(lookupWF (typingWF hb).2.2.1 (x := .bound 0) rfl).1.1,
          (typingWF hr).1.2⟩
      have he' := entailsSubstBound hF hσ hw.1 hwD he
      have hb' := ihb _ _ hσ
      simp only [envSubstBoundPush, Scheme.substBound] at hb'
      exact .letPoly (judgmentSubstBound hw hσ) hv hr' he' hb'
  | @perform Δ C Γ op arg ε decl args hw hs ha ht ih =>
      intro Δ' σ hσ
      have hd := hsig op decl hs
      have ht' := ih _ _ hσ
      rw [declarationOpenSubstBound hd.2.1 ha] at ht'
      have hw' := judgmentSubstBound hw hσ
      rw [declarationOpenSubstBound hd.2.2.1 ha] at hw' ⊢
      simp only [Ty.union, Ty.singleton, Ty.substBound, List.map_cons, List.map_nil] at hw' ⊢
      exact .perform hw' hs
        (List.forall₂_map_left_iff.mpr (forall₂ImplMem ha (fun _ _ _ h => kindSubstBound h hσ))) ht'
  | @handle Δ C Γ body op ret clause B εout decl A εin hw hs hb he hr hc ihb ihr ihc =>
      intro Δ' σ hσ
      have hd := hsig op decl hs
      have hr' := ihr _ _ hσ
      simp only [envSubstBoundPush, monoSubstBound] at hr'
      have hc' := ihc _ _ (BoundSubst.validLift hσ decl.kinds)
      simp only [constraintShiftLiftSubst, envSubstBoundPush, monoSubstBound,
        envShiftLiftSubst, Ty.arrow, Ty.substBound, List.map_cons, List.map_nil,
        declarationSubstBound hd.2.1, declarationSubstBound hd.2.2.1,
        tyShiftLiftSubst] at hc'
      have he' := entailsSubstBound hF hσ hw.1
        (leConstraintWF hF.signature.2.1 (typingWF hb).2.2.2.2.2
          (unionKind (singletonKind op) hw.2.2.2.2.2)) he
      simp only [Constraint.substBound, Constraint.le, Ty.union, Ty.singleton,
        Ty.substBound, List.map_cons, List.map_nil] at he'
      exact .handle (judgmentSubstBound hw hσ) hs (ihb _ _ hσ) he' hr' hc'
  | sub hw ht hT hε ih =>
      intro Δ' σ hσ
      have htw := typingWF ht
      have hT' := entailsSubstBound hF hσ hw.1
        (leConstraintWF hF.signature.1 htw.2.2.2.2.1 hw.2.2.2.2.1) hT
      have hε' := entailsSubstBound hF hσ hw.1
        (leConstraintWF hF.signature.2.1 htw.2.2.2.2.2 hw.2.2.2.2.2) hε
      exact .sub (judgmentSubstBound hw hσ) (ih _ _ hσ) hT' hε'
  | strengthen hw ht he ih =>
      intro Δ' σ hσ
      exact .strengthen (judgmentSubstBound hw hσ) (ih _ _ hσ)
        (entailsSubstBound hF hσ hw.1 (typingWF ht).1 he)
  | @exists_ Δ ks C Γ e T ε hw ht ih =>
      intro Δ' σ hσ
      have ht' := ih _ _ (BoundSubst.validLift hσ ks)
      simp only [envShiftLiftSubst, tyShiftLiftSubst] at ht'
      exact .exists_ (judgmentSubstBound hw hσ) ht'

/-- Instantiate a block without changing the remaining, possibly open, context. -/
theorem typingInstantiate (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (ht : Typing S M sig (ks ++ Δ) C Γ e T ε)
    (hargs : List.Forall₂ (Ty.HasKind S Δ) args ks) :
    Typing S M sig Δ (C.substBound (BoundSubst.many args))
      (Γ.substBound (BoundSubst.many args)) e (T.openAt 0 args) (ε.openAt 0 args) := by
  simpa only [tyOpenMany] using
    typingTypeEffectSubstitution hF hsig ht Δ _ (BoundSubst.validMany hargs)

/-- The argument and continuation types are instantiated by the *same* list.
This is type/effect instantiation only; substitution of the two term values and
reconstruction of the captured continuation remain separate proof obligations. -/
theorem operationClauseInstantiation {Γ : Env} (hF : EffectFramework S M)
    (hsig : OpSignature.WF S sig)
    (ht : Typing S M sig (ks ++ Δ) (C.shift ks.length 0)
      (((Γ.shift ks.length).push (.mono A)).push
        (.mono (.arrow R (ε.shift ks.length 0) (B.shift ks.length 0))))
      clause (B.shift ks.length 0) (ε.shift ks.length 0))
    (hargs : List.Forall₂ (Ty.HasKind S Δ) args ks) :
    Typing S M sig Δ C
      ((Γ.push (.mono (A.openAt 0 args))).push
        (.mono (.arrow (R.openAt 0 args) ε B))) clause B ε := by
  have h := typingTypeEffectSubstitution hF hsig ht Δ _ (BoundSubst.validMany hargs)
  have hlen := hargs.length_eq
  simpa only [← hlen, constraintShiftMany, envSubstBoundPush, monoSubstBound,
    envShiftMany, Ty.arrow, Ty.substBound, List.map_cons, List.map_nil,
    tyShiftMany, tyOpenMany] using h

end EHMX
