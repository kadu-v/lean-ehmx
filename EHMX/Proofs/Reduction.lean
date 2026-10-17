import EHMX.Proofs.ValueSubstitution
import EHMX.Proofs.Progress

/-! 使用先は保存の β・let・return 分岐。制約強化と存在量化を
反転の外へ飛び越えず、内側の判断で代入を完了する。 -/
namespace EHMX

theorem effectUnionRight (hF : EffectFramework S M)
    (hε : Ty.HasKind S Δ ε 1) (hη : Ty.HasKind S Δ η 1) :
    Entails S M Δ C (.le 1 η (.union ε η)) := by
  intro ρ bs ι hρ hbs _ _
  have hy := evalKind hF hρ hbs hη
  have hu := evalKind hF hρ hbs (unionKind hε hη)
  refine ⟨hy, hu, (hF.effectOrder _ _ hy hu).mpr ?_⟩
  rw [effectsUnion hF hρ hbs (unionKind hε hη)]
  exact Set.subset_union_right

/-- Inversion through sub/strengthen/exists for a let redex; both let rules occur. -/
theorem letPreservation (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hv : Value v) (ht : Typing S M sig Δ C Γ e T ε) :
    e = .letE v body → Typing S M sig Δ C Γ (body.openAt 0 [v]) T ε := by
  induction ht with
  | var | lam | app | perform | handle => intro h; cases h
  | letMono hw hr hb ihr ihb =>
      intro h; cases h
      have ht' := valueSubstitution hF hsig hv (valuePure hF hr hv) hb
      exact .sub (judgmentWithScope hw (typingWF ht').2.2.2.1) ht'
        (leRefl hF hF.signature.1 hw.2.2.2.2.1)
        (effectUnionRight hF (typingWF hr).2.2.2.2.2 (typingWF hb).2.2.2.2.2)
  | letPoly hw _ hr he hb ihr ihb =>
      intro h; cases h
      exact schemeValueSubstitution S M sig ⟨hF, hsig⟩ _ _ _ _ _ _ _ _ _ _ hv hr he hb
  | sub hw ht hT hε ih =>
      intro h
      have ht' := ih h
      exact .sub (judgmentWithScope hw (typingWF ht').2.2.2.1) ht' hT hε
  | strengthen hw ht he ih =>
      intro h
      have ht' := ih h
      exact .strengthen (judgmentWithScope hw (typingWF ht').2.2.2.1) ht' he
  | exists_ hw ht ih =>
      intro h
      have ht' := ih h
      apply Typing.exists_ (judgmentWithScope hw ?_) ht'
      simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def]
        using (typingWF ht').2.2.2.1

theorem returnPreservation (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hv : Value v) (ht : Typing S M sig Δ C Γ e T ε) :
    e = .handle v op ret clause → Typing S M sig Δ C Γ (ret.openAt 0 [v]) T ε := by
  induction ht with
  | var | lam | app | letMono | letPoly | perform => intro h; cases h
  | handle hw hs hb he hr hc ihb ihr ihc =>
      intro h; cases h
      exact valueSubstitution hF hsig hv (valuePure hF hb hv) hr
  | sub hw ht hT hε ih =>
      intro h
      have ht' := ih h
      exact .sub (judgmentWithScope hw (typingWF ht').2.2.2.1) ht' hT hε
  | strengthen hw ht he ih =>
      intro h
      have ht' := ih h
      exact .strengthen (judgmentWithScope hw (typingWF ht').2.2.2.1) ht' he
  | exists_ hw ht ih =>
      intro h
      have ht' := ih h
      apply Typing.exists_ (judgmentWithScope hw ?_) ht'
      simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def]
        using (typingWF ht').2.2.2.1

theorem leTrans (hF : EffectFramework S M) (hk : k ∈ S.kinds)
    (hTU : Entails S M Δ C (.le k T U)) (hUV : Entails S M Δ C (.le k U V)) :
    Entails S M Δ C (.le k T V) := by
  intro ρ bs ι hρ hbs hι hC
  have h := hTU _ _ _ hρ hbs hι hC
  have h' := hUV _ _ _ hρ hbs hι hC
  exact ⟨h.1, h'.2.1, hF.belowTrans k hk _ _ _ h.1 h.2.1 h'.2.1 h.2.2 h'.2.2⟩

theorem arrowKinds (h : Ty.HasKind S Δ (.arrow A ε B) 0) :
    Ty.HasKind S Δ A 0 ∧ Ty.HasKind S Δ ε 1 ∧ Ty.HasKind S Δ B 0 := by
  cases h with
  | con _ hs =>
      cases hs with
      | cons hA hs => cases hs with
        | cons hε hs => cases hs with | cons hB _ => exact ⟨hA, hε, hB⟩

theorem arrowLeComponents (hF : EffectFramework S M)
    (hleft : Ty.HasKind S Δ (.arrow A ε B) 0)
    (hright : Ty.HasKind S Δ (.arrow A' ε' B') 0)
    (h : Entails S M Δ C (.le 0 (.arrow A ε B) (.arrow A' ε' B'))) :
    Entails S M Δ C (.le 0 A' A) ∧ Entails S M Δ C (.le 1 ε ε') ∧
      Entails S M Δ C (.le 0 B B') := by
  have H : ∀ ρ bs ι, Assignment.Valid S M ρ → KindValues M Δ bs → ι.Valid →
      C.Holds M ρ bs ι →
      (Constraint.le 0 A' A).Holds M ρ bs ι ∧
      (Constraint.le 1 ε ε').Holds M ρ bs ι ∧
      (Constraint.le 0 B B').Holds M ρ bs ι := by
    intro ρ bs ι hρ hbs hι hC
    have hA := evalKind hF hρ hbs (arrowKinds hleft).1
    have hε := evalKind hF hρ hbs (arrowKinds hleft).2.1
    have hB := evalKind hF hρ hbs (arrowKinds hleft).2.2
    have hA' := evalKind hF hρ hbs (arrowKinds hright).1
    have hε' := evalKind hF hρ hbs (arrowKinds hright).2.1
    have hB' := evalKind hF hρ hbs (arrowKinds hright).2.2
    have hp := (hF.arrowOrder _ _ _ _ _ _ hA hε hB hA' hε' hB').mp
      (by simpa only [Ty.arrow, Ty.eval, List.map_cons, List.map_nil] using
        (h _ _ _ hρ hbs hι hC).2.2)
    exact ⟨⟨hA', hA, hp.1⟩, ⟨hε, hε', hp.2.1⟩, ⟨hB, hB', hp.2.2⟩⟩
  exact ⟨fun _ _ _ hρ hbs hι hC => (H _ _ _ hρ hbs hι hC).1,
    fun _ _ _ hρ hbs hι hC => (H _ _ _ hρ hbs hι hC).2.1,
    fun _ _ _ hρ hbs hι hC => (H _ _ _ hρ hbs hι hC).2.2⟩

theorem typingShift (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (ht : Typing S M sig Δ C Γ e T ε) (ks : List Kind) :
    Typing S M sig (ks ++ Δ) (C.shift ks.length 0) (Γ.shift ks.length) e
      (T.shift ks.length 0) (ε.shift ks.length 0) := by
  simpa only [shiftSubstBound.1, envShiftSubstBound, tyShiftSubstBound,
    Nat.not_lt_zero, ↓reduceIte] using
    typingTypeEffectSubstitution hF hsig ht _ _ (BoundSubst.validShift ks)

/-- Arrow inversion keeps existential witnesses inside the typing derivation.
D is generalized so the strengthen case can use the same argument derivation. -/
theorem lambdaApplication (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (ht : Typing S M sig Δ C Γ e T ε) :
    ∀ body, e = .lam body → ∀ D v A η B,
      D.WF S Δ 0 → D.fpi = ∅ → Entails S M Δ D C → Value v →
      Typing S M sig Δ D Γ v A .empty →
      Ty.HasKind S Δ η 1 → Ty.HasKind S Δ B 0 →
      Entails S M Δ D (.le 0 T (.arrow A η B)) →
      Typing S M sig Δ D Γ (body.openAt 0 [v]) B η := by
  induction ht with
  | var | app | letMono | letPoly | perform | handle => intro body h; cases h
  | lam hw hb ih =>
      intro body h D v A η B hD hDf hDC hv hvT hη hB hle
      cases h
      have hparts := arrowLeComponents hF hw.2.2.2.2.1
        (arrowKind (typingWF hvT).2.2.2.2.1 hη hB) hle
      have hwv := typingWF hvT
      have hv' := Typing.sub (T := A)
        ⟨hD, hDf, hwv.2.2.1, hwv.2.2.2.1, (arrowKinds hw.2.2.2.2.1).1,
          emptyKind hF.signature⟩ hvT hparts.1
        (leRefl hF hF.signature.2.1 (emptyKind hF.signature))
      have hwb := typingWF hb
      have hb' := Typing.strengthen ⟨hD, hDf, hwb.2.2⟩ hb hDC
      have hout := valueSubstitution hF hsig hv hv' hb'
      exact .sub ⟨hD, hDf, hwv.2.2.1, (typingWF hout).2.2.2.1, hB, hη⟩
        hout hparts.2.2 hparts.2.1
  | sub hw ht hT hε ih =>
      intro body h D v A η B hD hDf hDC hv hvT hη hB hle
      exact ih body h D v A η B hD hDf hDC hv hvT hη hB
        (leTrans hF hF.signature.1 (entailsTrans hDC hT) hle)
  | strengthen hw ht he ih =>
      intro body h D v A η B hD hDf hDC hv hvT hη hB hle
      exact ih body h D v A η B hD hDf (entailsTrans hDC he) hv hvT hη hB hle
  | @exists_ Δ ks C Γ e T ε hw ht ih =>
      intro body h D v A η B hD hDf hDC hv hvT hη hB hle
      let E : Constraint := .conj (D.shift ks.length 0) C
      have hE : E.WF S (ks ++ Δ) 0 := ⟨constraintShiftWF hD ks, (typingWF ht).1⟩
      have hEf : E.fpi = ∅ := by
        simp [E, Constraint.fpi, constraintShiftFpi, hDf, (typingWF ht).2.1]
      have hED : Entails S M (ks ++ Δ) E (D.shift ks.length 0) :=
        fun _ _ _ _ _ _ h => h.1
      have hv' := typingShift hF hsig hvT ks
      have hwv' := typingWF hv'
      have hv'' : Typing S M sig (ks ++ Δ) E (Γ.shift ks.length) v
          (A.shift ks.length 0) .empty := by
        simpa only [Ty.empty, Ty.shift, List.map_nil] using
          Typing.strengthen ⟨hE, hEf, hwv'.2.2⟩ hv' hED
      have hle' := entailsTrans hED (entailsShift hF ks hD
        (leConstraintWF hF.signature.1 hw.2.2.2.2.1
          (arrowKind (typingWF hvT).2.2.2.2.1 hη hB)) hle)
      simp only [Constraint.le, Constraint.shift, Ty.arrow, Ty.shift, List.map_cons, List.map_nil] at hle'
      have hout := ih body h E v (A.shift ks.length 0) (η.shift ks.length 0)
        (B.shift ks.length 0) hE hEf (fun _ _ _ _ _ _ h => h.2) hv hv''
        (kindShift hη ks) (kindShift hB ks) hle'
      have hscope : (body.openAt 0 [v]).Scoped Γ := by
        simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def]
          using (typingWF hout).2.2.2.1
      have hex : Typing S M sig Δ (.exists_ ks E) Γ (body.openAt 0 [v]) B η :=
        .exists_ ⟨⟨hw.1.1, hE⟩, hEf, hw.2.2.1, hscope, hB, hη⟩ hout
      apply Typing.strengthen ⟨hD, hDf, hw.2.2.1, hscope, hB, hη⟩ hex
      intro ρ bs ι hρ hbs hι hDholds
      obtain ⟨vs, hvs, hC⟩ := hDC _ _ _ hρ hbs hι hDholds
      refine ⟨vs, hvs, ?_, hC⟩
      have hlen := hvs.length_eq
      simpa only [← hlen] using (constraintShiftHolds hD ρ bs vs ι).mpr hDholds

theorem betaPreservation (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hv : Value v) (ht : Typing S M sig Δ C Γ e T ε) :
    e = .app (.lam body) v → Typing S M sig Δ C Γ (body.openAt 0 [v]) T ε := by
  induction ht with
  | var | lam | letMono | letPoly | perform | handle => intro h; cases h
  | app hw hf hx ihf ihx =>
      intro h; cases h
      have hft := (typingWF hf).2.2.2.2.1
      have hout := lambdaApplication hF hsig hf _ rfl _ _ _ _ _ hw.1 hw.2.1
        entailsRefl hv (valuePure hF hx hv) (arrowKinds hft).2.1 (arrowKinds hft).2.2
        (leRefl hF hF.signature.1 hft)
      exact .sub (judgmentWithScope hw (typingWF hout).2.2.2.1) hout
        (leRefl hF hF.signature.1 hw.2.2.2.2.1)
        (effectUnionRight hF (unionKinds hw.2.2.2.2.2).1 (arrowKinds hft).2.1)
  | sub hw ht hT hε ih =>
      intro h
      have ht' := ih h
      exact .sub (judgmentWithScope hw (typingWF ht').2.2.2.1) ht' hT hε
  | strengthen hw ht he ih =>
      intro h
      have ht' := ih h
      exact .strengthen (judgmentWithScope hw (typingWF ht').2.2.2.1) ht' he
  | exists_ hw ht ih =>
      intro h
      have ht' := ih h
      apply Typing.exists_ (judgmentWithScope hw ?_) ht'
      simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def]
        using (typingWF ht').2.2.2.1

end EHMX
