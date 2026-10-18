import EHMX.Proofs.Reduction

/-! 操作捕捉で使う評価文脈の再構成。 -/
namespace EHMX

def EvalCtx.comp : EvalCtx → EvalCtx → EvalCtx
  | .hole, F => F
  | .appFun E x, F => .appFun (E.comp F) x
  | .appArg v hv E, F => .appArg v hv (E.comp F)
  | .letRhs E body, F => .letRhs (E.comp F) body
  | .perform op E, F => .perform op (E.comp F)
  | .handle E op ret clause, F => .handle (E.comp F) op ret clause

theorem evalCtxCompPlug (E F : EvalCtx) (e : Expr) :
    (E.comp F).plug e = E.plug (F.plug e) := by
  induction E <;> simp_all [EvalCtx.comp, EvalCtx.plug]

theorem evalCtxCompShiftPlug (E F : EvalCtx) (e : Expr) :
    ((E.comp F).shift 1 0).plug e = (E.shift 1 0).plug ((F.shift 1 0).plug e) := by
  induction E <;> simp_all [EvalCtx.comp, EvalCtx.shift, EvalCtx.plug]

theorem monoWF (hA : Ty.HasKind S Δ A 0) :
    (Scheme.mono A).WF S Δ 0 ∧ (Scheme.mono A).fpi = ∅ := by
  simpa [Scheme.mono, Scheme.WF, Scheme.fpi, Constraint.WF, Constraint.fpi] using hA

theorem typingStronger (ht : Typing S M sig Δ C Γ e T ε)
    (hD : Constraint.WF S Δ 0 D) (hDf : D.fpi = ∅) (he : Entails S M Δ D C) :
    Typing S M sig Δ D Γ e T ε :=
  .strengthen ⟨hD, hDf, (typingWF ht).2.2⟩ ht he

theorem typingShiftStronger (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (ht : Typing S M sig Δ C Γ e T ε) (ks : List Kind)
    (hD : Constraint.WF S (ks ++ Δ) 0 D) (hDf : D.fpi = ∅)
    (he : Entails S M (ks ++ Δ) D (C.shift ks.length 0)) :
    Typing S M sig (ks ++ Δ) D (Γ.shift ks.length) e
      (T.shift ks.length 0) (ε.shift ks.length 0) :=
  typingStronger (typingShift hF hsig ht ks) hD hDf he

theorem operationClauseShift {C : Constraint} {Γ : Env} {B ε : Ty}
    (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hs : sig op = some decl)
    (hc : Typing S M sig (decl.kinds ++ Δ) (.conj (C.shift decl.kinds.length 0) decl.condition)
      (((Γ.shift decl.kinds.length).push (.mono decl.input)).push
        (.mono (.arrow decl.output (ε.shift decl.kinds.length 0) (B.shift decl.kinds.length 0))))
      clause (B.shift decl.kinds.length 0) (ε.shift decl.kinds.length 0)) (ks : List Kind) :
    Typing S M sig (decl.kinds ++ (ks ++ Δ))
      (.conj ((C.shift ks.length 0).shift decl.kinds.length 0) decl.condition)
      ((((Γ.shift ks.length).shift decl.kinds.length).push (.mono decl.input)).push
        (.mono (.arrow decl.output ((ε.shift ks.length 0).shift decl.kinds.length 0)
          ((B.shift ks.length 0).shift decl.kinds.length 0))))
      clause ((B.shift ks.length 0).shift decl.kinds.length 0)
        ((ε.shift ks.length 0).shift decl.kinds.length 0) := by
  have hd := hsig op decl hs
  have h := typingTypeEffectSubstitution hF hsig hc _ _
    (BoundSubst.validLift (BoundSubst.validShift ks) decl.kinds)
  simp only [Constraint.substBound, declarationConditionSubstBound hd.2.2.2.2.2.1,
    constraintShiftLiftSubst, envSubstBoundPush, monoSubstBound,
    envShiftLiftSubst, Ty.arrow, Ty.substBound, List.map_cons, List.map_nil,
    declarationSubstBound hd.2.1, declarationSubstBound hd.2.2.1,
    tyShiftLiftSubst] at h
  simpa only [shiftSubstBound.1, envShiftSubstBound, tyShiftSubstBound,
    Nat.not_lt_zero, ↓reduceIte, Ty.arrow] using h

/-- 存在量化の内側と新しい継続の引数束縛の下でも使える文脈の型付け。 -/
def ContextTyping (S : Signature) (M : Model) (sig : OpSignature)
    (Δ : List Kind) (C : Constraint) (Γ : Env) (E : EvalCtx)
    (A : Ty) (η : Effect) (B : Ty) (ε : Effect) : Prop :=
  ∀ ks D U e, D.WF S (ks ++ Δ) 0 → D.fpi = ∅ →
    Entails S M (ks ++ Δ) D (C.shift ks.length 0) →
    U.HasKind S (ks ++ Δ) 0 →
    Typing S M sig (ks ++ Δ) D ((Γ.shift ks.length).push (.mono U)) e
      (A.shift ks.length 0) (η.shift ks.length 0) →
    Typing S M sig (ks ++ Δ) D ((Γ.shift ks.length).push (.mono U))
      ((E.shift 1 0).plug e) (B.shift ks.length 0) (ε.shift ks.length 0)

theorem ContextTyping.comp
    (hE : ContextTyping S M sig Δ C Γ E A η B ε)
    (hF : ContextTyping S M sig Δ C Γ F T θ A η) :
    ContextTyping S M sig Δ C Γ (E.comp F) T θ B ε := by
  intro ks D U e hD hDf he hU ht
  rw [evalCtxCompShiftPlug]
  exact hE _ _ _ _ hD hDf he hU (hF _ _ _ _ hD hDf he hU ht)

theorem ContextTyping.appFun (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.app f x) B (.union (.union εf εx) η))
    (hx : Typing S M sig Δ C Γ x A εx) :
    ContextTyping S M sig Δ C Γ (.appFun .hole x) (.arrow A η B) εf B
      (.union (.union εf εx) η) := by
  intro ks D U e hD hDf he hU ht
  have hx' := typingWeakening (typingShiftStronger hF hsig hx ks hD hDf he) (monoWF hU)
  have hw' := judgmentInsertAfter
    (typingWF (typingShiftStronger hF hsig hx ks hD hDf he)) (pre := []) rfl (monoWF hU)
  have hT := kindShift hw.2.2.2.2.1 ks
  have hε := kindShift hw.2.2.2.2.2 ks
  simp only [Ty.arrow, Ty.union, Ty.shift, List.map_cons, List.map_nil] at ht hε ⊢
  exact .app ⟨hD, hDf, hw'.2.2.1,
    scopedApp (typingWF ht).2.2.2.1 (typingWF hx').2.2.2.1, hT, hε⟩ ht hx'

theorem ContextTyping.appArg (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.app f x) B (.union (.union εf εx) η))
    (hf : Typing S M sig Δ C Γ f (.arrow A η B) εf) (hv : Value f) :
    ContextTyping S M sig Δ C Γ (.appArg f hv .hole) A εx B
      (.union (.union εf εx) η) := by
  intro ks D U e hD hDf he hU ht
  have hf' := typingWeakening (typingShiftStronger hF hsig hf ks hD hDf he) (monoWF hU)
  have hε := kindShift hw.2.2.2.2.2 ks
  simp only [Ty.arrow, Ty.union, Ty.shift, List.map_cons, List.map_nil] at hf' hε ⊢
  exact .app ⟨hD, hDf, (typingWF ht).2.2.1,
    scopedApp (typingWF hf').2.2.2.1 (typingWF ht).2.2.2.1,
    kindShift hw.2.2.2.2.1 ks, hε⟩ hf' ht

theorem ContextTyping.letRhs (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.letE rhs body) B (.union εrhs εbody))
    (hb : Typing S M sig Δ C (Γ.push (.mono A)) body B εbody) :
    ContextTyping S M sig Δ C Γ (.letRhs .hole body) A εrhs B (.union εrhs εbody) := by
  intro ks D U e hD hDf he hU ht
  have hb' := typingShiftStronger hF hsig hb ks hD hDf he
  have hb'' := typingWeakeningAt hb' [.mono (A.shift ks.length 0)]
    (Γ.shift ks.length).bound (.mono U)
    (by simp [Env.shift, Env.push, Scheme.mono, Scheme.shift, Constraint.shift])
    (monoWF hU)
  have hε := kindShift hw.2.2.2.2.2 ks
  simp only [Ty.union, Ty.shift, List.map_cons, List.map_nil] at hε ⊢
  have hb''' : Typing S M sig (ks ++ Δ) D
      (((Γ.shift ks.length).push (.mono U)).push (.mono (A.shift ks.length 0)))
      (body.shift 1 1) (B.shift ks.length 0) (εbody.shift ks.length 0) := by
    simpa [Env.insertAfter, Env.shift, Env.push] using hb''
  exact .letMono ⟨hD, hDf, (typingWF ht).2.2.1,
    scopedLet (typingWF ht).2.2.2.1 (typingWF hb''').2.2.2.1,
    kindShift hw.2.2.2.2.1 ks, hε⟩ ht hb'''

theorem ContextTyping.perform (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.perform op arg) (decl.output.openAt 0 args)
      (.union (.singleton op) ε))
    (hs : sig op = some decl) (ha : List.Forall₂ (Ty.HasKind S Δ) args decl.kinds)
    (hp : Entails S M Δ C (decl.condition.substBound (BoundSubst.many args))) :
    ContextTyping S M sig Δ C Γ (.perform op .hole) (decl.input.openAt 0 args) ε
      (decl.output.openAt 0 args) (.union (.singleton op) ε) := by
  intro ks D U e hD hDf he hU ht
  have hd := hsig op decl hs
  have hσ := BoundSubst.validShift (S := S) (Δ := Δ) ks
  have hi := declarationOpenSubstBound hd.2.1 ha (σ := fun i => .bound (i + ks.length))
  have ho := declarationOpenSubstBound hd.2.2.1 ha (σ := fun i => .bound (i + ks.length))
  have hε := kindShift hw.2.2.2.2.2 ks
  have hT := kindShift hw.2.2.2.2.1 ks
  simp only [tyShiftSubstBound, Nat.not_lt_zero, ↓reduceIte] at ht hT ⊢
  rw [hi] at ht
  rw [ho] at hT ⊢
  simp only [Ty.union, Ty.singleton, Ty.shift, Ty.substBound, List.map_cons, List.map_nil] at hε ⊢
  simp only [tyShiftSubstBound, Nat.not_lt_zero, ↓reduceIte] at hε
  have hpw := (substBoundWF S).1 _ _ _ (constraintAppendWF hd.2.2.2.2.2.1 Δ) _ _
    (BoundSubst.validMany ha)
  have hp' := entailsTrans he (entailsShift hF ks hw.1 hpw hp)
  rw [shiftSubstBound.1, declarationConditionOpenSubstBound hd.2.2.2.2.2.1 ha] at hp'
  exact .perform ⟨hD, hDf, (typingWF ht).2.2.1, (typingWF ht).2.2.2.1, hT, hε⟩ hs
    (List.forall₂_map_left_iff.mpr (forall₂ImplMem ha (fun _ _ _ h => kindSubstBound h hσ))) hp' ht

theorem scopedHandle (hb : body.Scoped Γ) (hr : ret.Scoped (Γ.push s))
    (hc : clause.Scoped (((Γ.shift n).push t).push u)) :
    (Expr.handle body op ret clause).Scoped Γ := by
  have hc' : clause.LCAt (Γ.bound.length + 2) ∧ clause.fv ⊆ Γ.dpi := by
    simpa [Expr.Scoped, Env.shift, Env.push, Env.dpi, List.map_map, Function.comp_def,
      Nat.add_assoc] using hc
  exact ⟨⟨hb.1, hr.1, hc'.1⟩, Finset.union_subset (Finset.union_subset hb.2 hr.2) hc'.2⟩

theorem ContextTyping.handle (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hw : JudgmentWF S Δ C Γ (.handle body op ret clause) B εout)
    (hs : sig op = some decl) (hεin : Ty.HasKind S Δ εin 1)
    (heff : Entails S M Δ C (.le 1 εin (.union (.singleton op) εout)))
    (hr : Typing S M sig Δ C (Γ.push (.mono A)) ret B εout)
    (hc : Typing S M sig (decl.kinds ++ Δ) (.conj (C.shift decl.kinds.length 0) decl.condition)
      (((Γ.shift decl.kinds.length).push (.mono decl.input)).push
        (.mono (.arrow decl.output (εout.shift decl.kinds.length 0) (B.shift decl.kinds.length 0))))
      clause (B.shift decl.kinds.length 0) (εout.shift decl.kinds.length 0)) :
    ContextTyping S M sig Δ C Γ (.handle .hole op ret clause) A εin B εout := by
  intro ks D U e hD hDf he hU ht
  have hr' := typingShiftStronger hF hsig hr ks hD hDf he
  have hr'' := typingWeakeningAt hr' [.mono (A.shift ks.length 0)]
    (Γ.shift ks.length).bound (.mono U)
    (by simp [Env.shift, Env.push, Scheme.mono, Scheme.shift, Constraint.shift]) (monoWF hU)
  have hr''' : Typing S M sig (ks ++ Δ) D
      (((Γ.shift ks.length).push (.mono U)).push (.mono (A.shift ks.length 0)))
      (ret.shift 1 1) (B.shift ks.length 0) (εout.shift ks.length 0) := by
    simpa [Env.insertAfter, Env.shift, Env.push] using hr''
  have hc' := operationClauseShift hF hsig hs hc ks
  have hc'' := typingConjStronger hc' (constraintShiftWF hD decl.kinds)
    ((constraintShiftFpi _ _ _).trans hDf)
    (entailsShift hF decl.kinds hD (constraintShiftWF hw.1 ks) he)
  have hc''' := typingWeakeningAt hc''
    [.mono (.arrow decl.output ((εout.shift ks.length 0).shift decl.kinds.length 0)
      ((B.shift ks.length 0).shift decl.kinds.length 0)), .mono decl.input]
    ((Γ.shift ks.length).shift decl.kinds.length).bound
    (.mono (U.shift decl.kinds.length 0)) rfl (monoWF (kindShift hU decl.kinds))
  have hcFinal : Typing S M sig (decl.kinds ++ (ks ++ Δ)) (.conj (D.shift decl.kinds.length 0) decl.condition)
      (((((Γ.shift ks.length).push (.mono U)).shift decl.kinds.length).push (.mono decl.input)).push
        (.mono (.arrow decl.output ((εout.shift ks.length 0).shift decl.kinds.length 0)
          ((B.shift ks.length 0).shift decl.kinds.length 0))))
      (clause.shift 1 2) ((B.shift ks.length 0).shift decl.kinds.length 0)
        ((εout.shift ks.length 0).shift decl.kinds.length 0) := by
    simpa [Env.insertAfter, Env.shift, Env.push, Scheme.shift, Scheme.mono, Constraint.shift]
      using hc'''
  have heff' := entailsTrans he (entailsShift hF ks hw.1
    (leConstraintWF hF.signature.2.1 hεin (unionKind (singletonKind op) hw.2.2.2.2.2)) heff)
  simp only [Constraint.le, Constraint.shift, Ty.union, Ty.singleton, Ty.shift,
    List.map_cons, List.map_nil] at heff'
  exact .handle ⟨hD, hDf, (typingWF ht).2.2.1,
    scopedHandle (typingWF ht).2.2.2.1 (typingWF hr''').2.2.2.1 (typingWF hcFinal).2.2.2.1,
    kindShift hw.2.2.2.2.1 ks, kindShift hw.2.2.2.2.2 ks⟩ hs ht heff' hr''' hcFinal

theorem tyShiftAddZero (T : Ty) (n m : Nat) :
    (T.shift n 0).shift m 0 = T.shift (n + m) 0 := by
  simp only [tyShiftSubstBound, Nat.not_lt_zero, ↓reduceIte, tySubstBoundComp,
    Ty.substBound, Nat.add_assoc]

theorem constraintShiftAddZero (C : Constraint) (n m : Nat) :
    (C.shift n 0).shift m 0 = C.shift (n + m) 0 := by
  simp only [shiftSubstBound.1, Nat.not_lt_zero, ↓reduceIte, substBoundComp.1,
    Ty.substBound, Nat.add_assoc]

theorem envShiftAdd (Γ : Env) (n m : Nat) :
    (Γ.shift n).shift m = Γ.shift (n + m) := by
  simp only [envShiftSubstBound, envSubstBoundComp, Ty.substBound, Nat.add_assoc]

theorem ContextTyping.stronger (hF : EffectFramework S M)
    (h : ContextTyping S M sig Δ C Γ E A η B ε)
    (hC : Constraint.WF S Δ 0 C) (hD : Constraint.WF S Δ 0 D)
    (he : Entails S M Δ D C) : ContextTyping S M sig Δ D Γ E A η B ε := by
  intro ks Q U e hQ hQf hQD hU ht
  exact h _ _ _ _ hQ hQf (entailsTrans hQD (entailsShift hF ks hD hC he)) hU ht

theorem ContextTyping.shift (hF : EffectFramework S M)
    (h : ContextTyping S M sig Δ C Γ E A η B ε) (ks : List Kind)
    (hC : Constraint.WF S Δ 0 C) (hD : Constraint.WF S (ks ++ Δ) 0 D)
    (he : Entails S M (ks ++ Δ) D (C.shift ks.length 0)) :
    ContextTyping S M sig (ks ++ Δ) D (Γ.shift ks.length) E
      (A.shift ks.length 0) (η.shift ks.length 0)
      (B.shift ks.length 0) (ε.shift ks.length 0) := by
  intro ls Q U e hQ hQf hQD hU ht
  have he' := entailsTrans hQD (entailsShift hF ls hD (constraintShiftWF hC ks) he)
  have ht' := h (ls ++ ks) Q U e
    (by simpa only [List.append_assoc] using hQ) hQf
    (by simpa only [List.append_assoc, List.length_append, constraintShiftAddZero,
      Nat.add_comm] using he')
    (by simpa only [List.append_assoc] using hU)
    (by simpa only [List.append_assoc, List.length_append, envShiftAdd, tyShiftAddZero,
      Nat.add_comm] using ht)
  simpa only [List.append_assoc, List.length_append, envShiftAdd, tyShiftAddZero,
    Nat.add_comm] using ht'

theorem ContextTyping.sub (hF : EffectFramework S M)
    (hC : Constraint.WF S Δ 0 C) (hA : Ty.HasKind S Δ A 0) (hB : Ty.HasKind S Δ B 0)
    (hη : Ty.HasKind S Δ η 1) (hε : Ty.HasKind S Δ ε 1)
    (hAB : Entails S M Δ C (.le 0 A B)) (hηε : Entails S M Δ C (.le 1 η ε)) :
    ContextTyping S M sig Δ C Γ .hole A η B ε := by
  intro ks D U e hD hDf he hU ht
  have hAB' := entailsTrans he (entailsShift hF ks hC (leConstraintWF hF.signature.1 hA hB) hAB)
  have hηε' := entailsTrans he (entailsShift hF ks hC (leConstraintWF hF.signature.2.1 hη hε) hηε)
  simp only [Constraint.le, Constraint.shift, List.map_cons, List.map_nil] at hAB' hηε'
  exact .sub ⟨hD, hDf, (typingWF ht).2.2.1, (typingWF ht).2.2.2.1,
    kindShift hB ks, kindShift hε ks⟩ ht hAB' hηε'

end EHMX
