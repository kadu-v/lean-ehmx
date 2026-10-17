import EHMX.Proofs.OperationContext

/-! 操作捕捉の保存。操作節の束縛順序は継続、引数値の順。 -/
namespace EHMX

theorem exprOpenShiftSucc (e : Expr) (v : Expr) (n d : Nat) :
    (e.shift (n + 1) d).openAt (n + d) [v] = e.shift n d := by
  induction e generalizing d with
  | ident x =>
      cases x with
      | free => rfl
      | bound i =>
          by_cases h : i < d
          · simp [Expr.shift, Expr.openAt, h, show i < n + d by omega]
          · have h' : ¬ i + (n + 1) < n + d := by omega
            have h'' : i + (n + 1) - (n + d) ≠ 0 := by omega
            simp [Expr.shift, Expr.openAt, h, h', h'', show i + (n + 1) - 1 = i + n by omega]
  | _ => simp_all [Expr.shift, Expr.openAt, Nat.add_assoc]

theorem exprOpenTwo (e k v : Expr) (d : Nat) :
    (e.openAt d [k.shift 1 0]).openAt d [v] = e.openAt d [k, v] := by
  induction e generalizing d with
  | ident x =>
      cases x with
      | free => rfl
      | bound i =>
          by_cases h : i < d
          · simp [Expr.openAt, h]
          · by_cases h0 : i = d
            · subst i
              simp only [Expr.openAt, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
                List.getElem?_cons_zero, exprShiftAdd]
              simpa only [Nat.add_comm 1 d, Nat.add_zero] using exprOpenShiftSucc k v d 0
            · by_cases h1 : i = d + 1
              · subst i
                simp [Expr.openAt, show ¬ d + 1 < d by omega,
                  show d + 1 - d = 1 by omega]
              · have hi : ¬ i - 1 < d := by omega
                have hget₁ : [k.shift 1 0][i - d]? = none := by simp; omega
                have hget₂ : [k, v][i - d]? = none := by simp; omega
                have hget₃ : [v][i - 1 - d]? = none := by simp; omega
                simp only [Expr.openAt, h, hi, ↓reduceIte, hget₁, hget₂,
                  hget₃, List.length_cons, List.length_nil]
                congr 2
  | _ => simp_all [Expr.openAt]

theorem twoValueSubstitution (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hk : Value k) (hv : Value v)
    (hkt : Typing S M sig Δ C Γ k K .empty)
    (hvt : Typing S M sig Δ C Γ v A .empty)
    (hc : Typing S M sig Δ C ((Γ.push (.mono A)).push (.mono K)) clause B ε) :
    Typing S M sig Δ C Γ (clause.openAt 0 [k, v]) B ε := by
  have hA : (Scheme.mono A).WF S Δ 0 ∧ (Scheme.mono A).fpi = ∅ := by
    simpa [Scheme.mono, Scheme.WF, Scheme.fpi, Constraint.WF, Constraint.fpi]
      using (typingWF hvt).2.2.2.2.1
  have hk' := typingWeakening hkt hA
  have hc' := valueSubstitution hF hsig (valueShift hk 1 0) hk' hc
  simpa only [exprOpenTwo] using valueSubstitution hF hsig hv hvt hc'

theorem evalCtxCompAssoc (E F G : EvalCtx) : (E.comp F).comp G = E.comp (F.comp G) := by
  induction E <;> simp_all [EvalCtx.comp]

theorem evalCtxCompHole (E : EvalCtx) : E.comp .hole = E := by
  induction E <;> simp_all [EvalCtx.comp]

/-- 操作の結果を引数に取る lambda。深い handler は E に含まれる。 -/
theorem resumeContextTyping (hF : EffectFramework S M)
    (hC : Constraint.WF S Δ 0 C) (hCf : C.fpi = ∅) (hΓ : Env.WF S Δ Γ)
    (hA : Ty.HasKind S Δ A 0) (hθ : Ty.HasKind S Δ θ 1)
    (hB : Ty.HasKind S Δ B 0) (hε : Ty.HasKind S Δ ε 1)
    (hctx : ContextTyping S M sig Δ C Γ E A θ B ε) :
    Typing S M sig Δ C Γ (.lam ((E.shift 1 0).plug (.ident (.bound 0))))
      (.arrow A ε B) .empty := by
  have hΓ' : (Γ.push (.mono A)).WF S Δ := by
    refine ⟨hΓ.1, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact monoWF hA
    · exact hΓ.2 s hs
  have hscope : (Expr.ident (.bound 0)).Scoped (Γ.push (.mono A)) := by
    simp [Expr.Scoped, Expr.LCAt, Expr.fv, Env.push]
  have hv : Typing S M sig Δ C (Γ.push (.mono A)) (.ident (.bound 0)) A .empty :=
    .var ⟨hC, hCf, hΓ', hscope, hA, emptyKind hF.signature⟩ rfl (monoInstance hF hA)
  have hv' := Typing.sub ⟨hC, hCf, hΓ', hscope, hA, hθ⟩ hv
    (leRefl hF hF.signature.1 hA) (effectEmptyBelow hF hθ)
  have hb : Typing S M sig Δ C (Γ.push (.mono A))
      ((E.shift 1 0).plug (.ident (.bound 0))) B ε := by
    have h := hctx [] C A (.ident (.bound 0))
    simp only [List.nil_append, List.length_nil, constraintShiftZero, envShiftZero,
      tyShiftZero] at h
    exact h hC hCf entailsRefl hA hv'
  exact .lam ⟨hC, hCf, hΓ, (typingWF hb).2.2.2.1,
    arrowKind hA hε hB, emptyKind hF.signature⟩ hb

/-- 型引数は perform の導出で選び、exists_ の作用域内で代入を完了する。 -/
theorem operationElimination (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (ht : Typing S M sig Δ C Γ e T θ) :
    ∀ (E : EvalCtx) op v, e = E.plug (.perform op v) → Value v →
    ∀ D (F : EvalCtx) decl clause B η,
      D.WF S Δ 0 → D.fpi = ∅ → Entails S M Δ D C → sig op = some decl →
      B.HasKind S Δ 0 → η.HasKind S Δ 1 →
      Typing S M sig (decl.kinds ++ Δ) (D.shift decl.kinds.length 0)
        (((Γ.shift decl.kinds.length).push (.mono decl.input)).push
          (.mono (.arrow decl.output (η.shift decl.kinds.length 0) (B.shift decl.kinds.length 0))))
        clause (B.shift decl.kinds.length 0) (η.shift decl.kinds.length 0) →
      ContextTyping S M sig Δ D Γ F T θ B η →
      Typing S M sig Δ D Γ
        (clause.openAt 0 [.lam (((F.comp E).shift 1 0).plug (.ident (.bound 0))), v]) B η := by
  induction ht with
  | var hw hl hi =>
      intro E op v h
      cases E <;> cases h
  | lam hw hb ih =>
      intro E op v h
      cases E <;> cases h
  | app hw hf hx ihf ihx =>
      intro E op v h hv D F decl clause B η hD hDf hDC hs hB hη hc hctx
      cases E with
      | hole => cases h
      | appFun E x =>
          cases h
          have hframe := (ContextTyping.appFun hF hsig hw hx).stronger hF hw.1 hD hDC
          simpa only [evalCtxCompAssoc, EvalCtx.comp] using
            ihf E op v rfl hv D _ decl clause B η hD hDf hDC hs hB hη hc (hctx.comp hframe)
      | appArg f hfval E =>
          cases h
          have hframe := (ContextTyping.appArg hF hsig hw hf hfval).stronger hF hw.1 hD hDC
          simpa only [evalCtxCompAssoc, EvalCtx.comp] using
            ihx E op v rfl hv D _ decl clause B η hD hDf hDC hs hB hη hc (hctx.comp hframe)
      | letRhs | perform | handle => cases h
  | letMono hw hr hb ihr ihb =>
      intro E op v h hv D F decl clause B η hD hDf hDC hs hB hη hc hctx
      cases E with
      | hole | appFun | appArg | perform | handle => cases h
      | letRhs E body =>
          cases h
          have hframe := (ContextTyping.letRhs hF hsig hw hb).stronger hF hw.1 hD hDC
          simpa only [evalCtxCompAssoc, EvalCtx.comp] using
            ihr E op v rfl hv D _ decl clause B η hD hDf hDC hs hB hη hc (hctx.comp hframe)
  | letPoly hw hval hr he hb ihr ihb =>
      intro E op v h
      cases E with
      | hole | appFun | appArg | perform | handle => cases h
      | letRhs E body =>
          cases h
          have hn := evalCtxValue E hval
          simp [Value, Expr.isValue] at hn
  | @perform Δ C Γ op₀ arg ε decl₀ args hw hs₀ ha ht ih =>
      intro E op v h hv D F decl clause B η hD hDf hDC hs hB hη hc hctx
      cases E with
      | hole =>
          cases h
          have hd : decl₀ = decl := Option.some.inj (hs₀.symm.trans hs)
          subst decl
          have hv' := valuePure hF (typingStronger ht hD hDf hDC) hv
          have hk := resumeContextTyping hF hD hDf hw.2.2.1
            hw.2.2.2.2.1 hw.2.2.2.2.2 hB hη hctx
          have hc' := operationClauseInstantiation hF hsig hc ha
          simpa only [evalCtxCompHole] using
            twoValueSubstitution hF hsig (show Value (.lam _) from rfl) hv hk hv' hc'
      | perform op₁ E =>
          cases h
          have hframe := (ContextTyping.perform hF hsig hw hs₀ ha).stronger hF hw.1 hD hDC
          simpa only [evalCtxCompAssoc, EvalCtx.comp] using
            ih E op v rfl hv D _ decl clause B η hD hDf hDC hs hB hη hc (hctx.comp hframe)
      | appFun | appArg | letRhs | handle => cases h
  | handle hw hs₀ hb he hr hc₀ ihb ihr ihc =>
      intro E op v h hv D F decl clause B η hD hDf hDC hs hB hη hc hctx
      cases E with
      | hole | appFun | appArg | letRhs | perform => cases h
      | handle E op₁ ret clause₁ =>
          cases h
          have hframe := (ContextTyping.handle hF hsig hw hs₀
            (typingWF hb).2.2.2.2.2 he hr hc₀).stronger hF hw.1 hD hDC
          simpa only [evalCtxCompAssoc, EvalCtx.comp] using
            ihb E op v rfl hv D _ decl clause B η hD hDf hDC hs hB hη hc (hctx.comp hframe)
  | @sub Δ C Γ e U η₀ T θ hw ht hT hε ih =>
      intro E op v h hv D F decl clause B η hD hDf hDC hs hB hη hc hctx
      have hw₀ := typingWF ht
      have hframe := (ContextTyping.sub (Γ := Γ) (sig := sig) hF hw.1 hw₀.2.2.2.2.1 hw.2.2.2.2.1
        hw₀.2.2.2.2.2 hw.2.2.2.2.2 hT hε).stronger hF hw.1 hD hDC
      simpa only [evalCtxCompHole] using
        ih E op v h hv D _ decl clause B η hD hDf hDC hs hB hη hc (hctx.comp hframe)
  | strengthen hw ht he ih =>
      intro E op v h hv D F decl clause B η hD hDf hDC hs hB hη hc hctx
      exact ih E op v h hv D F decl clause B η hD hDf (entailsTrans hDC he) hs hB hη hc hctx
  | @exists_ Δ ks C Γ e T θ hw ht ih =>
      intro E op v h hv D F decl clause B η hD hDf hDC hs hB hη hc hctx
      let K : Constraint := .conj (D.shift ks.length 0) C
      have hK : K.WF S (ks ++ Δ) 0 := ⟨constraintShiftWF hD ks, (typingWF ht).1⟩
      have hKf : K.fpi = ∅ := by
        simp [K, Constraint.fpi, constraintShiftFpi, hDf, (typingWF ht).2.1]
      have hKD : Entails S M (ks ++ Δ) K (D.shift ks.length 0) := fun _ _ _ _ _ _ h => h.1
      have hc' := operationClauseShift hF hsig hs hc ks
      have hc'' := typingStronger hc' (constraintShiftWF hK decl.kinds)
        ((constraintShiftFpi _ _ _).trans hKf)
        (entailsShift hF decl.kinds hK (constraintShiftWF hD ks) hKD)
      have hout := ih E op v h hv K F decl clause (B.shift ks.length 0) (η.shift ks.length 0)
        hK hKf (fun _ _ _ _ _ _ h => h.2) hs (kindShift hB ks) (kindShift hη ks) hc''
        (hctx.shift hF ks hD hK hKD)
      have hscope : (clause.openAt 0 [.lam (((F.comp E).shift 1 0).plug (.ident (.bound 0))), v]).Scoped Γ := by
        simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def]
          using (typingWF hout).2.2.2.1
      have hex := Typing.exists_ (S := S) (M := M) (sig := sig)
        (ks := ks) (T := B) (ε := η) ⟨⟨hw.1.1, hK⟩, hKf, hw.2.2.1, hscope, hB, hη⟩ hout
      apply typingStronger hex hD hDf
      intro ρ bs ι hρ hbs hι hDh
      obtain ⟨vs, hvs, hC⟩ := hDC _ _ _ hρ hbs hι hDh
      refine ⟨vs, hvs, ?_, hC⟩
      have hlen := hvs.length_eq
      simpa only [← hlen] using (constraintShiftHolds hD ρ bs vs ι).mpr hDh

theorem resumeTyping (hF : EffectFramework S M)
    (hC : Constraint.WF S Δ 0 C) (hCf : C.fpi = ∅) (hΓ : Env.WF S Δ Γ)
    (hA : Ty.HasKind S Δ A 0) (hθ : Ty.HasKind S Δ θ 1)
    (hB : Ty.HasKind S Δ B 0) (hε : Ty.HasKind S Δ ε 1)
    (hctx : ContextTyping S M sig Δ C Γ (.handle E op ret clause) A θ B ε) :
    Typing S M sig Δ C Γ (Expr.resume E op ret clause) (.arrow A ε B) .empty :=
  resumeContextTyping hF hC hCf hΓ hA hθ hB hε hctx

theorem operationPreservationAux (hF : EffectFramework S M) (hsig : OpSignature.WF S sig)
    (hv : Value v) (ht : Typing S M sig Δ C Γ e B ε) :
    e = .handle (E.plug (.perform op v)) op ret clause →
    Typing S M sig Δ C Γ (clause.openAt 0 [Expr.resume E op ret clause, v]) B ε := by
  induction ht with
  | var | lam | app | letMono | letPoly | perform => intro h; cases h
  | handle hw hs hb he hr hc ihb ihr ihc =>
      intro h; cases h
      have hctx := ContextTyping.handle hF hsig hw hs (typingWF hb).2.2.2.2.2 he hr hc
      exact operationElimination hF hsig hb E op v rfl hv _ (.handle .hole op ret clause)
        _ clause _ _ hw.1 hw.2.1 entailsRefl hs hw.2.2.2.2.1 hw.2.2.2.2.2 hc hctx
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

/-- 追加の安全性仮定なしで、Goals.lean の操作保存の命題を満たす。 -/
theorem operationPreservation (S : Signature) (M : Model) (sig : OpSignature) :
    OperationPreservationGoal S M sig := by
  intro hA Δ C Γ E op ret clause v B ε hv _ ht
  exact operationPreservationAux hA.1.1 hA.1.2 hv ht rfl

end EHMX
