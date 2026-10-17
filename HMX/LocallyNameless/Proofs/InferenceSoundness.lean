import HMX.LocallyNameless.Proofs.InferenceSupport

namespace HMX.LN.Proofs

theorem inferenceApplication (hF : Framework S M I) (C : Constraint) (Γ : Env) (t u : Expr) (T : Ty)
    (hw : JudgmentWF S C Γ (.app t u) (.mono T)) (hscope : (Expr.app t u).fpi ⊆ Γ.dpi)
    (he : Entails S M C (infer Γ (.app t u) T))
    (iht : ∀ D U, JudgmentWF S D Γ t (.mono U) → Entails S M D (infer Γ t U) →
      AlternateTyping S M D Γ t U)
    (ihu : ∀ D U, JudgmentWF S D Γ u (.mono U) → Entails S M D (infer Γ u U) →
      AlternateTyping S M D Γ u U) : AlternateTyping S M C Γ (.app t u) T := by
  have hΓ := hw.2.1
  have hΓf := hw.2.2.2.2.2.1
  have hT := hw.2.2.2.1.2.2
  obtain ⟨X,hX,hXF⟩ := freshSameKind 0 (C.fv ∪ Γ.fv ∪ T.fv)
  have hxT : X ∉ T.fv := fun h => hXF (Finset.mem_union_right _ h)
  have hxΓ : X ∉ Γ.fv := fun h => hXF (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
  let D := Constraint.conj (generate t (.arrow (.free X) T)) (generate u (.free X))
  let K := Γ.letIn D
  have hgen := generateAppFresh t u T X (tyKindLC T S [] 0 hT) hX hxT
  have hW := inferWF hF.1.1 hΓ hw.2.2.1 hT
  have hFc := inferFpi Γ (.app t u) T hΓf hscope
  simp only [infer,hgen] at hW hFc
  obtain ⟨hK,hKf,hp⟩ := inferencePrefixExists hF.1 Γ [X] D hΓ hΓf (by simp) (by simp [hxΓ]) hW hFc
  have hA := arrowKind S hF.1.1 (.free X) T [] hXk hT
  have hkt := inferenceJudgment hK hΓ hw.2.2.1.1 hA hKf hΓf
  have hku := inferenceJudgment hK hΓ hw.2.2.1.2 hXk hKf hΓf
  have hdist := prefixConjunction S M hF.1 Γ (generate t (.arrow (.free X) T)) (generate u (.free X)) hK
    ⟨inferWF hF.1.1 hΓ hw.2.2.1.1 hA,inferWF hF.1.1 hΓ hw.2.2.1.2 hXk⟩
  have ht := iht K _ hkt (fun ρ ι hρ hι hh => (hdist.1 ρ ι hρ hι hh).1)
  have hu := ihu K _ hku (fun ρ ι hρ hι hh => (hdist.1 ρ ι hρ hι hh).2)
  have ha := AlternateTyping.app (judgmentChangeConstraint hw hK hKf) ht hu
  have hk : ∀ Y ∈ [X], Y.1 ∈ S.kinds := by simp [hX,hF.1.1.1]
  have hex := AlternateTyping.exists_
    (judgmentChangeConstraint hw (existsNamesWF S [X] K 0 hk hK) (by rw [existsNamesFpi,hKf]))
    (by simp) hk (by simp [hxΓ,hxT]) ha
  apply alternateWeakening S M I hF _ C Γ (.app t u) T hw ?_ hex
  intro ρ ι hρ hι hh
  apply hp.1 ρ ι hρ hι
  simpa only [infer,hgen] using he ρ ι hρ hι hh

theorem inferenceLambda (hF : Framework S M I) (C : Constraint) (Γ : Env) (t : Expr) (T : Ty)
    (hw : JudgmentWF S C Γ (.lam t) (.mono T)) (hscope : t.fpi ⊆ Γ.dpi)
    (he : Entails S M C (infer Γ (.lam t) T))
    (ih : ∀ z D Δ U, JudgmentWF S D Δ (Expr.openAt 0 (.ident (.free (.var z))) t) (.mono U) →
      (Expr.openAt 0 (.ident (.free (.var z))) t).fpi ⊆ Δ.dpi →
      Entails S M D (infer Δ (Expr.openAt 0 (.ident (.free (.var z))) t) U) →
      AlternateTyping S M D Δ (Expr.openAt 0 (.ident (.free (.var z))) t) U) :
    AlternateTyping S M C Γ (.lam t) T := by
  have hΓ := hw.2.1
  have hΓf := hw.2.2.2.2.2.1
  have hT := hw.2.2.2.1.2.2
  obtain ⟨X,hX,hXF⟩ := freshSameKind 0 (C.fv ∪ Γ.fv ∪ T.fv)
  obtain ⟨Y,hY,hYF⟩ := freshSameKind 0 (insert X (C.fv ∪ Γ.fv ∪ T.fv))
  simp only [Finset.mem_insert,not_or] at hYF
  have hXY : X ≠ Y := Ne.symm hYF.1
  have hxT : X ∉ T.fv := fun h => hXF (Finset.mem_union_right _ h)
  have hyT : Y ∉ T.fv := fun h => hYF.2 (Finset.mem_union_right _ h)
  have hxΓ : X ∉ Γ.fv := fun h => hXF (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hyΓ : Y ∉ Γ.fv := fun h => hYF.2 (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
  have hYk : (Ty.free Y).HasKind S [] 0 := by rw [← hY]; exact .free (by rw [hY]; exact hF.1.1.1)
  have hA := arrowKind S hF.1.1 (.free X) (.free Y) [] hXk hYk
  let B := (generate t (.free Y)).letBound .term (.mono (.free X))
  let D := Constraint.conj B (.le 0 (.arrow (.free X) (.free Y)) T)
  let K := Γ.letIn D
  have hgen := generateLamFresh t T X Y (tyKindLC T S [] 0 hT) hX hY hXY hxT hyT
  have hW := inferWF hF.1.1 hΓ hw.2.2.1 hT
  have hFc := inferFpi Γ (.lam t) T hΓf hscope
  simp only [infer,hgen] at hW hFc
  obtain ⟨hK,hKf,hp⟩ := inferencePrefixExists hF.1 Γ [X,Y] D hΓ hΓf
    (by simp [hXY]) (by simp [hxΓ,hyΓ]) hW hFc
  have hbody := prefixLeRight S M Γ B 0 (.arrow (.free X) (.free Y)) T
  have ha : AlternateTyping S M K Γ (.lam t) (.arrow (.free X) (.free Y)) := by
    apply AlternateTyping.abs (t.fpi.image idNumber)
      (inferenceJudgment hK hΓ hw.2.2.1 hA hKf hΓf)
    intro z hz
    have hzt : Id.var z ∉ t.fpi := fun hm => hz (Finset.mem_image.mpr ⟨.var z,hm,rfl⟩)
    have hΔ := envSnocWF Γ (.var z) (.mono (.free X)) hΓ (monoWF S _ hXk)
    have hΔf : (Γ ++ [(Id.var z,Scheme.mono (.free X))]).fpi = ∅ := by
      rw [envSnocFpi,hΓf]; rfl
    apply ih z K _ (.free Y)
      (inferenceJudgment hK hΔ (exprOpenNameLC t z 0 hw.2.2.1) hYk hKf hΔf)
      (openedScope Γ t (.var z) _ hscope)
    intro ρ ι hρ hι hh
    have hb := (hbody.1 ρ ι hρ hι hh).1
    change (Γ.letIn B).Holds S M ρ ι at hb
    change ((Γ ++ [(Id.var z,Scheme.mono (.free X))]).letIn _).Holds S M ρ ι
    rw [letInSnoc, ← generateLetName t z (.free Y) (.free X) hzt]
    exact hb
  have hs := AlternateTyping.sub (judgmentChangeConstraint hw hK hKf) ha
    (fun ρ ι hρ hι hh => (hbody.1 ρ ι hρ hι hh).2)
  have hk : ∀ Z ∈ [X,Y], Z.1 ∈ S.kinds := by simp [hX,hY,hF.1.1.1]
  have hex := AlternateTyping.exists_
    (judgmentChangeConstraint hw (existsNamesWF S [X,Y] K 0 hk hK) (by rw [existsNamesFpi,hKf]))
    (by simp [hXY]) hk (by simp [hxΓ,hyΓ,hxT,hyT]) hs
  apply alternateWeakening S M I hF _ C Γ (.lam t) T hw ?_ hex
  intro ρ ι hρ hι hh
  apply hp.1 ρ ι hρ hι
  simpa only [infer,hgen] using he ρ ι hρ hι hh

theorem inferenceLet (hF : Framework S M I) (C : Constraint) (Γ : Env) (t u : Expr) (T : Ty)
    (hw : JudgmentWF S C Γ (.letE t u) (.mono T)) (hscope : (Expr.letE t u).fpi ⊆ Γ.dpi)
    (he : Entails S M C (infer Γ (.letE t u) T))
    (iht : ∀ D U, JudgmentWF S D Γ t (.mono U) → Entails S M D (infer Γ t U) →
      AlternateTyping S M D Γ t U)
    (ihu : ∀ z D Δ U, JudgmentWF S D Δ (Expr.openAt 0 (.ident (.free (.var z))) u) (.mono U) →
      (Expr.openAt 0 (.ident (.free (.var z))) u).fpi ⊆ Δ.dpi →
      Entails S M D (infer Δ (Expr.openAt 0 (.ident (.free (.var z))) u) U) →
      AlternateTyping S M D Δ (Expr.openAt 0 (.ident (.free (.var z))) u) U) :
    AlternateTyping S M C Γ (.letE t u) T := by
  have hΓ := hw.2.1
  have hΓf := hw.2.2.2.2.2.1
  have hT := hw.2.2.2.1.2.2
  have ht := hw.2.2.1.1
  have hu := hw.2.2.1.2
  have hts : t.fpi ⊆ Γ.dpi := fun _ hm => hscope (Finset.mem_union_left _ hm)
  have hus : u.fpi ⊆ Γ.dpi := fun _ hm => hscope (Finset.mem_union_right _ hm)
  obtain ⟨X,hX,hXF⟩ := freshSameKind 0 (C.fv ∪ Γ.fv ∪ T.fv)
  have hxT : X ∉ T.fv := fun h => hXF (Finset.mem_union_right _ h)
  have hxΓ : X ∉ Γ.fv := fun h => hXF (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hxCΓ : X ∉ C.fv ∪ Γ.fv := fun h => hXF (Finset.mem_union_left _ h)
  have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
  let D := infer Γ t (.free X)
  let s := closedGeneratedScheme Γ t X
  have hD : D.WF S [] 0 := inferWF hF.1.1 hΓ ht hXk
  have hDf : D.fpi = ∅ := inferFpi Γ t (.free X) hΓf hts
  have hs := closedGenerationWF S hF.1.1 Γ t X hΓ hΓf ht hts hX hxΓ
  have hk : ∀ Y ∈ [X], Y.1 ∈ S.kinds := by simp [hX,hF.1.1.1]
  have hE : (D.existsNames [X]).WF S [] 0 := existsNamesWF S [X] D 0 hk hD
  have hEf : (D.existsNames [X]).fpi = ∅ := by rw [existsNamesFpi,hDf]
  have hR : (Constraint.conj C (D.existsNames [X])).WF S [] 0 := ⟨hw.1,hE⟩
  have hRf : (Constraint.conj C (D.existsNames [X])).fpi = ∅ := by
    simp [Constraint.fpi,hw.2.2.2.2.1,hEf]
  let L := u.fpi.image idNumber
  have htransfer : ∀ z, z ∉ L → Entails S M C
      (infer (Γ ++ [(.var z,s)]) (Expr.openAt 0 (.ident (.free (.var z))) u) T) := by
    intro z hz
    have hzu : Id.var z ∉ u.fpi := fun hm => hz (Finset.mem_image.mpr ⟨.var z,hm,rfl⟩)
    have hgen := generateLetFresh t u T X hX hxT
    have hEq : infer Γ (.letE t u) T =
        (Γ ++ [(Id.var z, Scheme.generalize [X] (generate t (.free X)) (.free X))]).letIn
          (generate (Expr.openAt 0 (.ident (.free (.var z))) u) T) := by
      rw [infer,hgen,letInSnoc,generateLetNameScheme u z T _ hzu]
    have hdup := letDup S M hF.1 Γ (.var z) [X] (generate t (.free X)) (.free X)
      (generate (Expr.openAt 0 (.ident (.free (.var z))) u) T) hΓ hΓf (by simp) (by simp [hxΓ])
      (hEq ▸ inferWF hF.1.1 hΓ hw.2.2.1 hT)
      (inferWF hF.1.1 (envSnocWF Γ (.var z) s hΓ hs.1) (exprOpenNameLC u z 0 hu) hT)
    intro ρ ι hρ hι hh
    apply hdup.1 ρ ι hρ hι
    rw [← hEq]
    exact he ρ ι hρ hι hh
  have hreal : Entails S M C (D.existsNames [X]) := by
    obtain ⟨z,hz⟩ := Finset.exists_notMem L
    exact fun ρ ι hρ hι hh =>
      prefixSnocRealizable hF.1 Γ (.var z) s _ hΓ hs.1 hs.2.1 ρ ι hρ hι
        (htransfer z hz ρ ι hρ hι hh)
  have hinit := iht (.conj C D) (.free X)
    (inferenceJudgment ⟨hw.1,hD⟩ hΓ ht hXk
      (by simp [Constraint.fpi,hw.2.2.2.2.1,hDf]) hΓf) (fun _ _ _ _ hh => hh.2)
  have hlet : AlternateTyping S M (.conj C (D.existsNames [X])) Γ (.letE t u) T := by
    apply AlternateTyping.letGen L (judgmentChangeConstraint hw hR hRf) (by simp)
      (by simpa using hxCΓ) hinit
    intro z hz
    apply ihu z _ _ T
      (inferenceJudgment hR (envSnocWF Γ (.var z) s hΓ hs.1) (exprOpenNameLC u z 0 hu)
        hT hRf (by rw [envSnocFpi,hΓf,hs.2.1]; rfl))
      (openedScope Γ u (.var z) s hus)
    exact fun ρ ι hρ hι hh => htransfer z hz ρ ι hρ hι hh.1
  exact alternateWeakening S M I hF (.conj C (D.existsNames [X])) C Γ (.letE t u) T hw
    (fun ρ ι hρ hι hh => ⟨hh,hreal ρ ι hρ hι hh⟩) hlet

/-- The induction constraint may be stronger than the generated constraint.
All environments and expected types remain universally quantified, including
those reached by opening a term binder. -/
theorem inferenceSoundnessBound (hF : Framework S M I) (n : Nat) :
    ∀ t, exprNodes t ≤ n → ∀ C Γ T, JudgmentWF S C Γ t (.mono T) → t.fpi ⊆ Γ.dpi →
      Entails S M C (infer Γ t T) → AlternateTyping S M C Γ t T := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro t hn C Γ T hw hscope he
      cases t with
      | ident x =>
          cases x with
          | free x =>
              exact inferenceVariable hF C Γ x T hw (hscope (by simp [Expr.fpi])) he
          | bound i => exact False.elim (Nat.not_lt_zero i hw.2.2.1)
      | lam t =>
          apply inferenceLambda hF C Γ t T hw hscope he
          intro z D Δ U hD hsc hgen
          apply ih (exprNodes t) (by simp only [exprNodes] at hn; omega)
            _ (by rw [exprNodesOpen]) D Δ U hD hsc hgen
      | app t u =>
          apply inferenceApplication hF C Γ t u T hw hscope he
          · intro D U hD hgen
            exact ih (exprNodes t) (by simp only [exprNodes] at hn; omega) t le_rfl D Γ U hD
              (fun _ hm => hscope (Finset.mem_union_left _ hm)) hgen
          · intro D U hD hgen
            exact ih (exprNodes u) (by simp only [exprNodes] at hn; omega) u le_rfl D Γ U hD
              (fun _ hm => hscope (Finset.mem_union_right _ hm)) hgen
      | letE t u =>
          apply inferenceLet hF C Γ t u T hw hscope he
          · intro D U hD hgen
            exact ih (exprNodes t) (by simp only [exprNodes] at hn; omega) t le_rfl D Γ U hD
              (fun _ hm => hscope (Finset.mem_union_left _ hm)) hgen
          · intro z D Δ U hD hsc hgen
            apply ih (exprNodes u) (by simp only [exprNodes] at hn; omega)
              _ (by rw [exprNodesOpen]) D Δ U hD hsc hgen

/-- ATTAPL 10.4.4 (Soundness), in the scoped locally nameless representation.
The source states the result on p.433 without a detailed proof; this fills in
the rule correspondence explained on p.432 and uses Figure 10-8 via 10.3.4. -/
theorem theorem10_4_4_soundness_scoped (S : Signature) (M : Model) (I : Set Nat) :
    HMX.LN.theorem10_4_4_soundness_scoped S M I := by
  intro hF Γ t T hΓ hΓf ht hscope hT
  apply (theorem10_3_4 S M I hF (infer Γ t T) Γ t T).mp
  exact inferenceSoundnessBound hF (exprNodes t) t le_rfl (infer Γ t T) Γ T
    (inferenceJudgment (inferWF hF.1.1 hΓ ht hT) hΓ ht hT (inferFpi Γ t T hΓf hscope) hΓf)
    hscope (fun _ _ _ _ hh => hh)

end HMX.LN.Proofs
