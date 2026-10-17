import EHMX.Proofs.Typing
import EHMX.Operational

/-!
使用先は保存の Step.context 分岐。穴の型付けを変換する仮定を
Δ・C・Γ・型・効果すべてについて量化し、exists_ の内側へも適用する。
SystemFXi.Poly の EvalCtx.replace
(9173a02d9c67eea0b0c665d3319d834e3947518f) に対応する。
let の右辺については、穴が非値なら letPoly を除外できる。
-/
namespace EHMX

theorem evalCtxValue (E : EvalCtx) (hv : Value (E.plug e)) : Value e := by
  cases E <;> simp_all [EvalCtx.plug, Value, Expr.isValue]

theorem valueNoStep (hv : Value e) : ¬ Step e e' := by
  intro hs
  induction hs with
  | beta | letValue | returnValue | operation => simp [Value, Expr.isValue] at hv
  | context hs ih => exact ih (evalCtxValue _ hv)

theorem valueOpening (hv : Value v) (hus : ∀ u ∈ us, Value u) (d : Nat) :
    Value (v.openAt d us) := by
  cases v with
  | ident x =>
      cases x with
      | free x => rfl
      | bound i =>
          simp only [Expr.openAt]
          split
          · rfl
          · split
            · rename_i u hu
              exact valueShift (hus u (List.mem_of_getElem? hu)) _ _
            · rfl
  | lam body => rfl
  | app | letE | perform | handle => simp [Value, Expr.isValue] at hv

theorem judgmentWithScope (hw : JudgmentWF S Δ C Γ e T ε) (hs : e'.Scoped Γ) :
    JudgmentWF S Δ C Γ e' T ε :=
  ⟨hw.1, hw.2.1, hw.2.2.1, hs, hw.2.2.2.2⟩

theorem scopedApp (hf : Expr.Scoped Γ f) (hx : Expr.Scoped Γ x) :
    (Expr.app f x).Scoped Γ :=
  ⟨⟨hf.1, hx.1⟩, Finset.union_subset hf.2 hx.2⟩

theorem scopedLet (hr : Expr.Scoped Γ rhs) (hb : Expr.Scoped (Γ.push s) body) :
    (Expr.letE rhs body).Scoped Γ :=
  ⟨⟨hr.1, hb.1⟩, Finset.union_subset hr.2 hb.2⟩

/-- Uniform replacement is crucial: the hole may be typed under existential
binders and stronger constraints, rather than in the outer judgment. -/
theorem evalCtxReplacement (hnv : ¬ Value e₀)
    (hreplace : ∀ Δ C Γ T ε, Typing S M sig Δ C Γ e₀ T ε → Typing S M sig Δ C Γ e₁ T ε)
    (ht : Typing S M sig Δ C Γ e T ε) :
    ∀ E : EvalCtx, e = E.plug e₀ → Typing S M sig Δ C Γ (E.plug e₁) T ε := by
  induction ht with
  | var hw hl he =>
      intro E h
      cases E <;> simp only [EvalCtx.plug] at h
      · subst h; exact hreplace _ _ _ _ _ (.var hw hl he)
      all_goals cases h
  | lam hw hb ih =>
      intro E h
      cases E <;> simp only [EvalCtx.plug] at h
      · subst h; exact hreplace _ _ _ _ _ (.lam hw hb)
      all_goals cases h
  | app hw hf hx ihf ihx =>
      intro E h
      cases E <;> simp only [EvalCtx.plug] at h
      · subst h; exact hreplace _ _ _ _ _ (.app hw hf hx)
      · cases h
        have hf' := ihf _ rfl
        exact .app (judgmentWithScope hw (scopedApp (typingWF hf').2.2.2.1
          (typingWF hx).2.2.2.1)) hf' hx
      · cases h
        have hx' := ihx _ rfl
        exact .app (judgmentWithScope hw (scopedApp (typingWF hf).2.2.2.1
          (typingWF hx').2.2.2.1)) hf hx'
      all_goals cases h
  | letMono hw hr hb ihr ihb =>
      intro E h
      cases E <;> simp only [EvalCtx.plug] at h
      · subst h; exact hreplace _ _ _ _ _ (.letMono hw hr hb)
      · cases h
      · cases h
      · cases h
        have hr' := ihr _ rfl
        exact .letMono (judgmentWithScope hw (scopedLet (typingWF hr').2.2.2.1
          (typingWF hb).2.2.2.1)) hr' hb
      all_goals cases h
  | letPoly hw hv hr he hb ihr ihb =>
      intro E h
      cases E <;> simp only [EvalCtx.plug] at h
      · subst h; exact hreplace _ _ _ _ _ (.letPoly hw hv hr he hb)
      · cases h
      · cases h
      · cases h; exact False.elim (hnv (evalCtxValue _ hv))
      all_goals cases h
  | perform hw hs ha ht ih =>
      intro E h
      cases E <;> simp only [EvalCtx.plug] at h
      · subst h; exact hreplace _ _ _ _ _ (.perform hw hs ha ht)
      · cases h
      · cases h
      · cases h
      · cases h
        have ht' := ih _ rfl
        exact .perform (judgmentWithScope hw (typingWF ht').2.2.2.1) hs ha ht'
      · cases h
  | handle hw hs hb he hr hc ihb ihr ihc =>
      intro E h
      cases E <;> simp only [EvalCtx.plug] at h
      · subst h; exact hreplace _ _ _ _ _ (.handle hw hs hb he hr hc)
      · cases h
      · cases h
      · cases h
      · cases h
      · cases h
        have hb' := ihb _ rfl
        have hscope := hw.2.2.2.1
        have hnew := (typingWF hb').2.2.2.1
        apply Typing.handle (judgmentWithScope hw ?_) hs hb' he hr hc
        exact ⟨⟨hnew.1, hscope.1.2⟩,
          Finset.union_subset (Finset.union_subset hnew.2
            (Finset.union_subset_iff.mp (Finset.union_subset_iff.mp hscope.2).1).2)
            (Finset.union_subset_iff.mp hscope.2).2⟩
  | sub hw ht hT hε ih =>
      intro E h
      have ht' := ih E h
      exact .sub (judgmentWithScope hw (typingWF ht').2.2.2.1) ht' hT hε
  | strengthen hw ht he ih =>
      intro E h
      have ht' := ih E h
      exact .strengthen (judgmentWithScope hw (typingWF ht').2.2.2.1) ht' he
  | exists_ hw ht ih =>
      intro E h
      have ht' := ih E h
      apply Typing.exists_ (judgmentWithScope hw ?_) ht'
      simpa [Expr.Scoped, Env.shift, Env.dpi, List.map_map, Function.comp_def]
        using (typingWF ht').2.2.2.1

end EHMX
