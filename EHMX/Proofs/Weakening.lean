import EHMX.Proofs.TypingTypeSubstitution
import EHMX.Operational

/-!
使用先: 捕捉継続の lambda と値代入の束縛分岐。
SystemFXi.Poly.Typing.renameTerm_preserves
(9173a02d9c67eea0b0c665d3319d834e3947518f) の環境拡張の場合。
EHMX のスキームと型量化の下でも同じ束縛位置を保持する。
-/
namespace EHMX

theorem exprShiftFv (e : Expr) (n d : Nat) : (e.shift n d).fv = e.fv := by
  induction e generalizing d with
  | ident x => cases x <;> simp [Expr.shift, Expr.fv]
  | _ => simp_all [Expr.shift, Expr.fv]

theorem exprShiftLC (he : Expr.LCAt n e) (m d : Nat) :
    (e.shift m d).LCAt (n + m) := by
  induction e generalizing n d with
  | ident x =>
      cases x with
      | free x => trivial
      | bound i => simp only [Expr.shift, Expr.LCAt] at he ⊢; split <;> omega
  | lam body ih =>
      simpa only [Expr.shift, Expr.LCAt, Nat.add_right_comm] using ih he (d + 1)
  | app f x ihf ihx => exact ⟨ihf he.1 d, ihx he.2 d⟩
  | letE rhs body ihr ihb =>
      exact ⟨ihr he.1 d, by simpa only [Nat.add_right_comm] using ihb he.2 (d + 1)⟩
  | perform op arg ih => exact ih he d
  | handle body op ret clause ihb ihr ihc =>
      exact ⟨ihb he.1 d, by simpa only [Nat.add_right_comm] using ihr he.2.1 (d + 1),
        by simpa only [Nat.add_right_comm] using ihc he.2.2 (d + 2)⟩

def Env.insertAfter (Γ : Env) (pre post : List Scheme) (s : Scheme) : Env :=
  { Γ with bound := pre ++ s :: post }

theorem lookupInsertAfter {Γ : Env} {x : PVar} (hΓ : Γ.bound = pre ++ post) :
    (Γ.insertAfter pre post s).lookup
      (match x with
       | .free x => .free x
       | .bound i => .bound (if i < pre.length then i else i + 1)) = Γ.lookup x := by
  cases x with
  | free x => rfl
  | bound i =>
      simp only [Env.lookup, Env.insertAfter, hΓ]
      by_cases h : i < pre.length
      · simp [h, List.getElem?_append]
      · have hn : ¬ i + 1 < pre.length := by omega
        have he : i + 1 - pre.length = (i - pre.length) + 1 := by omega
        simp [h, hn, List.getElem?_append, he]

theorem judgmentInsertAfter (hw : JudgmentWF S Δ C Γ e T ε)
    (hΓ : Γ.bound = pre ++ post) (hs : s.WF S Δ 0 ∧ s.fpi = ∅) :
    JudgmentWF S Δ C (Γ.insertAfter pre post s) (e.shift 1 pre.length) T ε := by
  refine ⟨hw.1, hw.2.1, ⟨hw.2.2.1.1, ?_⟩, ?_, hw.2.2.2.2⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact hw.2.2.1.2 t (by rw [hΓ]; exact List.mem_append_left _ ht)
    · rcases List.mem_cons.mp ht with rfl | ht
      · exact hs
      · exact hw.2.2.1.2 t (by rw [hΓ]; exact List.mem_append_right _ ht)
  · refine ⟨?_, ?_⟩
    · have h := exprShiftLC hw.2.2.2.1.1 1 pre.length
      simpa [Env.insertAfter, hΓ, List.length_append, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h
    · simpa only [exprShiftFv, Env.insertAfter, Env.dpi] using hw.2.2.2.1.2

theorem envInsertAfterShift (Γ : Env) (pre post : List Scheme) (s : Scheme) (n : Nat) :
    (Γ.insertAfter pre post s).shift n =
      (Γ.shift n).insertAfter (pre.map (Scheme.shift n 0))
        (post.map (Scheme.shift n 0)) (s.shift n 0) := by
  simp [Env.insertAfter, Env.shift]

/-- Insertion at an arbitrary depth is required when passing lambda, let,
return (one binder) and operation clauses (two binders). -/
theorem typingWeakeningAt (ht : Typing S M sig Δ C Γ e T ε) :
    ∀ pre post s, Γ.bound = pre ++ post → s.WF S Δ 0 ∧ s.fpi = ∅ →
      Typing S M sig Δ C (Γ.insertAfter pre post s) (e.shift 1 pre.length) T ε := by
  induction ht with
  | @var Δ C Γ x T t hw hl he =>
      intro pre post s hΓ hs
      have hl' := (lookupInsertAfter (x := x) (s := s) hΓ).trans hl
      cases x with
      | free x => exact .var (judgmentInsertAfter hw hΓ hs) hl' he
      | bound i => exact .var (judgmentInsertAfter hw hΓ hs) hl' he
  | @lam Δ C Γ body A ε B hw hb ih =>
      intro pre post s hΓ hs
      have hb' := ih (.mono A :: pre) post s (by simp [Env.push, hΓ]) hs
      exact .lam (judgmentInsertAfter hw hΓ hs) hb'
  | app hw hf hx ihf ihx =>
      intro pre post s hΓ hs
      exact .app (judgmentInsertAfter hw hΓ hs) (ihf _ _ _ hΓ hs) (ihx _ _ _ hΓ hs)
  | @letMono Δ C Γ rhs body B εrhs εbody A hw hr hb ihr ihb =>
      intro pre post s hΓ hs
      have hb' := ihb (.mono A :: pre) post s (by simp [Env.push, hΓ]) hs
      exact .letMono (judgmentInsertAfter hw hΓ hs) (ihr _ _ _ hΓ hs) hb'
  | @letPoly Δ C Γ rhs body B ε ks D A hw hv hr he hb ihr ihb =>
      intro pre post s hΓ hs
      have hs' : (s.shift ks.length 0).WF S (ks ++ Δ) 0 ∧ (s.shift ks.length 0).fpi = ∅ :=
        ⟨schemeShiftWF hs.1 ks, (schemeShiftFpi _ _ _).trans hs.2⟩
      have hr' := ihr (pre.map (Scheme.shift ks.length 0)) (post.map (Scheme.shift ks.length 0))
        (s.shift ks.length 0) (by simp [Env.shift, hΓ]) hs'
      rw [← envInsertAfterShift] at hr'
      simp only [List.length_map] at hr'
      have hb' := ihb (.all ks D A :: pre) post s (by simp [Env.push, hΓ]) hs
      exact .letPoly (judgmentInsertAfter hw hΓ hs) (valueShift hv _ _) hr' he hb'
  | perform hw hl ha hp ht ih =>
      intro pre post s hΓ hs
      exact .perform (judgmentInsertAfter hw hΓ hs) hl ha hp (ih _ _ _ hΓ hs)
  | @handle Δ C Γ body op ret clause B εout decl A εin hw hl hb he hr hc ihb ihr ihc =>
      intro pre post s hΓ hs
      have hr' := ihr (.mono A :: pre) post s (by simp [Env.push, hΓ]) hs
      have hs' : (s.shift decl.kinds.length 0).WF S (decl.kinds ++ Δ) 0 ∧
          (s.shift decl.kinds.length 0).fpi = ∅ :=
        ⟨schemeShiftWF hs.1 _, (schemeShiftFpi _ _ _).trans hs.2⟩
      have hc' := ihc (.mono (.arrow decl.output (εout.shift decl.kinds.length 0) (B.shift decl.kinds.length 0)) :: .mono decl.input :: pre.map (Scheme.shift decl.kinds.length 0))
        (post.map (Scheme.shift decl.kinds.length 0)) (s.shift decl.kinds.length 0)
        (by simp [Env.push, Env.shift, hΓ]) hs'
      simp only [List.length_cons, List.length_map] at hc'
      exact .handle (judgmentInsertAfter hw hΓ hs) hl (ihb _ _ _ hΓ hs) he hr'
        (by simpa [Env.insertAfter, Env.shift, Env.push] using hc')
  | sub hw ht hT hε ih =>
      intro pre post s hΓ hs
      exact .sub (judgmentInsertAfter hw hΓ hs) (ih _ _ _ hΓ hs) hT hε
  | strengthen hw ht he ih =>
      intro pre post s hΓ hs
      exact .strengthen (judgmentInsertAfter hw hΓ hs) (ih _ _ _ hΓ hs) he
  | @exists_ Δ ks C Γ e T ε hw ht ih =>
      intro pre post s hΓ hs
      have hs' : (s.shift ks.length 0).WF S (ks ++ Δ) 0 ∧ (s.shift ks.length 0).fpi = ∅ :=
        ⟨schemeShiftWF hs.1 ks, (schemeShiftFpi _ _ _).trans hs.2⟩
      have ht' := ih (pre.map (Scheme.shift ks.length 0)) (post.map (Scheme.shift ks.length 0))
        (s.shift ks.length 0) (by simp [Env.shift, hΓ]) hs'
      rw [← envInsertAfterShift] at ht'
      simp only [List.length_map] at ht'
      exact .exists_ (judgmentInsertAfter hw hΓ hs) ht'

theorem typingWeakening (ht : Typing S M sig Δ C Γ e T ε)
    (hs : s.WF S Δ 0 ∧ s.fpi = ∅) :
    Typing S M sig Δ C (Γ.push s) (e.shift 1 0) T ε :=
  typingWeakeningAt ht [] Γ.bound s rfl hs

end EHMX
