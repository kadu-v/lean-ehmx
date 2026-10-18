import EHMX.Semantics

/-! EHMX の宣言的型付け。let の一般化だけが多相スキームを導入する。
型・効果の新しい束縛は外側の環境と制約を shift して分離する。 -/
namespace EHMX

def JudgmentWF (S : Signature) (Δ : List Kind) (C : Constraint)
    (Γ : Env) (e : Expr) (T : Ty) (ε : Effect) : Prop :=
  C.WF S Δ 0 ∧ C.fpi = ∅ ∧ Γ.WF S Δ ∧ e.Scoped Γ ∧
  T.HasKind S Δ 0 ∧ ε.HasKind S Δ 1

inductive Typing (S : Signature) (M : Model) (sig : OpSignature) :
    List Kind → Constraint → Env → Expr → Ty → Effect → Prop where
  | var : JudgmentWF S Δ C Γ (.ident x) T .empty →
      Γ.lookup x = some s → Entails S M Δ C (s.instanceConstraint T) →
      Typing S M sig Δ C Γ (.ident x) T .empty
  | lam : JudgmentWF S Δ C Γ (.lam body) (.arrow A ε B) .empty →
      Typing S M sig Δ C (Γ.push (.mono A)) body B ε →
      Typing S M sig Δ C Γ (.lam body) (.arrow A ε B) .empty
  | app : JudgmentWF S Δ C Γ (.app f x) B (.union (.union εf εx) η) →
      Typing S M sig Δ C Γ f (.arrow A η B) εf →
      Typing S M sig Δ C Γ x A εx →
      Typing S M sig Δ C Γ (.app f x) B (.union (.union εf εx) η)
  | letMono : JudgmentWF S Δ C Γ (.letE rhs body) B (.union εrhs εbody) →
      Typing S M sig Δ C Γ rhs A εrhs →
      Typing S M sig Δ C (Γ.push (.mono A)) body B εbody →
      Typing S M sig Δ C Γ (.letE rhs body) B (.union εrhs εbody)
  | letPoly : JudgmentWF S Δ C Γ (.letE rhs body) B ε → Value rhs →
      Typing S M sig (ks ++ Δ) (.conj (C.shift ks.length 0) D)
        (Γ.shift ks.length) rhs A .empty →
      Entails S M Δ C (.exists_ ks D) →
      Typing S M sig Δ C (Γ.push (.all ks D A)) body B ε →
      Typing S M sig Δ C Γ (.letE rhs body) B ε
  | perform : JudgmentWF S Δ C Γ (.perform op arg)
        (decl.output.openAt 0 args) (.union (.singleton op) ε) →
      sig op = some decl → List.Forall₂ (Ty.HasKind S Δ) args decl.kinds →
      Entails S M Δ C (decl.condition.substBound (BoundSubst.many args)) →
      Typing S M sig Δ C Γ arg (decl.input.openAt 0 args) ε →
      Typing S M sig Δ C Γ (.perform op arg)
        (decl.output.openAt 0 args) (.union (.singleton op) ε)
  | handle : JudgmentWF S Δ C Γ (.handle body op ret clause) B εout →
      sig op = some decl →
      Typing S M sig Δ C Γ body A εin →
      Entails S M Δ C (.le 1 εin (.union (.singleton op) εout)) →
      Typing S M sig Δ C (Γ.push (.mono A)) ret B εout →
      Typing S M sig (decl.kinds ++ Δ) (.conj (C.shift decl.kinds.length 0) decl.condition)
        (((Γ.shift decl.kinds.length).push (.mono decl.input)).push
          (.mono (.arrow decl.output (εout.shift decl.kinds.length 0)
            (B.shift decl.kinds.length 0))))
        clause (B.shift decl.kinds.length 0) (εout.shift decl.kinds.length 0) →
      Typing S M sig Δ C Γ (.handle body op ret clause) B εout
  | sub : JudgmentWF S Δ C Γ e U η → Typing S M sig Δ C Γ e T ε →
      Entails S M Δ C (.le 0 T U) → Entails S M Δ C (.le 1 ε η) →
      Typing S M sig Δ C Γ e U η
  | strengthen : JudgmentWF S Δ D Γ e T ε → Typing S M sig Δ C Γ e T ε →
      Entails S M Δ D C → Typing S M sig Δ D Γ e T ε
  | exists_ : JudgmentWF S Δ (.exists_ ks C) Γ e T ε →
      Typing S M sig (ks ++ Δ) C (Γ.shift ks.length) e
        (T.shift ks.length 0) (ε.shift ks.length 0) →
      Typing S M sig Δ (.exists_ ks C) Γ e T ε

theorem typingWF (h : Typing S M sig Δ C Γ e T ε) : JudgmentWF S Δ C Γ e T ε := by
  cases h <;> assumption

/-- Keep a local condition while strengthening the surrounding constraint. -/
theorem typingConjStronger (ht : Typing S M sig Δ (.conj C P) Γ e T ε)
    (hD : D.WF S Δ 0) (hf : D.fpi = ∅) (he : Entails S M Δ D C) :
    Typing S M sig Δ (.conj D P) Γ e T ε := by
  have hw := typingWF ht
  have hp : P.fpi = ∅ := (Finset.union_eq_empty.mp hw.2.1).2
  exact .strengthen ⟨⟨hD, hw.1.2⟩, by simp [Constraint.fpi, hf, hp], hw.2.2⟩ ht
    (fun ρ bs ι hρ hbs hι h => ⟨he ρ bs ι hρ hbs hι h.1, h.2⟩)

/-- Unconditional declarations retain the former perform rule. -/
theorem Typing.performTruth {decl : OpDecl} (hcondition : decl.condition = .truth)
    (hw : JudgmentWF S Δ C Γ (.perform op arg)
      (decl.output.openAt 0 args) (.union (.singleton op) ε))
    (hs : sig op = some decl) (ha : List.Forall₂ (Ty.HasKind S Δ) args decl.kinds)
    (ht : Typing S M sig Δ C Γ arg (decl.input.openAt 0 args) ε) :
    Typing S M sig Δ C Γ (.perform op arg) (decl.output.openAt 0 args)
      (.union (.singleton op) ε) :=
  .perform hw hs ha (by simp [hcondition, Constraint.substBound, Entails, Constraint.Holds]) ht

theorem Typing.withConjTruth (ht : Typing S M sig Δ C Γ e T ε) :
    Typing S M sig Δ (.conj C .truth) Γ e T ε :=
  .strengthen ⟨⟨(typingWF ht).1, trivial⟩,
    by simpa only [Constraint.fpi, Finset.union_empty] using (typingWF ht).2.1,
    (typingWF ht).2.2⟩ ht (fun _ _ _ _ _ _ h => h.1)

/-- A truth condition gives precisely the former operation-clause obligation. -/
theorem Typing.handleTruth {decl : OpDecl} (hcondition : decl.condition = .truth)
    (hw : JudgmentWF S Δ C Γ (.handle body op ret clause) B εout)
    (hs : sig op = some decl) (hb : Typing S M sig Δ C Γ body A εin)
    (he : Entails S M Δ C (.le 1 εin (.union (.singleton op) εout)))
    (hr : Typing S M sig Δ C (Γ.push (.mono A)) ret B εout)
    (hc : Typing S M sig (decl.kinds ++ Δ) (C.shift decl.kinds.length 0)
      (((Γ.shift decl.kinds.length).push (.mono decl.input)).push
        (.mono (.arrow decl.output (εout.shift decl.kinds.length 0) (B.shift decl.kinds.length 0))))
      clause (B.shift decl.kinds.length 0) (εout.shift decl.kinds.length 0)) :
    Typing S M sig Δ C Γ (.handle body op ret clause) B εout :=
  .handle hw hs hb he hr (by rw [hcondition]; exact hc.withConjTruth)

end EHMX
