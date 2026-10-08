import SystemFXi.TermLemmas
import SystemFXi.Progress

/-!
# 値と型付けの逆向き補題

暗黙の部分型規則を取り除き、抽象の本体に対する型付けを得る。
-/

namespace SystemFXi

/-- 値 `v` の評価効果は空にできる: `Γ ⊢ v : σ ∣ ε ⇒ Γ ⊢ v : σ ∣ ∅`。 -/
theorem Typing.value_pure {sig : Signature} {n : Nat}
    {Γ : TermCtx} {v : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ v σ ε) :
    Value v → Typing sig n Γ v σ ∅ := by
  induction ht with
  | var hlookup => intro _; exact .var hlookup
  | lam hwf hbody _ => intro _; exact .lam hwf hbody
  | tlam hbody _ => intro _; exact .tlam hbody
  | app => intro hv; cases hv
  | tapp => intro hv; cases hv
  | perform => intro hv; cases hv
  | handle => intro hv; cases hv
  | sub _ hsub _ ih =>
      intro hv
      exact .sub (ih hv) hsub (by simp)

/-- `Γ ⊢ λx:ann.e : a → ε b ∣ ε′` の本体と元の矢印型を得る。 -/
theorem Typing.lambda_arrow_inv {sig : Signature} {n : Nat}
    {Γ : TermCtx} {ann : Ty} {body : Expr}
    {a b : Ty} {ε εval : Effect}
    (ht : Typing sig n Γ (.lam ann body) (.arr a ε b) εval) :
    ∃ b₀ ε₀,
      Typing sig n (ann :: Γ) body b₀ ε₀ ∧
      Subtype sig n (.arr ann ε₀ b₀) (.arr a ε b) := by
  generalize he : Expr.lam ann body = e at ht
  generalize hty : Ty.arr a ε b = ty at ht
  induction ht generalizing ann body a ε b with
  | lam _ hbody =>
      cases he
      cases hty
      exact ⟨_, _, hbody, Subtype.refl _ _⟩
  | sub _ hsub _ ih =>
      cases hty
      cases hsub with
      | arr harg heff hresult =>
          obtain ⟨b₀, ε₀, hbody, hs⟩ := ih he rfl
          exact ⟨b₀, ε₀, hbody,
            Subtype.trans hs (.arr harg heff hresult)⟩
  | var => cases he
  | app => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he
  | handle => cases he

/-- `Γ ⊢ Λα.e : ∀α.σ ∣ ε` から型抽象本体の型付けを得る。 -/
theorem Typing.typeLambda_all_inv {sig : Signature} {n : Nat}
    {Γ : TermCtx} {body : Expr} {σ : Ty} {εval : Effect}
    (ht : Typing sig n Γ (.tlam body) (.all σ) εval) :
    ∃ σ₀,
      Typing sig (n + 1) (Γ.liftTy 1) body σ₀ ∅ ∧
      Subtype sig n (.all σ₀) (.all σ) := by
  generalize he : Expr.tlam body = e at ht
  generalize hty : Ty.all σ = ty at ht
  induction ht generalizing body σ with
  | tlam hbody =>
      cases he
      cases hty
      exact ⟨_, hbody, Subtype.refl _ _⟩
  | sub _ hsub _ ih =>
      cases hty
      cases hsub with
      | all hbodySub =>
          obtain ⟨σ₀, hbody, hs⟩ := ih he rfl
          exact ⟨σ₀, hbody,
            Subtype.trans hs (.all hbodySub)⟩
  | var => cases he
  | lam => cases he
  | app => cases he
  | tapp => cases he
  | perform => cases he
  | handle => cases he

end SystemFXi
