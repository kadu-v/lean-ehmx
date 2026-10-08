import SystemFXi.TypeLemmas

/-!
# 項変数の改名

`Γ ⊢ e : σ ∣ ε` における自由項変数の改名は、参照先の型を保てば
型付けを保存する。項置換と評価文脈の補題の基礎になる。
-/

namespace SystemFXi

/-- `ρ` が `Γ` の各項変数を同じ型の `Δ` の変数へ送る。 -/
def TermRenaming (Γ Δ : TermCtx) (ρ : Nat → Nat) : Prop :=
  ∀ i σ, Γ[i]? = some σ → Δ[ρ i]? = some σ

/-- `Γ → Δ` の改名は、両側に同じ型の変数を加えても有効。 -/
theorem TermRenaming.lift {Γ Δ : TermCtx} {ρ : Nat → Nat}
    (h : TermRenaming Γ Δ ρ) (a : Ty) :
    TermRenaming (a :: Γ) (a :: Δ) (liftTermRen ρ) := by
  intro i σ hi
  cases i with
  | zero =>
      simp at hi ⊢
      cases hi
      rfl
  | succ j =>
      simpa [liftTermRen] using h j σ (by simpa using hi)

/-- 型に同じ変換を施した二つの環境にも、改名は作用する。 -/
theorem TermRenaming.map {Γ Δ : TermCtx} {ρ : Nat → Nat}
    (h : TermRenaming Γ Δ ρ) (f : Ty → Ty) :
    TermRenaming (Γ.map f) (Δ.map f) ρ := by
  intro i σ hi
  simp only [List.getElem?_map] at hi ⊢
  cases hget : Γ[i]? with
  | none => simp [hget] at hi
  | some a =>
      have hσ : f a = σ := by simpa [hget] using hi
      subst σ
      simp [h i a hget]

/-- `Γ` の変数は、先頭に新しい変数を加えた環境で一つ後ろへ移る。 -/
theorem TermRenaming.weaken (Γ : TermCtx) (a : Ty) :
    TermRenaming Γ (a :: Γ) Nat.succ := by
  intro i σ hi
  simpa using hi

/-- `Γ ⊢ e : σ ∣ ε` と `Γ → Δ` から `Δ ⊢ ρ(e) : σ ∣ ε` を得る。 -/
theorem Typing.renameTerm_preserves {sig : Signature} {n : Nat}
    {Γ : TermCtx} {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ e σ ε) :
    ∀ (Δ : TermCtx) (ρ : Nat → Nat),
      TermRenaming Γ Δ ρ →
      Typing sig n Δ (e.renameTerm ρ) σ ε := by
  induction ht with
  | var hlookup =>
      intro Δ ρ hρ
      exact .var (hρ _ _ hlookup)
  | lam hwf hbody ih =>
      intro Δ ρ hρ
      exact .lam hwf (ih ( _ :: Δ) (liftTermRen ρ) (hρ.lift _))
  | app _ _ ihF ihX =>
      intro Δ ρ hρ
      exact .app (ihF Δ ρ hρ) (ihX Δ ρ hρ)
  | tlam _ ih =>
      intro Δ ρ hρ
      exact .tlam (ih (Δ.liftTy 1) ρ (hρ.map _))
  | tapp _ hwf ih =>
      intro Δ ρ hρ
      exact .tapp (ih Δ ρ hρ) hwf
  | perform hsig hlen hargs _ ih =>
      intro Δ ρ hρ
      exact .perform hsig hlen hargs (ih Δ ρ hρ)
  | handle hsig harity _ hε _ _ ihBody ihRet ihClause =>
      intro Δ ρ hρ
      apply Typing.handle hsig harity (ihBody Δ ρ hρ) hε
      · exact ihRet (_ :: Δ) (liftTermRen ρ) (hρ.lift _)
      · exact ihClause (_ :: _ :: Δ.liftTy _) (liftTermRenN 2 ρ)
          (by simpa only [liftTermRenN_two, TermCtx.liftTy] using
            ((hρ.map (Ty.rename (fun i => i + _))).lift _).lift _)
  | sub _ hs hε ih =>
      intro Δ ρ hρ
      exact .sub (ih Δ ρ hρ) hs hε

/-- `s : Γ ⇒ Δ` は各変数を同じ型の空効果の式へ送る項置換。 -/
def TermSubstitution (sig : Signature) (n : Nat)
    (Γ Δ : TermCtx) (s : Nat → Expr) : Prop :=
  ∀ i σ, Γ[i]? = some σ → Typing sig n Δ (s i) σ ∅

/-- 項置換は、両側に同じ型の項束縛子を加えても有効。 -/
theorem TermSubstitution.lift {sig : Signature} {n : Nat}
    {Γ Δ : TermCtx} {s : Nat → Expr}
    (h : TermSubstitution sig n Γ Δ s) (a : Ty) :
    TermSubstitution sig n (a :: Γ) (a :: Δ) (liftTermSubst s) := by
  intro i σ hi
  cases i with
  | zero =>
      simp at hi
      subst σ
      exact Typing.var rfl
  | succ j =>
      have hbase : Γ[j]? = some σ := by simpa using hi
      exact (h j σ hbase).renameTerm_preserves
        (a :: Δ) Nat.succ (TermRenaming.weaken Δ a)

/-- 型変数の改名は、項置換の各像にも同時に作用する。 -/
theorem TermSubstitution.renameTy {sig : Signature}
    (hsigwf : Signature.WF sig) {n m : Nat}
    {Γ Δ : TermCtx} {s : Nat → Expr}
    (h : TermSubstitution sig n Γ Δ s)
    (ρ : Nat → Nat) (hρ : ∀ i, i < n → ρ i < m) :
    TermSubstitution sig m (Γ.map (Ty.rename ρ))
      (Δ.map (Ty.rename ρ)) (fun i => (s i).renameTy ρ) := by
  intro i σ hi
  simp only [List.getElem?_map] at hi
  cases hget : Γ[i]? with
  | none => simp [hget] at hi
  | some a =>
      have hσ : a.rename ρ = σ := by simpa [hget] using hi
      subst σ
      exact (h i a hget).renameTy_preserves hsigwf ρ hρ

/-- `Γ ⊢ e : σ ∣ ε` と `s : Γ ⇒ Δ` から `Δ ⊢ e[s] : σ ∣ ε` を得る。 -/
theorem Typing.substTerm_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat}
    {Γ : TermCtx} {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ e σ ε) :
    ∀ (Δ : TermCtx) (s : Nat → Expr),
      TermSubstitution sig n Γ Δ s →
      Typing sig n Δ (e.substTerm s) σ ε := by
  induction ht with
  | var hlookup =>
      intro Δ s hs
      exact hs _ _ hlookup
  | lam hwf _ ih =>
      intro Δ s hs
      exact .lam hwf (ih (_ :: Δ) (liftTermSubst s) (hs.lift _))
  | app _ _ ihF ihX =>
      intro Δ s hs
      exact .app (ihF Δ s hs) (ihX Δ s hs)
  | @tlam n Γ body σ _ ih =>
      intro Δ s hs
      have hs' := TermSubstitution.renameTy hsigwf (m := n + 1)
        hs Nat.succ (by intro i hi; omega)
      exact .tlam (ih (Δ.liftTy 1) (liftTermSubstTyN 1 s)
        (by
          have hsucc : (fun i : Nat => i + 1) = Nat.succ := by
            funext i
            omega
          simpa [TermSubstitution, TermCtx.liftTy,
            liftTermSubstTyN, hsucc] using hs'))
  | tapp _ hwf ih =>
      intro Δ s hs
      exact .tapp (ih Δ s hs) hwf
  | perform hlookup hlen hargs _ ih =>
      intro Δ s hs
      exact .perform hlookup hlen hargs (ih Δ s hs)
  | @handle n Γ body op arity ret clause decl σin σout εin εout
      hlookup harity _ hε _ _ ihBody ihRet ihClause =>
      intro Δ s hs
      apply Typing.handle hlookup harity (ihBody Δ s hs) hε
      · exact ihRet (_ :: Δ) (liftTermSubst s) (hs.lift _)
      · have hs' := TermSubstitution.renameTy hsigwf (m := n + arity)
          hs (fun i => i + arity)
          (by intro i hi; omega)
        exact ihClause (_ :: _ :: Δ.liftTy arity)
          (liftTermSubstN 2 (liftTermSubstTyN arity s))
          (by
            have hbase :
                (fun i => Expr.renameTy (fun j => j + arity) (s i)) =
                  liftTermSubstTyN arity s := rfl
            have hLift := (hs'.lift decl.input).lift
              (.arr decl.output εout (σout.rename (fun i => i + arity)))
            rw [hbase] at hLift
            simpa only [liftTermSubstN_two, TermCtx.liftTy] using hLift)
  | sub _ hsub hε ih =>
      intro Δ s hs
      exact .sub (ih Δ s hs) hsub hε

/-- `Γ,x:σ₁ ⊢ e : σ₂ ∣ ε` と `Γ ⊢ v : σ₁ ∣ ∅` から
`Γ ⊢ e[x ↦ v] : σ₂ ∣ ε` が得られる。 -/
theorem Typing.instantiateTerm {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat} {Γ : TermCtx}
    {body value : Expr} {a b : Ty} {ε : Effect}
    (hbody : Typing sig n (a :: Γ) body b ε)
    (hvalue : Typing sig n Γ value a ∅) :
    Typing sig n Γ (body.instantiate value) b ε := by
  apply hbody.substTerm_preserves hsigwf Γ
    (fun | 0 => value | i + 1 => .var i)
  intro i σ hi
  cases i with
  | zero =>
      simp at hi
      subst σ
      exact hvalue
  | succ j =>
      have hget : Γ[j]? = some σ := by simpa using hi
      exact Typing.var hget

end SystemFXi
