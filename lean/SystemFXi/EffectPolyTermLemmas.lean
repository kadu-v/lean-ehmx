import SystemFXi.EffectPolyTypingLemmas

/-!
# 効果多相な項変数の改名と置換

自由項変数の改名は参照先の型を保存する。項置換の像は空の評価効果を
持ち、型・効果変数の量化子の下では両種の添字を持ち上げる。
-/

namespace SystemFXi.Poly

/-- Δ ⊢ Γ は、Γ に格納された全ての値型が Δ で整形式であることを表す。 -/
def TermCtx.WF (sig : Signature) (Δ : List Kind) (Γ : TermCtx) : Prop :=
  ∀ (i : Nat) (σ : Ty), Γ[i]? = some σ → Ty.WF sig Δ σ

/-- 整形式の型を Γ の先頭に追加しても環境は整形式。 -/
theorem TermCtx.WF.cons {sig : Signature} {Δ : List Kind} {Γ : TermCtx}
    (hΓ : TermCtx.WF sig Δ Γ) {σ : Ty} (hσ : Ty.WF sig Δ σ) :
    TermCtx.WF sig Δ (σ :: Γ) := by
  intro i τ hi
  cases i with
  | zero =>
      simp at hi
      subst τ
      exact hσ
  | succ j => exact hΓ j τ (by simpa using hi)

/-- 空の項環境は任意の kind 環境で整形式。 -/
theorem TermCtx.WF.nil (sig : Signature) (Δ : List Kind) :
    TermCtx.WF sig Δ [] := by
  intro i σ hi
  simp at hi

/-- ρ : Γ → Γ′ は項変数の参照先の型を保存する。 -/
def TermRenaming (Γ Γ' : TermCtx) (ρ : Nat → Nat) : Prop :=
  ∀ i σ, Γ[i]? = some σ → Γ'[ρ i]? = some σ

/-- 同じ型の項変数を両環境に加えても改名は有効。 -/
theorem TermRenaming.lift {Γ Γ' : TermCtx} {ρ : Nat → Nat}
    (h : TermRenaming Γ Γ' ρ) (a : Ty) :
    TermRenaming (a :: Γ) (a :: Γ') (liftTermRen ρ) := by
  intro i σ hi
  cases i with
  | zero =>
      simp at hi ⊢
      cases hi
      rfl
  | succ j =>
      simpa [liftTermRen] using h j σ (by simpa using hi)

/-- 型注釈を同じ関数で写した環境にも改名は作用する。 -/
theorem TermRenaming.map {Γ Γ' : TermCtx} {ρ : Nat → Nat}
    (h : TermRenaming Γ Γ' ρ) (f : Ty → Ty) :
    TermRenaming (Γ.map f) (Γ'.map f) ρ := by
  intro i σ hi
  simp only [List.getElem?_map] at hi ⊢
  cases hget : Γ[i]? with
  | none => simp [hget] at hi
  | some a =>
      have hσ : f a = σ := by simpa [hget] using hi
      subst σ
      simp [h i a hget]

/-- Γ の変数は、先頭へ一つ追加した環境で一つ後ろへ移る。 -/
theorem TermRenaming.weaken (Γ : TermCtx) (a : Ty) :
    TermRenaming Γ (a :: Γ) Nat.succ := by
  intro i σ hi
  simpa using hi

/-- Γ ⊢ e : σ ∣ ε は項変数の型を保つ改名で保存される。 -/
theorem Typing.renameTerm_preserves {sig : Signature}
    {K : List Kind} {Γ : TermCtx}
    {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig K Γ e σ ε) :
    ∀ (Γ' : TermCtx) (ρ : Nat → Nat),
      TermRenaming Γ Γ' ρ →
      Typing sig K Γ' (e.renameTerm ρ) σ ε := by
  induction ht with
  | var hlookup hwf =>
      intro Γ' ρ hρ
      exact .var (hρ _ _ hlookup) hwf
  | lam hwf _ ih =>
      intro Γ' ρ hρ
      exact .lam hwf (ih (_ :: Γ') (liftTermRen ρ) (hρ.lift _))
  | app _ _ ihF ihX =>
      intro Γ' ρ hρ
      exact .app (ihF Γ' ρ hρ) (ihX Γ' ρ hρ)
  | tlam _ ih =>
      intro Γ' ρ hρ
      exact .tlam (ih (Γ'.liftKind 1) ρ (hρ.map _))
  | tapp _ hwf ih =>
      intro Γ' ρ hρ
      exact .tapp (ih Γ' ρ hρ) hwf
  | perform hsig hargs _ ih =>
      intro Γ' ρ hρ
      exact .perform hsig hargs (ih Γ' ρ hρ)
  | handle hsig harity _ hε _ _ ihBody ihRet ihClause =>
      intro Γ' ρ hρ
      apply Typing.handle hsig harity (ihBody Γ' ρ hρ) hε
      · exact ihRet (_ :: Γ') (liftTermRen ρ) (hρ.lift _)
      · exact ihClause (_ :: _ :: Γ'.liftKind _)
          (liftTermRenN 2 ρ)
          (by
            simpa only [TermCtx.liftKind, liftTermRenN_two] using
              ((hρ.map (Ty.rename (fun i => i + _))).lift _).lift _)
  | sub _ hs hσ hε hsubset ih =>
      intro Γ' ρ hρ
      exact .sub (ih Γ' ρ hρ) hs hσ hε hsubset

/-- s : Γ ⇒ Γ′ は各項変数を同じ型の空効果の式へ送る。 -/
def TermSubstitution (sig : Signature) (K : List Kind)
    (Γ Γ' : TermCtx) (s : Nat → Expr) : Prop :=
  ∀ i σ, Γ[i]? = some σ → Typing sig K Γ' (s i) σ ∅

/-- 項置換を同じ型の項束縛子の下へ移す。 -/
theorem TermSubstitution.lift {sig : Signature} {K : List Kind}
    {Γ Γ' : TermCtx} {s : Nat → Expr}
    (h : TermSubstitution sig K Γ Γ' s) (a : Ty)
    (ha : Ty.WF sig K a) :
    TermSubstitution sig K (a :: Γ) (a :: Γ')
      (liftTermSubst s) := by
  intro i σ hi
  cases i with
  | zero =>
      simp at hi
      subst σ
      exact Typing.var rfl ha
  | succ j =>
      have hbase : Γ[j]? = some σ := by simpa using hi
      exact (h j σ hbase).renameTerm_preserves
        (a :: Γ') Nat.succ (TermRenaming.weaken Γ' a)

/-- 型・効果変数の改名は項置換の像にも作用する。 -/
theorem TermSubstitution.renameKind {sig : Signature}
    (hsigwf : Signature.WF sig)
    {K K' : List Kind} {Γ Γ' : TermCtx} {s : Nat → Expr}
    (h : TermSubstitution sig K Γ Γ' s)
    (ρ : Nat → Nat) (hρ : RenValid K K' ρ) :
    TermSubstitution sig K'
      (Γ.map (Ty.rename ρ))
      (Γ'.map (Ty.rename ρ))
      (fun i => (s i).renameKind ρ) := by
  intro i σ hi
  simp only [List.getElem?_map] at hi
  cases hget : Γ[i]? with
  | none => simp [hget] at hi
  | some a =>
      have hσ : a.rename ρ = σ := by simpa [hget] using hi
      subst σ
      exact (h i a hget).renameKind_preserves hsigwf ρ hρ

/-- kind 環境 K の変数を n 個の量化子の外側へ移す改名。 -/
theorem RenValid.shift {K : List Kind}
    (ks : List Kind) :
    RenValid K (ks ++ K) (fun i => i + ks.length) := by
  intro i κ hi
  have hlarge : ks.length ≤ i + ks.length := by omega
  rw [List.getElem?_append_right hlarge]
  simpa using hi

/-- 宣言型は外側の kind 環境を付け足しても整形式。 -/
theorem Ty.WF.append_outer {sig : Signature}
    {ks : List Kind} {σ : Ty}
    (h : Ty.WF sig ks σ) (K : List Kind) :
    Ty.WF sig (ks ++ K) σ := by
  have hρ : RenValid ks (ks ++ K) id := by
    intro i κ hi
    simpa [List.getElem?_append_left
      ((List.getElem?_eq_some_iff.mp hi).choose)] using hi
  simpa only [Ty.rename_id] using h.rename_preserves id hρ

/-- Γ ⊢ e : σ ∣ ε は純粋な項置換 s の下で保存される。 -/
theorem Typing.substTerm_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {K : List Kind}
    {Γ : TermCtx} {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig K Γ e σ ε) :
    ∀ (Γ' : TermCtx) (s : Nat → Expr),
      TermSubstitution sig K Γ Γ' s →
      Typing sig K Γ' (e.substTerm s) σ ε := by
  induction ht with
  | var hlookup hwf =>
      intro Γ' s hs
      exact hs _ _ hlookup
  | lam hwf _ ih =>
      intro Γ' s hs
      exact .lam hwf (ih (_ :: Γ') (liftTermSubst s)
        (hs.lift _ hwf))
  | app _ _ ihF ihX =>
      intro Γ' s hs
      exact .app (ihF Γ' s hs) (ihX Γ' s hs)
  | @tlam K Γ κ body σ _ ih =>
      intro Γ' s hs
      have hs' := TermSubstitution.renameKind hsigwf hs
        Nat.succ (by
          simpa using (RenValid.shift (K := K) [κ]))
      exact .tlam (ih (Γ'.liftKind 1)
        (liftTermSubstKindN 1 s)
        (by
          have hsucc : (fun i : Nat => i + 1) = Nat.succ := by
            funext i
            omega
          simpa [TermSubstitution, TermCtx.liftKind,
            liftTermSubstKindN, hsucc] using hs'))
  | tapp _ hwf ih =>
      intro Γ' s hs
      exact .tapp (ih Γ' s hs) hwf
  | perform hlookup hargs _ ih =>
      intro Γ' s hs
      exact .perform hlookup hargs (ih Γ' s hs)
  | @handle K Γ body op arity ret clause decl σin σout εin εout
      hlookup harity hbody hsubset hret hclause
      ihBody ihRet ihClause =>
      intro Γ' s hs
      apply Typing.handle hlookup harity
        (ihBody Γ' s hs) hsubset
      · have hσin := (hbody.wf hsigwf).1
        exact ihRet (_ :: Γ') (liftTermSubst s)
          (hs.lift _ hσin)
      · obtain ⟨hinput, houtput⟩ := hsigwf op decl hlookup
        have hinput' : Ty.WF sig (decl.kinds ++ K) decl.input :=
          hinput.append_outer K
        have houtput' : Ty.WF sig (decl.kinds ++ K) decl.output :=
          houtput.append_outer K
        have hshift : RenValid K (decl.kinds ++ K)
            (fun i => i + arity) := by
          simpa [harity] using (RenValid.shift (K := K) decl.kinds)
        have hout := hret.wf hsigwf
        have hresult :
            Ty.WF sig (decl.kinds ++ K)
              (σout.rename (fun i => i + arity)) :=
          hout.1.rename_preserves _ hshift
        have heffect :
            Effect.WF (fun op => sig op ≠ none)
              (decl.kinds ++ K)
              (εout.rename (fun i => i + arity)) :=
          hout.2.rename_preserves hshift
        have hcont : Ty.WF sig (decl.kinds ++ K)
            (.arr decl.output
              (εout.rename (fun i => i + arity))
              (σout.rename (fun i => i + arity))) :=
          .arr houtput' heffect hresult
        have hs' := TermSubstitution.renameKind hsigwf hs
          (fun i => i + arity) hshift
        have hLift := (hs'.lift decl.input hinput').lift
          (.arr decl.output
            (εout.rename (fun i => i + arity))
            (σout.rename (fun i => i + arity))) hcont
        have hfn :
            (fun i => (s i).renameKind (fun i => i + arity)) =
              liftTermSubstKindN arity s := rfl
        rw [hfn] at hLift
        exact ihClause (_ :: _ :: Γ'.liftKind arity)
          (liftTermSubstN 2 (liftTermSubstKindN arity s))
          (by
            simpa only [liftTermSubstN_two, TermCtx.liftKind] using hLift)
  | sub _ hsub hσ hε hsubset ih =>
      intro Γ' s hs
      exact .sub (ih Γ' s hs) hsub hσ hε hsubset

/-- Γ,x:a ⊢ e : b ∣ ε と Γ ⊢ v : a ∣ ∅ から項 β 置換を得る。 -/
theorem Typing.instantiateTerm {sig : Signature}
    (hsigwf : Signature.WF sig)
    {K : List Kind} {Γ : TermCtx}
    {body value : Expr} {a b : Ty} {ε : Effect}
    (hbody : Typing sig K (a :: Γ) body b ε)
    (hΓ : TermCtx.WF sig K Γ)
    (hvalue : Typing sig K Γ value a ∅) :
    Typing sig K Γ (body.instantiate value) b ε := by
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
      exact Typing.var hget (hΓ j σ hget)

end SystemFXi.Poly
