import SystemFXi.Subtyping

/-!
# 型の改名と置換

型変数の de Bruijn 添字を変える操作は kinding と部分型を保存する。
後続の型適用と多相操作の preservation で使う。
-/

namespace SystemFXi

/-- 恒等改名は型を変えない: `id(σ) = σ`。 -/
theorem Ty.rename_id (σ : Ty) : σ.rename id = σ := by
  induction σ with
  | var _ => rfl
  | arr _ _ _ ihA ihB => simp [Ty.rename, ihA, ihB]
  | all _ ih =>
      have hlift : liftTyRen id = id := by
        funext i
        cases i <;> rfl
      simpa [Ty.rename, hlift] using congrArg Ty.all ih

/-- 型変数改名の合成は、関数の合成と一致する。 -/
theorem Ty.rename_comp (σ : Ty) :
    ∀ (ρ υ : Nat → Nat),
      (σ.rename ρ).rename υ = σ.rename (fun i => υ (ρ i)) := by
  induction σ with
  | var _ => intro _ _; rfl
  | arr _ _ _ ihA ihB =>
      intro ρ υ
      simp [Ty.rename, ihA, ihB]
  | all _ ih =>
      intro ρ υ
      have hlift :
          (fun i => liftTyRen υ (liftTyRen ρ i)) =
            liftTyRen (fun i => υ (ρ i)) := by
        funext i
        cases i <;> rfl
      simpa [Ty.rename, hlift] using
        congrArg Ty.all (ih (liftTyRen ρ) (liftTyRen υ))

/-- 恒等置換は型を変えない: `σ[α ↦ α] = σ`。 -/
theorem Ty.subst_id (σ : Ty) :
    σ.subst Ty.var = σ := by
  induction σ with
  | var _ => rfl
  | arr _ _ _ ihA ihB => simp [Ty.subst, ihA, ihB]
  | all _ ih =>
      have hlift : liftTySubst Ty.var = Ty.var := by
        funext i
        cases i <;> rfl
      simpa [Ty.subst, hlift] using congrArg Ty.all ih

/-- `σ[τ]` を改名する操作は、`τ` の各像を改名してから置換する操作と一致する。 -/
theorem Ty.subst_rename (σ : Ty) :
    ∀ (τ : Nat → Ty) (ρ : Nat → Nat),
      (σ.subst τ).rename ρ =
        σ.subst (fun i => (τ i).rename ρ) := by
  induction σ with
  | var _ => intro _ _; rfl
  | arr _ _ _ ihA ihB =>
      intro τ ρ
      simp [Ty.subst, Ty.rename, ihA, ihB]
  | all _ ih =>
      intro τ ρ
      have hlift :
          (fun i => (liftTySubst τ i).rename (liftTyRen ρ)) =
            liftTySubst (fun i => (τ i).rename ρ) := by
        funext i
        cases i with
        | zero => rfl
        | succ j =>
            simp only [liftTySubst]
            rw [Ty.rename_comp, Ty.rename_comp]
            congr 1
      simpa [Ty.subst, Ty.rename, hlift] using
        congrArg Ty.all (ih (liftTySubst τ) (liftTyRen ρ))

/-- 改名後の型置換は、置換の添字を先に改名したものと一致する。 -/
theorem Ty.rename_subst (σ : Ty) :
    ∀ (ρ : Nat → Nat) (τ : Nat → Ty),
      (σ.rename ρ).subst τ = σ.subst (fun i => τ (ρ i)) := by
  induction σ with
  | var _ => intro _ _; rfl
  | arr _ _ _ ihA ihB =>
      intro ρ τ
      simp [Ty.rename, Ty.subst, ihA, ihB]
  | all _ ih =>
      intro ρ τ
      have hlift :
          (fun i => liftTySubst τ (liftTyRen ρ i)) =
            liftTySubst (fun i => τ (ρ i)) := by
        funext i
        cases i <;> rfl
      simpa [Ty.rename, Ty.subst, hlift] using
        congrArg Ty.all (ih (liftTyRen ρ) (liftTySubst τ))

/-- 型置換を二回行うと、置換の各像を先に置換する一回の操作になる。 -/
theorem Ty.subst_subst (σ : Ty) :
    ∀ (τ υ : Nat → Ty),
      (σ.subst τ).subst υ =
        σ.subst (fun i => (τ i).subst υ) := by
  induction σ with
  | var _ => intro _ _; rfl
  | arr _ _ _ ihA ihB =>
      intro τ υ
      simp [Ty.subst, ihA, ihB]
  | all _ ih =>
      intro τ υ
      have hlift :
          (fun i => (liftTySubst τ i).subst (liftTySubst υ)) =
            liftTySubst (fun i => (τ i).subst υ) := by
        funext i
        cases i with
        | zero => rfl
        | succ j =>
            simp only [liftTySubst]
            rw [Ty.rename_subst, Ty.subst_rename]
            congr 1
      simpa [Ty.subst, hlift] using
        congrArg Ty.all (ih (liftTySubst τ) (liftTySubst υ))

/-- `Δ ⊢ σ :: T` の自由変数上で一致する二つの置換は、`σ` 上で一致する。 -/
theorem Ty.WF.subst_congr {sig : Signature} {n : Nat} {σ : Ty}
    (hwf : Ty.WF sig n σ) :
    ∀ (τ υ : Nat → Ty),
      (∀ i, i < n → τ i = υ i) → σ.subst τ = σ.subst υ := by
  induction hwf with
  | var hi =>
      intro τ υ h
      exact h _ hi
  | arr _ _ _ ihA ihB =>
      intro τ υ h
      simp only [Ty.subst, ihA τ υ h, ihB τ υ h]
  | all _ ih =>
      intro τ υ h
      simp only [Ty.subst]
      congr 1
      apply ih
      intro i hi
      cases i with
      | zero => rfl
      | succ j =>
          simp only [liftTySubst]
          rw [h j (by omega)]

/-- `ρ` が自由変数を固定すれば、`Δ ⊢ σ :: T` に対して `ρ(σ) = σ`。 -/
theorem Ty.WF.rename_eq {sig : Signature} {n : Nat} {σ : Ty}
    (hwf : Ty.WF sig n σ) :
    ∀ (ρ : Nat → Nat),
      (∀ i, i < n → ρ i = i) → σ.rename ρ = σ := by
  induction hwf with
  | var hi =>
      intro ρ h
      simp [Ty.rename, h _ hi]
  | arr _ _ _ ihA ihB =>
      intro ρ h
      simp only [Ty.rename, ihA ρ h, ihB ρ h]
  | all _ ih =>
      intro ρ h
      simp only [Ty.rename]
      congr 1
      apply ih
      intro i hi
      cases i with
      | zero => rfl
      | succ j => simp [liftTyRen, h j (by omega)]

/-- `n` 個の型束縛子の内側の添字 `i < n` は、外側の改名で変わらない。 -/
theorem liftTyRenN_fixed (n : Nat) (ρ : Nat → Nat) :
    ∀ i, i < n → liftTyRenN n ρ i = i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ j =>
          simp only [liftTyRenN, liftTyRen]
          rw [ih j (by omega)]

/-- 外側の添字 `i+n` は `ρ(i)+n` に改名される。 -/
theorem liftTyRenN_outer (n : Nat) (ρ : Nat → Nat) (i : Nat) :
    liftTyRenN n ρ (i + n) = ρ i + n := by
  induction n with
  | zero => simp [liftTyRenN]
  | succ n ih =>
      simp only [liftTyRenN]
      have h : i + (n + 1) = (i + n) + 1 := by omega
      rw [h, liftTyRen, ih]
      omega

/-- `ρ : Δ → Δ′` は `k` 個の型束縛子の下でも有効な改名になる。 -/
theorem liftTyRenN_valid {n m : Nat} (k : Nat) (ρ : Nat → Nat)
    (hρ : ∀ i, i < n → ρ i < m) :
    ∀ i, i < n + k → liftTyRenN k ρ i < m + k := by
  intro i hi
  by_cases hsmall : i < k
  · rw [liftTyRenN_fixed k ρ i hsmall]
    omega
  · have hidx : i = (i - k) + k := by omega
    rw [hidx, liftTyRenN_outer]
    have hbase : i - k < n := by omega
    have := hρ (i - k) hbase
    omega

/-- 型適用と型変数の改名は交換する。 -/
theorem Ty.instantiate_rename (body arg : Ty) (ρ : Nat → Nat) :
    (body.instantiate arg).rename ρ =
      (body.rename (liftTyRen ρ)).instantiate (arg.rename ρ) := by
  simp only [Ty.instantiate, Ty.subst_rename, Ty.rename_subst]
  congr 1
  funext i
  cases i <;> rfl

/-- 型適用と外側の型置換は交換する。 -/
theorem Ty.instantiate_subst (body arg : Ty) (τ : Nat → Ty) :
    (body.instantiate arg).subst τ =
      (body.subst (liftTySubst τ)).instantiate (arg.subst τ) := by
  simp only [Ty.instantiate, Ty.subst_subst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ j =>
      simp only [liftTySubst, Ty.subst]
      rw [Ty.rename_subst]
      simp only [Ty.subst_id]

/-- `Σ(op)` の型が `n` 個の型変数だけを使うなら、操作の型引数の
具体化は外側の型変数の改名と交換する。 -/
theorem Ty.instantiateMany_rename {sig : Signature} {n : Nat}
    {body : Ty} (hwf : Ty.WF sig n body)
    (args : List Ty) (hlen : args.length = n) (ρ : Nat → Nat) :
    (body.instantiateMany args).rename ρ =
      body.instantiateMany (args.map (Ty.rename ρ)) := by
  simp only [Ty.instantiateMany, Ty.subst_rename]
  apply hwf.subst_congr
  intro i hi
  have hidx : i < args.length := by omega
  simp [hidx]

/-- 宣言内の `n` 個の型変数に対する具体化は、外側の型置換と交換する。 -/
theorem Ty.instantiateMany_subst {sig : Signature} {n : Nat}
    {body : Ty} (hwf : Ty.WF sig n body)
    (args : List Ty) (hlen : args.length = n) (τ : Nat → Ty) :
    (body.instantiateMany args).subst τ =
      body.instantiateMany (args.map (Ty.subst τ)) := by
  simp only [Ty.instantiateMany, Ty.subst_subst]
  apply hwf.subst_congr
  intro i hi
  have hidx : i < args.length := by omega
  simp [hidx]

/-- `n` 個の型束縛子の内側の添字は、外側の型置換で変わらない。 -/
theorem liftTySubstN_fixed (n : Nat) (τ : Nat → Ty) :
    ∀ i, i < n → liftTySubstN n τ i = .var i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ j =>
          simp only [liftTySubstN, liftTySubst]
          rw [ih j (by omega)]
          rfl

/-- `i+n` 番目の外側の型変数は、置換像を `n` 個持ち上げた型になる。 -/
theorem liftTySubstN_outer (n : Nat) (τ : Nat → Ty) (i : Nat) :
    liftTySubstN n τ (i + n) =
      (τ i).rename (fun j => j + n) := by
  induction n with
  | zero =>
      simp only [liftTySubstN, Nat.add_zero]
      change τ i = (τ i).rename id
      exact (Ty.rename_id (τ i)).symm
  | succ n ih =>
      have h : i + (n + 1) = (i + n) + 1 := by omega
      rw [h, liftTySubstN, liftTySubst, ih, Ty.rename_comp]
      congr 1

/-- `σ↑ⁿ` への外側の型置換は、先に `σ` を置換してから持ち上げる操作。 -/
theorem Ty.shift_subst (σ : Ty) (n : Nat) (τ : Nat → Ty) :
    (σ.rename (fun i => i + n)).subst (liftTySubstN n τ) =
      (σ.subst τ).rename (fun i => i + n) := by
  rw [Ty.rename_subst, Ty.subst_rename]
  congr 1
  funext i
  exact liftTySubstN_outer n τ i

/-- `Γ↑ⁿ` に外側の型置換を行う順序を交換できる。 -/
theorem TermCtx.liftTy_subst (Γ : TermCtx) (n : Nat) (τ : Nat → Ty) :
    (Γ.liftTy n).map (Ty.subst (liftTySubstN n τ)) =
      TermCtx.liftTy n (Γ.map (Ty.subst τ)) := by
  simp only [TermCtx.liftTy, List.map_map]
  apply List.map_congr_left
  intro σ hσ
  change (σ.rename (fun i => i + n)).subst (liftTySubstN n τ) =
    (σ.subst τ).rename (fun i => i + n)
  exact σ.shift_subst n τ

/-- `ρ` が `Δ` の変数を `Δ′` の変数へ送れば、`Δ ⊢ σ :: T` から
`Δ′ ⊢ ρ(σ) :: T` が得られる。 -/
theorem Ty.WF.rename_preserves {sig : Signature} {n : Nat} {σ : Ty}
    (h : Ty.WF sig n σ) :
    ∀ {m : Nat} (ρ : Nat → Nat),
      (∀ i, i < n → ρ i < m) → Ty.WF sig m (σ.rename ρ) := by
  induction h with
  | var hi =>
      intro m ρ hρ
      exact .var (hρ _ hi)
  | arr _ hε _ ihA ihB =>
      intro m ρ hρ
      exact .arr (ihA ρ hρ) hε (ihB ρ hρ)
  | all _ ih =>
      intro m ρ hρ
      apply Ty.WF.all
      apply ih (liftTyRen ρ)
      intro i hi
      cases i with
      | zero => simp [liftTyRen]
      | succ j =>
          simpa only [liftTyRen] using Nat.succ_lt_succ (hρ j (by omega))

/-- 整形式な型置換は `k` 個の型束縛子の下でも整形式である。 -/
theorem liftTySubstN_valid {sig : Signature} {n m : Nat}
    (k : Nat) (τ : Nat → Ty)
    (hτ : ∀ i, i < n → Ty.WF sig m (τ i)) :
    ∀ i, i < n + k → Ty.WF sig (m + k) (liftTySubstN k τ i) := by
  intro i hi
  by_cases hsmall : i < k
  · rw [liftTySubstN_fixed k τ i hsmall]
    exact .var (by omega)
  · have hidx : i = (i - k) + k := by omega
    rw [hidx, liftTySubstN_outer]
    have hbase : i - k < n := by omega
    exact (hτ (i - k) hbase).rename_preserves
      (fun j => j + k) (by intro j hj; omega)

/-- `τ` の各像が整形式なら、`Δ ⊢ σ :: T` から
`Δ′ ⊢ σ[τ] :: T` が得られる。 -/
theorem Ty.WF.subst_preserves {sig : Signature} {n : Nat} {σ : Ty}
    (h : Ty.WF sig n σ) :
    ∀ {m : Nat} (τ : Nat → Ty),
      (∀ i, i < n → Ty.WF sig m (τ i)) →
      Ty.WF sig m (σ.subst τ) := by
  induction h with
  | var hi =>
      intro m τ hτ
      exact hτ _ hi
  | arr _ hε _ ihA ihB =>
      intro m τ hτ
      exact .arr (ihA τ hτ) hε (ihB τ hτ)
  | all _ ih =>
      intro m τ hτ
      apply Ty.WF.all
      apply ih (liftTySubst τ)
      intro i hi
      cases i with
      | zero => exact .var (by omega)
      | succ j =>
          exact (hτ j (by omega)).rename_preserves Nat.succ
            (by intro k hk; omega)

/-- `Δ ⊢ σ₁ <: σ₂` は整形式の型置換後も成立する。 -/
theorem Subtype.subst_preserves {sig : Signature} {n : Nat}
    {a b : Ty} (h : Subtype sig n a b) :
    ∀ {m : Nat} (τ : Nat → Ty),
      (∀ i, i < n → Ty.WF sig m (τ i)) →
      Subtype sig m (a.subst τ) (b.subst τ) := by
  induction h with
  | var =>
      intro m τ hτ
      exact Subtype.refl _ m
  | arr hA hε hB ihA ihB =>
      intro m τ hτ
      exact .arr (ihA τ hτ) hε (ihB τ hτ)
  | all hBody ih =>
      intro m τ hτ
      apply Subtype.all
      apply ih (liftTySubst τ)
      intro i hi
      cases i with
      | zero => exact .var (by omega)
      | succ j =>
          exact (hτ j (by omega)).rename_preserves Nat.succ
            (by intro k hk; omega)

/-- `Δ ⊢ σ₁ <: σ₂` は型変数の整形式な改名で保存される。 -/
theorem Subtype.rename_preserves {sig : Signature} {n : Nat}
    {a b : Ty} (h : Subtype sig n a b) :
    ∀ {m : Nat} (ρ : Nat → Nat),
      (∀ i, i < n → ρ i < m) →
      Subtype sig m (a.rename ρ) (b.rename ρ) := by
  induction h with
  | var =>
      intro m ρ hρ
      exact .var
  | arr _ hε _ ihA ihB =>
      intro m ρ hρ
      exact .arr (ihA ρ hρ) hε (ihB ρ hρ)
  | all _ ih =>
      intro m ρ hρ
      apply Subtype.all
      apply ih (liftTyRen ρ)
      intro i hi
      cases i with
      | zero => simp [liftTyRen]
      | succ j =>
          simpa only [liftTyRen] using Nat.succ_lt_succ (hρ j (by omega))

/-- `Γ↑ⁿ` を外側で改名した結果は、先に `Γ` を改名してから持ち上げた結果。 -/
theorem TermCtx.liftTy_rename (Γ : TermCtx) (k : Nat)
    (ρ : Nat → Nat) :
    (Γ.liftTy k).map (Ty.rename (liftTyRenN k ρ)) =
      TermCtx.liftTy k (Γ.map (Ty.rename ρ)) := by
  simp only [TermCtx.liftTy, List.map_map]
  apply List.map_congr_left
  intro σ hσ
  change ((σ.rename (fun i => i + k)).rename (liftTyRenN k ρ)) =
    ((σ.rename ρ).rename (fun i => i + k))
  rw [Ty.rename_comp, Ty.rename_comp]
  congr 1
  funext i
  exact liftTyRenN_outer k ρ i

/-- `Δ ∣ Γ ⊢ e : σ ∣ ε` は、型変数の整形式な改名 `ρ` の下で
`Δ′ ∣ ρ(Γ) ⊢ ρ(e) : ρ(σ) ∣ ε` を満たす。 -/
theorem Typing.renameTy_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat} {Γ : TermCtx}
    {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ e σ ε) :
    ∀ {m : Nat} (ρ : Nat → Nat),
      (∀ i, i < n → ρ i < m) →
      Typing sig m (Γ.map (Ty.rename ρ))
        (e.renameTy ρ) (σ.rename ρ) ε := by
  induction ht with
  | var hlookup =>
      intro m ρ hρ
      apply Typing.var
      simp [List.getElem?_map, hlookup]
  | lam hwf _ ih =>
      intro m ρ hρ
      exact .lam (hwf.rename_preserves ρ hρ) (ih ρ hρ)
  | app _ _ ihF ihX =>
      intro m ρ hρ
      exact .app (ihF ρ hρ) (ihX ρ hρ)
  | @tlam n Γ body σ _ ih =>
      intro m ρ hρ
      have hbody := ih (m := m + 1) (liftTyRen ρ)
        (by
          intro i hi
          cases i with
          | zero => simp [liftTyRen]
          | succ j =>
              simpa only [liftTyRen] using Nat.succ_lt_succ (hρ j (by omega)))
      have hbody' : Typing sig (m + 1)
          (TermCtx.liftTy 1 (Γ.map (Ty.rename ρ)))
          (body.renameTy (liftTyRen ρ))
          (σ.rename (liftTyRen ρ)) ∅ := by
        have hctx :
            (Γ.liftTy 1).map (Ty.rename (liftTyRen ρ)) =
              TermCtx.liftTy 1 (Γ.map (Ty.rename ρ)) := by
          simpa only [liftTyRenN] using TermCtx.liftTy_rename Γ 1 ρ
        simpa only [hctx] using hbody
      exact Typing.tlam hbody'
  | tapp _ hwf ih =>
      intro m ρ hρ
      have hterm := ih ρ hρ
      have harg := hwf.rename_preserves ρ hρ
      simpa only [Expr.renameTy, Ty.instantiate_rename] using
        (Typing.tapp hterm harg)
  | @perform n Γ op decl args arg εarg hlookup hlen hargs _ ih =>
      intro m ρ hρ
      obtain ⟨hinput, houtput⟩ := hsigwf op decl hlookup
      have hterm := ih ρ hρ
      have hargs' : ∀ a ∈ args.map (Ty.rename ρ), Ty.WF sig m a := by
        intro a ha
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp ha
        exact (hargs old hold).rename_preserves ρ hρ
      rw [Ty.instantiateMany_rename hinput args hlen ρ] at hterm
      have hperform := Typing.perform hlookup
        (by simpa using hlen) hargs'
        hterm
      simpa only [Expr.renameTy,
        Ty.instantiateMany_rename houtput args hlen ρ] using hperform
  | @handle n Γ body op arity ret clause decl σin σout εin εout
      hlookup harity _ hε _ _ ihBody ihRet ihClause =>
      intro m ρ hρ
      obtain ⟨hinput, houtput⟩ := hsigwf op decl hlookup
      have hbody := ihBody ρ hρ
      have hret := ihRet ρ hρ
      have hclause := ihClause (liftTyRenN arity ρ)
        (by
          intro i hi
          apply liftTyRenN_valid arity ρ hρ
          simpa [Nat.add_comm] using hi)
      have hinputEq :
          decl.input.rename (liftTyRenN arity ρ) = decl.input := by
        apply hinput.rename_eq
        intro i hi
        exact liftTyRenN_fixed arity ρ i (by simpa [harity] using hi)
      have houtputEq :
          decl.output.rename (liftTyRenN arity ρ) = decl.output := by
        apply houtput.rename_eq
        intro i hi
        exact liftTyRenN_fixed arity ρ i (by simpa [harity] using hi)
      have hresultEq :
          (σout.rename (fun i => i + arity)).rename (liftTyRenN arity ρ) =
            (σout.rename ρ).rename (fun i => i + arity) := by
        rw [Ty.rename_comp, Ty.rename_comp]
        congr 1
        funext i
        exact liftTyRenN_outer arity ρ i
      have hclause' : Typing sig (m + arity)
          ((.arr decl.output εout
              ((σout.rename ρ).rename (fun i => i + arity))) ::
            decl.input :: TermCtx.liftTy arity (Γ.map (Ty.rename ρ)))
          (clause.renameTy (liftTyRenN arity ρ))
          ((σout.rename ρ).rename (fun i => i + arity)) εout := by
        simpa only [List.map_cons, Ty.rename, hinputEq, houtputEq,
          hresultEq, TermCtx.liftTy_rename] using hclause
      exact .handle hlookup harity hbody hε hret hclause'
  | sub _ hs hε ih =>
      intro m ρ hρ
      exact .sub (ih ρ hρ) (hs.rename_preserves ρ hρ) hε

/-- `Δ ∣ Γ ⊢ e : σ ∣ ε` は整形式な型置換 `τ` の下で
`Δ′ ∣ Γ[τ] ⊢ e[τ] : σ[τ] ∣ ε` を満たす。 -/
theorem Typing.substTy_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat} {Γ : TermCtx}
    {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ e σ ε) :
    ∀ {m : Nat} (τ : Nat → Ty),
      (∀ i, i < n → Ty.WF sig m (τ i)) →
      Typing sig m (Γ.map (Ty.subst τ))
        (e.substTy τ) (σ.subst τ) ε := by
  induction ht with
  | var hlookup =>
      intro m τ hτ
      apply Typing.var
      simp [List.getElem?_map, hlookup]
  | lam hwf _ ih =>
      intro m τ hτ
      exact .lam (hwf.subst_preserves τ hτ) (ih τ hτ)
  | app _ _ ihF ihX =>
      intro m τ hτ
      exact .app (ihF τ hτ) (ihX τ hτ)
  | @tlam n Γ body σ _ ih =>
      intro m τ hτ
      have hbody := ih (m := m + 1) (liftTySubst τ)
        (by
          intro i hi
          apply liftTySubstN_valid (k := 1) τ hτ
          simpa [Nat.add_comm] using hi)
      have hctx :
          (Γ.liftTy 1).map (Ty.subst (liftTySubst τ)) =
            TermCtx.liftTy 1 (Γ.map (Ty.subst τ)) := by
        simpa only [liftTySubstN] using TermCtx.liftTy_subst Γ 1 τ
      have hbody' : Typing sig (m + 1)
          (TermCtx.liftTy 1 (Γ.map (Ty.subst τ)))
          (body.substTy (liftTySubst τ))
          (σ.subst (liftTySubst τ)) ∅ := by
        simpa only [hctx] using hbody
      exact Typing.tlam hbody'
  | tapp _ hwf ih =>
      intro m τ hτ
      have hterm := ih τ hτ
      have harg := hwf.subst_preserves τ hτ
      simpa only [Expr.substTy, Ty.instantiate_subst] using
        (Typing.tapp hterm harg)
  | @perform n Γ op decl args arg εarg hlookup hlen hargs _ ih =>
      intro m τ hτ
      obtain ⟨hinput, houtput⟩ := hsigwf op decl hlookup
      have hterm := ih τ hτ
      have hargs' : ∀ a ∈ args.map (Ty.subst τ), Ty.WF sig m a := by
        intro a ha
        obtain ⟨old, hold, rfl⟩ := List.mem_map.mp ha
        exact (hargs old hold).subst_preserves τ hτ
      rw [Ty.instantiateMany_subst hinput args hlen τ] at hterm
      have hperform := Typing.perform hlookup
        (by simpa using hlen) hargs' hterm
      simpa only [Expr.substTy,
        Ty.instantiateMany_subst houtput args hlen τ] using hperform
  | @handle n Γ body op arity ret clause decl σin σout εin εout
      hlookup harity _ hε _ _ ihBody ihRet ihClause =>
      intro m τ hτ
      obtain ⟨hinput, houtput⟩ := hsigwf op decl hlookup
      have hbody := ihBody τ hτ
      have hret := ihRet τ hτ
      have hclause := ihClause (m := m + arity)
        (liftTySubstN arity τ)
        (by
          intro i hi
          apply liftTySubstN_valid arity τ hτ
          simpa [Nat.add_comm] using hi)
      have hinputEq :
          decl.input.subst (liftTySubstN arity τ) = decl.input := by
        calc
          _ = decl.input.subst Ty.var :=
            hinput.subst_congr _ _ (by
              intro i hi
              exact liftTySubstN_fixed arity τ i (by simpa [harity] using hi))
          _ = decl.input := Ty.subst_id _
      have houtputEq :
          decl.output.subst (liftTySubstN arity τ) = decl.output := by
        calc
          _ = decl.output.subst Ty.var :=
            houtput.subst_congr _ _ (by
              intro i hi
              exact liftTySubstN_fixed arity τ i (by simpa [harity] using hi))
          _ = decl.output := Ty.subst_id _
      have hresultEq :
          (σout.rename (fun i => i + arity)).subst
            (liftTySubstN arity τ) =
          (σout.subst τ).rename (fun i => i + arity) :=
        σout.shift_subst arity τ
      have hclause' : Typing sig (m + arity)
          ((.arr decl.output εout
              ((σout.subst τ).rename (fun i => i + arity))) ::
            decl.input :: TermCtx.liftTy arity (Γ.map (Ty.subst τ)))
          (clause.substTy (liftTySubstN arity τ))
          ((σout.subst τ).rename (fun i => i + arity)) εout := by
        simpa only [List.map_cons, Ty.subst, hinputEq, houtputEq,
          hresultEq, TermCtx.liftTy_subst] using hclause
      exact .handle hlookup harity hbody hε hret hclause'
  | sub _ hs hε ih =>
      intro m τ hτ
      exact .sub (ih τ hτ) (hs.subst_preserves τ hτ) hε

/-- `Δ,α ∣ Γ↑ ⊢ e : σ ∣ ε` と `Δ ⊢ τ :: T` から
`Δ ∣ Γ ⊢ e[α ↦ τ] : σ[α ↦ τ] ∣ ε` を得る。 -/
theorem Typing.instantiateTy {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat} {Γ : TermCtx}
    {body : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig (n + 1) (Γ.liftTy 1) body σ ε)
    {arg : Ty} (harg : Ty.WF sig n arg) :
    Typing sig n Γ
      (body.substTy (fun | 0 => arg | i + 1 => .var i))
      (σ.instantiate arg) ε := by
  let τ : Nat → Ty := fun | 0 => arg | i + 1 => .var i
  have hτ : ∀ i, i < n + 1 → Ty.WF sig n (τ i) := by
    intro i hi
    cases i with
    | zero => exact harg
    | succ j => exact .var (by omega)
  have htyped := ht.substTy_preserves hsigwf τ hτ
  have hctx : (Γ.liftTy 1).map (Ty.subst τ) = Γ := by
    simp only [TermCtx.liftTy, List.map_map]
    have hfn :
        Ty.subst τ ∘ Ty.rename (fun i => i + 1) = id := by
      funext a
      change (a.rename (fun i => i + 1)).subst τ = a
      rw [Ty.rename_subst]
      have hmap : (fun i => τ (i + 1)) = Ty.var := by
        funext i
        rfl
      rw [hmap, Ty.subst_id]
    rw [hfn]
    simp
  rw [hctx] at htyped
  change Typing sig n Γ (body.substTy τ) (σ.subst τ) ε
  exact htyped

/-- `k` 個の束縛子を越えて持ち上げた型を、`k` 個の型引数で具体化すると
元の型へ戻る。 -/
theorem Ty.shift_instantiateMany (σ : Ty) (k : Nat)
    (args : List Ty) (hlen : args.length = k) :
    (σ.rename (fun i => i + k)).subst
      (fun i => (args[i]?).getD (.var (i - args.length))) = σ := by
  rw [Ty.rename_subst]
  have hmap :
      (fun i => (args[i + k]?).getD (.var (i + k - args.length))) =
        Ty.var := by
    funext i
    have hnot : ¬i + k < args.length := by omega
    simp [hlen]
  rw [hmap, Ty.subst_id]

/-- `Γ↑ᵏ` の型変数を具体化すると `Γ` に戻る。 -/
theorem TermCtx.liftTy_instantiateMany (Γ : TermCtx) (k : Nat)
    (args : List Ty) (hlen : args.length = k) :
    (Γ.liftTy k).map
      (Ty.subst (fun i => (args[i]?).getD (.var (i - args.length)))) = Γ := by
  simp only [TermCtx.liftTy, List.map_map]
  have hfn :
      Ty.subst (fun i => (args[i]?).getD (.var (i - args.length))) ∘
          Ty.rename (fun i => i + k) = id := by
    funext σ
    exact Ty.shift_instantiateMany σ k args hlen
  rw [hfn]
  simp

/-- 多相操作節の型変数 `ᾱ` を型引数 `τ̄` で具体化しても型付けを保つ。 -/
theorem Typing.instantiateManyTy {sig : Signature}
    (hsigwf : Signature.WF sig) {n k : Nat} {Γ : TermCtx}
    {body : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig (n + k) Γ body σ ε)
    (args : List Ty) (hlen : args.length = k)
    (hargs : ∀ a ∈ args, Ty.WF sig n a) :
    Typing sig n
      (Γ.map (Ty.subst
        (fun i => (args[i]?).getD (.var (i - args.length)))))
      (body.instantiateManyTy args)
      (σ.subst (fun i => (args[i]?).getD (.var (i - args.length)))) ε := by
  let τ : Nat → Ty := fun i => (args[i]?).getD (.var (i - args.length))
  have hτ : ∀ i, i < n + k → Ty.WF sig n (τ i) := by
    intro i hi
    by_cases hidx : i < args.length
    · have hmem : args[i] ∈ args := List.getElem_mem hidx
      simpa [τ, hidx] using hargs args[i] hmem
    · have hnone : args[i]? = none := by simp [hidx]
      simp [τ, hnone]
      exact .var (by omega)
  have htyped := ht.substTy_preserves hsigwf τ hτ
  change Typing sig n (Γ.map (Ty.subst τ))
    (body.instantiateManyTy args) (σ.subst τ) ε
  exact htyped

/-- 型引数 `τ̄` を操作節に代入すると、操作の引数型と結果型が具体化され、
外側の環境 `Γ` は元の形に戻る。 -/
theorem Typing.instantiateOpClause {sig : Signature}
    (hsigwf : Signature.WF sig) {n k : Nat} {Γ : TermCtx}
    {clause : Expr} {decl : OpDecl} {σout : Ty} {εout : Effect}
    (ht : Typing sig (n + k)
      ((.arr decl.output εout (σout.rename (fun i => i + k))) ::
        decl.input :: Γ.liftTy k)
      clause (σout.rename (fun i => i + k)) εout)
    (args : List Ty) (hlen : args.length = k)
    (hargs : ∀ a ∈ args, Ty.WF sig n a) :
    Typing sig n
      ((.arr (decl.output.instantiateMany args) εout σout) ::
        (decl.input.instantiateMany args) :: Γ)
      (clause.instantiateManyTy args) σout εout := by
  let τ : Nat → Ty := fun i => (args[i]?).getD (.var (i - args.length))
  have htyped := ht.instantiateManyTy hsigwf args hlen hargs
  have hctx :
      (((.arr decl.output εout (σout.rename (fun i => i + k))) ::
          decl.input :: Γ.liftTy k).map (Ty.subst τ)) =
        ((.arr (decl.output.instantiateMany args) εout σout) ::
          (decl.input.instantiateMany args) :: Γ) := by
    simp only [List.map_cons, Ty.subst]
    rw [Ty.shift_instantiateMany σout k args hlen]
    rw [TermCtx.liftTy_instantiateMany Γ k args hlen]
    rfl
  have hresult :
      (σout.rename (fun i => i + k)).subst τ = σout :=
    σout.shift_instantiateMany k args hlen
  rw [hctx, hresult] at htyped
  exact htyped

end SystemFXi
