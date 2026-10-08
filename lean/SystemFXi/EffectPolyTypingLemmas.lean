import SystemFXi.EffectPolyTypeLemmas

/-!
# 効果多相な型付けの構造補題

型・効果変数を同時に改名または置換したとき、型付け判定の
結果型と評価効果の双方に同じ操作が作用する。
-/

namespace SystemFXi.Poly

/-- Δ ∣ Γ ⊢ e : σ ∣ ε は kind を保つ改名 ρ で保存される。 -/
theorem Typing.renameKind_preserves {sig : Signature}
    (hsigwf : Signature.WF sig)
    {Δ : List Kind} {Γ : TermCtx}
    {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig Δ Γ e σ ε) :
    ∀ {Δ' : List Kind} (ρ : Nat → Nat),
      RenValid Δ Δ' ρ →
      Typing sig Δ' (Γ.map (Ty.rename ρ))
        (e.renameKind ρ) (σ.rename ρ) (ε.rename ρ) := by
  induction ht with
  | var hlookup hwf =>
      intro Δ' ρ hρ
      apply Typing.var
      · simpa using congrArg (Option.map (Ty.rename ρ)) hlookup
      · exact hwf.rename_preserves ρ hρ
  | lam hwf _ ih =>
      intro Δ' ρ hρ
      exact .lam (hwf.rename_preserves ρ hρ) (ih ρ hρ)
  | app _ _ ihF ihX =>
      intro Δ' ρ hρ
      have hterm := Typing.app (ihF ρ hρ) (ihX ρ hρ)
      simpa only [Expr.renameKind, Ty.rename,
        Effect.rename_union] using hterm
  | @tlam Δ Γ κ body σ _ ih =>
      intro Δ' ρ hρ
      have hbody := ih (liftRen ρ) (liftRen_valid hρ κ)
      have hctx :
          (Γ.liftKind 1).map (Ty.rename (liftRen ρ)) =
            TermCtx.liftKind (Γ.map (Ty.rename ρ)) 1 := by
        simpa only [liftRenN] using TermCtx.liftKind_rename Γ 1 ρ
      have hbody' : Typing sig (κ :: Δ')
          (TermCtx.liftKind (Γ.map (Ty.rename ρ)) 1)
          (body.renameKind (liftRen ρ))
          (σ.rename (liftRen ρ)) ∅ := by
        have hempty :
            (∅ : Effect).rename (liftRen ρ) = ∅ := by
          change Effect.mk ∅ ∅ = Effect.mk ∅ ∅
          rfl
        simpa only [hctx, hempty] using hbody
      exact Typing.tlam hbody'
  | @tapp Δ Γ fn κ body ε arg hfun harg ih =>
      intro Δ' ρ hρ
      have hbody : Ty.WF sig (κ :: Δ) body := by
        have hty := (hfun.wf hsigwf).1
        cases hty with
        | all h => exact h
      have hterm := Typing.tapp (ih ρ hρ)
        (harg.rename_preserves ρ hρ)
      simpa only [Expr.renameKind,
        Ty.instantiate_rename hbody harg ρ] using hterm
  | @perform Δ Γ op decl args arg εarg hlookup hargs _ ih =>
      intro Δ' ρ hρ
      obtain ⟨hinput, houtput⟩ := hsigwf op decl hlookup
      have hargs' := Arg.WF.renameMany hargs ρ hρ
      have hterm := ih ρ hρ
      rw [Ty.instantiateMany_rename hinput hargs ρ] at hterm
      have hperform := Typing.perform hlookup hargs' hterm
      have hEffEq :
          (Effect.singleton op ∪ εarg).rename ρ =
            Effect.singleton op ∪ εarg.rename ρ := by
        rw [Effect.rename_union]
        have hsingle :
            (Effect.singleton op).rename ρ = Effect.singleton op := by
          simp [Effect.rename, Effect.singleton]
        rw [hsingle]
      simpa only [Expr.renameKind,
        Ty.instantiateMany_rename houtput hargs ρ,
        hEffEq] using hperform
  | @handle Δ Γ body op arity ret clause decl σin σout εin εout
      hlookup harity _ hsubset _ _ ihBody ihRet ihClause =>
      intro Δ' ρ hρ
      obtain ⟨hinput, houtput⟩ := hsigwf op decl hlookup
      have hbody := ihBody ρ hρ
      have hret := ihRet ρ hρ
      have hρ' : RenValid (decl.kinds ++ Δ) (decl.kinds ++ Δ')
          (liftRenN arity ρ) := by
        simpa [harity] using liftRenN_valid hρ decl.kinds
      have hclause := ihClause (liftRenN arity ρ) hρ'
      have hfix : RenFix decl.kinds (liftRenN arity ρ) := by
        simpa [harity] using liftRenN_fix decl.kinds ρ
      have hinputEq :
          decl.input.rename (liftRenN arity ρ) = decl.input :=
        hinput.rename_eq _ hfix
      have houtputEq :
          decl.output.rename (liftRenN arity ρ) = decl.output :=
        houtput.rename_eq _ hfix
      have hresultEq :
          (σout.rename (fun i => i + arity)).rename
              (liftRenN arity ρ) =
            (σout.rename ρ).rename (fun i => i + arity) := by
        rw [Ty.rename_comp, Ty.rename_comp]
        congr 1
        funext i
        exact liftRenN_outer arity ρ i
      have heffectEq :
          (εout.rename (fun i => i + arity)).rename
              (liftRenN arity ρ) =
            (εout.rename ρ).rename (fun i => i + arity) := by
        rw [Effect.rename_comp, Effect.rename_comp]
        congr 1
        funext i
        exact liftRenN_outer arity ρ i
      have hclause' : Typing sig (decl.kinds ++ Δ')
          ((.arr decl.output
            ((εout.rename ρ).rename (fun i => i + arity))
            ((σout.rename ρ).rename (fun i => i + arity))) ::
            decl.input ::
            TermCtx.liftKind (Γ.map (Ty.rename ρ)) arity)
          (clause.renameKind (liftRenN arity ρ))
          ((σout.rename ρ).rename (fun i => i + arity))
          ((εout.rename ρ).rename (fun i => i + arity)) := by
        simpa only [List.map_cons, Ty.rename, hinputEq, houtputEq,
          hresultEq, heffectEq, TermCtx.liftKind_rename] using hclause
      have hsubset' :
          εin.rename ρ ⊆ Effect.singleton op ∪ εout.rename ρ := by
        have hsingle :
            (Effect.singleton op).rename ρ = Effect.singleton op := by
          simp [Effect.rename, Effect.singleton]
        simpa only [Effect.rename_union, hsingle] using hsubset.rename ρ
      exact .handle hlookup harity hbody hsubset' hret hclause'
  | sub _ hs hσ hε hsubset ih =>
      intro Δ' ρ hρ
      exact .sub (ih ρ hρ) (hs.rename_preserves ρ hρ)
        (hσ.rename_preserves ρ hρ)
        (hε.rename_preserves hρ)
        (hsubset.rename ρ)

/-- Δ ∣ Γ ⊢ e : σ ∣ ε は kind を保つ同時置換 τ で保存される。 -/
theorem Typing.substKind_preserves {sig : Signature}
    (hsigwf : Signature.WF sig)
    {Δ : List Kind} {Γ : TermCtx}
    {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig Δ Γ e σ ε) :
    ∀ {Δ' : List Kind} (τ : KindSubst),
      SubstValid sig Δ Δ' τ →
      Typing sig Δ' (Γ.map (Ty.subst τ))
        (e.substKind τ) (σ.subst τ) (ε.substKind τ) := by
  induction ht with
  | var hlookup hwf =>
      intro Δ' τ hτ
      apply Typing.var
      · simpa using congrArg (Option.map (Ty.subst τ)) hlookup
      · exact hwf.subst_preserves τ hτ
  | lam hwf _ ih =>
      intro Δ' τ hτ
      exact .lam (hwf.subst_preserves τ hτ) (ih τ hτ)
  | app _ _ ihF ihX =>
      intro Δ' τ hτ
      have hterm := Typing.app (ihF τ hτ) (ihX τ hτ)
      simpa only [Expr.substKind, Ty.subst, Effect.substKind,
        Effect.subst_union] using hterm
  | @tlam Δ Γ κ body σ _ ih =>
      intro Δ' τ hτ
      have hbody := ih τ.lift (KindSubst.lift_valid hτ κ)
      have hctx :
          (Γ.liftKind 1).map (Ty.subst τ.lift) =
            TermCtx.liftKind (Γ.map (Ty.subst τ)) 1 := by
        simpa only [KindSubst.liftN] using
          TermCtx.liftKind_subst Γ 1 τ
      have hempty :
          (∅ : Effect).substKind τ.lift = ∅ := by
        change Effect.mk ∅ ∅ = Effect.mk ∅ ∅
        rfl
      have hbody' : Typing sig (κ :: Δ')
          (TermCtx.liftKind (Γ.map (Ty.subst τ)) 1)
          (body.substKind τ.lift) (σ.subst τ.lift) ∅ := by
        simpa only [hctx, hempty] using hbody
      exact Typing.tlam hbody'
  | @tapp Δ Γ fn κ body ε arg hfun harg ih =>
      intro Δ' τ hτ
      have hbody : Ty.WF sig (κ :: Δ) body := by
        have hty := (hfun.wf hsigwf).1
        cases hty with
        | all h => exact h
      have hterm := Typing.tapp (ih τ hτ)
        (harg.subst_preserves τ hτ)
      simpa only [Expr.substKind,
        Ty.instantiate_subst hbody harg τ] using hterm
  | @perform Δ Γ op decl args arg εarg hlookup hargs _ ih =>
      intro Δ' τ hτ
      obtain ⟨hinput, houtput⟩ := hsigwf op decl hlookup
      have hargs' := Arg.WF.substMany hargs τ hτ
      have hterm := ih τ hτ
      rw [Ty.instantiateMany_subst hinput hargs τ] at hterm
      have hperform := Typing.perform hlookup hargs' hterm
      have hEffEq :
          (Effect.singleton op ∪ εarg).substKind τ =
            Effect.singleton op ∪ εarg.substKind τ := by
        unfold Effect.substKind
        rw [Effect.subst_union]
        have hsingle :
            (Effect.singleton op).subst τ.effects =
              Effect.singleton op := by
          simp [Effect.subst, Effect.singleton]
        rw [hsingle]
      simpa only [Expr.substKind,
        Ty.instantiateMany_subst houtput hargs τ,
        hEffEq] using hperform
  | @handle Δ Γ body op arity ret clause decl σin σout εin εout
      hlookup harity _ hsubset _ _ ihBody ihRet ihClause =>
      intro Δ' τ hτ
      obtain ⟨hinput, houtput⟩ := hsigwf op decl hlookup
      have hbody := ihBody τ hτ
      have hret := ihRet τ hτ
      have hτ' : SubstValid sig (decl.kinds ++ Δ) (decl.kinds ++ Δ')
          (τ.liftN arity) := by
        simpa [harity] using KindSubst.liftN_valid hτ decl.kinds
      have hclause := ihClause (τ.liftN arity) hτ'
      have hagree : SubstAgree decl.kinds (τ.liftN arity)
          KindSubst.identity := by
        constructor
        · intro i hi
          have hidx := (List.getElem?_eq_some_iff.mp hi).choose
          exact (τ.liftN_fixed arity i (by simpa [harity] using hidx)).1
        · intro i hi
          have hidx := (List.getElem?_eq_some_iff.mp hi).choose
          exact (τ.liftN_fixed arity i (by simpa [harity] using hidx)).2
      have hinputEq :
          decl.input.subst (τ.liftN arity) = decl.input := by
        calc
          _ = decl.input.subst KindSubst.identity :=
            hinput.subst_congr _ _ hagree
          _ = decl.input := Ty.subst_id _
      have houtputEq :
          decl.output.subst (τ.liftN arity) = decl.output := by
        calc
          _ = decl.output.subst KindSubst.identity :=
            houtput.subst_congr _ _ hagree
          _ = decl.output := Ty.subst_id _
      have hresultEq :
          (σout.rename (fun i => i + arity)).subst (τ.liftN arity) =
            (σout.subst τ).rename (fun i => i + arity) :=
        σout.shift_substN arity τ
      have heffectEq :
          (εout.rename (fun i => i + arity)).subst
              (τ.liftN arity).effects =
            (εout.subst τ.effects).rename (fun i => i + arity) :=
        εout.shift_substN arity τ
      have hclause' : Typing sig (decl.kinds ++ Δ')
          ((.arr decl.output
            ((εout.subst τ.effects).rename (fun i => i + arity))
            ((σout.subst τ).rename (fun i => i + arity))) ::
            decl.input ::
            TermCtx.liftKind (Γ.map (Ty.subst τ)) arity)
          (clause.substKind (τ.liftN arity))
          ((σout.subst τ).rename (fun i => i + arity))
          ((εout.subst τ.effects).rename (fun i => i + arity)) := by
        simpa only [List.map_cons, Ty.subst, Effect.substKind,
          hinputEq, houtputEq, hresultEq, heffectEq,
          TermCtx.liftKind_subst] using hclause
      have hsubset' :
          εin.subst τ.effects ⊆
            Effect.singleton op ∪ εout.subst τ.effects := by
        have hsingle :
            (Effect.singleton op).subst τ.effects =
              Effect.singleton op := by
          simp [Effect.subst, Effect.singleton]
        simpa only [Effect.subst_union, hsingle] using
          hsubset.subst τ.effects
      exact .handle hlookup harity hbody hsubset' hret hclause'
  | sub _ hs hσ hε hsubset ih =>
      intro Δ' τ hτ
      exact .sub (ih τ hτ) (hs.subst_preserves τ hτ)
        (hσ.subst_preserves τ hτ)
        (hε.subst_preserves hτ)
        (hsubset.subst τ.effects)

/-- ∀β::κ の本体に kind の一致する引数 θ を代入しても型付けを保つ。 -/
theorem Typing.instantiateKind {sig : Signature}
    (hsigwf : Signature.WF sig)
    {Δ : List Kind} {Γ : TermCtx} {κ : Kind}
    {body : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig (κ :: Δ) (Γ.liftKind 1) body σ ε)
    {arg : Arg} (harg : Arg.WF sig Δ κ arg) :
    Typing sig Δ Γ
      (body.substKind (KindSubst.single arg))
      (σ.instantiate arg)
      (ε.substKind (KindSubst.single arg)) := by
  have htyped := ht.substKind_preserves hsigwf
    (KindSubst.single arg) (KindSubst.single_valid harg)
  have hctx :
      (Γ.liftKind 1).map
        (Ty.subst (KindSubst.single arg)) = Γ := by
    simp only [TermCtx.liftKind, List.map_map]
    have hfn :
        Ty.subst (KindSubst.single arg) ∘
            Ty.rename (fun i => i + 1) = id := by
      funext σ
      exact Ty.shift_instantiate σ arg
    rw [hfn]
    simp
  rw [hctx] at htyped
  exact htyped

/-- 操作節の混合量化変数を同時に具体化しても型付けを保つ。 -/
theorem Typing.instantiateMany {sig : Signature}
    (hsigwf : Signature.WF sig)
    {Δ : List Kind} {Γ : TermCtx} {ks : List Kind}
    {body : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig (ks ++ Δ) Γ body σ ε)
    {args : List Arg}
    (hargs : List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) ks args) :
    Typing sig Δ (Γ.map (Ty.subst (KindSubst.many args)))
      (body.instantiateMany args)
      (σ.instantiateMany args)
      (ε.substKind (KindSubst.many args)) := by
  exact ht.substKind_preserves hsigwf (KindSubst.many args)
    (KindSubst.many_valid_append hargs)

/-- 操作節の具体化は継続と引数の型を同じ混合引数で具体化する。 -/
theorem Typing.instantiateOpClause {sig : Signature}
    (hsigwf : Signature.WF sig)
    {Δ : List Kind} {Γ : TermCtx} {ks : List Kind}
    {clause : Expr} {decl : OpDecl}
    {σout : Ty} {εout : Effect}
    (ht : Typing sig (ks ++ Δ)
      ((.arr decl.output
        (εout.rename (fun i => i + ks.length))
        (σout.rename (fun i => i + ks.length))) ::
        decl.input :: Γ.liftKind ks.length)
      clause (σout.rename (fun i => i + ks.length))
      (εout.rename (fun i => i + ks.length)))
    {args : List Arg}
    (hargs : List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) ks args) :
    Typing sig Δ
      ((.arr (decl.output.instantiateMany args) εout σout) ::
        (decl.input.instantiateMany args) :: Γ)
      (clause.instantiateMany args) σout εout := by
  let τ := KindSubst.many args
  have hlen : args.length = ks.length := hargs.length_eq.symm
  have htyped := ht.instantiateMany hsigwf hargs
  have hctx :
      (((.arr decl.output
        (εout.rename (fun i => i + ks.length))
        (σout.rename (fun i => i + ks.length))) ::
        decl.input :: Γ.liftKind ks.length).map (Ty.subst τ)) =
      ((.arr (decl.output.instantiateMany args) εout σout) ::
        (decl.input.instantiateMany args) :: Γ) := by
    simp only [List.map_cons, Ty.subst, Effect.substKind]
    rw [Ty.shift_instantiateMany σout args ks.length hlen]
    rw [Effect.shift_instantiateMany εout args ks.length hlen]
    rw [TermCtx.liftKind_instantiateMany Γ args ks.length hlen]
    rfl
  have hresult :
      (σout.rename (fun i => i + ks.length)).subst τ = σout :=
    Ty.shift_instantiateMany σout args ks.length hlen
  have heffect :
      (εout.rename (fun i => i + ks.length)).subst τ.effects = εout :=
    Effect.shift_instantiateMany εout args ks.length hlen
  rw [hctx] at htyped
  change Typing sig Δ
    ((.arr (decl.output.instantiateMany args) εout σout) ::
      (decl.input.instantiateMany args) :: Γ)
    (clause.instantiateMany args)
    ((σout.rename (fun i => i + ks.length)).subst τ)
    ((εout.rename (fun i => i + ks.length)).subst τ.effects) at htyped
  rw [hresult, heffect] at htyped
  exact htyped

end SystemFXi.Poly
