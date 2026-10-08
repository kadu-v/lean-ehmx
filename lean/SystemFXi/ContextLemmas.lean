import SystemFXi.Redex

/-!
# 評価文脈内の型付け

文脈の穴に置かれた式の型付けを取り出し、同じ型と効果を持つ式に
差し替えられることを示す。
-/

namespace SystemFXi

/-- 項変数の改名は評価文脈の穴への代入と交換する。 -/
theorem EvalCtx.renameTerm_plug (E : EvalCtx) (e : Expr)
    (ρ : Nat → Nat) :
    (E.plug e).renameTerm ρ =
      (E.renameTerm ρ).plug (e.renameTerm ρ) := by
  induction E with
  | hole => rfl
  | appFun E x ih => simp [EvalCtx.plug, EvalCtx.renameTerm, Expr.renameTerm, ih]
  | appArg f hv E ih => simp [EvalCtx.plug, EvalCtx.renameTerm, Expr.renameTerm, ih]
  | tapp E arg ih => simp [EvalCtx.plug, EvalCtx.renameTerm, Expr.renameTerm, ih]
  | perform op args E ih => simp [EvalCtx.plug, EvalCtx.renameTerm, Expr.renameTerm, ih]
  | handle E op arity ret clause ih =>
      simp [EvalCtx.plug, EvalCtx.renameTerm, Expr.renameTerm, ih]

/-- `Γ ⊢ perform op[τ̄] v : σ ∣ ε` は操作の引数と結果型の情報を含む。 -/
theorem Typing.perform_inv {sig : Signature} {n : Nat} {Γ : TermCtx}
    {op : Op} {args : List Ty} {v : Expr} {σ : Ty} {ε : Effect}
    {decl : OpDecl} (hsig : sig op = some decl)
    (ht : Typing sig n Γ (.perform op args v) σ ε) :
    (∀ a ∈ args, Ty.WF sig n a) ∧
    ∃ εarg,
      Typing sig n Γ v (decl.input.instantiateMany args) εarg ∧
      Subtype sig n (decl.output.instantiateMany args) σ ∧
      op ∈ ε := by
  generalize he : Expr.perform op args v = e at ht
  induction ht generalizing op args v with
  | @perform n Γ op₀ decl₀ args₀ arg εarg hsig₀ hlen hargs harg =>
      cases he
      have hdecl : decl₀ = decl := Option.some.inj (hsig₀.symm.trans hsig)
      subst decl₀
      exact ⟨hargs, εarg, harg, Subtype.refl _ _, by simp⟩
  | sub _ hs hε ih =>
      obtain ⟨hargs, εarg, harg, hsub, hmem⟩ := ih hsig he
      exact ⟨hargs, εarg, harg, Subtype.trans hsub hs, hε hmem⟩
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | tapp => cases he
  | handle => cases he

end SystemFXi

namespace SystemFXi

/-- 関数位置を同じ型・効果の式へ差し替えると、適用全体の型付けを保つ。 -/
theorem Typing.map_app_fun {sig : Signature} {n : Nat} {Γ : TermCtx}
    {f f' x : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (.app f x) σ ε)
    (hm : ∀ {τ η}, Typing sig n Γ f τ η → Typing sig n Γ f' τ η) :
    Typing sig n Γ (.app f' x) σ ε := by
  generalize he : Expr.app f x = e at ht
  induction ht generalizing f x with
  | app hf hx =>
      cases he
      exact .app (hm hf) hx
  | sub _ hs hε ih => exact .sub (ih hm he) hs hε
  | var => cases he
  | lam => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he
  | handle => cases he

/-- 引数位置を同じ型・効果の式へ差し替えると、適用全体の型付けを保つ。 -/
theorem Typing.map_app_arg {sig : Signature} {n : Nat} {Γ : TermCtx}
    {f x x' : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (.app f x) σ ε)
    (hm : ∀ {τ η}, Typing sig n Γ x τ η → Typing sig n Γ x' τ η) :
    Typing sig n Γ (.app f x') σ ε := by
  generalize he : Expr.app f x = e at ht
  induction ht generalizing f x with
  | app hf hx =>
      cases he
      exact .app hf (hm hx)
  | sub _ hs hε ih => exact .sub (ih hm he) hs hε
  | var => cases he
  | lam => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he
  | handle => cases he

/-- 型適用の関数位置を同じ型・効果の式へ差し替えても型付けを保つ。 -/
theorem Typing.map_tapp {sig : Signature} {n : Nat} {Γ : TermCtx}
    {f f' : Expr} {arg σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (.tapp f arg) σ ε)
    (hm : ∀ {τ η}, Typing sig n Γ f τ η → Typing sig n Γ f' τ η) :
    Typing sig n Γ (.tapp f' arg) σ ε := by
  generalize he : Expr.tapp f arg = e at ht
  induction ht generalizing f arg with
  | tapp hf harg =>
      cases he
      exact .tapp (hm hf) harg
  | sub _ hs hε ih => exact .sub (ih hm he) hs hε
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | perform => cases he
  | handle => cases he

/-- 操作の引数位置を同じ型・効果の式へ差し替えても型付けを保つ。 -/
theorem Typing.map_perform {sig : Signature} {n : Nat} {Γ : TermCtx}
    {op : Op} {args : List Ty} {arg arg' : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (.perform op args arg) σ ε)
    (hm : ∀ {τ η}, Typing sig n Γ arg τ η → Typing sig n Γ arg' τ η) :
    Typing sig n Γ (.perform op args arg') σ ε := by
  generalize he : Expr.perform op args arg = e at ht
  induction ht generalizing op args arg with
  | perform hsig hlen hargs harg =>
      cases he
      exact .perform hsig hlen hargs (hm harg)
  | sub _ hs hε ih => exact .sub (ih hm he) hs hε
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | tapp => cases he
  | handle => cases he

/-- handler 本体を同じ型・効果の式へ差し替えても型付けを保つ。 -/
theorem Typing.map_handle_body {sig : Signature} {n : Nat} {Γ : TermCtx}
    {body body' ret clause : Expr} {op arity : Nat}
    {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (.handle body op arity ret clause) σ ε)
    (hm : ∀ {τ η}, Typing sig n Γ body τ η → Typing sig n Γ body' τ η) :
    Typing sig n Γ (.handle body' op arity ret clause) σ ε := by
  generalize he : Expr.handle body op arity ret clause = e at ht
  induction ht generalizing body op arity ret clause with
  | handle hsig harity hb hε hr hc =>
      cases he
      exact .handle hsig harity (hm hb) hε hr hc
  | sub _ hs hε ih => exact .sub (ih hm he) hs hε
  | var => cases he
  | lam => cases he
  | app => cases he
  | tlam => cases he
  | tapp => cases he
  | perform => cases he

/-- `Γ ⊢ E[e] : σ ∣ ε` と、`e` の全ての型付けを保つ差替えから `E[e′]` を得る。 -/
theorem EvalCtx.replace {sig : Signature} {n : Nat} {Γ : TermCtx}
    {E : EvalCtx} {e e' : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (E.plug e) σ ε)
    (hm : ∀ {τ η}, Typing sig n Γ e τ η → Typing sig n Γ e' τ η) :
    Typing sig n Γ (E.plug e') σ ε := by
  induction E generalizing σ ε with
  | hole => exact hm ht
  | appFun E x ih =>
      exact ht.map_app_fun (fun h => ih h)
  | appArg f hv E ih =>
      exact ht.map_app_arg (fun h => ih h)
  | tapp E arg ih =>
      exact ht.map_tapp (fun h => ih h)
  | perform op args E ih =>
      exact ht.map_perform (fun h => ih h)
  | handle E op arity ret clause ih =>
      exact ht.map_handle_body (fun h => ih h)

/-- `Γ ⊢ E[e] : σ ∣ ε` なら、穴の式 `e` にもある型付けが存在する。 -/
theorem EvalCtx.subterm {sig : Signature} {n : Nat} {Γ : TermCtx}
    {E : EvalCtx} {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ (E.plug e) σ ε) :
    ∃ τ η, Typing sig n Γ e τ η := by
  induction E generalizing σ ε with
  | hole => exact ⟨σ, ε, ht⟩
  | appFun E x ihE =>
      change Typing sig n Γ (.app (E.plug e) x) σ ε at ht
      generalize he : Expr.app (E.plug e) x = z at ht
      induction ht with
      | app hf _ => cases he; exact ihE hf
      | sub _ _ _ ihT => exact ihT ihE he
      | var => cases he
      | lam => cases he
      | tlam => cases he
      | tapp => cases he
      | perform => cases he
      | handle => cases he
  | appArg f hv E ihE =>
      change Typing sig n Γ (.app f (E.plug e)) σ ε at ht
      generalize he : Expr.app f (E.plug e) = z at ht
      induction ht with
      | app _ hx => cases he; exact ihE hx
      | sub _ _ _ ihT => exact ihT ihE he
      | var => cases he
      | lam => cases he
      | tlam => cases he
      | tapp => cases he
      | perform => cases he
      | handle => cases he
  | tapp E arg ihE =>
      change Typing sig n Γ (.tapp (E.plug e) arg) σ ε at ht
      generalize he : Expr.tapp (E.plug e) arg = z at ht
      induction ht with
      | tapp hf _ => cases he; exact ihE hf
      | sub _ _ _ ihT => exact ihT ihE he
      | var => cases he
      | lam => cases he
      | app => cases he
      | tlam => cases he
      | perform => cases he
      | handle => cases he
  | perform op args E ihE =>
      change Typing sig n Γ (.perform op args (E.plug e)) σ ε at ht
      generalize he : Expr.perform op args (E.plug e) = z at ht
      induction ht with
      | perform _ _ _ harg => cases he; exact ihE harg
      | sub _ _ _ ihT => exact ihT ihE he
      | var => cases he
      | lam => cases he
      | app => cases he
      | tlam => cases he
      | tapp => cases he
      | handle => cases he
  | handle E op arity ret clause ihE =>
      change Typing sig n Γ (.handle (E.plug e) op arity ret clause) σ ε at ht
      generalize he : Expr.handle (E.plug e) op arity ret clause = z at ht
      induction ht with
      | handle _ _ hbody _ _ _ => cases he; exact ihE hbody
      | sub _ _ _ ihT => exact ihT ihE he
      | var => cases he
      | lam => cases he
      | app => cases he
      | tlam => cases he
      | tapp => cases he
      | perform => cases he

/-- 宣言内の型 `δ` と整形式の型引数列から、具体化した型の整形式を得る。 -/
theorem Ty.WF.instantiateMany {sig : Signature} {n k : Nat}
    {δ : Ty} (hδ : Ty.WF sig k δ)
    (args : List Ty) (hlen : args.length = k)
    (hargs : ∀ a ∈ args, Ty.WF sig n a) :
    Ty.WF sig n (δ.instantiateMany args) := by
  apply hδ.subst_preserves
    (fun i => (args[i]?).getD (.var (i - args.length)))
  intro i hi
  have hidx : i < args.length := by omega
  simpa [Ty.instantiateMany, hidx] using hargs args[i] (List.getElem_mem hidx)

/-- deep 継続 `λy. handle E[y] with h` は、操作結果から handler 出力への関数。 -/
theorem Typing.resume_preserves {sig : Signature} {n : Nat}
    {Γ : TermCtx} {E : EvalCtx} {op : Op} {arity : Nat}
    {ret clause v : Expr} {args : List Ty} {decl : OpDecl}
    {σout : Ty} {εout : Effect}
    (hsig : sig op = some decl)
    (hout : Ty.WF sig n (decl.output.instantiateMany args))
    (ht : Typing sig n Γ
      (.handle (E.plug (.perform op args v)) op arity ret clause)
      σout εout) :
    Typing sig n Γ
      (Expr.resume E op arity ret clause
        (decl.output.instantiateMany args))
      (.arr (decl.output.instantiateMany args) εout σout) ∅ := by
  let outputTy := decl.output.instantiateMany args
  have hweak := ht.renameTerm_preserves (outputTy :: Γ) Nat.succ
    (TermRenaming.weaken Γ outputTy)
  rw [Expr.renameTerm, EvalCtx.renameTerm_plug] at hweak
  have hbody : Typing sig n (outputTy :: Γ)
      (.handle ((E.renameTerm Nat.succ).plug (.var 0)) op arity
        (ret.renameTerm (liftTermRen Nat.succ))
        (clause.renameTerm (liftTermRenN 2 Nat.succ)))
      σout εout := by
    apply hweak.map_handle_body
    intro τ η hinner
    apply EvalCtx.replace hinner
    intro τ' η' hperf
    obtain ⟨_, _, _, hsub, _⟩ := hperf.perform_inv hsig
    exact .sub (.var rfl) hsub (by simp)
  exact .lam hout hbody

/-- 操作節の継続 `k` と引数 `x` を型の合う値に置換する。 -/
theorem Typing.instantiateOp_preserves {sig : Signature}
    (hsigwf : Signature.WF sig) {n : Nat} {Γ : TermCtx}
    {clause continuation argument : Expr}
    {continuationTy argumentTy σ : Ty} {ε : Effect}
    (hclause : Typing sig n
      (continuationTy :: argumentTy :: Γ) clause σ ε)
    (hcont : Typing sig n Γ continuation continuationTy ∅)
    (harg : Typing sig n Γ argument argumentTy ∅) :
    Typing sig n Γ (clause.instantiateOp continuation argument) σ ε := by
  apply hclause.substTerm_preserves hsigwf Γ
    (fun | 0 => continuation | 1 => argument | i + 2 => .var i)
  intro i τ hi
  cases i with
  | zero =>
      simp at hi
      subst τ
      exact hcont
  | succ j =>
      cases j with
      | zero =>
          simp at hi
          subst τ
          exact harg
      | succ k =>
          have hget : Γ[k]? = some τ := by simpa using hi
          exact .var hget

end SystemFXi
