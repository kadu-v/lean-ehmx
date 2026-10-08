import SystemFXi.Semantics
import SystemFXi.Subtyping

/-!
# Progress

効果を持つ閉項の進行は、値、一歩の簡約、未処理操作の露出という
三場合で述べる。未処理操作にはシグネチャと型引数の情報も保持する。
-/

namespace SystemFXi

/-- `e = E[perform op[τ̄] v]` で、`op ∉ handled(E)` かつ操作宣言が有効。 -/
structure OpenOp (sig : Signature) (e : Expr) (ε : Effect) where
  op : Op
  context : EvalCtx
  args : List Ty
  argument : Expr
  decl : OpDecl
  equation : e = context.plug (.perform op args argument)
  signature : sig op = some decl
  arity : args.length = decl.arity
  value : Value argument
  unhandled : op ∉ context.handled
  allowed : op ∈ ε

/-- `OpenOp Σ e` なら、`e` には未処理の操作呼出しが露出する。 -/
theorem OpenOp.toUnhandled {sig : Signature} {e : Expr} {ε : Effect}
    (h : OpenOp sig e ε) : Unhandled e h.op := by
  exact ⟨h.context, h.args, h.argument, h.equation, h.value, h.unhandled⟩

/-- `Σ ∣ ∅ ⊢ v : (σ₁ → ε σ₂) ∣ ε′` かつ `v` が値なら `v` は項抽象。 -/
private theorem canonical_arr_aux {sig : Signature} {n : Nat} {Γ : TermCtx}
    {v : Expr} {ty : Ty} {εv : Effect}
    (ht : Typing sig n Γ v ty εv) :
    (∃ a ε b, ty = .arr a ε b) → Value v → Γ = [] →
      ∃ ann body, v = .lam ann body := by
  induction ht with
  | var hlookup =>
      intro _ _ hΓ
      simp [hΓ] at hlookup
  | lam => intro _ _ _; exact ⟨_, _, rfl⟩
  | tlam =>
      intro ⟨_, _, _, hshape⟩ _ _
      cases hshape
  | app => intro _ hv _; cases hv
  | tapp => intro _ hv _; cases hv
  | perform => intro _ hv _; cases hv
  | handle => intro _ hv _; cases hv
  | sub _ hs _ ih =>
      intro ⟨a, ε, b, hshape⟩ hv hΓ
      subst hshape
      cases hs with
      | arr => exact ih ⟨_, _, _, rfl⟩ hv hΓ

/-- `Σ ∣ ∅ ⊢ v : (σ₁ → ε σ₂) ∣ ε′` かつ `v` が値なら `v` は項抽象。 -/
private theorem canonical_arr {sig : Signature} {n : Nat} {Γ : TermCtx} {v : Expr}
    {a b : Ty} {ε εv : Effect}
    (ht : Typing sig n Γ v (.arr a ε b) εv) (hv : Value v)
    (hΓ : Γ = []) : ∃ ann body, v = .lam ann body :=
  canonical_arr_aux ht ⟨a, ε, b, rfl⟩ hv hΓ

/-- `Σ ∣ ∅ ⊢ v : ∀α.σ ∣ ε` かつ `v` が値なら `v` は型抽象。 -/
private theorem canonical_all_aux {sig : Signature} {n : Nat} {Γ : TermCtx}
    {v : Expr} {ty : Ty} {εv : Effect}
    (ht : Typing sig n Γ v ty εv) :
    (∃ body, ty = .all body) → Value v → Γ = [] →
      ∃ e, v = .tlam e := by
  induction ht with
  | var hlookup =>
      intro _ _ hΓ
      simp [hΓ] at hlookup
  | lam =>
      intro ⟨_, hshape⟩ _ _
      cases hshape
  | tlam => intro _ _ _; exact ⟨_, rfl⟩
  | app => intro _ hv _; cases hv
  | tapp => intro _ hv _; cases hv
  | perform => intro _ hv _; cases hv
  | handle => intro _ hv _; cases hv
  | sub _ hs _ ih =>
      intro ⟨body, hshape⟩ hv hΓ
      subst hshape
      cases hs with
      | all => exact ih ⟨_, rfl⟩ hv hΓ

/-- `Σ ∣ ∅ ⊢ v : ∀α.σ ∣ ε` かつ `v` が値なら `v` は型抽象。 -/
private theorem canonical_all {sig : Signature} {n : Nat} {Γ : TermCtx} {v : Expr}
    {body : Ty} {εv : Effect}
    (ht : Typing sig n Γ v (.all body) εv) (hv : Value v)
    (hΓ : Γ = []) : ∃ e, v = .tlam e :=
  canonical_all_aux ht ⟨body, rfl⟩ hv hΓ

/-- `Σ ∣ ∅ ⊢ e : σ ∣ ε` なら、`e` は値、一歩進む、または操作が露出する。 -/
private theorem progress_general {sig : Signature} {n : Nat} {Γ : TermCtx}
    {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig n Γ e σ ε) (hΓ : Γ = []) :
    Value e ∨ (∃ e', Step sig e e') ∨ Nonempty (OpenOp sig e ε) := by
  induction ht with
  | var hlookup => simp [hΓ] at hlookup
  | lam => exact Or.inl (.lam _ _)
  | tlam => exact Or.inl (.tlam _)
  | @app n Γ f x a b εf εx εbody hf hx ihf ihx =>
      rcases ihf hΓ with hval | ⟨f', hstep⟩ | ⟨hop⟩
      · rcases ihx hΓ with xval | ⟨x', xstep⟩ | ⟨xop⟩
        · rcases canonical_arr hf hval hΓ with ⟨ann, body, heq⟩
          subst heq
          exact Or.inr (Or.inl ⟨body.instantiate _, .beta xval⟩)
        · exact Or.inr (Or.inl ⟨_, .context (E := .appArg _ hval .hole) xstep⟩)
        · rcases xop with ⟨xop⟩
          exact Or.inr (Or.inr (Nonempty.intro {
            xop with
            context := .appArg f hval xop.context
            equation := by simp [xop.equation, EvalCtx.plug]
            unhandled := xop.unhandled
            allowed := by simp only [Finset.mem_union]; exact Or.inl (Or.inr xop.allowed)
          }))
      · exact Or.inr (Or.inl ⟨_, .context (E := .appFun .hole _) hstep⟩)
      · rcases hop with ⟨hop⟩
        exact Or.inr (Or.inr (Nonempty.intro {
          hop with
          context := .appFun hop.context x
          equation := by simp [hop.equation, EvalCtx.plug]
          unhandled := hop.unhandled
          allowed := by simp only [Finset.mem_union]; exact Or.inl (Or.inl hop.allowed)
        }))
  | @tapp n Γ fn bodyTy eff tyArg he _ ihe =>
      rcases ihe hΓ with hval | ⟨e', hstep⟩ | ⟨hop⟩
      · rcases canonical_all he hval hΓ with ⟨body, heq⟩
        subst heq
        exact Or.inr (Or.inl ⟨_, .typeBeta⟩)
      · exact Or.inr (Or.inl ⟨_, .context (E := .tapp .hole _) hstep⟩)
      · rcases hop with ⟨hop⟩
        exact Or.inr (Or.inr (Nonempty.intro {
          hop with
          context := .tapp hop.context tyArg
          equation := by simp [hop.equation, EvalCtx.plug]
          unhandled := hop.unhandled
          allowed := hop.allowed
        }))
  | @perform n Γ op decl args arg eff hsig hlen _ harg iharg =>
      rcases iharg hΓ with hval | ⟨arg', hstep⟩ | ⟨hop⟩
      · exact Or.inr (Or.inr (Nonempty.intro {
          op := op
          context := .hole
          args := args
          argument := arg
          decl := decl
          equation := rfl
          signature := hsig
          arity := hlen
          value := hval
          unhandled := by simp [EvalCtx.handled]
          allowed := by simp
        }))
      · exact Or.inr (Or.inl ⟨_, .context (E := .perform _ _ .hole) hstep⟩)
      · rcases hop with ⟨hop⟩
        exact Or.inr (Or.inr (Nonempty.intro {
          hop with
          context := .perform op args hop.context
          equation := by simp [hop.equation, EvalCtx.plug]
          unhandled := hop.unhandled
          allowed := Finset.mem_insert_of_mem hop.allowed
        }))
  | @handle n Γ body op arity ret clause decl σin σout εin εout
      hsig harity _ hsubset _ _ ihbody ihret ihclause =>
      rcases ihbody hΓ with hval | ⟨body', hstep⟩ | ⟨hop⟩
      · exact Or.inr (Or.inl ⟨_, .ret hval⟩)
      · exact Or.inr (Or.inl ⟨_, .context (E := .handle .hole _ _ _ _) hstep⟩)
      · rcases hop with ⟨hop⟩
        by_cases heq : hop.op = op
        · subst op
          have hdecl : hop.decl = decl :=
            Option.some.inj (hop.signature.symm.trans hsig)
          subst decl
          have hargs : hop.args.length = arity :=
            hop.arity.trans harity.symm
          have hstep : Step sig
              (.handle (hop.context.plug
                (.perform hop.op hop.args hop.argument)) hop.op arity ret clause)
              ((clause.instantiateManyTy hop.args).instantiateOp
                (Expr.resume hop.context hop.op arity ret clause
                  (hop.decl.output.instantiateMany hop.args)) hop.argument) :=
            .operation hsig harity hargs hop.value hop.unhandled
          exact Or.inr (Or.inl ⟨_, by
            simpa only [hop.equation] using hstep⟩)
        · exact Or.inr (Or.inr (Nonempty.intro {
            hop with
            context := .handle hop.context op arity ret clause
            equation := by simp [hop.equation, EvalCtx.plug]
            unhandled := by
              simp only [EvalCtx.handled, Finset.mem_insert, not_or]
              exact ⟨heq, hop.unhandled⟩
            allowed := by
              have hmem := hsubset hop.allowed
              simpa only [Finset.mem_insert, heq, false_or] using hmem
          }))
  | sub _ _ hε ih =>
      rcases ih hΓ with hv | ⟨e', hs⟩ | ⟨hop⟩
      · exact Or.inl hv
      · exact Or.inr (Or.inl ⟨e', hs⟩)
      · rcases hop with ⟨hop⟩
        exact Or.inr (Or.inr (Nonempty.intro {
          hop with allowed := hε hop.allowed
        }))

/-- `Σ ∣ ∅ ⊢ e : σ ∣ ε` なら、`e` は値、一歩進む、または操作が露出する。 -/
theorem progress {sig : Signature} {e : Expr} {σ : Ty} {ε : Effect}
    (ht : Typing sig 0 [] e σ ε) :
    Value e ∨ (∃ e', Step sig e e') ∨ Nonempty (OpenOp sig e ε) :=
  progress_general ht rfl

/-- `Σ ∣ ∅ ⊢ e : σ ∣ ε` なら、露出した操作 `op` は `ε` に属する。 -/
theorem progress_effect_safety {sig : Signature} {e : Expr}
    {σ : Ty} {ε : Effect} (ht : Typing sig 0 [] e σ ε) :
    Value e ∨ (∃ e', Step sig e e') ∨
      ∃ op, Unhandled e op ∧ op ∈ ε := by
  rcases progress ht with hv | hs | ⟨hop⟩
  · exact Or.inl hv
  · exact Or.inr (Or.inl hs)
  · rcases hop with ⟨hop⟩
    exact Or.inr (Or.inr ⟨hop.op, hop.toUnhandled, hop.allowed⟩)

/-- `Σ ∣ ∅ ⊢ e : σ ∣ ∅` なら、`e` は値か、一歩進む。 -/
theorem progress_empty_effect {sig : Signature} {e : Expr} {σ : Ty}
    (ht : Typing sig 0 [] e σ ∅) :
    Value e ∨ ∃ e', Step sig e e' := by
  rcases progress ht with hv | hs | ⟨hop⟩
  · exact Or.inl hv
  · exact Or.inr hs
  · rcases hop with ⟨hop⟩
    exact False.elim (by simpa using hop.allowed)

end SystemFXi
