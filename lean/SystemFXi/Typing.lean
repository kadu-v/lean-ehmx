import SystemFXi.Substitution

/-!
# 部分型と型付け

`Typing sig n Γ e σ ε` は TeX の `Δ ∣ Γ ⊢ e : σ ∣ ε` に対応する。
`n` は `Δ` に含まれる型変数の個数である。効果の包含は `Finset` の
通常の包含関係を使う。
-/

namespace SystemFXi

/-- `Γ↑ⁿ` は各項変数の型を `n` 個の型束縛子の下に移す。 -/
def TermCtx.liftTy (n : Nat) (Γ : TermCtx) : TermCtx :=
  Γ.map (Ty.rename (fun i => i + n))

/-- `σ[ᾱ ↦ τ̄]`。リストは de Bruijn 添字の小さい順に並ぶ。 -/
def Ty.instantiateMany (body : Ty) (args : List Ty) : Ty :=
  body.subst (fun i => (args[i]?).getD (.var (i - args.length)))

/-- `e[ᾱ ↦ τ̄]`。操作節の型変数を同時に置換する。 -/
def Expr.instantiateManyTy (body : Expr) (args : List Ty) : Expr :=
  body.substTy (fun i => (args[i]?).getD (.var (i - args.length)))

/-- `Δ ⊢ σ₁ <: σ₂`。関数の引数は反変、結果と潜在効果は共変。 -/
inductive Subtype (sig : Signature) : Nat → Ty → Ty → Prop where
  | var {n i} : Subtype sig n (.var i) (.var i)
  | arr {n a a' ε ε' b b'} :
      Subtype sig n a' a → ε ⊆ ε' → Subtype sig n b b' →
      Subtype sig n (.arr a ε b) (.arr a' ε' b')
  | all {n body body'} :
      Subtype sig (n + 1) body body' →
      Subtype sig n (.all body) (.all body')

/-- `Δ ∣ Γ ⊢ e : σ ∣ ε`。`sub` は型と効果の暗黙の拡大である。 -/
inductive Typing (sig : Signature) : Nat → TermCtx → Expr → Ty → Effect → Prop where
  | var {n Γ i σ} : Γ[i]? = some σ →
      Typing sig n Γ (.var i) σ ∅
  | lam {n Γ a body b ε} : Ty.WF sig n a →
      Typing sig n (a :: Γ) body b ε →
      Typing sig n Γ (.lam a body) (.arr a ε b) ∅
  | app {n Γ f x a b εf εx εbody} :
      Typing sig n Γ f (.arr a εbody b) εf →
      Typing sig n Γ x a εx →
      Typing sig n Γ (.app f x) b (εf ∪ εx ∪ εbody)
  | tlam {n Γ body σ} :
      Typing sig (n + 1) (Γ.liftTy 1) body σ ∅ →
      Typing sig n Γ (.tlam body) (.all σ) ∅
  | tapp {n Γ e σ ε arg} :
      Typing sig n Γ e (.all σ) ε → Ty.WF sig n arg →
      Typing sig n Γ (.tapp e arg) (σ.instantiate arg) ε
  | perform {n Γ op decl args arg ε} :
      sig op = some decl → args.length = decl.arity →
      (∀ a ∈ args, Ty.WF sig n a) →
      Typing sig n Γ arg (decl.input.instantiateMany args) ε →
      Typing sig n Γ (.perform op args arg)
        (decl.output.instantiateMany args) (insert op ε)
  | handle {n Γ body op arity ret clause decl σin σout εin εout} :
      sig op = some decl → arity = decl.arity →
      Typing sig n Γ body σin εin →
      εin ⊆ insert op εout →
      Typing sig n (σin :: Γ) ret σout εout →
      Typing sig (n + arity)
        ((.arr decl.output εout (σout.rename (fun i => i + arity))) ::
          decl.input :: Γ.liftTy arity)
        clause (σout.rename (fun i => i + arity)) εout →
      Typing sig n Γ (.handle body op arity ret clause) σout εout
  | sub {n Γ e σ σ' ε ε'} :
      Typing sig n Γ e σ ε → Subtype sig n σ σ' → ε ⊆ ε' →
      Typing sig n Γ e σ' ε'

end SystemFXi
