import SystemFXi.EffectPolySubstitution

/-!
# 効果多相な型付け

型抽象と型適用の kind は T と E の双方を許す。
操作宣言の引数列も kind ごとに照合する。効果包含は Effect の
意味論的包含と同値な集合正規形上の包含を使う。
-/

namespace SystemFXi.Poly

/-- Γ は直近の項変数の型を先頭に置く。 -/
abbrev TermCtx := List Ty

/-- Γ↑ⁿ は型と効果の de Bruijn 添字を n だけ持ち上げる。 -/
def TermCtx.liftKind (Γ : TermCtx) (n : Nat) : TermCtx :=
  Γ.map (Ty.rename (fun i => i + n))

/-- Δ ⊢ σ₁ <: σ₂。関数は引数反変、結果と潜在効果が共変。 -/
inductive Subtype (sig : Signature) : List Kind → Ty → Ty → Prop where
  | var {Δ i} : Subtype sig Δ (.var i) (.var i)
  | arr {Δ a a' ε ε' b b'} :
      Subtype sig Δ a' a → ε ⊆ ε' → Subtype sig Δ b b' →
      Subtype sig Δ (.arr a ε b) (.arr a' ε' b')
  | all {Δ κ body body'} :
      Subtype sig (κ :: Δ) body body' →
      Subtype sig Δ (.all κ body) (.all κ body')

/-- Δ ∣ Γ ⊢ e : σ ∣ ε。値の評価効果は空集合。 -/
inductive Typing (sig : Signature) :
    List Kind → TermCtx → Expr → Ty → Effect → Prop where
  | var {Δ Γ i σ} :
      Γ[i]? = some σ → Ty.WF sig Δ σ →
      Typing sig Δ Γ (.var i) σ ∅
  | lam {Δ Γ a body b ε} :
      Ty.WF sig Δ a →
      Typing sig Δ (a :: Γ) body b ε →
      Typing sig Δ Γ (.lam a body) (.arr a ε b) ∅
  | app {Δ Γ f x a b εf εx εbody} :
      Typing sig Δ Γ f (.arr a εbody b) εf →
      Typing sig Δ Γ x a εx →
      Typing sig Δ Γ (.app f x) b (εf ∪ εx ∪ εbody)
  | tlam {Δ Γ κ body σ} :
      Typing sig (κ :: Δ) (Γ.liftKind 1) body σ ∅ →
      Typing sig Δ Γ (.tlam κ body) (.all κ σ) ∅
  | tapp {Δ Γ e κ σ ε arg} :
      Typing sig Δ Γ e (.all κ σ) ε →
      Arg.WF sig Δ κ arg →
      Typing sig Δ Γ (.tapp e arg) (σ.instantiate arg) ε
  | perform {Δ Γ op decl args arg ε} :
      sig op = some decl →
      List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) decl.kinds args →
      Typing sig Δ Γ arg (decl.input.instantiateMany args) ε →
      Typing sig Δ Γ (.perform op args arg)
        (decl.output.instantiateMany args)
        (Effect.singleton op ∪ ε)
  | handle {Δ Γ body op arity ret clause decl σin σout εin εout} :
      sig op = some decl →
      arity = decl.kinds.length →
      Typing sig Δ Γ body σin εin →
      εin ⊆ Effect.singleton op ∪ εout →
      Typing sig Δ (σin :: Γ) ret σout εout →
      Typing sig (decl.kinds ++ Δ)
        ((.arr decl.output
          (εout.rename (fun i => i + arity))
          (σout.rename (fun i => i + arity))) ::
          decl.input :: Γ.liftKind arity)
        clause (σout.rename (fun i => i + arity))
        (εout.rename (fun i => i + arity)) →
      Typing sig Δ Γ (.handle body op arity ret clause) σout εout
  | sub {Δ Γ e σ σ' ε ε'} :
      Typing sig Δ Γ e σ ε →
      Subtype sig Δ σ σ' →
      Ty.WF sig Δ σ' →
      Effect.WF (fun op => sig op ≠ none) Δ ε' →
      ε ⊆ ε' →
      Typing sig Δ Γ e σ' ε'

end SystemFXi.Poly
