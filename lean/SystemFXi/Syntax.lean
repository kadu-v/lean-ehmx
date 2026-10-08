import Mathlib.Data.Finset.Basic

/-!
# System Fξ の構文

型変数と項変数には、それぞれ独立した de Bruijn 添字を使う。
`Ty.all` と `Expr.tlam` は型変数を一つ、`Expr.lam` は項変数を一つ束縛する。
handler の return 節は項変数を一つ、操作節は型変数を `arity` 個と
項変数を二つ束縛する。操作節の項変数 0 は継続、1 は操作の引数である。
-/

namespace SystemFXi

abbrev Op := Nat
/-- `ε` は重複のない有限の操作集合。 -/
abbrev Effect := Finset Op

/-- `σ` は型変数、潜在効果付き関数型、全称型からなる。 -/
inductive Ty where
  | var : Nat → Ty
  | arr : Ty → Effect → Ty → Ty
  | all : Ty → Ty
  deriving DecidableEq

/-- `e` は値呼び System Fξ の式。handler は return 節と操作節を各一つ持つ。 -/
inductive Expr where
  | var : Nat → Expr
  | lam : Ty → Expr → Expr
  | app : Expr → Expr → Expr
  | tlam : Expr → Expr
  | tapp : Expr → Ty → Expr
  | perform : Op → List Ty → Expr → Expr
  | handle : Expr → Op → Nat → Expr → Expr → Expr
  deriving DecidableEq

/-- `Σ(op) = (n, σᵢₙ, σₒᵤₜ)` は型引数を `n` 個取る操作宣言。 -/
structure OpDecl where
  arity : Nat
  input : Ty
  output : Ty
  deriving DecidableEq

/-- `Σ` は各操作名に高々一つの宣言を対応付ける。 -/
abbrev Signature := Op → Option OpDecl

/-- `ε ⊆ dom(Σ)` は効果集合の全操作が宣言済みであることを表す。 -/
def Effect.WF (sig : Signature) (ε : Effect) : Prop :=
  ∀ op ∈ ε, sig op ≠ none

/-- `Δ ⊢ σ :: T`。`Δ` は利用できる型変数の個数である。 -/
inductive Ty.WF (sig : Signature) : Nat → Ty → Prop where
  | var {n i} : i < n → WF sig n (.var i)
  | arr {n a ε b} : WF sig n a → Effect.WF sig ε → WF sig n b → WF sig n (.arr a ε b)
  | all {n body} : WF sig (n + 1) body → WF sig n (.all body)

/-- 大域的シグネチャの各宣言は、その操作の型引数の下で整形式である。 -/
def Signature.WF (sig : Signature) : Prop :=
  ∀ op decl, sig op = some decl →
    Ty.WF sig decl.arity decl.input ∧ Ty.WF sig decl.arity decl.output

/-- `Γ` は直近の項変数の型を先頭に置く。 -/
abbrev TermCtx := List Ty

end SystemFXi
