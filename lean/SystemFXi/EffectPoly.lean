import SystemFXi.Syntax
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Lattice.Fold

/-!
# 効果変数を持つ System Fξ の効果式

Effect は有限個の操作ラベルと効果変数の和集合を正規形で保持する。
効果変数への代入は操作の有限集合への評価とは異なり、別の効果変数を含められる。
包含は、すべての有限集合への評価で成り立つ意味論的包含である。
-/

namespace SystemFXi.Poly

/-- κ ::= T | E。 -/
inductive Kind where
  | type
  | effect
  deriving DecidableEq

/-- ε ::= ∅ | {op} | μ | ε ∪ ε の集合正規形。 -/
structure Effect where
  labels : Finset Op
  vars : Finset Nat
  deriving DecidableEq

namespace Effect

/-- ∅ は操作も変数も含まない。 -/
def empty : Effect := ⟨∅, ∅⟩

/-- {op} は操作を一つだけ含む。 -/
def singleton (op : Op) : Effect := ⟨{op}, ∅⟩

/-- μ は効果変数を一つだけ含む。 -/
def var (μ : Nat) : Effect := ⟨∅, {μ}⟩

/-- 効果和は両成分の集合和である。 -/
def union (ε η : Effect) : Effect :=
  ⟨ε.labels ∪ η.labels, ε.vars ∪ η.vars⟩

instance : EmptyCollection Effect := ⟨empty⟩
instance : Union Effect := ⟨union⟩

@[simp] theorem labels_empty : (∅ : Effect).labels = ∅ := rfl
@[simp] theorem vars_empty : (∅ : Effect).vars = ∅ := rfl
@[simp] theorem labels_singleton (op : Op) :
    (singleton op).labels = {op} := rfl
@[simp] theorem vars_singleton (op : Op) :
    (singleton op).vars = ∅ := rfl
@[simp] theorem labels_union (ε η : Effect) :
    (ε ∪ η).labels = ε.labels ∪ η.labels := rfl
@[simp] theorem vars_union (ε η : Effect) :
    (ε ∪ η).vars = ε.vars ∪ η.vars := rfl

/-- Iρ(ε) は各効果変数を有限操作集合として解釈した結果。 -/
def eval (ρ : Nat → Finset Op) (ε : Effect) : Finset Op :=
  ε.labels ∪ ε.vars.biUnion ρ

/-- ε ⊑ η は各成分の集合包含である。 -/
def Subset (ε η : Effect) : Prop :=
  ε.labels ⊆ η.labels ∧ ε.vars ⊆ η.vars

instance : HasSubset Effect := ⟨Subset⟩

/-- ε ⊑ η なら、任意の有限集合解釈で Iρ(ε) ⊆ Iρ(η)。 -/
theorem subset_eval {ε η : Effect} (h : ε ⊆ η)
    (ρ : Nat → Finset Op) : ε.eval ρ ⊆ η.eval ρ := by
  intro op hop
  rcases Finset.mem_union.mp hop with hl | hv
  · exact Finset.mem_union.mpr (Or.inl (h.1 hl))
  · apply Finset.mem_union.mpr
    right
    rcases Finset.mem_biUnion.mp hv with ⟨μ, hμ, hopρ⟩
    exact Finset.mem_biUnion.mpr ⟨μ, h.2 hμ, hopρ⟩

/-- 任意の有限集合解釈での包含から、構文上の包含 ε ⊑ η が従う。 -/
theorem subset_of_eval_subset {ε η : Effect}
    (h : ∀ ρ : Nat → Finset Op, ε.eval ρ ⊆ η.eval ρ) :
    ε ⊆ η := by
  constructor
  · intro op hop
    have hmem : op ∈ ε.eval (fun _ => ∅) := by
      exact Finset.mem_union.mpr (Or.inl hop)
    have := h (fun _ => ∅) hmem
    simpa [eval] using this
  · intro μ hμ
    let fresh : Op := η.labels.sup id + 1
    let ρ : Nat → Finset Op := fun ν => if ν = μ then {fresh} else ∅
    have hmem : fresh ∈ ε.eval ρ := by
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      exact ⟨μ, hμ, by simp [ρ]⟩
    have htarget := h ρ hmem
    rcases Finset.mem_union.mp htarget with hlabel | hvar
    · have hbound : fresh ≤ η.labels.sup id :=
        Finset.le_sup (f := id) hlabel
      have himpossible :
          η.labels.sup id + 1 ≤ η.labels.sup id := by
        simpa only [fresh] using hbound
      exact False.elim ((Nat.not_succ_le_self _)
        (by simpa only [Nat.succ_eq_add_one] using himpossible))
    · rcases Finset.mem_biUnion.mp hvar with ⟨ν, hν, hρ⟩
      have hνμ : ν = μ := by
        by_contra hne
        simp [ρ, hne] at hρ
      simpa [hνμ] using hν

/-- 意味論的包含と正規形の成分ごとの包含は同値。 -/
theorem subset_iff_eval_subset {ε η : Effect} :
    ε ⊆ η ↔ ∀ ρ : Nat → Finset Op, ε.eval ρ ⊆ η.eval ρ :=
  ⟨fun h ρ => subset_eval h ρ, subset_of_eval_subset⟩

/-- 効果の空集合は和集合の左単位元である。 -/
theorem empty_union (ε : Effect) : empty ∪ ε = ε := by
  cases ε with
  | mk labels vars =>
      change Effect.mk (∅ ∪ labels) (∅ ∪ vars) = _
      simp

/-- 効果の和集合は交換的である。 -/
theorem union_comm (ε η : Effect) : ε ∪ η = η ∪ ε := by
  cases ε with
  | mk labels vars =>
      cases η with
      | mk labels' vars' =>
          change Effect.mk (labels ∪ labels') (vars ∪ vars') =
            Effect.mk (labels' ∪ labels) (vars' ∪ vars)
          simp [Finset.union_comm]

/-- 効果の和集合は冪等である。 -/
theorem union_idem (ε : Effect) : ε ∪ ε = ε := by
  cases ε with
  | mk labels vars =>
      change Effect.mk (labels ∪ labels) (vars ∪ vars) = _
      simp

/-- 型・効果変数の同時改名のうち効果側。 -/
def rename (ρ : Nat → Nat) (ε : Effect) : Effect :=
  ⟨ε.labels, ε.vars.image ρ⟩

/-- 型・効果変数の同時置換のうち効果側。 -/
def subst (τ : Nat → Effect) (ε : Effect) : Effect :=
  ⟨ε.labels ∪ ε.vars.biUnion (fun μ => (τ μ).labels),
   ε.vars.biUnion (fun μ => (τ μ).vars)⟩

/-- 型・効果変数の kind 環境で ε :: E。 -/
def WF (declared : Op → Prop) (Δ : List Kind) (ε : Effect) : Prop :=
  (∀ op ∈ ε.labels, declared op) ∧
  (∀ μ ∈ ε.vars, Δ[μ]? = some .effect)

end Effect

/-- 型変数と効果変数は同じ de Bruijn 空間を用い、kind で区別する。 -/
inductive Ty where
  | var : Nat → Ty
  | arr : Ty → Effect → Ty → Ty
  | all : Kind → Ty → Ty
  deriving DecidableEq

/-- 多相操作宣言の量化 kind は de Bruijn 添字の小さい順に並ぶ。 -/
structure OpDecl where
  kinds : List Kind
  input : Ty
  output : Ty
  deriving DecidableEq

abbrev Signature := Op → Option OpDecl

/-- Δ ⊢ σ :: T。効果変数を関数型の潜在効果に出現させられる。 -/
inductive Ty.WF (sig : Signature) : List Kind → Ty → Prop where
  | var {Δ i} : Δ[i]? = some .type → WF sig Δ (.var i)
  | arr {Δ a ε b} :
      WF sig Δ a → Effect.WF (fun op => sig op ≠ none) Δ ε → WF sig Δ b →
      WF sig Δ (.arr a ε b)
  | all {Δ κ body} :
      WF sig (κ :: Δ) body → WF sig Δ (.all κ body)

/-- θ ::= σ | ε。操作宣言は両 kind の引数を混在させられる。 -/
inductive Arg where
  | type : Ty → Arg
  | effect : Effect → Arg
  deriving DecidableEq

/-- Δ ⊢ θ :: κ。 -/
def Arg.WF (sig : Signature) (Δ : List Kind) : Kind → Arg → Prop
  | .type, .type σ => Ty.WF sig Δ σ
  | .effect, .effect ε => Effect.WF (fun op => sig op ≠ none) Δ ε
  | _, _ => False

/-- Σ の宣言は量化変数の下で kind T を持つ。 -/
def Signature.WF (sig : Signature) : Prop :=
  ∀ op decl, sig op = some decl →
    Ty.WF sig decl.kinds decl.input ∧ Ty.WF sig decl.kinds decl.output

/-- 型付き式の構文。単一操作の handler は deep に再開する。 -/
inductive Expr where
  | var : Nat → Expr
  | lam : Ty → Expr → Expr
  | app : Expr → Expr → Expr
  | tlam : Kind → Expr → Expr
  | tapp : Expr → Arg → Expr
  | perform : Op → List Arg → Expr → Expr
  | handle : Expr → Op → Nat → Expr → Expr → Expr
  deriving DecidableEq

end SystemFXi.Poly
