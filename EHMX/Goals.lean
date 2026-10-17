import EHMX.Typing
import EHMX.Inference
import EHMX.Operational

/-! 最終目標の正確な命題。`def ... : Prop` は証明ではない。
健全性・完全性・保存・進行の仮定を互いの仮定として埋め込まない。 -/
namespace EHMX

def Assumptions (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  EffectFramework S M ∧ OpSignature.WF S sig

/-- ATTAPL 10.4.4 の作用域を明示した EHMX 版。`inferenceSoundness` が証明する。 -/
def InferenceSoundnessGoal (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  Assumptions S M sig → ∀ Δ Γ e T ε,
    (∀ k ∈ Δ, k ∈ S.kinds) → Γ.WF S Δ → e.Scoped Γ → e.Declared sig →
    T.HasKind S Δ 0 → ε.HasKind S Δ 1 →
    Typing S M sig Δ (infer sig Γ e T ε) Γ e T ε

/-- ATTAPL 10.4.8 に対応し、環境実現可能性を明示する。`inferenceCompleteness` が証明する。 -/
def InferenceCompletenessGoal (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  Assumptions S M sig → ∀ Δ C Γ e T ε,
    (∀ k ∈ Δ, k ∈ S.kinds) → Entails S M Δ C Γ.exists_ →
    Typing S M sig Δ C Γ e T ε → Entails S M Δ C (infer sig Γ e T ε)

def PrincipalConstraint (S : Signature) (M : Model) (sig : OpSignature)
    (Δ : List Kind) (Γ : Env) (e : Expr) (T : Ty) (ε : Effect) (D : Constraint) : Prop :=
  Typing S M sig Δ D Γ e T ε ∧
  ∀ C, Entails S M Δ C Γ.exists_ → Typing S M sig Δ C Γ e T ε → Entails S M Δ C D

def PrincipalityGoal (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  Assumptions S M sig → ∀ Δ Γ e T ε,
    (∀ k ∈ Δ, k ∈ S.kinds) → Γ.WF S Δ → e.Scoped Γ → e.Declared sig →
    T.HasKind S Δ 0 → ε.HasKind S Δ 1 →
    PrincipalConstraint S M sig Δ Γ e T ε (infer sig Γ e T ε)

def SafetyAssumptions (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  Assumptions S M sig ∧ ArrowSeparated S M

def PreservationGoal (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  SafetyAssumptions S M sig → ∀ Δ C Γ e e' T ε,
    Typing S M sig Δ C Γ e T ε → Step e e' → Typing S M sig Δ C Γ e' T ε

/-- The constraint is interpreted by an actual satisfying valuation, not an empty set of models. -/
def ProgressGoal (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  SafetyAssumptions S M sig → ∀ C e T ε,
    Typing S M sig [] C {} e T ε →
    ∀ ρ ι, Assignment.Valid S M ρ → ι.Valid → C.Holds M ρ [] ι →
      Value e ∨ (∃ e', Step e e') ∨ ∃ op, Unhandled e op ∧ op ∈ M.effects (ε.eval M ρ [])

def EffectSafetyGoal (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  SafetyAssumptions S M sig → ∀ C e e' T ε,
    Typing S M sig [] C {} e T ε → Steps e e' →
    ∀ ρ ι, Assignment.Valid S M ρ → ι.Valid → C.Holds M ρ [] ι →
      Value e' ∨ (∃ e'', Step e' e'') ∨
        ∃ op, Unhandled e' op ∧ op ∈ M.effects (ε.eval M ρ [])

def EmptyEffectSafetyGoal (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  SafetyAssumptions S M sig → ∀ C e e' T,
    Satisfiable S M [] C → Typing S M sig [] C {} e T .empty → Steps e e' →
      Value e' ∨ ∃ e'', Step e' e''

/-- The exact substitution obligation for the polymorphic let redex. -/
def SchemeValueSubstitutionGoal (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  Assumptions S M sig → ∀ Δ C Γ v body ks D A T ε,
    Value v → Typing S M sig (ks ++ Δ) (.conj (C.shift ks.length 0) D)
      (Γ.shift ks.length) v A .empty →
    Entails S M Δ C (.exists_ ks D) →
    Typing S M sig Δ C (Γ.push (.all ks D A)) body T ε →
    Typing S M sig Δ C Γ (body.openAt 0 [v]) T ε

/-- Prove this by exposing existential typing binders before choosing operation
arguments. Moving those arguments outside their scope is not a valid inversion. -/
def OperationPreservationGoal (S : Signature) (M : Model) (sig : OpSignature) : Prop :=
  SafetyAssumptions S M sig → ∀ Δ C Γ (E : EvalCtx) op ret clause v B ε,
    Value v → op ∉ E.handled →
    Typing S M sig Δ C Γ (.handle (E.plug (.perform op v)) op ret clause) B ε →
    Typing S M sig Δ C Γ
      (clause.openAt 0 [Expr.resume E op ret clause, v]) B ε

end EHMX
