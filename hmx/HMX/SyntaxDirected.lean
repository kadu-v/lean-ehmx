import HMX.Judgments

namespace HMX
noncomputable section
local instance syntaxDirectedDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
universe u v w
variable {V : Type u} {K : Type v} {arity : K → Nat} {P : Type w} {parity : P → Nat}

/-- Figure 3.2: neither an arbitrary forall-introduction rule nor an arbitrary
    forall-elimination rule occurs in this relation. -/
inductive SyntaxDirected (X : ConstraintTheory V K arity P parity)
    (S : Set (Constraint V K arity P parity)) : Constraint V K arity P parity →
    Environment (N ⊕ Const) V K arity P parity → Expr N Const → Ty V K arity → Prop where
  | var (lookup : Γ.lookup (.inl x) = some s) (i : Instance X S C s (.type t))
      (ok : JudgmentAdmissible X S C Γ (.type t)) : SyntaxDirected X S C Γ (.var x) t
  | constant (lookup : Γ.lookup (.inr c) = some s) (i : Instance X S C s (.type t))
      (ok : JudgmentAdmissible X S C Γ (.type t)) : SyntaxDirected X S C Γ (.constant c) t
  | abs (d : SyntaxDirected X S C (Γ.extend (.inl x) (.type t)) e u)
      (ok : JudgmentAdmissible X S C Γ (.type (.arrow t u))) : SyntaxDirected X S C Γ (.lam x e) (.arrow t u)
  | app (f : SyntaxDirected X S C Γ e₁ (.arrow t u)) (a : SyntaxDirected X S C Γ e₂ t) :
      SyntaxDirected X S C Γ (.app e₁ e₂) u
  | sub (d : SyntaxDirected X S C Γ e t) (h : X.Entails C (Constraint.le t u)) : SyntaxDirected X S C Γ e u
  | letE (d : SyntaxDirected X S C Γ e t) (g : Generalizes X S C Γ (.type t) C' s)
      (b : SyntaxDirected X S C'' (Γ.extend (.inl x) s) e' u)
      (solvedConjunction : JudgmentAdmissible X S (C' ∪ C'') Γ (.type u)) :
      SyntaxDirected X S (C' ∪ C'') Γ (.letE x e e') u
  | equ (d : SyntaxDirected X S C Γ e t) (h : X.Equivalent C D)
      (ok : JudgmentAdmissible X S D Γ (.type t)) : SyntaxDirected X S D Γ e t
end
end HMX
