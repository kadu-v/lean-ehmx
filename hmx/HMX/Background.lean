import HMX.Semantics

/-! Chapter 2. Source transcription, including the unbound substitutions in
Figure 2.2 and the beta/alpha discrepancy in the generic-instance sentence.
Those are parameters, not corrections to Robinson or Damas–Milner. -/
namespace HMX.HM
noncomputable section
local instance backgroundDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
local instance backgroundDecidable (p : Prop) : Decidable p := Classical.propDecidable p
universe u v d
variable {V : Type u} {K : Type v} {arity : K → Nat} {N Const : Type}

structure Scheme (V : Type u) (K : Type v) (arity : K → Nat) where
  bound : Finset V
  body : Ty V K arity

def Scheme.fv (s : Scheme V K arity) : Finset V := s.body.fv \ s.bound
abbrev Scheme.mono (t : Ty V K arity) : Scheme V K arity := ⟨∅, t⟩
abbrev Env (N : Type) (V : Type u) (K : Type v) (arity : K → Nat) :=
  List (N × Scheme V K arity)
def envFV (Γ : Env N V K arity) : Finset V := Γ.foldr (fun p A => p.2.fv ∪ A) ∅
def lookup (Γ : Env N V K arity) (x : N) : Option (Scheme V K arity) :=
  (Γ.find? fun p => p.1 = x).map Prod.snd
def extend (Γ : Env N V K arity) (x : N) (s : Scheme V K arity) : Env N V K arity :=
  (x,s) :: Γ.filter (fun p => p.1 ≠ x)

def Scheme.rename (π : Equiv.Perm V) (s : Scheme V K arity) : Scheme V K arity :=
  ⟨s.bound.image π, s.body.subst (fun a => if a ∈ s.bound then .var (π a) else .var a)⟩
inductive Scheme.Alpha : Scheme V K arity → Scheme V K arity → Prop
  | refl (s) : Alpha s s
  | rename (s) (π : Equiv.Perm V) (fresh : Disjoint (s.bound.image π) s.fv) : Alpha s (s.rename π)
  | symm : Alpha s t → Alpha t s
  | trans : Alpha s t → Alpha t u → Alpha s u

def Scheme.Substitutes (φ : Assignment V K arity) (s t : Scheme V K arity) : Prop :=
  ∃ r, s.Alpha r ∧ Disjoint (r.bound : Set V) φ.codomain ∧
    Scheme.Alpha ⟨r.bound, r.body.subst (φ.without r.bound)⟩ t

def EnvSubstitutes (φ : Assignment V K arity) (Γ Δ : Env N V K arity) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2.Substitutes φ q.2) Γ Δ

def gen (Γ : Env N V K arity) (t : Ty V K arity) : Scheme V K arity :=
  ⟨t.fv \ envFV Γ, t⟩

/-- p.15 literally substitutes for the target's beta variables, not source alpha.
The list-length discrepancy is retained in the source note HM-GENERIC. -/
def GenericInstancePrinted (s t : Scheme V K arity) : Prop :=
  ∃ φ : Assignment V K arity, φ.IsSubstitution ∧ φ.domain ⊆ (t.bound : Set V) ∧
    t.body = s.body.subst φ ∧ Disjoint t.bound s.fv

inductive Typing : Env (N ⊕ Const) V K arity → Expr N Const → Scheme V K arity → Prop
  | var (h : lookup Γ (.inl x) = some s) : Typing Γ (.var x) s
  | constant (h : lookup Γ (.inr c) = some s) : Typing Γ (.constant c) s
  | abs (unbound : lookup Γ (.inl x) = none) (d : Typing (extend Γ (.inl x) (.mono t)) e (.mono u)) :
      Typing Γ (.lam x e) (.mono (.arrow t u))
  | app (f : Typing Γ e (.mono (.arrow t u))) (a : Typing Γ b (.mono t)) :
      Typing Γ (.app e b) (.mono u)
  | letE (unbound : lookup Γ (.inl x) = none) (d : Typing Γ e s) (b : Typing (extend Γ (.inl x) s) e' (.mono t)) :
      Typing Γ (.letE x e e') (.mono t)
  | intro (d : Typing Γ e (.mono t)) (fresh : Disjoint A (envFV Γ)) : Typing Γ e ⟨A,t⟩
  | elim (d : Typing Γ e ⟨A,t⟩) (φ : Assignment V K arity)
      (finite : φ.IsSubstitution) (domain : φ.domain ⊆ (A : Set V)) : Typing Γ e (.mono (t.subst φ))
  | alpha (d : Typing Γ e s) (h : s.Alpha t) : Typing Γ e t

def Unifier (t u : Ty V K arity) (φ : Assignment V K arity) : Prop :=
  φ.IsSubstitution ∧ t.subst φ = u.subst φ

def MGU (t u : Ty V K arity) (ψ : Assignment V K arity) : Prop :=
  Unifier t u ψ ∧ ∀ φ, Unifier t u φ → ∃ ρ : Assignment V K arity, ρ.IsSubstitution ∧ φ = ρ.comp ψ

def MoreGeneral (ψ φ : Assignment V K arity) : Prop :=
  ψ.IsSubstitution ∧ φ.IsSubstitution ∧ ∃ ρ : Assignment V K arity, ρ.IsSubstitution ∧ φ = ρ.comp ψ

def LUB (φ ψ θ : Assignment V K arity) : Prop :=
  MoreGeneral φ θ ∧ MoreGeneral ψ θ ∧
  ∀ ρ, MoreGeneral φ ρ → MoreGeneral ψ ρ → MoreGeneral θ ρ

abbrev Unify (V : Type u) (K : Type v) (arity : K → Nat) :=
  Ty V K arity → Ty V K arity → Option (Assignment V K arity)
def Unify.Specification (unify : Unify V K arity) : Prop :=
  ∀ t u, (∀ ψ, unify t u = some ψ → MGU t u ψ) ∧
    (unify t u = none ↔ ¬ ∃ ψ, Unifier t u ψ)

/-- Figure 2.2, without repairing its unbound psi-prime in App or psi in Let. -/
inductive Inference (unify : Unify V K arity) : Assignment V K arity →
    Env (N ⊕ Const) V K arity → Expr N Const → Ty V K arity → Prop
  | var (h : lookup Γ (.inl x) = some s)
      (π : Assignment V K arity) (fresh : Freshening s.bound (envFV Γ) π) :
      Inference unify Assignment.id Γ (.var x) (s.body.subst π)
  | constant (h : lookup Γ (.inr c) = some s)
      (π : Assignment V K arity) (fresh : Freshening s.bound (envFV Γ) π) :
      Inference unify Assignment.id Γ (.constant c) (s.body.subst π)
  | abs (unbound : lookup Γ (.inl x) = none) (d : Inference unify ψ (extend Γ (.inl x) (.mono (.var a))) e t)
      (fresh : a ∉ envFV Γ) : Inference unify (ψ.without {a}) Γ (.lam x e) (.arrow (ψ a) t)
  | app (f : Inference unify ψ₁ Γ e t) (b : Inference unify ψ₂ Γ e' u)
      (a : V) (fresh : a ∉ envFV Γ ∪ t.fv ∪ u.fv)
      (unifies : unify t (.arrow u (.var a)) = some ψ₃)
      (combine : LUB ψ₁ ψ₂ θ) (combine' : LUB θ ψ₃ ψ)
      (unboundPsiPrime : Assignment V K arity) :
      Inference unify (ψ.restrict (envFV Γ)) Γ (.app e e') ((ψ.comp unboundPsiPrime) a)
  | letE (unbound : lookup Γ (.inl x) = none) (d : Inference unify ψ₁ Γ e t)
      (b : Inference unify ψ₂ (extend Γ (.inl x) (gen Γ t)) e' u)
      (combine : LUB ψ₁ ψ₂ ψ') (unboundPsi : Assignment V K arity) :
      Inference unify (unboundPsi.restrict (envFV Γ)) Γ (.letE x e e') (u.subst unboundPsi)

structure Meaning (N Const : Type) (V : Type u) (K : Type v) (arity : K → Nat) (D : Type d) where
  wrong : D
  term : Expr N Const → (N ⊕ Const → D) → D
  scheme : Scheme V K arity → Set D

def Meaning.Models (M : Meaning N Const V K arity D) (η : N ⊕ Const → D)
    (Γ : Env (N ⊕ Const) V K arity) : Prop :=
  envFV Γ = ∅ ∧ ∀ x s, lookup Γ x = some s → η x ∈ M.scheme s

namespace Statement
variable {D : Type d} (M : Meaning N Const V K arity D)

def lemma1 [PartialOrder D] : Prop := ∀ s, s.fv = ∅ → DomainIdeal (M.scheme s) ∧ M.wrong ∉ M.scheme s

def theorem1 : Prop := ∀ (Γ Δ : Env (N ⊕ Const) V K arity) e s s' φ η,
  Typing Γ e s → φ.IsSubstitution → EnvSubstitutes φ Γ Δ → s.Substitutes φ s' →
  envFV Δ = ∅ → s'.fv = ∅ → M.Models η Δ →
    M.wrong ∉ M.scheme s' ∧ M.term e η ∈ M.scheme s'

def theorem2 : Prop := ∀ t u : Ty V K arity,
  (∃ ψ, MGU t u ψ ∧ ∀ φ, MGU t u φ → ∃ π : Assignment V K arity, π.IsRenaming ∧ φ = π.comp ψ) ∨
    ¬ ∃ φ, Unifier t u φ

def theorem3 (unify : Unify V K arity) : Prop := unify.Specification →
  ∀ ψ (Γ Δ : Env (N ⊕ Const) V K arity) e t, Inference unify ψ Γ e t →
    EnvSubstitutes ψ Γ Δ → Typing Δ e (.mono t) ∧ t.subst ψ = t

def theorem4 (unify : Unify V K arity) : Prop := unify.Specification →
  ∀ φ (Γ Δ : Env (N ⊕ Const) V K arity) e s,
    φ.IsSubstitution → EnvSubstitutes φ Γ Δ → Typing Δ e s →
    ∃ ψ ρ t Ψ so, ρ.IsSubstitution ∧ Inference unify ψ Γ e t ∧
      EnvSubstitutes ψ Γ Ψ ∧ (gen Ψ t).Substitutes ρ so ∧ GenericInstancePrinted so s

def corollary1 (unify : Unify V K arity) : Prop := unify.Specification →
  ∀ (Γ : Env (N ⊕ Const) V K arity) e s,
    Typing Γ e s → envFV Γ = ∅ → s.fv = ∅ →
    ∃ t, Inference unify Assignment.id Γ e t ∧ GenericInstancePrinted (gen Γ t) s
end Statement
end
end HMX.HM
