import SystemFXi.EffectPoly

namespace SystemFXi.EHMX

abbrev Effect := SystemFXi.Poly.Effect

inductive Ty where
  | var : Nat → Ty
  | arr : Ty → Effect → Ty → Ty
  deriving DecidableEq

def Ty.rename (ρ : Nat → Nat) (η : Nat → Nat) : Ty → Ty
  | .var i => .var (ρ i)
  | .arr a ε b => .arr (a.rename ρ η) (ε.rename η) (b.rename ρ η)

inductive GroundTy where
  | atom : Nat → GroundTy
  | arr : GroundTy → Finset Op → GroundTy → GroundTy
  deriving DecidableEq

structure Valuation where
  types : Nat → GroundTy
  effects : Nat → Finset Op

def Ty.eval (ρ : Valuation) : Ty → GroundTy
  | .var i => ρ.types i
  | .arr a ε b => .arr (a.eval ρ) (ε.eval ρ.effects) (b.eval ρ)

/-- X contains static predicates, with the variable sets needed for generalization. -/
structure Domain where
  Pred : Type
  rename : (Nat → Nat) → (Nat → Nat) → Pred → Pred
  holds : Valuation → Pred → Prop
  fvTypes : Pred → Finset Nat
  fvEffects : Pred → Finset Nat

/-- `Split` is a derived triple of primitive effect constraints. -/
inductive Constraint (X : Domain) where
  | top : Constraint X
  | and : Constraint X → Constraint X → Constraint X
  | typeEq : Ty → Ty → Constraint X
  | effectLe : Effect → Effect → Constraint X
  | lacks : Op → Effect → Constraint X
  | predicate : X.Pred → Constraint X
  | allTy : Nat → Constraint X → Constraint X
  | allEff : Nat → Constraint X → Constraint X

def Constraint.holds {X : Domain} (ρ : Valuation) : Constraint X → Prop
  | .top => True
  | .and c d => c.holds ρ ∧ d.holds ρ
  | .typeEq a b => a.eval ρ = b.eval ρ
  | .effectLe ε η => ε.eval ρ.effects ⊆ η.eval ρ.effects
  | .lacks op ε => op ∉ ε.eval ρ.effects
  | .predicate p => X.holds ρ p
  | .allTy i c => ∀ t, c.holds {ρ with types := Function.update ρ.types i t}
  | .allEff i c => ∀ ε, c.holds {ρ with effects := Function.update ρ.effects i ε}

def Constraint.Entails {X : Domain} (c d : Constraint X) : Prop :=
  ∀ ρ, c.holds ρ → d.holds ρ

theorem Constraint.entails_refl {X : Domain} (c : Constraint X) : c.Entails c :=
  fun _ h => h

theorem Constraint.entails_left {X : Domain} (c d : Constraint X) :
    (Constraint.and c d).Entails c := fun _ h => h.1

theorem Constraint.entails_right {X : Domain} (c d : Constraint X) :
    (Constraint.and c d).Entails d := fun _ h => h.2

theorem Constraint.entails_trans {X : Domain} {a b c : Constraint X}
    (hab : a.Entails b) (hbc : b.Entails c) : a.Entails c :=
  fun ρ h => hbc ρ (hab ρ h)

def Constraint.rename {X : Domain} (ρ η : Nat → Nat) : Constraint X → Constraint X
  | .top => .top
  | .and c d => .and (c.rename ρ η) (d.rename ρ η)
  | .typeEq a b => .typeEq (a.rename ρ η) (b.rename ρ η)
  | .effectLe ε ζ => .effectLe (ε.rename η) (ζ.rename η)
  | .lacks op ε => .lacks op (ε.rename η)
  | .predicate p => .predicate (X.rename ρ η p)
  | .allTy i c => .allTy (ρ i) (c.rename ρ η)
  | .allEff i c => .allEff (η i) (c.rename ρ η)

def Ty.fvTypes : Ty → Finset Nat
  | .var i => {i}
  | .arr a _ b => a.fvTypes ∪ b.fvTypes

def Ty.fvEffects : Ty → Finset Nat
  | .var _ => ∅
  | .arr a ε b => a.fvEffects ∪ ε.vars ∪ b.fvEffects

def Constraint.fvTypes {X : Domain} : Constraint X → Finset Nat
  | .top => ∅
  | .and c d => c.fvTypes ∪ d.fvTypes
  | .typeEq a b => a.fvTypes ∪ b.fvTypes
  | .effectLe _ _ => ∅
  | .lacks _ _ => ∅
  | .predicate p => X.fvTypes p
  | .allTy i c => c.fvTypes.erase i
  | .allEff _ c => c.fvTypes

def Constraint.fvEffects {X : Domain} : Constraint X → Finset Nat
  | .top => ∅
  | .and c d => c.fvEffects ∪ d.fvEffects
  | .typeEq a b => a.fvEffects ∪ b.fvEffects
  | .effectLe ε η => ε.vars ∪ η.vars
  | .lacks _ ε => ε.vars
  | .predicate p => X.fvEffects p
  | .allTy _ c => c.fvEffects
  | .allEff i c => c.fvEffects.erase i

def Constraint.split {X : Domain} (op : Op) (ε δ : Effect) : Constraint X :=
  .and (.effectLe δ ε)
    (.and (.effectLe ε (Poly.Effect.singleton op ∪ δ)) (.lacks op δ))

structure Scheme (X : Domain) where
  typeVars : Finset Nat
  effectVars : Finset Nat
  predicates : Constraint X
  result : Ty

def Scheme.mono {X : Domain} (τ : Ty) : Scheme X :=
  ⟨∅, ∅, .top, τ⟩

def Scheme.fvTypes {X : Domain} (σ : Scheme X) : Finset Nat :=
  (σ.result.fvTypes ∪ σ.predicates.fvTypes) \ σ.typeVars

def Scheme.fvEffects {X : Domain} (σ : Scheme X) : Finset Nat :=
  (σ.result.fvEffects ∪ σ.predicates.fvEffects) \ σ.effectVars

abbrev Context (X : Domain) := List (Scheme X)

def Context.fvTypes {X : Domain} (Γ : Context X) : Finset Nat :=
  Γ.foldl (fun acc σ => acc ∪ σ.fvTypes) ∅

def Context.fvEffects {X : Domain} (Γ : Context X) : Finset Nat :=
  Γ.foldl (fun acc σ => acc ∪ σ.fvEffects) ∅

def Scheme.generalize {X : Domain} (Γ : Context X) (c : Constraint X)
    (τ : Ty) : Scheme X :=
  { typeVars := (τ.fvTypes ∪ c.fvTypes) \ Γ.fvTypes
    effectVars := (τ.fvEffects ∪ c.fvEffects) \ Γ.fvEffects
    predicates := c
    result := τ }

def Scheme.instantiate {X : Domain} (σ : Scheme X)
    (ρ η : Nat → Nat) : Ty × Constraint X :=
  (σ.result.rename ρ η, σ.predicates.rename ρ η)

def Scheme.AdmissibleRename {X : Domain} (σ : Scheme X)
    (ρ η : Nat → Nat) : Prop :=
  (∀ i ∉ σ.typeVars, ρ i = i) ∧
  (∀ i ∉ σ.effectVars, η i = i)

structure OpDecl where
  typeVars : Finset Nat
  effectVars : Finset Nat
  input : Ty
  output : Ty

def OpDecl.AdmissibleRename (decl : OpDecl) (ρ η : Nat → Nat) : Prop :=
  (∀ i ∉ decl.typeVars, ρ i = i) ∧
  (∀ i ∉ decl.effectVars, η i = i)

/-- Operation-bound variables cannot escape into the handler's outer result. -/
def OpDecl.HandlerScope {X : Domain} (decl : OpDecl)
    (Γ : Context X) (τin a : Ty) (εin εr δ χ : Effect) : Prop :=
  decl.typeVars ∩ (Γ.fvTypes ∪ τin.fvTypes ∪ a.fvTypes) = ∅ ∧
  decl.effectVars ∩
    (Γ.fvEffects ∪ τin.fvEffects ∪ a.fvEffects ∪
      εin.vars ∪ εr.vars ∪ δ.vars ∪ χ.vars) = ∅

abbrev Signature := Op → Option OpDecl

inductive Expr where
  | var : Nat → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  | letE : Expr → Expr → Expr
  | perform : Op → Expr → Expr
  | handle : Expr → Op → Expr → Expr → Expr
  deriving DecidableEq

inductive Value : Expr → Prop where
  | var (i : Nat) : Value (.var i)
  | lam (body : Expr) : Value (.lam body)

def Expr.isValue : Expr → Bool
  | .var _ | .lam _ => true
  | _ => false

theorem Expr.isValue_iff {e : Expr} : e.isValue = true ↔ Value e := by
  cases e <;> simp [Expr.isValue]
  · exact Value.var _
  · exact Value.lam _
  all_goals intro h; cases h

end SystemFXi.EHMX
