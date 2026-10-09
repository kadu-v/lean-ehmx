import SystemFXi.EffectPoly

namespace SystemFXi.EHMX

abbrev Effect := SystemFXi.Poly.Effect

inductive BaseTy where
  | int | bool
  deriving DecidableEq

inductive Ty where
  | var : Nat → Ty
  | base : BaseTy → Ty
  | arr : Ty → Effect → Ty → Ty
  deriving DecidableEq

def Ty.rename (ρ : Nat → Nat) (η : Nat → Nat) : Ty → Ty
  | .var i => .var (ρ i)
  | .base b => .base b
  | .arr a ε b => .arr (a.rename ρ η) (ε.rename η) (b.rename ρ η)

def Effect.subst (θ : Nat → Effect) (ε : Effect) : Effect :=
  ⟨ε.labels ∪ ε.vars.biUnion (fun i => (θ i).labels),
    ε.vars.biUnion (fun i => (θ i).vars)⟩

structure Substitution where
  types : Nat → Ty
  effects : Nat → Effect

def Ty.subst (θ : Substitution) : Ty → Ty
  | .var i => θ.types i
  | .base b => .base b
  | .arr a ε b => .arr (a.subst θ) (ε.subst θ.effects) (b.subst θ)

inductive GroundTy where
  | atom : Nat → GroundTy
  | arr : GroundTy → Finset Op → GroundTy → GroundTy
  deriving DecidableEq

structure Valuation where
  types : Nat → GroundTy
  effects : Nat → Finset Op

def Ty.eval (ρ : Valuation) : Ty → GroundTy
  | .var i => ρ.types i
  | .base .int => .atom 0
  | .base .bool => .atom 1
  | .arr a ε b => .arr (a.eval ρ) (ε.eval ρ.effects) (b.eval ρ)

def Valuation.pullbackSubst (v : Valuation) (θ : Substitution) : Valuation :=
  ⟨fun i => (θ.types i).eval v, fun i => (θ.effects i).eval v.effects⟩

theorem Effect.eval_subst (ε : Effect) (θ : Nat → Effect)
    (ρ : Nat → Finset Op) :
    (ε.subst θ).eval ρ = ε.eval (fun i => (θ i).eval ρ) := by
  ext op
  simp [Effect.subst, Poly.Effect.eval, Finset.mem_biUnion,
    Finset.mem_union]
  aesop

theorem Ty.eval_subst (τ : Ty) (θ : Substitution) (v : Valuation) :
    (τ.subst θ).eval v = τ.eval (v.pullbackSubst θ) := by
  induction τ with
  | var i => rfl
  | base b => cases b <;> rfl
  | arr a ε b iha ihb =>
      simp [Ty.subst, Ty.eval, iha, ihb, Effect.eval_subst,
        Valuation.pullbackSubst]

/-- X contains static predicates, with the variable sets needed for generalization. -/
structure Domain where
  Pred : Type
  rename : (Nat → Nat) → (Nat → Nat) → Pred → Pred
  holds : Valuation → Pred → Prop
  fvTypes : Pred → Finset Nat
  fvEffects : Pred → Finset Nat

def Valuation.pullback (v : Valuation) (ρ η : Nat → Nat) : Valuation :=
  ⟨v.types ∘ ρ, v.effects ∘ η⟩

theorem Effect.eval_rename (ε : Effect) (η : Nat → Nat)
    (v : Valuation) :
    (ε.rename η).eval v.effects = ε.eval (v.effects ∘ η) := by
  ext op
  simp [Poly.Effect.eval, Poly.Effect.rename, Finset.mem_biUnion,
    Finset.mem_image]

theorem Ty.eval_rename (τ : Ty) (ρ η : Nat → Nat)
    (v : Valuation) :
    (τ.rename ρ η).eval v = τ.eval (v.pullback ρ η) := by
  induction τ with
  | var i => rfl
  | base b => cases b <;> rfl
  | arr a ε b iha ihb =>
      simp [Ty.rename, Ty.eval, iha, ihb, Effect.eval_rename,
        Valuation.pullback]

/-- A minimal semantic law required before completeness can quantify over X. -/
structure LawfulRename (X : Domain) : Prop where
  holds_rename : ∀ (ρ η : Nat → Nat) (p : X.Pred) (v : Valuation),
    X.holds v (X.rename ρ η p) ↔ X.holds (v.pullback ρ η) p

/-- HM(X)'s free-variable operation must really bound semantic dependence. -/
structure LawfulSupport (X : Domain) : Prop where
  holds_support : ∀ (p : X.Pred) (v w : Valuation),
    (∀ i ∈ X.fvTypes p, v.types i = w.types i) →
    (∀ i ∈ X.fvEffects p, v.effects i = w.effects i) →
    (X.holds v p ↔ X.holds w p)

/-- HM(X)'s substitution law, extended to the type and effect variable sorts. -/
structure LawfulSubst (X : Domain) where
  subst : Substitution → X.Pred → X.Pred
  holds_subst : ∀ (θ : Substitution) (p : X.Pred) (v : Valuation),
    X.holds v (subst θ p) ↔ X.holds (v.pullbackSubst θ) p

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
  | exTy : Nat → Constraint X → Constraint X
  | exEff : Nat → Constraint X → Constraint X

def Constraint.holds {X : Domain} (ρ : Valuation) : Constraint X → Prop
  | .top => True
  | .and c d => c.holds ρ ∧ d.holds ρ
  | .typeEq a b => a.eval ρ = b.eval ρ
  | .effectLe ε η => ε.eval ρ.effects ⊆ η.eval ρ.effects
  | .lacks op ε => op ∉ ε.eval ρ.effects
  | .predicate p => X.holds ρ p
  | .allTy i c => ∀ t, c.holds {ρ with types := Function.update ρ.types i t}
  | .allEff i c => ∀ ε, c.holds {ρ with effects := Function.update ρ.effects i ε}
  | .exTy i c => ∃ t, c.holds {ρ with types := Function.update ρ.types i t}
  | .exEff i c => ∃ ε, c.holds {ρ with effects := Function.update ρ.effects i ε}

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
  | .exTy i c => .exTy (ρ i) (c.rename ρ η)
  | .exEff i c => .exEff (η i) (c.rename ρ η)

def Ty.fvTypes : Ty → Finset Nat
  | .var i => {i}
  | .base _ => ∅
  | .arr a _ b => a.fvTypes ∪ b.fvTypes

def Ty.fvEffects : Ty → Finset Nat
  | .var _ => ∅
  | .base _ => ∅
  | .arr a ε b => a.fvEffects ∪ ε.vars ∪ b.fvEffects

theorem Ty.fvTypes_rename (τ : Ty) (ρ η : Nat → Nat) :
    (τ.rename ρ η).fvTypes = τ.fvTypes.image ρ := by
  induction τ with
  | var i => simp [Ty.rename, Ty.fvTypes]
  | base b => simp [Ty.rename, Ty.fvTypes]
  | arr a ε b iha ihb =>
      simp [Ty.rename, Ty.fvTypes, iha, ihb, Finset.image_union]

theorem Ty.fvEffects_rename (τ : Ty) (ρ η : Nat → Nat) :
    (τ.rename ρ η).fvEffects = τ.fvEffects.image η := by
  induction τ with
  | var i => simp [Ty.rename, Ty.fvEffects]
  | base b => simp [Ty.rename, Ty.fvEffects]
  | arr a ε b iha ihb =>
      simp [Ty.rename, Ty.fvEffects, iha, ihb,
        Poly.Effect.rename, Finset.image_union]

/-- Free-variable coherence for a static predicate domain. In HM(X), the
free-variable operation is defined by projection, so this is the ordinary
renaming law rather than a new solving capability. -/
structure LawfulFVRename (X : Domain) : Prop where
  types : ∀ (ρ η : Nat → Nat) (p : X.Pred),
    X.fvTypes (X.rename ρ η p) ⊆ (X.fvTypes p).image ρ
  effects : ∀ (ρ η : Nat → Nat) (p : X.Pred),
    X.fvEffects (X.rename ρ η p) ⊆ (X.fvEffects p).image η

theorem Effect.eval_support (ε : Effect) (v w : Valuation)
    (h : ∀ i ∈ ε.vars, v.effects i = w.effects i) :
    ε.eval v.effects = ε.eval w.effects := by
  unfold Poly.Effect.eval
  congr 1
  exact Finset.biUnion_congr rfl h

theorem Ty.eval_support (τ : Ty) (v w : Valuation)
    (ht : ∀ i ∈ τ.fvTypes, v.types i = w.types i)
    (he : ∀ i ∈ τ.fvEffects, v.effects i = w.effects i) :
    τ.eval v = τ.eval w := by
  induction τ with
  | var i => exact ht i (by simp [Ty.fvTypes])
  | base b => cases b <;> rfl
  | arr a ε b iha ihb =>
      simp only [Ty.eval]
      congr 1
      · exact iha (by
          intro i hi
          exact ht i (by simp [Ty.fvTypes, hi]))
          (by intro i hi; exact he i (by simp [Ty.fvEffects, hi]))
      · exact Effect.eval_support ε v w (by
          intro i hi
          exact he i (by simp [Ty.fvEffects, hi]))
      · exact ihb (by
          intro i hi
          exact ht i (by simp [Ty.fvTypes, hi]))
          (by intro i hi; exact he i (by simp [Ty.fvEffects, hi]))

def Constraint.fvTypes {X : Domain} : Constraint X → Finset Nat
  | .top => ∅
  | .and c d => c.fvTypes ∪ d.fvTypes
  | .typeEq a b => a.fvTypes ∪ b.fvTypes
  | .effectLe _ _ => ∅
  | .lacks _ _ => ∅
  | .predicate p => X.fvTypes p
  | .allTy i c => c.fvTypes.erase i
  | .allEff _ c => c.fvTypes
  | .exTy i c => c.fvTypes.erase i
  | .exEff _ c => c.fvTypes

def Constraint.fvEffects {X : Domain} : Constraint X → Finset Nat
  | .top => ∅
  | .and c d => c.fvEffects ∪ d.fvEffects
  | .typeEq a b => a.fvEffects ∪ b.fvEffects
  | .effectLe ε η => ε.vars ∪ η.vars
  | .lacks _ ε => ε.vars
  | .predicate p => X.fvEffects p
  | .allTy _ c => c.fvEffects
  | .allEff i c => c.fvEffects.erase i
  | .exTy _ c => c.fvEffects
  | .exEff i c => c.fvEffects.erase i

def Constraint.boundTypes {X : Domain} : Constraint X → Finset Nat
  | .and c d => c.boundTypes ∪ d.boundTypes
  | .allTy i c | .exTy i c => insert i c.boundTypes
  | .allEff _ c | .exEff _ c => c.boundTypes
  | _ => ∅

def Constraint.boundEffects {X : Domain} : Constraint X → Finset Nat
  | .and c d => c.boundEffects ∪ d.boundEffects
  | .allEff i c | .exEff i c => insert i c.boundEffects
  | .allTy _ c | .exTy _ c => c.boundEffects
  | _ => ∅

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

/-- Renamed scheme binders cannot capture a free name or a binder inside its
predicate constraint. -/
def Scheme.SafeRename {X : Domain} (σ : Scheme X)
    (ρ η : Nat → Nat) : Prop :=
  (σ.typeVars.image ρ).card = σ.typeVars.card ∧
  (σ.effectVars.image η).card = σ.effectVars.card ∧
  (σ.typeVars.image ρ) ∩
    (σ.fvTypes ∪ σ.predicates.boundTypes) = ∅ ∧
  (σ.effectVars.image η) ∩
    (σ.fvEffects ∪ σ.predicates.boundEffects) = ∅

structure OpDecl where
  typeVars : Finset Nat
  effectVars : Finset Nat
  input : Ty
  output : Ty

def OpDecl.AdmissibleRename (decl : OpDecl) (ρ η : Nat → Nat) : Prop :=
  (∀ i ∉ decl.typeVars, ρ i = i) ∧
  (∀ i ∉ decl.effectVars, η i = i)

def OpDecl.alphaRename (decl : OpDecl) (ρ η : Nat → Nat) : OpDecl :=
  { typeVars := decl.typeVars.image ρ
    effectVars := decl.effectVars.image η
    input := decl.input.rename ρ η
    output := decl.output.rename ρ η }

/-- The renamed binders stay distinct and cannot capture free signature names. -/
def OpDecl.AlphaSafe (decl : OpDecl) (ρ η : Nat → Nat) : Prop :=
  (decl.typeVars.image ρ).card = decl.typeVars.card ∧
  (decl.effectVars.image η).card = decl.effectVars.card ∧
  (decl.typeVars.image ρ) ∩
    ((decl.input.fvTypes ∪ decl.output.fvTypes) \ decl.typeVars) = ∅ ∧
  (decl.effectVars.image η) ∩
    ((decl.input.fvEffects ∪ decl.output.fvEffects) \ decl.effectVars) = ∅

/-- Operation-bound variables cannot escape into the handler's outer result. -/
def OpDecl.HandlerScope {X : Domain} (decl : OpDecl)
    (Γ : Context X) (τin a : Ty) (εin εr δ χ : Effect) : Prop :=
  decl.typeVars ∩ (Γ.fvTypes ∪ τin.fvTypes ∪ a.fvTypes) = ∅ ∧
  decl.effectVars ∩
    (Γ.fvEffects ∪ τin.fvEffects ∪ a.fvEffects ∪
      εin.vars ∪ εr.vars ∪ δ.vars ∪ χ.vars) = ∅

/-- Names hidden in a clause are disjoint from the operation binders and
all data fixed before the clause is checked. -/
def OpDecl.ClauseScope {X : Domain} (decl : OpDecl) (Γ : Context X)
    (outer : Constraint X) (τin a : Ty)
    (εin εr δ χ : Effect) (localTypes localEffects : Finset Nat) : Prop :=
  decl.typeVars ∩ outer.fvTypes = ∅ ∧
  decl.effectVars ∩ outer.fvEffects = ∅ ∧
  localTypes ∩ (Γ.fvTypes ∪ outer.fvTypes ∪
    τin.fvTypes ∪ a.fvTypes ∪
    decl.typeVars ∪ decl.input.fvTypes ∪ decl.output.fvTypes) = ∅ ∧
  localEffects ∩ (Γ.fvEffects ∪ outer.fvEffects ∪
    τin.fvEffects ∪ a.fvEffects ∪
    εin.vars ∪ εr.vars ∪ δ.vars ∪ χ.vars ∪
    decl.effectVars ∪ decl.input.fvEffects ∪ decl.output.fvEffects) = ∅

abbrev Signature := Op → Option OpDecl

/-- All names occurring in an operation type are bound by its signature. -/
def OpDecl.Closed (decl : OpDecl) : Prop :=
  decl.input.fvTypes ∪ decl.output.fvTypes ⊆ decl.typeVars ∧
  decl.input.fvEffects ∪ decl.output.fvEffects ⊆ decl.effectVars

def Signature.Closed (sig : Signature) : Prop :=
  ∀ op decl, sig op = some decl → decl.Closed

inductive Expr where
  | var : Nat → Expr
  | int : Int → Expr
  | bool : Bool → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  | letE : Expr → Expr → Expr
  | perform : Op → Expr → Expr
  | handle : Expr → Op → Expr → Expr → Expr
  deriving DecidableEq

inductive Value : Expr → Prop where
  | var (i : Nat) : Value (.var i)
  | int (n : Int) : Value (.int n)
  | bool (b : Bool) : Value (.bool b)
  | lam (body : Expr) : Value (.lam body)

def Expr.isValue : Expr → Bool
  | .var _ | .int _ | .bool _ | .lam _ => true
  | _ => false

theorem Expr.isValue_iff {e : Expr} : e.isValue = true ↔ Value e := by
  cases e <;> simp [Expr.isValue]
  · exact Value.var _
  · exact Value.int _
  · exact Value.bool _
  · exact Value.lam _
  all_goals intro h; cases h

end SystemFXi.EHMX
