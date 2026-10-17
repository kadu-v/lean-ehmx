import HMX.Syntax

namespace HMX

/-- Definition 10.2.5. A tagged carrier represents the disjoint many-kinded carriers.
Interpretations on ill-kinded argument lists are irrelevant and are never constrained. -/
structure Model where
  Carrier : Type
  kind : Carrier → Nat
  constructor : Nat → List Carrier → Carrier
  predicate : Nat → List Carrier → Prop
  below : Nat → Carrier → Carrier → Prop

abbrev Assignment (M : Model) := TVar → M.Carrier
abbrev GroundEnv (M : Model) := Id → Set M.Carrier

def Model.Requirements (S : Signature) (M : Model) : Prop :=
  S.Valid ∧
  (∀ k ∈ S.kinds, ∃ v, M.kind v = k) ∧
  (∀ f ∈ S.constructors, ∀ vs,
    List.Forall₂ (fun v p => M.kind v = p.2) vs (S.parameters f) →
    M.kind (M.constructor f vs) = S.result f) ∧
  (∀ k ∈ S.kinds, ∀ a, M.kind a = k → M.below k a a) ∧
  (∀ k ∈ S.kinds, ∀ a b c, M.kind a = k → M.kind b = k → M.kind c = k →
    M.below k a b → M.below k b c → M.below k a c) ∧
  (∀ k ∈ S.kinds, ∀ a b, M.kind a = k → M.kind b = k →
    M.below k a b → M.below k b a → a = b)

def Assignment.Valid (S : Signature) (M : Model) (ρ : Assignment M) : Prop :=
  ∀ X, X.1 ∈ S.kinds → M.kind (ρ X) = X.1

def GroundEnv.Valid (M : Model) (ι : GroundEnv M) : Prop :=
  ∀ x, (∀ a ∈ ι x, M.kind a = 0) ∧
    ∀ a b, a ∈ ι x → M.kind b = 0 → M.below 0 a b → b ∈ ι x

def Ty.eval (M : Model) (ρ : Assignment M) : Ty → M.Carrier
  | .var X => ρ X
  | .con f ts => M.constructor f (ts.map (Ty.eval M ρ))

def Predicate.eval (M : Model) : Predicate → List M.Carrier → Prop
  | .equal k, [a,b] => M.kind a = k ∧ M.kind b = k ∧ a = b
  | .sub k, [a,b] => M.kind a = k ∧ M.kind b = k ∧ M.below k a b
  | .other p, vs => M.predicate p vs
  | _, _ => False

def Assignment.AgreeOutside (ρ ρ' : Assignment M) (A : Vars) : Prop :=
  ∀ X, X ∉ A → ρ X = ρ' X

/- Definition 10.2.10 / Figure 10-5. An absent ground binding is represented by
an empty set; lookup is its only observable operation. -/
mutual
def Constraint.Holds (S : Signature) (M : Model) (ρ : Assignment M)
    (ι : GroundEnv M) : Constraint → Prop
  | .truth => True
  | .falsity => False
  | .atom p ts => p.eval M (ts.map (Ty.eval M ρ))
  | .conj C D => C.Holds S M ρ ι ∧ D.Holds S M ρ ι
  | .exists_ A C => ∃ ρ', ρ'.Valid S M ∧ ρ.AgreeOutside ρ' A ∧ C.Holds S M ρ' ι
  | .def_ x s C => C.Holds S M ρ (fun y => if y = x then s.denote S M ρ ι else ι y)
  | .inst x T => T.eval M ρ ∈ ι x
def Scheme.denote (S : Signature) (M : Model) (ρ : Assignment M)
    (ι : GroundEnv M) : Scheme → Set M.Carrier
  | .all A C T => {v | M.kind v = 0 ∧ ∃ ρ', ρ'.Valid S M ∧
      ρ.AgreeOutside ρ' A ∧ C.Holds S M ρ' ι ∧ M.below 0 (T.eval M ρ') v}
end

def Satisfiable (S : Signature) (M : Model) (C : Constraint) : Prop :=
  C.WF S ∧ ∃ ρ ι, ρ.Valid S M ∧ ι.Valid M ∧ C.Holds S M ρ ι

def Entails (S : Signature) (M : Model) (C D : Constraint) : Prop :=
  ∀ ρ ι, ρ.Valid S M → ι.Valid M → C.Holds S M ρ ι → D.Holds S M ρ ι

def Equivalent (S : Signature) (M : Model) (C D : Constraint) : Prop :=
  Entails S M C D ∧ Entails S M D C

/-- p.416: C-Arrow is an explicit requirement on the chosen model. -/
def ArrowLaw (S : Signature) (M : Model) : Prop :=
  ∀ T₁ T₂ U₁ U₂, T₁.HasKind S 0 → T₂.HasKind S 0 → U₁.HasKind S 0 → U₂.HasKind S 0 →
  Equivalent S M (.le 0 (.arrow T₁ T₂) (.arrow U₁ U₂))
    (.conj (.le 0 U₁ T₁) (.le 0 T₂ U₂))

def Incompatible (S : Signature) (M : Model) (f g : Nat) : Prop :=
  ∀ ts us, (Ty.con f ts).HasKind S (S.result f) →
    (Ty.con g us).HasKind S (S.result f) →
    Equivalent S M (.le (S.result f) (.con f ts) (.con g us)) .falsity ∧
    Equivalent S M (.le (S.result f) (.con g us) (.con f ts)) .falsity

def Isolation (S : Signature) (M : Model) (isolated : Set Nat) : Prop :=
  0 ∈ isolated ∧ isolated ⊆ S.constructors ∧
  ∀ f ∈ isolated, ∀ g ∈ isolated, f ≠ g → S.result f = S.result g → Incompatible S M f g

def Framework (S : Signature) (M : Model) (isolated : Set Nat) : Prop :=
  M.Requirements S ∧ ArrowLaw S M ∧ Isolation S M isolated

def Determines (S : Signature) (M : Model) (C : Constraint) (A : Vars) : Prop :=
  ∀ Γ : Env, Γ.WF S → ∀ ρ ρ' ι,
    ρ.Valid S M → ρ'.Valid S M → ι.Valid M →
    (Γ.defIn C).Holds S M ρ ι → (Γ.defIn C).Holds S M ρ' ι →
    ρ.AgreeOutside ρ' A → ∀ X ∈ A, ρ X = ρ' X

inductive Variance where
  | covariant
  | contravariant
  | invariant

def Variance.comparison (k : Nat) (T U : Ty) : Variance → Constraint
  | .covariant => .le k T U
  | .contravariant => .le k U T
  | .invariant => .eq k T U

/-- p.415: the argument index follows the ordered directions of p.401. -/
def ConstructorVariance (S : Signature) (M : Model) (f i : Nat) (v : Variance) : Prop :=
  ∀ ts T U k, ts[i]? = some T → (S.parameters f)[i]?.map Prod.snd = some k →
    (Ty.con f ts).HasKind S (S.result f) → U.HasKind S k →
    Equivalent S M (.le (S.result f) (.con f ts) (.con f (ts.set i U))) (v.comparison k T U)

end HMX
