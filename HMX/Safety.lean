import HMX.Inference
import HMX.Operational

namespace HMX

/-- Lemma 10.5.1: capture-avoiding term substitution. -/
def lemma10_5_1 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ z A t u v T U, T.HasKind S 0 → U.HasKind S 0 →
    (∀ X ∈ A, X.1 ∈ S.kinds) → Expr.Substitutes z u t v →
    Entails S M (.let_ (.var z) (.all A (generate u U) U) (generate t T)) (generate v T)

/-- Definition 10.5.2. The source's finite-environment/infinite-Q tension is
retained, not resolved by assuming Q finite; see audit ambiguity A-02. -/
def InitialEnvironment (S : Signature) (M : Model) (L : Language) (Γ₀ : Env) : Prop :=
  Γ₀.WF S ∧ (∀ x, x ∈ Γ₀.dpi ↔ ∃ c ∈ L.constants, x = .const c) ∧
    Γ₀.fv = ∅ ∧ Γ₀.fpi = ∅ ∧ Equivalent S M Γ₀.exists_ .truth

/-- Definition 10.5.3: ref is invariant and isolated. -/
def ReferenceConstructor (S : Signature) (M : Model) (I : Set Nat) (ref : Nat) : Prop :=
  ref ∈ I ∧ S.result ref = 0 ∧ (∃ d, S.parameters ref = [(d,0)]) ∧
  ∀ T U, T.HasKind S 0 → U.HasKind S 0 →
    Equivalent S M (.le 0 (.con ref [T]) (.con ref [U])) (.eq 0 T U)

abbrev StoreType := List (Nat × Ty)
def StoreType.dom (N : StoreType) : Finset Nat := (N.map Prod.fst).toFinset
def StoreType.fv (N : StoreType) : Vars := (N.map (fun p => p.2.fv)).foldr (· ∪ ·) ∅
def StoreType.WF (S : Signature) (N : StoreType) : Prop :=
  (N.map Prod.fst).Nodup ∧ ∀ p ∈ N, p.2.HasKind S 0

def StoreType.Extends (N' N : StoreType) : Prop := ∀ p ∈ N, p ∈ N'

def StoreType.refEnv (ref : Nat) (N : StoreType) : Env :=
  N.map (fun p => (.loc p.1, .mono (.con ref [p.2])))

/-- Used only with matching domains and well-formed finite maps. -/
def generateStore (μ : Store) (N : StoreType) : Constraint :=
  μ.foldr (fun p C => match N.find? (fun q => q.1 == p.1) with
    | some q => .conj (generate p.2 q.2) C
    | none => .falsity) .truth

def generateConfig (p : Config) (T : Ty) (N : StoreType) : Constraint :=
  .conj (generate p.term T) (generateStore p.store N)

def configConstraint (Γ₀ : Env) (ref : Nat) (p : Config) (T : Ty) (N : StoreType) : Constraint :=
  (Γ₀ ++ N.refEnv ref).letIn (generateConfig p T N)

def Config.WellTyped (S : Signature) (M : Model) (L : Language) (Γ₀ : Env)
    (ref : Nat) (p : Config) : Prop :=
  p.Closed L ∧ ∃ T N, T.HasKind S 0 ∧ N.WF S ∧ p.store.dom = N.dom ∧
    Satisfiable S M (configConstraint Γ₀ ref p T N)

/-- Definition 10.5.4, including both freshness and the upper bound on fv(M'). -/
def Config.Approximates (S : Signature) (M : Model) (Γ₀ : Env) (ref : Nat)
    (p q : Config) : Prop :=
  ∀ T N, T.HasKind S 0 → N.WF S → p.store.dom = N.dom →
    ∃ A N', (∀ X ∈ A, X.1 ∈ S.kinds) ∧ N'.WF S ∧ Disjoint A (T.fv ∪ N.fv) ∧
      N'.fv ⊆ A ∪ N.fv ∧ N'.dom = q.store.dom ∧ N'.Extends N ∧
      Entails S M (configConstraint Γ₀ ref p T N)
        (.exists_ A (configConstraint Γ₀ ref q T N'))

/-- The two alternatives of 10.5.6. In the restricted calculus, configurations
and δ are relations on the syntactically restricted universe. -/
inductive SafetyMode where
  | pure
  | valueRestricted
  deriving DecidableEq

def SafetyMode.Admitted (L : Language) : SafetyMode → Config → Prop
  | .pure, _ => True
  | .valueRestricted, p => p.ValueRestricted L

def SafetyMode.delta (L : Language) (mode : SafetyMode) (δ : Delta) : Delta :=
  fun p q => mode.Admitted L p ∧ mode.Admitted L q ∧ δ p q

def SafetyMode.reduce (L : Language) (mode : SafetyMode) (δ : Delta) (p q : Config) : Prop :=
  mode.Admitted L p ∧ mode.Admitted L q ∧ Reduce L (mode.delta L δ) p q

def SafetyMode.Requirement (mode : SafetyMode) (δ : Delta) : Prop :=
  mode = .pure → PureSemantics δ

/-- Definition 10.5.5: only the two obligations for constants, not general safety. -/
def ConstantsAdequate (S : Signature) (M : Model) (L : Language) (Γ₀ : Env)
    (ref : Nat) (mode : SafetyMode) (δ : Delta) : Prop :=
  (∀ p q, mode.delta L δ p q → p.Approximates S M Γ₀ ref q) ∧
  (∀ c vs μ, c ∈ L.constants → (∀ v ∈ vs, Value L v) →
    mode.Admitted L ⟨Expr.apply c vs, μ⟩ →
    Config.WellTyped S M L Γ₀ ref ⟨Expr.apply c vs, μ⟩ →
    (∃ q, mode.reduce L δ ⟨Expr.apply c vs, μ⟩ q) ∨ Value L (Expr.apply c vs))

/-- Source assumptions shared by 10.5.8–11; no general preservation/progress
conclusion is made an assumption. -/
def SafetyAssumptions (S : Signature) (M : Model) (L : Language) (I : Set Nat)
    (Γ₀ : Env) (ref : Nat) (mode : SafetyMode) (δ : Delta) : Prop :=
  Framework S M I ∧ InitialEnvironment S M L Γ₀ ∧ ReferenceConstructor S M I ref ∧
  (mode.delta L δ).Requirements L ∧ mode.Requirement δ ∧
  ConstantsAdequate S M L Γ₀ ref mode δ

/-- Lemma 10.5.7: remove the let-context production on the restricted universe. -/
def lemma10_5_7 (L : Language) (δ : Delta) : Prop :=
  δ.Requirements L → ∀ p q, p.ValueRestricted L → q.ValueRestricted L →
    (Reduce L δ p q ↔ ReduceWith L δ false p q)

def theorem10_5_8_subjectReduction (S : Signature) (M : Model) (L : Language)
    (I : Set Nat) (Γ₀ : Env) (ref : Nat) (mode : SafetyMode) (δ : Delta) : Prop :=
  SafetyAssumptions S M L I Γ₀ ref mode δ → ∀ p q,
    mode.reduce L δ p q → p.Approximates S M Γ₀ ref q

def corollary10_5_9 (S : Signature) (M : Model) (L : Language)
    (I : Set Nat) (Γ₀ : Env) (ref : Nat) (mode : SafetyMode) (δ : Delta) : Prop :=
  SafetyAssumptions S M L I Γ₀ ref mode δ → ∀ p q,
    mode.reduce L δ p q → p.WellTyped S M L Γ₀ ref → q.WellTyped S M L Γ₀ ref

def theorem10_5_10_progress (S : Signature) (M : Model) (L : Language)
    (I : Set Nat) (Γ₀ : Env) (ref : Nat) (mode : SafetyMode) (δ : Delta) : Prop :=
  SafetyAssumptions S M L I Γ₀ ref mode δ → ∀ p, mode.Admitted L p →
    p.WellTyped S M L Γ₀ ref → (∃ q, mode.reduce L δ p q) ∨ Value L p.term

def SafetyMode.goesWrong (L : Language) (mode : SafetyMode) (δ : Delta) (t : Expr) : Prop :=
  t.Closed ∧ t.Source ∧ ∃ q,
    Relation.ReflTransGen (mode.reduce L δ) ⟨t, []⟩ q ∧
    q.Closed L ∧ mode.Admitted L q ∧ ¬ (∃ r, mode.reduce L δ q r) ∧ ¬ Value L q.term

def theorem10_5_11_typeSoundness (S : Signature) (M : Model) (L : Language)
    (I : Set Nat) (Γ₀ : Env) (ref : Nat) (mode : SafetyMode) (δ : Delta) : Prop :=
  SafetyAssumptions S M L I Γ₀ ref mode δ → ∀ t,
    t.Source → mode.Admitted L ⟨t, []⟩ → Config.WellTyped S M L Γ₀ ref ⟨t, []⟩ →
    ¬ mode.goesWrong L δ t

end HMX
