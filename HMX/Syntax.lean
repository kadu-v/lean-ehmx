import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic

/-! ATTAPL §10.1–10.2. Countable alphabets are encoded by natural numbers.
Kinds/directions/symbols outside the signature's declared sets are excluded by WF.
Lists of arguments follow the ordering of directions specified on p.401. -/
namespace HMX

abbrev TVar := Nat × Nat
abbrev Vars := Finset TVar

inductive Id where
  | var : Nat → Id
  | loc : Nat → Id
  | const : Nat → Id
  deriving DecidableEq, Repr

inductive Expr where
  | ident : Id → Expr
  | lam : Nat → Expr → Expr
  | app : Expr → Expr → Expr
  | letE : Nat → Expr → Expr → Expr
  deriving DecidableEq, Repr

def Expr.fpi : Expr → Finset Id
  | .ident x => {x}
  | .lam z t => t.fpi.erase (.var z)
  | .app t u => t.fpi ∪ u.fpi
  | .letE z t u => t.fpi ∪ u.fpi.erase (.var z)

def Expr.Closed (t : Expr) : Prop := ∀ z, Id.var z ∉ t.fpi
def Expr.Source (t : Expr) : Prop := ∀ m, Id.loc m ∉ t.fpi

def Expr.apply (c : Nat) (vs : List Expr) : Expr :=
  vs.foldl Expr.app (.ident (.const c))

/-- Figure 10-1: Q is not assumed finite. -/
structure Language where
  constants : Set Nat
  constructor : Nat → Prop
  arity : Nat → Nat

inductive Value (L : Language) : Expr → Prop where
  | variable (z) : Value L (.ident (.var z))
  | location (m) : Value L (.ident (.loc m))
  | lambda (z t) : Value L (.lam z t)
  | constant (c vs) : c ∈ L.constants → (∀ v ∈ vs, Value L v) →
      ((L.constructor c ∧ vs.length ≤ L.arity c) ∨
       (¬ L.constructor c ∧ vs.length < L.arity c)) → Value L (.apply c vs)

/-- Definitions 10.1.14 and 10.2.1; arrow is symbol 0, normal kind is 0. -/
structure Signature where
  kinds : Set Nat
  directions : Set Nat
  constructors : Set Nat
  parameters : Nat → List (Nat × Nat)
  result : Nat → Nat
  predicates : Set Nat
  predicateKinds : Nat → List Nat

def Signature.Valid (S : Signature) : Prop :=
  0 ∈ S.kinds ∧ 0 ∈ S.constructors ∧ S.parameters 0 = [(0, 0), (1, 0)] ∧
  S.result 0 = 0 ∧
  (∀ f ∈ S.constructors, (S.parameters f).map Prod.fst |>.Nodup) ∧
  (∀ f ∈ S.constructors, S.result f ∈ S.kinds ∧
    ∀ p ∈ S.parameters f, p.1 ∈ S.directions ∧ p.2 ∈ S.kinds) ∧
  (∀ p ∈ S.predicates, ∀ k ∈ S.predicateKinds p, k ∈ S.kinds)

inductive Ty where
  | var : TVar → Ty
  | con : Nat → List Ty → Ty

def Ty.arrow (T U : Ty) : Ty := .con 0 [T, U]

def Ty.fv : Ty → Vars
  | .var X => {X}
  | .con _ ts => (ts.map Ty.fv).foldr (· ∪ ·) ∅

inductive Ty.HasKind (S : Signature) : Ty → Nat → Prop where
  | var (X) : X.1 ∈ S.kinds → HasKind S (.var X) X.1
  | con (f ts) : f ∈ S.constructors →
      List.Forall₂ (fun T p => HasKind S T p.2) ts (S.parameters f) →
      HasKind S (.con f ts) (S.result f)

abbrev Subst := TVar → Ty

def Ty.subst (θ : Subst) : Ty → Ty
  | .var X => θ X
  | .con f ts => .con f (ts.map (Ty.subst θ))

def Subst.dom (θ : Subst) : Set TVar := {X | θ X ≠ .var X}
def Subst.range (θ : Subst) : Set TVar := {Y | ∃ X ∈ θ.dom, Y ∈ (θ X).fv}
def Subst.Valid (S : Signature) (θ : Subst) : Prop :=
  θ.dom.Finite ∧ (∀ X ∈ θ.dom, X.1 ∈ S.kinds) ∧ ∀ X, X.1 ∈ S.kinds → (θ X).HasKind S X.1
def Subst.Idempotent (θ : Subst) : Prop := ∀ X, (θ X).subst θ = θ X

def Subst.Away (θ : Subst) (A : Vars) : Subst :=
  fun X => if X ∈ A then .var X else θ X

structure DMScheme where
  bound : Vars
  body : Ty

def DMScheme.fv (s : DMScheme) : Vars := s.body.fv \ s.bound
def DMScheme.WF (S : Signature) (s : DMScheme) : Prop :=
  s.body.HasKind S 0 ∧ ∀ X ∈ s.bound, X.1 ∈ S.kinds
def DMScheme.mono (T : Ty) : DMScheme := ⟨∅, T⟩
def DMScheme.Instance (S : Signature) (s : DMScheme) (T : Ty) : Prop :=
  ∃ θ : Subst, θ.Valid S ∧ θ.dom ⊆ ↑s.bound ∧ T = s.body.subst θ

inductive Predicate where
  | equal : Nat → Predicate
  | sub : Nat → Predicate
  | other : Nat → Predicate
  deriving DecidableEq, Repr

mutual
inductive Constraint where
  | truth
  | falsity
  | atom : Predicate → List Ty → Constraint
  | conj : Constraint → Constraint → Constraint
  | exists_ : Vars → Constraint → Constraint
  | def_ : Id → Scheme → Constraint → Constraint
  | inst : Id → Ty → Constraint
inductive Scheme where
  | all : Vars → Constraint → Ty → Scheme
end

mutual
def Constraint.fv : Constraint → Vars
  | .truth | .falsity => ∅
  | .atom _ ts => (ts.map Ty.fv).foldr (· ∪ ·) ∅
  | .conj C D => C.fv ∪ D.fv
  | .exists_ A C => C.fv \ A
  | .def_ _ s C => s.fv ∪ C.fv
  | .inst _ T => T.fv
def Scheme.fv : Scheme → Vars
  | .all A C T => (C.fv ∪ T.fv) \ A
end

mutual
def Constraint.fpi : Constraint → Finset Id
  | .truth | .falsity | .atom _ _ => ∅
  | .conj C D => C.fpi ∪ D.fpi
  | .exists_ _ C => C.fpi
  | .def_ x s C => s.fpi ∪ C.fpi.erase x
  | .inst x _ => {x}
def Scheme.fpi : Scheme → Finset Id
  | .all _ C _ => C.fpi
end

def Predicate.Kinds (S : Signature) : Predicate → List Nat
  | .equal k | .sub k => [k,k]
  | .other p => S.predicateKinds p

def Predicate.WF (S : Signature) : Predicate → Prop
  | .equal k | .sub k => k ∈ S.kinds
  | .other p => p ∈ S.predicates

mutual
def Constraint.WF (S : Signature) : Constraint → Prop
  | .truth | .falsity => True
  | .atom p ts => p.WF S ∧ List.Forall₂ (Ty.HasKind S) ts (p.Kinds S)
  | .conj C D => C.WF S ∧ D.WF S
  | .exists_ A C => (∀ X ∈ A, X.1 ∈ S.kinds) ∧ C.WF S
  | .def_ _ s C => s.WF S ∧ C.WF S
  | .inst _ T => T.HasKind S 0
def Scheme.WF (S : Signature) : Scheme → Prop
  | .all A C T => (∀ X ∈ A, X.1 ∈ S.kinds) ∧ C.WF S ∧ T.HasKind S 0
end

def Constraint.eq (k : Nat) (T U : Ty) := Constraint.atom (.equal k) [T,U]
def Constraint.le (k : Nat) (T U : Ty) := Constraint.atom (.sub k) [T,U]
def Scheme.mono (T : Ty) := Scheme.all ∅ .truth T

def Scheme.exists_ : Scheme → Constraint
  | .all A C _ => .exists_ A C
/-- Use only when bound variables are fresh for U (Definition 10.2.3). -/
def Scheme.instanceConstraint : Scheme → Ty → Constraint
  | .all A C T, U => .exists_ A (.conj C (.le 0 T U))
def Scheme.InstanceFresh : Scheme → Ty → Prop
  | .all A _ _, U => Disjoint A U.fv

def Constraint.let_ (x : Id) (s : Scheme) (C : Constraint) :=
  Constraint.conj s.exists_ (.def_ x s C)

abbrev Env := List (Id × Scheme)
abbrev DMEnv := List (Id × DMScheme)
/-- Definition 10.1.19: rightmost occurrence wins; repetitions are allowed. -/
def lookup {α : Type} (Γ : List (Id × α)) (x : Id) : Option α :=
  (Γ.reverse.find? (fun p => p.1 == x)).map Prod.snd

def Env.fv (Γ : Env) : Vars := (Γ.map (fun p => p.2.fv)).foldr (· ∪ ·) ∅
def Env.fpi (Γ : Env) : Finset Id := (Γ.map (fun p => p.2.fpi)).foldr (· ∪ ·) ∅
def Env.dpi (Γ : Env) : Finset Id := (Γ.map Prod.fst).toFinset
def Env.dfpi (Γ : Env) : Finset Id := Γ.dpi ∪ Γ.fpi
def Env.WF (S : Signature) (Γ : Env) : Prop := ∀ p ∈ Γ, p.2.WF S
def DMEnv.fv (Γ : DMEnv) : Vars := (Γ.map (fun p => p.2.fv)).foldr (· ∪ ·) ∅
def DMEnv.WF (S : Signature) (Γ : DMEnv) : Prop := ∀ p ∈ Γ, p.2.WF S

def Env.defIn (Γ : Env) (C : Constraint) :=
  Γ.foldr (fun p D => Constraint.def_ p.1 p.2 D) C

def Env.letIn (Γ : Env) (C : Constraint) :=
  Γ.foldr (fun p D => Constraint.let_ p.1 p.2 D) C

def Env.exists_ (Γ : Env) : Constraint :=
  (Γ.foldl (fun (acc : Env × Constraint) p =>
    (acc.1 ++ [p], .conj acc.2 (acc.1.defIn p.2.exists_))) ([], .truth)).2

end HMX
