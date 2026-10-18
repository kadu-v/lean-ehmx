import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Forall2

/-! EHMX の生の構文。型 kind は 0、効果 kind は 1。
型・効果の束縛と項の束縛は別の添字列を持つ。
`HMX` の原典の定義は変更しない。 -/
namespace EHMX

abbrev Kind := Nat
abbrev TVar := Kind × Nat
abbrev Op := Nat

inductive Symbol where
  | arrow | empty | union | operation : Op → Symbol | other : Nat → Symbol
  deriving DecidableEq, Repr

structure Signature where
  kinds : Set Kind
  constructors : Set Nat
  parameters : Nat → List Kind
  result : Nat → Kind
  predicates : Set Nat
  predicateKinds : Nat → List Kind

def Signature.WF (S : Signature) : Prop :=
  0 ∈ S.kinds ∧ 1 ∈ S.kinds ∧
  (∀ f ∈ S.constructors, S.result f ∈ S.kinds ∧ ∀ k ∈ S.parameters f, k ∈ S.kinds) ∧
  ∀ p ∈ S.predicates, ∀ k ∈ S.predicateKinds p, k ∈ S.kinds

def Symbol.parameters (S : Signature) : Symbol → List Kind
  | .arrow => [0, 1, 0]
  | .empty | .operation _ => []
  | .union => [1, 1]
  | .other f => S.parameters f

def Symbol.result (S : Signature) : Symbol → Kind
  | .arrow => 0
  | .empty | .union | .operation _ => 1
  | .other f => S.result f

def Symbol.Declared (S : Signature) : Symbol → Prop
  | .other f => f ∈ S.constructors
  | _ => True

inductive Ty where
  | free : TVar → Ty
  | bound : Nat → Ty
  | con : Symbol → List Ty → Ty
  deriving BEq, Repr

/-- Effect is a raw type expression; kind 1 is required by every judgment. -/
abbrev Effect := Ty
def Ty.arrow (A : Ty) (ε : Effect) (B : Ty) : Ty := .con .arrow [A, ε, B]
def Ty.empty : Effect := .con .empty []
def Ty.singleton (op : Op) : Effect := .con (.operation op) []
def Ty.union (ε η : Effect) : Effect := .con .union [ε, η]
abbrev Effect.empty := Ty.empty
abbrev Effect.singleton := Ty.singleton
abbrev Effect.union := Ty.union

inductive Ty.HasKind (S : Signature) (Δ : List Kind) : Ty → Kind → Prop where
  | free : X.1 ∈ S.kinds → HasKind S Δ (.free X) X.1
  | bound : Δ[i]? = some k → k ∈ S.kinds → HasKind S Δ (.bound i) k
  | con : f.Declared S →
      List.Forall₂ (HasKind S Δ) ts (f.parameters S) →
      HasKind S Δ (.con f ts) (f.result S)

def Ty.fv : Ty → Finset TVar
  | .free X => {X}
  | .bound _ => ∅
  | .con _ ts => (ts.map Ty.fv).foldr (· ∪ ·) ∅

def Ty.LCAt (d : Nat) : Ty → Prop
  | .free _ => True
  | .bound i => i < d
  | .con _ ts => ∀ T ∈ ts, T.LCAt d

def Ty.shift (n d : Nat) : Ty → Ty
  | .free X => .free X
  | .bound i => .bound (if i < d then i else i + n)
  | .con f ts => .con f (ts.map (Ty.shift n d))

/-- Remove a block of type/effect binders; index 0 is the first block entry. -/
def Ty.openAt (d : Nat) (us : List Ty) : Ty → Ty
  | .free X => .free X
  | .bound i => if i < d then .bound i else
      match us[i - d]? with
      | some U => U.shift d 0
      | none => .bound (i - us.length)
  | .con f ts => .con f (ts.map (Ty.openAt d us))

def Ty.subst (θ : TVar → Ty) : Ty → Ty
  | .free X => θ X
  | .bound i => .bound i
  | .con f ts => .con f (ts.map (Ty.subst θ))

inductive PVar where
  | free : Nat → PVar
  | bound : Nat → PVar
  deriving DecidableEq, Repr

inductive Expr where
  | ident : PVar → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  | letE : Expr → Expr → Expr
  | perform : Op → Expr → Expr
  | handle : Expr → Op → Expr → Expr → Expr
  deriving DecidableEq, Repr

def Expr.LCAt (d : Nat) : Expr → Prop
  | .ident (.free _) => True
  | .ident (.bound i) => i < d
  | .lam t => t.LCAt (d + 1)
  | .app t u => t.LCAt d ∧ u.LCAt d
  | .letE t u => t.LCAt d ∧ u.LCAt (d + 1)
  | .perform _ t => t.LCAt d
  | .handle t _ r c => t.LCAt d ∧ r.LCAt (d + 1) ∧ c.LCAt (d + 2)

def Expr.fv : Expr → Finset Nat
  | .ident (.free x) => {x}
  | .ident (.bound _) => ∅
  | .lam t | .perform _ t => t.fv
  | .app t u | .letE t u => t.fv ∪ u.fv
  | .handle t _ r c => t.fv ∪ r.fv ∪ c.fv

def Expr.Closed (e : Expr) : Prop := e.LCAt 0 ∧ e.fv = ∅

/-- Only variables and abstractions are values. -/
def Expr.isValue : Expr → Bool
  | .ident _ | .lam _ => true
  | _ => false
def Value (e : Expr) : Prop := e.isValue = true

def Expr.shift (n d : Nat) : Expr → Expr
  | .ident (.free x) => .ident (.free x)
  | .ident (.bound i) => .ident (.bound (if i < d then i else i + n))
  | .lam t => .lam (t.shift n (d + 1))
  | .app t u => .app (t.shift n d) (u.shift n d)
  | .letE t u => .letE (t.shift n d) (u.shift n (d + 1))
  | .perform op t => .perform op (t.shift n d)
  | .handle t op r c => .handle (t.shift n d) op (r.shift n (d + 1)) (c.shift n (d + 2))

/-- Capture-avoiding simultaneous term opening; operation clauses use [k,x]. -/
def Expr.openAt (d : Nat) (us : List Expr) : Expr → Expr
  | .ident (.free x) => .ident (.free x)
  | .ident (.bound i) => if i < d then .ident (.bound i) else
      match us[i - d]? with
      | some u => u.shift d 0
      | none => .ident (.bound (i - us.length))
  | .lam t => .lam (t.openAt (d + 1) us)
  | .app t u => .app (t.openAt d us) (u.openAt d us)
  | .letE t u => .letE (t.openAt d us) (u.openAt (d + 1) us)
  | .perform op t => .perform op (t.openAt d us)
  | .handle t op r c => .handle (t.openAt d us) op (r.openAt (d + 1) us) (c.openAt (d + 2) us)

def Expr.subst (x : Nat) (v : Expr) : Expr → Expr
  | .ident (.free y) => if x = y then v else .ident (.free y)
  | .ident (.bound i) => .ident (.bound i)
  | .lam t => .lam (Expr.subst x v t)
  | .app t u => .app (Expr.subst x v t) (Expr.subst x v u)
  | .letE t u => .letE (Expr.subst x v t) (Expr.subst x v u)
  | .perform op t => .perform op (Expr.subst x v t)
  | .handle t op r c => .handle (Expr.subst x v t) op (Expr.subst x v r) (Expr.subst x v c)

inductive Predicate where
  | equal : Kind → Predicate
  | sub : Kind → Predicate
  | other : Nat → Predicate
  deriving DecidableEq, Repr

def Predicate.kinds (S : Signature) : Predicate → List Kind
  | .equal k | .sub k => [k, k]
  | .other p => S.predicateKinds p

def Predicate.WF (S : Signature) : Predicate → Prop
  | .equal k | .sub k => k ∈ S.kinds
  | .other p => p ∈ S.predicates

mutual
inductive Constraint where
  | truth | falsity
  | atom : Predicate → List Ty → Constraint
  | conj : Constraint → Constraint → Constraint
  | exists_ : List Kind → Constraint → Constraint
  | forall_ : List Kind → Constraint → Constraint
  | def_ : Scheme → Constraint → Constraint
  | defFree : Nat → Scheme → Constraint → Constraint
  | inst : PVar → Ty → Constraint
  | implies : Constraint → Constraint → Constraint
  deriving BEq, Repr
inductive Scheme where
  | all : List Kind → Constraint → Ty → Scheme
  deriving BEq, Repr
end

def Constraint.le (k : Kind) (T U : Ty) := Constraint.atom (.sub k) [T,U]
def Constraint.eq (k : Kind) (T U : Ty) := Constraint.atom (.equal k) [T,U]
def Scheme.mono (T : Ty) := Scheme.all [] .truth T
def Scheme.exists_ : Scheme → Constraint
  | .all ks C _ => .exists_ ks C
def Constraint.letBound (s : Scheme) (C : Constraint) : Constraint :=
  .conj s.exists_ (.def_ s C)
def Constraint.letFree (x : Nat) (s : Scheme) (C : Constraint) : Constraint :=
  .conj s.exists_ (.defFree x s C)

mutual
def Constraint.fpi : Constraint → Finset Nat
  | .truth | .falsity | .atom _ _ => ∅
  | .conj C D | .implies C D => C.fpi ∪ D.fpi
  | .exists_ _ C | .forall_ _ C => C.fpi
  | .def_ s C => s.fpi ∪ C.fpi
  | .defFree x s C => s.fpi ∪ C.fpi.erase x
  | .inst (.free x) _ => {x}
  | .inst (.bound _) _ => ∅
def Scheme.fpi : Scheme → Finset Nat
  | .all _ C _ => C.fpi
end

mutual
/-- Free type and effect variables, including those in locally defined schemes. -/
def Constraint.fv : Constraint → Finset TVar
  | .truth | .falsity => ∅
  | .atom _ ts => (ts.map Ty.fv).foldr (· ∪ ·) ∅
  | .conj C D | .implies C D => C.fv ∪ D.fv
  | .exists_ _ C | .forall_ _ C => C.fv
  | .def_ s C | .defFree _ s C => s.fv ∪ C.fv
  | .inst _ T => T.fv
def Scheme.fv : Scheme → Finset TVar
  | .all _ C T => C.fv ∪ T.fv
end

mutual
def Constraint.WF (S : Signature) (Δ : List Kind) (n : Nat) : Constraint → Prop
  | .truth | .falsity => True
  | .atom p ts => p.WF S ∧ List.Forall₂ (Ty.HasKind S Δ) ts (p.kinds S)
  | .conj C D => C.WF S Δ n ∧ D.WF S Δ n
  | .implies P D => P.WF S Δ 0 ∧ P.fpi = ∅ ∧ D.WF S Δ n
  | .exists_ ks C | .forall_ ks C =>
      (∀ k ∈ ks, k ∈ S.kinds) ∧ C.WF S (ks ++ Δ) n
  | .def_ s C => s.WF S Δ n ∧ C.WF S Δ (n + 1)
  | .defFree _ s C => s.WF S Δ n ∧ C.WF S Δ n
  | .inst x T => T.HasKind S Δ 0 ∧ match x with
      | .free _ => True
      | .bound i => i < n
def Scheme.WF (S : Signature) (Δ : List Kind) (n : Nat) : Scheme → Prop
  | .all ks C T => (∀ k ∈ ks, k ∈ S.kinds) ∧
      C.WF S (ks ++ Δ) n ∧ T.HasKind S (ks ++ Δ) 0
end

mutual
def Constraint.shift (n d : Nat) : Constraint → Constraint
  | .truth => .truth
  | .falsity => .falsity
  | .atom p ts => .atom p (ts.map (Ty.shift n d))
  | .conj C D => .conj (C.shift n d) (D.shift n d)
  | .implies P D => .implies (P.shift n d) (D.shift n d)
  | .exists_ ks C => .exists_ ks (C.shift n (d + ks.length))
  | .forall_ ks C => .forall_ ks (C.shift n (d + ks.length))
  | .def_ s C => .def_ (s.shift n d) (C.shift n d)
  | .defFree x s C => .defFree x (s.shift n d) (C.shift n d)
  | .inst x T => .inst x (T.shift n d)
def Scheme.shift (n d : Nat) : Scheme → Scheme
  | .all ks C T => .all ks (C.shift n (d + ks.length)) (T.shift n (d + ks.length))
end

abbrev BoundSubst := Nat → Ty

def Ty.substBound (σ : BoundSubst) : Ty → Ty
  | .free X => .free X
  | .bound i => σ i
  | .con f ts => .con f (ts.map (Ty.substBound σ))

def BoundSubst.lift (n : Nat) (σ : BoundSubst) : BoundSubst :=
  fun i => if i < n then .bound i else (σ (i - n)).shift n 0

mutual
def Constraint.substBound (σ : BoundSubst) : Constraint → Constraint
  | .truth => .truth
  | .falsity => .falsity
  | .atom p ts => .atom p (ts.map (Ty.substBound σ))
  | .conj C D => .conj (C.substBound σ) (D.substBound σ)
  | .implies P D => .implies (P.substBound σ) (D.substBound σ)
  | .exists_ ks C => .exists_ ks (C.substBound (σ.lift ks.length))
  | .forall_ ks C => .forall_ ks (C.substBound (σ.lift ks.length))
  | .def_ s C => .def_ (s.substBound σ) (C.substBound σ)
  | .defFree x s C => .defFree x (s.substBound σ) (C.substBound σ)
  | .inst x T => .inst x (T.substBound σ)
def Scheme.substBound (σ : BoundSubst) : Scheme → Scheme
  | .all ks C T => .all ks (C.substBound (σ.lift ks.length))
      (T.substBound (σ.lift ks.length))
end

/-- Remove precisely the initial block, leaving all outer variables in scope. -/
def BoundSubst.many (args : List Ty) : BoundSubst := fun i =>
  match args[i]? with
  | some U => U
  | none => .bound (i - args.length)

structure OpDecl where
  kinds : List Kind
  input : Ty
  output : Ty
  condition : Constraint := .truth
  deriving BEq, Repr
abbrev OpSignature := Op → Option OpDecl

/-- Static operation scope, independent of type/effect inference. -/
def Expr.Declared (sig : OpSignature) : Expr → Prop
  | .ident _ => True
  | .lam t => t.Declared sig
  | .app t u | .letE t u => t.Declared sig ∧ u.Declared sig
  | .perform op t => sig op ≠ none ∧ t.Declared sig
  | .handle t op r c => sig op ≠ none ∧ t.Declared sig ∧ r.Declared sig ∧ c.Declared sig

/-- Operation declarations have no free type/effect variables. -/
def OpSignature.WF (S : Signature) (sig : OpSignature) : Prop :=
  ∀ op d, sig op = some d →
    (∀ k ∈ d.kinds, k ∈ S.kinds) ∧ d.input.HasKind S d.kinds 0 ∧
    d.output.HasKind S d.kinds 0 ∧ d.input.fv = ∅ ∧ d.output.fv = ∅ ∧
    d.condition.WF S d.kinds 0 ∧ d.condition.fpi = ∅ ∧ d.condition.fv = ∅

/-- Bound schemes are nearest-first; free bindings are rightmost-wins. -/
structure Env where
  free : List (Nat × Scheme) := []
  bound : List Scheme := []

def Env.lookup (Γ : Env) : PVar → Option Scheme
  | .bound i => Γ.bound[i]?
  | .free x => (Γ.free.reverse.find? (fun p => p.1 == x)).map Prod.snd

def Env.push (Γ : Env) (s : Scheme) : Env := { Γ with bound := s :: Γ.bound }
def Env.shift (Γ : Env) (n : Nat) : Env :=
  ⟨Γ.free.map (fun p => (p.1, p.2.shift n 0)), Γ.bound.map (Scheme.shift n 0)⟩
def Env.WF (S : Signature) (Δ : List Kind) (Γ : Env) : Prop :=
  (∀ p ∈ Γ.free, p.2.WF S Δ 0 ∧ p.2.fpi = ∅) ∧
  ∀ s ∈ Γ.bound, s.WF S Δ 0 ∧ s.fpi = ∅
def Env.dpi (Γ : Env) : Finset Nat := (Γ.free.map Prod.fst).toFinset
def Expr.Scoped (Γ : Env) (e : Expr) : Prop := e.LCAt Γ.bound.length ∧ e.fv ⊆ Γ.dpi

def Env.letIn (Γ : Env) (C : Constraint) : Constraint :=
  Γ.free.foldr (fun p D => D.letFree p.1 p.2)
    (Γ.bound.foldl (fun D s => D.letBound s) C)
def Env.exists_ (Γ : Env) : Constraint := Γ.letIn .truth

end EHMX
