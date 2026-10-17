import HMX.Syntax

namespace HMX

/-- A binding masks both names, preventing capture. Constants and locations are
not renamed by the expression α relation. -/
def bindId (r : Id → Id → Prop) (x y : Id) (u v : Id) : Prop :=
  (u = x ∧ v = y) ∨ (u ≠ x ∧ v ≠ y ∧ r u v)

inductive Expr.Related : (Id → Id → Prop) → Expr → Expr → Prop where
  | ident : r x y → Related r (.ident x) (.ident y)
  | lam : Related (bindId r (.var x) (.var y)) t u → Related r (.lam x t) (.lam y u)
  | app : Related r t t' → Related r u u' → Related r (.app t u) (.app t' u')
  | letE : Related r t t' → Related (bindId r (.var x) (.var y)) u u' →
      Related r (.letE x t u) (.letE y t' u')

def Expr.Alpha (t u : Expr) : Prop := Expr.Related Eq t u

inductive Ty.Related (r : TVar → TVar → Prop) : Ty → Ty → Prop where
  | var : r X Y → Related r (.var X) (.var Y)
  | con : List.Forall₂ (Related r) ts us → Related r (.con f ts) (.con f us)

/-- A kind-preserving bijection between finite sets of bound variables; free
variables retain the surrounding correspondence. Quantifier order is irrelevant. -/
def Binds (r r' : TVar → TVar → Prop) (A B : Vars) : Prop :=
  (∀ X ∈ A, ∃! Y, Y ∈ B ∧ X.1 = Y.1 ∧ r' X Y) ∧
  (∀ Y ∈ B, ∃! X, X ∈ A ∧ X.1 = Y.1 ∧ r' X Y) ∧
  (∀ X Y, r' X Y ↔
    ((X ∈ A ∧ Y ∈ B ∧ X.1 = Y.1 ∧ r' X Y) ∨ (X ∉ A ∧ Y ∉ B ∧ r X Y)))

mutual
inductive Constraint.Related : (TVar → TVar → Prop) → (Id → Id → Prop) →
    Constraint → Constraint → Prop where
  | truth : Constraint.Related r q .truth .truth
  | falsity : Constraint.Related r q .falsity .falsity
  | atom : List.Forall₂ (Ty.Related r) ts us → Constraint.Related r q (.atom p ts) (.atom p us)
  | conj : Constraint.Related r q C C' → Constraint.Related r q D D' → Constraint.Related r q (.conj C D) (.conj C' D')
  | exists_ : Binds r r' A B → Constraint.Related r' q C D →
      Constraint.Related r q (.exists_ A C) (.exists_ B D)
  | def_ : (x = y ∨ (∃ a b, x = .var a ∧ y = .var b) ∨ (∃ a b, x = .loc a ∧ y = .loc b)) → Scheme.Related r q s s' → Constraint.Related r (bindId q x y) C D →
      Constraint.Related r q (.def_ x s C) (.def_ y s' D)
  | inst : q x y → Ty.Related r T U → Constraint.Related r q (.inst x T) (.inst y U)
inductive Scheme.Related : (TVar → TVar → Prop) → (Id → Id → Prop) →
    Scheme → Scheme → Prop where
  | all : Binds r r' A B → Constraint.Related r' q C D → Ty.Related r' T U →
      Scheme.Related r q (.all A C T) (.all B D U)
end

def Constraint.Alpha := Constraint.Related Eq Eq
def Scheme.Alpha := Scheme.Related Eq Eq

def DMScheme.Alpha (s s' : DMScheme) : Prop :=
  ∃ r, Binds Eq r s.bound s'.bound ∧ Ty.Related r s.body s'.body

mutual
def Constraint.rawSubst (θ : Subst) : Constraint → Constraint
  | .truth => .truth
  | .falsity => .falsity
  | .atom p ts => .atom p (ts.map (Ty.subst θ))
  | .conj C D => .conj (C.rawSubst θ) (D.rawSubst θ)
  | .exists_ A C => .exists_ A (C.rawSubst (θ.Away A))
  | .def_ x s C => .def_ x (s.rawSubst θ) (C.rawSubst θ)
  | .inst x T => .inst x (T.subst θ)
def Scheme.rawSubst (θ : Subst) : Scheme → Scheme
  | .all A C T => .all A (C.rawSubst (θ.Away A)) (T.subst (θ.Away A))
end

/-- The range condition concerns only variables actually free in the scope. -/
def FreshImages (θ : Subst) (A F : Vars) : Prop :=
  ∀ X ∈ F, X ∉ A → Disjoint A (θ X).fv

mutual
def Constraint.SafeSubst (θ : Subst) : Constraint → Prop
  | .truth | .falsity | .atom _ _ | .inst _ _ => True
  | .conj C D => C.SafeSubst θ ∧ D.SafeSubst θ
  | .exists_ A C => FreshImages θ A C.fv ∧ C.SafeSubst (θ.Away A)
  | .def_ _ s C => s.SafeSubst θ ∧ C.SafeSubst θ
def Scheme.SafeSubst (θ : Subst) : Scheme → Prop
  | .all A C T => FreshImages θ A (C.fv ∪ T.fv) ∧ C.SafeSubst (θ.Away A)
end

/-- Capture-avoiding substitution is a relation on representatives, not an
unconstrained parameter. α-renaming is performed before the structural operation. -/
def Constraint.Substitutes (θ : Subst) (C D : Constraint) : Prop :=
  ∃ C', C.Alpha C' ∧ C'.SafeSubst θ ∧ (C'.rawSubst θ).Alpha D

def Scheme.Substitutes (θ : Subst) (s s' : Scheme) : Prop :=
  ∃ r, s.Alpha r ∧ r.SafeSubst θ ∧ (r.rawSubst θ).Alpha s'

def Expr.rawSubst (z : Nat) (v : Expr) : Expr → Expr
  | .ident x => if x = .var z then v else .ident x
  | .lam x t => .lam x (if x = z then t else Expr.rawSubst z v t)
  | .app t u => .app (Expr.rawSubst z v t) (Expr.rawSubst z v u)
  | .letE x t u => .letE x (Expr.rawSubst z v t) (if x = z then u else Expr.rawSubst z v u)

def Expr.SafeSubst (z : Nat) (v : Expr) : Expr → Prop
  | .ident _ => True
  | .lam x t => x ≠ z → Id.var x ∉ v.fpi ∧ Expr.SafeSubst z v t
  | .app t u => Expr.SafeSubst z v t ∧ Expr.SafeSubst z v u
  | .letE x t u => Expr.SafeSubst z v t ∧ (x ≠ z → Id.var x ∉ v.fpi ∧ Expr.SafeSubst z v u)

def Expr.Substitutes (z : Nat) (v t u : Expr) : Prop :=
  ∃ t', t.Alpha t' ∧ Expr.SafeSubst z v t' ∧ (Expr.rawSubst z v t').Alpha u

end HMX
