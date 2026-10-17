import HMX.Syntax

/-! Proof representation for §10.2–10.4. Term and type indices have separate
stacks. A block's index 0 denotes its first entry; inner blocks are prepended.
Free names retain the source's kinds. No claim about the named representation
is assumed here; correspondence statements are in Correspondence. -/
namespace HMX.LN

inductive PVar where
  | free : Id → PVar
  | bound : Nat → PVar
  deriving DecidableEq, Repr

/-- Preserve the source's restriction that constants cannot be α-renamed. -/
inductive Binder where
  | term
  | location
  | constant : Nat → Binder
  deriving DecidableEq, Repr

def Binder.ofId : Id → Binder
  | .var _ => .term
  | .loc _ => .location
  | .const c => .constant c

inductive Expr where
  | ident : PVar → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  | letE : Expr → Expr → Expr
  deriving DecidableEq, Repr

def Expr.fpi : Expr → Finset Id
  | .ident (.free x) => {x}
  | .ident (.bound _) => ∅
  | .lam t => t.fpi
  | .app t u | .letE t u => t.fpi ∪ u.fpi

def Expr.LCAt (d : Nat) : Expr → Prop
  | .ident (.free _) => True
  | .ident (.bound i) => i < d
  | .lam t => t.LCAt (d + 1)
  | .app t u => t.LCAt d ∧ u.LCAt d
  | .letE t u => t.LCAt d ∧ u.LCAt (d + 1)

def Expr.shift (n d : Nat) : Expr → Expr
  | .ident (.bound i) => .ident (.bound (if i < d then i else i + n))
  | .ident (.free x) => .ident (.free x)
  | .lam t => .lam (t.shift n (d + 1))
  | .app t u => .app (t.shift n d) (u.shift n d)
  | .letE t u => .letE (t.shift n d) (u.shift n (d + 1))

/-- Remove one binder, substituting its body and lowering outer indices. -/
def Expr.openAt (d : Nat) (v : Expr) : Expr → Expr
  | .ident (.bound i) => if i = d then v.shift d 0 else
      .ident (.bound (if i < d then i else i - 1))
  | .ident (.free x) => .ident (.free x)
  | .lam t => .lam (Expr.openAt (d + 1) v t)
  | .app t u => .app (Expr.openAt d v t) (Expr.openAt d v u)
  | .letE t u => .letE (Expr.openAt d v t) (Expr.openAt (d + 1) v u)

/-- Insert one binder. Existing dangling indices are shifted as well. -/
def Expr.closeAt (d z : Nat) : Expr → Expr
  | .ident (.free x) => if x = .var z then .ident (.bound d) else .ident (.free x)
  | .ident (.bound i) => .ident (.bound (if i < d then i else i + 1))
  | .lam t => .lam (t.closeAt (d + 1) z)
  | .app t u => .app (t.closeAt d z) (u.closeAt d z)
  | .letE t u => .letE (t.closeAt d z) (u.closeAt (d + 1) z)

def Expr.subst (z : Nat) (v : Expr) : Expr → Expr
  | .ident (.free x) => if x = .var z then v else .ident (.free x)
  | .ident (.bound i) => .ident (.bound i)
  | .lam t => .lam (Expr.subst z v t)
  | .app t u => .app (Expr.subst z v t) (Expr.subst z v u)
  | .letE t u => .letE (Expr.subst z v t) (Expr.subst z v u)

inductive Ty where
  | free : TVar → Ty
  | bound : Nat → Ty
  | con : Nat → List Ty → Ty
  deriving Repr, BEq

def Ty.arrow (T U : Ty) : Ty := .con 0 [T,U]

def Ty.fv : Ty → Vars
  | .free X => {X}
  | .bound _ => ∅
  | .con _ ts => (ts.map Ty.fv).foldr (· ∪ ·) ∅

inductive Ty.HasKind (S : Signature) (ks : List Nat) : Ty → Nat → Prop where
  | free : X.1 ∈ S.kinds → HasKind S ks (.free X) X.1
  | bound : ks[i]? = some k → k ∈ S.kinds → HasKind S ks (.bound i) k
  | con : f ∈ S.constructors →
      List.Forall₂ (fun T p => HasKind S ks T p.2) ts (S.parameters f) →
      HasKind S ks (.con f ts) (S.result f)

def Ty.LCAt (d : Nat) : Ty → Prop
  | .free _ => True
  | .bound i => i < d
  | .con _ ts => ∀ T ∈ ts, T.LCAt d

def Ty.shift (n d : Nat) : Ty → Ty
  | .free X => .free X
  | .bound i => .bound (if i < d then i else i + n)
  | .con f ts => .con f (ts.map (Ty.shift n d))

def Ty.openAt (d : Nat) (us : List Ty) : Ty → Ty
  | .free X => .free X
  | .bound i => if i < d then .bound i else
      match us[i - d]? with
      | some T => T.shift d 0
      | none => .bound (i - us.length)
  | .con f ts => .con f (ts.map (Ty.openAt d us))

def Ty.closeAt (d : Nat) (xs : List TVar) : Ty → Ty
  | .free X => if X ∈ xs then .bound (d + xs.idxOf X) else .free X
  | .bound i => .bound (if i < d then i else i + xs.length)
  | .con f ts => .con f (ts.map (Ty.closeAt d xs))

def Ty.renameAt (d : Nat) (p : Nat → Nat) : Ty → Ty
  | .free X => .free X
  | .bound i => .bound (if i < d then i else d + p (i - d))
  | .con f ts => .con f (ts.map (Ty.renameAt d p))

abbrev Subst := TVar → Ty

def Ty.subst (θ : Subst) : Ty → Ty
  | .free X => θ X
  | .bound i => .bound i
  | .con f ts => .con f (ts.map (Ty.subst θ))

def Subst.Valid (S : Signature) (θ : Subst) : Prop :=
  {X | θ X ≠ .free X}.Finite ∧
  (∀ X, θ X ≠ .free X → X.1 ∈ S.kinds) ∧
  ∀ X, X.1 ∈ S.kinds → (θ X).HasKind S [] X.1

mutual
inductive Constraint where
  | truth
  | falsity
  | atom : Predicate → List Ty → Constraint
  | conj : Constraint → Constraint → Constraint
  | exists_ : List Nat → Constraint → Constraint
  | def_ : Binder → Scheme → Constraint → Constraint
  | inst : PVar → Ty → Constraint
  deriving Repr, BEq
inductive Scheme where
  | all : List Nat → Constraint → Ty → Scheme
  deriving Repr, BEq
end

mutual
def Constraint.fv : Constraint → Vars
  | .truth | .falsity => ∅
  | .atom _ ts => (ts.map Ty.fv).foldr (· ∪ ·) ∅
  | .conj C D => C.fv ∪ D.fv
  | .exists_ _ C => C.fv
  | .def_ _ s C => s.fv ∪ C.fv
  | .inst _ T => T.fv
def Scheme.fv : Scheme → Vars
  | .all _ C T => C.fv ∪ T.fv
end

mutual
def Constraint.fpi : Constraint → Finset Id
  | .truth | .falsity | .atom _ _ => ∅
  | .conj C D => C.fpi ∪ D.fpi
  | .exists_ _ C => C.fpi
  | .def_ _ s C => s.fpi ∪ C.fpi
  | .inst (.free x) _ => {x}
  | .inst (.bound _) _ => ∅
def Scheme.fpi : Scheme → Finset Id
  | .all _ C _ => C.fpi
end

mutual
def Constraint.WF (S : Signature) (ks : List Nat) (d : Nat) : Constraint → Prop
  | .truth | .falsity => True
  | .atom p ts => p.WF S ∧ List.Forall₂ (Ty.HasKind S ks) ts (p.Kinds S)
  | .conj C D => C.WF S ks d ∧ D.WF S ks d
  | .exists_ bs C => (∀ k ∈ bs, k ∈ S.kinds) ∧ C.WF S (bs ++ ks) d
  | .def_ _ s C => s.WF S ks d ∧ C.WF S ks (d + 1)
  | .inst x T => T.HasKind S ks 0 ∧ match x with
      | .free _ => True
      | .bound i => i < d
def Scheme.WF (S : Signature) (ks : List Nat) (d : Nat) : Scheme → Prop
  | .all bs C T => (∀ k ∈ bs, k ∈ S.kinds) ∧
      C.WF S (bs ++ ks) d ∧ T.HasKind S (bs ++ ks) 0
end

/- Traversal of type indices; [d] counts enclosing type binders only. -/
mutual
def Constraint.mapTypes (f : Nat → Ty → Ty) (d : Nat) : Constraint → Constraint
  | .truth => .truth
  | .falsity => .falsity
  | .atom p ts => .atom p (ts.map (f d))
  | .conj C D => .conj (C.mapTypes f d) (D.mapTypes f d)
  | .exists_ ks C => .exists_ ks (C.mapTypes f (d + ks.length))
  | .def_ b s C => .def_ b (s.mapTypes f d) (C.mapTypes f d)
  | .inst x T => .inst x (f d T)
def Scheme.mapTypes (f : Nat → Ty → Ty) (d : Nat) : Scheme → Scheme
  | .all ks C T => .all ks (C.mapTypes f (d + ks.length)) (f (d + ks.length) T)
end

mutual
def Constraint.mapIds (f : Nat → PVar → PVar) (d : Nat) : Constraint → Constraint
  | .truth => .truth
  | .falsity => .falsity
  | .atom p ts => .atom p ts
  | .conj C D => .conj (C.mapIds f d) (D.mapIds f d)
  | .exists_ ks C => .exists_ ks (C.mapIds f d)
  | .def_ b s C => .def_ b (s.mapIds f d) (C.mapIds f (d + 1))
  | .inst x T => .inst (f d x) T
def Scheme.mapIds (f : Nat → PVar → PVar) (d : Nat) : Scheme → Scheme
  | .all ks C T => .all ks (C.mapIds f d) T
end

def PVar.closeAt (d : Nat) (x : Id) : PVar → PVar
  | .free y => if y = x then .bound d else .free y
  | .bound i => .bound (if i < d then i else i + 1)

def PVar.openAt (d : Nat) (x : Id) : PVar → PVar
  | .free y => .free y
  | .bound i => if i = d then .free x else .bound (if i < d then i else i - 1)

def Constraint.openTypes (us : List Ty) (C : Constraint) : Constraint :=
  C.mapTypes (fun d T => T.openAt d us) 0

def Constraint.closeTypes (xs : List TVar) (C : Constraint) : Constraint :=
  C.mapTypes (fun d T => T.closeAt d xs) 0

def Constraint.subst (θ : Subst) (C : Constraint) : Constraint :=
  C.mapTypes (fun _ T => T.subst θ) 0

def Scheme.subst (θ : Subst) (s : Scheme) : Scheme :=
  s.mapTypes (fun _ T => T.subst θ) 0

def Constraint.closeId (x : Id) (C : Constraint) : Constraint :=
  C.mapIds (fun d v => v.closeAt d x) 0

def Constraint.openId (x : Id) (C : Constraint) : Constraint :=
  C.mapIds (fun d v => v.openAt d x) 0

def Constraint.eq (k : Nat) (T U : Ty) : Constraint := .atom (.equal k) [T,U]
def Constraint.le (k : Nat) (T U : Ty) : Constraint := .atom (.sub k) [T,U]
def Scheme.mono (T : Ty) : Scheme := .all [] .truth T

def Constraint.existsNames (xs : List TVar) (C : Constraint) : Constraint :=
  .exists_ (xs.map Prod.fst) (C.closeTypes xs)

def Scheme.generalize (xs : List TVar) (C : Constraint) (T : Ty) : Scheme :=
  .all (xs.map Prod.fst) (C.closeTypes xs) (T.closeAt 0 xs)

def Scheme.exists_ : Scheme → Constraint
  | .all ks C _ => .exists_ ks C

/-- Shift the target underneath the entire quantifier block; no freshness premise. -/
def Scheme.instanceConstraint : Scheme → Ty → Constraint
  | .all ks C T, U => .exists_ ks (.conj C (.le 0 T (U.shift ks.length 0)))

/-- The body already has index 0 bound by this definition. -/
def Constraint.letBound (b : Binder) (s : Scheme) (C : Constraint) : Constraint :=
  .conj s.exists_ (.def_ b s C)

def Constraint.define (x : Id) (s : Scheme) (C : Constraint) : Constraint :=
  .def_ (Binder.ofId x) s (C.closeId x)

def Constraint.letName (x : Id) (s : Scheme) (C : Constraint) : Constraint :=
  .conj s.exists_ (C.define x s)

abbrev Env := List (Id × Scheme)
def Env.fv (Γ : Env) : Vars := (Γ.map (fun p => p.2.fv)).foldr (· ∪ ·) ∅
def Env.fpi (Γ : Env) : Finset Id := (Γ.map (fun p => p.2.fpi)).foldr (· ∪ ·) ∅
def Env.dpi (Γ : Env) : Finset Id := (Γ.map Prod.fst).toFinset
def Env.WF (S : Signature) (Γ : Env) : Prop := ∀ p ∈ Γ, p.2.WF S [] 0

def Env.letIn (Γ : Env) (C : Constraint) : Constraint :=
  Γ.foldr (fun p D => D.letName p.1 p.2) C

def Env.defIn (Γ : Env) (C : Constraint) : Constraint :=
  Γ.foldr (fun p D => D.define p.1 p.2) C

def Env.exists_ (Γ : Env) : Constraint :=
  (Γ.foldl (fun (acc : Env × Constraint) p =>
    (acc.1 ++ [p], .conj acc.2 (acc.1.defIn p.2.exists_))) ([], .truth)).2

def Env.subst (θ : Subst) (Γ : Env) : Env := Γ.map (fun p => (p.1, p.2.subst θ))

/-- Permutations within a simultaneous quantifier block. Outside it, indices stay put. -/
def BlockPermutation (ks ls : List Nat) (p : Nat → Nat) : Prop :=
  ks.length = ls.length ∧ Function.Bijective p ∧
  (∀ i, ks.length ≤ i → p i = i) ∧ (∀ i, ks[i]? = ls[p i]?)

mutual
inductive Constraint.BinderEq : Constraint → Constraint → Prop where
  | refl : Constraint.BinderEq C C
  | symm : Constraint.BinderEq C D → Constraint.BinderEq D C
  | trans : Constraint.BinderEq C D → Constraint.BinderEq D E → Constraint.BinderEq C E
  | conj : Constraint.BinderEq C C' → Constraint.BinderEq D D' → Constraint.BinderEq (.conj C D) (.conj C' D')
  | exists_ : BlockPermutation ks ls p →
      Constraint.BinderEq (C.mapTypes (fun d T => T.renameAt d p) 0) D →
      Constraint.BinderEq (.exists_ ks C) (.exists_ ls D)
  | def_ : Scheme.BinderEq s r → Constraint.BinderEq C D → Constraint.BinderEq (.def_ b s C) (.def_ b r D)
inductive Scheme.BinderEq : Scheme → Scheme → Prop where
  | refl : Scheme.BinderEq s s
  | symm : Scheme.BinderEq s r → Scheme.BinderEq r s
  | trans : Scheme.BinderEq s r → Scheme.BinderEq r u → Scheme.BinderEq s u
  | all : BlockPermutation ks ls p →
      Constraint.BinderEq (C.mapTypes (fun d T => T.renameAt d p) 0) D →
      T.renameAt 0 p = U → Scheme.BinderEq (.all ks C T) (.all ls D U)
end

def Env.BinderEq (Γ Δ : Env) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2.BinderEq q.2) Γ Δ

end HMX.LN
