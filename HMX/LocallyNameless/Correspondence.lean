import HMX.LocallyNameless.Inference
import HMX.Inference
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

namespace HMX.LN

/-- Fixed enumeration for translating a source finite-set binder. Other orders
are compared by BinderEq, not identified by syntactic equality. -/
def boundNames (A : Vars) : List TVar := ((A.map toLex.toEmbedding).sort (· ≤ ·)).map ofLex

def ofTy (xs : List TVar) : HMX.Ty → Ty
  | .var X => if X ∈ xs then .bound (xs.idxOf X) else .free X
  | .con f ts => .con f (ts.map (ofTy xs))

def ofId (zs : List Id) (x : Id) : PVar :=
  if x ∈ zs then .bound (zs.idxOf x) else .free x

def ofExpr (zs : List Id) : HMX.Expr → Expr
  | .ident x => .ident (ofId zs x)
  | .lam z t => .lam (ofExpr (.var z :: zs) t)
  | .app t u => .app (ofExpr zs t) (ofExpr zs u)
  | .letE z t u => .letE (ofExpr zs t) (ofExpr (.var z :: zs) u)

mutual
def ofConstraint (xs : List TVar) (zs : List Id) : HMX.Constraint → Constraint
  | .truth => .truth
  | .falsity => .falsity
  | .atom p ts => .atom p (ts.map (ofTy xs))
  | .conj C D => .conj (ofConstraint xs zs C) (ofConstraint xs zs D)
  | .exists_ A C => .exists_ ((boundNames A).map Prod.fst) (ofConstraint (boundNames A ++ xs) zs C)
  | .def_ x s C => .def_ (Binder.ofId x) (ofScheme xs zs s) (ofConstraint xs (x :: zs) C)
  | .inst x T => .inst (ofId zs x) (ofTy xs T)
def ofScheme (xs : List TVar) (zs : List Id) : HMX.Scheme → Scheme
  | .all A C T => .all ((boundNames A).map Prod.fst)
      (ofConstraint (boundNames A ++ xs) zs C) (ofTy (boundNames A ++ xs) T)
end

def ofEnv (Γ : HMX.Env) : Env := Γ.map (fun p => (p.1, ofScheme [] [] p.2))

/-- Representation obligations, not assumptions of the inference statements. -/
def encodingWF (S : Signature) : Prop :=
  (∀ t, (ofExpr [] t).LCAt 0) ∧
  (∀ T k, T.HasKind S k → (ofTy [] T).HasKind S [] k) ∧
  (∀ C, C.WF S → (ofConstraint [] [] C).WF S [] 0) ∧
  (∀ s, s.WF S → (ofScheme [] [] s).WF S [] 0)

def encodingFreeVariables : Prop :=
  (∀ t, (ofExpr [] t).fpi = t.fpi) ∧
  (∀ C, (ofConstraint [] [] C).fv = C.fv ∧ (ofConstraint [] [] C).fpi = C.fpi) ∧
  (∀ s, (ofScheme [] [] s).fv = s.fv ∧ (ofScheme [] [] s).fpi = s.fpi)

def encodingAlpha : Prop :=
  (∀ t u, t.Alpha u ↔ ofExpr [] t = ofExpr [] u) ∧
  (∀ C D, C.Alpha D → (ofConstraint [] [] C).BinderEq (ofConstraint [] [] D)) ∧
  (∀ s r, s.Alpha r → (ofScheme [] [] s).BinderEq (ofScheme [] [] r))

def encodingSemantics (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ ρ ι, ρ.Valid S M → ι.Valid M →
  (∀ C, C.WF S → ((ofConstraint [] [] C).Holds S M ρ ι ↔ C.Holds S M ρ ι)) ∧
  (∀ s, s.WF S → (ofScheme [] [] s).denote S M ρ ι = s.denote S M ρ ι)

def frameworkCorrespondence (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I ↔ HMX.Framework S M I

def typingCorrespondence (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  HMX.Framework S M I → ∀ C Γ t s,
    HMX.Typing S M C Γ t s ↔
      Typing S M (ofConstraint [] [] C) (ofEnv Γ) (ofExpr [] t) (ofScheme [] [] s)

def generationCorrespondence : Prop :=
  ∀ Γ t T, (ofConstraint [] [] (HMX.infer Γ t T)).BinderEq
    (infer (ofEnv Γ) (ofExpr [] t) (ofTy [] T))

end HMX.LN

namespace HMX

/-- The literal statement is retained in Inference. This separately named target
makes the source's implicit identifier scope explicit (audit A-04). -/
def theorem10_4_4_soundness_scoped (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ Γ t T, Γ.WF S → Γ.fpi = ∅ → t.fpi ⊆ Γ.dpi → T.HasKind S 0 →
    Typing S M (infer Γ t T) Γ t (.mono T)

def constraintGenerationPrincipality_scoped (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ Γ t T, Γ.WF S → Γ.fpi = ∅ → t.fpi ⊆ Γ.dpi → T.HasKind S 0 →
    PrincipalConstraint S M Γ t T (infer Γ t T)

end HMX
