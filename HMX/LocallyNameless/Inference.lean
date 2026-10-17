import HMX.LocallyNameless.Typing

namespace HMX.LN

def Ty.maxIndex : Ty → Nat
  | .free X => X.2
  | .bound _ => 0
  | .con _ ts => (ts.map Ty.maxIndex).foldr max 0

def freshIndex (T : Ty) : Nat := T.maxIndex + 1

/-- Figure 10-9. Type binders close fresh names; term binders are already indices. -/
def generate : Expr → Ty → Constraint
  | .ident x, T => .inst x T
  | .lam t, T =>
      let X : TVar := (0, freshIndex T)
      let Y : TVar := (0, freshIndex T + 1)
      Constraint.existsNames [X,Y] (.conj
        (.letBound .term (.mono (.free X)) (generate t (.free Y)))
        (.le 0 (.arrow (.free X) (.free Y)) T))
  | .app t u, T =>
      let X : TVar := (0, freshIndex T)
      Constraint.existsNames [X] (.conj (generate t (.arrow (.free X) T)) (generate u (.free X)))
  | .letE t u, T =>
      let X : TVar := (0, freshIndex T)
      .letBound .term (Scheme.generalize [X] (generate t (.free X)) (.free X)) (generate u T)

def infer (Γ : Env) (t : Expr) (T : Ty) : Constraint := Γ.letIn (generate t T)

def closedGeneratedScheme (Γ : Env) (t : Expr) (X : TVar) : Scheme :=
  Scheme.generalize [X] (infer Γ t (.free X)) (.free X)

/-- Explicit scope qualification of the named transcription (audit A-04). -/
def theorem10_4_4_soundness_scoped (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ Γ t T, Γ.WF S → Γ.fpi = ∅ → t.LCAt 0 →
    t.fpi ⊆ Γ.dpi → T.HasKind S [] 0 → Typing S M (infer Γ t T) Γ t (.mono T)

def lemma10_4_5 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ t T U, t.LCAt 0 → T.HasKind S [] 0 → U.HasKind S [] 0 →
    Entails S M (.conj (generate t T) (.le 0 T U)) (generate t U)

def lemma10_4_6 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ t X T, t.LCAt 0 → X.1 = 0 → T.HasKind S [] 0 → X ∉ T.fv →
    Equivalent S M (Constraint.existsNames [X]
      (.conj (generate t (.free X)) (.le 0 (.free X) T))) (generate t T)

/-- Opening the lambda body exposes the free name bound by letName. -/
def lemma10_4_7 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ t z T U, t.LCAt 1 → Id.var z ∉ t.fpi →
    T.HasKind S [] 0 → U.HasKind S [] 0 → Equivalent S M
    (generate (.lam t) (.arrow T U))
    ((generate (Expr.openAt 0 (.ident (.free (.var z))) t) U).letName (.var z) (.mono T))

def theorem10_4_8_completeness (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ C Γ t T, Entails S M C Γ.exists_ → C.fpi ∪ Γ.fpi = ∅ →
    Typing S M C Γ t (.mono T) → Entails S M C (infer Γ t T)

def PrincipalConstraint (S : Signature) (M : Model) (Γ : Env) (t : Expr) (T : Ty)
    (D : Constraint) : Prop :=
  Typing S M D Γ t (.mono T) ∧
  ∀ C, Entails S M C Γ.exists_ → C.fpi ∪ Γ.fpi = ∅ →
    Typing S M C Γ t (.mono T) → Entails S M C D

def constraintGenerationPrincipality_scoped (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ Γ t T, Γ.WF S → Γ.fpi = ∅ → t.LCAt 0 → t.fpi ⊆ Γ.dpi →
    T.HasKind S [] 0 → PrincipalConstraint S M Γ t T (infer Γ t T)

end HMX.LN
