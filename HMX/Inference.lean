import HMX.Typing

namespace HMX

/-- A deterministic choice of the fresh normal variables in Figure 10-9. -/
def Ty.maxIndex : Ty → Nat
  | .var X => X.2
  | .con _ ts => (ts.map Ty.maxIndex).foldr max 0

def freshIndex (T : Ty) : Nat := T.maxIndex + 1

/-- Figure 10-9. Recursion is on the expression, not on a supplied derivation. -/
def generate : Expr → Ty → Constraint
  | .ident x, T => .inst x T
  | .lam z t, T =>
      let X : TVar := (0, freshIndex T)
      let Y : TVar := (0, freshIndex T + 1)
      .exists_ {X,Y} (.conj (.let_ (.var z) (.mono (.var X)) (generate t (.var Y)))
        (.le 0 (.arrow (.var X) (.var Y)) T))
  | .app t u, T =>
      let X : TVar := (0, freshIndex T)
      .exists_ {X} (.conj (generate t (.arrow (.var X) T)) (generate u (.var X)))
  | .letE z t u, T =>
      let X : TVar := (0, freshIndex T)
      .let_ (.var z) (.all {X} (generate t (.var X)) (.var X)) (generate u T)

def infer (Γ : Env) (t : Expr) (T : Ty) : Constraint := Γ.letIn (generate t T)

/-- p.432: the scheme produced for a let-bound expression. -/
def generatedScheme (t : Expr) (X : TVar) : Scheme := .all {X} (generate t (.var X)) (.var X)

/-- Theorem 10.4.4 [Soundness]. No unprinted free-identifier coverage condition
has been inserted; the scope question is recorded in audit ambiguity A-04. -/
def theorem10_4_4_soundness (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ Γ t T, Γ.WF S → Γ.fpi = ∅ → T.HasKind S 0 →
    Typing S M (infer Γ t T) Γ t (.mono T)

def lemma10_4_5 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ t T U, T.HasKind S 0 → U.HasKind S 0 →
    Entails S M (.conj (generate t T) (.le 0 T U)) (generate t U)

def lemma10_4_6 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ t X T, X.1 = 0 → T.HasKind S 0 → X ∉ T.fv →
    Equivalent S M (.exists_ {X} (.conj (generate t (.var X)) (.le 0 (.var X) T))) (generate t T)

def lemma10_4_7 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ z t T U, T.HasKind S 0 → U.HasKind S 0 →
    Equivalent S M (generate (.lam z t) (.arrow T U)) (.let_ (.var z) (.mono T) (generate t U))

def theorem10_4_8_completeness (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ C Γ t T, Entails S M C Γ.exists_ → C.fpi ∪ Γ.fpi = ∅ →
    Typing S M C Γ t (.mono T) → Entails S M C (infer Γ t T)

/-- p.429–430, unnumbered: least-specific constraint, under the qualifications of
10.4.8. This is a statement to be assessed, not a new assumption or a proof. -/
def PrincipalConstraint (S : Signature) (M : Model) (Γ : Env) (t : Expr) (T : Ty)
    (D : Constraint) : Prop :=
  Typing S M D Γ t (.mono T) ∧
  ∀ C, Entails S M C Γ.exists_ → C.fpi ∪ Γ.fpi = ∅ →
    Typing S M C Γ t (.mono T) → Entails S M C D

def constraintGenerationPrincipality (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ Γ t T, Γ.WF S → Γ.fpi = ∅ → T.HasKind S 0 →
    PrincipalConstraint S M Γ t T (infer Γ t T)

/-- Exercise 10.4.1, first assertion; no exercise solution is included. -/
def exercise10_4_1 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ Γ t X, X.1 = 0 → X ∉ Γ.fv →
    (∃ C T, Satisfiable S M C ∧ Typing S M C Γ t (.mono T)) →
    ∃ C, Satisfiable S M C ∧ Typing S M C Γ t (.mono (.var X))

end HMX
