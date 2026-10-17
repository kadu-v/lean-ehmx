import HMX.Binding
import HMX.Semantics
import Mathlib.Logic.Relation

namespace HMX

inductive Shape where
  | node : Nat → List Shape → Shape

def DMJudgmentWF (S : Signature) (Γ : DMEnv) (s : DMScheme) : Prop := Γ.WF S ∧ s.WF S

def JudgmentWF (S : Signature) (C : Constraint) (Γ : Env) (s : Scheme) : Prop :=
  C.WF S ∧ Γ.WF S ∧ s.WF S ∧ C.fpi = ∅ ∧ Γ.fpi = ∅ ∧ s.fpi = ∅

def Env.Alpha (Γ Δ : Env) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2.Alpha q.2) Γ Δ

def DMEnv.Alpha (Γ Δ : DMEnv) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ p.2.Alpha q.2) Γ Δ

/-- Figure 10-3. Conversion expresses the stated identification by α-conversion;
it is not an additional mathematical result. -/
inductive DMDerivation (S : Signature) : DMEnv → Expr → DMScheme → Shape → Prop where
  | var : DMJudgmentWF S Γ s → lookup Γ x = some s →
      DMDerivation S Γ (.ident x) s (.node 0 [])
  | abs : DMJudgmentWF S Γ (.mono (.arrow T U)) →
      DMDerivation S (Γ ++ [(.var z, .mono T)]) t (.mono U) d →
      DMDerivation S Γ (.lam z t) (.mono (.arrow T U)) (.node 1 [d])
  | app : DMJudgmentWF S Γ (.mono U) →
      DMDerivation S Γ t (.mono (.arrow T U)) d → DMDerivation S Γ u (.mono T) e →
      DMDerivation S Γ (.app t u) (.mono U) (.node 2 [d,e])
  | letE : DMJudgmentWF S Γ (.mono T) → DMDerivation S Γ t s d →
      DMDerivation S (Γ ++ [(.var z, s)]) u (.mono T) e →
      DMDerivation S Γ (.letE z t u) (.mono T) (.node 3 [d,e])
  | gen : DMJudgmentWF S Γ ⟨A,T⟩ → DMDerivation S Γ t (.mono T) d → Disjoint A Γ.fv →
      DMDerivation S Γ t ⟨A,T⟩ (.node 4 [d])
  | inst : DMJudgmentWF S Γ (.mono U) → DMDerivation S Γ t s d → s.Instance S U →
      DMDerivation S Γ t (.mono U) (.node 5 [d])
  | convert : DMJudgmentWF S Δ s' → DMDerivation S Γ t s d →
      Γ.Alpha Δ → t.Alpha t' → s.Alpha s' → DMDerivation S Δ t' s' d

def DMTyping (S : Signature) (Γ : DMEnv) (t : Expr) (s : DMScheme) : Prop :=
  ∃ d, DMDerivation S Γ t s d

/-- Figure 10-7. The constraint is arbitrary, and may be unsatisfiable. -/
inductive Derivation (S : Signature) (M : Model) :
    Constraint → Env → Expr → Scheme → Shape → Prop where
  | var : JudgmentWF S C Γ s → lookup Γ x = some s → Entails S M C s.exists_ →
      Derivation S M C Γ (.ident x) s (.node 0 [])
  | abs : JudgmentWF S C Γ (.mono (.arrow T U)) →
      Derivation S M C (Γ ++ [(.var z, .mono T)]) t (.mono U) d →
      Derivation S M C Γ (.lam z t) (.mono (.arrow T U)) (.node 1 [d])
  | app : JudgmentWF S C Γ (.mono U) →
      Derivation S M C Γ t (.mono (.arrow T U)) d → Derivation S M C Γ u (.mono T) e →
      Derivation S M C Γ (.app t u) (.mono U) (.node 2 [d,e])
  | letE : JudgmentWF S C Γ (.mono T) → Derivation S M C Γ t s d →
      Derivation S M C (Γ ++ [(.var z, s)]) u (.mono T) e →
      Derivation S M C Γ (.letE z t u) (.mono T) (.node 3 [d,e])
  | gen : JudgmentWF S (.conj C (.exists_ A D)) Γ (.all A D T) →
      Derivation S M (.conj C D) Γ t (.mono T) d → Disjoint A (C.fv ∪ Γ.fv) →
      Derivation S M (.conj C (.exists_ A D)) Γ t (.all A D T) (.node 4 [d])
  | inst : JudgmentWF S (.conj C D) Γ (.mono T) →
      Derivation S M C Γ t (.all A D T) d →
      Derivation S M (.conj C D) Γ t (.mono T) (.node 5 [d])
  | sub : JudgmentWF S C Γ (.mono U) → Derivation S M C Γ t (.mono T) d →
      Entails S M C (.le 0 T U) → Derivation S M C Γ t (.mono U) (.node 6 [d])
  | exists_ : JudgmentWF S (.exists_ A C) Γ s → Derivation S M C Γ t s d →
      Disjoint A (Γ.fv ∪ s.fv) → Derivation S M (.exists_ A C) Γ t s (.node 7 [d])
  | convert : JudgmentWF S D Δ s' → Derivation S M C Γ t s d →
      Equivalent S M C D → Γ.Alpha Δ → t.Alpha t' → s.Alpha s' →
      Derivation S M D Δ t' s' d

def Typing (S : Signature) (M : Model) (C : Constraint) (Γ : Env) (t : Expr) (s : Scheme) : Prop :=
  ∃ d, Derivation S M C Γ t s d

/-- Figure 10-8 (hmd): monotypes only. -/
inductive AlternateTyping (S : Signature) (M : Model) : Constraint → Env → Expr → Ty → Prop where
  | varInst : JudgmentWF S (.conj C D) Γ (.mono T) →
      lookup Γ x = some (.all A D T) → AlternateTyping S M (.conj C D) Γ (.ident x) T
  | abs : JudgmentWF S C Γ (.mono (.arrow T U)) →
      AlternateTyping S M C (Γ ++ [(.var z, .mono T)]) t U →
      AlternateTyping S M C Γ (.lam z t) (.arrow T U)
  | app : JudgmentWF S C Γ (.mono U) → AlternateTyping S M C Γ t (.arrow T U) →
      AlternateTyping S M C Γ u T → AlternateTyping S M C Γ (.app t u) U
  | letGen : JudgmentWF S (.conj C (.exists_ A D)) Γ (.mono U) →
      AlternateTyping S M (.conj C D) Γ t T → Disjoint A (C.fv ∪ Γ.fv) →
      AlternateTyping S M (.conj C (.exists_ A D)) (Γ ++ [(.var z, .all A D T)]) u U →
      AlternateTyping S M (.conj C (.exists_ A D)) Γ (.letE z t u) U
  | sub : JudgmentWF S C Γ (.mono U) → AlternateTyping S M C Γ t T →
      Entails S M C (.le 0 T U) → AlternateTyping S M C Γ t U
  | exists_ : JudgmentWF S (.exists_ A C) Γ (.mono T) → AlternateTyping S M C Γ t T →
      Disjoint A (Γ.fv ∪ T.fv) → AlternateTyping S M (.exists_ A C) Γ t T
  | convert : JudgmentWF S D Δ (.mono T) → AlternateTyping S M C Γ t T →
      Equivalent S M C D → Γ.Alpha Δ → t.Alpha t' → AlternateTyping S M D Δ t' T

def DMScheme.embed (s : DMScheme) : Scheme := .all s.bound .truth s.body
def DMEnv.embed (Γ : DMEnv) : Env := Γ.map (fun p => (p.1, p.2.embed))

def WellTypedProgram (S : Signature) (M : Model) (Γ : Env) (t : Expr) : Prop :=
  t.Closed ∧ Γ.fv = ∅ ∧ ∃ C s, Satisfiable S M C ∧ Typing S M C Γ t s

/-- Lemma 10.3.1 [Weakening], including preservation of derivation shape. -/
def lemma10_3_1_weakening (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ C D Γ t s d, JudgmentWF S D Γ s →
    Entails S M D C → Derivation S M C Γ t s d → Derivation S M D Γ t s d

/-- Exercise 10.3.2: the admissibility assertion, not its solution. -/
def exercise10_3_2 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ C Γ t A D T θ D', θ.Valid S → θ.dom ⊆ ↑A →
    D.Substitutes θ D' → Typing S M C Γ t (.all A D T) → Entails S M C D' →
    Typing S M C Γ t (.mono (T.subst θ))

def theorem10_3_4 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ C Γ t T,
    AlternateTyping S M C Γ t T ↔ Typing S M C Γ t (.mono T)

def theorem10_3_6 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ Γ t s, DMTyping S Γ t s → Typing S M .truth Γ.embed t s.embed

/-- p.405: the two permitted steps in the definition of a principal DM scheme. -/
inductive DMScheme.Specializes (S : Signature) (Γ : DMEnv) : DMScheme → DMScheme → Prop where
  | inst : s.Instance S T → Specializes S Γ s (.mono T)
  | gen : Disjoint A Γ.fv → (DMScheme.mk A T).WF S →
      Specializes S Γ (.mono T) ⟨A,T⟩
  | alpha : s.Alpha s' → Specializes S Γ s s'

def DMPrincipalScheme (S : Signature) (Γ : DMEnv) (t : Expr) (s : DMScheme) : Prop :=
  DMTyping S Γ t s ∧ ∀ s', DMTyping S Γ t s' →
    Relation.ReflTransGen (DMScheme.Specializes S Γ) s s'

/-- p.405, unnumbered existence claim; algorithm implementation is outside this scope. -/
def dmPrincipalSchemeExistence (S : Signature) : Prop :=
  S.Valid → ∀ Γ t, Γ.fv = ∅ → (∃ s, DMTyping S Γ t s) →
    ∃ s, DMPrincipalScheme S Γ t s

end HMX
