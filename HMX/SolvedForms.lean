import HMX.ConstraintLaws
import HMX.Typing

namespace HMX

/-- Example 10.2.6: the carrier consists exactly of finite closed well-kinded terms.
The representation map is part of the model description, not a solver oracle. -/
def SyntacticModel (S : Signature) (M : Model) : Prop :=
  ∃ decode : M.Carrier → Ty,
    (∀ v, (decode v).HasKind S (M.kind v) ∧ (decode v).fv = ∅) ∧
    Function.Injective decode ∧
    (∀ T k, T.HasKind S k → T.fv = ∅ → ∃ v, M.kind v = k ∧ decode v = T) ∧
    (∀ f ∈ S.constructors, ∀ vs,
      List.Forall₂ (fun v p => M.kind v = p.2) vs (S.parameters f) →
      decode (M.constructor f vs) = .con f (vs.map decode))

/-- Example 10.2.8: equality-only additionally excludes other predicate symbols. -/
def EqualityOnly (S : Signature) (M : Model) : Prop :=
  S.predicates = ∅ ∧ ∀ k ∈ S.kinds, ∀ a b,
    M.kind a = k → M.kind b = k → (M.below k a b ↔ a = b)

/-- p.421: both nondegeneracy conditions, including inhabited constructor roots. -/
def Nondegenerate (S : Signature) (M : Model) : Prop :=
  (∀ k ∈ S.kinds, ∃ f ∈ S.constructors, ∃ g ∈ S.constructors,
    f ≠ g ∧ S.result f = k ∧ S.result g = k) ∧
  (∀ f ∈ S.constructors, ∃ vs,
    List.Forall₂ (fun v p => M.kind v = p.2) vs (S.parameters f))

def EqualitySyntacticSetting (S : Signature) (M : Model) : Prop :=
  M.Requirements S ∧ SyntacticModel S M ∧ EqualityOnly S M ∧ Nondegenerate S M

/-- Definition 10.2.18: X need not be disjoint from the quantified Y. -/
def SolvedForm (S : Signature) (C : Constraint) : Prop :=
  ∃ (A : Vars) (es : Equations), es.WF S ∧ Disjoint es.dom es.range ∧
    C = .exists_ A es.constraint ∧ C.WF S

/-- Definition 10.2.20. -/
def CanonicalSolvedForm (S : Signature) (C : Constraint) : Prop :=
  ∃ (A : Vars) (es : Equations), es.WF S ∧ es.range ⊆ A ∧ Disjoint es.dom A ∧
    C = .exists_ A es.constraint ∧ C.WF S

/-- Definition 10.2.22: enumerate the *actual* domain, not an arbitrary support. -/
def Subst.Closure (θ : Subst) (C : Constraint) : Prop :=
  ∃ xs : List TVar, xs.Nodup ∧ (∀ X, X ∈ xs ↔ X ∈ θ.dom) ∧
    let es : Equations := xs.map (fun X => (X, θ X))
    C = .exists_ es.range es.constraint

def MostGeneralUnifier (S : Signature) (M : Model) (θ : Subst) (C : Constraint) : Prop :=
  θ.Valid S ∧ θ.Idempotent ∧ ∃ D, θ.Closure D ∧ Equivalent S M D C

def lemma10_2_19 (S : Signature) (M : Model) : Prop :=
  EqualitySyntacticSetting S M → ∀ C, C.WF S → C.fpi = ∅ →
    (∃ D, SolvedForm S D ∧ Equivalent S M C D) ∨ Equivalent S M C .falsity

def lemma10_2_21 (S : Signature) (M : Model) : Prop :=
  EqualitySyntacticSetting S M → ∀ C, SolvedForm S C →
    ∃ D, CanonicalSolvedForm S D ∧ Equivalent S M C D

/-- p.428 omits the construction of this translation. These two functions are
explicit source parameters. No correctness theorem is included as a field. -/
structure DMTranslation where
  scheme : Subst → Scheme → DMScheme
  environment : Subst → Env → DMEnv

/-- The domain of the omitted scheme translation, as printed on p.428. -/
def TranslationDomain (S : Signature) (M : Model) (θ : Subst) (s : Scheme) : Prop :=
  θ.Valid S ∧ θ.Idempotent ∧ s.WF S ∧ (↑s.fv : Set TVar) ⊆ θ.dom ∧
    ∃ D, θ.Closure D ∧ Entails S M D s.exists_

/-- The printed intended meaning, retained separately from Theorem 10.3.7.
This specification neither supplies the omitted construction nor proves adequacy. -/
def DMTranslation.Meaning (S : Signature) (M : Model) (tr : DMTranslation) : Prop :=
  (∀ θ s, TranslationDomain S M θ s → (tr.scheme θ s).WF S ∧
    ∀ s', s.Substitutes θ s' → ∀ ρ ι, ρ.Valid S M → ι.Valid M →
      ((tr.scheme θ s).embed).denote S M ρ ι = s'.denote S M ρ ι) ∧
  (∀ θ Γ, Γ.WF S → (↑Γ.fv : Set TVar) ⊆ θ.dom →
    tr.environment θ Γ = Γ.map (fun p => (p.1, tr.scheme θ p.2)))

/-- Theorem 10.3.7. The source symbol J·Kθ remains the named parameter tr.
Meaning is not assumed here as a substitute for the missing definition. -/
def theorem10_3_7 (S : Signature) (M : Model) (tr : DMTranslation) : Prop :=
  EqualitySyntacticSetting S M → ∀ C Γ t s θ,
    Typing S M C Γ t s → MostGeneralUnifier S M θ C →
    (↑(Γ.fv ∪ s.fv) : Set TVar) ⊆ θ.dom →
    DMTyping S (tr.environment θ Γ) t (tr.scheme θ s)

end HMX
