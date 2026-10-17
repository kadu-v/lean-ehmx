import HMX.LocallyNameless.Correspondence

/-! Additional obligations for the §10.4 proof route. These are propositions,
not new assumptions of Framework. Proofs are separate declarations; see
docs/proofs.md for their scope and provenance. -/
namespace HMX.LN

def termOpeningClosing : Prop :=
  (∀ (t : Expr) (z : Nat), t.LCAt 0 → Expr.openAt 0 (.ident (.free (.var z))) (t.closeAt 0 z) = t) ∧
  (∀ (t : Expr) (z : Nat), t.LCAt 1 → Id.var z ∉ t.fpi →
    (Expr.openAt 0 (.ident (.free (.var z))) t).closeAt 0 z = t)

def typeOpeningClosing : Prop :=
  (∀ (xs : List TVar) (T : Ty), xs.Nodup → T.LCAt 0 →
    (T.closeAt 0 xs).openAt 0 (xs.map Ty.free) = T) ∧
  (∀ (xs : List TVar) (T : Ty), xs.Nodup → T.LCAt xs.length → Disjoint xs.toFinset T.fv →
    (T.openAt 0 (xs.map Ty.free)).closeAt 0 xs = T)

def constraintOpeningClosing (S : Signature) : Prop :=
  ∀ (xs : List TVar) (C : Constraint), xs.Nodup → C.WF S [] 0 →
    (C.closeTypes xs).openTypes (xs.map Ty.free) = C

def typeOpeningWF (S : Signature) : Prop :=
  ∀ (ks : List Nat) (us : List Ty) (C : Constraint), C.WF S ks 0 → List.Forall₂ (Ty.HasKind S []) us ks →
    (C.openTypes us).WF S [] 0

def freeSubstitutionWF (S : Signature) : Prop :=
  ∀ (θ : Subst), θ.Valid S →
  (∀ (ks : List Nat) (T : Ty) (k : Nat), T.HasKind S ks k → (T.subst θ).HasKind S ks k) ∧
  (∀ (ks : List Nat) (d : Nat) (C : Constraint), C.WF S ks d → (C.subst θ).WF S ks d) ∧
  (∀ (ks : List Nat) (d : Nat) (s : Scheme), s.WF S ks d → (s.subst θ).WF S ks d)

def termOpeningSubstitution : Prop :=
  ∀ (t : Expr) (v : Expr) (z : Nat) (x : Nat), t.LCAt 1 → v.LCAt 0 → x ≠ z →
    Expr.subst z v (Expr.openAt 0 (.ident (.free (.var x))) t) =
      Expr.openAt 0 (.ident (.free (.var x))) (Expr.subst z v t)

def typeOpeningSubstitution (S : Signature) : Prop :=
  ∀ (θ : Subst) (ks : List Nat) (us : List Ty) (C : Constraint), θ.Valid S → C.WF S ks 0 → List.Forall₂ (Ty.HasKind S []) us ks →
    (C.openTypes us).subst θ = (C.subst θ).openTypes (us.map (Ty.subst θ))

def evaluationKind (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (ρ : Assignment M) (β : Nat → M.Carrier) (ks : List Nat) (T : Ty) (k : Nat), ρ.Valid S M →
    (∀ (i : Nat) (j : Nat), ks[i]? = some j → M.kind (β i) = j) → T.HasKind S ks k →
    M.kind (T.evalAt M ρ β) = k

def schemeDenotationValid (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (ρ : Assignment M) (ι : GroundEnv M) (s : Scheme) (x : Id), ρ.Valid S M → ι.Valid M → s.WF S [] 0 →
    GroundEnv.Valid M (fun y => if y = x then s.denote S M ρ ι else ι y)

def semanticLocality (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (ρ : Assignment M) (ρ' : Assignment M) (ι : GroundEnv M) (ι' : GroundEnv M), ρ.Valid S M → ρ'.Valid S M → ι.Valid M → ι'.Valid M →
  (∀ (C : Constraint), C.WF S [] 0 → (∀ X ∈ C.fv, ρ X = ρ' X) → (∀ x ∈ C.fpi, ι x = ι' x) →
    (C.Holds S M ρ ι ↔ C.Holds S M ρ' ι')) ∧
  (∀ (s : Scheme), s.WF S [] 0 → (∀ X ∈ s.fv, ρ X = ρ' X) → (∀ x ∈ s.fpi, ι x = ι' x) →
    s.denote S M ρ ι = s.denote S M ρ' ι')

def semanticSubstitution (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (θ : Subst) (ρ : Assignment M) (ι : GroundEnv M), θ.Valid S → ρ.Valid S M → ι.Valid M →
    let ρ' := fun X => (θ X).eval M ρ
    Assignment.Valid S M ρ' ∧
    (∀ (C : Constraint), C.WF S [] 0 → ((C.subst θ).Holds S M ρ ι ↔ C.Holds S M ρ' ι)) ∧
    (∀ (s : Scheme), s.WF S [] 0 → (s.subst θ).denote S M ρ ι = s.denote S M ρ' ι)

def binderPermutationSemantics (S : Signature) (M : Model) : Prop :=
  M.Requirements S →
  (∀ (C : Constraint) (D : Constraint), C.WF S [] 0 → D.WF S [] 0 → C.BinderEq D → Equivalent S M C D) ∧
  (∀ (s : Scheme) (r : Scheme) (ρ : Assignment M) (ι : GroundEnv M), s.WF S [] 0 → r.WF S [] 0 → s.BinderEq r →
    ρ.Valid S M → ι.Valid M → s.denote S M ρ ι = r.denote S M ρ ι)

def groundEnvironmentMonotonicity (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (ρ : Assignment M) (ι : GroundEnv M) (ι' : GroundEnv M), ρ.Valid S M → ι.Valid M → ι'.Valid M → (∀ (x : Id), ι x ⊆ ι' x) →
  (∀ (C : Constraint), C.WF S [] 0 → C.Holds S M ρ ι → C.Holds S M ρ ι') ∧
  (∀ (s : Scheme), s.WF S [] 0 → s.denote S M ρ ι ⊆ s.denote S M ρ ι')

/-- Contexts use named closing operations to express the source's capturing plug. -/
inductive Context where
  | hole
  | fixed : Constraint → Context
  | conj : Context → Context → Context
  | exists_ : List TVar → Context → Context
  | define : Id → List TVar → Context → Ty → Context → Context

def Context.plug (D : Constraint) : Context → Constraint
  | .hole => D
  | .fixed C => C
  | .conj K L => .conj (K.plug D) (L.plug D)
  | .exists_ xs K => (K.plug D).existsNames xs
  | .define x xs K T L => (L.plug D).define x (Scheme.generalize xs (K.plug D) T)

def constraintCongruence (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (K : Context) (C : Constraint) (D : Constraint), C.WF S [] 0 → D.WF S [] 0 →
    (Context.plug C K).WF S [] 0 → (K.plug D).WF S [] 0 →
    Entails S M C D → Entails S M (K.plug C) (K.plug D)

def EquationLaw (S : Signature) (M : Model) (C D : Constraint) : Prop :=
  C.WF S [] 0 → D.WF S [] 0 → Equivalent S M C D

/-- The elementary fragment of Figure 10-6 needed before generation covariance. -/
def basicConstraintLaws (S : Signature) (M : Model) : Prop :=
  M.Requirements S →
  (∀ C D, EquationLaw S M (.conj C D) (.conj D C)) ∧
  (∀ C D E, EquationLaw S M (.conj (.conj C D) E) (.conj C (.conj D E))) ∧
  (∀ C, EquationLaw S M (.conj C .truth) C) ∧
  (∀ C D, Entails S M C D → EquationLaw S M (.conj C D) C) ∧
  (∀ (xs : List TVar) (C : Constraint), xs.Nodup → Disjoint xs.toFinset C.fv →
    EquationLaw S M (C.existsNames xs) C) ∧
  (∀ (xs : List TVar) (C D : Constraint), xs.Nodup → Disjoint xs.toFinset D.fv →
    EquationLaw S M (.conj (C.existsNames xs) D) ((Constraint.conj C D).existsNames xs)) ∧
  (∀ (T : Ty) k, T.HasKind S [] k → Entails S M .truth (.le k T T)) ∧
  (∀ (T U V : Ty) k, T.HasKind S [] k → U.HasKind S [] k → V.HasKind S [] k →
    Entails S M (.conj (.le k T U) (.le k U V)) (.le k T V)) ∧
  (∀ (X : TVar) (T : Ty), T.HasKind S [] X.1 → X ∉ T.fv →
    EquationLaw S M ((Constraint.eq X.1 (.free X) T).existsNames [X]) .truth)

def letSub (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (X : TVar) (x : Id) (T : Ty) (C : Constraint),
    X.1 = 0 → X ∉ T.fv ∪ C.fv → EquationLaw S M
    ((Constraint.conj (.le 0 T (.free X)) (C.letName x (.mono (.free X)))).existsNames [X])
    (C.letName x (.mono T))

def prefixConjunction (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (Γ : Env) (C : Constraint) (D : Constraint),
    EquationLaw S M (Env.letIn Γ (.conj C D)) (.conj (Γ.letIn C) (Γ.letIn D))

def prefixExists (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (Γ : Env) (xs : List TVar) (C : Constraint), xs.Nodup → Disjoint xs.toFinset (Env.fv Γ) →
    EquationLaw S M (Γ.letIn (C.existsNames xs)) ((Γ.letIn C).existsNames xs)

def prefixLookup (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (Γ : Env) (x : Id) (s : Scheme) (T : Ty), Γ.WF S → Γ.fpi = ∅ → lookup Γ x = some s →
    EquationLaw S M (Γ.letIn (.inst (.free x) T)) (.conj Γ.exists_ (s.instanceConstraint T))

def letDup (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (Γ : Env) (x : Id) (xs : List TVar) (C : Constraint) (T : Ty) (D : Constraint), Γ.WF S → Γ.fpi = ∅ →
    xs.Nodup → Disjoint xs.toFinset Γ.fv → EquationLaw S M
    ((Γ ++ [(x, Scheme.generalize xs C T)]).letIn D)
    ((Γ ++ [(x, Scheme.generalize xs (Γ.letIn C) T)]).letIn D)

def letSchemeMonotonicity (S : Signature) (M : Model) : Prop :=
  M.Requirements S → ∀ (C : Constraint) (x : Id) (s : Scheme) (r : Scheme) (D : Constraint), C.WF S [] 0 → s.WF S [] 0 → r.WF S [] 0 →
    D.WF S [] 0 → Scheme.IncludedUnder S M C s r →
    Entails S M (.conj C (D.letName x s)) (D.letName x r)

def generationWF (S : Signature) : Prop :=
  S.Valid → ∀ (d : Nat) (t : Expr) (T : Ty), t.LCAt d → T.HasKind S [] 0 → (generate t T).WF S [] d

def generationFreeVariables : Prop :=
  ∀ (t : Expr) (T : Ty), (generate t T).fv ⊆ T.fv ∧ (generate t T).fpi = t.fpi

def generationSubstitution (S : Signature) : Prop :=
  S.Valid → ∀ (θ : Subst) (t : Expr) (T : Ty), θ.Valid S → t.LCAt 0 → T.HasKind S [] 0 →
    ((generate t T).subst θ).BinderEq (generate t (T.subst θ))

def generationOpening : Prop :=
  ∀ (t : Expr) (z : Nat) (T : Ty), t.LCAt 1 → T.LCAt 0 →
    (generate t T).openId (.var z) = generate (Expr.openAt 0 (.ident (.free (.var z))) t) T

def generationFreshChoices (S : Signature) : Prop :=
  S.Valid → ∀ (t : Expr) (u : Expr) (T : Ty) (X : TVar) (Y : TVar), t.LCAt 1 → u.LCAt 1 → T.HasKind S [] 0 →
    X.1 = 0 → Y.1 = 0 → X ≠ Y → X ∉ T.fv → Y ∉ T.fv →
  (generate (.lam t) T).BinderEq (Constraint.existsNames [X,Y] (.conj
    (.letBound .term (.mono (.free X)) (generate t (.free Y)))
    (.le 0 (.arrow (.free X) (.free Y)) T))) ∧
  (generate (.app t u) T).BinderEq (Constraint.existsNames [X]
    (.conj (generate t (.arrow (.free X) T)) (generate u (.free X)))) ∧
  (generate (.letE t u) T).BinderEq
    (.letBound .term (Scheme.generalize [X] (generate t (.free X)) (.free X)) (generate u T))

def closedGenerationWF (S : Signature) : Prop :=
  S.Valid → ∀ (Γ : Env) (t : Expr) (X : TVar), Γ.WF S → Γ.fpi = ∅ → t.LCAt 0 → t.fpi ⊆ Γ.dpi → X.1 = 0 →
    X ∉ Γ.fv → (closedGeneratedScheme Γ t X).WF S [] 0 ∧
    (closedGeneratedScheme Γ t X).fpi = ∅ ∧ (closedGeneratedScheme Γ t X).fv ⊆ Γ.fv

def generatedInstance (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ (Γ : Env) (t : Expr) (X : TVar) (T : Ty), Γ.WF S → Γ.fpi = ∅ → t.LCAt 0 →
    X.1 = 0 → X ∉ Γ.fv ∪ T.fv → T.HasKind S [] 0 →
    Equivalent S M ((closedGeneratedScheme Γ t X).instanceConstraint T) (infer Γ t T)

def generalizedLetComparison (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ (C : Constraint) (Γ : Env) (t : Expr) (xs : List TVar) (D : Constraint) (T : Ty) (X : TVar), C.WF S [] 0 → D.WF S [] 0 →
    T.HasKind S [] 0 → Γ.WF S → Γ.fpi = ∅ → t.LCAt 0 → xs.Nodup →
    (∀ Y ∈ xs, Y.1 ∈ S.kinds) → Disjoint xs.toFinset (C.fv ∪ Γ.fv) →
    X.1 = 0 → X ∉ C.fv ∪ Γ.fv ∪ D.fv ∪ T.fv →
    Entails S M (.conj C D) (infer Γ t T) →
    Scheme.IncludedUnder S M C (Scheme.generalize xs D T) (closedGeneratedScheme Γ t X)

def typingProperties (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ (C : Constraint) (Γ : Env) (t : Expr) (s : Scheme), Typing S M C Γ t s →
    JudgmentWF S C Γ t s ∧ t.fpi ⊆ Γ.dpi ∧ Entails S M C s.exists_

def lemma10_3_1_weakening (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ (C : Constraint) (D : Constraint) (Γ : Env) (t : Expr) (s : Scheme) (d : Shape), JudgmentWF S D Γ t s →
    Entails S M D C → Derivation S M C Γ t s d → Derivation S M D Γ t s d

def alternateWeakening (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ (C : Constraint) (D : Constraint) (Γ : Env) (t : Expr) (T : Ty), JudgmentWF S D Γ t (.mono T) →
    Entails S M D C → AlternateTyping S M C Γ t T → AlternateTyping S M D Γ t T

def alternateSubstitution (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ (θ : Subst) (C : Constraint) (Γ : Env) (t : Expr) (T : Ty), θ.Valid S → AlternateTyping S M C Γ t T →
    AlternateTyping S M (C.subst θ) (Γ.subst θ) t (T.subst θ)

def schemeElimination (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ (C : Constraint) (Γ : Env) (t : Expr) (xs : List TVar) (D : Constraint) (T : Ty), xs.Nodup → D.WF S [] 0 → T.HasKind S [] 0 →
    Typing S M C Γ t (Scheme.generalize xs D T) → AlternateTyping S M (.conj C D) Γ t T

def theorem10_3_4 (S : Signature) (M : Model) (I : Set Nat) : Prop :=
  Framework S M I → ∀ (C : Constraint) (Γ : Env) (t : Expr) (T : Ty), AlternateTyping S M C Γ t T ↔ Typing S M C Γ t (.mono T)

end HMX.LN
