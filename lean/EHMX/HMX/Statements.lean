import EHMX.HMX.TermReconstruction

/-! Statements awaiting proof. Each public declaration below defines a Prop;
it does not supply a proof or introduce an axiom. References are Sulzmann
(2000), §§3.6, 4.4, Appendix C.4. Approved EHMX changes are named explicitly. -/
namespace EHMX.HMX.Statements
variable {T : TypeSyntax} (X : Theory T) (S : X.Formula → Prop) (sig : Signature T)

/-- Theorem 7 changes the solved set, not the rule presentation. Both source
and target have the same fragment and presentation. -/
def Transformation (p : Presentation) (fragment : Fragment) : Prop :=
  (∀ c g g' e t eff, Typing p fragment sig X X.Satisfiable c g e (.mono t) eff →
    X.Admissible S c → Context.Approximates S c g g' →
    Typing p fragment sig X S c g' e (.mono t) eff) ∧
  (∀ c g g' e s eff, Typing p fragment sig X X.Satisfiable c g e s eff →
    X.Admissible S c → Context.Approximates S c g g' → s.Realizable c →
    ∃ s', Typing p fragment sig X S c g' e s' eff ∧ Scheme.Approximates S c s s')

/-- Original premises, with the retained value restriction and effects.
No full Definition 28 or global conjunction closure is assumed. -/
def theorem7 : Prop :=
  X.SolvedForms S → Logical.PrincipalNormalForms X S → X.ProjectionClosed S →
    Transformation X S sig .term .core

/-- Additional EHMX lifting obligation, explicitly stated on admissible
representatives rather than silently equated with literal Definition 28(iv). -/
def theorem7EHMX : Prop :=
  X.SolvedForms S → Logical.PrincipalNormalForms X S → X.ProjectionClosed S →
    X.AdmissibleLifting S → sig.Closed →
    ∀ p, Transformation X S sig p .handlers

/-- Lemma 20-style bridge is separate from the choice of solved set.
Only types expressible in the constraint presentation are compared. -/
def presentationCorrespondence (fragment : Fragment) : Prop :=
  ∀ c g e s eff, g.InPresentation .constraint → s.InPresentation .constraint →
    (Typing .term fragment sig X S c g e s eff ↔
      Typing .constraint fragment sig X S c g e s eff)

/-- Theorem 16 for the inference relation: fixedness is a conclusion.
There is no top-realizability assumption on the input environment. -/
def Soundness (fragment : Fragment) : Prop :=
  ∀ g e ψ c t eff, g.Admissible S →
    Nonempty (Reconstructs fragment sig X S g e ψ c t eff) →
    Typing .term fragment sig X S c (g.subst ψ) e (.mono t) eff ∧
    X.Equivalent (X.subst ψ c) c ∧ ψ.apply t = t ∧ eff.subst ψ.effects = eff

def theorem16 : Prop :=
  X.SolvedForms S → Logical.PrincipalNormalForms X S → X.ProjectionClosed S →
    Soundness X S sig .core

def theorem16EHMX : Prop :=
  X.SolvedForms S → Logical.PrincipalNormalForms X S → X.ProjectionClosed S →
    X.AdmissibleLifting S → sig.Closed → Soundness X S sig .handlers

/-- One finite factor witnesses the environment, scheme, residual and effect
comparisons together. The environment/effect agreement under C is the retained
EHMX change. Generalization is existential, not a maximal-binder function. -/
def CompleteResult (g : Context X) (σ ψ : FiniteSubstitution T) (c : X.Formula)
    (s : Scheme X) (eff : Effect) (d : X.Formula) (t : T.Term) (out : Effect) : Prop :=
  ∃ outer result, Generalizes S d (g.subst ψ) t outer result ∧
    ∃ φ : Substitution T, X.AgreesOn c (φ.compose ψ) σ g.freeNames ∧
      SolvedInstance X S c (result.subst φ) s ∧
      X.Entails c (X.subst φ outer) ∧ X.Entails c (X.effectEq (out.subst φ.effects) eff)

def Completeness (fragment : Fragment) : Prop :=
  ∀ g e (σ : Substitution T) c s eff,
    Typing .term fragment sig X S c (g.subst σ) e s eff → (g.subst σ).Realizable c →
    ∃ ψ d t out, Nonempty (Reconstructs fragment sig X S g e ψ d t out) ∧
      CompleteResult X S g σ ψ c s eff d t out

/-- Theorem 17 has no global projection or renaming closure premise. -/
def theorem17 : Prop :=
  X.SolvedForms S → Logical.PrincipalNormalForms X S → Completeness X S sig .core

def theorem17EHMX : Prop :=
  X.SolvedForms S → Logical.PrincipalNormalForms X S → X.AdmissibleLifting S →
    sig.Closed → Completeness X S sig .handlers

/-- Definition 29: principal constrained scheme pair. This is separate from
closed principal values and the EHMX computation-scheme property. -/
def PrincipalPair (fragment : Fragment) (g : Context X) (e : Expr)
    (c : X.Formula) (s : Scheme X) (eff : Effect) : Prop :=
  Typing .term fragment sig X S c g e s eff ∧
    ∀ d target, Typing .term fragment sig X S d g e target eff →
      X.Entails d c ∧ Instance X d s target

/-- Corollary 7's source-matching conclusion: generalize with outer top,
then compare with the original target. It is not replaced by a stronger
principal-computation assertion. -/
def ClosedCompleteness (fragment : Fragment) : Prop :=
  ∀ g e s eff, g.Closed → g.Realizable X.top →
    Typing .term fragment sig X S X.top g e s eff →
    ∃ ψ d t out result, Nonempty (Reconstructs fragment sig X S g e ψ d t out) ∧
      Generalizes S d (g.subst ψ) t X.top result ∧
      SolvedInstance X S X.top result s ∧ X.Entails X.top (X.effectEq out eff)

def corollary7 : Prop :=
  X.SolvedForms S → Logical.PrincipalNormalForms X S → ClosedCompleteness X S sig .core

def corollary7EHMX : Prop :=
  X.SolvedForms S → Logical.PrincipalNormalForms X S → X.AdmissibleLifting S →
    sig.Closed → ClosedCompleteness X S sig .handlers

/-- Obligations for the actual implementation, with the SAME N and P throughout.
These are additional obligations, not consequences asserted without proof of
the relation/implementation connection. -/
def implementationGeneration (N : X.Simplifier) : Prop :=
  sig.Closed → ∀ g e d,
    generateProjected sig X N g e (g.support.shiftTypes 0)
      (Effect.var (g.support.shiftEffects 0)) = some d →
    Nonempty (Generates .handlers sig X g e (g.support.shiftTypes 0)
      (Effect.var (g.support.shiftEffects 0)) d)

def implementationSoundness (N : X.Simplifier) (P : PrincipalNormalizer X S) : Prop :=
  X.SolvedForms S → X.ProjectionClosed S → X.AdmissibleLifting S → sig.Closed →
  ∀ g e n, g.Admissible S → inferTerm sig X N P g e = some (.reconstructed n) →
    let ψ := environmentSubstitution g n
    let t := inferredType g n
    let eff := inferredEffect g n
    Typing .term .handlers sig X S n.constraint (g.subst ψ) e (.mono t) eff ∧
    X.Equivalent (X.subst ψ n.constraint) n.constraint ∧ ψ.apply t = t ∧ eff.subst ψ.effects = eff

def implementationCompleteness (N : X.Simplifier) (P : PrincipalNormalizer X S) : Prop :=
  X.SolvedForms S → X.AdmissibleLifting S → sig.Closed →
  ∀ g e (σ : Substitution T) c s eff,
    Typing .term .handlers sig X S c (g.subst σ) e s eff → (g.subst σ).Realizable c →
    ∃ n, inferTerm sig X N P g e = some (.reconstructed n) ∧
      CompleteResult X S g σ (environmentSubstitution g n) c s eff n.constraint
        (inferredType g n) (inferredEffect g n)

def implementationCorollary7 (N : X.Simplifier) (P : PrincipalNormalizer X S) : Prop :=
  X.SolvedForms S → X.AdmissibleLifting S → sig.Closed →
  ∀ g e s eff, g.Closed → g.Realizable X.top →
    Typing .term .handlers sig X S X.top g e s eff →
    ∃ n result, inferTerm sig X N P g e = some (.reconstructed n) ∧
      Generalizes S n.constraint (g.subst (environmentSubstitution g n))
        (inferredType g n) X.top result ∧ SolvedInstance X S X.top result s ∧
      X.Entails X.top (X.effectEq (inferredEffect g n) eff)

def PrincipalValue (g : Context X) (e : Expr) (s : Scheme X) : Prop :=
  Value e ∧ Typing .term .handlers sig X S X.top g e s ∅ ∧
    ∀ c target, Typing .term .handlers sig X S c g e target ∅ → SolvedInstance X S c s target

/-- Stronger EHMX output obligations, distinct from original Corollary 7. -/
def implementationPrincipalComputation (N : X.Simplifier) (P : PrincipalNormalizer X S) : Prop :=
  X.SolvedForms S → X.ProjectionClosed S → X.AdmissibleLifting S → sig.Closed →
  ∀ g e n, g.Closed → g.Realizable X.top → g.Admissible S →
    inferTerm sig X N P g e = some (.reconstructed n) →
    ∃ result : ComputationScheme X,
      result.result = inferredType g n ∧ result.effect = inferredEffect g n ∧
      Generalizes S n.constraint (g.subst (environmentSubstitution g n))
        result.result result.outer result.valueScheme ∧
      PrincipalComputationScheme sig X S g e result ∧
      (Value e → PrincipalValue X S sig g e result.valueScheme)

end EHMX.HMX.Statements
