import EHMX.HMX.ReconstructionPrincipality

/-! HM(X) Theorems 16, 17 and Corollary 7 on the same prepared normalizer.
All additional hypotheses are explicit. Theorem 17 covers open environments
and qualified targets; its equalities hold under the target constraint. -/

namespace EHMX.HMX
open EHMX EHMX.HMX
open Constraints.ScopedPrincipalNormalizer
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
theorem theorem17
 {sig : Signature equalityTypes}
 (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
 (cl : X.SolvedClosure P.solved)
 (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
 (allow : ∀ (r : X.Formula) (s : HMX.Substitution equalityTypes), s.domain.types = ∅ →
   X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
   X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
 {g : Context X} {e : Expr} (σ : HMX.Substitution equalityTypes)
 {c : X.Formula} {s : Scheme X} {eff : Effect}
 (typed : Typing sig X P.solved c (g.subst σ) e s eff)
 (real : (g.subst σ).Realizable c) :
 ∃ n, inferTerm sig X N (prepare P allow) g e = some (.reconstructed n) ∧
   ∃ φ : HMX.Substitution equalityTypes,
     (∀ v, X.holds c v →
       (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) g.support) ∧
     Instance X c ((reconstructedScheme g n).valueScheme.subst φ) s ∧
     X.Entails c (X.subst φ (reconstructedScheme g n).outer) ∧
     ∀ v, X.holds c v →
       (reconstructedScheme g n).effect.eval (φ.pullback v).effects = eff.eval v.effects :=
 inferTerm_complete_scheme N (prepare P allow) cl reflect (prepare_shape P allow) σ typed real
end EHMX.HMX

namespace EHMX.HMX
open EHMX EHMX.HMX
open Constraints.ScopedPrincipalNormalizer
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
theorem theorem16 {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (cl : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hsig : sig.Closed)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (run : inferTerm sig X N (prepare P allow) g e = some (.reconstructed n))
    (real : g.Realizable X.top)
    (envAdm : (g.subst n.substitution).Admissible P.solved) :
    Typing sig X P.solved n.residual (g.subst n.substitution) e
      (.mono (n.substitution.types (g.support.shiftTypes 0))) (n.substitution.effects (g.support.shiftEffects 0)) := by
  exact inferTerm_sound N (prepare P allow) cl reflect allow lift hr truth hsig run real envAdm

theorem corollary7 {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (cl : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hsig : sig.Closed)
    {g : Context X} {e : Expr} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X P.solved X.top g e s eff)
    (closed : g.support = Names.empty) (real : g.Realizable X.top) :
    ∃ n, inferTerm sig X N (prepare P allow) g e = some (.reconstructed n) ∧
    let result := reconstructedScheme g n
    X.Equivalent result.outer X.top ∧
    PrincipalComputationScheme sig X P.solved g e result ∧
    (∀ c t eff, Typing sig X P.solved c g e (.mono t) eff →
      result.FiniteInstance c t eff) ∧
    (∀ c s eff, Typing sig X P.solved c g e s eff →
      Instance X c result.valueScheme s) ∧
    (Value e → PrincipalPair (fun c g e s => Typing sig X P.solved c g e s ∅)
      g e X.top result.valueScheme) := by
 exact EHMX.HMX.Typing.corollary7 N (prepare P allow) cl reflect allow lift hr truth hsig
   typed closed real

end EHMX.HMX
