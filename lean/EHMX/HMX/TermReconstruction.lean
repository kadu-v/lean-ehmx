import EHMX.HMX.Generation
import EHMX.HMX.ComputationSchemes

namespace EHMX.HMX
variable {T : TypeSyntax}

inductive ReconstructionResult (X : Theory T) where
  | reconstructed : X.Problem → ReconstructionResult X
  | unrepresented : X.Formula → ReconstructionResult X

/-- An implementation strategy; the inductive relation also permits Equ at
other stages. Generalization is a separate relation, not a fixed output here. -/
noncomputable def inferTermAt (sig : Signature T) (X : Theory T)
    (N : X.Simplifier) {S : X.Formula → Prop} (P : PrincipalNormalizer X S)
    (g : Context X) (e : Expr) (i : Nat) (eff : Effect) : Option (ReconstructionResult X) :=
  (generateProjected sig X N g e i eff).map fun d =>
    match P.run (Logical.ConstraintProblem.identityProblem d) with
    | some n => .reconstructed n
    | none => .unrepresented d

noncomputable def inferTerm (sig : Signature T) (X : Theory T)
    (N : X.Simplifier) {S : X.Formula → Prop} (P : PrincipalNormalizer X S)
    (g : Context X) (e : Expr) : Option (ReconstructionResult X) :=
  inferTermAt sig X N P g e (g.support.shiftTypes 0) (Effect.var (g.support.shiftEffects 0))

noncomputable def environmentSubstitution {X : Theory T} (g : Context X) (n : X.Problem) :
    FiniteSubstitution T := n.substitution.restrict g.freeNames

def inferredType {X : Theory T} (g : Context X) (n : X.Problem) : T.Term :=
  n.substitution.types (g.support.shiftTypes 0)

def inferredEffect {X : Theory T} (g : Context X) (n : X.Problem) : Effect :=
  n.substitution.effects (g.support.shiftEffects 0)

end EHMX.HMX
