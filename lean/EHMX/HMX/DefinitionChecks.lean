import EHMX.HMX.Statements
import EHMX.HMX.LogicalTheoryChecks

/-! Regression checks of definitions, not proofs of the four statements. -/
namespace EHMX.HMX.DefinitionChecks
open LogicalChecks

private def predicates : PredicateSignature := ⟨Unit, fun _ => 1, fun _ => 1⟩
private abbrev F := ConstraintSyntax variableArrowSyntax predicates

-- A free type name in an image must not be captured by an existential binder.
private def typeCapture : F :=
  .existsNames ⟨{1}, ∅⟩ (.atom (.typeEq (.var 0) (.var 1)))
#guard (typeCapture.subst (FiniteSubstitution.singleType variableArrowSyntax 0 (.var 1))).support
  = (⟨{1}, ∅⟩ : Names)

-- The same check across a universal and an existential binder, both named 1.
private def nestedCapture : F :=
  .forallNames ⟨{1}, ∅⟩
    (.and (.atom (.typeLe (.var 0) (.var 1))) typeCapture)
#guard (nestedCapture.subst (FiniteSubstitution.singleType variableArrowSyntax 0 (.var 1))).support
  = (⟨{1}, ∅⟩ : Names)

-- Handler quantification: free effect images remain free through ∀B.∃W.
private def effectCapture : F :=
  .forallNames ⟨∅, {1}⟩ (.existsNames ⟨∅, {2}⟩
    (.atom (.effectLe (Effect.var 0) (Effect.var 1 ∪ Effect.var 2))))
#guard (effectCapture.subst
  (FiniteSubstitution.singleEffect variableArrowSyntax 0 (Effect.var 1))).support
  = (⟨∅, {1}⟩ : Names)

-- Predicate parameters and latent arrow effects use the very same action.
private def predicateCapture : F := .existsNames ⟨{1}, {1}⟩
  (.atom (.predicate () (fun _ => .arrow (.var 0) (Effect.var 0) (.var 1))
    (fun _ => Effect.var 0 ∪ Effect.var 1)))
private def both : FiniteSubstitution variableArrowSyntax :=
  (FiniteSubstitution.singleEffect variableArrowSyntax 0 (Effect.var 1)).compose
    (FiniteSubstitution.singleType variableArrowSyntax 0 (.var 1))
#guard (predicateCapture.subst both).support = (⟨{1}, {1}⟩ : Names)

-- An arbitrary finite map cannot be passed as a Definition 6 substitution.
#check_failure (show Substitution variableArrowSyntax from FiniteSubstitution.identity variableArrowSyntax)

-- Empty finite environments do not require a closed type or literal signature.
private def emptyContext {T : TypeSyntax} (X : Theory T) : Context X :=
  { constants := [], locals := [], uniqueConstants := by simp }

-- Public interfaces accept abstract syntax, including nested polymorphic lets
-- and the additional EHMX rules; these are type checks, not correctness proofs.
section
variable {T : TypeSyntax} (X : Theory T) (S : X.Formula → Prop)
  (sig : Signature T) (N : X.Simplifier) (P : PrincipalNormalizer X S)
  (g : Context X)
#check (Statements.theorem7 X S sig : Prop)
#check (Statements.theorem7EHMX X S sig : Prop)
#check (Statements.theorem16 X S sig : Prop)
#check (Statements.theorem17 X S sig : Prop)
#check (Statements.corollary7 X S sig : Prop)
#check (Statements.implementationSoundness X S sig N P : Prop)
#check (Statements.implementationCompleteness X S sig N P : Prop)
#check (Statements.implementationCorollary7 X S sig N P : Prop)
#check (Derivation.forallElimSubst (X := X))
#check (Derivation.forallElimConstraint (X := X))
#check (Generates.lam (X := X))
#check (Generates.app (X := X))
#check (Generates.letVal (X := X))
#check (Generates.perform (X := X))
#check (Generates.handle (X := X))
#check Generalizes (X := X) S
#check inferTerm sig X N P g (.letE (.lam (.var 0)) (.letE (.var 0) (.var 0)))
#check inferTerm sig X N P g (.handle (.perform 0 (.const (.int 1))) 0 (.var 0) (.app (.var 0) (.var 1)))
end

end EHMX.HMX.DefinitionChecks
