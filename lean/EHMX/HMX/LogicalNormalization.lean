import EHMX.HMX.Theory

namespace EHMX.HMX.Logical
variable {T : TypeSyntax} {X : Theory T}

/-- Definitions 6 and 22: substitution is finite and idempotent. -/
structure ConstraintProblem (X : Theory T) where
  constraint : X.Formula
  substitution : Substitution T

namespace ConstraintProblem

def WellFormed (p : ConstraintProblem X) : Prop :=
  X.Equivalent (X.subst p.substitution p.constraint) p.constraint

def identityProblem (d : X.Formula) : ConstraintProblem X := ⟨d, Substitution.identity T⟩

/-- The agreed EHMX comparison: one factor for all entailments, and agreement
under the target residual. This deliberately differs from original Def.23. -/
def MoreGeneralOn (u : Names) (n m : ConstraintProblem X) : Prop :=
  ∃ φ : Substitution T,
    X.AgreesOn m.constraint (φ.compose n.substitution) m.substitution u ∧
    X.Entails m.constraint (X.subst φ n.constraint)

def MoreGeneral (n m : ConstraintProblem X) : Prop :=
  ∃ φ : Substitution T,
    (∀ u, X.AgreesOn m.constraint (φ.compose n.substitution) m.substitution u) ∧
    X.Entails m.constraint (X.subst φ n.constraint)

def IsNormal (S : X.Formula → Prop) (p n : ConstraintProblem X) : Prop :=
  p.WellFormed ∧ n.WellFormed ∧ S n.constraint ∧ MoreGeneral p n

def IsPrincipal (S : X.Formula → Prop) (p n : ConstraintProblem X) : Prop :=
  IsNormal S p n ∧ ∀ m, IsNormal S p m → MoreGeneral n m

end ConstraintProblem

/-- Definition 25 is conditional on existence of a normal form. -/
def PrincipalNormalForms (X : Theory T) (S : X.Formula → Prop) : Prop :=
  ∀ p, (∃ m : ConstraintProblem X, ConstraintProblem.IsNormal S p m) →
    ∃ n : ConstraintProblem X, ConstraintProblem.IsPrincipal S p n

end EHMX.HMX.Logical
