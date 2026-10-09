import SystemFXi.EHMX.Solver

namespace SystemFXi.EHMX

inductive ClassPred where
  | eq : Ty → ClassPred
  | show : Ty → ClassPred
  deriving DecidableEq

structure ClassEnv where
  eq : GroundTy → Prop
  showClass : GroundTy → Prop

def ClassPred.rename (ρ η : Nat → Nat) : ClassPred → ClassPred
  | .eq τ => .eq (τ.rename ρ η)
  | .show τ => .show (τ.rename ρ η)

def ClassPred.subst (θ : Substitution) : ClassPred → ClassPred
  | .eq τ => .eq (τ.subst θ)
  | .show τ => .show (τ.subst θ)

def ClassPred.fvTypes : ClassPred → Finset Nat
  | .eq τ | .show τ => τ.fvTypes

def ClassPred.fvEffects : ClassPred → Finset Nat
  | .eq τ | .show τ => τ.fvEffects

def classDomain (I : ClassEnv) : Domain where
  Pred := ClassPred
  rename := ClassPred.rename
  holds := fun ρ p => match p with
    | .eq τ => I.eq (τ.eval ρ)
    | .show τ => I.showClass (τ.eval ρ)
  fvTypes := ClassPred.fvTypes
  fvEffects := ClassPred.fvEffects

theorem classDomain_lawfulRename (I : ClassEnv) :
    LawfulRename (classDomain I) := by
  constructor
  intro ρ η p v
  cases p <;> simp [classDomain, ClassPred.rename, Ty.eval_rename]

theorem classDomain_lawfulSupport (I : ClassEnv) :
    LawfulSupport (classDomain I) := by
  constructor
  intro p v w ht he
  cases p with
  | eq τ =>
      simp only [classDomain, ClassPred.fvTypes, ClassPred.fvEffects] at ht he
      simp only [classDomain]
      rw [Ty.eval_support τ v w ht he]
  | «show» τ =>
      simp only [classDomain, ClassPred.fvTypes, ClassPred.fvEffects] at ht he
      simp only [classDomain]
      rw [Ty.eval_support τ v w ht he]

theorem classDomain_lawfulFVRename (I : ClassEnv) :
    LawfulFVRename (classDomain I) := by
  constructor
  · intro ρ η p
    cases p <;>
      simp [classDomain, ClassPred.rename, ClassPred.fvTypes,
        Ty.fvTypes_rename]
  · intro ρ η p
    cases p <;>
      simp [classDomain, ClassPred.rename, ClassPred.fvEffects,
        Ty.fvEffects_rename]

def classDomain_lawfulSubst (I : ClassEnv) :
    LawfulSubst (classDomain I) where
  subst := ClassPred.subst
  holds_subst := by
    intro θ p v
    cases p <;>
      simp [classDomain, ClassPred.subst, Ty.eval_subst]

instance (I : ClassEnv) : DecidableEq (classDomain I).Pred :=
  inferInstanceAs (DecidableEq ClassPred)

/-- A qualified identity function, standing for a value that requires `Eq α`. -/
def eqIdentityScheme (I : ClassEnv) (α : Nat) : Scheme (classDomain I) :=
  { typeVars := {α}
    effectVars := ∅
    predicates := .predicate (.eq (.var α))
    result := .arr (.var α) ∅ (.var α) }

/-- The generic solver removes an exactly assumed class predicate. -/
theorem assumed_eq_resolves (I : ClassEnv) (α : Nat) :
    resolveX (X := classDomain I) [ClassPred.eq (.var α)]
      (.predicate (.eq (.var α))) = Constraint.top := by
  have hp : ClassPred.eq (.var α) ∈ [ClassPred.eq (.var α)] := by simp
  simp [resolveX]
  exact hp

/-- With no class assumption, the same predicate remains in the result. -/
theorem unassumed_eq_remains (I : ClassEnv) (α : Nat) :
    resolveX (X := classDomain I) []
      (.predicate (ClassPred.eq (.var α))) =
        Constraint.predicate (ClassPred.eq (.var α)) := by
  simp [resolveX]
  intro h
  cases h

end SystemFXi.EHMX
