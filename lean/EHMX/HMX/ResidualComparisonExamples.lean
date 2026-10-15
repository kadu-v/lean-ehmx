import EHMX.HMX.VariableEqualityReflection

namespace EHMX.HMX.ResidualComparisonExamples
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

private def assignAlias : Substitution T where
  domain := ⟨{0}, ∅⟩
  types := fun i => if i = 0 then T.var 1 else T.var i
  effects := Effect.var
  types_outside := by intro i hi; simp_all
  effects_outside := by intros; rfl

/-- A variable equation has a principal normal form under residual-relative
comparison, even when competing substitutions agree only under their residual.
No restriction to effect-only residuals is needed for this example. -/
theorem variable_equation_principal {S : X.Formula → Prop} (top : S X.top) (u : Names) :
    (⟨X.top, assignAlias⟩ : X.NormalForm).IsPrincipalOn u S (X.eq (T.var 0) (T.var 1)) := by
  have solved : (assignAlias (T := T)).Solved := by
    constructor
    · intro i hi
      have h : i = 0 := by simpa [assignAlias] using hi
      subst i
      simp [assignAlias, T.support_var, Names.Disjoint]
    · intro i hi; simp [assignAlias] at hi
  refine ⟨⟨top, solved, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro v _; exact (X.holds_top _).mpr trivial
  · intro v _; exact (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial)
  · intro v hv
    have eq := ((X.holds_substitutionConstraint _ _).mp ((X.holds_and _ _ _).mp hv).2).1 0
      (by simp [assignAlias])
    apply (X.holds_eq _ _ _).mpr
    simpa [assignAlias, T.eval_var] using eq
  · intro m hm
    refine ⟨m.substitution, ?_⟩
    intro v hv
    have eq := (X.holds_eq _ _ _).mp ((X.holds_subst _ _ _).mp
      (Constraints.NormalForm.reconstruct_entails X hm v hv))
    refine ⟨⟨?_, ?_⟩, (X.holds_top _).mpr trivial⟩
    · intro i _
      by_cases hi : i = 0
      · subst i
        simpa [assignAlias, Substitution.pullback, T.eval_var] using eq.symm
      · simp [assignAlias, Substitution.pullback, hi, T.eval_var]
    · intro i _
      simp [assignAlias, Substitution.pullback, Effect.eval, Effect.var]

end EHMX.HMX.ResidualComparisonExamples
