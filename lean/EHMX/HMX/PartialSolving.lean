import EHMX.HMX.ComputationSchemes

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

namespace Constraints
variable {X : Constraints T O}

/-- OutsideIn-style S1/S2, with global axioms interpreted by X and local givens
explicit. This is a checkable per-result obligation, not solver completeness.
The existing solved-substitution discipline is stronger than idempotence. -/
structure NormalForm.SoundSolution (given wanted : X.Formula) (n : X.NormalForm) : Prop where
  solved : n.substitution.Solved
  fixed_given : X.Avoids given n.substitution.domain
  fixed_residual : X.Avoids n.residual n.substitution.domain
  sound : X.Entails (X.and given n.residual) (X.subst n.substitution wanted)

/-- P1 forbids choosing a visible type merely because it has an instance.
Existential witnesses internal to wanted need not be exported in substitution. -/
structure NormalForm.GuessFreeSolution (given wanted : X.Formula) (n : X.NormalForm) : Prop
    extends n.SoundSolution given wanted where
  no_guess : X.Entails (X.and given wanted) n.formula

theorem NormalForm.GuessFreeSolution.formula_equivalent
    {given wanted : X.Formula} {n : X.NormalForm}
    (h : n.GuessFreeSolution given wanted) :
    X.Equivalent (X.and given n.formula) (X.and given wanted) := by
  constructor
  · intro v hv
    obtain ⟨hg, hf⟩ := (X.holds_and _ _ v).mp hv
    obtain ⟨hr, he⟩ := (X.holds_and _ _ v).mp hf
    have hw := (X.holds_subst _ _ v).mp (h.sound v ((X.holds_and _ _ v).mpr ⟨hg, hr⟩))
    rw [X.substitutionConstraint_fixed _ v he] at hw
    exact (X.holds_and _ _ v).mpr ⟨hg, hw⟩
  · intro v hv
    exact (X.holds_and _ _ v).mpr ⟨((X.holds_and _ _ v).mp hv).1, h.no_guess v hv⟩

theorem NormalForm.GuessFreeSolution.formula_equivalent_top
    {wanted : X.Formula} {n : X.NormalForm}
    (h : n.GuessFreeSolution X.top wanted) : X.Equivalent n.formula wanted := by
  constructor
  · intro v hv
    exact ((X.holds_and _ _ v).mp (h.formula_equivalent.1 v
      ((X.holds_and _ _ v).mpr ⟨(X.holds_top v).mpr trivial, hv⟩))).2
  · intro v hv
    exact h.no_guess v ((X.holds_and _ _ v).mpr ⟨(X.holds_top v).mpr trivial, hv⟩)

/-- Exact constraint simplification is guess-free with no exported assignment.
In particular, proving an existential formula true is not type defaulting. -/
theorem NormalForm.guessFree_identity {given wanted residual : X.Formula}
    (eq : X.Equivalent residual wanted) :
    (NormalForm.mk residual (Substitution.identity T)).GuessFreeSolution given wanted := by
  constructor
  · refine ⟨Substitution.identity_solved T, ?_, ?_, ?_⟩
    · constructor <;> intro i hi <;> simp [Substitution.identity, Names.empty] at hi
    · constructor <;> intro i hi <;> simp [Substitution.identity, Names.empty] at hi
    · intro v hv
      apply (X.holds_subst _ _ v).mpr
      rw [Substitution.identity_pullback]
      exact eq.1 v ((X.holds_and _ _ v).mp hv).2
  · intro v hv
    apply (X.holds_and _ _ v).mpr
    refine ⟨eq.2 v ((X.holds_and _ _ v).mp hv).2, ?_⟩
    apply (X.holds_substitutionConstraint _ _).mpr
    constructor <;> intro i hi <;> simp [Substitution.identity, Names.empty] at hi

/-- Eliminate a hidden, independently satisfiable obligation while retaining
every constraint on visible names. A witness is used only inside its binder. -/
theorem exists_independent_valid {a : Names} {independent hidden : X.Formula}
    (fresh : X.Avoids independent a)
    (valid : ∀ v, X.holds (X.existsNames a hidden) v) :
    X.Equivalent (X.existsNames a (X.and independent hidden)) independent := by
  constructor
  · intro v hv
    obtain ⟨w, outside, hw⟩ := (X.holds_exists _ _ v).mp hv
    exact (X.holds_agreeOutside fresh outside).mp ((X.holds_and _ _ w).mp hw).1
  · intro v hv
    obtain ⟨w, outside, hw⟩ := (X.holds_exists _ _ v).mp (valid v)
    exact (X.holds_exists _ _ v).mpr ⟨w, outside,
      (X.holds_and _ _ w).mpr ⟨(X.holds_agreeOutside fresh outside).mpr hv, hw⟩⟩

end Constraints

/-- Reifying a guess-free result as residual plus equations preserves the
principal qualified scheme. This does not certify an arbitrary solver run. -/
theorem PrincipalComputationScheme.guessFree {sig : Signature T} {X : Constraints T O}
    {g : Context X} {e : Expr} {s : ComputationScheme X} {n : X.NormalForm}
    (h : PrincipalComputationScheme sig X X.Satisfiable g e s)
    (solution : n.GuessFreeSolution X.top s.condition) :
    PrincipalComputationScheme sig X X.Satisfiable g e {s with condition := n.formula} :=
  h.condition_equivalent solution.formula_equivalent_top

theorem ComputationScheme.FiniteInstance.guessFree {X : Constraints T O}
    {s : ComputationScheme X} {n : X.NormalForm} {c : X.Formula} {t : T.Term} {eff : Effect}
    (h : s.FiniteInstance c t eff) (solution : n.GuessFreeSolution X.top s.condition) :
    ({s with condition := n.formula} : ComputationScheme X).FiniteInstance c t eff :=
  h.condition_equivalent solution.formula_equivalent_top

end EHMX.HMX
