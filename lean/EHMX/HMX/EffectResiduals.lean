import EHMX.HMX.ContextApproximation

/-! Solved residuals may constrain effects, but are independent of type valuations.
These definitions do not assert existence of a normalizer for every constraint. -/
namespace EHMX.HMX.EffectResiduals
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

def EffectOnly (d : X.Formula) : Prop :=
  ∀ v w : Valuation T.Value, v.effects = w.effects → (X.holds d v ↔ X.holds d w)

def Solved (d : X.Formula) : Prop := X.Satisfiable d ∧ EffectOnly X d

theorem effect_graph_allowed {r : X.Formula} {s : Substitution T}
    (typesEmpty : s.domain.types = ∅)
    (admitted : X.Admissible (Solved X) r)
    (sat : X.Satisfiable (X.and r (X.substitutionConstraint s))) :
    X.Admissible (Solved X) (X.and r (X.substitutionConstraint s)) := by
  obtain ⟨q, ⟨_, onlyEffects⟩, forward, backward⟩ := admitted
  refine ⟨_, ⟨sat, ?_⟩, X.entails_refl _, X.entails_refl _⟩
  intro v w same
  have eqr : X.holds r v ↔ X.holds r w :=
    (Iff.intro (forward v) (backward v)).trans
      ((onlyEffects v w same).trans (Iff.intro (backward w) (forward w)))
  simp only [X.holds_and, X.holds_substitutionConstraint, typesEmpty,
    Finset.notMem_empty, false_implies, implies_true, true_and, eqr, same]

end EHMX.HMX.EffectResiduals

namespace EHMX.HMX.EffectResiduals
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

theorem effectOnly_of_admissible {d : X.Formula}
    (h : X.Admissible (Solved X) d) : EffectOnly X d := by
  obtain ⟨r, hr, f, b⟩ := h
  intro v w same
  exact ⟨fun hd => b w ((hr.2 v w same).mp (f v hd)),
    fun hd => b v ((hr.2 v w same).mpr (f w hd))⟩

theorem effectOnly_subst {d : X.Formula}
    (h : EffectOnly X d) (σ : Substitution T) : EffectOnly X (X.subst σ d) := by
  intro v w same
  rw [X.holds_subst, X.holds_subst]
  apply h
  funext i
  change (σ.effects i).eval v.effects = (σ.effects i).eval w.effects
  rw [same]

theorem scheme_admissible_subst {s : Scheme X} {c : X.Formula}
    (valid : s.Admissible (Solved X)) (real : s.Realizable c)
    (σ : Substitution T) (sat : X.Satisfiable (X.subst σ c)) :
    (s.subst σ).Admissible (Solved X) := by
  have ordinary := real.admissible_subst σ sat
  cases s with
  | mono => trivial
  | qualified a d t =>
    let avoid := Scheme.substAvoid σ a d t
    let η := σ.underBinder a avoid.shiftTypes avoid.shiftEffects
    change X.Admissible (Solved X) (X.subst η d)
    change X.Admissible X.Satisfiable (X.subst η d) at ordinary
    have eqOnly := effectOnly_subst (effectOnly_of_admissible valid) η
    exact ⟨X.subst η d,
      ⟨(X.admissible_satisfiable_iff _).mp ordinary, eqOnly⟩,
      X.entails_refl _, X.entails_refl _⟩

theorem context_admissible_subst {g : Context X} {c : X.Formula}
    (valid : g.Admissible (Solved X)) (real : g.Realizable c)
    (σ : Substitution T) (sat : X.Satisfiable (X.subst σ c)) :
    (g.subst σ).Admissible (Solved X) := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  exact scheme_admissible_subst (valid t ht) (real t ht) σ sat

theorem output_environment_self {g : Context X} {C : X.Formula}
    (valid : g.Admissible (Solved X)) (real : g.Realizable X.top)
    (σ : Substitution T) (sat : X.Satisfiable C) :
    (g.subst σ).Approximates (Solved X) C (g.subst σ) := by
  have entails : X.Entails C (X.subst σ X.top) := by
    intro v _
    exact (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial)
  have topsat : X.Satisfiable (X.subst σ X.top) := by
    obtain ⟨v, hv⟩ := sat
    exact ⟨v, entails v hv⟩
  exact Context.Approximates.refl
    (context_admissible_subst valid real σ topsat)
    ((real.subst σ).weaken entails)

end EHMX.HMX.EffectResiduals
