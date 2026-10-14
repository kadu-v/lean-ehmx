import EHMX.TypeClasses.Solver

namespace EHMX.TypeClasses
open HMX

/-- A checked, syntactic domain of the concrete decision procedure. -/
inductive DecisionFragment {K} (E : ClassEnv K) : Formula K E.count → Prop where
  | flat {c f} : collect c = some f → DecisionFragment E c
  | ex {a c} : DecisionFragment E c → DecisionFragment E (.ex a c)

def Decision.Success {K} {E : ClassEnv K} {c} : Decision E c → Prop
  | .sat _ => True
  | _ => False

theorem decideSimple_complete {K} (E : ClassEnv K) {c f}
    (collected : collect c = some f) (sat : (constraints E).Satisfiable c) :
    (decideSimple E c).Success := by
  have hs := (flatSat_iff E c f collected).mpr sat
  cases c <;> first
    | solve | simp [collect] at collected
    | (simp only [decideSimple]; split <;> simp_all [Decision.Success])

theorem decideWith_complete {K} (E : ClassEnv K) {c}
    (fragment : DecisionFragment E c) (sat : (constraints E).Satisfiable c) (fuel) :
    (decideWith E fuel c).Success := by
  induction fragment generalizing fuel with
  | @flat c f hc =>
    have hs := decideSimple_complete E hc sat
    cases c <;> try simp [collect] at hc
    all_goals
      unfold decideWith
      cases hd : decideSimple E _ <;> simp_all [Decision.Success]
  | @ex a c _ ih =>
    have hs := ih (((constraints E).satisfiable_exists_iff a c).mp sat) fuel
    rw [decideWith]
    cases hd : decideWith E fuel c <;> simp_all [Decision.Success]

theorem decideConstraint_complete {K} (E : ClassEnv K) {c}
    (fragment : DecisionFragment E (simplify E c))
    (sat : (constraints E).Satisfiable c) : (decideConstraint E c).Success := by
  have sn : (constraints E).Satisfiable (simplify E c) := by
    obtain ⟨v, hv⟩ := sat
    exact ⟨v, (simplify_correct E c v).mpr hv⟩
  have hs := decideWith_complete E fragment sn (((constraints E).support c).types.card + 1)
  unfold decideConstraint
  cases hd : decideWith E _ (simplify E c) <;> simp_all [Decision.Success]

/-- Completeness of the actual solver on its explicit normalized decision
fragment. This is not completeness for every handler-free generated formula. -/
theorem solver_complete_fragment {K} (E : ClassEnv K) (g w : Formula K E.count)
    (fragment : DecisionFragment E (simplify E (.and g (normalize E w))))
    (sat : (constraints E).Satisfiable (.and g w)) :
    ∃ n, (solver E).run g w = .solved n := by
  have sn : (constraints E).Satisfiable (.and g (normalize E w)) := by
    obtain ⟨v, hv⟩ := sat
    exact ⟨v, (holds_and E _ _ _).mpr ⟨hv.1, (normalize_correct E w v).mpr hv.2⟩⟩
  have hs := decideConstraint_complete E fragment sn
  change ∃ n, (solve E g w).val = .solved n
  unfold solve
  dsimp only
  split
  · rename_i result h
    have cert := result.property
    cases hr : result.val with
    | solved n => exact ⟨n, rfl⟩
    | inconsistent =>
      rw [hr] at cert
      change ¬ (constraints E).Satisfiable (.and g w) at cert
      exact False.elim (cert sat)
    | unresolved r =>
      -- Only solved/inconsistent constructors can be returned by solveBinding.
      split at h
      · contradiction
      · unfold solveBinding at h
        dsimp only at h
        split at h <;> cases h <;> cases hr
  · cases hd : decideConstraint E (.and g (normalize E w)) <;>
      simp_all [Decision.Success]

end EHMX.TypeClasses
