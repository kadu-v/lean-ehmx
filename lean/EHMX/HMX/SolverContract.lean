import EHMX.HMX.PartialSolving

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

inductive SolveResult (X : Constraints T O) where
  | solved : X.NormalForm → SolveResult X
  | unresolved : X.Formula → SolveResult X
  | inconsistent : SolveResult X

/-- Constraint-only laws. No field refers to expressions or typing judgments.
Qualified residuals may retain quantifiers; solved does not mean residual = top. -/
structure PartialSolver (X : Constraints T O) where
  run : X.Formula → X.Formula → SolveResult X
  success : ∀ g w n, run g w = .solved n →
    n.GuessFreeSolution g w ∧ X.Satisfiable (X.and g n.residual)
  unresolved : ∀ g w r, run g w = .unresolved r →
    X.Equivalent (X.and g r) (X.and g w)
  inconsistent : ∀ g w, run g w = .inconsistent → ¬ X.Satisfiable (X.and g w)

/-- Completeness for the full qualified constraint language, including clauses.
It is an additional constraint-solving law, not a typing-completeness premise. -/
def PartialSolver.Complete {X : Constraints T O} (S : PartialSolver X) : Prop :=
  ∀ g w, X.Satisfiable (X.and g w) → ∃ n, S.run g w = .solved n

/-- HM(X)'s constraint-form inference requires a satisfiability test, not
elimination of equalities or quantifiers. This interface covers every formula
of X, including handler clauses. An executable implementation must supply a
computable `decide`; the semantic model below is not such an implementation. -/
structure SatDecider (X : Constraints T O) where
  decide : X.Formula → Bool
  correct : ∀ c, decide c = true ↔ X.Satisfiable c

namespace SatDecider
variable {X : Constraints T O} (D : SatDecider X)

/-- Retain the complete wanted constraint and select no type witnesses.
The executable branch depends only on the supplied Boolean test. -/
def solver : PartialSolver X where
  run := fun g w => if D.decide (X.and g w) then
    .solved ⟨w, Substitution.identity T⟩ else .inconsistent
  success := by
    intro g w n h
    split at h
    · cases h
      exact ⟨Constraints.NormalForm.guessFree_identity ⟨X.entails_refl _, X.entails_refl _⟩,
        (D.correct _).mp ‹D.decide (X.and g w) = true›⟩
    · contradiction
  unresolved := by intro g w r h; split at h <;> contradiction
  inconsistent := by
    intro g w h
    split at h
    · contradiction
    · intro sat
      exact ‹¬ D.decide (X.and g w) = true› ((D.correct _).mpr sat)

theorem solver_solved_iff (g w : X.Formula) (n : X.NormalForm) :
    D.solver.run g w = .solved n ↔
      X.Satisfiable (X.and g w) ∧ n = ⟨w, Substitution.identity T⟩ := by
  by_cases h : D.decide (X.and g w) = true
  · simp only [solver, h, ↓reduceIte, SolveResult.solved.injEq,
      (D.correct _).mp h, true_and]
    exact eq_comm
  · have hn : ¬ X.Satisfiable (X.and g w) := fun hs => h ((D.correct _).mpr hs)
    simp [solver, h, hn]

theorem solver_inconsistent_iff (g w : X.Formula) :
    D.solver.run g w = .inconsistent ↔ ¬ X.Satisfiable (X.and g w) := by
  simp [solver, ← D.correct]

theorem solver_ne_unresolved (g w r : X.Formula) :
    D.solver.run g w ≠ .unresolved r := by
  by_cases h : D.decide (X.and g w) = true <;> simp [solver, h]

theorem solver_complete : D.solver.Complete := by
  intro g w sat
  exact ⟨⟨w, Substitution.identity T⟩, (D.solver_solved_iff g w _).mpr ⟨sat, rfl⟩⟩

end SatDecider

def PartialSolver.defer (X : Constraints T O) : PartialSolver X where
  run := fun _ w => .unresolved w
  success := by intros; contradiction
  unresolved := by intro g w r h; cases h; exact ⟨X.entails_refl _, X.entails_refl _⟩
  inconsistent := by intros; contradiction

/-- Model of the contract, not an executable satisfiability procedure. -/
noncomputable def PartialSolver.semantic (X : Constraints T O) : PartialSolver X := by
  classical
  exact {
    run := fun g w => if X.Satisfiable (X.and g w)
      then .solved ⟨w, Substitution.identity T⟩ else .inconsistent
    success := by
      intro g w n h
      split at h
      · cases h
        exact ⟨Constraints.NormalForm.guessFree_identity ⟨X.entails_refl _, X.entails_refl _⟩,
          ‹X.Satisfiable (X.and g w)›⟩
      · contradiction
    unresolved := by intro g w r h; split at h <;> contradiction
    inconsistent := by intro g w h; split at h <;> first | contradiction | assumption }

theorem PartialSolver.semantic_complete (X : Constraints T O) :
    (PartialSolver.semantic X).Complete := by
  intro g w sat
  exact ⟨⟨w, Substitution.identity T⟩, by simp [PartialSolver.semantic, sat]⟩

/-- Success laws alone do not imply completeness, even for the tautology. -/
theorem PartialSolver.defer_not_complete (X : Constraints T O) :
    ¬ (PartialSolver.defer X).Complete := by
  intro complete
  obtain ⟨a⟩ := T.value_nonempty
  let v : Valuation T.Value := ⟨fun _ => a, fun _ => ∅⟩
  have sat : X.Satisfiable (X.and X.top X.top) :=
    ⟨v, (X.holds_and _ _ v).mpr ⟨(X.holds_top v).mpr trivial, (X.holds_top v).mpr trivial⟩⟩
  obtain ⟨n, hn⟩ := complete X.top X.top sat
  cases hn

end EHMX.HMX
