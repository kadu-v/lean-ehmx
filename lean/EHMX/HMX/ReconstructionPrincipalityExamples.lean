import EHMX.HMX.SatisfiableReconstruction
import EHMX.HMX.AlgorithmExamples
import EHMX.HMX.ReconstructionExamples

namespace EHMX.HMX.ReconstructionPrincipalityExamples
private abbrev T := equalityTypes
private abbrev O := TypeOrder.equality T
private abbrev X := Constraints.semantic T O
private abbrev N := Constraints.Simplifier.identity X
private def sig : Signature T := fun _ => some ⟨⟨{0}, ∅⟩, .var 0, .var 0⟩
private noncomputable def P : X.ScopedPrincipalNormalizer :=
  Constraints.ScopedPrincipalNormalizer.satisfiable X

private theorem sig_closed : sig.Closed := by
  intro op d hd
  cases hd
  simp [Operation.Closed, Ty.fvTypes, Ty.fvEffects]

private theorem top_sat : X.Satisfiable X.top :=
  ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, trivial⟩

private theorem corollary {g : Context X} {e : Expr} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X P.solved X.top g e s eff)
    (closed : g.support = Names.empty) (real : g.Realizable X.top) :
    ∃ n, inferTerm sig X N P g e = some (.reconstructed n) ∧
    let result := reconstructedScheme g n
    X.Equivalent result.outer X.top ∧
    PrincipalComputationScheme sig X P.solved g e result ∧
    (∀ c t eff, Typing sig X P.solved c g e (.mono t) eff →
      result.FiniteInstance c t eff) ∧
    (∀ c s eff, Typing sig X P.solved c g e s eff →
      Instance X c result.valueScheme s) ∧
    (Value e → PrincipalPair (fun c g e s => Typing sig X P.solved c g e s ∅)
      g e X.top result.valueScheme) :=
  inferTerm_satisfiable_closed N typed closed real

/-- Both empty and nonempty closed qualified environments use the actual
normalizer. This includes the generalization regression from Theorem 17. -/
theorem identity_principal (g : Context X) (closed : g.support = Names.empty)
    (adm : g.Admissible P.solved) (real : g.Realizable X.top) :
    ∃ n, inferTerm sig X N P g (.lam (.var 0)) = some (.reconstructed n) ∧
      PrincipalPair (fun c g e s => Typing sig X P.solved c g e s ∅)
        g (.lam (.var 0)) X.top (reconstructedScheme g n).valueScheme := by
  have typed : Typing sig X P.solved X.top g (.lam (.var 0))
      (.mono (.arr (.var 0) ∅ (.var 0))) ∅ := by
    apply Typing.of_ground N adm top_sat
    intro v _
    exact .lam (.var rfl rfl)
  obtain ⟨n, run, _, _, _, _, value⟩ := corollary typed closed real
  exact ⟨n, run, value (.lam (.var 0))⟩

theorem empty_identity_principal :
    ∃ n, inferTerm sig X N P [] (.lam (.var 0)) = some (.reconstructed n) ∧
      PrincipalPair (fun c g e s => Typing sig X P.solved c g e s ∅)
        [] (.lam (.var 0)) X.top (reconstructedScheme [] n).valueScheme :=
  identity_principal [] rfl (by intro s hs; cases hs) (by intro s hs; cases hs)

private def closedContext : Context X := [.qualified Names.empty X.top (.base .int)]
private theorem closed_adm : closedContext.Admissible P.solved := by
  intro s hs
  have hs : s = .qualified Names.empty X.top (.base .int) := List.mem_singleton.mp hs
  subst s
  exact (X.admissible_satisfiable_iff _).mpr top_sat
private theorem closed_real : closedContext.Realizable X.top := by
  intro s hs
  have hs : s = .qualified Names.empty X.top (.base .int) := List.mem_singleton.mp hs
  subst s
  refine ⟨.base .int, .forallLeft (Substitution.identity T)
    (by simp [Substitution.identity, Names.empty])
    (by simp [Substitution.identity, Names.empty]) ?_ (.sub (fun _ _ => rfl))⟩
  intro v _
  exact (X.holds_subst _ _ _).mpr trivial

theorem closed_qualified_identity_principal :
    ∃ n, inferTerm sig X N P closedContext (.lam (.var 0)) = some (.reconstructed n) ∧
      PrincipalPair (fun c g e s => Typing sig X P.solved c g e s ∅)
        closedContext (.lam (.var 0)) X.top (reconstructedScheme closedContext n).valueScheme :=
  identity_principal closedContext (by decide) closed_adm closed_real

/-- A qualified target is projected over nonempty sets of both sorts before
being compared with the same principal output. -/
theorem qualified_projection_compared :
    ∃ n, inferTerm sig X N P closedContext (.var 0) = some (.reconstructed n) ∧
      Instance X (X.existsNames ⟨{50}, {50}⟩ X.top)
        (reconstructedScheme closedContext n).valueScheme
        (.qualified Names.empty X.top (.base .int)) := by
  have typed : Typing sig X P.solved X.top closedContext (.var 0)
      (.qualified Names.empty X.top (.base .int)) ∅ :=
    ⟨.var rfl, Derivation.valid_of_satisfiable _ top_sat closed_adm⟩
  have projected := typed.existsIntro
    ((X.admissible_satisfiable_iff _).mpr ((X.satisfiable_exists_iff _ _).mpr top_sat))
    (closedContext.avoids_of_support_disjoint ⟨{50}, {50}⟩ (by constructor <;> decide))
    (by
      constructor
      · intro i hi hf
        rcases hf.2 with hf | hf
        · exact (X.top_avoids ⟨{50}, {50}⟩).1 i hi hf
        · simp [Ty.fvTypes] at hf
      · intro i hi hf
        rcases hf.2 with hf | hf
        · exact (X.top_avoids ⟨{50}, {50}⟩).2 i hi hf
        · simp [Ty.fvEffects] at hf)
    (by simp)
  obtain ⟨n, run, _, _, _, compare, _⟩ := corollary typed (by decide) closed_real
  exact ⟨n, run, compare _ _ _ projected⟩

private def collisionScheme : Scheme X := .qualified ⟨{1}, {1}⟩ X.top
  (.arr (.var 1) (.var 1) (.var 1))

/-- Both substitution ranges hit quantified names, but the original closed
environment remains a valid approximation after capture avoidance. -/
theorem closed_environment_capture :
    (Context.subst (Substitution.outputs (T := T) 0 0 (.var 1) (.var 1)) [collisionScheme]).Approximates
      P.solved X.top [collisionScheme] := by
  apply Context.subst_approximates_closed (by decide)
  · intro s hs
    have hs : s = collisionScheme := List.mem_singleton.mp hs
    subst s
    exact (X.admissible_satisfiable_iff _).mpr top_sat
  · intro s hs
    have hs : s = collisionScheme := List.mem_singleton.mp hs
    subst s
    refine ⟨_, .forallLeft (Substitution.identity T)
      (by simp [Substitution.identity, Names.empty])
      (by simp [Substitution.identity, Names.empty]) ?_ (.sub (fun _ _ => rfl))⟩
    intro v _
    exact (X.holds_subst _ _ _).mpr trivial

private theorem from_ground {e : Expr} {t : Ty} {eff : Effect}
    (ground : ∀ v : Valuation GroundTy,
      GroundTyping sig O [] e (T.eval v t) (eff.eval v.effects)) :
    ∃ n, inferTerm sig X N P [] e = some (.reconstructed n) ∧
      PrincipalComputationScheme sig X P.solved [] e (reconstructedScheme [] n) ∧
      (reconstructedScheme [] n).FiniteInstance X.top t eff := by
  have typed : Typing sig X P.solved X.top [] e (.mono t) eff :=
    Typing.of_ground N (by intro s hs; cases hs) top_sat (fun v _ => ground v)
  obtain ⟨n, run, _, comp, finite, _, _⟩ := corollary typed rfl (by intro s hs; cases hs)
  exact ⟨n, run, comp, finite _ _ _ typed⟩

theorem polymorphic_let_principal :
    ∃ n, inferTerm sig X N P [] AlgorithmExamples.polymorphicLet = some (.reconstructed n) ∧
      PrincipalComputationScheme sig X P.solved [] AlgorithmExamples.polymorphicLet
        (reconstructedScheme [] n) ∧
      (reconstructedScheme [] n).FiniteInstance X.top (.base .bool) ∅ :=
  from_ground (fun _ => AlgorithmExamples.polymorphicLet_ground)

theorem nested_handler_principal :
    ∃ n, inferTerm sig X N P []
      (.handle AlgorithmExamples.resumeIdentity 0 (.var 0) (.app (.var 0) (.var 1))) =
        some (.reconstructed n) ∧
      PrincipalComputationScheme sig X P.solved []
        (.handle AlgorithmExamples.resumeIdentity 0 (.var 0) (.app (.var 0) (.var 1)))
        (reconstructedScheme [] n) ∧
      (reconstructedScheme [] n).FiniteInstance X.top (.base .int) ∅ :=
  from_ground (fun _ => AlgorithmExamples.nestedHandler_ground)

/-- A computation with a nonempty immediate effect is still covered; no
ordinary polymorphic typing of this non-value is asserted. -/
theorem perform_principal :
    ∃ n, inferTerm sig X N P [] (.perform 0 (.int 0)) = some (.reconstructed n) ∧
      PrincipalComputationScheme sig X P.solved [] (.perform 0 (.int 0)) (reconstructedScheme [] n) ∧
      (reconstructedScheme [] n).FiniteInstance X.top (.base .int) (Effect.singleton 0) := by
  apply from_ground
  intro v
  let w : Valuation GroundTy := ⟨fun _ => .atom 0, fun _ => ∅⟩
  simpa [w, Ty.eval, Effect.eval, Effect.singleton] using
    (GroundTyping.perform (sig := sig) (O := O) (g := []) (op := 0)
      (raw := ⟨⟨{0}, ∅⟩, .var 0, .var 0⟩) w rfl
      (by simp [Operation.Closed, Ty.fvTypes, Ty.fvEffects]) (.int 0))

/-- The comparison part of Corollary 7 does not require a uniformly realizable
target. The chosen model and normalizer exist, rather than being assumptions. -/
theorem unrealizable_target_compared :
    ∃ (Y : Constraints T O) (Q : Y.ScopedPrincipalNormalizer) (c : Y.Formula) (s : Scheme Y),
      ¬ s.Realizable c ∧ ∃ n,
      inferTerm (fun _ => none) Y (Constraints.Simplifier.identity Y) Q [] (.lam (.var 0)) =
        some (.reconstructed n) ∧
      Instance Y c (reconstructedScheme [] n).valueScheme s := by
  obtain ⟨Y, c, s, typed, notReal, _⟩ := RealizabilityExample.valid_let_without_realizable_scheme
  obtain ⟨n, run, _, _, _, cover, _⟩ := inferTerm_satisfiable_closed
    (Constraints.Simplifier.identity Y) typed rfl (by intro t ht; cases ht)
  exact ⟨Y, Constraints.ScopedPrincipalNormalizer.satisfiable Y, c, s, notReal, n, run,
    cover _ _ _ typed⟩

private theorem resume {g : GroundContext T} {e : Expr} {eff : Finset Op}
    (body : GroundTyping sig O g e (.atom 0) eff) (he : eff ⊆ {0}) :
    GroundTyping sig O g (.handle e 0 (.var 0) (.app (.var 0) (.var 1))) (.atom 0) ∅ := by
  let op : Operation T := ⟨⟨{0}, ∅⟩, .var 0, .var 0⟩
  apply GroundTyping.handle (raw := op) (decl := op)
    (input := .atom 0) (ein := eff) (er := ∅) (rest := ∅) (fun _ => ∅)
  · rfl
  · simp [op, Operation.Closed, Ty.fvTypes, Ty.fvEffects]
  · exact ⟨id, id, Function.injective_id.injOn, Function.injective_id.injOn, rfl⟩
  · exact body
  · exact .var rfl rfl
  · intro w
    simpa [op, Ty.eval] using (GroundTyping.app
      (show GroundTyping sig O (upper O (.arr (w.types 0) ∅ (.atom 0)) :: upper O (w.types 0) :: g)
        (.var 0) (.arr (w.types 0) ∅ (.atom 0)) ∅ from .var rfl rfl)
      (show GroundTyping sig O (upper O (.arr (w.types 0) ∅ (.atom 0)) :: upper O (w.types 0) :: g)
        (.var 1) (w.types 0) ∅ from .var rfl rfl))
  · intro w; simp
  · exact Finset.empty_subset _
  · simpa only [Finset.union_empty] using he
  all_goals simp

/-- Both polymorphic value lets, perform, and nested handlers occur in one
program, with a nonempty closed environment and an actual Sat normalizer. -/
theorem mixed_principal :
    ∃ n, inferTerm sig X N P [.mono (.base .int)] ReconstructionExamples.mixedReconstruction =
      some (.reconstructed n) ∧
      PrincipalComputationScheme sig X P.solved [.mono (.base .int)]
        ReconstructionExamples.mixedReconstruction (reconstructedScheme [.mono (.base .int)] n) := by
  let g : Context X := [.mono (.base .int)]
  have adm : g.Admissible P.solved := by
    intro s hs
    have hs : s = .mono (.base .int) := List.mem_singleton.mp hs
    subst s
    trivial
  have real : g.Realizable X.top := by
    intro s hs
    have hs : s = .mono (.base .int) := List.mem_singleton.mp hs
    subst s
    exact ⟨.base .int, .sub (fun _ _ => rfl)⟩
  have typed : Typing sig X P.solved X.top g ReconstructionExamples.mixedReconstruction
      (.mono (.base .int)) ∅ := by
    apply Typing.of_ground N adm top_sat
    intro v _
    let instances : Set GroundTy := {t | ∃ a, t = .arr a ∅ a}
    have ne : instances.Nonempty := ⟨_, .atom 0, rfl⟩
    have identity (ctx : GroundContext T) : ∀ a ∈ instances,
        GroundTyping sig O ctx (.lam (.var 0)) a ∅ := by
      rintro a ⟨b, rfl⟩
      exact .lam (.var rfl rfl)
    apply GroundTyping.letVal (.lam (.var 0)) ne (identity _)
    apply GroundTyping.letVal (.lam (.var 0)) ne (identity _)
    apply resume (eff := ∅) _ (Finset.empty_subset _)
    apply resume (eff := {0}) _ (Finset.Subset.refl _)
    let w : Valuation GroundTy := ⟨fun _ => .atom 0, fun _ => ∅⟩
    have arg : GroundTyping sig O (instances :: instances :: g.ground v)
        (.app (.var 0) (.var 2)) (.atom 0) ∅ := by
      simpa using (GroundTyping.app
        (show GroundTyping sig O (instances :: instances :: g.ground v) (.var 0)
          (.arr (.atom 0) ∅ (.atom 0)) ∅ from .var rfl ⟨_, rfl⟩)
        (show GroundTyping sig O (instances :: instances :: g.ground v) (.var 2) (.atom 0) ∅
          from .var rfl rfl))
    simpa [w, Ty.eval] using
      (GroundTyping.perform (sig := sig) (O := O) (op := 0)
        (raw := ⟨⟨{0}, ∅⟩, .var 0, .var 0⟩) w rfl
        (by simp [Operation.Closed, Ty.fvTypes, Ty.fvEffects]) arg)
  obtain ⟨n, run, _, comp, _⟩ := corollary typed (by decide) real
  exact ⟨n, run, comp⟩

end EHMX.HMX.ReconstructionPrincipalityExamples
