import EHMX.HMX.SatisfiableReconstruction
import EHMX.HMX.OpenExamples

namespace EHMX.HMX.ReconstructionCompletenessExamples
private abbrev T := equalityTypes
private abbrev O := TypeOrder.equality T
private abbrev X := Constraints.semantic T O
private abbrev N := Constraints.Simplifier.identity X
private def sig : Signature T := fun _ => some ⟨⟨{0}, ∅⟩, .var 0, .var 0⟩
private noncomputable def P : X.ScopedPrincipalNormalizer :=
  Constraints.ScopedPrincipalNormalizer.satisfiable X

private def closedContext : Context X := [.qualified Names.empty X.top (.base .int)]
private def normal : X.NormalForm :=
  ⟨X.top, Substitution.outputs 1 1 (.arr (.var 4) ∅ (.var 4)) ∅⟩
private def generated : X.Formula :=
  (generateProjected sig X N closedContext (.lam (.var 0)) (.var 1) (.var 1)).getD X.top
private def observed : Names :=
  reconstructionScope X closedContext (.var 1) (.var 1) generated
private def tautologies (c : X.Formula) : Prop := ∀ v, X.holds c v

private theorem generated_run :
    generateProjected sig X N closedContext (.lam (.var 0)) (.var 1) (.var 1) = some generated := rfl

private theorem signature_closed : sig.Closed := by
  intro op d hd
  cases hd
  simp [Operation.Closed, Ty.fvTypes, Ty.fvEffects]

private theorem closed_real (v : Valuation GroundTy) : closedContext.GroundRealizable v := by
  intro s hs
  have hs : s = .qualified Names.empty X.top (.base .int) := List.mem_singleton.mp hs
  subst s
  exact ⟨.atom 0, v, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, trivial, rfl⟩

/-- A real generated lambda constraint has the intended principal local normal
form. This does not assume a global tautology-only normalizer. -/
theorem generated_identity_principal : normal.IsPrincipalOn observed tautologies generated := by
  have normalValid : normal.IsNormal tautologies generated := by
    refine ⟨fun _ => trivial, Substitution.outputs_solved 1 1 _ _
      (by simp [Names.Disjoint, Ty.fvTypes, Ty.fvEffects]) (by simp), ⟨?_, ?_⟩, ?_⟩
    · intro _ _; trivial
    · intro _ _; trivial
    · intro v hv
      have graph := (X.holds_substitutionConstraint normal.substitution v).mp
        ((X.holds_and _ _ _).mp hv).2
      have ht := graph.1 1 (by simp [normal, Substitution.outputs])
      have he := graph.2 1 (by simp [normal, Substitution.outputs])
      apply (generateProjected_ground_iff N signature_closed generated_run v (closed_real v)).mpr
      have ht' : v.types 1 = .arr (v.types 4) ∅ (v.types 4) := by
        simpa [normal, Substitution.outputs, Ty.eval, Effect.eval] using ht
      have he' : v.effects 1 = ∅ := by
        simpa [normal, Substitution.outputs, Effect.eval] using he
      simpa [Ty.eval, Effect.eval, Effect.var, ht', he'] using
        (show GroundTyping sig O (closedContext.ground v) (.lam (.var 0))
          (.arr (v.types 4) ∅ (v.types 4)) ∅ from .lam (.var rfl rfl))
  refine ⟨normalValid, ?_⟩
  intro m hm
  have shape (v : Valuation GroundTy) :
      ∃ z, T.eval v (m.substitution.types 1) = .arr z ∅ z ∧
        (m.substitution.effects 1).eval v.effects = ∅ := by
    have hd := (X.holds_subst _ _ _).mp
      (Constraints.NormalForm.reconstruct_entails X hm v (hm.1 v))
    have ground := (generateProjected_ground_iff N signature_closed generated_run _
      (closed_real _)).mp hd
    obtain ⟨⟨a, b, latent, body, ht⟩, he⟩ := ground.lam_inv rfl
    obtain ⟨⟨s, t, found, member, le⟩, latentEmpty⟩ := body.var_inv rfl
    have hs : s = upper O a := Option.some.inj found.symm
    subst s
    change a = t at member
    change t = b at le
    have ab : a = b := member.trans le
    change GroundTy.arr a latent b = T.eval (m.substitution.pullback v) (.var 1) at ht
    rw [← ab, latentEmpty] at ht
    refine ⟨a, ?_, ?_⟩
    · simpa [Ty.eval, Substitution.pullback] using ht.symm
    · simpa [Effect.eval, Effect.var, Substitution.pullback] using he
  cases image : m.substitution.types 1 with
  | var i =>
      obtain ⟨z, hz, _⟩ := shape ⟨fun _ => .atom 0, fun _ => ∅⟩
      simp [image, Ty.eval] at hz
  | base b =>
      obtain ⟨z, hz, _⟩ := shape ⟨fun _ => .atom 0, fun _ => ∅⟩
      cases b <;> simp [image, Ty.eval] at hz
  | arr a latent b =>
      let φ : Substitution T := {
        domain := m.substitution.domain.union ⟨{4}, ∅⟩
        types := fun i => if i = 4 then a else m.substitution.types i
        effects := m.substitution.effects
        types_outside := by
          intro i hi
          have hi' : i ∉ m.substitution.domain.types ∧ i ≠ 4 := by simpa [Names.union, and_comm] using hi
          simp [hi'.2, m.substitution.types_outside i hi'.1]
        effects_outside := by
          intro i hi
          exact m.substitution.effects_outside i (by simpa [Names.union] using hi) }
      refine ⟨φ, ?_⟩
      intro v hv
      refine ⟨?_, trivial⟩
      obtain ⟨z, hz, he⟩ := shape v
      rw [image] at hz
      obtain ⟨ha, hl, hb⟩ := GroundTy.arr.inj hz
      constructor
      · intro i hi
        have not4 : i ≠ 4 := by
          intro h
          subst i
          have fresh : 4 ∉ observed.types := by decide
          exact fresh hi
        by_cases is1 : i = 1
        · subst i
          simp [normal, Substitution.outputs, φ, Substitution.pullback, image,
            Ty.eval, Effect.eval, ha, hb]
          exact hl.symm
        · simp [normal, Substitution.outputs, φ, Substitution.pullback, is1, not4,
            Ty.eval]
      · intro i _
        by_cases is1 : i = 1
        · subst i
          simpa [normal, Substitution.outputs, φ, Substitution.pullback, Effect.eval] using he.symm
        · simp [normal, Substitution.outputs, φ, Substitution.pullback, is1, Effect.eval, Effect.var]

/-- An unrelated closed qualified assumption must not freeze the output's
polymorphic parameter. The old environment-support choice excluded name 4. -/
theorem closed_qualified_generalizes :
    (reconstructedScheme closedContext normal).bound = ⟨{4}, ∅⟩ ∧
    4 ∈ (closedContext.subst normal.substitution).support.types := by decide

theorem closed_qualified_comparison :
    Instance X X.top (reconstructedScheme closedContext normal).valueScheme
      (.qualified ⟨{4}, ∅⟩ X.top (.arr (.var 4) ∅ (.var 4))) := by
  have presentation : (reconstructedScheme closedContext normal).valueScheme =
      .qualified ⟨{4}, ∅⟩ X.top (.arr (.var 4) ∅ (.var 4)) := by
    change Scheme.qualified (reconstructedScheme closedContext normal).bound X.top
      (.arr (.var 4) ∅ (.var 4)) = _
    rw [closed_qualified_generalizes.1]
  rw [presentation]
  apply Instance.of_mono_targets ?_ (fun _ _ _ h => h)
  intro v _
  exact ⟨.arr (v.types 4) ∅ (v.types 4), v,
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩, trivial, rfl⟩

/-- Target realizability is not silently added to Theorem 17. -/
theorem unrealizable_target_complete :
    ∃ (Y : Constraints T O) (Q : Y.ScopedPrincipalNormalizer) (c : Y.Formula) (s : Scheme Y),
      Q.solved = Y.Satisfiable ∧ ¬ s.Realizable c ∧
      ∃ n, inferTerm (fun _ => none) Y (Constraints.Simplifier.identity Y) Q [] (.lam (.var 0)) =
        some (.reconstructed n) ∧
        Instance Y c (reconstructedScheme [] n).valueScheme s ∧
        Y.Entails c (reconstructedScheme [] n).outer := by
  obtain ⟨Y, c, s, typed, notReal, _⟩ := RealizabilityExample.valid_let_without_realizable_scheme
  obtain ⟨n, run, _, cover, _⟩ := inferTerm_satisfiable_open
    (Constraints.Simplifier.identity Y) typed (by intro t ht; cases ht)
  have target := cover _ _ _ typed (by intro t ht; cases ht)
  exact ⟨Y, Constraints.ScopedPrincipalNormalizer.satisfiable Y, c, s, rfl, notReal,
    n, run, target.2, target.1⟩

private def capture : Substitution T := Substitution.outputs 0 0 (.var 1) (.var 1)

/-- The target is qualified, both ranges hit its old binder, and the source
derivation ends in a nonempty existential projection. -/
theorem projected_capture_complete :
    let c := X.subst capture OpenExamples.condition
    let g := OpenExamples.qualifiedContext.subst capture
    let s := OpenExamples.qualified.subst capture
    ∃ n, inferTerm sig X N P g (.var 0) = some (.reconstructed n) ∧
      Instance X (X.existsNames ⟨{50}, {50}⟩ c) (reconstructedScheme g n).valueScheme s ∧
      X.Entails (X.existsNames ⟨{50}, {50}⟩ c) (reconstructedScheme g n).outer := by
  dsimp only
  let c := X.subst capture OpenExamples.condition
  let g := OpenExamples.qualifiedContext
  let s := OpenExamples.qualified.subst capture
  let b : Names := ⟨{50}, {50}⟩
  have sat : X.Satisfiable c := ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, rfl⟩
  have real := OpenExamples.qualified_realizable.subst capture
  have typed : Typing sig X X.Satisfiable c (g.subst capture) (.var 0) s ∅ := by
    refine ⟨.var rfl, Derivation.valid_of_satisfiable _ sat ?_⟩
    exact OpenExamples.qualified_realizable.admissible_subst capture sat
  have fresh : b.Disjoint (g.support.union capture.range) := by
    constructor <;> decide
  have hc : b.Disjoint (X.support c) := by constructor <;> decide
  have proj := typed.existsIntro
    ((X.admissible_satisfiable_iff _).mpr ((X.satisfiable_exists_iff b c).mpr sat))
    (g.subst_avoids capture b fresh)
    (Scheme.subst_avoids _ capture b (by constructor <;> decide))
    (by simp)
  have realProj := real.weaken (X.project_independent b c hc).1
  obtain ⟨n, run, _, cover, _⟩ := inferTerm_satisfiable_open N proj realProj
  have target := cover _ _ _ proj realProj
  exact ⟨n, run, target.2, target.1⟩

end EHMX.HMX.ReconstructionCompletenessExamples
