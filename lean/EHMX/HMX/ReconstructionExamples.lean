import EHMX.HMX.TermReconstruction
import EHMX.HMX.ReconstructionSoundness
import EHMX.HMX.ReconstructionCompleteness
import EHMX.HMX.OpenExamples

namespace EHMX.HMX.ReconstructionExamples
private abbrev T := equalityTypes
private abbrev O := TypeOrder.equality T
private abbrev X := Constraints.semantic T O

private def capture : Substitution T where
  domain := ⟨{0}, {0}⟩
  types := fun i => if i = 0 then .var 1 else .var i
  effects := fun i => if i = 0 then Effect.var 1 else Effect.var i
  types_outside := by intro i hi; simp at hi; simp [hi]
  effects_outside := by intro i hi; simp at hi; simp [hi]

private def inspect : Scheme X → Names × Ty
  | .mono t => (Names.empty, t)
  | .qualified a _ t => (a, t)

private def source : Scheme X := .qualified ⟨{1}, {1}⟩ X.top
  (.arr (.var 0) (Effect.var 0) (.arr (.var 1) (Effect.var 1) (.base .int)))

/-- Both type and effect substitution images deliberately collide with binders. -/
theorem capture_avoided : inspect (source.subst capture) =
    (⟨{3}, {3}⟩, .arr (.var 1) (Effect.var 1)
      (.arr (.var 3) (Effect.var 3) (.base .int))) := by decide

theorem capture_environment (v : Valuation T.Value) :
    (Context.subst capture [source]).ground v = Context.ground [source] (capture.pullback v) :=
  Context.ground_subst capture [source] v

private def polyIdentity : Scheme X := .qualified ⟨{2}, ∅⟩ X.top
  (.arr (.var 2) ∅ (.var 2))

private def qualifiedIdentity : Scheme X := .qualified ⟨{1}, ∅⟩
  (X.eq (.var 0) (.var 1)) (.arr (.var 1) ∅ (.var 1))

private theorem identity_instance : Instance X X.top polyIdentity qualifiedIdentity := by
  let a : Names := ⟨{1}, ∅⟩
  let q := X.eq (T.var 0) (T.var 1)
  let θ : Substitution T := {
    domain := ⟨{2}, ∅⟩
    types := fun i => if i = 2 then T.var 1 else T.var i
    effects := Effect.var
    types_outside := by intro i hi; simp at hi; simp [hi]
    effects_outside := by intros; rfl }
  have body : Instance X (X.and X.top q) polyIdentity
      (.mono (.arr (.var 1) ∅ (.var 1))) := by
    apply Instance.forallLeft θ (fun _ h => h) (fun _ h => h)
    · intro v _
      exact (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial)
    · apply Instance.sub
      intro v _
      apply (X.holds_le _ _ _).mpr
      rfl
  have projected : X.Entails X.top (X.existsNames a q) := by
    intro v _
    let w : Valuation T.Value := ⟨Function.update v.types 1 (v.types 0), v.effects⟩
    apply (X.holds_exists _ _ _).mpr
    refine ⟨w, ⟨?_, fun _ _ => rfl⟩, ?_⟩
    · intro i hi
      have hn : i ≠ 1 := by simpa [a] using hi
      simp [w, hn]
    · change w.types 0 = w.types 1
      simp [w]
  have h : Instance X (X.and X.top (X.existsNames a q)) polyIdentity qualifiedIdentity :=
    .forallRight (X.top_avoids a)
      (by
        simp only [polyIdentity, Scheme.Avoids, Scheme.FreeType, Scheme.FreeEffect,
          a, Finset.mem_singleton, Finset.notMem_empty, forall_eq]
        constructor
        · rintro ⟨_, hf | hf⟩
          · exact (X.top_avoids a).1 1 (by simp [a]) hf
          · simp [Ty.fvTypes] at hf
        · intro i hi; exact hi.elim) body
  exact .equivalent ⟨X.entails_left _ _, fun v hv =>
    (X.holds_and _ _ _).mpr ⟨hv, projected v hv⟩⟩ h

/-- A genuinely qualified target retains its uniform instance when the free
variable is substituted by the target's old bound name. -/
theorem qualified_instance_capture :
    Instance X (X.subst capture X.top)
      (polyIdentity.subst capture) (qualifiedIdentity.subst capture) :=
  identity_instance.subst capture

theorem qualified_target_binder_fresh :
    inspect (qualifiedIdentity.subst capture) =
      (⟨{3}, ∅⟩, .arr (.var 3) ∅ (.var 3)) := by decide

/-- The requested target binds 1, but the environment uses 1 freely.
Qualified instance application must freshen that binder before generalizing. -/
theorem qualified_instance_in_open_context :
    Typing (fun _ => none) X X.Satisfiable X.top
      [polyIdentity, .mono (.var 1)] (.var 0) qualifiedIdentity ∅ := by
  have topSat : X.Satisfiable X.top :=
    ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, trivial⟩
  have source : Typing (fun _ => none) X X.Satisfiable X.top
      [polyIdentity, .mono (.var 1)] (.var 0) polyIdentity ∅ := by
    refine ⟨.var rfl, Derivation.valid_of_satisfiable _ topSat ?_⟩
    apply Context.admissible_cons
    · apply Context.admissible_cons
      · intro s hs; cases hs
      · trivial
    · exact (X.admissible_satisfiable_iff _).mpr topSat
  apply source.instance_value (fun _ h => h) (Constraints.SolvedClosure.satisfiable X)
    (.var 0) identity_instance
  exact (X.admissible_satisfiable_iff _).mpr
    ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, rfl⟩

/-- The existing non-realizable let example is nevertheless a legitimate
self-approximation when its qualifier is admissible. Uniform realizability
must not be imposed on this reflexivity argument. -/
theorem admissible_unrealizable_scheme_approximation :
    ∃ (Y : Constraints equalityTypes (TypeOrder.equality equalityTypes))
      (c : Y.Formula) (s : Scheme Y),
      ¬ s.Realizable c ∧
      (∀ t, s.Approximates Y.Satisfiable c t → ¬ t.Realizable c) ∧
      s.Approximates Y.Satisfiable c s ∧
      Context.Approximates Y.Satisfiable c [s] [s] ∧
      Typing (fun _ => none) Y Y.Satisfiable c []
        (.letE (.lam (.var 0)) (.int 0)) (.mono (.base .int)) ∅ := by
  obtain ⟨Y, c, s, typed, notReal, letTyped⟩ :=
    RealizabilityExample.valid_let_without_realizable_scheme
  have approx := typed.result_approximates_self typed.root.2.2
    (by intro v hv t ht; cases ht)
  exact ⟨Y, c, s, notReal,
    fun _ h ht => notReal (h.realizable_iff.mpr ht), approx, .cons approx .nil, letTyped⟩

/-- The same finite name bound protects both type and effect generalization. -/
theorem substituted_environment_fresh (a : Names)
    (fresh : a.Disjoint ((Context.support [source]).union capture.range)) :
    (Context.subst capture [source]).Avoids a :=
  Context.subst_avoids [source] capture a fresh

private def swap : Substitution T where
  domain := ⟨{0, 1}, ∅⟩
  types := fun i => if i = 0 then .var 1 else if i = 1 then .var 0 else .var i
  effects := Effect.var
  types_outside := by intro i hi; simp at hi; simp [hi.1, hi.2]
  effects_outside := by intros; rfl

theorem swap_not_solved : ¬ swap.Solved := by
  intro h
  have H := h.type_range 0 (by decide)
  have bad := Finset.disjoint_left.mp H.1 (show 1 ∈ swap.domain.types by decide)
    (show 1 ∈ (T.support (swap.types 0)).types by decide)
  exact bad

private def condition : X.Formula := X.eq (T.var 0) (T.literal .int)
private def wanted : X.Formula := X.eq (T.var 1) (T.literal .int)

theorem swap_not_invariant : ¬ X.Equivalent (X.subst swap condition) condition := by
  intro h
  let v : Valuation T.Value := ⟨fun i => if i = 0 then .atom 0 else .atom 1, fun _ => ∅⟩
  have H := h.2 v (show X.holds condition v from rfl)
  change GroundTy.atom 1 = GroundTy.atom 0 at H
  cases H

/-- New completeness accepts a cyclic raw map and a non-invariant C. The
previous competitor theorem required both of the excluded hypotheses. -/
theorem fresh_competitor_covers_swap :
    ∃ n, (Constraints.ScopedPrincipalNormalizer.satisfiable X).normalize
        ⟨{0, 1}, ∅⟩ wanted = some n ∧
      ∃ φ : Substitution T,
        (∀ v, X.holds condition v → (n.substitution.pullback (φ.pullback v)).AgreeOn (swap.pullback v) ⟨{0, 1}, ∅⟩) ∧
        X.Entails condition (X.subst φ n.residual) := by
  apply Constraints.ScopedPrincipalNormalizer.complete_of_substitution
    (Constraints.ScopedPrincipalNormalizer.satisfiable X)
    (Constraints.SolvedClosure.satisfiable X).rename
  · constructor
    · intro i hi
      have h := X.freeType_mem_support ((X.mem_freeNames_types wanted i).mp hi)
      change i ∈ ({1} ∪ ∅ : Finset Nat) at h
      simpa using Finset.mem_union_right ({0} : Finset Nat) h
    · intro i hi
      have h := X.freeEffect_mem_support ((X.mem_freeNames_effects wanted i).mp hi)
      change i ∈ (∅ ∪ ∅ : Finset Nat) at h
      simp at h
  · exact (X.admissible_satisfiable_iff _).mpr
      ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, rfl⟩
  · intro v hv
    exact hv

/-- The generic reconstruction path preserves the existing qualified/open case. -/
theorem qualified_reconstruction (D : SatDecider X) :
    ∃ n, inferTerm (fun _ => some ⟨⟨{0}, ∅⟩, T.var 0, T.var 0⟩)
      X (Constraints.Simplifier.identity X) D.normalizer
      OpenExamples.qualifiedContext (.var 0) = some (.reconstructed n) :=
  D.inferTerm_complete _ OpenExamples.qualified_typed OpenExamples.qualified_realizable

private def signature : Signature T := fun _ => some ⟨⟨{0}, ∅⟩, T.var 0, T.var 0⟩

private theorem reconstruction_of_ground (D : SatDecider X) {e : Expr} {t : Ty}
    (ground : ∀ v, GroundTyping signature O [] e (T.eval v t) ∅) :
    ∃ n, inferTerm signature X (Constraints.Simplifier.identity X) D.normalizer [] e =
      some (.reconstructed n) := by
  have typed : Typing signature X X.Satisfiable X.top [] e (.mono t) ∅ := by
    apply Typing.of_ground (c := X.top) (Constraints.Simplifier.identity X) (by intro s hs; cases hs)
      ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, trivial⟩
    intro v _
    simpa [Context.ground, Effect.eval] using ground v
  exact D.inferTerm_complete _ typed (by intro s hs; cases hs)

theorem polymorphic_let_reconstruction (D : SatDecider X) :
    ∃ n, inferTerm signature X (Constraints.Simplifier.identity X) D.normalizer []
      AlgorithmExamples.polymorphicLet = some (.reconstructed n) :=
  reconstruction_of_ground D (t := T.literal .bool) (fun _ => AlgorithmExamples.polymorphicLet_ground)

theorem handler_reconstruction (D : SatDecider X) :
    ∃ n, inferTerm signature X (Constraints.Simplifier.identity X) D.normalizer []
      AlgorithmExamples.resumeIdentity = some (.reconstructed n) :=
  reconstruction_of_ground D (t := T.literal .int) (fun _ => AlgorithmExamples.resumeIdentity_ground)

theorem nested_handler_reconstruction (D : SatDecider X) :
    ∃ n, inferTerm signature X (Constraints.Simplifier.identity X) D.normalizer []
      (.handle AlgorithmExamples.resumeIdentity 0 (.var 0) (.app (.var 0) (.var 1))) =
        some (.reconstructed n) :=
  reconstruction_of_ground D (t := T.literal .int) (fun _ => AlgorithmExamples.nestedHandler_ground)

/-- An empty representation is a lawful normalizer whose failure proves no
representation, even for a satisfiable generated constraint. -/
private def emptyRepresentation : X.ScopedPrincipalNormalizer where
  solved := fun _ => False
  solved_satisfiable := by intros; contradiction
  normalize := fun _ _ => none
  principal := by intros; contradiction
  failure := by intro u d _; simp [Constraints.NormalForm.IsNormal]

theorem representation_failure_is_not_inconsistency :
    ∃ d, inferTermAt (fun _ => none) X (Constraints.Simplifier.identity X)
      emptyRepresentation [] (.int 0) (T.literal .int) ∅ = some (.unrepresented d) ∧
      X.Satisfiable d := by
  let v : Valuation T.Value := ⟨fun _ => .atom 0, fun _ => ∅⟩
  obtain ⟨d, run, _, cover⟩ := Inference.groundComplete_projected_run
    (sig := fun _ => none) (Constraints.Simplifier.identity X) [] (.int 0) (T.literal .int) ∅
    ⟨v, GroundTyping.int 0⟩
  exact ⟨d, by simp [inferTermAt, run, emptyRepresentation], ⟨v, cover v (GroundTyping.int 0)⟩⟩


/-- Two value lets, perform, and two nested handlers share an open environment. -/
def mixedReconstruction : Expr :=
  .letE (.lam (.var 0)) (.letE (.lam (.var 0))
    (.handle
      (.handle (.perform 0 (.app (.var 0) (.var 2))) 0
        (.var 0) (.app (.var 0) (.var 1)))
      0 (.var 0) (.app (.var 0) (.var 1))))

private def mixedContext : Context X := [.mono (.var 0), source]

private theorem reconstruction_signature_closed : signature.Closed := by
  intro op d h
  cases h
  simp [Operation.Closed, Ty.fvTypes, Ty.fvEffects]

private theorem top_effect_solved : EffectResiduals.Solved X X.top :=
  ⟨⟨⟨fun _ => .atom 0, fun _ => ∅⟩, trivial⟩, fun _ _ _ => Iff.rfl⟩

private theorem mixed_admissible : mixedContext.Admissible (EffectResiduals.Solved X) := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · trivial
  · have hs : s = source := List.mem_singleton.mp hs
    subst s
    exact ⟨X.top, top_effect_solved, X.entails_refl _, X.entails_refl _⟩

private theorem mixed_realizable : mixedContext.Realizable X.top := by
  intro s hs
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ⟨.var 0, .sub (fun _ _ => rfl)⟩
  · have hs : s = source := List.mem_singleton.mp hs
    subst s
    refine ⟨_, .forallLeft (Substitution.identity T)
      (by simp [Substitution.identity, Names.empty])
      (by simp [Substitution.identity, Names.empty]) ?_ (.sub (fun _ _ => rfl))⟩
    intro v _
    exact (X.holds_subst _ _ _).mpr trivial

/-- The real generator, including its existential projections, meets the
transformation's rule condition for mixed lets and nested handlers. -/
theorem mixed_generated_rules :
    ∃ d, generateProjected signature X (Constraints.Simplifier.identity X)
      mixedContext mixedReconstruction (.var 0) (Effect.var 0) = some d ∧
      ∃ tree : Derivation signature X d mixedContext mixedReconstruction
        (.mono (.var 0)) (Effect.var 0), tree.UsesReconstructionRules := by
  have success : (generateProjected signature X (Constraints.Simplifier.identity X)
      mixedContext mixedReconstruction (.var 0) (Effect.var 0)).isSome = true := by decide
  cases run : generateProjected signature X (Constraints.Simplifier.identity X)
      mixedContext mixedReconstruction (.var 0) (Effect.var 0) with
  | none => simp [run] at success
  | some d =>
    exact ⟨d, rfl, (generateProjected_sound _ reconstruction_signature_closed run).sound_reconstruction.1⟩

/-- Both substitution ranges collide with the qualifier's old bound name.
Admissibility and self-approximation still hold in the actual substituted context. -/
theorem effect_environment_capture :
    (mixedContext.subst capture).Approximates (EffectResiduals.Solved X) X.top
      (mixedContext.subst capture) :=
  EffectResiduals.output_environment_self mixed_admissible mixed_realizable capture top_effect_solved.1

/-- Qualified existential projection remains outside the proved transformation. -/
theorem qualified_projection_excluded {c : X.Formula} {g : Context X} {e : Expr}
    {A B : Names} {d : X.Formula} {t : Ty} {eff : Effect}
    (tree : Derivation signature X c g e (.qualified B d t) eff)
    (fg : g.Avoids A) (fs : (Scheme.qualified B d t).Avoids A)
    (fe : Disjoint A.effects eff.vars) :
    ¬ (Derivation.existsIntro fg fs fe tree).UsesReconstructionRules := by
  rintro ⟨⟨u, h⟩, _⟩
  cases h

section ConditionalSoundness
variable (P : X.ScopedPrincipalNormalizer)
    (hsol : P.solved = EffectResiduals.Solved X)
    (closure : X.SolvedClosure P.solved)
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution T, θ.domain.Subset a ∧ X.Admissible P.solved (X.subst θ d))

include hsol closure lift

/-- The public Theorem 16 uses the generated program, exact substituted context,
type and effect. Solver assumptions remain explicit; no complete solver is supplied. -/
theorem mixed_reconstruction_sound {n : X.NormalForm}
    (run : inferTermAt signature X (Constraints.Simplifier.identity X) P
      mixedContext mixedReconstruction (.var 0) (Effect.var 0) = some (.reconstructed n)) :
    Typing signature X P.solved n.residual (mixedContext.subst n.substitution)
      mixedReconstruction (.mono (n.substitution.apply (.var 0)))
      ((Effect.var 0).subst n.substitution.effects) := by
  have allow : ∀ (r : X.Formula) (s : Substitution T), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)) := by
    rw [hsol]
    exact fun _ _ => EffectResiduals.effect_graph_allowed X
  apply inferTermAt_sound_effectOnly _ P hsol closure allow lift
    (r := X.top) (by rw [hsol]; exact top_effect_solved) (fun _ => trivial)
    reconstruction_signature_closed run
  · rw [hsol]; exact mixed_admissible
  · exact mixed_realizable

/-- Theorem 17 applied to the same-solved-set judgment of the mixed open
program: two value lets, perform, and nested handlers. -/
theorem mixed_reconstruction_complete
    (shape : ∀ u d n, P.normalize u d = some n →
      (∀ i, ReconstructionFactor.VariableEffects (n.substitution.types i)) ∧
      n.substitution.effects = Effect.var) {n : X.NormalForm}
    (run : inferTermAt signature X (Constraints.Simplifier.identity X) P
      mixedContext mixedReconstruction (.var 0) (Effect.var 0) = some (.reconstructed n)) :
    ∃ m, inferTerm signature X (Constraints.Simplifier.identity X) P
        mixedContext mixedReconstruction = some (.reconstructed m) ∧ ∃ φ,
      (∀ v, X.holds n.residual v → (m.substitution.pullback (φ.pullback v)).AgreeOn
        (n.substitution.pullback v) mixedContext.support) ∧
      Instance X n.residual ((reconstructedScheme mixedContext m).valueScheme.subst φ)
        (.mono (n.substitution.apply (.var 0))) ∧
      X.Entails n.residual (X.subst φ (reconstructedScheme mixedContext m).outer) ∧
      ∀ v, X.holds n.residual v → (reconstructedScheme mixedContext m).effect.eval (φ.pullback v).effects =
        ((Effect.var 0).subst n.substitution.effects).eval v.effects := by
  have typed := mixed_reconstruction_sound P hsol closure lift run
  have real : (mixedContext.subst n.substitution).Realizable n.residual :=
    (mixed_realizable.subst n.substitution).weaken (fun v _ =>
      (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial))
  have reflect : EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved := by
    rw [hsol]
    exact EffectResidualNormalization.effectOnly_reflection
  exact inferTerm_complete_scheme _ P closure reflect shape n.substitution typed real

end ConditionalSoundness

end EHMX.HMX.ReconstructionExamples
