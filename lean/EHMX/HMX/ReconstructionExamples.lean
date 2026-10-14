import EHMX.HMX.TermReconstruction
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
    ∃ n, ((Constraints.PrincipalNormalizer.satisfiable X).scoped X).normalize
        ⟨{0, 1}, ∅⟩ wanted = some n ∧
      ∃ φ : Substitution T,
        (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn (swap.pullback v) ⟨{0, 1}, ∅⟩) ∧
        X.Entails condition (X.subst φ n.residual) := by
  apply Constraints.ScopedPrincipalNormalizer.complete_of_substitution
    ((Constraints.PrincipalNormalizer.satisfiable X).scoped X)
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

end EHMX.HMX.ReconstructionExamples
