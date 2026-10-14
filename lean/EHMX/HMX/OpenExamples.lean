import EHMX.HMX.AlgorithmExamples

namespace EHMX.HMX.OpenExamples

private abbrev T := equalityTypes
private abbrev O := TypeOrder.equality T
private abbrev X := Constraints.semantic T O
private abbrev N := Constraints.Simplifier.identity X
private def sig : Signature T := fun _ => some ⟨⟨{0}, ∅⟩, T.var 0, T.var 0⟩
private def intVal : Valuation T.Value := ⟨fun _ => .atom 0, fun _ => ∅⟩
private theorem top_sat : X.Satisfiable X.top := ⟨intVal, trivial⟩

/-- A genuinely open assumption: its qualifier is realizable under C, but not
under top. Bound name 1 is deliberately also the algorithm's fresh output name. -/
def condition : X.Formula := X.eq (T.var 0) (T.literal .int)
def qualified : Scheme X := .qualified ⟨{1}, {1}⟩ condition (T.var 1)
def qualifiedContext : Context X := [qualified]

theorem condition_sat : X.Satisfiable condition := ⟨intVal, rfl⟩

theorem qualified_realizable : qualifiedContext.Realizable condition := by
  intro s hs
  have eq : s = qualified := by simpa [qualifiedContext] using hs
  subst s
  refine ⟨T.literal .int, .forallLeft (Substitution.outputs 1 1 (T.literal .int) ∅)
    (by simp [Substitution.outputs]) (by simp [Substitution.outputs]) ?_ ?_⟩
  · intro v hv
    exact hv
  · apply Instance.sub
    intro v _
    exact (X.holds_le _ _ v).mpr rfl

theorem qualified_not_realizable_top : ¬ qualifiedContext.Realizable X.top := by
  intro real
  let v : Valuation T.Value := ⟨fun _ => .atom 1, fun _ => ∅⟩
  obtain ⟨_, w, hw, hc, _⟩ := (real qualified (by simp [qualifiedContext])).groundInstance
    (v := v) (show X.holds X.top v from trivial)
  have same := hw.1 0 (by decide)
  have eq : w.types 0 = GroundTy.atom 0 := hc
  have bad : GroundTy.atom 1 = GroundTy.atom 0 := same.symm.trans eq
  cases bad

theorem qualified_typed : Typing sig X X.Satisfiable condition qualifiedContext
    (.var 0) qualified ∅ := by
  have tree : Derivation sig X condition qualifiedContext (.var 0) qualified ∅ := .var rfl
  refine ⟨tree, tree.valid_of_satisfiable condition_sat ?_⟩
  intro s hs
  have eq : s = qualified := by simpa [qualifiedContext] using hs
  subst s
  exact (X.admissible_satisfiable_iff _).mpr condition_sat

/-- Compare against a fresh alpha-variant after an explicit projection rule. -/
theorem qualified_projected_alpha_complete :
    ∃ s' d, Scheme.AlphaEquivalent X qualified s' ∧
      generateProjected sig X N qualifiedContext (.var 0)
        (T.var (qualifiedContext.support.shiftTypes 0))
        (Effect.var (qualifiedContext.support.shiftEffects 0)) = some d ∧
      let s := ComputationScheme.generalize qualifiedContext d
        (T.var (qualifiedContext.support.shiftTypes 0))
        (Effect.var (qualifiedContext.support.shiftEffects 0))
      X.Entails condition s.outer ∧ Instance X condition s.valueScheme s' := by
  obtain ⟨a, q, t, alpha, _⟩ := Scheme.fresh_alpha ⟨{1}, {1}⟩ condition (T.var 1)
    ⟨{0, 1, 2}, {0, 1, 2}⟩
  have renamed := qualified_typed.alpha alpha (alpha.admissible_iff.mp qualified_typed.root.2.2)
  have projected := renamed.existsIntro
    ((X.admissible_satisfiable_iff _).mpr ((X.satisfiable_exists_iff Names.empty _).mpr condition_sat))
    (a := Names.empty) (by intro s hs; constructor <;> simp [Names.empty])
    (by constructor <;> simp [Names.empty]) (by simp [Names.empty])
  have ht := projected.weaken ((X.admissible_satisfiable_iff _).mpr condition_sat)
    (X.exists_intro Names.empty condition)
  obtain ⟨d, run, _, _, _, entails, inst, _⟩ := ht.inference_complete_scheme N qualified_realizable
  exact ⟨_, d, alpha, run, entails, inst⟩

theorem qualified_complete_of_decider (D : SatDecider X) :
    ∃ n, infer sig X N D.solver qualifiedContext (.var 0) = some (.solved n) ∧
      X.Entails condition (inferredScheme qualifiedContext n).outer ∧
      Instance X condition (inferredScheme qualifiedContext n).valueScheme qualified := by
  obtain ⟨n, run, _, entails, inst, _⟩ := D.infer_complete_scheme N qualified_typed qualified_realizable
  exact ⟨n, run, entails, inst⟩

/-- The generated outer condition really retains the free environmental
constraint a0 = Int. Satisfiability alone cannot justify replacing it by top. -/
theorem qualified_outer_condition :
    ∃ d, generateProjected sig X N qualifiedContext (.var 0)
        (T.var (qualifiedContext.support.shiftTypes 0))
        (Effect.var (qualifiedContext.support.shiftEffects 0)) = some d ∧
      let s := ComputationScheme.generalize qualifiedContext d
        (T.var (qualifiedContext.support.shiftTypes 0))
        (Effect.var (qualifiedContext.support.shiftEffects 0))
      X.Equivalent s.outer condition ∧ ¬ X.Entails X.top s.outer := by
  obtain ⟨d, run, _, _, _, entails, _, _⟩ :=
    qualified_typed.inference_complete_scheme N qualified_realizable
  let t := T.var (qualifiedContext.support.shiftTypes 0)
  let eff := Effect.var (qualifiedContext.support.shiftEffects 0)
  let fixed := (Inference.Protected X qualifiedContext t eff).union (X.support X.top)
  let raw := X.instantiateConstraint X.top qualified t eff (fixed.union (X.support X.top))
  have eq : X.existsNames ((X.support raw).diff fixed) raw = d := by
    exact Option.some.inj run
  have zeroContext : 0 ∈ qualifiedContext.support.types := by decide
  have zeroFixed : 0 ∈ fixed.types := by
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ zeroContext))
  have dc : X.Entails d condition := by
    intro v hv
    rw [← eq] at hv
    obtain ⟨w, hw, hr⟩ := (X.holds_exists _ _ v).mp hv
    have qual := (X.holds_checked _ _ _ _ _ _ w).mp hr |>.2.1
    have hwc : w.types 0 = GroundTy.atom 0 := qual
    have same := hw.1 0 (by simp [Names.diff, zeroFixed])
    exact same.symm.trans hwc
  let s := ComputationScheme.generalize qualifiedContext d t eff
  have back : X.Entails s.outer condition := by
    intro v hv
    obtain ⟨w, hw, hd⟩ := (X.holds_exists _ _ v).mp hv
    have same := hw.1 0 (by simp [s, ComputationScheme.generalize, Names.diff, zeroContext])
    exact same.symm.trans (dc w hd)
  refine ⟨d, run, ⟨back, entails⟩, ?_⟩
  intro tautology
  have bad := back ⟨fun _ => .atom 1, fun _ => ∅⟩ (tautology _ trivial)
  change GroundTy.atom 1 = GroundTy.atom 0 at bad
  cases bad

private def openContext : Context X := [.mono (T.var 0)]
private theorem open_admissible : openContext.Admissible X.Satisfiable := by
  intro s hs
  have eq : s = .mono (T.var 0) := by simpa [openContext] using hs
  subst s
  trivial
private theorem open_realizable : openContext.Realizable X.top := by
  intro s hs
  have eq : s = .mono (T.var 0) := by simpa [openContext] using hs
  subst s
  exact ⟨T.var 0, .sub (fun v _ => (X.holds_le _ _ v).mpr rfl)⟩

/-- A polymorphic identity in an environment with a free type variable. -/
theorem open_identity_typed : Typing sig X X.Satisfiable X.top openContext
    (.lam (.var 0)) (.qualified ⟨{1}, ∅⟩ X.top (T.arrow (T.var 1) ∅ (T.var 1))) ∅ := by
  have ht : Typing sig X X.Satisfiable X.top openContext (.lam (.var 0))
      (.mono (T.arrow (T.var 1) ∅ (T.var 1))) ∅ := by
    apply Typing.of_ground N open_admissible top_sat
    intro v _
    exact .lam (.var rfl rfl)
  have gen := ht.generalize (.lam (.var 0)) ⟨{1}, ∅⟩
    (openContext.avoids_of_support_disjoint _ (by
      simp [openContext, Context.support, Scheme.support, Names.union, Names.empty,
        T, equalityTypes, Ty.fvTypes, Ty.fvEffects, Names.Disjoint]))
    ((X.admissible_satisfiable_iff _).mpr ((X.satisfiable_exists_iff _ _).mpr top_sat))
  exact gen.weaken ((X.admissible_satisfiable_iff _).mpr top_sat) (X.exists_intro _ _)

theorem open_identity_principal (D : SatDecider X) :
    ∃ n, infer sig X N D.solver openContext (.lam (.var 0)) = some (.solved n) ∧
      PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
        openContext (.lam (.var 0)) (inferredScheme openContext n).outer
        (inferredScheme openContext n).valueScheme :=
  D.infer_principal_value_open N open_identity_typed open_realizable (.lam (.var 0))

/-- The handler proof is uniform in an extra open environment. -/
private theorem handle_ground (g : GroundContext T) {body : Expr} {ein : Finset Op}
    {result : T.Value}
    (bodyTyped : GroundTyping sig O g body result ein) (allowed : ein ⊆ {0}) :
    GroundTyping sig O g (.handle body 0 (.var 0) (.app (.var 0) (.var 1))) result ∅ := by
  let op : Operation T := ⟨⟨{0}, ∅⟩, T.var 0, T.var 0⟩
  apply GroundTyping.handle (raw := op) (decl := op) (input := result)
    (ein := ein) (er := ∅) (rest := ∅) (fun _ => ∅)
  · rfl
  · simp [op, Operation.Closed, Ty.fvTypes, Ty.fvEffects]
  · exact ⟨id, id, Function.injective_id.injOn, Function.injective_id.injOn, rfl⟩
  · exact bodyTyped
  · exact .var rfl rfl
  · intro w
    -- The two bound entries have the same indices with the open tail present.
    have hk' : GroundTyping sig O
        (upper O (T.groundArrow (T.eval w op.output) ∅ result) ::
         upper O (T.eval w op.input) :: g) (.var 0)
        (T.groundArrow (T.eval w op.output) ∅ result) ∅ := .var rfl rfl
    have hx : GroundTyping sig O
        (upper O (T.groundArrow (T.eval w op.output) ∅ result) ::
         upper O (T.eval w op.input) :: g) (.var 1) (T.eval w op.output) ∅ := .var rfl rfl
    simpa using GroundTyping.app hk' hx
  · simp
  · simp
  · simpa using allowed
  all_goals simp

def openResume : Expr := .handle (.perform 0 (.var 0)) 0 (.var 0) (.app (.var 0) (.var 1))

theorem open_nested_handler_complete (D : SatDecider X) :
    ∃ n, infer sig X N D.solver openContext
        (.handle openResume 0 (.var 0) (.app (.var 0) (.var 1))) = some (.solved n) ∧
      let s := inferredScheme openContext n
      X.Entails X.top s.outer ∧ s.FiniteInstance X.top (T.var 0) ∅ := by
  have typed : Typing sig X X.Satisfiable X.top openContext
      (.handle openResume 0 (.var 0) (.app (.var 0) (.var 1)))
      (.mono (T.var 0)) ∅ := by
    apply Typing.of_ground N open_admissible top_sat
    intro v _
    have perform : GroundTyping sig O (openContext.ground v) (.perform 0 (.var 0)) (v.types 0) {0} := by
      have h := GroundTyping.perform (sig := sig) (O := O) (g := openContext.ground v)
        (op := 0) (raw := ⟨⟨{0}, ∅⟩, T.var 0, T.var 0⟩) v rfl
        (by simp [Operation.Closed, Ty.fvTypes, Ty.fvEffects])
        (.var (i := 0) (s := upper O (v.types 0)) rfl rfl)
      simpa [T, equalityTypes, Ty.eval] using h
    exact handle_ground _ (handle_ground _ perform (fun _ h => h)) (by simp)
  obtain ⟨n, run, _, entails, _, finite⟩ := D.infer_complete_scheme N typed open_realizable
  exact ⟨n, run, entails, finite _ rfl⟩

end EHMX.HMX.OpenExamples
