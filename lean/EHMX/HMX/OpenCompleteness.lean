import EHMX.HMX.PrincipalCompleteness

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

/-- The condition left outside generalization; it need not be a tautology. -/
def ComputationScheme.outer {X : Constraints T O} (s : ComputationScheme X) : X.Formula :=
  X.existsNames s.bound s.condition

def ComputationScheme.valueScheme {X : Constraints T O} (s : ComputationScheme X) : Scheme X :=
  .qualified s.bound s.condition s.result

/-- Lift uniform monotype coverage to the syntactic scheme-instance judgment.
Realizability is relative to the target constraint, not to `top`. The target's
immediate effect is arbitrary; this lemma does not introduce polymorphic lets. -/
theorem Typing.instance_of_finite_realizable {sig : Signature T} {X : Constraints T O}
    {g : Context X} {e : Expr} {result : ComputationScheme X}
    (finite : ∀ c t eff, Typing sig X X.Satisfiable c g e (.mono t) eff →
      g.Realizable c → result.FiniteInstance c t eff)
    {c : X.Formula} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e s eff) (real : g.Realizable c) :
    Instance X c result.valueScheme s := by
  cases s with
  | mono t => exact (finite c t eff typed real).instance
  | qualified a q t =>
    obtain ⟨b, q', u, alpha, fresh⟩ := Scheme.fresh_alpha a q t
      ((X.support c).union result.valueScheme.support)
    have hc : X.Avoids c b := by
      constructor
      · intro i hi hf
        exact Finset.disjoint_left.mp fresh.1 hi
          (Finset.mem_union_left _ (X.freeType_mem_support hf))
      · intro i hi hf
        exact Finset.disjoint_left.mp fresh.2 hi
          (Finset.mem_union_left _ (X.freeEffect_mem_support hf))
    have hs : result.valueScheme.Avoids b := by
      constructor
      · intro i hi hf
        exact Finset.disjoint_left.mp fresh.1 hi
          (Finset.mem_union_right _ (Scheme.freeType_mem_support hf))
      · intro i hi hf
        exact Finset.disjoint_left.mp fresh.2 hi
          (Finset.mem_union_right _ (Scheme.freeEffect_mem_support hf))
    have renamed := typed.alpha alpha (alpha.admissible_iff.mp typed.root.2.2)
    have projected : X.Entails c (X.existsNames b q') := by
      obtain ⟨tree, _⟩ := renamed
      intro v hv
      obtain ⟨_, w, hw, hq, _⟩ := tree.groundInstance_exists v hv (real.ground hv)
      exact (X.holds_exists _ _ v).mpr ⟨w, hw, hq⟩
    have joint : X.Satisfiable (X.and c q') := by
      obtain ⟨v, hv⟩ := (X.admissible_satisfiable_iff _).mp typed.root.1
      obtain ⟨w, hw, hq⟩ := (X.holds_exists _ _ v).mp (projected v hv)
      exact ⟨w, (X.holds_and _ _ w).mpr ⟨(X.holds_agreeOutside hc hw).mpr hv, hq⟩⟩
    have mono : Typing sig X X.Satisfiable (X.and c q') g e (.mono u) eff := by
      have inst := (renamed.weaken ((X.admissible_satisfiable_iff _).mpr joint)
        (X.entails_left c q')).forallElim (Substitution.identity T)
        (by simp [Substitution.identity, Names.empty])
        (by simp [Substitution.identity, Names.empty])
        (show X.Entails (X.and c q') (X.subst (Substitution.identity T) q') from by
          intro v hv
          simpa only [X.holds_subst, Substitution.identity_pullback] using
            (X.holds_and _ _ v).mp hv |>.2)
      apply inst.sub
      intro v _
      apply (X.holds_le _ _ v).mpr
      simpa only [Substitution.eval_apply, Substitution.identity_pullback] using O.refl (T.eval v u)
    have cover := (finite (X.and c q') u eff mono (real.weaken (X.entails_left _ _))).instance
    have quantified := Instance.forallRight hc hs cover
    have equivalent : X.Equivalent (X.and c (X.existsNames b q')) c :=
      ⟨X.entails_left _ _, fun v hv => (X.holds_and _ _ v).mpr ⟨hv, projected v hv⟩⟩
    exact .alphaRight (.symm alpha) (Instance.equivalent equivalent quantified)

/-- Constraint-form completeness in an open environment. The same actual
generated result covers every realizable target judgment, including qualified
schemes. The outer condition is retained, and no satisfiability decider is used. -/
theorem Typing.principal_computation_open_at {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (a b : Nat) {g : Context X} {e : Expr}
    (freshT : a ∉ g.support.types) (freshE : b ∉ g.support.effects)
    {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e scheme eff) (real : g.Realizable c) :
    ∃ d, generateProjected sig X N g e (T.var a) (Effect.var b) = some d ∧
      Inference sig X N X.top g e (T.var a) (Effect.var b) d ∧ X.Satisfiable d ∧
      Typing sig X X.Satisfiable d g e (.mono (T.var a)) (Effect.var b) ∧
      let s := ComputationScheme.generalize g d (T.var a) (Effect.var b)
      ComputationTyping sig X X.Satisfiable s.outer g e s ∧
      (∀ c' scheme' eff', Typing sig X X.Satisfiable c' g e scheme' eff' →
        g.Realizable c' → X.Entails c' s.outer ∧ Instance X c' s.valueScheme scheme') ∧
      (∀ c' t' eff', Typing sig X X.Satisfiable c' g e (.mono t') eff' →
        g.Realizable c' → s.FiniteInstance c' t' eff') := by
  let outputs : Names := ⟨{a}, {b}⟩
  have fresh : g.Avoids outputs := by
    apply g.avoids_of_support_disjoint
    exact ⟨Finset.disjoint_singleton_left.mpr freshT, Finset.disjoint_singleton_left.mpr freshE⟩
  have liftGround {c' : X.Formula} {s' : Scheme X} {eff' : Effect}
      (ht : Typing sig X X.Satisfiable c' g e s' eff') (hr : g.Realizable c')
      (v : Valuation T.Value) (hv : X.holds c' v) :
      ∃ w, w.AgreeOutside v outputs ∧
        GroundTyping sig O (g.ground w) e (T.eval w (T.var a)) ((Effect.var b).eval w.effects) := by
    obtain ⟨tree, _⟩ := ht
    obtain ⟨u, hu⟩ := tree.groundInstance_exists v hv (hr.ground hv)
    let w : Valuation T.Value :=
      ⟨Function.update v.types a u, Function.update v.effects b (eff'.eval v.effects)⟩
    have outside : w.AgreeOutside v outputs := by
      constructor <;> intro i hi <;> simp only [outputs, Finset.mem_singleton] at hi
      · simp [w, Function.update, hi]
      · simp [w, Function.update, hi]
    refine ⟨w, outside, ?_⟩
    rw [Context.ground_avoids fresh outside]
    simpa [w, T.eval_var, Effect.eval, Effect.var] using tree.ground v hv (hr.ground hv) u hu
  obtain ⟨v, hv⟩ := (X.admissible_satisfiable_iff c).mp typed.root.1
  obtain ⟨seed, _, initial⟩ := liftGround typed real v hv
  obtain ⟨d, run, inferred, cover⟩ := Inference.groundComplete_projected_run N g e
    (T.var a) (Effect.var b) ⟨seed, initial⟩
  have sat : X.Satisfiable d := ⟨seed, cover seed initial⟩
  have valid := (inferred.sound_valid typed.root.2.1 sat).1
  let s := ComputationScheme.generalize g d (T.var a) (Effect.var b)
  have ha : a ∈ s.bound.types := by
    simp [s, ComputationScheme.generalize, Names.diff, Names.union, T.support_var, freshT]
  have hb : b ∈ s.bound.effects := by
    simp [s, ComputationScheme.generalize, Names.diff, Names.union, Effect.var, freshE]
  have scope : outputs.Subset s.bound :=
    ⟨fun _ hi => (Finset.mem_singleton.mp hi) ▸ ha,
      fun _ hi => (Finset.mem_singleton.mp hi) ▸ hb⟩
  have projected {c' : X.Formula} {s' : Scheme X} {eff' : Effect}
      (ht : Typing sig X X.Satisfiable c' g e s' eff') (hr : g.Realizable c') :
      X.Entails c' s.outer := by
    intro w hw
    obtain ⟨z, hz, hg⟩ := liftGround ht hr w hw
    exact (X.holds_exists _ _ w).mpr ⟨z,
      ⟨fun i hi => hz.1 i (fun hj => hi (scope.1 hj)),
        fun i hi => hz.2 i (fun hj => hi (scope.2 hj))⟩, cover z hg⟩
  have finite c' t' eff' (ht : Typing sig X X.Satisfiable c' g e (.mono t') eff')
      (hr : g.Realizable c') : s.FiniteInstance c' t' eff' := by
    let θ := Substitution.outputs a b t' eff'
    refine ⟨θ, scope.1, scope.2, ?_⟩
    intro w hw
    obtain ⟨tree, _⟩ := ht
    have ground := tree.ground w hw (hr.ground hw) _ (O.refl _)
    have shifted : GroundTyping sig O (g.ground (θ.pullback w)) e
        (T.eval (θ.pullback w) (T.var a)) ((Effect.var b).eval (θ.pullback w).effects) := by
      rw [Context.ground_avoids fresh (θ.pullback_outside w)]
      simpa [θ, Substitution.outputs, Substitution.pullback, T.eval_var, Effect.eval, Effect.var] using ground
    refine ⟨cover _ shifted, ?_, ?_⟩
    · simpa [s, ComputationScheme.generalize, θ, Substitution.outputs, Substitution.pullback,
        T.eval_var] using O.refl (T.eval w t')
    · simp [s, ComputationScheme.generalize, θ, Substitution.outputs, Substitution.pullback,
        Effect.eval, Effect.var]
  refine ⟨d, run, inferred, sat, valid, ?_, ?_, finite⟩
  · exact valid.computation_generalize
      ((X.admissible_satisfiable_iff _).mpr ((X.satisfiable_exists_iff _ _).mpr sat))
  · intro c' s' eff' ht hr
    exact ⟨projected ht hr, ht.instance_of_finite_realizable finite hr⟩

/-- The entry point's output slots are fresh even when the environment is open. -/
theorem Context.output_names_fresh {X : Constraints T O} (g : Context X) :
    g.support.shiftTypes 0 ∉ g.support.types ∧ g.support.shiftEffects 0 ∉ g.support.effects := by
  constructor <;> intro h
  · have bound := Finset.le_sup (f := id) h
    simp only [id_eq, Names.shiftTypes] at bound
    omega
  · have bound := Finset.le_sup (f := id) h
    simp only [id_eq, Names.shiftEffects] at bound
    omega

/-- Dissertation Theorem 15 in the present value-restricted, effectful system:
actual generation, outer entailment, and syntactic comparison with an arbitrary
target scheme. For monotype targets the same result also compares effects by
one finite substitution. Neither a closed environment nor a decider is assumed. -/
theorem Typing.inference_complete_scheme {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {g : Context X} {e : Expr}
    {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e scheme eff) (real : g.Realizable c) :
    ∃ d, generateProjected sig X N g e (T.var (g.support.shiftTypes 0))
        (Effect.var (g.support.shiftEffects 0)) = some d ∧ X.Satisfiable d ∧
      Typing sig X X.Satisfiable d g e (.mono (T.var (g.support.shiftTypes 0)))
        (Effect.var (g.support.shiftEffects 0)) ∧
      let s := ComputationScheme.generalize g d (T.var (g.support.shiftTypes 0))
        (Effect.var (g.support.shiftEffects 0))
      ComputationTyping sig X X.Satisfiable s.outer g e s ∧
      X.Entails c s.outer ∧ Instance X c s.valueScheme scheme ∧
      (∀ t, scheme = .mono t → s.FiniteInstance c t eff) := by
  obtain ⟨d, run, _, sat, valid, comp, cover, finite⟩ :=
    typed.principal_computation_open_at N _ _ g.output_names_fresh.1 g.output_names_fresh.2 real
  exact ⟨d, run, sat, valid, comp, (cover _ _ _ typed real).1,
    (cover _ _ _ typed real).2, fun t eq => finite c t eff (eq ▸ typed) real⟩

/-- Open values have ordinary principal pairs with a possibly nontrivial outer
constraint. `Realizable top` discharges realizability for every comparison in
the existing, unrestricted `PrincipalPair` definition. -/
theorem Typing.principal_value_open {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {g : Context X} {e : Expr}
    {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e scheme eff)
    (real : g.Realizable X.top) (value : Value e) :
    ∃ s : ComputationScheme X,
      PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
        g e s.outer s.valueScheme := by
  obtain ⟨d, _, _, _, _, comp, cover, _⟩ := typed.principal_computation_open_at N _ _
    g.output_names_fresh.1 g.output_names_fresh.2
    (real.weaken (fun v _ => (X.holds_top v).mpr trivial))
  refine ⟨_, comp.value value (comp.value_effect real value), ?_⟩
  intro c' s' ht
  exact cover c' s' ∅ ht (real.weaken (fun v _ => (X.holds_top v).mpr trivial))

/-- Recover the closed-environment corollary by discharging the retained outer
condition. Finite coverage, rather than only ground inclusion, is preserved. -/
theorem Typing.principal_closed_from_open {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {g : Context X} {e : Expr}
    {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e scheme eff)
    (closed : g.support = Names.empty) (real : g.Realizable X.top) :
    ∃ s : ComputationScheme X,
      PrincipalComputationScheme sig X X.Satisfiable g e s ∧
      (∀ c' t' eff', Typing sig X X.Satisfiable c' g e (.mono t') eff' →
        s.FiniteInstance c' t' eff') ∧
      (Value e → PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
        g e X.top s.valueScheme) := by
  have weakenReal c' : g.Realizable c' :=
    real.weaken (fun v _ => (X.holds_top v).mpr trivial)
  obtain ⟨d, _, _, sat, valid, _, _, finite⟩ := typed.principal_computation_open_at N _ _
    g.output_names_fresh.1 g.output_names_fresh.2 (weakenReal c)
  have topSat : X.Satisfiable X.top := by
    obtain ⟨v, _⟩ := sat
    exact ⟨v, (X.holds_top v).mpr trivial⟩
  have comp := valid.computation_generalize_closed closed sat
    ((X.admissible_satisfiable_iff _).mpr topSat)
  have allFinite c' t' eff' ht := finite c' t' eff' ht (weakenReal c')
  exact ⟨_, ⟨comp, fun c' t' eff' ht v hv => (allFinite c' t' eff' ht).ground v hv⟩,
    allFinite, fun hv => comp.principal_value (fun _ h => h) real hv allFinite⟩

end EHMX.HMX
