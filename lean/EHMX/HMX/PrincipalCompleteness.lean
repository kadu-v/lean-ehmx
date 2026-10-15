import EHMX.HMX.AlgorithmSoundness
import EHMX.HMX.NormalizationCompleteness
import EHMX.HMX.ComputationSchemes
import EHMX.HMX.PartialSolving

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

/-- Declarative completeness also applies to open environments. One generated
constraint covers every source solution, preserving any chosen finite support. -/
theorem Typing.inference_complete {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {g : Context X} {e : Expr} {c : X.Formula} {t : T.Term} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e (.mono t) eff) (hreal : g.Realizable c)
    (fixed : Names) (hf : (Inference.Protected X g t eff).Subset fixed) :
    ∃ d, Inference sig X N X.top g e t eff d ∧
      Typing sig X X.Satisfiable d g e (.mono t) eff ∧
      ∀ v, X.holds c v → ∃ w, w.AgreeOn v fixed ∧ X.holds d w := by
  have root := typed.root
  obtain ⟨tree, _⟩ := typed
  have ground (v : Valuation T.Value) (hc : X.holds c v) :=
    tree.ground v hc (hreal.ground hc) _ (O.refl (T.eval v t))
  obtain ⟨v, hv⟩ := (X.admissible_satisfiable_iff c).mp root.1
  obtain ⟨d, _, hd, cover⟩ := Inference.groundComplete sig X N e g t eff fixed hf ⟨v, ground v hv⟩
  obtain ⟨w, _, hw⟩ := cover v (ground v hv)
  exact ⟨d, hd, (hd.sound_valid root.2.1 ⟨w, hw⟩).1,
    fun v hv => cover v (ground v hv)⟩

/-- Hide local inference names. Every ground typing then satisfies the same
generated constraint at its original valuation, without changing that valuation. -/
theorem Inference.groundComplete_projected_run {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (g : Context X) (e : Expr) (t : T.Term) (eff : Effect)
    (hex : ∃ v, GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects)) :
    ∃ d, generateProjected sig X N g e t eff = some d ∧
      Inference sig X N X.top g e t eff d ∧
      ∀ v, GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects) → X.holds d v := by
  let fixed := (Inference.Protected X g t eff).union (X.support X.top)
  have hf : (Inference.Protected X g t eff).Subset fixed := Names.subset_union_left _ _
  obtain ⟨d, run, hd, cover⟩ := Inference.groundComplete sig X N e g t eff fixed hf hex
  let hidden := (X.support d).diff fixed
  have hdis : hidden.Disjoint fixed :=
    ⟨Finset.disjoint_left.mpr (fun _ hi => (Finset.mem_sdiff.mp hi).2),
      Finset.disjoint_left.mpr (fun _ hi => (Finset.mem_sdiff.mp hi).2)⟩
  have hgt := hdis.mono_right ((Inference.Protected.context g t eff).trans hf)
  have htt := hdis.mono_right ((Inference.Protected.type g t eff).trans hf)
  have projected : Inference sig X N X.top g e t eff (X.existsNames hidden d) :=
    hd.project (g.avoids_of_support_disjoint hidden hgt)
      ⟨fun _ hi hj => Finset.disjoint_left.mp htt.1 hi hj,
        fun _ hi hj => Finset.disjoint_left.mp htt.2 hi hj⟩
      (Finset.disjoint_left.mpr (fun _ hi hj => Finset.disjoint_left.mp hdis.2 hi
        (hf.2 (Inference.Protected.effect g t eff hj))))
      (hdis.mono_right (Names.subset_union_right _ _))
  refine ⟨X.existsNames hidden d, by simp [generateProjected, run, fixed, hidden], projected, ?_⟩
  intro u hu
  obtain ⟨w, hw, hdw⟩ := cover u hu
  let z := u.patch w hidden
  have hz : z.AgreeOn w (X.support d) := by
    constructor
    · intro i hi
      by_cases hf : i ∈ fixed.types
      · simp [z, Valuation.patch, hidden, Names.diff, hf, hw.1 i hf]
      · simp [z, Valuation.patch, hidden, Names.diff, hi, hf]
    · intro i hi
      by_cases hf : i ∈ fixed.effects
      · simp [z, Valuation.patch, hidden, Names.diff, hf, hw.2 i hf]
      · simp [z, Valuation.patch, hidden, Names.diff, hi, hf]
  exact (X.holds_exists _ _ u).mpr
    ⟨z, u.patch_agreeOutside w hidden, (X.holds_support d z w hz).mpr hdw⟩

theorem Inference.groundComplete_projected {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (g : Context X) (e : Expr) (t : T.Term) (eff : Effect)
    (hex : ∃ v, GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects)) :
    ∃ d, Inference sig X N X.top g e t eff d ∧
      ∀ v, GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects) → X.holds d v := by
  obtain ⟨d, _, hd, cover⟩ := Inference.groundComplete_projected_run N g e t eff hex
  exact ⟨d, hd, cover⟩

/-- Uniform ground typability yields a valid declarative derivation. Local
inference names are projected away while the context and result support is fixed. -/
theorem Typing.of_ground {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {g : Context X} {e : Expr} {c : X.Formula} {t : T.Term} {eff : Effect}
    (hg : g.Admissible X.Satisfiable) (hc : X.Satisfiable c)
    (ground : ∀ v, X.holds c v →
      GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects)) :
    Typing sig X X.Satisfiable c g e (.mono t) eff := by
  obtain ⟨v, hv⟩ := hc
  obtain ⟨d, hd, cover⟩ := Inference.groundComplete_projected N g e t eff ⟨v, ground v hv⟩
  have entails : X.Entails c d := fun w hw => cover w (ground w hw)
  exact (hd.sound_valid hg ⟨v, entails v hv⟩).1.weaken
    ((X.admissible_satisfiable_iff c).mpr ⟨v, hv⟩) entails

/-- Substitution and strengthening for an open environment whose free names are
unchanged. The reconstructed derivation includes lets and handler clauses; its
validity remains satisfiability-based, not validity for an arbitrary solved set. -/
theorem Typing.substitute_avoiding_context {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {c d : X.Formula} {g : Context X} {e : Expr}
    {t : T.Term} {eff : Effect} (typed : Typing sig X X.Satisfiable c g e (.mono t) eff)
    (θ : Substitution T) (hg : g.Avoids θ.domain) (hreal : g.Realizable c)
    (hd : X.Satisfiable d) (he : X.Entails d (X.subst θ c)) :
    Typing sig X X.Satisfiable d g e (.mono (θ.apply t)) (eff.subst θ.effects) := by
  have root := typed.root
  obtain ⟨tree, _⟩ := typed
  apply Typing.of_ground N root.2.1 hd
  intro v hv
  have hc := (X.holds_subst _ _ v).mp (he v hv)
  have h := tree.ground (θ.pullback v) hc (hreal.ground hc) _ (O.refl _)
  rw [Context.ground_avoids hg (θ.pullback_outside v)] at h
  simpa only [Substitution.eval_apply, Effect.eval_subst, Substitution.pullback] using h

/-- Conditional soundness of a partial solver's output. No satisfiability,
principal-normalizer, or solver-completeness assumption is needed. The residual
must entail the substituted generated constraint; environment names stay fixed.
This applies to every inference constructor, including let and handlers. -/
theorem Inference.normalized_ground_sound {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {c d r : X.Formula} {g : Context X} {e : Expr}
    {t : T.Term} {eff : Effect}
    (inferred : Inference sig X N c g e t eff d)
    (θ : Substitution T) (fixed : g.Avoids θ.domain) (real : g.Realizable c)
    (sound : X.Entails r (X.subst θ d)) :
    ∀ v, X.holds r v → GroundTyping sig O (g.ground v) e
      (T.eval v (θ.apply t)) ((eff.subst θ.effects).eval v.effects) := by
  obtain ⟨⟨tree⟩, input⟩ := inferred.sound
  intro v hv
  have hd := (X.holds_subst _ _ v).mp (sound v hv)
  have ground := tree.ground (θ.pullback v) hd (real.ground (input _ hd)) _ (O.refl _)
  rw [Context.ground_avoids fixed (θ.pullback_outside v)] at ground
  simpa only [Substitution.eval_apply, Effect.eval_subst, Substitution.pullback] using ground

/-- With an actual residual solution, conditional reconstruction becomes a
valid declarative typing. Unknown residuals must not be reported as accepted
using this theorem: their satisfiability is a separate obligation. -/
theorem Inference.normalized_sound {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {c d r : X.Formula} {g : Context X} {e : Expr}
    {t : T.Term} {eff : Effect}
    (inferred : Inference sig X N c g e t eff d)
    (θ : Substitution T) (fixed : g.Avoids θ.domain) (real : g.Realizable c)
    (sound : X.Entails r (X.subst θ d))
    (hg : g.Admissible X.Satisfiable) (hr : X.Satisfiable r) :
    Typing sig X X.Satisfiable r g e (.mono (θ.apply t)) (eff.subst θ.effects) :=
  Typing.of_ground N hg hr (inferred.normalized_ground_sound θ fixed real sound)

/-- Consume a partial solution under givens. Unknown residuals do not supply
the separate satisfiability premise of the resulting declarative typing. -/
theorem Inference.partial_solution_sound {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {c d : X.Formula} {g : Context X} {e : Expr}
    {t : T.Term} {eff : Effect} {n : X.NormalForm}
    (inferred : Inference sig X N c g e t eff d)
    (solution : n.SoundSolution c d) (fixed : g.Avoids n.substitution.domain)
    (real : g.Realizable c) (hg : g.Admissible X.Satisfiable)
    (sat : X.Satisfiable (X.and c n.residual)) :
    Typing sig X X.Satisfiable (X.and c n.residual) g e
      (.mono (n.substitution.apply t)) (eff.subst n.substitution.effects) :=
  inferred.normalized_sound n.substitution fixed real solution.sound hg sat

/-- A partial solver can produce a sound generalized computation result without
any principal constraint property. The closed-environment hypothesis is only
needed to discharge the outer projected condition to top. -/
theorem Inference.normalized_computation_sound {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {c d r : X.Formula} {g : Context X} {e : Expr}
    {t : T.Term} {eff : Effect}
    (inferred : Inference sig X N c g e t eff d)
    (θ : Substitution T) (fixed : g.Avoids θ.domain) (real : g.Realizable c)
    (sound : X.Entails r (X.subst θ d))
    (hg : g.Admissible X.Satisfiable) (hr : X.Satisfiable r)
    (closed : g.support = Names.empty) :
    ComputationTyping sig X X.Satisfiable X.top g e
      (ComputationScheme.generalize g r (θ.apply t) (eff.subst θ.effects)) := by
  obtain ⟨v, hv⟩ := hr
  exact (inferred.normalized_sound θ fixed real sound hg ⟨v, hv⟩).computation_generalize_closed
    closed ⟨v, hv⟩ ((X.admissible_satisfiable_iff _).mpr ⟨v, (X.holds_top v).mpr trivial⟩)

/-- Projecting local inference names gives symbolic principality: one finite
substitution for each target judgment works at every solution of its constraint.
Only the two result names are quantified in the computation scheme. -/
theorem Typing.principal_computation_at {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (resultName effectName : Nat) {g : Context X} {e : Expr} {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (hg : g.support = Names.empty) (hreal : g.Realizable X.top)
    (typed : Typing sig X X.Satisfiable c g e scheme eff) :
    ∃ d, generateProjected sig X N g e (T.var resultName) (Effect.var effectName) = some d ∧
      Inference sig X N X.top g e (T.var resultName) (Effect.var effectName) d ∧ X.Satisfiable d ∧
      PrincipalComputationScheme sig X X.Satisfiable g e ⟨⟨{resultName}, {effectName}⟩, d, T.var resultName, Effect.var effectName⟩ ∧
      ∀ c' t' eff', Typing sig X X.Satisfiable c' g e (.mono t') eff' →
        (ComputationScheme.mk ⟨{resultName}, {effectName}⟩ d (T.var resultName) (Effect.var effectName)).FiniteInstance c' t' eff' := by
  let bound : Names := ⟨{resultName}, {effectName}⟩
  let outputSubst := Substitution.outputs (T := T) resultName effectName
  have hat (a : T.Term) (eff : Effect) (v : Valuation T.Value) :
      T.eval ((outputSubst a eff).pullback v) (T.var resultName) = T.eval v a := by
    simp [T.eval_var, Substitution.pullback, outputSubst, Substitution.outputs]
  have hae (a : T.Term) (eff : Effect) (v : Valuation T.Value) :
      (Effect.var effectName).eval ((outputSubst a eff).pullback v).effects = eff.eval v.effects := by
    simp [Effect.eval, Effect.var, Substitution.pullback, outputSubst, Substitution.outputs]
  have hcontext (v w : Valuation T.Value) : g.ground v = g.ground w := by
    apply Context.ground_support
    rw [hg]
    constructor <;> intro i hi <;> simp [Names.empty] at hi
  have ground {c' : X.Formula} {t' : T.Term} {eff' : Effect}
      (ht : Typing sig X X.Satisfiable c' g e (.mono t') eff')
      (v : Valuation T.Value) (hc : X.holds c' v) :
      GroundTyping sig O (g.ground ((outputSubst t' eff').pullback v)) e
        (T.eval ((outputSubst t' eff').pullback v) (T.var resultName))
        ((Effect.var effectName).eval ((outputSubst t' eff').pullback v).effects) := by
    obtain ⟨tree, _⟩ := ht
    have h := tree.ground v hc (hreal.ground ((X.holds_top v).mpr trivial)) _ (O.refl _)
    simpa only [hat, hae, hcontext _ v] using h
  obtain ⟨v₀, hv₀⟩ := (X.admissible_satisfiable_iff c).mp typed.root.1
  have contextAdmissible := typed.root.2.1
  obtain ⟨source, _⟩ := typed
  have real := hreal.ground ((X.holds_top v₀).mpr trivial)
  obtain ⟨u, hu⟩ := source.groundInstance_exists v₀ hv₀ real
  let seed : Valuation T.Value := ⟨Function.update v₀.types resultName u,
    Function.update v₀.effects effectName (eff.eval v₀.effects)⟩
  have initial : GroundTyping sig O (g.ground seed) e (T.eval seed (T.var resultName))
      ((Effect.var effectName).eval seed.effects) := by
    rw [hcontext seed v₀]
    simpa [T.eval_var, Effect.eval, Effect.var, seed] using
      source.ground v₀ hv₀ real u hu
  obtain ⟨d, run, hd, cover⟩ := Inference.groundComplete_projected_run N g e (T.var resultName) (Effect.var effectName) ⟨seed, initial⟩
  have inferred := (hd.sound_valid contextAdmissible ⟨seed, cover seed initial⟩).1
  have finite c' t' eff' (ht : Typing sig X X.Satisfiable c' g e (.mono t') eff') :
      (ComputationScheme.mk bound d (T.var resultName) (Effect.var effectName)).FiniteInstance c' t' eff' := by
    refine ⟨outputSubst t' eff', fun _ hi => hi, fun _ hi => hi, ?_⟩
    intro v hv
    exact ⟨cover _ (ground ht v hv), (hat t' eff' v).symm ▸ O.refl _, hae t' eff' v⟩
  have projected (v : Valuation T.Value) : X.holds (X.existsNames bound d) v := by
    let w := v.patch seed bound
    have ht : T.eval w (T.var resultName) = T.eval seed (T.var resultName) := by
      simp [T.eval_var, w, Valuation.patch, bound]
    have he : (Effect.var effectName).eval w.effects = (Effect.var effectName).eval seed.effects := by
      simp [Effect.eval, Effect.var, w, Valuation.patch, bound]
    exact (X.holds_exists _ _ v).mpr ⟨w, v.patch_agreeOutside seed bound,
      cover w (by simpa only [ht, he, hcontext w seed] using initial)⟩
  have fresh : g.Avoids bound := by
    apply g.avoids_of_support_disjoint
    simp [hg, Names.Disjoint, Names.empty]
  have comp : ComputationTyping sig X X.Satisfiable X.top g e
      ⟨bound, d, T.var resultName, Effect.var effectName⟩ :=
    .weaken (.generalize bound fresh
      ((X.admissible_satisfiable_iff _).mpr ⟨seed, projected seed⟩) inferred)
      ((X.admissible_satisfiable_iff _).mpr ⟨seed, (X.holds_top seed).mpr trivial⟩)
      (fun v _ => projected v)
  exact ⟨d, run, hd, ⟨seed, cover seed initial⟩,
    ⟨comp, fun c' t' eff' ht v hv => (finite c' t' eff' ht).ground v hv⟩, finite⟩

theorem Typing.principal_computation_run {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {g : Context X} {e : Expr} {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (hg : g.support = Names.empty) (hreal : g.Realizable X.top)
    (typed : Typing sig X X.Satisfiable c g e scheme eff) :
    ∃ d, generateProjected sig X N g e (T.var 0) (Effect.var 0) = some d ∧
      Inference sig X N X.top g e (T.var 0) (Effect.var 0) d ∧ X.Satisfiable d ∧
      PrincipalComputationScheme sig X X.Satisfiable g e ⟨⟨{0}, {0}⟩, d, T.var 0, Effect.var 0⟩ ∧
      ∀ c' t' eff', Typing sig X X.Satisfiable c' g e (.mono t') eff' →
        (ComputationScheme.mk ⟨{0}, {0}⟩ d (T.var 0) (Effect.var 0)).FiniteInstance c' t' eff' := by
  exact typed.principal_computation_at N 0 0 hg hreal

theorem Typing.principal_computation {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {g : Context X} {e : Expr} {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (hg : g.support = Names.empty) (hreal : g.Realizable X.top)
    (typed : Typing sig X X.Satisfiable c g e scheme eff) :
    ∃ d, Inference sig X N X.top g e (T.var 0) (Effect.var 0) d ∧ X.Satisfiable d ∧
      PrincipalComputationScheme sig X X.Satisfiable g e ⟨⟨{0}, {0}⟩, d, T.var 0, Effect.var 0⟩ ∧
      ∀ c' t' eff', Typing sig X X.Satisfiable c' g e (.mono t') eff' →
        (ComputationScheme.mk ⟨{0}, {0}⟩ d (T.var 0) (Effect.var 0)).FiniteInstance c' t' eff' := by
  obtain ⟨d, _, hd, sat, principal, finite⟩ := typed.principal_computation_run N hg hreal
  exact ⟨d, hd, sat, principal, finite⟩

/-- Same-solved-set monotype coverage extends to qualified targets when
admissibility is stable under finite renaming and satisfiable conjunction.
Both closure hypotheses are explicit; scoped principality does not supply them.
This proof also handles targets derived using existential projection. -/
theorem Typing.instance_of_finite_sameSolved {sig : Signature T} {X : Constraints T O}
    {solved : X.Formula → Prop} {g : Context X} {e : Expr} {result : ComputationScheme X}
    (sound : ∀ c, solved c → X.Satisfiable c)
    (rename : ∀ (p : Renaming) c, X.Admissible solved c →
      X.Admissible solved (X.subst (p.asSubstitution T) c))
    (conjoin : ∀ c d, X.Admissible solved c → X.Admissible solved d →
      X.Satisfiable (X.and c d) → X.Admissible solved (X.and c d))
    (hreal : g.Realizable X.top)
    (finite : ∀ c t eff, Typing sig X solved c g e (.mono t) eff →
      result.FiniteInstance c t eff)
    {c' : X.Formula} {s' : Scheme X} {eff' : Effect}
    (typed' : Typing sig X solved c' g e s' eff') :
    Instance X c' (.qualified result.bound result.condition result.result) s' := by
  let s : Scheme X := .qualified result.bound result.condition result.result
  cases s' with
  | mono t' => exact (finite c' t' eff' typed').instance
  | qualified a q t' =>
    obtain ⟨b, q', u, alpha, fresh⟩ := Scheme.fresh_alpha a q t' ((X.support c').union s.support)
    have hc : X.Avoids c' b := by
      constructor
      · intro i hi hf
        exact Finset.disjoint_left.mp fresh.1 hi
          (Finset.mem_union_left _ (X.freeType_mem_support hf))
      · intro i hi hf
        exact Finset.disjoint_left.mp fresh.2 hi
          (Finset.mem_union_left _ (X.freeEffect_mem_support hf))
    have hs : s.Avoids b := by
      constructor
      · intro i hi hf
        exact Finset.disjoint_left.mp fresh.1 hi
          (Finset.mem_union_right _ (Scheme.freeType_mem_support hf))
      · intro i hi hf
        exact Finset.disjoint_left.mp fresh.2 hi
          (Finset.mem_union_right _ (Scheme.freeEffect_mem_support hf))
    have root := typed'.root
    have renamed := typed'.alpha alpha (alpha.admissible_of_rename rename |>.mp root.2.2)
    have projected : X.Entails c' (X.existsNames b q') := by
      obtain ⟨tree, _⟩ := renamed
      intro v hvc
      obtain ⟨_, w, hw, hq, _⟩ := tree.groundInstance_exists v hvc
        (hreal.ground ((X.holds_top v).mpr trivial))
      exact (X.holds_exists _ _ v).mpr ⟨w, hw, hq⟩
    have joint : X.Satisfiable (X.and c' q') := by
      obtain ⟨v, hv⟩ := (X.admissible_satisfiable_iff _).mp (typed'.to_satisfiable sound).root.1
      obtain ⟨w, hw, hq⟩ := (X.holds_exists _ _ v).mp (projected v hv)
      exact ⟨w, (X.holds_and _ _ w).mpr ⟨(X.holds_agreeOutside hc hw).mpr hv, hq⟩⟩
    have mono : Typing sig X solved (X.and c' q') g e (.mono u) eff' := by
      have inst := (renamed.weaken (conjoin c' q' root.1 renamed.root.2.2 joint)
        (X.entails_left c' q')).forallElim (Substitution.identity T)
        (by simp [Substitution.identity, Names.empty])
        (by simp [Substitution.identity, Names.empty])
        (show X.Entails (X.and c' q') (X.subst (Substitution.identity T) q') from by
          intro v hv
          simpa only [X.holds_subst, Substitution.identity_pullback] using (X.holds_and _ _ v).mp hv |>.2)
      apply inst.sub
      intro v _
      apply (X.holds_le _ _ v).mpr
      simpa only [Substitution.eval_apply, Substitution.identity_pullback] using O.refl (T.eval v u)
    have cover := (finite (X.and c' q') u eff' mono).instance
    have quantified := Instance.forallRight hc hs cover
    have equivalent : X.Equivalent (X.and c' (X.existsNames b q')) c' :=
      ⟨X.entails_left _ _, fun v hv => (X.holds_and _ _ v).mpr ⟨hv, projected v hv⟩⟩
    exact .alphaRight (.symm alpha) (Instance.equivalent equivalent quantified)

/-- Ground soundness gives the empty immediate effect of a value at the
scheme's condition, without any comparison or normalization premise. -/
theorem ComputationTyping.value_effect {sig : Signature T} {X : Constraints T O}
    {solved : X.Formula → Prop} {c : X.Formula} {g : Context X} {e : Expr}
    {result : ComputationScheme X}
    (typed : ComputationTyping sig X solved c g e result)
    (hreal : g.Realizable X.top) (hv : Value e) :
    X.Entails result.condition (X.effectEq result.effect ∅) := by
  induction typed with
  | generalize a fresh hc h =>
    obtain ⟨tree, _⟩ := h
    intro v hvc
    apply (X.holds_effectEq _ _ v).mpr
    exact (tree.ground v hvc (hreal.ground ((X.holds_top v).mpr trivial)) _ (O.refl _)).value_effect hv
  | weaken _ _ _ ih => exact ih hreal hv

/-- Sound value generalization after partial normalization. The syntactic value
restriction is required, and the residual has a separate satisfiability proof.
This statement asserts soundness only, not principality of the chosen solution. -/
theorem Inference.normalized_value_sound {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {c d r : X.Formula} {g : Context X} {e : Expr}
    {t : T.Term} {eff : Effect}
    (inferred : Inference sig X N c g e t eff d)
    (θ : Substitution T) (fixed : g.Avoids θ.domain) (real : g.Realizable X.top)
    (sound : X.Entails r (X.subst θ d))
    (hg : g.Admissible X.Satisfiable) (hr : X.Satisfiable r)
    (closed : g.support = Names.empty) (hv : Value e) :
    let s := ComputationScheme.generalize g r (θ.apply t) (eff.subst θ.effects)
    Typing sig X X.Satisfiable X.top g e (.qualified s.bound s.condition s.result) ∅ := by
  have comp := inferred.normalized_computation_sound θ fixed
    (real.weaken (fun v _ => (X.holds_top v).mpr trivial)) sound hg hr closed
  exact comp.value hv (comp.value_effect real hv)

/-- Principal values compared entirely inside the same solved set. This is a
conditional bridge: renaming and satisfiable-conjunction closure must be proved
for the chosen set, not inserted into a scoped normalizer as new fields. -/
theorem ComputationTyping.principal_value_sameSolved {sig : Signature T} {X : Constraints T O}
    {solved : X.Formula → Prop} {g : Context X} {e : Expr} {result : ComputationScheme X}
    (typed : ComputationTyping sig X solved X.top g e result)
    (sound : ∀ c, solved c → X.Satisfiable c)
    (rename : ∀ (p : Renaming) c, X.Admissible solved c →
      X.Admissible solved (X.subst (p.asSubstitution T) c))
    (conjoin : ∀ c d, X.Admissible solved c → X.Admissible solved d →
      X.Satisfiable (X.and c d) → X.Admissible solved (X.and c d))
    (hreal : g.Realizable X.top) (hv : Value e)
    (finite : ∀ c t eff, Typing sig X solved c g e (.mono t) eff →
      result.FiniteInstance c t eff) :
    PrincipalPair (fun c g e s => Typing sig X solved c g e s ∅)
      g e X.top (.qualified result.bound result.condition result.result) := by
  refine ⟨typed.value hv (typed.value_effect hreal hv), ?_⟩
  intro c s target
  exact ⟨fun v _ => (X.holds_top v).mpr trivial,
    target.instance_of_finite_sameSolved sound rename conjoin hreal finite⟩

/-- A positive check of the same-set bridge with solved forms restricted to
tautologies, over any abstract type domain. All qualified comparison derivations
are covered, including those using projection; no global normalizer is assumed. -/
theorem Typing.tautological_int_principal (sig : Signature T) (X : Constraints T O)
    (n : Int) :
    PrincipalPair (fun c g e s => Typing sig X (fun d => ∀ v, X.holds d v) c g e s ∅)
      [] (.int n) X.top (.qualified Names.empty X.top (T.literal .int)) := by
  let solved := fun d => ∀ v, X.holds d v
  have admissible {c : X.Formula} (hc : X.Admissible solved c) : solved c := by
    obtain ⟨r, hr, _, back⟩ := hc
    exact fun v => back v (hr v)
  have ofTautology {c : X.Formula} (hc : solved c) : X.Admissible solved c :=
    ⟨c, hc, X.entails_refl _, X.entails_refl _⟩
  have top : X.Admissible solved X.top := ofTautology (fun v => (X.holds_top v).mpr trivial)
  have sound c (hc : solved c) : X.Satisfiable c := by
    obtain ⟨v⟩ := T.value_nonempty
    exact ⟨⟨fun _ => v, fun _ => ∅⟩, hc _⟩
  have rename (p : Renaming) c (hc : X.Admissible solved c) :
      X.Admissible solved (X.subst (p.asSubstitution T) c) :=
    ofTautology (fun v => (X.holds_subst _ _ v).mpr (admissible hc _))
  have conjoin c d (hc : X.Admissible solved c) (hd : X.Admissible solved d)
      (_ : X.Satisfiable (X.and c d)) : X.Admissible solved (X.and c d) :=
    ofTautology (fun v => (X.holds_and _ _ v).mpr ⟨admissible hc v, admissible hd v⟩)
  have real : Context.Realizable X.top ([] : Context X) := by intro s hs; cases hs
  have env : Context.Admissible ([] : Context X) solved := by intro s hs; cases hs
  have projected : X.Admissible solved (X.existsNames Names.empty X.top) :=
    ofTautology (fun v => X.exists_intro _ _ v ((X.holds_top v).mpr trivial))
  have initial : Typing sig X solved X.top [] (.int n) (.mono (T.literal .int)) ∅ :=
    ⟨.int n, top, env, trivial, trivial⟩
  let result : ComputationScheme X := ⟨Names.empty, X.top, T.literal .int, ∅⟩
  have typed : ComputationTyping sig X solved X.top [] (.int n) result :=
    .weaken (.generalize Names.empty (by intro s hs; cases hs) projected initial)
      top (X.exists_intro _ _)
  apply typed.principal_value_sameSolved sound rename conjoin real (.int n)
  intro c t eff ht
  refine ⟨Substitution.identity T, by simp [result, Substitution.identity, Names.empty],
    by simp [result, Substitution.identity, Names.empty], ?_⟩
  intro v hv
  obtain ⟨tree, _⟩ := ht
  have ground := tree.ground v hv (real.ground ((X.holds_top v).mpr trivial)) _ (O.refl _)
  obtain ⟨htype, heffect⟩ := ground.int_inv rfl
  simpa [result, Substitution.identity_pullback, T.eval_literal, Effect.eval] using
    And.intro ((X.holds_top v).mpr trivial) (And.intro htype heffect.symm)

/-- Finite coverage of monotypes gives the full principal-pair judgment for
values, including qualified targets. The output retains the chosen solved set;
only comparison derivations are moved to the satisfiability-based system. -/
theorem ComputationTyping.principal_value {sig : Signature T} {X : Constraints T O}
    {solved : X.Formula → Prop} {g : Context X} {e : Expr} {result : ComputationScheme X}
    (typed : ComputationTyping sig X solved X.top g e result)
    (sound : ∀ c, solved c → X.Satisfiable c)
    (hreal : g.Realizable X.top) (hv : Value e)
    (finite : ∀ c t eff, Typing sig X X.Satisfiable c g e (.mono t) eff →
      result.FiniteInstance c t eff) :
    PrincipalPair (fun c g e s => Typing sig X solved c g e s ∅)
      g e X.top (.qualified result.bound result.condition result.result) := by
  refine ⟨typed.value hv (typed.value_effect hreal hv), ?_⟩
  intro c s target
  refine ⟨fun v _ => (X.holds_top v).mpr trivial, ?_⟩
  apply (target.to_satisfiable sound).instance_of_finite_sameSolved
    (fun _ h => h) _ _ hreal finite
  · intro p c hc
    exact (X.admissible_satisfiable_iff _).mpr
      ((X.satisfiable_rename_iff p c).mpr ((X.admissible_satisfiable_iff _).mp hc))
  · intro c d _ _ h
    exact (X.admissible_satisfiable_iff _).mpr h

/-- Every typable value has a principal value scheme, compared with all
valid schemes by the syntactic Instance judgment. -/
theorem Typing.principal_value {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {g : Context X} {e : Expr} {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (hg : g.support = Names.empty) (hreal : g.Realizable X.top) (hv : Value e)
    (typed : Typing sig X X.Satisfiable c g e scheme eff) :
    ∃ s, PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
      g e X.top s := by
  obtain ⟨_, _, _, hp, finite⟩ := typed.principal_computation N hg hreal
  exact ⟨_, hp.1.principal_value (fun _ h => h) hreal hv finite⟩

/-- The constraint-preserving principal route needs no global principal
normalizer or arbitrary-solved-set transformation. This is existence of a
certified generating derivation, not principality of every `Inference` tree. -/
theorem Typing.principal_computation_simplified {sig : Signature T} {X : Constraints T O}
    (N M : X.Simplifier) {g : Context X} {e : Expr} {c : X.Formula}
    {scheme : Scheme X} {eff : Effect}
    (closed : g.support = Names.empty) (real : g.Realizable X.top)
    (typed : Typing sig X X.Satisfiable c g e scheme eff) :
    ∃ d, Inference sig X N X.top g e (T.var 0) (Effect.var 0) d ∧
      X.Satisfiable (M.run d) ∧
      let s : ComputationScheme X := ⟨⟨{0}, {0}⟩, M.run d, T.var 0, Effect.var 0⟩
      PrincipalComputationScheme sig X X.Satisfiable g e s ∧
      (∀ c' t' eff', Typing sig X X.Satisfiable c' g e (.mono t') eff' →
        s.FiniteInstance c' t' eff') ∧
      (Value e → PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
        g e X.top (.qualified s.bound s.condition s.result)) := by
  obtain ⟨d, inferred, sat, principal, finite⟩ := typed.principal_computation N closed real
  have hp := principal.condition_equivalent (M.equivalent d)
  have cover c' t' eff' ht := (finite c' t' eff' ht).condition_equivalent (M.equivalent d)
  exact ⟨d, inferred, X.satisfiable_of_entails (M.equivalent d).2 sat,
    hp, cover, fun hv => hp.1.principal_value (fun _ h => h) real hv cover⟩

/-- A nonidentity output substitution exercises successful reconstruction.
This checks a real generated constraint, not an assumed typing conclusion. -/
theorem Inference.normalized_int_example (sig : Signature T) (X : Constraints T O)
    (n : Int) :
    ComputationTyping sig X X.Satisfiable X.top [] (.int n)
      (ComputationScheme.generalize [] X.top (T.literal .int) ∅) := by
  let θ := Substitution.outputs (T := T) 0 0 (T.literal .int) ∅
  have inferred : Inference sig X (Constraints.Simplifier.identity X) X.top [] (.int n)
      (T.var 0) (Effect.var 0)
      (X.checked X.top X.top (T.literal .int) (T.var 0) ∅ (Effect.var 0)) := .int n
  have sound : X.Entails X.top (X.subst θ
      (X.checked X.top X.top (T.literal .int) (T.var 0) ∅ (Effect.var 0))) := by
    intro v _
    apply (X.holds_subst _ _ v).mpr
    apply (X.holds_checked _ _ _ _ _ _ _).mpr
    refine ⟨(X.holds_top _).mpr trivial, (X.holds_top _).mpr trivial, ?_, ?_⟩
    · simpa [θ, Substitution.outputs, Substitution.pullback, T.eval_var, T.eval_literal]
        using O.refl (T.groundLiteral .int)
    · simp [θ, Substitution.outputs, Substitution.pullback, Effect.eval, Effect.var]
  obtain ⟨base⟩ := T.value_nonempty
  have sat : X.Satisfiable X.top :=
    ⟨⟨fun _ => base, fun _ => ∅⟩, (X.holds_top _).mpr trivial⟩
  have h := inferred.normalized_computation_sound θ (by intro s hs; cases hs)
    (by intro s hs; cases hs) sound (by intro s hs; cases hs) sat rfl
  have he : (Effect.var 0).subst θ.effects = ∅ := by
    simp [θ, Substitution.outputs, Effect.subst, Effect.var]
    rfl
  rw [he] at h
  simpa [θ, Substitution.outputs, Substitution.apply, T.subst_var] using h

end EHMX.HMX
