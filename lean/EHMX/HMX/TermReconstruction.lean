import EHMX.HMX.ScopedNormalization
import EHMX.HMX.ContextSubstitution
import EHMX.HMX.ContextApproximation
import EHMX.HMX.DerivationTransformation
import EHMX.HMX.FreshNormalForms
import EHMX.HMX.AlgorithmCorrectness
import EHMX.HMX.ReconstructionGeneralization

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

/-- Representation failure is deliberately distinct from inconsistency. -/
inductive ReconstructionResult (X : Constraints T O) where
  | reconstructed : X.NormalForm → ReconstructionResult X
  | unrepresented : X.Formula → ReconstructionResult X

def reconstructionScope (X : Constraints T O) (g : Context X)
    (t : T.Term) (eff : Effect) (d : X.Formula) : Names :=
  (Inference.Protected X g t eff).union (X.support d)

theorem reconstructionScope_covers (X : Constraints T O) (g : Context X)
    (t : T.Term) (eff : Effect) (d : X.Formula) :
    (X.freeNames d).Subset (reconstructionScope X g t eff d) := by
  constructor
  · intro i hi
    exact Finset.mem_union_right _ (X.freeType_mem_support ((X.mem_freeNames_types d i).mp hi))
  · intro i hi
    exact Finset.mem_union_right _ (X.freeEffect_mem_support ((X.mem_freeNames_effects d i).mp hi))

/-- Generate once, then reconstruct once. Intermediate lets retain constraints. -/
def inferTermAt (sig : Signature T) (X : Constraints T O) (N : X.Simplifier)
    (P : X.ScopedPrincipalNormalizer) (g : Context X) (e : Expr)
    (t : T.Term) (eff : Effect) : Option (ReconstructionResult X) :=
  (generateProjected sig X N g e t eff).map fun d =>
    match P.normalize (reconstructionScope X g t eff d) d with
    | some n => .reconstructed n
    | none => .unrepresented d

def inferTerm (sig : Signature T) (X : Constraints T O) (N : X.Simplifier)
    (P : X.ScopedPrincipalNormalizer) (g : Context X) (e : Expr) :
    Option (ReconstructionResult X) :=
  inferTermAt sig X N P g e (T.var (g.support.shiftTypes 0))
    (Effect.var (g.support.shiftEffects 0))

def reconstructedScheme (g : Context X) (n : X.NormalForm) : ComputationScheme X :=
  ComputationScheme.generalizeWithSupport (n.substitution.imageSupport g.support) n.residual
    (n.substitution.types (g.support.shiftTypes 0))
    (n.substitution.effects (g.support.shiftEffects 0))

/-- Executable relative to the supplied test; no classical choice is used.
This instance retains constraints and therefore targets `S = Sat_X`. -/
def SatDecider.normalizer {X : Constraints T O} (D : SatDecider X) : X.ScopedPrincipalNormalizer where
  solved := X.Satisfiable
  solved_satisfiable := fun _ h => h
  normalize := fun _ d => if D.decide d then some ⟨d, Substitution.identity T⟩ else none
  principal := by
    intro u d _ n run
    split at run
    · cases Option.some.inj run
      refine ⟨⟨(D.correct d).mp ‹D.decide d = true›, Substitution.identity_solved T, ?_, ?_⟩, ?_⟩
      · constructor <;> intro v hv <;>
          simpa only [X.holds_subst, Substitution.identity_pullback] using hv
      · exact X.entails_left _ _
      · intro m hm
        refine ⟨m.substitution, ?_, Constraints.NormalForm.reconstruct_entails X hm⟩
        intro v
        rw [Substitution.identity_pullback]
        exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    · contradiction
  failure := by
    intro u d _
    constructor
    · intro run ⟨n, hn⟩
      obtain ⟨v, hv⟩ := hn.1
      have sat : X.Satisfiable d := ⟨n.substitution.pullback v,
        (X.holds_subst _ _ _).mp (Constraints.NormalForm.reconstruct_entails X hn v hv)⟩
      simp [(D.correct d).mpr sat] at run
    · intro hn
      have noSat : ¬ X.Satisfiable d := by
        intro hd
        apply hn
        refine ⟨⟨d, Substitution.identity T⟩, hd, Substitution.identity_solved T, ⟨?_, ?_⟩,
          X.entails_left _ _⟩ <;> intro v hv <;>
          simpa only [X.holds_subst, Substitution.identity_pullback] using hv
      have noTest : D.decide d ≠ true := fun h => noSat ((D.correct d).mp h)
      simp [noTest]

theorem SatDecider.inferTerm_complete {sig : Signature T} {X : Constraints T O}
    (D : SatDecider X) (N : X.Simplifier) {c : X.Formula} {g : Context X}
    {e : Expr} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e s eff) (real : g.Realizable c) :
    ∃ n, inferTerm sig X N D.normalizer g e = some (.reconstructed n) := by
  obtain ⟨d, generated, sat, _⟩ := typed.inference_complete_scheme N real
  exact ⟨⟨d, Substitution.identity T⟩,
    by simp [inferTerm, inferTermAt, generated, normalizer, (D.correct d).mpr sat]⟩

theorem inferTermAt_normal {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {P : X.ScopedPrincipalNormalizer} {g : Context X}
    {e : Expr} {t : T.Term} {eff : Effect} {n : X.NormalForm}
    (run : inferTermAt sig X N P g e t eff = some (.reconstructed n)) :
    ∃ d, generateProjected sig X N g e t eff = some d ∧
      P.normalize (reconstructionScope X g t eff d) d = some n ∧
      n.IsPrincipalOn (reconstructionScope X g t eff d) P.solved d := by
  obtain ⟨d, generated, h⟩ := Option.map_eq_some_iff.mp run
  split at h
  · cases ReconstructionResult.reconstructed.inj h
    exact ⟨d, generated, ‹_ = some _›,
      P.principal _ _ (reconstructionScope_covers X g t eff d) _ ‹_ = some _›⟩
  · contradiction

theorem inferTermAt_unrepresented {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {P : X.ScopedPrincipalNormalizer} {g : Context X}
    {e : Expr} {t : T.Term} {eff : Effect} {d : X.Formula}
    (run : inferTermAt sig X N P g e t eff = some (.unrepresented d)) :
    generateProjected sig X N g e t eff = some d ∧
      ¬ ∃ n : X.NormalForm, n.IsNormal P.solved d := by
  obtain ⟨d', generated, h⟩ := Option.map_eq_some_iff.mp run
  split at h
  · contradiction
  · cases ReconstructionResult.unrepresented.inj h
    exact ⟨generated, (P.failure _ _ (reconstructionScope_covers X g t eff _)).mp ‹_ = none›⟩

/-- Constraint-form soundness in the actual capture-avoiding substituted
environment. This does not assert internal validity for `P.solved`. -/
theorem inferTermAt_sound_constraint {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer) (hsig : sig.Closed)
    {g : Context X} {e : Expr} {t : T.Term} {eff : Effect} {n : X.NormalForm}
    (run : inferTermAt sig X N P g e t eff = some (.reconstructed n))
    (real : g.Realizable X.top) :
    Typing sig X X.Satisfiable n.residual (g.subst n.substitution) e
      (.mono (n.substitution.apply t)) (eff.subst n.substitution.effects) := by
  obtain ⟨d, generated, normalized, _⟩ := inferTermAt_normal run
  obtain ⟨_, sat, entails⟩ := P.sound (reconstructionScope_covers X g t eff d) normalized
  have topSat : X.Satisfiable (X.subst n.substitution X.top) := by
    obtain ⟨v, _⟩ := sat
    exact ⟨v, (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial)⟩
  apply Typing.of_ground N (real.admissible_subst _ topSat) sat
  intro v hv
  have ground := (generateProjected_ground_iff N hsig generated _
    (real.ground ((X.holds_top _).mpr trivial))).mp ((X.holds_subst _ _ _).mp (entails v hv))
  simpa only [Context.ground_subst, Substitution.eval_apply, Effect.eval_subst,
    Substitution.pullback] using ground

/-- A typed substituted input produces a uniformly solving substitution for
the actual generated constraint, including handler clauses. -/
theorem generateProjected_entails_subst {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) {g : Context X} {e : Expr} {t : T.Term} {eff : Effect}
    (σ : Substitution T) {c : X.Formula}
    (real : (g.subst σ).Realizable c)
    (typed : Typing sig X X.Satisfiable c (g.subst σ) e
      (.mono (σ.apply t)) (eff.subst σ.effects)) :
    ∃ d, generateProjected sig X N g e t eff = some d ∧ X.Entails c (X.subst σ d) := by
  have ground (v : Valuation T.Value) (hv : X.holds c v) :
      GroundTyping sig O (g.ground (σ.pullback v)) e
        (T.eval (σ.pullback v) t) (eff.eval (σ.pullback v).effects) := by
    obtain ⟨tree, _⟩ := typed
    simpa only [Context.ground_subst, Substitution.eval_apply, Effect.eval_subst,
      Substitution.pullback] using tree.ground v hv (real.ground hv) _ (O.refl _)
  obtain ⟨v, hv⟩ := (X.admissible_satisfiable_iff c).mp typed.root.1
  obtain ⟨d, generated, _, cover⟩ := Inference.groundComplete_projected_run N g e t eff
    ⟨_, ground v hv⟩
  exact ⟨d, generated, fun v hv => (X.holds_subst _ _ _).mpr (cover _ (ground v hv))⟩

/-- An explicit competing normal form supplies success and a uniform factor.
Solvedness and residual invariance are obligations, not consequences of a
generic finite substitution or of pointwise satisfiability. -/
theorem inferTermAt_complete_of_competitor {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    {g : Context X} {e : Expr} {t : T.Term} {eff : Effect}
    (σ : Substitution T) (solved : σ.Solved) {c : X.Formula}
    (admissible : X.Admissible P.solved c)
    (invariant : X.Equivalent (X.subst σ c) c)
    (real : (g.subst σ).Realizable c)
    (typed : Typing sig X P.solved c (g.subst σ) e
      (.mono (σ.apply t)) (eff.subst σ.effects)) :
    ∃ n, inferTermAt sig X N P g e t eff = some (.reconstructed n) ∧
      ∃ φ : Substitution T,
        (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v)
          (Inference.Protected X g t eff)) ∧
        X.Entails c (X.subst φ n.residual) := by
  obtain ⟨d, generated, entails⟩ := generateProjected_entails_subst N σ real
    (typed.to_satisfiable P.solved_satisfiable)
  obtain ⟨r, hr, forward, backward⟩ := admissible
  let m : X.NormalForm := ⟨r, σ⟩
  have normal : m.IsNormal P.solved d := by
    refine ⟨hr, solved, ⟨?_, ?_⟩, ?_⟩
    · intro v hv
      exact forward v (invariant.1 v ((X.holds_subst _ _ _).mpr
        (backward _ ((X.holds_subst _ _ _).mp hv))))
    · intro v hv
      exact (X.holds_subst _ _ _).mpr
        (forward _ ((X.holds_subst _ _ _).mp (invariant.2 v (backward v hv))))
    · intro v hv
      obtain ⟨hR, graph⟩ := (X.holds_and _ _ _).mp hv
      have hd := (X.holds_subst _ _ _).mp (entails v (backward v hR))
      rwa [X.substitutionConstraint_fixed σ v graph] at hd
  obtain ⟨n, run, φ, factor, residual⟩ :=
    P.complete_of_competitor (reconstructionScope_covers X g t eff d) m normal
  refine ⟨n, by simp [inferTermAt, generated, run], φ, ?_, X.entails_trans forward residual⟩
  intro v
  exact (factor v).mono (Names.subset_union_left _ _)

/-- Monomorphic reconstruction completeness with the actual substituted
environment. Freshening constructs the competitor; neither solvedness nor
invariance is imposed on the target substitution. This is not yet the
qualified-type comparison of dissertation Theorem 17. -/
theorem inferTermAt_complete_mono {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (rename : ∀ (p : Renaming) c, X.Admissible P.solved c →
      X.Admissible P.solved (X.subst (p.asSubstitution T) c))
    {g : Context X} {e : Expr} {t : T.Term} {eff : Effect}
    (σ : Substitution T) {c : X.Formula}
    (real : (g.subst σ).Realizable c)
    (typed : Typing sig X P.solved c (g.subst σ) e
      (.mono (σ.apply t)) (eff.subst σ.effects)) :
    ∃ n, inferTermAt sig X N P g e t eff = some (.reconstructed n) ∧
      ∃ φ : Substitution T,
        (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v)
          (Inference.Protected X g t eff)) ∧
        X.Entails c (X.subst φ n.residual) := by
  obtain ⟨d, generated, entails⟩ := generateProjected_entails_subst N σ real
    (typed.to_satisfiable P.solved_satisfiable)
  obtain ⟨n, run, φ, factor, residual⟩ := P.complete_of_substitution rename
    (reconstructionScope_covers X g t eff d) σ typed.root.1 entails
  exact ⟨n, by simp [inferTermAt, generated, run], φ,
    fun v => (factor v).mono (Names.subset_union_left _ _), residual⟩

/-- The factor simultaneously transports the environment, result, and effect. -/
theorem reconstruction_factor {X : Constraints T O}
    {g : Context X} {t : T.Term} {eff : Effect} {ψ φ σ : Substitution T}
    (factor : ∀ v, (ψ.pullback (φ.pullback v)).AgreeOn (σ.pullback v)
      (Inference.Protected X g t eff)) (v : Valuation T.Value) :
    (g.subst ψ).ground (φ.pullback v) = (g.subst σ).ground v ∧
      T.eval (φ.pullback v) (ψ.apply t) = T.eval v (σ.apply t) ∧
      (eff.subst ψ.effects).eval (φ.pullback v).effects = (eff.subst σ.effects).eval v.effects := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Context.ground_subst]
    exact Context.ground_support ((factor v).mono (Inference.Protected.context g t eff))
  · simp only [Substitution.eval_apply]
    exact T.eval_support _ _ t ((factor v).mono (Inference.Protected.type g t eff))
  · simp only [Effect.eval_subst]
    exact Effect.eval_support eff _ _ (fun i hi => (factor v).2 i (Inference.Protected.effect g t eff hi))

/-- Instantiate a target scheme under a consistent, admissible strengthening.
Only the assumption environment, not the target scheme, must be realizable at C.
Alpha conversion prevents the target binder from capturing C. -/
theorem Typing.mono_strengthening {sig : Signature T} {X : Constraints T O}
    {S : X.Formula → Prop} (sound : ∀ c, S c → X.Satisfiable c)
    (closure : X.SolvedClosure S) {c : X.Formula} {g : Context X}
    {e : Expr} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X S c g e s eff) (real : g.Realizable c) :
    ∃ d t, X.Entails d c ∧ Typing sig X S d g e (.mono t) eff ∧ g.Realizable d := by
  cases s with
  | mono t => exact ⟨c, t, X.entails_refl _, typed, real⟩
  | qualified a q t =>
    obtain ⟨b, r, u, alpha, fresh⟩ := Scheme.fresh_alpha a q t (X.support c)
    have adm := (Scheme.AlphaEquivalent.admissible_of_rename closure.rename alpha).mp typed.root.2.2
    have renamed := typed.alpha alpha adm
    obtain ⟨v, hv⟩ := (typed.to_satisfiable sound).root.1 |> (X.admissible_satisfiable_iff _).mp
    obtain ⟨tree, valid⟩ := renamed
    have renamed : Typing sig X S c g e (.qualified b r u) eff := ⟨tree, valid⟩
    obtain ⟨value, w, hw, hr, _⟩ := tree.groundInstance_exists v hv (real.ground hv)
    have outside : X.Avoids c b :=
      ⟨fun i hi hf => Finset.disjoint_left.mp fresh.1 hi (X.freeType_mem_support hf),
       fun i hi hf => Finset.disjoint_left.mp fresh.2 hi (X.freeEffect_mem_support hf)⟩
    have sat : X.Satisfiable (X.and c r) :=
      ⟨w, (X.holds_and _ _ _).mpr ⟨(X.holds_agreeOutside outside hw).mpr hv, hr⟩⟩
    have hc := closure.conjoin c r typed.root.1 adm sat
    have inst : Instance X (X.and c r) (.qualified b r u) (.mono u) := by
      apply Instance.forallLeft (Substitution.identity T)
        (by simp [Substitution.identity, Names.empty]) (by simp [Substitution.identity, Names.empty])
      · intro v hv
        simpa only [X.holds_subst, Substitution.identity_pullback] using (X.holds_and _ _ _).mp hv |>.2
      · apply Instance.sub
        intro v _
        exact (X.holds_le _ _ _).mpr (by simpa [Substitution.eval_apply,
          Substitution.identity_pullback] using O.refl (T.eval v u))
    exact ⟨X.and c r, u, X.entails_left _ _,
      (renamed.weaken hc (X.entails_left _ _)).instance_mono inst, real.weaken (X.entails_left _ _)⟩

private def Substitution.withOutputs (σ : Substitution T) (a b : Nat)
    (t : T.Term) (eff : Effect) : Substitution T where
  domain := σ.domain.union ⟨{a}, {b}⟩
  types := fun i => if i = a then t else σ.types i
  effects := fun i => if i = b then eff else σ.effects i
  types_outside := by intro i hi; simp only [Names.union, Finset.mem_union,
    Finset.mem_singleton, not_or] at hi; simp [hi.2, σ.types_outside i hi.1]
  effects_outside := by intro i hi; simp only [Names.union, Finset.mem_union,
    Finset.mem_singleton, not_or] at hi; simp [hi.2, σ.effects_outside i hi.1]

/-- Completeness at the actual fresh output slots. A single factor preserves
the original environment and the target type and immediate effect. -/
theorem inferTerm_complete_mono {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (closure : X.SolvedClosure P.solved) {g : Context X} {e : Expr}
    (σ : Substitution T) {c : X.Formula} {t : T.Term} {eff : Effect}
    (typed : Typing sig X P.solved c (g.subst σ) e (.mono t) eff)
    (real : (g.subst σ).Realizable c) :
    ∃ n, inferTerm sig X N P g e = some (.reconstructed n) ∧
      ∃ φ : Substitution T,
        (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) g.support) ∧
        X.Entails c (X.subst φ n.residual) ∧
        ∀ v, T.eval (φ.pullback v) (reconstructedScheme g n).result = T.eval v t ∧
          (reconstructedScheme g n).effect.eval (φ.pullback v).effects = eff.eval v.effects := by
  let a := g.support.shiftTypes 0
  let b := g.support.shiftEffects 0
  let θ := σ.withOutputs a b t eff
  have same (v : Valuation T.Value) : (θ.pullback v).AgreeOn (σ.pullback v) g.support := by
    have fresh := g.output_names_fresh
    constructor
    · intro i hi
      have ha : i ≠ a := by intro h; apply fresh.1; simpa only [h, a] using hi
      simp [θ, Substitution.withOutputs, Substitution.pullback, ha]
    · intro i hi
      have hb : i ≠ b := by intro h; apply fresh.2; simpa only [h, b] using hi
      simp [θ, Substitution.withOutputs, Substitution.pullback, hb]
  have ground (v : Valuation T.Value) (hv : X.holds c v) :
      GroundTyping sig O (g.ground (θ.pullback v)) e
        (T.eval (θ.pullback v) (T.var a)) ((Effect.var b).eval (θ.pullback v).effects) := by
    obtain ⟨tree, _⟩ := typed
    have ht := tree.ground v hv (real.ground hv) _ (O.refl _)
    rw [Context.ground_subst, ← Context.ground_support (same v)] at ht
    simpa [θ, Substitution.pullback, Substitution.withOutputs, T.eval_var, Effect.eval, Effect.var] using ht
  obtain ⟨v, hv⟩ := (X.admissible_satisfiable_iff c).mp (typed.to_satisfiable P.solved_satisfiable).root.1
  obtain ⟨d, generated, _, cover⟩ := Inference.groundComplete_projected_run N g e (T.var a) (Effect.var b)
    ⟨_, ground v hv⟩
  have entails : X.Entails c (X.subst θ d) := fun v hv =>
    (X.holds_subst _ _ _).mpr (cover _ (ground v hv))
  obtain ⟨n, run, φ, factor, residual⟩ := P.complete_of_substitution closure.rename
    (reconstructionScope_covers X g (T.var a) (Effect.var b) d) θ typed.root.1 entails
  refine ⟨n, by simp [inferTerm, inferTermAt, a, b, generated, run], φ, ?_, residual, ?_⟩
  · intro v
    exact ((factor v).mono
      ((Inference.Protected.context g (T.var a) (Effect.var b)).trans
        (Names.subset_union_left _ _))).trans (same v)
  · intro v
    have ha := (factor v).1 a
      (Finset.mem_union_left _ ((Inference.Protected.type g (T.var a) (Effect.var b)).1
        (by simp [T.support_var])))
    have hb := (factor v).2 b
      (Finset.mem_union_left _ (Inference.Protected.effect g (T.var a) (Effect.var b)
        (by simp [Effect.var])))
    exact ⟨by simpa [a, θ, Substitution.withOutputs, Substitution.pullback,
        reconstructedScheme, ComputationScheme.generalizeWithSupport] using ha,
      by simpa [b, θ, Substitution.withOutputs, Substitution.pullback,
        reconstructedScheme, ComputationScheme.generalizeWithSupport] using hb⟩


/-- Acceptance for arbitrary qualified target judgments, including open
environments and handlers. The comparison is proved separately. -/
theorem inferTerm_complete_acceptance {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (closure : X.SolvedClosure P.solved) {g : Context X} {e : Expr}
    (σ : Substitution T) {c : X.Formula} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X P.solved c (g.subst σ) e s eff)
    (real : (g.subst σ).Realizable c) :
    ∃ n, inferTerm sig X N P g e = some (.reconstructed n) := by
  obtain ⟨c', t, _, mono, real'⟩ := typed.mono_strengthening P.solved_satisfiable closure real
  obtain ⟨n, run, _⟩ := inferTerm_complete_mono N P closure σ mono real'
  exact ⟨n, run⟩

end EHMX.HMX
