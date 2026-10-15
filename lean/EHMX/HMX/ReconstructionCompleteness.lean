import EHMX.HMX.ReconstructionSoundness
import EHMX.HMX.PreparedNormalization

/-! Theorem 17: one finite factor compares the environment, the qualified
reconstruction result, and its outer constraint. A factor is repaired under the target constraint using variable-equality
reflection and the prepared output shape, to prevent bound names from escaping. -/
set_option maxHeartbeats 2000000

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

theorem ComputationScheme.outer_of_typing_instance
    {sig : Signature T} {S : X.Formula → Prop}
    {c : X.Formula} {g : Context X} {e : Expr} {target : Scheme X} {eff : Effect}
    {result : ComputationScheme X} (φ : Substitution T)
    (typed : Typing sig X S c g e target eff) (real : g.Realizable c)
    (comparison : Instance X c (result.valueScheme.subst φ) target) :
    X.Entails c (X.subst φ result.outer) := by
  intro v hv
  obtain ⟨tree, _⟩ := typed
  obtain ⟨t, ht⟩ := tree.groundInstance_exists v hv (real.ground hv)
  have hs := (Scheme.groundInstance_subst φ result.valueScheme v t).mp
    (comparison.groundInstance hv ht)
  obtain ⟨w, hw, hr, _⟩ := hs
  exact (X.holds_subst _ _ _).mpr ((X.holds_exists _ _ _).mpr ⟨w, hw, hr⟩)

private theorem qualified_of_mono
    {c q : X.Formula} {b : Names} {t : T.Term} {source : Scheme X}
    (freshC : X.Avoids c b) (freshSource : source.Avoids b)
    (projected : X.Entails c (X.existsNames b q))
    (mono : Instance X (X.and c q) source (.mono t)) :
    Instance X c source (.qualified b q t) := by
  exact (Instance.forallRight freshC freshSource mono).weaken
    (fun v hv => (X.holds_and _ _ _).mpr ⟨hv, projected v hv⟩)

theorem ComputationScheme.instance_of_factor
    (φ : Substitution T) {c : X.Formula} {result : ComputationScheme X} {t : T.Term}
    (residual : X.Entails c (X.subst φ result.condition))
    (resultType : X.Entails c (X.le (φ.apply result.result) t)) :
    Instance X c (result.valueScheme.subst φ) (.mono t) := by
  exact (Instance.subst_qualified_mono_iff φ).mpr
    ⟨φ, fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩, residual, resultType⟩


/-- Generalization of a reconstructed monomorphic judgment stays in the same
solved set. Freshness uses images of the original environment's support. -/
theorem Typing.reconstructed_computation {sig : Signature T}
    {S : X.Formula → Prop} (closure : X.SolvedClosure S)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (typed : Typing sig X S n.residual (g.subst n.substitution) e
      (.mono (reconstructedScheme g n).result) (reconstructedScheme g n).effect) :
    ComputationTyping sig X S (reconstructedScheme g n).outer
      (g.subst n.substitution) e (reconstructedScheme g n) :=
  .generalize _ (ComputationScheme.generalizeWithSupport_avoids _ _ _ _ _)
    (closure.project _ _ typed.root.1) typed

end EHMX.HMX
namespace EHMX.HMX
open EHMX EHMX.HMX EHMX.HMX.ReconstructionFactor
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
theorem pullback_outside_on (σ : HMX.Substitution equalityTypes) (u b : Names)
 (fresh : b.Disjoint (σ.imageSupport u)) {v w : Valuation GroundTy}
 (same : v.AgreeOutside w b) : (σ.pullback v).AgreeOn (σ.pullback w) u := by
 constructor
 · intro i hi
   apply equalityTypes.eval_support
   have h := fresh.mono_right (σ.imageSupport_type hi)
   exact ⟨fun j hj => same.1 j (fun hb => Finset.disjoint_left.mp h.1 hb hj),
     fun j hj => same.2 j (fun hb => Finset.disjoint_left.mp h.2 hb hj)⟩
 · intro i hi
   apply Effect.eval_support
   intro j hj
   exact same.2 j (fun hb => Finset.disjoint_left.mp fresh.2 hb
     (σ.imageSupport_effect hi hj))
theorem project_factor {c q : X.Formula} {b u : Names}
 (ψ ρ σ : HMX.Substitution equalityTypes)
 (freshC : X.Avoids c b) (fresh : b.Disjoint (σ.imageSupport u))
 (support : (ρ.imageSupport (ψ.imageSupport u)).Subset (σ.imageSupport u))
 (projected : X.Entails c (X.existsNames b q))
 (factor : ∀ v, X.holds (X.and c q) v →
   (ψ.pullback (ρ.pullback v)).AgreeOn (σ.pullback v) u) :
 ∀ v, X.holds c v →
   (ψ.pullback (ρ.pullback v)).AgreeOn (σ.pullback v) u := by
 intro v hv
 obtain ⟨w, hw, hq⟩ := (X.holds_exists _ _ _).mp (projected v hv)
 have hc := (X.holds_agreeOutside freshC hw).mpr hv
 have h := factor w ((X.holds_and _ _ _).mpr ⟨hc, hq⟩)
 have hf : b.Disjoint ((ρ.compose ψ).imageSupport u) := by
   rw [← ReconstructionSupport.imageSupport_compose]
   exact fresh.mono_right support
 have lhs := pullback_outside_on (ρ.compose ψ) u b hf hw
 simp only [HMX.Substitution.compose_pullback] at lhs
 have rhs := pullback_outside_on σ u b fresh hw
 exact ⟨fun i hi => (lhs.1 i hi).symm.trans ((h.1 i hi).trans (rhs.1 i hi)),
   fun i hi => (lhs.2 i hi).symm.trans ((h.2 i hi).trans (rhs.2 i hi))⟩
theorem inferTerm_complete_scheme
    {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
    {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (closure : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (shape : ∀ u d n, P.normalize u d = some n →
      (∀ i, EHMX.HMX.ReconstructionFactor.VariableEffects (n.substitution.types i)) ∧ n.substitution.effects = Effect.var)
    {g : Context X} {e : Expr}
    (σ : Substitution equalityTypes) {c : X.Formula} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X P.solved c (g.subst σ) e s eff)
    (real : (g.subst σ).Realizable c) :
    ∃ n, inferTerm sig X N P g e = some (.reconstructed n) ∧
      ∃ φ : Substitution equalityTypes,
        (∀ v, X.holds c v → (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) g.support) ∧
        Instance X c ((reconstructedScheme g n).valueScheme.subst φ) s ∧
        X.Entails c (X.subst φ (reconstructedScheme g n).outer) ∧
        ∀ v, X.holds c v → (reconstructedScheme g n).effect.eval (φ.pullback v).effects = eff.eval v.effects := by
  have comparison :
      ∃ n, inferTerm sig X N P g e = some (.reconstructed n) ∧
        ∃ φ : Substitution equalityTypes,
          (∀ v, X.holds c v → (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) g.support) ∧
          Instance X c ((reconstructedScheme g n).valueScheme.subst φ) s ∧
          ∀ v, X.holds c v → (reconstructedScheme g n).effect.eval (φ.pullback v).effects = eff.eval v.effects := by
    cases s with
    | mono t =>
        obtain ⟨n, run, φ, factor, residual, images⟩ :=
          inferTerm_complete_mono N P closure σ typed real
        refine ⟨n, run, φ, factor, ?_, fun v hv => (images v hv).2⟩
        apply ComputationScheme.instance_of_factor φ residual
        intro v hv
        apply (X.holds_le _ _ _).mpr
        rw [Substitution.eval_apply, (images v hv).1]
        exact O.refl _
    | qualified a q t =>
        obtain ⟨b, r, u, alpha, fresh⟩ := Scheme.fresh_alpha a q t
          ((X.support c).union ((g.support.union σ.range).union ⟨∅, eff.vars⟩))
        have freshC : X.Avoids c b :=
          ⟨fun i hi hf => Finset.disjoint_left.mp fresh.1 hi
            (Finset.mem_union_left _ (X.freeType_mem_support hf)),
           fun i hi hf => Finset.disjoint_left.mp fresh.2 hi
            (Finset.mem_union_left _ (X.freeEffect_mem_support hf))⟩
        have freshG : b.Disjoint ((g.support.union σ.range).union ⟨∅, eff.vars⟩) :=
          fresh.mono_right (Names.subset_union_right _ _)
        have adm := (alpha.admissible_of_rename closure.rename).mp typed.root.2.2
        have renamed := typed.alpha alpha adm
        have projected : X.Entails c (X.existsNames b r) := by
          obtain ⟨tree, _⟩ := renamed
          intro v hv
          obtain ⟨_, w, hw, hr, _⟩ := tree.groundInstance_exists v hv (real.ground hv)
          exact (X.holds_exists _ _ _).mpr ⟨w, hw, hr⟩
        have joint : X.Satisfiable (X.and c r) := by
          obtain ⟨v, hv⟩ := (X.admissible_satisfiable_iff _).mp
            (typed.to_satisfiable P.solved_satisfiable).root.1
          obtain ⟨w, hw, hr⟩ := (X.holds_exists _ _ _).mp (projected v hv)
          exact ⟨w, (X.holds_and _ _ _).mpr
            ⟨(X.holds_agreeOutside freshC hw).mpr hv, hr⟩⟩
        have mono : Typing sig X P.solved (X.and c r) (g.subst σ) e (.mono u) eff := by
          have inst := (renamed.weaken (closure.conjoin _ _ typed.root.1 adm joint)
            (X.entails_left _ _)).forallElim (Substitution.identity equalityTypes)
            (by simp [Substitution.identity, Names.empty])
            (by simp [Substitution.identity, Names.empty])
            (show X.Entails (X.and c r) (X.subst (Substitution.identity equalityTypes) r) from by
              intro v hv
              simpa only [X.holds_subst, Substitution.identity_pullback] using
                ((X.holds_and _ _ _).mp hv).2)
          apply inst.sub
          intro v hv
          apply (X.holds_le _ _ _).mpr
          simpa only [Substitution.identity_apply] using
            O.refl (equalityTypes.eval v u)
        obtain ⟨n, run, φ, factor, residual, images⟩ :=
          inferTerm_complete_mono N P closure σ mono (real.weaken (X.entails_left _ _))

        let ai := g.support.shiftTypes 0
        let ei := g.support.shiftEffects 0
        let observed := g.support.union ⟨∅, {ei}⟩
        let θ := Substitution.withOutputs σ ai ei u eff
        have sameθ (v : Valuation GroundTy) :
            (θ.pullback v).AgreeOn (σ.pullback v) g.support := by
          have fresh := g.output_names_fresh
          constructor
          · intro i hi
            have ne : i ≠ ai := by intro h; apply fresh.1; simpa [h, ai] using hi
            simp [θ, Substitution.withOutputs, Substitution.pullback, ne]
          · intro i hi
            have ne : i ≠ ei := by intro h; apply fresh.2; simpa [h, ei] using hi
            simp [θ, Substitution.withOutputs, Substitution.pullback, ne]
        have extended (v : Valuation GroundTy) (hv : X.holds (X.and c r) v) :
            (n.substitution.pullback (φ.pullback v)).AgreeOn (θ.pullback v) observed := by
          constructor
          · intro i hi
            have hi' : i ∈ g.support.types := by simpa [observed, Names.union, or_comm] using hi
            exact ((factor v hv).1 i hi').trans ((sameθ v).1 i hi').symm
          · intro i hi
            have hi' : i ∈ g.support.effects ∨ i = ei := by
              simpa [observed, Names.union, or_comm] using hi
            rcases hi' with hi' | rfl
            · exact ((factor v hv).2 i hi').trans ((sameθ v).2 i hi').symm
            · simpa [θ, Substitution.withOutputs, Substitution.pullback, ei,
                reconstructedScheme, ComputationScheme.generalizeWithSupport] using (images v hv).2
        have targetSupport : (θ.imageSupport observed).Subset
            ((g.support.union σ.range).union ⟨∅, eff.vars⟩) := by
          constructor
          · intro j hj
            obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
            have hi' : i ∈ g.support.types := by simpa [observed, Names.union, or_comm] using hi
            have ne : i ≠ ai := by intro h; apply g.output_names_fresh.1; simpa [h, ai] using hi'
            have hj' : j ∈ (equalityTypes.support (σ.types i)).types := by
              simpa [θ, Substitution.withOutputs, ne] using hj
            exact Finset.mem_union_left _ ((σ.type_support_subset g.support hi').1 hj')
          · intro j hj
            rcases Finset.mem_union.mp hj with hj | hj
            · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
              have hi' : i ∈ g.support.types := by simpa [observed, Names.union, or_comm] using hi
              have ne : i ≠ ai := by intro h; apply g.output_names_fresh.1; simpa [h, ai] using hi'
              have hj' : j ∈ (equalityTypes.support (σ.types i)).effects := by
                simpa [θ, Substitution.withOutputs, ne] using hj
              exact Finset.mem_union_left _ ((σ.type_support_subset g.support hi').2 hj')
            · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
              have hi' : i ∈ g.support.effects ∨ i = ei := by
                simpa [observed, Names.union, or_comm] using hi
              by_cases ne : i = ei
              · subst i
                exact Finset.mem_union_right _ (by simpa [θ, Substitution.withOutputs] using hj)
              · have hi'' : i ∈ g.support.effects := hi'.resolve_right ne
                have hj' : j ∈ (σ.effects i).vars := by simpa [θ, Substitution.withOutputs, ne] using hj
                exact Finset.mem_union_left _ (σ.effect_support_subset g.support hi'' hj')
        obtain ⟨d, _, normalized, _⟩ := inferTermAt_normal run
        have shape := shape _ _ n normalized
        obtain ⟨ρ, support, same⟩ := EHMX.HMX.ReconstructionFactor.repair_factor joint (reflect _ mono.root.1)
          n.substitution φ θ observed (fun i _ => shape.1 i)
          (fun i _ => congrFun shape.2 i) extended
        have freshθ : b.Disjoint (θ.imageSupport observed) := freshG.mono_right targetSupport
        have factorρ (v : Valuation GroundTy) (hv : X.holds (X.and c r) v) :
            (n.substitution.pullback (ρ.pullback v)).AgreeOn (θ.pullback v) observed := by
          rw [same v hv]
          exact extended v hv
        have factorC := project_factor n.substitution ρ θ freshC freshθ support projected factorρ
        have freshSource : ((reconstructedScheme g n).valueScheme.subst ρ).Avoids b := by
          apply Scheme.subst_avoids_imageSupport
          apply freshθ.mono_right
          apply Names.Subset.trans _ support
          apply ρ.imageSupport_mono
          exact (ComputationScheme.generalizeWithSupport_support _ _ _ _).trans
            (n.substitution.imageSupport_mono (Names.subset_union_left _ _))
        have monoComparison : Instance X (X.and c r)
            ((reconstructedScheme g n).valueScheme.subst ρ) (.mono u) := by
          apply ComputationScheme.instance_of_factor ρ
          · intro v hv
            apply (X.holds_subst _ _ _).mpr
            rw [same v hv]
            exact (X.holds_subst _ _ _).mp (residual v hv)
          · intro v hv
            apply (X.holds_le _ _ _).mpr
            rw [Substitution.eval_apply, same v hv, (images v hv).1]
            exact O.refl _
        have inst : Instance X c ((reconstructedScheme g n).valueScheme.subst ρ)
            (.qualified b r u) :=
          (Instance.forallRight freshC freshSource monoComparison).weaken
            (fun v hv => (X.holds_and _ _ _).mpr ⟨hv, projected v hv⟩)
        refine ⟨n, run, ρ, ?_, .alphaRight (.symm alpha) inst, ?_⟩
        · intro v hv
          exact ((factorC v hv).mono (Names.subset_union_left _ _)).trans (sameθ v)
        · intro v hv
          have h := (factorC v hv).2 ei (by simp [observed, Names.union])
          simpa [θ, Substitution.withOutputs, Substitution.pullback, ei,
            reconstructedScheme, ComputationScheme.generalizeWithSupport] using h
  obtain ⟨n, run, φ, factor, inst, effects⟩ := comparison
  exact ⟨n, run, φ, factor, inst,
    ComputationScheme.outer_of_typing_instance φ typed real inst, effects⟩

end EHMX.HMX
