import EHMX.HMX.ReconstructionSoundness

/-! Theorem 17: one finite factor compares the environment, the qualified
reconstruction result, and its outer constraint. The concrete type algebra is
used only to prove that a global factor cannot hide free variable occurrences. -/
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

/-- Dissertation Theorem 17 for equalityTypes, arbitrary comparison order,
constraints and solved set. All expression forms and all target derivations,
including qualified existential projections, are covered. Realizability is
required of the substituted input environment, not of the target scheme.
The same factor also preserves the immediate effect. -/
theorem inferTerm_complete_scheme
    {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
    {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (closure : X.SolvedClosure P.solved) {g : Context X} {e : Expr}
    (σ : Substitution equalityTypes) {c : X.Formula} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X P.solved c (g.subst σ) e s eff)
    (real : (g.subst σ).Realizable c) :
    ∃ n, inferTerm sig X N P g e = some (.reconstructed n) ∧
      ∃ φ : Substitution equalityTypes,
        (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) g.support) ∧
        Instance X c ((reconstructedScheme g n).valueScheme.subst φ) s ∧
        X.Entails c (X.subst φ (reconstructedScheme g n).outer) ∧
        ∀ v, (reconstructedScheme g n).effect.eval (φ.pullback v).effects = eff.eval v.effects := by
  have comparison :
      ∃ n, inferTerm sig X N P g e = some (.reconstructed n) ∧
        ∃ φ : Substitution equalityTypes,
          (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) g.support) ∧
          Instance X c ((reconstructedScheme g n).valueScheme.subst φ) s ∧
          ∀ v, (reconstructedScheme g n).effect.eval (φ.pullback v).effects = eff.eval v.effects := by
    cases s with
    | mono t =>
        obtain ⟨n, run, φ, factor, residual, images⟩ :=
          inferTerm_complete_mono N P closure σ typed real
        refine ⟨n, run, φ, factor, ?_, fun v => (images v).2⟩
        apply ComputationScheme.instance_of_factor φ residual
        intro v _
        apply (X.holds_le _ _ _).mpr
        rw [Substitution.eval_apply, (images v).1]
        exact O.refl _
    | qualified a q t =>
        obtain ⟨b, r, u, alpha, fresh⟩ := Scheme.fresh_alpha a q t
          ((X.support c).union (g.support.union σ.range))
        have freshC : X.Avoids c b :=
          ⟨fun i hi hf => Finset.disjoint_left.mp fresh.1 hi
            (Finset.mem_union_left _ (X.freeType_mem_support hf)),
           fun i hi hf => Finset.disjoint_left.mp fresh.2 hi
            (Finset.mem_union_left _ (X.freeEffect_mem_support hf))⟩
        have freshG : b.Disjoint (g.support.union σ.range) :=
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
          intro v _
          apply (X.holds_le _ _ _).mpr
          simpa only [Substitution.identity_apply] using
            O.refl (equalityTypes.eval v u)
        obtain ⟨n, run, φ, factor, residual, images⟩ :=
          inferTerm_complete_mono N P closure σ mono (real.weaken (X.entails_left _ _))
        have monoComparison : Instance X (X.and c r)
            ((reconstructedScheme g n).valueScheme.subst φ) (.mono u) := by
          apply ComputationScheme.instance_of_factor φ residual
          intro v _
          apply (X.holds_le _ _ _).mpr
          rw [Substitution.eval_apply, (images v).1]
          exact O.refl _
        have freshSource : ((reconstructedScheme g n).valueScheme.subst φ).Avoids b :=
          ComputationScheme.generalizeWithSupport_subst_avoids g n.substitution φ σ
            _ _ _ b factor freshG
        exact ⟨n, run, φ, factor,
          .alphaRight (.symm alpha)
            (qualified_of_mono freshC freshSource projected monoComparison),
          fun v => (images v).2⟩
  obtain ⟨n, run, φ, factor, inst, effects⟩ := comparison
  exact ⟨n, run, φ, factor, inst,
    ComputationScheme.outer_of_typing_instance φ typed real inst, effects⟩

end EHMX.HMX
