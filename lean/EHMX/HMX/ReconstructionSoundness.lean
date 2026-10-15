import EHMX.HMX.TermReconstruction
import EHMX.HMX.EffectResiduals

/-! Output soundness for the same solved set used by normalization.
No additional rule restriction is imposed on generated expressions. -/

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}
open Derivation
/-- Generation constructs a derivation whose existential projections have
monomorphic results, including under polymorphic lets and handlers. -/
theorem Inference.sound_reconstruction {sig : Signature T} {X : Constraints T O} {N : X.Simplifier}
    {c g e a eff d} (h : Inference sig X N c g e a eff d) :
    (∃ tree : Derivation sig X d g e (.mono a) eff, UsesReconstructionRules tree) ∧ X.Entails d c := by
  induction h with
  | varMono found =>
    exact ⟨⟨(Derivation.var found).check, by trivial⟩, X.conjunction_entails (by simp)⟩
  | varPoly s found ht he =>
    let tree := Derivation.forallElim (sig := sig) s ht he (Derivation.var found) (X.entails_refl _)
    exact ⟨⟨tree.check, by simp [tree, Derivation.check, UsesReconstructionRules]⟩, X.conjunction_entails (by simp)⟩
  | int n => exact ⟨⟨(Derivation.int n).check, by trivial⟩, X.conjunction_entails (by simp)⟩
  | bool b => exact ⟨⟨(Derivation.bool b).check, by trivial⟩, X.conjunction_entails (by simp)⟩
  | lam _ ih =>
    obtain ⟨tree, good⟩ := ih.1
    exact ⟨⟨(Derivation.lam tree).check, good⟩, X.checked_input _ _ _ _ _ _⟩
  | @app c c₁ c₂ g f x ft xt result ef ex latent eff d₁ d₂ _ _ ihf ihx =>
    obtain ⟨tf, gf⟩ := ihf.1
    obtain ⟨tx, gx⟩ := ihx.1
    refine ⟨⟨?_, ?_⟩, X.conjunction_entails (by simp)⟩
    · apply Derivation.effectEq (eff := ef ∪ ex ∪ latent)
      · apply Derivation.app (a := xt) (latent := latent)
        · apply Derivation.sub
          · exact .weaken tf (X.conjunction_entails (by simp))
          · exact X.conjunction_entails (by simp)
        · exact .weaken tx (X.conjunction_entails (by simp))
      · exact X.conjunction_entails (by simp)
    · exact ⟨gf, gx⟩
  | letVal hv fresh _ _ ihv ihb =>
    obtain ⟨tv, gv⟩ := ihv.1
    obtain ⟨tb, gb⟩ := ihb.1
    refine ⟨⟨?_, ?_⟩, X.conjunction_entails (by simp)⟩
    · apply Derivation.letVal hv
      · exact .weaken (tv.generalize_normalized hv N _ fresh) (X.conjunction_entails (by simp))
      · exact .weaken tb (X.conjunction_entails (by simp))
    · exact ⟨gv, gb⟩
  | letMono hv _ _ ihv ihb =>
    obtain ⟨tv, gv⟩ := ihv.1
    obtain ⟨tb, gb⟩ := ihb.1
    refine ⟨⟨?_, ?_⟩, X.conjunction_entails (by simp)⟩
    · apply Derivation.effectEq
      · exact .letMono hv (.weaken tv (X.conjunction_entails (by simp)))
          (.weaken tb (X.conjunction_entails (by simp)))
      · exact X.conjunction_entails (by simp)
    · exact ⟨gv, gb⟩
  | @perform c c₁ g op raw arg a result ea eff d s hs hc ht he _ ih =>
    obtain ⟨tree, good⟩ := ih.1
    let argument := Derivation.sub (b := s.apply raw.input)
      (Derivation.weaken tree (X.entails_left _ _)) (X.entails_right _ _)
    exact ⟨⟨(Derivation.perform s hs hc ht he argument).check, by simpa [argument, Derivation.check, UsesReconstructionRules] using good⟩, X.checked_input _ _ _ _ _ _⟩
  | handle hs hc hf scope _ _ _ ihb ihr ihc =>
    obtain ⟨tb, gb⟩ := ihb.1
    obtain ⟨tr, gr⟩ := ihr.1
    obtain ⟨tc, gc⟩ := ihc.1
    refine ⟨⟨?_, ?_⟩, X.conjunction_entails (by simp)⟩
    · apply Derivation.handle hs hc hf scope.context scope.rigid_types
        scope.rigid_effects scope.witness_scope scope.witness_constraint scope.witness_effects
      · exact .weaken tb (X.conjunction_entails (by simp))
      · exact .sub (.weaken tr (X.conjunction_entails (by simp))) (X.conjunction_entails (by simp))
      · exact tc
      · exact X.conjunction_entails (by simp)
      · exact X.conjunction_entails (by simp)
      · exact X.conjunction_entails (by simp)
      · exact X.conjunction_entails (by simp)
    · exact ⟨gb, gr, gc⟩
  | check _ ih =>
    obtain ⟨tree, good⟩ := ih.1
    exact ⟨⟨tree.check, good⟩, X.checked_input _ _ _ _ _ _⟩
  | equivalent _ hd ih =>
    obtain ⟨tree, good⟩ := ih.1
    exact ⟨⟨.weaken tree hd.1, good⟩, X.entails_trans hd.1 ih.2⟩
  | project hg ht he hc _ ih =>
    obtain ⟨tree, good⟩ := ih.1
    exact ⟨⟨.existsIntro hg ht he tree, ⟨⟨_, rfl⟩, good⟩⟩,
      X.entails_trans (X.exists_mono _ ih.2) (X.project_independent _ _ hc).1⟩
end EHMX.HMX

namespace EHMX.HMX
open EHMX EHMX.HMX
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
/-- Reconstruction soundness in any supplied approximation of the substituted
input environment. This also permits returning to a closed original context. -/
theorem inferTermAt_sound_of_approximation {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (cl : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hsig : sig.Closed)
    {g g' : Context X} {e : Expr} {t : Ty} {eff : Effect} {n : X.NormalForm}
    (run : inferTermAt sig X N P g e t eff = some (.reconstructed n))
    (env : (g.subst n.substitution).Approximates P.solved n.residual g') :
    Typing sig X P.solved n.residual g' e
      (.mono (n.substitution.apply t)) (eff.subst n.substitution.effects) := by
  obtain ⟨d, generated, normalized, _⟩ := inferTermAt_normal run
  obtain ⟨solved, _, entails⟩ := P.sound (reconstructionScope_covers X g t eff d) normalized
  obtain ⟨⟨tree, good⟩, _⟩ := Inference.sound_reconstruction (generateProjected_sound N hsig generated)
  have adm : X.Admissible P.solved n.residual :=
    ⟨n.residual, solved, X.entails_refl _, X.entails_refl _⟩
  obtain ⟨s', typed, approx⟩ :=
    EHMX.HMX.Derivation.transform_to_solved_subst_reconstruction P cl reflect allow lift hr truth tree good n.substitution n.residual
      g' adm entails env
  exact typed.instance_mono (approx.2.2 _ trivial
    (Scheme.Approximates.refl_of_ground (S := P.solved) (c := n.residual)
      (s := Scheme.mono (n.substitution.apply t)) trivial
      (fun v _ => ⟨equalityTypes.eval v (n.substitution.apply t), O.refl _⟩)).2.1)

/-- Conditional counterpart of HM(X) Theorem 16, extended to generated
perform/handler derivations. For arbitrary S, admissibility of the actual
substituted environment is an explicit premise. -/
theorem inferTermAt_sound {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (cl : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hsig : sig.Closed)
    {g : Context X} {e : Expr} {t : Ty} {eff : Effect} {n : X.NormalForm}
    (run : inferTermAt sig X N P g e t eff = some (.reconstructed n))
    (real : g.Realizable X.top)
    (envAdm : (g.subst n.substitution).Admissible P.solved) :
    Typing sig X P.solved n.residual (g.subst n.substitution) e
      (.mono (n.substitution.apply t)) (eff.subst n.substitution.effects) := by
  have entTop : X.Entails n.residual (X.subst n.substitution X.top) := by
    intro v _
    exact (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial)
  exact inferTermAt_sound_of_approximation N P cl reflect allow lift hr truth hsig run
    (Context.Approximates.refl envAdm ((real.subst n.substitution).weaken entTop))

/-- Effect-only residuals preserve environment admissibility under substitution.
The output uses exactly the capture-avoiding substituted input environment. -/
theorem inferTermAt_sound_effectOnly {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (hsol : P.solved = EffectResiduals.Solved X)
    (cl : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hsig : sig.Closed)
    {g : Context X} {e : Expr} {t : Ty} {eff : Effect} {n : X.NormalForm}
    (run : inferTermAt sig X N P g e t eff = some (.reconstructed n))
    (envAdm : g.Admissible P.solved) (real : g.Realizable X.top) :
    Typing sig X P.solved n.residual (g.subst n.substitution) e
      (.mono (n.substitution.apply t)) (eff.subst n.substitution.effects) := by
  have reflect : EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved := by
    rw [hsol]
    exact EffectResidualNormalization.effectOnly_reflection
  apply inferTermAt_sound N P cl reflect allow lift hr truth hsig run real
  obtain ⟨d, _, normalized, _⟩ := inferTermAt_normal run
  have sat := (P.sound (reconstructionScope_covers X g t eff d) normalized).2.1
  rw [hsol] at envAdm ⊢
  exact (EffectResiduals.output_environment_self envAdm real n.substitution sat).admissible
/-- Soundness for the fresh output variables chosen by inferTerm. -/
theorem inferTerm_sound {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (cl : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hsig : sig.Closed)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (run : inferTerm sig X N P g e = some (.reconstructed n))
    (real : g.Realizable X.top)
    (envAdm : (g.subst n.substitution).Admissible P.solved) :
    Typing sig X P.solved n.residual (g.subst n.substitution) e
      (.mono (n.substitution.types (g.support.shiftTypes 0))) (n.substitution.effects (g.support.shiftEffects 0)) := by
  simpa [Substitution.apply, Ty.subst, Effect.subst, Effect.var] using
    inferTermAt_sound N P cl reflect allow lift hr truth hsig run real envAdm

/-- Soundness for the fresh output variables chosen by inferTerm. -/
theorem inferTerm_sound_effectOnly {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (hsol : P.solved = EffectResiduals.Solved X)
    (cl : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hsig : sig.Closed)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (run : inferTerm sig X N P g e = some (.reconstructed n))
    (envAdm : g.Admissible P.solved) (real : g.Realizable X.top) :
    Typing sig X P.solved n.residual (g.subst n.substitution) e
      (.mono (n.substitution.types (g.support.shiftTypes 0))) (n.substitution.effects (g.support.shiftEffects 0)) := by
  simpa [Substitution.apply, Ty.subst, Effect.subst, Effect.var] using
    inferTermAt_sound_effectOnly N P hsol cl allow lift hr truth hsig run envAdm real

end EHMX.HMX
