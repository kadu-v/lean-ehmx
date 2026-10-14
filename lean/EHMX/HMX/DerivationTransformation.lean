import EHMX.HMX.ContextApproximation
import EHMX.HMX.PrincipalCompleteness
import EHMX.HMX.ScopedSchemeApproximation

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

/-- The generalization step of the transformation, once its monomorphic body
has been proved in the selected solved set. Projection and the instance
comparison are proved here, not included in a transformation contract. -/
theorem Typing.generalize_normal_form {sig : Signature T}
    (Q : T.GroundRepresentation) (P : X.PrincipalNormalizer)
    {r c d : X.Formula} {a : Names} {t : T.Term} {n : X.NormalForm}
    {g : Context X} {e : Expr}
    (hr : P.solved r) (hrTrue : ∀ v, X.holds r v)
    (hc : X.Admissible P.solved (X.and c (X.existsNames a d)))
    (hn : n.IsPrincipal P.solved (X.and c d))
    (scope : n.substitution.domain.Subset a) (fresh : X.Avoids c a)
    (contextFresh : g.Avoids a) (value : Value e)
    (body : Typing sig X P.solved n.residual g e
      (.mono (n.substitution.apply t)) ∅) :
    Typing sig X P.solved (X.and c (X.existsNames a d)) g e
      (.qualified a n.residual (n.substitution.apply t)) ∅ ∧
    (Scheme.qualified a d t).Approximates P.solved (X.and c (X.existsNames a d))
      (.qualified a n.residual (n.substitution.apply t)) := by
  have projection := Constraints.NormalForm.project_equivalent X Q hr hrTrue hn scope
  have entails : X.Entails (X.and c (X.existsNames a d))
      (X.existsNames a n.residual) :=
    X.entails_trans (X.project_and_avoids fresh).2 projection.1
  have projected := P.admissible_exists X Q hr hrTrue body.root.1 a
  exact ⟨(body.generalize value a contextFresh projected).weaken hc entails,
    Constraints.NormalForm.generalized_approximation X Q hr hrTrue hn scope fresh⟩

/-- Construct the normal form used in the forall-introduction case and
substitute its monomorphic premise without changing the environment.
The resulting body is still a constraint-form derivation: transforming it to
`P.solved` is a separate obligation of Theorem 7. -/
theorem Typing.forallIntro_normal_form {O : TypeOrder equalityTypes}
    {X : Constraints equalityTypes O} {sig : Signature equalityTypes}
    (P : X.PrincipalNormalizer) {r c d : X.Formula} {a : Names} {t : Ty}
    {g : Context X} {e : Expr}
    (hr : P.solved r) (hrTrue : ∀ v, X.holds r v)
    (hc : X.Admissible P.solved (X.and c (X.existsNames a d)))
    (fresh : X.Avoids c a) (contextFresh : g.Avoids a)
    (real : (Scheme.qualified a d t).Realizable (X.and c (X.existsNames a d)))
    (contextReal : g.Realizable (X.and c (X.existsNames a d)))
    (body : Typing sig X X.Satisfiable (X.and c d) g e (.mono t) ∅) :
    ∃ n : X.NormalForm, n.IsPrincipal P.solved (X.and c d) ∧
      n.substitution.domain.Subset a ∧
      (Scheme.qualified a d t).Approximates P.solved (X.and c (X.existsNames a d))
        (.qualified a n.residual (n.substitution.apply t)) ∧
      Typing sig X X.Satisfiable n.residual g e
        (.mono (n.substitution.apply t)) ∅ := by
  obtain ⟨m, hm, scope, _⟩ :=
    Constraints.NormalForm.exists_of_realizable_finite X hc fresh real
  obtain ⟨n, hn⟩ : ∃ n, P.normalize (Constraints.ConstraintProblem.initial X (X.and c d)) =
      some n := by
    cases run : P.normalize (Constraints.ConstraintProblem.initial X (X.and c d)) with
    | some n => exact ⟨n, rfl⟩
    | none => exact False.elim ((P.failure _).mp run
        ⟨m, (Constraints.NormalForm.isNormalOf_initial_iff X).mpr hm⟩)
  obtain ⟨n', principal, domainScope⟩ := P.scope X hr hrTrue
    (P.principal_initial X hn) hm scope
  have avoids : g.Avoids n'.substitution.domain := by
    intro s hs
    exact ⟨fun i hi => (contextFresh s hs).1 i (domainScope.1 hi),
      fun i hi => (contextFresh s hs).2 i (domainScope.2 hi)⟩
  have entails : X.Entails (X.and c d) (X.and c (X.existsNames a d)) := by
    intro v hv
    obtain ⟨hc, hd⟩ := (X.holds_and _ _ _).mp hv
    exact (X.holds_and _ _ _).mpr ⟨hc, X.exists_intro a d v hd⟩
  have substituted := body.substitute_avoiding_context (Constraints.Simplifier.identity X)
    n'.substitution avoids (contextReal.weaken entails)
    (P.solved_satisfiable _ principal.1.1)
    (Constraints.NormalForm.reconstruct_entails X principal.1)
  have empty : (∅ : Effect).subst n'.substitution.effects = ∅ :=
    Effect.subst_eq_self _ _ (by simp)
  exact ⟨n', principal, domainScope,
    Constraints.NormalForm.generalized_approximation X equalityGroundRepresentation
      hr hrTrue principal domainScope fresh, by simpa only [empty] using substituted⟩

end EHMX.HMX
namespace EHMX.HMX
namespace Derivation
variable {O : TypeOrder equalityTypes} (X : Constraints equalityTypes O)

private theorem context_project {T : TypeDomain} {O : TypeOrder T}
    (X : Constraints T O) {S : X.Formula → Prop}
    (sound : ∀ d, S d → X.Satisfiable d) (closure : X.SolvedClosure S)
    {c r : X.Formula} {a : Names} {g g' : Context X}
    (h : g.Approximates S c g') (hr : X.Admissible S r)
    (proj : X.Equivalent c (X.existsNames a r))
    (freshC : X.Avoids c a) (freshG : g.Avoids a) :
    g.Approximates S r g' := by
  induction h with
  | nil => exact .nil
  | @cons s s' tail tail' hs hg ih =>
    exact .cons (Scheme.Approximates.project sound closure hs hr proj freshC
      (freshG s (by simp))) (ih (fun s hm => freshG s (List.mem_cons_of_mem _ hm)))


theorem forallIntro_original_child
    {sig : Signature equalityTypes}
    (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r c d D : X.Formula} {a : Names} {t : Ty} {g g' : Context X} {e : Expr}
    (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (value : Value e) (freshC : X.Avoids c a) (freshG : g.Avoids a)
    (θ : Substitution equalityTypes) (admitted : X.Admissible P.solved D)
    (entails : X.Entails D (X.subst θ (X.and c (X.existsNames a d))))
    (env : (g.subst θ).Approximates P.solved D g')
    (ih : ∀ (σ : Substitution equalityTypes) (q : X.Formula) (target : Context X),
      X.Admissible P.solved q → X.Entails q (X.subst σ (X.and c d)) →
      (g.subst σ).Approximates P.solved q target →
      ∃ s', Typing sig X P.solved q target e s' ((∅ : Effect).subst σ.effects) ∧
        ((Scheme.mono t).subst σ).Approximates P.solved q s') :
    let avoid := Scheme.substAvoid θ a d t
    let b : Names := ⟨a.types.image avoid.shiftTypes, a.effects.image avoid.shiftEffects⟩
    let η := θ.underBinder a avoid.shiftTypes avoid.shiftEffects
    ∀ u : Names,
      (X.freeNames (X.and D (X.subst η d))).Subset u →
      (X.freeNames (X.subst η d)).Subset u →
      (equalityTypes.support (η.apply t)).Subset u →
      (X.support D).Subset (u.diff b) →
      (g.support.union θ.range).Subset (u.diff b) →
      g'.support.Subset (u.diff b) →
      ∃ s', Typing sig X P.solved D g' e s' ∅ ∧
        ((Scheme.qualified a d t).subst θ).Approximates P.solved D s' := by
  intro avoid b η u obs qscope tscope dscope protectScope targetScope
  have originalGround (v : Valuation GroundTy) (hv : X.holds D v) :
      ∃ z, (Scheme.qualified a d t).GroundInstance (θ.pullback v) z := by
    have original := (X.holds_subst _ _ _).mp (entails v hv)
    obtain ⟨w, hw, hd⟩ := (X.holds_exists _ _ _).mp ((X.holds_and _ _ _).mp original).2
    exact ⟨equalityTypes.eval w t, w, hw, hd, O.refl _⟩
  have project : X.Entails D (X.existsNames b (X.subst η d)) := by
    intro v hv
    obtain ⟨z, hz⟩ := originalGround v hv
    have subst := (Scheme.groundInstance_subst θ v z (s := .qualified a d t)).mpr hz
    obtain ⟨w, hw, hd, _⟩ := subst
    exact (X.holds_exists _ _ _).mpr ⟨w, hw, hd⟩
  have outerEq : X.Equivalent (X.and D (X.existsNames b (X.subst η d))) D :=
    ⟨X.entails_left _ _, fun v hv => (X.holds_and _ _ _).mpr ⟨hv, project v hv⟩⟩
  have outerAdm : X.Admissible P.solved (X.and D (X.existsNames b (X.subst η d))) := by
    obtain ⟨rr, hrr, f, back⟩ := admitted
    exact ⟨rr, hrr, X.entails_trans outerEq.1 f, X.entails_trans back outerEq.2⟩
  have freshD : X.Avoids D b := by
    constructor
    · intro i hi hf
      exact (Finset.mem_sdiff.mp (dscope.1 (X.freeType_mem_support hf))).2 hi
    · intro i hi hf
      exact (Finset.mem_sdiff.mp (dscope.2 (X.freeEffect_mem_support hf))).2 hi
  obtain ⟨n, bound, hn, effects, protect, boundFresh, domainBound,
      _, targetFresh, _, approx, projection⟩ :=
    SchemeApproximation.generalized_approximation X P closure allow lift
      hr truth freshD outerAdm obs qscope tscope targetScope
  have projected : X.Equivalent D (X.existsNames bound n.residual) :=
    ⟨X.entails_trans outerEq.2 projection.1, X.entails_trans projection.2 outerEq.1⟩
  have residualAdm : X.Admissible P.solved n.residual :=
    ⟨n.residual, hn.1.1, X.entails_refl _, X.entails_refl _⟩
  have freshD' : X.Avoids D bound := by
    constructor
    · intro i hi hf
      exact Finset.disjoint_left.mp boundFresh.1 hi (dscope.1 (X.freeType_mem_support hf))
    · intro i hi hf
      exact Finset.disjoint_left.mp boundFresh.2 hi (dscope.2 (X.freeEffect_mem_support hf))
  have sourceFresh : (g.subst θ).Avoids bound :=
    g.subst_avoids θ bound (boundFresh.mono_right protectScope)
  have envR := context_project X P.solved_satisfiable closure env residualAdm projected freshD' sourceFresh
  have envComposed := Context.Approximates.underBinder_compose θ n.substitution a
    avoid.shiftTypes avoid.shiftEffects freshG (protect.mono_right protectScope) envR
  have solve : X.Entails n.residual
      (X.subst (n.substitution.compose η) (X.and c d)) := by
    intro v hv
    have norm := (X.holds_subst _ _ _).mp
      (Constraints.NormalForm.reconstruct_entails X hn.1 v hv)
    obtain ⟨hD, hd⟩ := (X.holds_and _ _ _).mp norm
    apply (X.holds_subst _ _ _).mpr
    rw [Substitution.compose_pullback]
    apply (X.holds_and _ _ _).mpr
    refine ⟨?_, (X.holds_subst _ _ _).mp hd⟩
    have hc := ((X.holds_and _ _ _).mp
      ((X.holds_subst _ _ _).mp (entails _ hD))).1
    apply (X.holds_agreeOutside freshC ?_).mpr hc
    constructor
    · intro i hi
      simp [η, Substitution.underBinder, Substitution.pullback, hi]
    · intro i hi
      simp [η, Substitution.underBinder, Substitution.pullback, hi]
  obtain ⟨s', body, bodyApprox⟩ := ih (n.substitution.compose η) n.residual g'
    residualAdm solve envComposed
  have inst : Instance X n.residual ((Scheme.mono t).subst (n.substitution.compose η))
      (.mono (n.substitution.apply (η.apply t))) := by
    apply Instance.sub
    intro v _
    apply (X.holds_le _ _ _).mpr
    have eqt : equalityTypes.eval v ((n.substitution.compose η).apply t) =
        equalityTypes.eval v (n.substitution.apply (η.apply t)) :=
      ((n.substitution.compose η).eval_apply v t).trans
        ((congrArg (fun w => equalityTypes.eval w t) (Substitution.compose_pullback _ _ v)).trans
          ((η.eval_apply (n.substitution.pullback v) t).symm.trans
            (n.substitution.eval_apply v (η.apply t)).symm))
    exact eqt ▸ O.refl _
  have monoBody := body.instance_mono
    (bodyApprox.2.2 (.mono (n.substitution.apply (η.apply t))) trivial inst)
  have empty : (∅ : Effect).subst (n.substitution.compose η).effects = ∅ :=
    Effect.subst_eq_self _ _ (by simp)
  rw [empty] at monoBody
  refine ⟨_, (monoBody.generalize value bound targetFresh
    (closure.project bound n.residual residualAdm)).weaken admitted projected.1, ?_⟩
  refine ⟨approx.1, approx.2.1.equivalent outerEq, ?_⟩
  intro target ha inst'
  exact (approx.2.2 target ha (inst'.equivalent ⟨outerEq.2, outerEq.1⟩)).equivalent outerEq


end Derivation
end EHMX.HMX
namespace EHMX.HMX
namespace Derivation
variable {O : TypeOrder equalityTypes} (X : Constraints equalityTypes O)

private def pad (θ : Substitution equalityTypes) (f : Names) : Substitution equalityTypes where
  domain := f.union θ.domain
  types := θ.types
  effects := θ.effects
  types_outside := by
    intro i hi
    exact θ.types_outside i ((Finset.notMem_union.mp hi).2)
  effects_outside := by
    intro i hi
    exact θ.effects_outside i ((Finset.notMem_union.mp hi).2)

theorem forallIntro_arbitrary_substitution
    {sig : Signature equalityTypes}
    (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r c d D : X.Formula} {a : Names} {t : Ty} {g g' : Context X} {e : Expr}
    (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (value : Value e) (freshC : X.Avoids c a) (freshG : g.Avoids a)
    (θ : Substitution equalityTypes) (admitted : X.Admissible P.solved D)
    (entails : X.Entails D (X.subst θ (X.and c (X.existsNames a d))))
    (env : (g.subst θ).Approximates P.solved D g')
    (ih : ∀ (σ : Substitution equalityTypes) (q : X.Formula) (target : Context X),
      X.Admissible P.solved q → X.Entails q (X.subst σ (X.and c d)) →
      (g.subst σ).Approximates P.solved q target →
      ∃ s', Typing sig X P.solved q target e s' ((∅ : Effect).subst σ.effects) ∧
        ((Scheme.mono t).subst σ).Approximates P.solved q s') :
    ∃ s', Typing sig X P.solved D g' e s' ∅ ∧
      ((Scheme.qualified a d t).subst θ).Approximates P.solved D s' := by
  let f := (X.support D).union (g.support.union g'.support)
  let δ := pad θ f
  let avoid := Scheme.substAvoid δ a d t
  let b : Names := ⟨a.types.image avoid.shiftTypes, a.effects.image avoid.shiftEffects⟩
  let η := δ.underBinder a avoid.shiftTypes avoid.shiftEffects
  let protectedNames := f.union δ.range
  have fresh : b.Disjoint protectedNames := by
    have base : b.Disjoint avoid :=
      ⟨avoid.shiftTypes_disjoint a, avoid.shiftEffects_disjoint a⟩
    apply base.mono_right
    constructor <;> intro i hi
    · rcases Finset.mem_union.mp hi with hf | hr
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_union_left _ hf)))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hr)
    · rcases Finset.mem_union.mp hi with hf | hr
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_union_left _ hf)))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hr)
  let u := (((X.freeNames (X.and D (X.subst η d))).union
      (X.freeNames (X.subst η d))).union (equalityTypes.support (η.apply t))).union protectedNames
  have scope : protectedNames.Subset (u.diff b) := by
    constructor
    · intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hi,
        fun hb => Finset.disjoint_left.mp fresh.1 hb hi⟩
    · intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hi,
        fun hb => Finset.disjoint_left.mp fresh.2 hb hi⟩
  have dscope : (X.support D).Subset protectedNames :=
    (Names.subset_union_left _ _).trans (Names.subset_union_left _ _)
  have gscope : g.support.Subset protectedNames :=
    ((Names.subset_union_left _ _).trans (Names.subset_union_right _ _)).trans
      (Names.subset_union_left _ _)
  have g'scope : g'.support.Subset protectedNames :=
    ((Names.subset_union_right _ _).trans (Names.subset_union_right _ _)).trans
      (Names.subset_union_left _ _)
  have rangeScope : δ.range.Subset protectedNames := Names.subset_union_right _ _
  have envδ : (g.subst δ).Approximates P.solved D g' :=
    Context.Approximates.subst_congr θ δ (fun _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ => rfl) env
  have entailsδ : X.Entails D (X.subst δ (X.and c (X.existsNames a d))) := by
    intro v hv
    exact (X.holds_subst _ _ _).mpr ((X.holds_subst θ _ v).mp (entails v hv))
  obtain ⟨s', typed, approx⟩ :=
    forallIntro_original_child X P closure allow lift hr truth value freshC freshG
      δ admitted entailsδ envδ ih u
      (((Names.subset_union_left _ _).trans (Names.subset_union_left _ _)).trans
        (Names.subset_union_left _ _))
      (((Names.subset_union_right _ _).trans (Names.subset_union_left _ _)).trans
        (Names.subset_union_left _ _))
      ((Names.subset_union_right _ _).trans (Names.subset_union_left _ _))
      (dscope.trans scope) ((gscope.union rangeScope).trans scope) (g'scope.trans scope)
  exact ⟨s', typed, Scheme.Approximates.subst_congr δ θ
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) approx⟩


end Derivation
end EHMX.HMX
namespace EHMX.HMX
namespace Derivation
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}

private theorem mono_approx {S : X.Formula → Prop} {c : X.Formula} (t : Ty) :
    (Scheme.mono t).Approximates S c (.mono t) :=
  Scheme.Approximates.refl_of_ground trivial (fun v _ => ⟨equalityTypes.eval v t, O.refl _⟩)

private theorem as_mono {S : X.Formula → Prop} {c : X.Formula} {g : Context X}
    {sig : Signature equalityTypes} {e : Expr} {s : Scheme X} {t : Ty} {eff : Effect}
    (typed : Typing sig X S c g e s eff) (approx : (Scheme.mono t).Approximates S c s) :
    Typing sig X S c g e (.mono t) eff :=
  typed.instance_mono (approx.2.2 (.mono t) trivial (mono_approx (S := S) t).2.1)

private theorem empty_subst (σ : Substitution equalityTypes) :
    (∅ : Effect).subst σ.effects = ∅ := Effect.subst_eq_self _ _ (by simp)

private theorem union_subst (σ : Substitution equalityTypes) (e f : Effect) :
    (e ∪ f).subst σ.effects = e.subst σ.effects ∪ f.subst σ.effects := by
  change Effect.mk _ _ = Effect.mk _ _
  apply congrArg₂ Effect.mk
  · ext i
    simp only [Effect.subst, Finset.mem_union, Finset.mem_biUnion]
    aesop
  · ext i
    simp only [Effect.subst, Finset.mem_union, Finset.mem_biUnion]
    aesop

private theorem alpha_source {s t target : Scheme X} {S : X.Formula → Prop} {c : X.Formula}
    (h : Scheme.AlphaEquivalent X s t) (σ : Substitution equalityTypes)
    (approx : (s.subst σ).Approximates S c target) :
    (t.subst σ).Approximates S c target := by
  have transport {p : X.Formula} {u : Scheme X}
      (h' : Scheme.AlphaEquivalent X s t) (inst : Instance X p (s.subst σ) u) :
      Instance X p (t.subst σ) u := by
    apply Instance.of_mono_targets (fun _ hv => inst.target_nonempty hv)
    intro q v hq hv
    exact (h'.subst_mono_iff σ q v).mp ((inst.weaken hq).trans hv)
  refine ⟨approx.1, transport h approx.2.1, ?_⟩
  intro u hu inst
  apply approx.2.2 u hu
  apply Instance.of_mono_targets (fun _ hv => inst.target_nonempty hv)
  intro q v hq hv
  exact (h.subst_mono_iff σ q v).mpr ((inst.weaken hq).trans hv)

/-- Source rules covered by the conditional Theorem 7. This is a property of
all nodes of the derivation, not merely the absence of handlers in the expression.
Value restriction and effect equality remain part of the current calculus. -/
def UsesHMXRules {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}
    {sig : Signature T} {c g e s eff}
    (tree : Derivation sig X c g e s eff) : Prop :=
  match tree with
  | .var _ | .int _ | .bool _ => True
  | .lam body => UsesHMXRules body
  | .app f x => UsesHMXRules f ∧ UsesHMXRules x
  | .letVal _ v body => UsesHMXRules v ∧ UsesHMXRules body
  | .letMono _ v body => UsesHMXRules v ∧ UsesHMXRules body
  | .sub body _ => UsesHMXRules body
  | .forallIntro _ _ _ body => UsesHMXRules body
  | .forallElim _ _ _ body _ => UsesHMXRules body
  | .weaken body _ => UsesHMXRules body
  | .effectEq body _ => UsesHMXRules body
  | .alpha body _ => UsesHMXRules body
  | .existsIntro .. | .perform .. | .handle .. => False

end Derivation
end EHMX.HMX

namespace EHMX.HMX.Derivation
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}
private theorem binder_environment {S : X.Formula → Prop}
    (sound : ∀ d, S d → X.Satisfiable d) (closure : X.SolvedClosure S)
    {C R : X.Formula} {A B : Names} {g g' : Context X}
    (θ κ : Substitution T) (ft fe : Nat → Nat)
    (env : (g.subst θ).Approximates S C g')
    (admitted : X.Admissible S R)
    (projection : X.Equivalent C (X.existsNames B R))
    (freshC : X.Avoids C B)
    (freshG : g.Avoids A)
    (freshB : B.Disjoint (g.support.union θ.range))
    (protect : κ.domain.Disjoint (g.support.union θ.range)) :
    (g.subst (κ.compose (θ.underBinder A ft fe))).Approximates S R g' := by
  have atR := context_project X sound closure env admitted projection freshC
    (g.subst_avoids θ B freshB)
  exact Context.Approximates.underBinder_compose θ κ A ft fe freshG protect atR

private theorem mono_approx_of_eval_eq {S : X.Formula → Prop} {C : X.Formula} {t u : T.Term}
    (equal : ∀ v, T.eval v t = T.eval v u) :
    (Scheme.mono (X := X) t).Approximates S C (.mono u) := by
  have forward : Instance X C (.mono t) (.mono u) := .sub (by
    intro v _
    apply (X.holds_le _ _ _).mpr
    rw [equal v]
    exact O.refl _)
  have backward : Instance X C (.mono u) (.mono t) := .sub (by
    intro v _
    apply (X.holds_le _ _ _).mpr
    rw [equal v]
    exact O.refl _)
  exact ⟨trivial, forward, fun _ _ inst => backward.trans inst⟩

private theorem clause_environment {S : X.Formula → Prop} {R : X.Formula}
    {g g' : Context X} (σ : Substitution T) (a b a' b' : T.Term)
    (env : (g.subst σ).Approximates S R g')
    (eqA : ∀ v, T.eval v (σ.apply a) = T.eval v a')
    (eqB : ∀ v, T.eval v (σ.apply b) = T.eval v b') :
    (Context.subst σ (.mono a :: .mono b :: g)).Approximates S R
      (.mono a' :: .mono b' :: g') :=
  .cons (mono_approx_of_eval_eq eqA) (.cons (mono_approx_of_eval_eq eqB) env)

end EHMX.HMX.Derivation

namespace EHMX.HMX.Derivation
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}
private theorem underBinder_agrees_on (θ : Substitution T) (A U : Names) (ft fe : Nat → Nat)
    (fresh : (Names.mk (A.types.image ft) (A.effects.image fe)).Disjoint (U.union θ.range))
    (v w z : Valuation T.Value)
    (hw : w.AgreeOutside v ⟨A.types.image ft, A.effects.image fe⟩)
    (ht : ∀ i ∈ A.types, z.types i = w.types (ft i))
    (he : ∀ i ∈ A.effects, z.effects i = w.effects (fe i))
    (hz : z.AgreeOutside (θ.pullback v) A) :
    ((θ.underBinder A ft fe).pullback w).AgreeOn z U := by
  constructor
  · intro i hi
    by_cases ha : i ∈ A.types
    · simpa [Substitution.pullback, Substitution.underBinder, ha, T.eval_var] using (ht i ha).symm
    · have scope := θ.type_support_subset U hi
      have same : T.eval w (θ.types i) = T.eval v (θ.types i) := by
        apply T.eval_support
        exact ⟨fun j hj => hw.1 j (fun hb => Finset.disjoint_left.mp fresh.1 hb (scope.1 hj)),
          fun j hj => hw.2 j (fun hb => Finset.disjoint_left.mp fresh.2 hb (scope.2 hj))⟩
      simpa [Substitution.pullback, Substitution.underBinder, ha] using same.trans (hz.1 i ha).symm
  · intro i hi
    by_cases ha : i ∈ A.effects
    · simpa [Substitution.pullback, Substitution.underBinder, ha, Effect.eval, Effect.var] using (he i ha).symm
    · have scope := θ.effect_support_subset U hi
      have same := Effect.eval_support (θ.effects i) w.effects v.effects
        (fun j hj => hw.2 j (fun hb => Finset.disjoint_left.mp fresh.2 hb (scope hj)))
      simpa [Substitution.pullback, Substitution.underBinder, ha] using same.trans (hz.2 i ha).symm

private theorem assignImages_agrees_outside (v z : Valuation T.Value) (A : Names) (ft fe : Nat → Nat) :
    (v.assignImages z A ft fe).AgreeOutside v ⟨A.types.image ft, A.effects.image fe⟩ := by
  constructor
  · intro i hi
    exact (v.assignImages_agree z A ft fe ⟨{i}, ∅⟩ (by simpa using hi) (by simp)).1 i (by simp)
  · intro i hi
    exact (v.assignImages_agree z A ft fe ⟨∅, {i}⟩ (by simp) (by simpa using hi)).2 i (by simp)

private theorem exists_subst_underBinder (θ : Substitution T) (A : Names) (Q : X.Formula)
    (ft fe : Nat → Nat) (hti : Function.Injective ft) (hei : Function.Injective fe)
    (fresh : (Names.mk (A.types.image ft) (A.effects.image fe)).Disjoint
      ((X.support Q).union θ.range)) :
    X.Equivalent (X.subst θ (X.existsNames A Q))
      (X.existsNames ⟨A.types.image ft, A.effects.image fe⟩
        (X.subst (θ.underBinder A ft fe) Q)) := by
  constructor
  · intro v hv
    obtain ⟨z, hz, hq⟩ := (X.holds_exists _ _ _).mp ((X.holds_subst _ _ _).mp hv)
    let w := v.assignImages z A ft fe
    have hw := assignImages_agrees_outside v z A ft fe
    have same := underBinder_agrees_on θ A (X.support Q) ft fe fresh v w z hw
      (fun i hi => (v.assignImages_types z A ft fe hti.injOn i hi).symm)
      (fun i hi => (v.assignImages_effects z A ft fe hei.injOn i hi).symm) hz
    exact (X.holds_exists _ _ _).mpr
      ⟨w, hw, (X.holds_subst _ _ _).mpr ((X.holds_support Q _ _ same).mpr hq)⟩
  · intro v hv
    obtain ⟨w, hw, hq⟩ := (X.holds_exists _ _ _).mp hv
    let z := (θ.pullback v).patch ⟨w.types ∘ ft, w.effects ∘ fe⟩ A
    have hz := Valuation.patch_agreeOutside (θ.pullback v) ⟨w.types ∘ ft, w.effects ∘ fe⟩ A
    have same := underBinder_agrees_on θ A (X.support Q) ft fe fresh v w z hw
      (by intro i hi; simp [z, Valuation.patch, hi])
      (by intro i hi; simp [z, Valuation.patch, hi]) hz
    exact (X.holds_subst _ _ _).mpr ((X.holds_exists _ _ _).mpr
      ⟨z, hz, (X.holds_support Q _ _ same).mp ((X.holds_subst _ _ _).mp hq)⟩)

private theorem clause_subst_underBinder (θ : Substitution T) (B J : Names) (Q : X.Formula)
    (ft fe : Nat → Nat) (hti : Function.Injective ft) (hei : Function.Injective fe)
    (_disjoint : B.Disjoint J)
    (fresh : (Names.mk ((B.union J).types.image ft) ((B.union J).effects.image fe)).Disjoint
      ((X.support Q).union θ.range)) :
    X.Entails (X.subst θ (X.clause B J Q))
      (X.clause ⟨B.types.image ft, B.effects.image fe⟩
        ⟨J.types.image ft, J.effects.image fe⟩
        (X.subst (θ.underBinder (B.union J) ft fe) Q)) := by
  intro v hv
  have old := (X.holds_clause _ _ _ _).mp ((X.holds_subst _ _ _).mp hv)
  apply (X.holds_clause _ _ _ _).mpr
  intro w hw
  let y := (θ.pullback v).patch ⟨w.types ∘ ft, w.effects ∘ fe⟩ B
  have hy := Valuation.patch_agreeOutside (θ.pullback v) ⟨w.types ∘ ft, w.effects ∘ fe⟩ B
  obtain ⟨z, hz, hq⟩ := old y hy
  let u := w.assignImages z J ft fe
  have hu := assignImages_agrees_outside w z J ft fe
  have outside : u.AgreeOutside v ⟨(B.union J).types.image ft, (B.union J).effects.image fe⟩ := by
    constructor
    · intro i hi
      have hb : i ∉ B.types.image ft := fun h =>
        hi (Finset.mem_image.mpr (by obtain ⟨j, hj, eq⟩ := Finset.mem_image.mp h; exact ⟨j, Finset.mem_union_left _ hj, eq⟩))
      have hj : i ∉ J.types.image ft := fun h =>
        hi (Finset.mem_image.mpr (by obtain ⟨j, hj, eq⟩ := Finset.mem_image.mp h; exact ⟨j, Finset.mem_union_right _ hj, eq⟩))
      exact (hu.1 i hj).trans (hw.1 i hb)
    · intro i hi
      have hb : i ∉ B.effects.image fe := fun h =>
        hi (Finset.mem_image.mpr (by obtain ⟨j, hj, eq⟩ := Finset.mem_image.mp h; exact ⟨j, Finset.mem_union_left _ hj, eq⟩))
      have hj : i ∉ J.effects.image fe := fun h =>
        hi (Finset.mem_image.mpr (by obtain ⟨j, hj, eq⟩ := Finset.mem_image.mp h; exact ⟨j, Finset.mem_union_right _ hj, eq⟩))
      exact (hu.2 i hj).trans (hw.2 i hb)
  have originalOutside : z.AgreeOutside (θ.pullback v) (B.union J) := by
    constructor
    · intro i hi
      have h := Finset.notMem_union.mp hi
      exact (hz.1 i h.2).trans (hy.1 i h.1)
    · intro i hi
      have h := Finset.notMem_union.mp hi
      exact (hz.2 i h.2).trans (hy.2 i h.1)
  have typematch : ∀ i ∈ (B.union J).types, z.types i = u.types (ft i) := by
    intro i hi
    by_cases hj : i ∈ J.types
    · exact (w.assignImages_types z J ft fe hti.injOn i hj).symm
    · have hb := (Finset.mem_union.mp hi).resolve_right hj
      have hfi : ft i ∉ J.types.image ft := by
        rintro h
        obtain ⟨j, hj', heq⟩ := Finset.mem_image.mp h
        exact hj ((hti heq) ▸ hj')
      have eq := hz.1 i hj
      have yu : y.types i = w.types (ft i) := by simp [y, Valuation.patch, hb]
      exact eq.trans (yu.trans (hu.1 (ft i) hfi).symm)
  have effectmatch : ∀ i ∈ (B.union J).effects, z.effects i = u.effects (fe i) := by
    intro i hi
    by_cases hj : i ∈ J.effects
    · exact (w.assignImages_effects z J ft fe hei.injOn i hj).symm
    · have hb := (Finset.mem_union.mp hi).resolve_right hj
      have hfi : fe i ∉ J.effects.image fe := by
        rintro h
        obtain ⟨j, hj', heq⟩ := Finset.mem_image.mp h
        exact hj ((hei heq) ▸ hj')
      have eq := hz.2 i hj
      have yu : y.effects i = w.effects (fe i) := by simp [y, Valuation.patch, hb]
      exact eq.trans (yu.trans (hu.2 (fe i) hfi).symm)
  have same := underBinder_agrees_on θ (B.union J) (X.support Q) ft fe fresh
    v u z outside typematch effectmatch originalOutside
  exact ⟨u, hu, (X.holds_subst _ _ _).mpr ((X.holds_support Q _ _ same).mpr hq)⟩
end EHMX.HMX.Derivation

namespace EHMX.HMX.Derivation
variable {T : TypeDomain} {O : TypeOrder T}
private theorem operation_underBinder (θ : Substitution T) (A : Names)
    (ft fe : Nat → Nat) (hti : Function.Injective ft) (hei : Function.Injective fe)
    {raw decl : Operation T} (closed : raw.Closed) (old : raw.FreshInstance decl)
    (bound : decl.bound.Subset A) :
    ∃ decl' : Operation T, raw.FreshInstance decl' ∧
      decl'.bound = ⟨decl.bound.types.image ft, decl.bound.effects.image fe⟩ ∧
      ∀ v, T.eval v ((θ.underBinder A ft fe).apply decl.input) = T.eval v decl'.input ∧
        T.eval v ((θ.underBinder A ft fe).apply decl.output) = T.eval v decl'.output := by
  obtain ⟨p, q, hp, hq, rfl⟩ := old
  let decl' := raw.rename (ft ∘ p) (fe ∘ q)
  refine ⟨decl', ⟨ft ∘ p, fe ∘ q, ?_, ?_, rfl⟩, ?_, ?_⟩
  · intro i hi j hj eq
    exact hp hi hj (hti eq)
  · intro i hi j hj eq
    exact hq hi hj (hei eq)
  · simp [decl', Operation.rename, Finset.image_image]
  · intro v
    have term (t : T.Term) (ht : (T.support t).Subset raw.bound) :
        T.eval v ((θ.underBinder A ft fe).apply (T.rename p q t)) =
        T.eval v (T.rename (ft ∘ p) (fe ∘ q) t) := by
      rw [Substitution.eval_apply, T.eval_rename, T.eval_rename]
      apply T.eval_support
      constructor
      · intro i hi
        have hm := bound.1 (Finset.mem_image.mpr ⟨i, ht.1 hi, rfl⟩)
        simp [Substitution.pullback, Substitution.underBinder, hm, T.eval_var, Function.comp_def]
      · intro i hi
        have hm := bound.2 (Finset.mem_image.mpr ⟨i, ht.2 hi, rfl⟩)
        simp [Substitution.pullback, Substitution.underBinder, hm, Effect.eval, Effect.var, Function.comp_def]
    exact ⟨term raw.input
      ⟨fun _ hi => closed.1 (Finset.mem_union_left _ hi),
       fun _ hi => closed.2 (Finset.mem_union_left _ hi)⟩,
      term raw.output
      ⟨fun _ hi => closed.1 (Finset.mem_union_right _ hi),
       fun _ hi => closed.2 (Finset.mem_union_right _ hi)⟩⟩

private theorem external_term_eval (θ κ : Substitution T) (A : Names) (ft fe : Nat → Nat)
    (t : T.Term) (avoid : A.Disjoint (T.support t))
    (protect : κ.domain.Disjoint (T.support (θ.apply t))) (v : Valuation T.Value) :
    T.eval v ((κ.compose (θ.underBinder A ft fe)).apply t) =
      T.eval v (θ.apply t) := by
  rw [Substitution.eval_apply, Substitution.compose_pullback]
  have h : T.eval ((θ.underBinder A ft fe).pullback (κ.pullback v)) t =
      T.eval (θ.pullback (κ.pullback v)) t := by
    apply T.eval_support
    constructor
    · intro i hi
      have ha : i ∉ A.types := fun h => Finset.disjoint_left.mp avoid.1 h hi
      simp [Substitution.pullback, Substitution.underBinder, ha]
    · intro i hi
      have ha : i ∉ A.effects := fun h => Finset.disjoint_left.mp avoid.2 h hi
      simp [Substitution.pullback, Substitution.underBinder, ha]
  rw [h, ← Substitution.eval_apply]
  apply T.eval_support
  constructor
  · intro i hi
    exact (κ.pullback_outside v).1 i
      (fun h => Finset.disjoint_left.mp protect.1 h hi)
  · intro i hi
    exact (κ.pullback_outside v).2 i
      (fun h => Finset.disjoint_left.mp protect.2 h hi)
end EHMX.HMX.Derivation

namespace EHMX.HMX.Derivation
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
/-- Normalize a projected premise while fixing the finite set of external names. -/
private theorem normal_project
    (P : X.ScopedPrincipalNormalizer) (cl : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r D Q : X.Formula} {A F : Names}
    (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (adm : X.Admissible P.solved D)
    (fresh : X.Avoids D A) (dis : A.Disjoint F)
    (ent : X.Entails D (X.existsNames A Q)) :
    ∃ (n : X.NormalForm) (W : Names),
      n.IsNormal P.solved (X.and D Q) ∧ n.substitution.domain.Disjoint F ∧
      n.substitution.effects = Effect.var ∧ W.Disjoint F ∧
      X.Equivalent D (X.existsNames W n.residual) := by
  let U := (X.freeNames (X.and D Q)).union F
  have fscope : F.Subset (U.diff A) := by
    constructor
    · intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hi,
        fun ha => Finset.disjoint_left.mp dis.1 ha hi⟩
    · intro i hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hi,
        fun ha => Finset.disjoint_left.mp dis.2 ha hi⟩
  have eqv : X.Equivalent (X.and D (X.existsNames A Q)) D :=
    ⟨X.entails_left _ _, fun v hv => (X.holds_and _ _ _).mpr ⟨hv, ent v hv⟩⟩
  have outer : X.Admissible P.solved (X.and D (X.existsNames A Q)) := by
    obtain ⟨s, hs, f, b⟩ := adm
    exact ⟨s, hs, X.entails_trans eqv.1 f, X.entails_trans b eqv.2⟩
  obtain ⟨n, hn, protect, effects⟩ :=
    EffectResidualNormalization.scoped_principal_with_effect_residual X P cl allow lift
      fresh outer (Names.subset_union_left _ F)
  obtain ⟨W, _, _, freshW, _, proj⟩ :=
    SchemeApproximation.projected_residual X equalityGroundRepresentation hr truth
      (Names.subset_union_left _ F) hn protect Names.empty
  have peq := X.project_and_avoids (d := Q) fresh
  exact ⟨n, W, hn.1, protect.mono_right fscope, effects, freshW.mono_right fscope,
    X.entails_trans eqv.2 (X.entails_trans peq.2 proj.1),
    X.entails_trans proj.2 (X.entails_trans peq.1 eqv.1)⟩

private theorem avoids_of_disjoint_support (D : X.Formula) (A : Names)
    (h : A.Disjoint (X.support D)) : X.Avoids D A :=
  ⟨fun _ hi hf => Finset.disjoint_left.mp h.1 hi (X.freeType_mem_support hf),
   fun _ hi hf => Finset.disjoint_left.mp h.2 hi (X.freeEffect_mem_support hf)⟩

private theorem external_effect_eval (θ κ : Substitution equalityTypes) (A : Names)
    (ft fe : Nat → Nat) (eff : Effect)
    (avoid : Disjoint A.effects eff.vars) (idE : κ.effects = Effect.var)
    (v : Valuation GroundTy) :
    (eff.subst (κ.compose (θ.underBinder A ft fe)).effects).eval v.effects =
      (eff.subst θ.effects).eval v.effects := by
  rw [Effect.eval_subst, Effect.eval_subst]
  change eff.eval ((κ.compose (θ.underBinder A ft fe)).pullback v).effects =
    eff.eval (θ.pullback v).effects
  rw [Substitution.compose_pullback]
  apply Effect.eval_support
  intro i hi
  have ha : i ∉ A.effects := fun h => Finset.disjoint_left.mp avoid h hi
  simp [Substitution.underBinder, Substitution.pullback, ha, idE, Effect.eval, Effect.var]

/-- Reconstruct monomorphic existential projection after any outer substitution. -/
private theorem existsIntro_arbitrary_substitution {sig : Signature equalityTypes}
    (P : X.ScopedPrincipalNormalizer) (cl : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r c D : X.Formula} {A : Names} {g g' : Context X} {e : Expr} {t : Ty} {eff : Effect}
    (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (freshG : g.Avoids A) (freshT : (Scheme.mono (X := X) t).Avoids A)
    (freshE : Disjoint A.effects eff.vars)
    (θ : Substitution equalityTypes) (admitted : X.Admissible P.solved D)
    (entails : X.Entails D (X.subst θ (X.existsNames A c)))
    (env : (g.subst θ).Approximates P.solved D g')
    (ih : ∀ (σ : Substitution equalityTypes) (R : X.Formula) (target : Context X),
      X.Admissible P.solved R → X.Entails R (X.subst σ c) →
      (g.subst σ).Approximates P.solved R target →
      Typing sig X P.solved R target e (.mono (σ.apply t)) (eff.subst σ.effects)) :
    Typing sig X P.solved D g' e (.mono (θ.apply t)) (eff.subst θ.effects) := by
  let F := (X.support D).union ((g.support.union θ.range).union
    (g'.support.union ((equalityTypes.support (θ.apply t)).union
      ⟨∅, (eff.subst θ.effects).vars⟩)))
  let avoid := F.union ((X.support c).union θ.range)
  let B : Names := ⟨A.types.image avoid.shiftTypes, A.effects.image avoid.shiftEffects⟩
  let η := θ.underBinder A avoid.shiftTypes avoid.shiftEffects
  have fresh : B.Disjoint avoid := ⟨avoid.shiftTypes_disjoint A, avoid.shiftEffects_disjoint A⟩
  have freshF := fresh.mono_right (Names.subset_union_left _ _)
  have dc : (X.support D).Subset F := Names.subset_union_left _ _
  have gc : (g.support.union θ.range).Subset F :=
    (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
  have g'c : g'.support.Subset F :=
    ((Names.subset_union_left _ _).trans (Names.subset_union_right _ _)).trans (Names.subset_union_right _ _)
  have tc : (equalityTypes.support (θ.apply t)).Subset F :=
    (((Names.subset_union_left _ _).trans (Names.subset_union_right _ _)).trans
      (Names.subset_union_right _ _)).trans (Names.subset_union_right _ _)
  have ec : (Names.mk ∅ (eff.subst θ.effects).vars).Subset F :=
    (((Names.subset_union_right _ _).trans (Names.subset_union_right _ _)).trans
      (Names.subset_union_right _ _)).trans (Names.subset_union_right _ _)
  have ent : X.Entails D (X.existsNames B (X.subst η c)) :=
    X.entails_trans entails
      (exists_subst_underBinder θ A c avoid.shiftTypes avoid.shiftEffects
        avoid.shiftTypes_injective avoid.shiftEffects_injective
        (fresh.mono_right (Names.subset_union_right _ _))).1
  obtain ⟨n, W, hn, protect, effects, fw, proj⟩ :=
    normal_project P cl allow lift hr truth admitted
      (avoids_of_disjoint_support D B (freshF.mono_right dc)) freshF ent
  have adm : X.Admissible P.solved n.residual :=
    ⟨n.residual, hn.1, X.entails_refl _, X.entails_refl _⟩
  have envσ := binder_environment P.solved_satisfiable cl
    θ n.substitution avoid.shiftTypes avoid.shiftEffects env adm proj
    (avoids_of_disjoint_support D W (fw.mono_right dc)) freshG (fw.mono_right gc) (protect.mono_right gc)
  have solve : X.Entails n.residual (X.subst (n.substitution.compose η) c) := by
    intro v hv
    have h := (X.holds_subst _ _ _).mp (Constraints.NormalForm.reconstruct_entails X hn v hv)
    apply (X.holds_subst _ _ _).mpr
    rw [Substitution.compose_pullback]
    exact (X.holds_subst _ _ _).mp ((X.holds_and _ _ _).mp h).2
  have body := ih (n.substitution.compose η) n.residual g' adm solve envσ
  have avoidsT : A.Disjoint (equalityTypes.support t) :=
    ⟨Finset.disjoint_left.mpr (fun i hi hf => freshT.1 i hi hf),
     Finset.disjoint_left.mpr (fun i hi hf => freshT.2 i hi hf)⟩
  have cast : Typing sig X P.solved n.residual g' e (.mono (θ.apply t))
      (eff.subst (n.substitution.compose η).effects) := body.instance_mono (Instance.sub (by
    intro v _
    apply (X.holds_le _ _ _).mpr
    rw [external_term_eval θ n.substitution A avoid.shiftTypes avoid.shiftEffects t avoidsT
      (protect.mono_right tc) v]
    exact O.refl _))
  have body' : Typing sig X P.solved n.residual g' e (.mono (θ.apply t))
      (eff.subst θ.effects) := cast.effectEq (by
    intro v _
    exact (X.holds_effectEq _ _ _).mpr
      (external_effect_eval θ n.substitution A avoid.shiftTypes avoid.shiftEffects eff freshE effects v))
  apply (body'.existsIntro (cl.project W n.residual adm)
    (g'.avoids_of_support_disjoint W (fw.mono_right g'c)) _ _).weaken admitted proj.1
  · exact ⟨fun i hi hf => Finset.disjoint_left.mp fw.1 hi (tc.1 hf),
      fun i hi hf => Finset.disjoint_left.mp fw.2 hi (tc.2 hf)⟩
  · exact Finset.disjoint_left.mpr (fun i hi hf => Finset.disjoint_left.mp fw.2 hi (ec.2 hf))
end EHMX.HMX.Derivation

namespace EHMX.HMX.Derivation
private theorem support_rename (t : Ty) (f h : Nat → Nat) :
    (t.rename f h).fvTypes = t.fvTypes.image f ∧
      (t.rename f h).fvEffects = t.fvEffects.image h := by
  induction t with
  | var => simp [Ty.rename, Ty.fvTypes, Ty.fvEffects]
  | base => simp [Ty.rename, Ty.fvTypes, Ty.fvEffects]
  | arr a eff b iha ihb =>
    simp [Ty.rename, Ty.fvTypes, Ty.fvEffects, Effect.rename, iha, ihb, Finset.image_union]
private theorem fresh_instance_closed {raw decl : Operation equalityTypes}
    (closed : raw.Closed) (fresh : raw.FreshInstance decl) : decl.Closed := by
  obtain ⟨f, h, _, _, rfl⟩ := fresh
  change (raw.input.rename f h).fvTypes ∪ (raw.output.rename f h).fvTypes ⊆ _ ∧
    (raw.input.rename f h).fvEffects ∪ (raw.output.rename f h).fvEffects ⊆ _
  rw [(support_rename _ _ _).1, (support_rename _ _ _).1,
    (support_rename _ _ _).2, (support_rename _ _ _).2]
  constructor
  · rw [← Finset.image_union]
    exact Finset.image_subset_image closed.1
  · rw [← Finset.image_union]
    exact Finset.image_subset_image closed.2
private theorem image_disjoint (a b : Finset Nat) (f : Nat → Nat)
    (inj : Function.Injective f) (dis : Disjoint a b) :
    Disjoint (a.image f) (b.image f) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, eq⟩ := Finset.mem_image.mp hy
  exact Finset.disjoint_left.mp dis hi ((inj eq) ▸ hj)
end EHMX.HMX.Derivation

namespace EHMX.HMX.Derivation
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
/-- Freshen rigid and witness names, transform the original clause, and rebuild
its universal/existential condition without allowing names to escape. -/
private theorem handler_arbitrary_substitution {sig : Signature equalityTypes}
    (P : X.ScopedPrincipalNormalizer) (cl : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r c d D : X.Formula} {g g' : Context X}
    {body ret clause : Expr} {op : Op} {raw decl : Operation equalityTypes}
    {input result ct : Ty} {ein er eo rest out : Effect} {J : Names}
    (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hs : sig op = some raw) (hc : raw.Closed) (hf : raw.FreshInstance decl)
    (scopeH : decl.Scoped X c g input result ein er rest out J)
    (hclause : X.Entails c (X.clause decl.bound J
      (X.and d (X.and (X.le ct result) (X.effectLe eo out)))))
    (hSplit : X.Entails c (X.split op ein rest))
    (hRest : X.Entails c (X.effectLe rest out))
    (hRet : X.Entails c (X.effectLe er out))
    (θ : Substitution equalityTypes) (admitted : X.Admissible P.solved D)
    (entails : X.Entails D (X.subst θ c))
    (env : (g.subst θ).Approximates P.solved D g')
    (bodyTyped : Typing sig X P.solved D g' body (.mono (θ.apply input)) (ein.subst θ.effects))
    (retTyped : Typing sig X P.solved D (.mono (θ.apply input) :: g') ret
      (.mono (θ.apply result)) (er.subst θ.effects))
    (ih : ∀ (σ : Substitution equalityTypes) (R : X.Formula) (target : Context X),
      X.Admissible P.solved R → X.Entails R (X.subst σ d) →
      (Context.subst σ (.mono (Ty.arr decl.output out result) :: .mono decl.input :: g)).Approximates
        P.solved R target →
      Typing sig X P.solved R target clause (.mono (σ.apply ct)) (eo.subst σ.effects)) :
    Typing sig X P.solved D g' (.handle body op ret clause) (.mono (θ.apply result))
      (out.subst θ.effects) := by
  let Q := X.and d (X.and (X.le ct result) (X.effectLe eo out))
  let A := decl.bound.union J
  let external := g'.support.union
    (((equalityTypes.support (θ.apply input)).union (equalityTypes.support (θ.apply result))).union
      ⟨∅, (ein.subst θ.effects).vars ∪ (er.subst θ.effects).vars ∪
        (rest.subst θ.effects).vars ∪ (out.subst θ.effects).vars⟩)
  let F0 := (X.support D).union ((g.support.union θ.range).union external)
  let avoid := F0.union ((X.support Q).union θ.range)
  let B' : Names := ⟨decl.bound.types.image avoid.shiftTypes, decl.bound.effects.image avoid.shiftEffects⟩
  let J' : Names := ⟨J.types.image avoid.shiftTypes, J.effects.image avoid.shiftEffects⟩
  let η := θ.underBinder A avoid.shiftTypes avoid.shiftEffects
  have freshA : (Names.mk (A.types.image avoid.shiftTypes) (A.effects.image avoid.shiftEffects)).Disjoint avoid :=
    ⟨avoid.shiftTypes_disjoint A, avoid.shiftEffects_disjoint A⟩
  have freshB0 : B'.Disjoint F0 :=
    ⟨(avoid.shiftTypes_disjoint decl.bound).mono_right Finset.subset_union_left,
      (avoid.shiftEffects_disjoint decl.bound).mono_right Finset.subset_union_left⟩
  have freshJ0 : J'.Disjoint F0 :=
    ⟨(avoid.shiftTypes_disjoint J).mono_right Finset.subset_union_left,
      (avoid.shiftEffects_disjoint J).mono_right Finset.subset_union_left⟩
  have jB : J.Disjoint decl.bound := scopeH.witness_scope.mono_right
    (by constructor <;> intro i hi <;> simp [Names.union, hi])
  have bj : decl.bound.Disjoint J := ⟨jB.1.symm, jB.2.symm⟩
  have j'b' : J'.Disjoint B' :=
    ⟨image_disjoint _ _ _ avoid.shiftTypes_injective jB.1,
      image_disjoint _ _ _ avoid.shiftEffects_injective jB.2⟩
  let F := F0.union B'
  have freshJF : J'.Disjoint F :=
    ⟨Finset.disjoint_union_right.mpr ⟨freshJ0.1, j'b'.1⟩,
      Finset.disjoint_union_right.mpr ⟨freshJ0.2, j'b'.2⟩⟩
  have dc0 : (X.support D).Subset F0 := Names.subset_union_left _ _
  have gc0 : (g.support.union θ.range).Subset F0 :=
    (Names.subset_union_left _ _).trans (Names.subset_union_right _ _)
  have ext0 : external.Subset F0 :=
    (Names.subset_union_right _ _).trans (Names.subset_union_right _ _)
  have dc : (X.support D).Subset F := dc0.trans (Names.subset_union_left _ _)
  have gc : (g.support.union θ.range).Subset F := gc0.trans (Names.subset_union_left _ _)
  have ext : external.Subset F := ext0.trans (Names.subset_union_left _ _)
  have tc0 : (equalityTypes.support (θ.apply result)).Subset F0 :=
    (((Names.subset_union_right _ _).trans (Names.subset_union_left _ _)).trans
      (Names.subset_union_right _ _)).trans ext0
  have tc : (equalityTypes.support (θ.apply result)).Subset F := tc0.trans (Names.subset_union_left _ _)
  have g'c0 : g'.support.Subset F0 := (Names.subset_union_left _ _).trans ext0
  have ic0 : (equalityTypes.support (θ.apply input)).Subset F0 :=
    (((Names.subset_union_left _ _).trans (Names.subset_union_left _ _)).trans
      (Names.subset_union_right _ _)).trans ext0
  have ec0 : (Names.mk ∅ ((ein.subst θ.effects).vars ∪ (er.subst θ.effects).vars ∪
      (rest.subst θ.effects).vars ∪ (out.subst θ.effects).vars)).Subset F0 :=
    ((Names.subset_union_right _ _).trans (Names.subset_union_right _ _)).trans ext0
  obtain ⟨decl', hf', bEq, declEq⟩ :=
    operation_underBinder θ A avoid.shiftTypes avoid.shiftEffects
      avoid.shiftTypes_injective avoid.shiftEffects_injective hc hf (Names.subset_union_left _ _)
  have closed' := fresh_instance_closed hc hf'
  have diB : (equalityTypes.support decl'.input).Subset B' := by
    change (equalityTypes.support _).Subset (Names.mk (decl.bound.types.image avoid.shiftTypes) (decl.bound.effects.image avoid.shiftEffects))
    rw [← bEq]
    exact ⟨fun _ hi => closed'.1 (Finset.mem_union_left _ hi),
      fun _ hi => closed'.2 (Finset.mem_union_left _ hi)⟩
  have doB : (equalityTypes.support decl'.output).Subset B' := by
    change (equalityTypes.support _).Subset (Names.mk (decl.bound.types.image avoid.shiftTypes) (decl.bound.effects.image avoid.shiftEffects))
    rw [← bEq]
    exact ⟨fun _ hi => closed'.1 (Finset.mem_union_right _ hi),
      fun _ hi => closed'.2 (Finset.mem_union_right _ hi)⟩
  have freshD : X.Avoids D B' := avoids_of_disjoint_support D B' (freshB0.mono_right dc0)
  have quant : X.Entails D (X.clause B' J' (X.subst η Q)) := by
    intro v hv
    apply clause_subst_underBinder θ decl.bound J Q avoid.shiftTypes avoid.shiftEffects
      avoid.shiftTypes_injective avoid.shiftEffects_injective bj
      (freshA.mono_right (Names.subset_union_right _ _))
    exact (X.holds_subst _ _ _).mpr (hclause _ ((X.holds_subst _ _ _).mp (entails v hv)))
  have ent : X.Entails D (X.existsNames J' (X.subst η Q)) := by
    intro v hv
    exact (X.holds_exists _ _ _).mpr
      ((X.holds_clause _ _ _ _).mp (quant v hv) v ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  obtain ⟨n, W, hn, protect, effects, fw, proj⟩ :=
    normal_project P cl allow lift hr truth admitted
      (avoids_of_disjoint_support D J' (freshJ0.mono_right dc0)) freshJF ent
  have adm : X.Admissible P.solved n.residual :=
    ⟨n.residual, hn.1, X.entails_refl _, X.entails_refl _⟩
  have fgA : g.Avoids A := by
    intro s hs
    have jg := scopeH.witness_scope.mono_right (Names.subset_union_left _ _)
    have freshJg := g.avoids_of_support_disjoint J jg
    constructor
    · intro i hi hf
      rcases Finset.mem_union.mp hi with hb | hj
      · exact (scopeH.context s hs).1 i hb hf
      · exact (freshJg s hs).1 i hj hf
    · intro i hi hf
      rcases Finset.mem_union.mp hi with hb | hj
      · exact (scopeH.context s hs).2 i hb hf
      · exact (freshJg s hs).2 i hj hf
  have envσ := binder_environment P.solved_satisfiable cl θ n.substitution
    avoid.shiftTypes avoid.shiftEffects env adm proj
    (avoids_of_disjoint_support D W (fw.mono_right dc)) fgA (fw.mono_right gc) (protect.mono_right gc)
  let σ := n.substitution.compose η
  have resultAvoid : A.Disjoint (equalityTypes.support result) := by
    have jb := scopeH.witness_scope.mono_right (show (equalityTypes.support result).Subset
      (g.support.union (((equalityTypes.support input).union (equalityTypes.support result)).union
        (((equalityTypes.support decl.input).union (equalityTypes.support decl.output)).union decl.bound))) from
      by constructor <;> intro i hi <;> simp [Names.union, hi])
    exact ⟨Finset.disjoint_union_left.mpr ⟨scopeH.rigid_types.1.mono_right Finset.subset_union_right, jb.1⟩,
      Finset.disjoint_union_left.mpr ⟨scopeH.rigid_types.2.mono_right Finset.subset_union_right, jb.2⟩⟩
  have outAvoid : Disjoint A.effects out.vars :=
    Finset.disjoint_union_left.mpr
      ⟨scopeH.rigid_effects.mono_right Finset.subset_union_right,
       scopeH.witness_effects.mono_right Finset.subset_union_right⟩
  have eqResult (v : Valuation GroundTy) :
      equalityTypes.eval v (σ.apply result) = equalityTypes.eval v (θ.apply result) :=
    external_term_eval θ n.substitution A avoid.shiftTypes avoid.shiftEffects result resultAvoid
      (protect.mono_right tc) v
  have eqOut (v : Valuation GroundTy) :
      (out.subst σ.effects).eval v.effects = (out.subst θ.effects).eval v.effects :=
    external_effect_eval θ n.substitution A avoid.shiftTypes avoid.shiftEffects out outAvoid effects v
  have eqDecl (v : Valuation GroundTy) :
      equalityTypes.eval v (σ.apply decl.input) = equalityTypes.eval v decl'.input ∧
      equalityTypes.eval v (σ.apply decl.output) = equalityTypes.eval v decl'.output := by
    have go (t t' : Ty) (he : ∀ v, equalityTypes.eval v (η.apply t) = equalityTypes.eval v t')
        (scopeT : (equalityTypes.support t').Subset B') :
        equalityTypes.eval v (σ.apply t) = equalityTypes.eval v t' := by
      rw [Substitution.eval_apply, Substitution.compose_pullback, ← Substitution.eval_apply, he]
      apply equalityTypes.eval_support
      constructor
      · intro i hi
        exact (n.substitution.pullback_outside v).1 i
          (fun h => Finset.disjoint_left.mp protect.1 h (Finset.mem_union_right _ (scopeT.1 hi)))
      · intro i hi
        exact (n.substitution.pullback_outside v).2 i
          (fun h => Finset.disjoint_left.mp protect.2 h (Finset.mem_union_right _ (scopeT.2 hi)))
    exact ⟨go decl.input decl'.input (fun v => (declEq v).1) diB,
      go decl.output decl'.output (fun v => (declEq v).2) doB⟩
  have eqArrow (v : Valuation GroundTy) :
      equalityTypes.eval v (σ.apply (Ty.arr decl.output out result)) =
      equalityTypes.eval v (Ty.arr decl'.output (out.subst θ.effects) (θ.apply result)) := by
    have hd := (eqDecl v).2
    have ht := eqResult v
    have he := eqOut v
    rw [σ.eval_apply v decl.output] at hd
    rw [σ.eval_apply v result] at ht
    rw [σ.eval_apply v (Ty.arr decl.output out result)]
    change GroundTy.arr (equalityTypes.eval (σ.pullback v) decl.output) (out.eval (σ.pullback v).effects) (equalityTypes.eval (σ.pullback v) result) = _
    rw [hd, ht]
    have he' : out.eval (σ.pullback v).effects = (out.subst θ.effects).eval v.effects := by
      simpa only [Effect.eval_subst, Substitution.pullback] using he
    rw [he']
    rfl
  let target : Context X := .mono (Ty.arr decl'.output (out.subst θ.effects) (θ.apply result)) ::
    .mono decl'.input :: g'
  have ecg := clause_environment σ _ _ _ _ envσ eqArrow (fun v => (eqDecl v).1)
  have solveQ : X.Entails n.residual (X.subst σ Q) := by
    intro v hv
    have h := (X.holds_subst _ _ _).mp (Constraints.NormalForm.reconstruct_entails X hn v hv)
    apply (X.holds_subst _ _ _).mpr
    rw [Substitution.compose_pullback]
    exact (X.holds_subst _ _ _).mp ((X.holds_and _ _ _).mp h).2
  have solved : X.Entails n.residual (X.subst σ d) := by
    intro v hv
    exact (X.holds_subst _ _ _).mpr
      ((X.holds_and _ _ _).mp ((X.holds_subst _ _ _).mp (solveQ v hv))).1
  have clauseTyped := ih σ n.residual target adm solved ecg
  have compare : X.Entails n.residual
      (X.and (X.le (σ.apply ct) (θ.apply result))
        (X.effectLe (eo.subst σ.effects) (out.subst θ.effects))) := by
    intro v hv
    have hq := ((X.holds_and _ _ _).mp ((X.holds_subst _ _ _).mp (solveQ v hv))).2
    obtain ⟨ht, he⟩ := (X.holds_and _ _ _).mp hq
    apply (X.holds_and _ _ _).mpr
    constructor
    · apply (X.holds_le _ _ _).mpr
      have h := (X.holds_le _ _ _).mp ht
      rw [← σ.eval_apply v ct, ← σ.eval_apply v result, eqResult v] at h
      exact h
    · apply (X.holds_effectLe _ _ _).mpr
      have h := (X.holds_effectLe _ _ _).mp he
      have h : (eo.subst σ.effects).eval v.effects ⊆ (out.subst σ.effects).eval v.effects := by
        simpa only [Effect.eval_subst, Substitution.pullback] using h
      rwa [eqOut v] at h
  have finalClause : X.Entails D (X.clause decl'.bound W
      (X.and n.residual (X.and (X.le (σ.apply ct) (θ.apply result))
        (X.effectLe (eo.subst σ.effects) (out.subst θ.effects))))) := by
    rw [bEq]
    intro v hv
    apply (X.holds_clause _ _ _ _).mpr
    intro w same
    have hw : X.holds D w := (X.holds_agreeOutside freshD same).mpr hv
    obtain ⟨z, hz, hR⟩ := (X.holds_exists _ _ _).mp (proj.1 w hw)
    exact ⟨z, hz, (X.holds_and _ _ _).mpr ⟨hR, compare z hR⟩⟩
  have externalScope : (g'.support.union
      (((equalityTypes.support (θ.apply input)).union (equalityTypes.support (θ.apply result))).union
      (((equalityTypes.support decl'.input).union (equalityTypes.support decl'.output)).union decl'.bound))).Subset F := by
    constructor <;> intro i hi
    · simp only [Names.union, Finset.mem_union] at hi
      rcases hi with hg | ((hi | hr) | ((hd | ho) | hb))
      · exact Finset.mem_union_left _ (g'c0.1 hg)
      · exact Finset.mem_union_left _ (ic0.1 hi)
      · exact tc.1 hr
      · exact Finset.mem_union_right _ (diB.1 hd)
      · exact Finset.mem_union_right _ (doB.1 ho)
      · exact Finset.mem_union_right _ (by simpa only [bEq] using hb)
    · simp only [Names.union, Finset.mem_union] at hi
      rcases hi with hg | ((hi | hr) | ((hd | ho) | hb))
      · exact Finset.mem_union_left _ (g'c0.2 hg)
      · exact Finset.mem_union_left _ (ic0.2 hi)
      · exact tc.2 hr
      · exact Finset.mem_union_right _ (diB.2 hd)
      · exact Finset.mem_union_right _ (doB.2 ho)
      · exact Finset.mem_union_right _ (by simpa only [bEq] using hb)
  have hge : g'.Avoids decl'.bound := by
    rw [bEq]; exact g'.avoids_of_support_disjoint B' (freshB0.mono_right g'c0)
  have hte : decl'.bound.Disjoint ((equalityTypes.support (θ.apply input)).union
      (equalityTypes.support (θ.apply result))) := by
    rw [bEq]; exact freshB0.mono_right (ic0.union tc0)
  have hee : Disjoint decl'.bound.effects ((ein.subst θ.effects).vars ∪
      (er.subst θ.effects).vars ∪ (rest.subst θ.effects).vars ∪ (out.subst θ.effects).vars) := by
    rw [bEq]; exact freshB0.2.mono_right ec0.2
  have hwe : Disjoint W.effects ((ein.subst θ.effects).vars ∪ (er.subst θ.effects).vars ∪
      (rest.subst θ.effects).vars ∪ (out.subst θ.effects).vars) :=
    fw.2.mono_right (ec0.2.trans Finset.subset_union_left)
  have split : X.Entails D (X.split op (ein.subst θ.effects) (rest.subst θ.effects)) := by
    intro v hv
    have h := hSplit _ ((X.holds_subst _ _ _).mp (entails v hv))
    simpa only [Constraints.split, X.holds_and, X.holds_effectLe, X.holds_lacks,
      Effect.eval_subst, Substitution.pullback, effect_eval_union, effect_eval_singleton] using h
  have effLe {e f : Effect} (h : X.Entails c (X.effectLe e f)) :
      X.Entails D (X.effectLe (e.subst θ.effects) (f.subst θ.effects)) := by
    intro v hv
    have h' := h _ ((X.holds_subst _ _ _).mp (entails v hv))
    simpa only [X.holds_effectLe, Effect.eval_subst, Substitution.pullback] using h'
  obtain ⟨tb, vb⟩ := bodyTyped
  obtain ⟨tr, vr⟩ := retTyped
  obtain ⟨tc, vc⟩ := clauseTyped
  exact ⟨.handle hs hc hf' hge hte hee (fw.mono_right externalScope)
      (avoids_of_disjoint_support D W (fw.mono_right dc)) hwe tb tr tc finalClause split
      (effLe hRest) (effLe hRet),
    admitted, env.admissible, trivial, vb, vr, vc⟩
end EHMX.HMX.Derivation

namespace EHMX.HMX.Derivation
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}
private theorem perform_arbitrary_substitution {sig : Signature T} {S : X.Formula → Prop}
    {D : X.Formula} {g : Context X} {arg : Expr} {op : Op} {raw : Operation T}
    {eff : Effect} (θ ζ : Substitution T)
    (found : sig op = some raw) (closed : raw.Closed)
    (body : Typing sig X S D g arg (.mono (θ.apply (ζ.apply raw.input)))
      (eff.subst θ.effects)) :
    Typing sig X S D g (.perform op arg) (.mono (θ.apply (ζ.apply raw.output)))
      ((Effect.singleton op ∪ eff).subst θ.effects) := by
  let σ := (θ.compose ζ).restrictTo raw.bound
  have evaluated (v : Valuation T.Value) (q : T.Term)
      (hq : (T.support q).Subset raw.bound) :
      T.eval v (σ.apply q) = T.eval v (θ.apply (ζ.apply q)) := by
    rw [Substitution.eval_apply, Substitution.eval_apply, Substitution.eval_apply]
    rw [← Substitution.compose_pullback]
    apply T.eval_support
    constructor
    · intro i hi
      simp [σ, Substitution.restrictTo, Substitution.pullback, hq.1 hi]
    · intro i hi
      simp [σ, Substitution.restrictTo, Substitution.pullback, hq.2 hi]
  have inputScope : (T.support raw.input).Subset raw.bound :=
    ⟨fun _ hi => closed.1 (Finset.mem_union_left _ hi),
     fun _ hi => closed.2 (Finset.mem_union_left _ hi)⟩
  have outputScope : (T.support raw.output).Subset raw.bound :=
    ⟨fun _ hi => closed.1 (Finset.mem_union_right _ hi),
     fun _ hi => closed.2 (Finset.mem_union_right _ hi)⟩
  have argTyped : Typing sig X S D g arg (.mono (σ.apply raw.input))
      (eff.subst θ.effects) := body.instance_mono (.sub (by
    intro v _
    apply (X.holds_le _ _ _).mpr
    rw [evaluated v raw.input inputScope]
    exact O.refl _))
  have root := argTyped.root
  obtain ⟨tree, valid⟩ := argTyped
  have performed : Typing sig X S D g (.perform op arg) (.mono (σ.apply raw.output))
      (Effect.singleton op ∪ eff.subst θ.effects) :=
    ⟨.perform σ found closed (Finset.Subset.refl _) (Finset.Subset.refl _) tree,
      root.1, root.2.1, trivial, valid⟩
  have converted : Typing sig X S D g (.perform op arg)
      (.mono (θ.apply (ζ.apply raw.output))) (Effect.singleton op ∪ eff.subst θ.effects) :=
    performed.instance_mono (.sub (by
      intro v _
      apply (X.holds_le _ _ _).mpr
      rw [evaluated v raw.output outputScope]
      exact O.refl _))
  apply converted.effectEq
  intro v _
  apply (X.holds_effectEq _ _ _).mpr
  simp only [Effect.eval_subst, effect_eval_union, effect_eval_singleton]
end EHMX.HMX.Derivation

namespace EHMX.HMX
namespace Derivation
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
/-- Rules used by reconstructed terms: all expression forms are allowed.
Only existential projection of a qualified result is excluded. -/
def UsesReconstructionRules {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}
    {sig : Signature T} {c g e s eff}
    (tree : Derivation sig X c g e s eff) : Prop :=
  match tree with
  | .var _ | .int _ | .bool _ => True
  | .lam body => UsesReconstructionRules body
  | .app f x => UsesReconstructionRules f ∧ UsesReconstructionRules x
  | .letVal _ v body => UsesReconstructionRules v ∧ UsesReconstructionRules body
  | .letMono _ v body => UsesReconstructionRules v ∧ UsesReconstructionRules body
  | .sub body _ => UsesReconstructionRules body
  | .forallIntro _ _ _ body => UsesReconstructionRules body
  | .forallElim _ _ _ body _ => UsesReconstructionRules body
  | .weaken body _ => UsesReconstructionRules body
  | .effectEq body _ => UsesReconstructionRules body
  | .alpha body _ => UsesReconstructionRules body
  | @Derivation.existsIntro _ _ _ _ _ _ _ _ s _ _ _ _ body =>
      (∃ t, s = .mono t) ∧ UsesReconstructionRules body
  | .perform _ _ _ _ _ body => UsesReconstructionRules body
  | .handle _ _ _ _ _ _ _ _ _ body ret clause _ _ _ _ =>
      UsesReconstructionRules body ∧ UsesReconstructionRules ret ∧ UsesReconstructionRules clause

/-- Strong induction statement: substitute the original derivation's premises,
then transform under any admissible entailing constraint. Induction is on the
original tree; no size bound on regenerated derivations is assumed. -/
theorem transform_to_solved_subst_reconstruction {sig : Signature equalityTypes}
    (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    {c : X.Formula} {g : Context X} {e : Expr} {s : Scheme X} {eff : Effect}
    (tree : Derivation sig X c g e s eff) :
    UsesReconstructionRules tree →
    ∀ (θ : Substitution equalityTypes) (D : X.Formula) (g' : Context X),
      X.Admissible P.solved D → X.Entails D (X.subst θ c) →
      (g.subst θ).Approximates P.solved D g' →
      ∃ s', Typing sig X P.solved D g' e s' (eff.subst θ.effects) ∧
        (s.subst θ).Approximates P.solved D s' := by
  induction tree with
  | @var c g i s found =>
    intro _ θ D g' admitted entails env
    have lookup : (g.subst θ)[i]? = some (s.subst θ) := by
      simp only [Context.subst, List.getElem?_map, found, Option.map_some]
    obtain ⟨s', found', approx⟩ := env.lookup lookup
    refine ⟨s', ?_, approx⟩
    rw [empty_subst]
    exact ⟨.var found', admitted, env.admissible, approx.1, trivial⟩
  | @int c g n =>
    intro _ θ D g' admitted entails env
    refine ⟨.mono (θ.apply (equalityTypes.literal .int)), ?_, mono_approx _⟩
    rw [empty_subst]
    exact ⟨.int n, admitted, env.admissible, trivial, trivial⟩
  | @bool c g b =>
    intro _ θ D g' admitted entails env
    refine ⟨.mono (θ.apply (equalityTypes.literal .bool)), ?_, mono_approx _⟩
    rw [empty_subst]
    exact ⟨.bool b, admitted, env.admissible, trivial, trivial⟩
  | @lam c g e a b eff body ih =>
    intro core θ D g' admitted entails env
    obtain ⟨s', typed, approx⟩ := ih core θ D (.mono (θ.apply a) :: g')
      admitted entails (.cons (mono_approx _) env)
    obtain ⟨bt, bv⟩ := as_mono typed approx
    refine ⟨.mono (θ.apply (equalityTypes.arrow a eff b)), ?_, mono_approx _⟩
    rw [empty_subst]
    exact ⟨.lam bt, admitted, env.admissible, trivial, bv⟩
  | @app c g f x a b ef ex latent fn arg ihf ihx =>
    intro core θ D g' admitted entails env
    obtain ⟨fs, ft, fa⟩ := ihf core.1 θ D g' admitted entails env
    obtain ⟨xs, xt, xa⟩ := ihx core.2 θ D g' admitted entails env
    obtain ⟨fd, fv⟩ := as_mono ft fa
    obtain ⟨xd, xv⟩ := as_mono xt xa
    refine ⟨.mono (θ.apply b), ?_, mono_approx _⟩
    simp only [union_subst]
    exact ⟨.app fd xd, admitted, env.admissible, trivial, fv, xv⟩
  | @letVal c g v e s t eff value val body ihv ihb =>
    intro core θ D g' admitted entails env
    obtain ⟨vs, vt, va⟩ := ihv core.1 θ D g' admitted entails env
    obtain ⟨bs, bt, ba⟩ := ihb core.2 θ D (vs :: g') admitted entails (.cons va env)
    obtain ⟨vd, vv⟩ := (show Typing sig X P.solved D g' v vs ∅ from by
      simpa only [empty_subst] using vt)
    obtain ⟨bd, bv⟩ := as_mono bt ba
    exact ⟨.mono (θ.apply t), ⟨.letVal value vd bd, admitted, env.admissible,
      trivial, vv, bv⟩, mono_approx _⟩
  | @letMono c g v e a b ev ee value val body ihv ihb =>
    intro core θ D g' admitted entails env
    obtain ⟨vs, vt, va⟩ := ihv core.1 θ D g' admitted entails env
    obtain ⟨bs, bt, ba⟩ := ihb core.2 θ D (.mono (θ.apply a) :: g')
      admitted entails (.cons (mono_approx _) env)
    obtain ⟨vd, vv⟩ := as_mono vt va
    obtain ⟨bd, bv⟩ := as_mono bt ba
    refine ⟨.mono (θ.apply b), ?_, mono_approx _⟩
    rw [union_subst]
    exact ⟨.letMono value vd bd, admitted, env.admissible, trivial, vv, bv⟩
  | @sub c g e a b eff body le ih =>
    intro core θ D g' admitted entails env
    obtain ⟨s', typed, approx⟩ := ih core θ D g' admitted entails env
    have inst := ((Instance.sub le).subst θ).weaken entails
    exact ⟨.mono (θ.apply b), typed.instance_mono
      (approx.2.2 (.mono (θ.apply b)) trivial inst), mono_approx _⟩
  | @forallIntro c d g e a t value freshC freshG body ih =>
    intro core θ D g' admitted entails env
    obtain ⟨s', typed, approx⟩ := forallIntro_arbitrary_substitution X P closure allow lift
      hr truth value freshC freshG θ admitted entails env
      (fun σ q target => ih core σ q target)
    refine ⟨s', ?_, approx⟩
    simpa only [empty_subst] using typed
  | @forallElim c d g e a t eff ζ ht he body ent ih =>
    intro core θ D g' admitted entails env
    obtain ⟨s', typed, approx⟩ := ih core θ D g' admitted entails env
    have inst : Instance X c (.qualified a d t) (.mono (ζ.apply t)) :=
      .forallLeft ζ ht he ent (mono_approx (S := P.solved) _).2.1
    have subinst := (inst.subst θ).weaken entails
    exact ⟨.mono (θ.apply (ζ.apply t)), typed.instance_mono
      (approx.2.2 (.mono (θ.apply (ζ.apply t))) trivial subinst), mono_approx _⟩
  | @weaken c d g e s eff body ent ih =>
    intro core θ D g' admitted entails env
    apply ih core θ D g' admitted _ env
    intro v hv
    exact (X.holds_subst _ _ _).mpr (ent _ ((X.holds_subst _ _ _).mp (entails v hv)))
  | @effectEq c g e s eff eff' body eq ih =>
    intro core θ D g' admitted entails env
    obtain ⟨s', typed, approx⟩ := ih core θ D g' admitted entails env
    have eq' : X.Entails D (X.effectEq (eff.subst θ.effects) (eff'.subst θ.effects)) := by
      intro v hv
      have old := eq _ ((X.holds_subst _ _ _).mp (entails v hv))
      simpa only [Constraints.effectEq, X.holds_and, X.holds_effectLe,
        Effect.eval_subst, Substitution.pullback] using old
    obtain ⟨td, tv⟩ := typed
    exact ⟨s', ⟨.effectEq td eq', admitted, env.admissible, approx.1, tv⟩, approx⟩
  | @alpha c g e s s' eff body alpha ih =>
    intro core θ D g' admitted entails env
    obtain ⟨target, typed, approx⟩ := ih core θ D g' admitted entails env
    exact ⟨target, typed, alpha_source alpha θ approx⟩
  | @existsIntro c g e a s eff fg fs fe body ih =>
    intro core θ D g' admitted entails env
    obtain ⟨⟨t, rfl⟩, good⟩ := core
    refine ⟨.mono (θ.apply t), ?_, mono_approx _⟩
    apply existsIntro_arbitrary_substitution P closure allow lift hr truth fg fs fe θ admitted entails env
    intro σ R target adm ent en
    obtain ⟨s', typed, approx⟩ := ih good σ R target adm ent en
    exact as_mono typed approx
  | @perform c g op raw arg eff ζ hs hc ht he body ih =>
    intro core θ D g' admitted entails env
    obtain ⟨s', typed, approx⟩ := ih core θ D g' admitted entails env
    exact ⟨.mono (θ.apply (ζ.apply raw.output)),
      perform_arbitrary_substitution θ ζ hs hc (as_mono typed approx), mono_approx _⟩
  | @handle c d g body op ret clause raw decl input result ct ein er eo rest out J
      hs hc hf fg ft fe fw fwc fwe btree rtree ctree hcl hspl hrst hret ihb ihr ihc =>
    intro core θ D g' admitted entails env
    obtain ⟨bs, bt, ba⟩ := ihb core.1 θ D g' admitted entails env
    obtain ⟨rs, rt, ra⟩ := ihr core.2.1 θ D (.mono (θ.apply input) :: g')
      admitted entails (.cons (mono_approx _) env)
    refine ⟨.mono (θ.apply result), ?_, mono_approx _⟩
    apply handler_arbitrary_substitution P closure allow lift hr truth hs hc hf
      ⟨fg, ft, fe, fw, fwc, fwe⟩ hcl hspl hrst hret θ admitted entails env
      (as_mono bt ba) (as_mono rt ra)
    intro σ R target adm ent en
    obtain ⟨s', typed, approx⟩ := ihc core.2.2 σ R target adm ent en
    exact as_mono typed approx

/-- Every derivation in the original thirteen-rule fragment is also covered
by reconstruction soundness. -/
theorem UsesHMXRules.reconstruction {sig : Signature equalityTypes}
    {c g e s eff} {tree : Derivation sig X c g e s eff}
    (h : UsesHMXRules tree) : UsesReconstructionRules tree := by
  induction tree <;> simp_all [UsesHMXRules, UsesReconstructionRules]

/-- Compatibility entry point for the original thirteen-rule fragment. -/
theorem transform_to_solved_subst {sig : Signature equalityTypes}
    (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    {c : X.Formula} {g : Context X} {e : Expr} {s : Scheme X} {eff : Effect}
    (tree : Derivation sig X c g e s eff) :
    UsesHMXRules tree →
    ∀ (θ : Substitution equalityTypes) (D : X.Formula) (g' : Context X),
      X.Admissible P.solved D → X.Entails D (X.subst θ c) →
      (g.subst θ).Approximates P.solved D g' →
      ∃ s', Typing sig X P.solved D g' e s' (eff.subst θ.effects) ∧
        (s.subst θ).Approximates P.solved D s' := by
  intro core
  exact transform_to_solved_subst_reconstruction P closure allow lift hr truth tree core.reconstruction


end Derivation
end EHMX.HMX
namespace EHMX.HMX
namespace Derivation
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}

/-- Conditional counterpart of HM(X) Theorem 7 for the current value-restricted
calculus and constraint-relative approximation. The source must use only
UsesHMXRules. Scoped principality, solved closure, effect-equation closure,
projection lifting and a true solved residual are explicit hypotheses.
No uniform realizability of internal schemes or contexts is required.
This does not establish these hypotheses for a concrete solver. -/
theorem theorem7_core {sig : Signature equalityTypes}
    (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    {c : X.Formula} {g g' : Context X} {e : Expr} {s : Scheme X} {eff : Effect}
    (tree : Derivation sig X c g e s eff) (core : UsesHMXRules tree)
    (admitted : X.Admissible P.solved c) (env : g.Approximates P.solved c g') :
    ∃ s', Typing sig X P.solved c g' e s' eff ∧ s.Approximates P.solved c s' := by
  have entails : X.Entails c (X.subst (Substitution.identity equalityTypes) c) := by
    intro v hv
    simpa only [X.holds_subst, Substitution.identity_pullback] using hv
  obtain ⟨s', typed, approx⟩ := transform_to_solved_subst P closure allow lift hr truth tree core
    (Substitution.identity equalityTypes) c g' admitted entails
    (Context.Approximates.subst_identity env)
  have empty : eff.subst (Substitution.identity equalityTypes).effects = eff :=
    Effect.subst_eq_self _ _ (fun _ _ => rfl)
  rw [empty] at typed
  exact ⟨s', typed, (Scheme.Approximates.subst_identity_iff s s').mp approx⟩

/-- Monotype conclusion of Theorem 7: retain exactly the original type and effect.
The same explicit hypotheses and source-rule restriction as theorem7_core apply. -/
theorem theorem7_mono_core {sig : Signature equalityTypes}
    (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    {c : X.Formula} {g g' : Context X} {e : Expr} {t : Ty} {eff : Effect}
    (tree : Derivation sig X c g e (.mono t) eff) (core : UsesHMXRules tree)
    (admitted : X.Admissible P.solved c) (env : g.Approximates P.solved c g') :
    Typing sig X P.solved c g' e (.mono t) eff := by
  obtain ⟨s', typed, approx⟩ := theorem7_core P closure allow lift hr truth tree core admitted env
  exact as_mono typed approx



end Derivation
end EHMX.HMX
