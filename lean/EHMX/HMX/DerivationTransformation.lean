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

private theorem context_project {S : X.Formula → Prop}
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

/-- Strong induction statement: substitute the original derivation's premises,
then transform under any admissible entailing constraint. Induction is on the
original tree; no size bound on regenerated derivations is assumed. -/
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
  | existsIntro => intro core; exact False.elim core
  | perform => intro core; exact False.elim core
  | handle => intro core; exact False.elim core


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
