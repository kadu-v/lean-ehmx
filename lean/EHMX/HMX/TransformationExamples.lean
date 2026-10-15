import EHMX.HMX.DerivationTransformation


/-! Applications of the public conditional transformation theorem.
The normalizer assumptions remain explicit; these examples do not supply a
complete solver for the effect-only residual language. -/

namespace EHMX.HMX.TransformationExamples
open EHMX EHMX.HMX
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
private abbrev sig : Signature equalityTypes := fun _ => none
private def bound : Names := ⟨{1}, ∅⟩
private def polyId : Scheme X := .qualified bound X.top (.arr (.var 1) ∅ (.var 1))

private def polyTree (g : Context X) (fresh : g.Avoids bound) :
    Derivation sig X X.top g (.lam (.var 0)) polyId ∅ :=
  .weaken (.forallIntro (.lam _) (X.top_avoids bound) fresh (.lam (.var rfl)))
    (by
      intro v hv
      exact (X.holds_and _ _ _).mpr ⟨hv, X.exists_intro bound X.top v hv⟩)

private def intInstance : Substitution equalityTypes where
  domain := bound
  types := fun i => if i = 1 then .base .int else .var i
  effects := Effect.var
  types_outside := by intro i hi; simp [bound] at hi; simp [hi]
  effects_outside := by intros; rfl

private theorem polyFresh : (polyId (X := X)).Avoids bound :=
  ⟨fun _ hi hf => hf.1 hi, fun _ hi hf => hf.1 hi⟩

private def nestedLetTree (g : Context X) (fresh : g.Avoids bound) :
    Derivation sig X X.top g
      (.letE (.lam (.var 0)) (.letE (.lam (.var 0)) (.app (.var 0) (.int 1))))
      (.mono (.base .int)) ∅ := by
  have fresh' : Context.Avoids (polyId :: g) bound := by
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact polyFresh
    · exact fresh s hs
  let fn : Derivation sig X X.top (polyId :: polyId :: g) (.var 0)
      (.mono (.arr (.base .int) ∅ (.base .int))) ∅ :=
    .forallElim (t := Ty.arr (.var 1) ∅ (.var 1)) intInstance
      (fun _ h => h) (fun _ h => h) (.var rfl)
      (by intro v _; exact (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial))
  let app := Derivation.app fn (.int 1)
  have body : Derivation sig X X.top (polyId :: polyId :: g)
      (.app (.var 0) (.int 1)) (.mono (.base .int)) ∅ :=
    .effectEq app (by
      intro v _
      simp [Constraints.effectEq, X.holds_and, X.holds_effectLe, Effect.eval])
  exact .letVal (.lam _) (polyTree g fresh)
    (.letVal (.lam _) (polyTree (polyId :: g) fresh') body)

private theorem nestedLet_rules (g : Context X) (fresh : g.Avoids bound) :
    (nestedLetTree g fresh).UsesHMXRules := by
  simp [nestedLetTree, polyTree, Derivation.UsesHMXRules]

private def capture : Substitution equalityTypes where
  domain := ⟨{0}, ∅⟩
  types := fun i => if i = 0 then .var 1 else .var i
  effects := Effect.var
  types_outside := by intro i hi; simp at hi; simp [hi]
  effects_outside := by intros; rfl

section Conditional
variable (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)

include hr truth in
private theorem topAdm : X.Admissible P.solved X.top :=
  ⟨r, hr, fun v _ => truth v, fun v _ => (X.holds_top v).mpr trivial⟩

include closure reflect allow lift hr truth

/-- Two value lets introduce qualified identities; the inner identity is
specialized and applied. No internal Realizable premise is supplied. -/
theorem nested_polymorphic_let :
    Typing sig X P.solved X.top []
      (.letE (.lam (.var 0)) (.letE (.lam (.var 0)) (.app (.var 0) (.int 1))))
      (.mono (.base .int)) ∅ :=
  EHMX.HMX.Derivation.theorem7_mono_core P closure reflect allow lift hr truth
    (nestedLetTree [] (by intro s hs; cases hs))
    (nestedLet_rules [] _) (topAdm P hr truth) .nil

/-- The outer substitution maps free type 0 to the old bound name 1.
Generalization must choose fresh names in the presence of the open environment. -/
theorem open_context_capture :
    ∃ s', Typing sig X P.solved X.top [.mono (.var 1)] (.lam (.var 0)) s' ∅ ∧
      ((polyId (X := X)).subst capture).Approximates P.solved X.top s' := by
  have fresh : Context.Avoids ([.mono (.var 0)] : Context X) bound := by
    intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    simp [Scheme.Avoids, Scheme.FreeType, Scheme.FreeEffect, bound, Ty.fvTypes, Ty.fvEffects]
  have env : Context.Approximates P.solved X.top
      (Context.subst capture [.mono (.var 0)]) [.mono (.var 1)] := by
    exact .cons (Scheme.Approximates.refl_of_ground trivial
      (fun v _ => ⟨v.types 1, O.refl _⟩)) .nil
  have result := EHMX.HMX.Derivation.transform_to_solved_subst P closure reflect allow lift hr truth
    (polyTree [.mono (.var 0)] fresh)
    (by simp [polyTree, Derivation.UsesHMXRules]) capture X.top [.mono (.var 1)]
    (topAdm P hr truth) (by intro v _; exact (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial)) env
  have empty : (∅ : Effect).subst capture.effects = ∅ :=
    Effect.subst_eq_self _ _ (by simp)
  simpa only [empty] using result

/-- A nonempty latent effect and an open monomorphic variable retain the exact
type and effect through the public monotype theorem. -/
theorem preserves_latent_effect (eff : Effect) :
    Typing sig X P.solved X.top
      [.mono (.arr (.base .int) eff (.base .int))]
      (.app (.var 0) (.int 1)) (.mono (.base .int)) eff := by
  let tree : Derivation sig X X.top
      [.mono (.arr (.base .int) eff (.base .int))]
      (.app (.var 0) (.int 1)) (.mono (.base .int)) ((∅ ∪ ∅) ∪ eff) :=
    .app (.var rfl) (.int 1)
  have env : Context.Approximates P.solved X.top
      [.mono (.arr (.base .int) eff (.base .int))]
      [.mono (.arr (.base .int) eff (.base .int))] :=
    .cons (Scheme.Approximates.refl_of_ground trivial
      (fun v _ => ⟨equalityTypes.eval v (.arr (.base .int) eff (.base .int)), O.refl _⟩)) .nil
  have result := EHMX.HMX.Derivation.theorem7_mono_core P closure reflect allow lift hr truth tree
    (by trivial) (topAdm P hr truth) env
  have empty : ((∅ : Effect) ∪ ∅) ∪ eff = eff :=
    (congrArg (fun e => e ∪ eff) (Effect.empty_union Effect.empty)).trans
      (Effect.empty_union eff)
  rw [empty] at result
  exact result
end Conditional
end EHMX.HMX.TransformationExamples



namespace EHMX.HMX
namespace TransformationExamples.EffectResiduals
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

/-- Compatibility aliases for the residual model now used by reconstruction. -/
abbrev EffectOnly := EHMX.HMX.EffectResiduals.EffectOnly X
abbrev Solved := EHMX.HMX.EffectResiduals.Solved X

theorem effect_bound_solved :
    Solved X (X.effectLe (Effect.var 0) (Effect.singleton 0)) := by
  constructor
  · obtain ⟨t⟩ := T.value_nonempty
    exact ⟨⟨fun _ => t, fun _ => ∅⟩,
      (X.holds_effectLe _ _ _).mpr (by simp [Effect.eval, Effect.var, Effect.singleton])⟩
  · intro v w same
    simp only [X.holds_effectLe, same]

theorem effect_graph_allowed {r : X.Formula} {s : Substitution T}
    (typesEmpty : s.domain.types = ∅)
    (admitted : X.Admissible (Solved X) r)
    (sat : X.Satisfiable (X.and r (X.substitutionConstraint s))) :
    X.Admissible (Solved X) (X.and r (X.substitutionConstraint s)) :=
  EHMX.HMX.EffectResiduals.effect_graph_allowed X typesEmpty admitted sat

theorem identity_is_principal {S : X.Formula → Prop} {d : X.Formula}
    (solved : S d) (u : Names) :
    (⟨d, Substitution.identity T⟩ : X.NormalForm).IsPrincipalOn u S d := by
  refine ⟨⟨solved, Substitution.identity_solved T, ⟨?_, ?_⟩, X.entails_left _ _⟩, ?_⟩
  · intro v hv; simpa only [X.holds_subst, Substitution.identity_pullback] using hv
  · intro v hv; simpa only [X.holds_subst, Substitution.identity_pullback] using hv
  · intro m hm
    refine ⟨m.substitution, ?_⟩
    intro v hv
    refine ⟨?_, (X.holds_subst _ _ _).mp (Constraints.NormalForm.reconstruct_entails X hm v hv)⟩
    rw [Substitution.identity_pullback]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem effect_bound_has_principal (u : Names) :
    (⟨X.effectLe (Effect.var 0) (Effect.singleton 0), Substitution.identity T⟩ :
      X.NormalForm).IsPrincipalOn u (Solved X)
        (X.effectLe (Effect.var 0) (Effect.singleton 0)) :=
  identity_is_principal X (effect_bound_solved X) u

theorem ordinary_type_equation_rejected
    {O : TypeOrder equalityTypes} (X : Constraints equalityTypes O) :
    ¬ Solved X (X.eq (Ty.var 0) (Ty.base .int)) := by
  intro h
  let v : Valuation GroundTy := ⟨fun _ => .atom 0, fun _ => ∅⟩
  let w : Valuation GroundTy := ⟨fun _ => .atom 1, fun _ => ∅⟩
  have hv : X.holds (X.eq (.var 0) (.base .int)) v :=
    (X.holds_eq _ _ _).mpr rfl
  have hw := (h.2 v w rfl).mp hv
  have bad := (X.holds_eq _ _ _).mp hw
  change GroundTy.atom 1 = GroundTy.atom 0 at bad
  cases bad




end TransformationExamples.EffectResiduals
end EHMX.HMX
