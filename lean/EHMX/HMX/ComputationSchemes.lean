import EHMX.HMX.GroundInstances

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

/-- Generalization of a whole inference result, not a value usable at a let.
Keeping this separate preserves the language's value restriction. -/
structure ComputationScheme (X : Constraints T O) where
  bound : Names
  condition : X.Formula
  result : T.Term
  effect : Effect

def ComputationScheme.support {X : Constraints T O} (s : ComputationScheme X) : Names :=
  (((X.support s.condition).union (T.support s.result)).union ⟨∅, s.effect.vars⟩).diff s.bound

def ComputationScheme.GroundInstance {X : Constraints T O}
    (s : ComputationScheme X) (v : Valuation T.Value) (t : T.Value) (eff : Finset Op) : Prop :=
  ∃ w, w.AgreeOutside v s.bound ∧ X.holds s.condition w ∧
    O.le (T.eval w s.result) t ∧ s.effect.eval w.effects = eff

/-- A single finite substitution works for all valuations of the target
judgment. This is stronger than inclusion of ground instances. -/
def ComputationScheme.FiniteInstance {X : Constraints T O}
    (s : ComputationScheme X) (c : X.Formula) (t : T.Term) (eff : Effect) : Prop :=
  ∃ θ : Substitution T, θ.domain.types ⊆ s.bound.types ∧ θ.domain.effects ⊆ s.bound.effects ∧
    ∀ v, X.holds c v → X.holds s.condition (θ.pullback v) ∧
      O.le (T.eval (θ.pullback v) s.result) (T.eval v t) ∧
      s.effect.eval (θ.pullback v).effects = eff.eval v.effects

theorem ComputationScheme.FiniteInstance.ground {X : Constraints T O}
    {s : ComputationScheme X} {c : X.Formula} {t : T.Term} {eff : Effect}
    (h : s.FiniteInstance c t eff) (v : Valuation T.Value) (hv : X.holds c v) :
    s.GroundInstance v (T.eval v t) (eff.eval v.effects) := by
  obtain ⟨θ, ht, he, h⟩ := h
  exact ⟨θ.pullback v,
    ⟨fun i hi => (θ.pullback_outside v).1 i (fun hj => hi (ht hj)),
      fun i hi => (θ.pullback_outside v).2 i (fun hj => hi (he hj))⟩, h v hv⟩

/-- Finite computation instances yield the declarative scheme-instance
judgment; the immediate effect is checked separately by computation typing. -/
theorem ComputationScheme.FiniteInstance.instance {X : Constraints T O}
    {s : ComputationScheme X} {c : X.Formula} {t : T.Term} {eff : Effect}
    (h : s.FiniteInstance c t eff) :
    Instance X c (.qualified s.bound s.condition s.result) (.mono t) := by
  obtain ⟨θ, ht, he, h⟩ := h
  refine .forallLeft θ ht he (fun v hv => (X.holds_subst _ _ v).mpr (h v hv).1) (.sub ?_)
  intro v hv
  exact (X.holds_le _ _ v).mpr (by simpa only [θ.eval_apply] using (h v hv).2.1)

def ComputationScheme.generalize {X : Constraints T O}
    (g : Context X) (c : X.Formula) (t : T.Term) (eff : Effect) : ComputationScheme X :=
  ⟨(((X.support c).union (T.support t)).union ⟨∅, eff.vars⟩).diff g.support, c, t, eff⟩

theorem ComputationScheme.generalize_finite {X : Constraints T O}
    (g : Context X) (r : X.Formula) (t : T.Term) (eff : Effect)
    (hg : g.support = Names.empty) (σ : Substitution T)
    {c : X.Formula} {target : T.Term} {out : Effect}
    (h : ∀ v, X.holds c v → X.holds r (σ.pullback v) ∧
      O.le (T.eval (σ.pullback v) t) (T.eval v target) ∧
      eff.eval (σ.pullback v).effects = out.eval v.effects) :
    (ComputationScheme.generalize g r t eff).FiniteInstance c target out := by
  let a := (ComputationScheme.generalize g r t eff).bound
  have ha : a = ((X.support r).union (T.support t)).union ⟨∅, eff.vars⟩ := by
    simp [a, ComputationScheme.generalize, hg, Names.diff, Names.empty]
  let τ : Substitution T := {
    domain := a
    types := fun i => if i ∈ a.types then σ.types i else T.var i
    effects := fun i => if i ∈ a.effects then σ.effects i else Effect.var i
    types_outside := by intro i hi; simp [hi]
    effects_outside := by intro i hi; simp [hi] }
  refine ⟨τ, fun _ hi => hi, fun _ hi => hi, ?_⟩
  intro v hv
  have agree : (τ.pullback v).AgreeOn (σ.pullback v) a := by
    constructor <;> intro i hi <;> simp [τ, Substitution.pullback, hi]
  rw [ha] at agree
  have hr := X.holds_support r (τ.pullback v) (σ.pullback v)
    (agree.mono ((Names.subset_union_left _ _).trans (Names.subset_union_left _ _)))
  have ht := T.eval_support (τ.pullback v) (σ.pullback v) t
    (agree.mono ((Names.subset_union_right _ _).trans (Names.subset_union_left _ _)))
  have he : eff.eval (τ.pullback v).effects = eff.eval (σ.pullback v).effects := by
    unfold Effect.eval
    congr 1
    exact Finset.biUnion_congr rfl (fun i hi => agree.2 i (Finset.mem_union_right _ hi))
  exact ⟨hr.mpr (h v hv).1, ht.symm ▸ (h v hv).2.1, he.trans (h v hv).2.2⟩

/-- A scoped comparison factor gives one finite computation instance, uniformly
in the target residual's valuations. Only the result type and effect need to be
observed. This compares normal-form outputs; it does not assert coverage of all
satisfiability-based typings under arbitrary target constraints. -/
theorem ComputationScheme.generalize_finite_of_moreGeneralOn {X : Constraints T O}
    (g : Context X) (hg : g.support = Names.empty)
    {u : Names} {n m : X.NormalForm} (h : n.MoreGeneralOn u m)
    (t : T.Term) (eff : Effect)
    (ht : (T.support t).Subset u) (he : eff.vars ⊆ u.effects) :
    (ComputationScheme.generalize g n.residual
      (n.substitution.apply t) (eff.subst n.substitution.effects)).FiniteInstance
      m.residual (m.substitution.apply t) (eff.subst m.substitution.effects) := by
  obtain ⟨φ, factor, residual⟩ := h
  apply ComputationScheme.generalize_finite g _ _ _ hg φ
  intro v hv
  refine ⟨(X.holds_subst _ _ v).mp (residual v hv), ?_, ?_⟩
  · rw [Substitution.eval_apply, Substitution.eval_apply,
      T.eval_support _ _ t ((factor v).mono ht)]
    exact O.refl _
  · rw [Effect.eval_subst, Effect.eval_subst]
    exact Effect.eval_support eff _ _ (fun i hi => (factor v).2 i (he hi))

/-- Finite-observation principality covers every competing normal form by a
single finite substitution, without ground representatives or `canonical`. -/
theorem ComputationScheme.generalize_finite_of_principalOn {X : Constraints T O}
    (g : Context X) (hg : g.support = Names.empty)
    {u : Names} {solved : X.Formula → Prop} {d : X.Formula} {n m : X.NormalForm}
    (hn : n.IsPrincipalOn u solved d) (hm : m.IsNormal solved d)
    (t : T.Term) (eff : Effect)
    (ht : (T.support t).Subset u) (he : eff.vars ⊆ u.effects) :
    (ComputationScheme.generalize g n.residual
      (n.substitution.apply t) (eff.subst n.substitution.effects)).FiniteInstance
      m.residual (m.substitution.apply t) (eff.subst m.substitution.effects) :=
  ComputationScheme.generalize_finite_of_moreGeneralOn g hg (hn.2 m hm) t eff ht he

/-- Admissible target constraints yield uniform finite coverage of the observed
input type and effect. This replaces ground witnesses by an actual comparison
factor, but requires an entailment into the input constraint. -/
theorem ComputationScheme.generalize_finite_of_admissible {X : Constraints T O}
    (g : Context X) (hg : g.support = Names.empty)
    {u : Names} {solved : X.Formula → Prop} {c d : X.Formula} {n : X.NormalForm}
    (hn : n.IsPrincipalOn u solved d) (hc : X.Admissible solved c)
    (entails : X.Entails c d) (t : T.Term) (eff : Effect)
    (ht : (T.support t).Subset u) (he : eff.vars ⊆ u.effects) :
    (ComputationScheme.generalize g n.residual
      (n.substitution.apply t) (eff.subst n.substitution.effects)).FiniteInstance c t eff := by
  obtain ⟨φ, factor, residual⟩ := hn.factor_admissible X hc entails
  apply ComputationScheme.generalize_finite g _ _ _ hg φ
  intro v hv
  refine ⟨(X.holds_subst _ _ v).mp (residual v hv), ?_, ?_⟩
  · rw [Substitution.eval_apply, T.eval_support _ _ t ((factor v).mono ht)]
    exact O.refl _
  · rw [Effect.eval_subst]
    exact Effect.eval_support eff _ _ (fun i hi => (factor v).2 i (he hi))

/-- Uniform target substitutions can be transferred through scoped
normalization when they form a competing normal form. Neither their solvedness
nor invariance of the target constraint follows from arbitrary finite coverage;
both obligations remain explicit here. -/
theorem ComputationScheme.generalize_finite_of_admissible_substitution
    {X : Constraints T O} (g : Context X) (hg : g.support = Names.empty)
    {u : Names} {solved : X.Formula → Prop} {c d : X.Formula} {n : X.NormalForm}
    (hn : n.IsPrincipalOn u solved d) (hc : X.Admissible solved c)
    (σ : Substitution T) (hσ : σ.Solved)
    (invariant : X.Equivalent (X.subst σ c) c)
    (entails : X.Entails c (X.subst σ d)) (t : T.Term) (eff : Effect)
    (ht : (T.support t).Subset u) (he : eff.vars ⊆ u.effects) :
    (ComputationScheme.generalize g n.residual
      (n.substitution.apply t) (eff.subst n.substitution.effects)).FiniteInstance
      c (σ.apply t) (eff.subst σ.effects) := by
  obtain ⟨φ, factor, residual⟩ := hn.factor_admissible_substitution X hc σ hσ invariant entails
  apply ComputationScheme.generalize_finite g _ _ _ hg φ
  intro v hv
  refine ⟨(X.holds_subst _ _ v).mp (residual v hv), ?_, ?_⟩
  · rw [Substitution.eval_apply, Substitution.eval_apply,
      T.eval_support _ _ t ((factor v).mono ht)]
    exact O.refl _
  · rw [Effect.eval_subst, Effect.eval_subst]
    exact Effect.eval_support eff _ _ (fun i hi => (factor v).2 i (he hi))

/-- Fresh output slots turn a concrete target type and effect into a solved
competitor. Constraint invariance follows from freshness, rather than being a
separate assumption. Obtaining fresh slots for an existing principal form and
the entailment from a typing derivation are separate obligations. -/
theorem ComputationScheme.generalize_finite_of_fresh_outputs
    {X : Constraints T O} (g : Context X) (hg : g.support = Names.empty)
    {u : Names} {solved : X.Formula → Prop} {c d : X.Formula} {n : X.NormalForm}
    (hn : n.IsPrincipalOn u solved d) (hc : X.Admissible solved c)
    (a b : Nat) (ha : a ∈ u.types) (hb : b ∈ u.effects)
    (t : T.Term) (eff : Effect)
    (freshC : X.Avoids c ⟨{a}, {b}⟩)
    (freshT : (Names.mk {a} {b}).Disjoint (T.support t))
    (freshE : b ∉ eff.vars)
    (entails : X.Entails c (X.subst (Substitution.outputs a b t eff) d)) :
    (ComputationScheme.generalize g n.residual
      (n.substitution.types a) (n.substitution.effects b)).FiniteInstance c t eff := by
  let σ := Substitution.outputs a b t eff
  have invariant : X.Equivalent (X.subst σ c) c := by
    constructor <;> intro v hv
    · exact (X.holds_agreeOutside freshC (σ.pullback_outside v)).mp
        ((X.holds_subst _ _ v).mp hv)
    · exact (X.holds_subst _ _ v).mpr
        ((X.holds_agreeOutside freshC (σ.pullback_outside v)).mpr hv)
  have ht : (T.support (T.var a)).Subset u := by
    simpa [T.support_var, Names.Subset] using ha
  have he : (Effect.var b).vars ⊆ u.effects := by simpa [Effect.var] using hb
  have h := generalize_finite_of_admissible_substitution g hg hn hc σ
    (Substitution.outputs_solved a b t eff freshT freshE) invariant entails
    (T.var a) (Effect.var b) ht he
  simpa [Substitution.apply, T.subst_var, Effect.subst, Effect.var,
    σ, Substitution.outputs] using h

theorem ComputationScheme.generalize_avoids {X : Constraints T O}
    (g : Context X) (c : X.Formula) (t : T.Term) (eff : Effect) :
    g.Avoids (ComputationScheme.generalize g c t eff).bound := by
  apply g.avoids_of_support_disjoint
  exact ⟨Finset.disjoint_left.mpr fun _ hi hg => (Finset.mem_sdiff.mp hi).2 hg,
    Finset.disjoint_left.mpr fun _ hi hg => (Finset.mem_sdiff.mp hi).2 hg⟩

theorem ComputationScheme.generalize_support {X : Constraints T O}
    (g : Context X) (c : X.Formula) (t : T.Term) (eff : Effect) :
    (ComputationScheme.generalize g c t eff).support.types ⊆ g.support.types ∧
    (ComputationScheme.generalize g c t eff).support.effects ⊆ g.support.effects := by
  constructor <;> intro i hi <;>
    simp only [ComputationScheme.support, ComputationScheme.generalize,
      Names.diff, Names.union, Finset.mem_sdiff, not_and, not_not] at hi <;>
    exact hi.2 hi.1

/-- This is a judgment about the result of inference. It does not add a
polymorphic introduction rule to the expression language. -/
inductive ComputationTyping (sig : Signature T) (X : Constraints T O)
    (solved : X.Formula → Prop) : X.Formula → Context X → Expr → ComputationScheme X → Prop where
  | generalize {c g e t eff} (a : Names) : g.Avoids a →
      X.Admissible solved (X.existsNames a c) →
      Typing sig X solved c g e (.mono t) eff →
      ComputationTyping sig X solved (X.existsNames a c) g e ⟨a, c, t, eff⟩
  | weaken {c d g e s} : ComputationTyping sig X solved c g e s →
      X.Admissible solved d → X.Entails d c → ComputationTyping sig X solved d g e s

/-- A pure value's computation scheme is also an ordinary value scheme.
Every intermediate constraint remains admissible for the same solved set. -/
theorem ComputationTyping.value {sig : Signature T} {X : Constraints T O}
    {solved c g e s} (h : ComputationTyping sig X solved c g e s) (hv : Value e)
    (he : X.Entails s.condition (X.effectEq s.effect ∅)) :
    Typing sig X solved c g e (.qualified s.bound s.condition s.result) ∅ := by
  induction h with
  | generalize a fresh hc typed => exact (typed.effectEq he).generalize hv a fresh hc
  | weaken _ hd entails ih => exact (ih hv he).weaken hd entails

theorem Typing.computation_generalize {sig : Signature T} {X : Constraints T O}
    {solved c g e t eff} (h : Typing sig X solved c g e (.mono t) eff)
    (hc : X.Admissible solved (X.existsNames (ComputationScheme.generalize g c t eff).bound c)) :
    ComputationTyping sig X solved
      (X.existsNames (ComputationScheme.generalize g c t eff).bound c) g e
      (ComputationScheme.generalize g c t eff) :=
  .generalize _ (ComputationScheme.generalize_avoids g c t eff) hc h

theorem ComputationScheme.generalize_closed_instance {X : Constraints T O}
    (g : Context X) (c : X.Formula) (t : T.Term) (eff : Effect)
    (hg : g.support = Names.empty) (v : Valuation T.Value) (hc : X.holds c v)
    (outer : Valuation T.Value) :
    (ComputationScheme.generalize g c t eff).GroundInstance outer
      (T.eval v t) (eff.eval v.effects) := by
  let a := (ComputationScheme.generalize g c t eff).bound
  let w := outer.patch v a
  have ht (i : Nat) (hi : i ∈ (X.support c).types ∪ (T.support t).types) :
      w.types i = v.types i := by
    have ha : i ∈ a.types := by
      simpa [a, ComputationScheme.generalize, Names.union, Names.diff, hg, Names.empty] using hi
    simp [w, Valuation.patch, ha]
  have he (i : Nat) (hi : i ∈ (X.support c).effects ∪ (T.support t).effects ∪ eff.vars) :
      w.effects i = v.effects i := by
    have ha : i ∈ a.effects := by
      simpa [a, ComputationScheme.generalize, Names.union, Names.diff, hg, Names.empty] using hi
    simp [w, Valuation.patch, ha]
  have hc' : X.holds c w := (X.holds_support c w v
    ⟨fun i hi => ht i (Finset.mem_union_left _ hi),
      fun i hi => he i (Finset.mem_union_left _ (Finset.mem_union_left _ hi))⟩).mpr hc
  have ht' : T.eval w t = T.eval v t := T.eval_support w v t
    ⟨fun i hi => ht i (Finset.mem_union_right _ hi),
      fun i hi => he i (Finset.mem_union_left _ (Finset.mem_union_right _ hi))⟩
  have he' : eff.eval w.effects = eff.eval v.effects := by
    unfold Effect.eval
    congr 1
    apply Finset.biUnion_congr rfl
    intro i hi
    exact he i (Finset.mem_union_right _ hi)
  exact ⟨w, outer.patch_agreeOutside v a, hc', ht' ▸ O.refl _, he'⟩

theorem Typing.computation_generalize_closed {sig : Signature T} {X : Constraints T O}
    {solved c g e t eff} (h : Typing sig X solved c g e (.mono t) eff)
    (hg : g.support = Names.empty) (hc : X.Satisfiable c)
    (htop : X.Admissible solved X.top) :
    ComputationTyping sig X solved X.top g e (ComputationScheme.generalize g c t eff) := by
  obtain ⟨v, hv⟩ := hc
  have hp : ∀ w, X.holds (X.existsNames (ComputationScheme.generalize g c t eff).bound c) w := by
    intro w
    obtain ⟨u, hu, hc, _, _⟩ := ComputationScheme.generalize_closed_instance g c t eff hg v hv w
    exact (X.holds_exists _ _ _).mpr ⟨u, hu, hc⟩
  have had : X.Admissible solved
      (X.existsNames (ComputationScheme.generalize g c t eff).bound c) := by
    obtain ⟨r, hr, equivalent⟩ := htop
    exact ⟨r, hr, fun w _ => equivalent.1 w ((X.holds_top w).mpr trivial),
      fun w _ => hp w⟩
  exact .weaken (h.computation_generalize had) htop (fun w _ => hp w)

/-- Principality includes every valid declarative monotype and its evaluation
effect; comparison uses the parameter order on result values. -/
def PrincipalComputationScheme (sig : Signature T) (X : Constraints T O)
    (solved : X.Formula → Prop) (g : Context X) (e : Expr) (s : ComputationScheme X) : Prop :=
  ComputationTyping sig X solved X.top g e s ∧
  ∀ c t eff, Typing sig X solved c g e (.mono t) eff →
    ∀ v, X.holds c v → s.GroundInstance v (T.eval v t) (eff.eval v.effects)

/-- Exact simplification of the condition preserves the same uniform finite
instance, not merely pointwise ground witnesses. Bound names are retained. -/
theorem ComputationScheme.FiniteInstance.condition_equivalent {X : Constraints T O}
    {s : ComputationScheme X} {r c : X.Formula} {t : T.Term} {eff : Effect}
    (h : s.FiniteInstance c t eff) (eq : X.Equivalent r s.condition) :
    ({ s with condition := r } : ComputationScheme X).FiniteInstance c t eff := by
  obtain ⟨θ, ht, he, cover⟩ := h
  exact ⟨θ, ht, he, fun v hv => ⟨eq.2 _ (cover v hv).1, (cover v hv).2⟩⟩

theorem ComputationScheme.GroundInstance.condition_equivalent {X : Constraints T O}
    {s : ComputationScheme X} {r : X.Formula} {v : Valuation T.Value}
    {t : T.Value} {eff : Finset Op} (h : s.GroundInstance v t eff)
    (eq : X.Equivalent r s.condition) :
    ({ s with condition := r } : ComputationScheme X).GroundInstance v t eff := by
  obtain ⟨w, hw, hc, ht, he⟩ := h
  exact ⟨w, hw, eq.2 w hc, ht, he⟩

/-- All internal nodes retain satisfiability-based validity after exact
condition simplification. No closure property of an arbitrary solved set is
asserted. This transports an existing computation derivation. -/
theorem ComputationTyping.condition_equivalent {sig : Signature T} {X : Constraints T O}
    {c : X.Formula} {g : Context X} {e : Expr} {s : ComputationScheme X}
    (h : ComputationTyping sig X X.Satisfiable c g e s)
    {r : X.Formula} (eq : X.Equivalent r s.condition) :
    ComputationTyping sig X X.Satisfiable c g e { s with condition := r } := by
  induction h with
  | generalize a fresh hc typed =>
    have hr := X.satisfiable_of_entails eq.2
      ((X.admissible_satisfiable_iff _).mp typed.root.1)
    have projected := (X.admissible_satisfiable_iff _).mpr
      ((X.satisfiable_exists_iff a r).mpr hr)
    exact .weaken (.generalize a fresh projected
      (typed.weaken ((X.admissible_satisfiable_iff _).mpr hr) eq.1)) hc
      (X.exists_mono a eq.2)
  | weaken _ hd entails ih => exact .weaken (ih eq) hd entails

theorem PrincipalComputationScheme.condition_equivalent {sig : Signature T}
    {X : Constraints T O} {g : Context X} {e : Expr} {s : ComputationScheme X}
    (h : PrincipalComputationScheme sig X X.Satisfiable g e s)
    {r : X.Formula} (eq : X.Equivalent r s.condition) :
    PrincipalComputationScheme sig X X.Satisfiable g e { s with condition := r } :=
  ⟨h.1.condition_equivalent eq,
    fun c t eff typed v hv => (h.2 c t eff typed v hv).condition_equivalent eq⟩

end EHMX.HMX
