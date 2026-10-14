import EHMX.HMX.EqualityModel

namespace EHMX.HMX

/-- Semantic values have closed representatives, fixed by substitution. -/
structure TypeDomain.GroundRepresentation (T : TypeDomain) where
  quote : T.Value → T.Term
  eval_quote : ∀ v t, T.eval v (quote t) = t
  support_quote : ∀ t, T.support (quote t) = Names.empty

def equalityGroundRepresentation : equalityTypes.GroundRepresentation where
  quote := GroundTy.toTy
  eval_quote := fun v t => t.toTy_eval ⟨v.types, v.effects⟩
  support_quote := by
    intro t
    have closed : t.toTy.fvTypes = ∅ ∧ t.toTy.fvEffects = ∅ := by
      induction t with
      | atom n =>
          cases n with
          | zero => exact ⟨rfl, rfl⟩
          | succ n => cases n <;> exact ⟨rfl, rfl⟩
      | arr a e b ha hb =>
          simp [GroundTy.toTy, Ty.fvTypes, Ty.fvEffects, ha, hb]
    exact congrArg₂ Names.mk closed.1 closed.2

private theorem Substitution.factor_type_alias {s ρ : Substitution equalityTypes}
    (hs : s.Solved) {a : Names} (scope : ρ.domain.Subset a)
    (factor : ∀ v, s.pullback (ρ.pullback v) = ρ.pullback v)
    {i : Nat} (hi : i ∈ s.domain.types) (ha : i ∉ a.types) :
    ∃ j ∈ a.types, s.types i = Ty.var j := by
  have fixed (v : Valuation GroundTy) :
      equalityTypes.eval (ρ.pullback v) (s.types i) = v.types i := by
    have h := congrArg (fun w => w.types i) (factor v)
    exact h.trans ((ρ.pullback_outside v).1 i (fun h => ha (scope.1 h)))
  cases image : s.types i with
  | var j =>
      refine ⟨j, ?_, rfl⟩
      by_contra hj
      have h := fixed ⟨GroundTy.atom, fun _ => ∅⟩
      have outside := ρ.types_outside j (fun h => hj (scope.1 h))
      have eq : j = i := by
        simpa [image, Substitution.pullback, equalityTypes, Ty.eval, outside] using h
      have disjoint := (hs.type_range i hi).1
      simp [image, equalityTypes, Ty.fvTypes, eq, hi] at disjoint
  | base b =>
      have h := fixed ⟨fun _ => .arr (.atom 0) ∅ (.atom 0), fun _ => ∅⟩
      cases b <;> simp [image, equalityTypes, Ty.eval] at h
  | arr t e u =>
      have h := fixed ⟨fun _ => .atom 0, fun _ => ∅⟩
      simp [image, equalityTypes, Ty.eval] at h

/-- In the concrete free type algebra, a scoped comparison factor is enough
to orient all type assignments inside the binder. The effect domain is retained;
this theorem does not assume that finite-union effects are free constructors. -/
theorem Substitution.scope_types {O : TypeOrder equalityTypes}
    (X : Constraints equalityTypes O) {s ρ : Substitution equalityTypes}
    (hs : s.Solved) {a : Names} (scope : ρ.domain.Subset a)
    (factor : ∀ v, s.pullback (ρ.pullback v) = ρ.pullback v) :
    ∃ σ : Substitution equalityTypes, σ.Solved ∧ σ.domain.types ⊆ a.types ∧
      σ.domain.effects = s.domain.effects ∧
      X.Equivalent (X.substitutionConstraint s) (X.substitutionConstraint σ) := by
  classical
  by_cases ht : s.domain.types ⊆ a.types
  · exact ⟨s, hs, ht, rfl, X.entails_refl _, X.entails_refl _⟩
  · obtain ⟨i, hi, ha⟩ := Finset.not_subset.mp ht
    obtain ⟨j, hj, image⟩ := Substitution.factor_type_alias hs scope factor hi ha
    let p := s.pivot i j image
    have hp : p.Solved := hs.pivot hi image
    have graph := X.substitutionConstraint_pivot s hs hi image
    have fp (v : Valuation GroundTy) : p.pullback (ρ.pullback v) = ρ.pullback v := by
      apply X.substitutionConstraint_fixed
      apply graph.1
      rw [← factor v]
      exact X.substitutionConstraint_pullback s hs.idempotent _
    obtain ⟨σ, hσ, htypes, heffects, equivalent⟩ :=
      Substitution.scope_types X hp scope fp
    exact ⟨σ, hσ, htypes, heffects,
      X.entails_trans graph.1 equivalent.1, X.entails_trans equivalent.2 graph.2⟩
termination_by (s.domain.types \ a.types).card
decreasing_by
  have shrink : p.domain.types \ a.types = (s.domain.types \ a.types).erase i := by
    ext k
    simp only [p, Substitution.pivot, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_erase]
    aesop
  rw [shrink]
  exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hi, ha⟩)

variable {T : TypeDomain} {O : TypeOrder T}

/-- An assignment outside a scoped comparison factor contains only bound
effect variables and no labels. Unlike types, it may still be a union. -/
theorem Substitution.factor_effect_support {s ρ : Substitution T}
    (hs : s.Solved) {a : Names} (scope : ρ.domain.Subset a)
    (factor : ∀ v, s.pullback (ρ.pullback v) = ρ.pullback v)
    {i : Nat} (hi : i ∈ s.domain.effects) (ha : i ∉ a.effects) :
    (s.effects i).labels = ∅ ∧ (s.effects i).vars.Nonempty ∧ (s.effects i).vars ⊆ a.effects := by
  classical
  obtain ⟨base⟩ := T.value_nonempty
  have fixed (v : Valuation T.Value) :
      (s.effects i).eval (ρ.pullback v).effects = v.effects i := by
    have h := congrArg (fun w => w.effects i) (factor v)
    exact h.trans ((ρ.pullback_outside v).2 i (fun h => ha (scope.2 h)))
  have labels : (s.effects i).labels = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro op hop
    have mem : op ∈ (s.effects i).eval (ρ.pullback ⟨fun _ => base, fun _ => ∅⟩).effects :=
      Finset.mem_union_left _ hop
    rw [fixed] at mem
    exact Finset.notMem_empty _ mem
  refine ⟨labels, ?_, ?_⟩
  · by_contra h
    have empty := Finset.not_nonempty_iff_eq_empty.mp h
    have bad := fixed ⟨fun _ => base, fun _ => {0}⟩
    simp [Effect.eval, labels, empty] at bad
  · intro j hj
    by_contra outside
    have hji : j ≠ i := fun h => Finset.disjoint_left.mp (hs.effect_range i hi) hi (h ▸ hj)
    let v : Valuation T.Value := ⟨fun _ => base, fun k => if k = j then {0} else ∅⟩
    have mem : 0 ∈ (s.effects i).eval (ρ.pullback v).effects := by
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨j, hj, ?_⟩
      rw [(ρ.pullback_outside v).2 j (fun h => outside (scope.2 h))]
      simp [v]
    rw [fixed] at mem
    simp [v, Ne.symm hji] at mem

private theorem Substitution.scope_one_effect (X : Constraints T O)
    {s ρ : Substitution T} (hs : s.Solved) {a : Names} {z : Nat}
    (single : a.effects = {z}) (scope : ρ.domain.Subset a)
    (factor : ∀ v, s.pullback (ρ.pullback v) = ρ.pullback v) :
    ∃ σ : Substitution T, σ.Solved ∧ σ.domain.types = s.domain.types ∧
      σ.domain.effects ⊆ a.effects ∧
      X.Equivalent (X.substitutionConstraint s) (X.substitutionConstraint σ) := by
  classical
  by_cases he : s.domain.effects ⊆ a.effects
  · exact ⟨s, hs, rfl, he, X.entails_refl _, X.entails_refl _⟩
  · obtain ⟨i, hi, ha⟩ := Finset.not_subset.mp he
    obtain ⟨labels, nonempty, bound⟩ := Substitution.factor_effect_support hs scope factor hi ha
    have vars : (s.effects i).vars = {z} := by
      apply Finset.Subset.antisymm (single ▸ bound)
      obtain ⟨j, hj⟩ := nonempty
      have eq : j = z := by simpa [single] using bound hj
      simpa [eq] using hj
    have heq : s.effects i = Effect.var z := congrArg₂ Effect.mk labels vars
    let p := s.pivotEffect i z heq
    have hp := hs.pivotEffect hi heq
    have graph := X.substitutionConstraint_pivotEffect s hs hi heq
    have fp (v : Valuation T.Value) : p.pullback (ρ.pullback v) = ρ.pullback v := by
      apply X.substitutionConstraint_fixed
      apply graph.1
      rw [← factor v]
      exact X.substitutionConstraint_pullback s hs.idempotent _
    obtain ⟨σ, hσ, ht, he, eq⟩ := Substitution.scope_one_effect X hp single scope fp
    exact ⟨σ, hσ, ht, he, X.entails_trans graph.1 eq.1, X.entails_trans eq.2 graph.2⟩
termination_by (s.domain.effects \ a.effects).card
decreasing_by
  have shrink : p.domain.effects \ a.effects = (s.domain.effects \ a.effects).erase i := by
    ext k
    simp only [p, Substitution.pivotEffect, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_erase]
    have _hz : z ∈ a.effects := by simp [single]
    aesop
  rw [shrink]
  exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hi, ha⟩)

/-- A comparison factor supported on one effect name admits a principal-equation
representative on that same name, for an arbitrary abstract type domain. -/
theorem Substitution.scope_singleton_effect (X : Constraints T O)
    {s ρ : Substitution T} (hs : s.Solved) {z : Nat}
    (scope : ρ.domain.Subset ⟨∅, {z}⟩)
    (factor : ∀ v, s.pullback (ρ.pullback v) = ρ.pullback v) :
    ∃ σ : Substitution T, σ.Solved ∧ σ.domain.Subset ⟨∅, {z}⟩ ∧
      X.Equivalent (X.substitutionConstraint s) (X.substitutionConstraint σ) := by
  classical
  have outside (i : Nat) : ρ.types i = T.var i :=
    ρ.types_outside i (fun hi => Finset.notMem_empty i (scope.1 hi))
  have types (v : Valuation T.Value) (i : Nat) : T.eval v (s.types i) = v.types i := by
    by_cases hi : i ∈ s.domain.types
    · have unique (x y : T.Value) : x = y := by
        let w : Valuation T.Value := ⟨fun _ => x, fun _ => ∅⟩
        let u : Valuation T.Value := ⟨Function.update w.types i y, w.effects⟩
        have same : (ρ.pullback w).AgreeOutside (ρ.pullback u) s.domain := by
          constructor
          · intro j hj
            have hji : j ≠ i := fun h => hj (h ▸ hi)
            simp [Substitution.pullback, outside, T.eval_var, u, hji]
          · intro j _; rfl
        have eq : ρ.pullback w = ρ.pullback u := by
          rw [← factor w, ← factor u]
          exact hs.pullback_agreeOutside same
        simpa [Substitution.pullback, outside, T.eval_var, w, u] using
          congrArg (fun v => v.types i) eq
      exact unique _ _
    · simp [s.types_outside i hi, T.eval_var]
  let p : Substitution T := {
    domain := ⟨∅, s.domain.effects⟩
    types := T.var
    effects := s.effects
    types_outside := fun _ _ => rfl
    effects_outside := s.effects_outside }
  have hp : p.Solved := ⟨by simp [p], hs.effect_range⟩
  have graph : X.Equivalent (X.substitutionConstraint s) (X.substitutionConstraint p) := by
    constructor
    · intro v hv
      exact (X.holds_substitutionConstraint p v).mpr
        ⟨by simp [p], ((X.holds_substitutionConstraint s v).mp hv).2⟩
    · intro v hv
      exact (X.holds_substitutionConstraint s v).mpr
        ⟨fun i _ => (types v i).symm, ((X.holds_substitutionConstraint p v).mp hv).2⟩
  have fp (v : Valuation T.Value) : p.pullback (ρ.pullback v) = ρ.pullback v := by
    apply X.substitutionConstraint_fixed
    apply graph.1
    rw [← factor v]
    exact X.substitutionConstraint_pullback s hs.idempotent _
  obtain ⟨σ, hσ, ht, he, eq⟩ := Substitution.scope_one_effect X hp rfl scope fp
  exact ⟨σ, hσ, ⟨by simp [ht, p], he⟩,
    X.entails_trans graph.1 eq.1, X.entails_trans eq.2 graph.2⟩

/-- A finite ground substitution, restricted to the input's support. -/
def Substitution.groundOn (Q : T.GroundRepresentation) (a : Names)
    (v : Valuation T.Value) : Substitution T where
  domain := a
  types := fun i => if i ∈ a.types then Q.quote (v.types i) else T.var i
  effects := fun i => if i ∈ a.effects then ⟨v.effects i, ∅⟩ else Effect.var i
  types_outside := by intro i hi; simp [hi]
  effects_outside := by intro i hi; simp [hi]

theorem Substitution.groundOn_solved (Q : T.GroundRepresentation)
    (a : Names) (v : Valuation T.Value) : (Substitution.groundOn Q a v).Solved := by
  constructor
  · intro i hi
    change i ∈ a.types at hi
    simp [Substitution.groundOn, hi, Q.support_quote, Names.Disjoint, Names.empty]
  · intro i hi
    change i ∈ a.effects at hi
    simp [Substitution.groundOn, hi]

/-- A uniform realizer can be chosen solved by replacing its local type
parameters with a fresh variable and local effects with the empty effect.
No semantic value needs a closed term representative. -/
theorem Scheme.Realizable.solved_witness_finite {X : Constraints T O}
    {c d : X.Formula} {a : Names} {t : T.Term}
    (h : (Scheme.qualified a d t).Realizable c) (fresh : X.Avoids c a) :
    ∃ θ : Substitution T, θ.Solved ∧ θ.domain.Subset a ∧ X.Entails c (X.subst θ d) := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨ρ, scope, hd, _⟩ := Instance.qualified_mono_iff.mp hu
  let freshType := a.shiftTypes 0
  have freshType_not_mem : freshType ∉ a.types := by
    intro hi
    have := Finset.le_sup (f := id) hi
    simp only [freshType, Names.shiftTypes, id_eq] at this
    omega
  let γ : Substitution T := {
    domain := a
    types := fun i => if i ∈ a.types then T.var freshType else T.var i
    effects := fun i => if i ∈ a.effects then ∅ else Effect.var i
    types_outside := by intro i hi; simp [hi]
    effects_outside := by intro i hi; simp [hi] }
  have types (i : Nat) : a.Disjoint (T.support (γ.types i)) := by
    by_cases hi : i ∈ a.types
    · simp [γ, hi, T.support_var, Names.Disjoint, freshType_not_mem]
    · simp [γ, hi, T.support_var, Names.Disjoint]
  have effects (i : Nat) : Disjoint a.effects (γ.effects i).vars := by
    by_cases hi : i ∈ a.effects <;>
      simp [γ, hi, Effect.var]
  have typeClosed (t : T.Term) : a.Disjoint (T.support (γ.apply t)) :=
    T.support_subst_avoids _ _ _ _ (fun i _ => types i) (fun i _ => effects i)
  have effectClosed (e : Effect) : Disjoint a.effects (e.subst γ.effects).vars := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j, _, hij⟩ := Finset.mem_biUnion.mp hj
    exact Finset.disjoint_left.mp (effects j) hi hij
  let θ : Substitution T := {
    domain := a
    types := fun i => if i ∈ a.types then γ.apply (ρ.types i) else T.var i
    effects := fun i => if i ∈ a.effects then (ρ.effects i).subst γ.effects else Effect.var i
    types_outside := by intro i hi; simp [hi]
    effects_outside := by intro i hi; simp [hi] }
  have solved : θ.Solved := by
    constructor
    · intro i hi
      simpa [θ, hi] using typeClosed (ρ.types i)
    · intro i hi
      simpa [θ, hi] using effectClosed (ρ.effects i)
  have pullback (v : Valuation T.Value) : θ.pullback v = ρ.pullback (γ.pullback v) := by
    apply congrArg₂ Valuation.mk
    · funext i
      by_cases hi : i ∈ a.types
      · simp [Substitution.pullback, θ, hi, Substitution.eval_apply]
      · simp [Substitution.pullback, θ, γ, hi,
          ρ.types_outside i (fun hm => hi (scope.1 hm)), T.eval_var]
    · funext i
      by_cases hi : i ∈ a.effects
      · simp [Substitution.pullback, θ, hi, Effect.eval_subst]
      · simp [Substitution.pullback, θ, γ, hi,
          ρ.effects_outside i (fun hm => hi (scope.2 hm)), Effect.eval, Effect.var]
  refine ⟨θ, solved, Names.Subset.refl a, ?_⟩
  intro v hv
  apply (X.holds_subst _ _ _).mpr
  rw [pullback]
  exact (X.holds_subst _ _ _).mp
    (hd _ ((X.holds_agreeOutside fresh (γ.pullback_outside v)).mpr hv))

/-- Compatibility with the earlier interface; ground representation is no
longer needed to construct the solved witness. -/
theorem Scheme.Realizable.solved_witness {X : Constraints T O}
    (_Q : T.GroundRepresentation) {c d : X.Formula} {a : Names} {t : T.Term}
    (h : (Scheme.qualified a d t).Realizable c) (fresh : X.Avoids c a) :
    ∃ θ : Substitution T, θ.Solved ∧ θ.domain.Subset a ∧ X.Entails c (X.subst θ d) :=
  h.solved_witness_finite fresh

namespace Constraints
variable (X : Constraints T O)

/-- The scoped competitor used in dissertation Theorem 7 is constructed
from realizability and admissibility, rather than postulated by the solver. -/
theorem NormalForm.exists_of_realizable_finite
    {solved : X.Formula → Prop} {c d : X.Formula} {a : Names} {t : T.Term}
    (hc : X.Admissible solved (X.and c (X.existsNames a d))) (fresh : X.Avoids c a)
    (hreal : (Scheme.qualified a d t).Realizable (X.and c (X.existsNames a d))) :
    ∃ m : X.NormalForm, m.IsNormal solved (X.and c d) ∧
      m.substitution.domain.Subset a ∧
      X.Equivalent m.residual (X.and c (X.existsNames a d)) := by
  have freshOuter : X.Avoids (X.and c (X.existsNames a d)) a := by
    apply X.avoids_of_transport
    intro v w hw hv
    obtain ⟨hvC, hvD⟩ := (X.holds_and _ _ _).mp hv
    exact (X.holds_and _ _ _).mpr ⟨(X.holds_agreeOutside fresh hw).mp hvC,
      (X.holds_agreeOutside (X.exists_avoids a d) hw).mp hvD⟩
  obtain ⟨θ, hθ, scope, hd⟩ := hreal.solved_witness_finite freshOuter
  obtain ⟨r, hr, he⟩ := hc
  have outside (v : Valuation T.Value) : (θ.pullback v).AgreeOutside v a :=
    ⟨fun i hi => (θ.pullback_outside v).1 i (fun hm => hi (scope.1 hm)),
      fun i hi => (θ.pullback_outside v).2 i (fun hm => hi (scope.2 hm))⟩
  refine ⟨⟨r, θ⟩, ⟨hr, hθ, ⟨?_, ?_⟩, ?_⟩, scope, ⟨he.2, he.1⟩⟩
  · intro v hv
    exact he.1 v ((X.holds_agreeOutside freshOuter (outside v)).mp
      (he.2 _ ((X.holds_subst _ _ _).mp hv)))
  · intro v hv
    exact (X.holds_subst _ _ _).mpr (he.1 _
      ((X.holds_agreeOutside freshOuter (outside v)).mpr (he.2 v hv)))
  · intro v hv
    obtain ⟨hrv, graph⟩ := (X.holds_and _ _ _).mp hv
    have outer := he.2 v hrv
    have hdv := (X.holds_subst _ _ _).mp (hd v outer)
    rw [X.substitutionConstraint_fixed θ v graph] at hdv
    exact (X.holds_and _ _ _).mpr ⟨((X.holds_and _ _ _).mp outer).1, hdv⟩

/-- Compatibility wrapper for callers of the previous semantic interface. -/
theorem NormalForm.exists_of_realizable (_Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {c d : X.Formula} {a : Names} {t : T.Term}
    (hc : X.Admissible solved (X.and c (X.existsNames a d))) (fresh : X.Avoids c a)
    (hreal : (Scheme.qualified a d t).Realizable (X.and c (X.existsNames a d))) :
    ∃ m : X.NormalForm, m.IsNormal solved (X.and c d) ∧
      m.substitution.domain.Subset a ∧
      X.Equivalent m.residual (X.and c (X.existsNames a d)) :=
  NormalForm.exists_of_realizable_finite X hc fresh hreal

/-- Realizability supplies a normal form, hence normalization succeeds without
assuming a solved tautology. Principality supplies a uniform finite realization
of the resulting qualifier using only the original bound names. -/
theorem PrincipalNormalizer.normalize_realizable_finite (P : X.PrincipalNormalizer)
    {c d : X.Formula} {a : Names} {t : T.Term}
    (hc : X.Admissible P.solved (X.and c (X.existsNames a d))) (fresh : X.Avoids c a)
    (hreal : (Scheme.qualified a d t).Realizable (X.and c (X.existsNames a d))) :
    ∃ n, P.normalize (ConstraintProblem.initial X (X.and c d)) = some n ∧
      (Scheme.qualified a n.residual (n.substitution.apply t)).Realizable
        (X.and c (X.existsNames a d)) := by
  obtain ⟨m, hm, scope, he⟩ := NormalForm.exists_of_realizable_finite X hc fresh hreal
  cases hn : P.normalize (ConstraintProblem.initial X (X.and c d)) with
  | none =>
      exact False.elim ((P.failure _).mp hn
        ⟨m, (NormalForm.isNormalOf_initial_iff X).mpr hm⟩)
  | some n =>
      have principal := P.principal_initial X hn
      have hr := ((principal.2 m hm).canonical X principal.1).2
      refine ⟨n, rfl, m.substitution.apply (n.substitution.apply t), ?_⟩
      exact .forallLeft m.substitution scope.1 scope.2 (X.entails_trans he.2 hr)
        (.sub (fun v _ => (X.holds_le _ _ _).mpr (O.refl _)))

/-- Compatibility wrapper; the proof no longer uses ground representation. -/
theorem PrincipalNormalizer.normalize_realizable (P : X.PrincipalNormalizer)
    (_Q : T.GroundRepresentation) {c d : X.Formula} {a : Names} {t : T.Term}
    (hc : X.Admissible P.solved (X.and c (X.existsNames a d))) (fresh : X.Avoids c a)
    (hreal : (Scheme.qualified a d t).Realizable (X.and c (X.existsNames a d))) :
    ∃ n, P.normalize (ConstraintProblem.initial X (X.and c d)) = some n ∧
      (Scheme.qualified a n.residual (n.substitution.apply t)).Realizable
        (X.and c (X.existsNames a d)) :=
  P.normalize_realizable_finite X hc fresh hreal

/-- A solved substitution erases its domain, so an invariant residual cannot
depend on those names. This uses the syntactic convention from Lemma 4. -/
theorem NormalForm.residual_avoids {solved : X.Formula → Prop}
    {d : X.Formula} {n : X.NormalForm} (hn : n.IsNormal solved d) :
    X.Avoids n.residual n.substitution.domain := by
  apply X.avoids_of_transport
  intro v w hw hv
  have h := (X.holds_subst _ _ v).mp (hn.2.2.1.2 v hv)
  rw [hn.2.1.pullback_agreeOutside hw] at h
  exact hn.2.2.1.1 w ((X.holds_subst _ _ w).mpr h)

theorem groundOn_graph_holds (Q : T.GroundRepresentation) (a : Names)
    (v : Valuation T.Value) : X.holds (X.substitutionConstraint (Substitution.groundOn Q a v)) v := by
  apply (X.holds_substitutionConstraint _ _).mpr
  constructor
  · intro i hi
    change i ∈ a.types at hi
    simp [Substitution.groundOn, hi, Q.eval_quote]
  · intro i hi
    change i ∈ a.effects at hi
    simp [Substitution.groundOn, hi, Effect.eval]

theorem groundOn_graph_agrees (Q : T.GroundRepresentation) (a : Names)
    (v w : Valuation T.Value)
    (hw : X.holds (X.substitutionConstraint (Substitution.groundOn Q a v)) w) :
    w.AgreeOn v a := by
  obtain ⟨ht, he⟩ := (X.holds_substitutionConstraint _ _).mp hw
  constructor
  · intro i hi
    simpa [Substitution.groundOn, hi, Q.eval_quote] using ht i hi
  · intro i hi
    simpa [Substitution.groundOn, hi, Effect.eval] using he i hi

def NormalForm.groundOn (Q : T.GroundRepresentation) (r d : X.Formula)
    (v : Valuation T.Value) : X.NormalForm :=
  ⟨r, Substitution.groundOn Q (X.support d) v⟩

theorem NormalForm.groundOn_isNormal (Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {r d : X.Formula} (hr : solved r)
    (hrTrue : ∀ v, X.holds r v) (v : Valuation T.Value) (hv : X.holds d v) :
    (NormalForm.groundOn X Q r d v).IsNormal solved d := by
  refine ⟨hr, Substitution.groundOn_solved Q _ v, ⟨?_, ?_⟩, ?_⟩
  · intro w _; exact hrTrue w
  · intro w _; exact (X.holds_subst _ r w).mpr (hrTrue _)
  · intro w hw
    obtain ⟨_, hgraph⟩ := (X.holds_and _ _ w).mp hw
    exact (X.holds_support d w v (X.groundOn_graph_agrees Q _ v w hgraph)).mpr hv

/-- Finite-observation principality covers precisely the input solutions when
the input depends only on the observed names. The witness is a valuation, not a
uniform type substitution; private output parameters remain existential. -/
theorem NormalForm.principalOn_solutions (Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {u : Names} {r d : X.Formula} {n : X.NormalForm}
    (hr : solved r) (hrTrue : ∀ v, X.holds r v)
    (scope : (X.freeNames d).Subset u)
    (hn : n.IsPrincipalOn u solved d) (v : Valuation T.Value) :
    X.holds d v ↔ ∃ w, X.holds n.formula w ∧ w.AgreeOn v u := by
  constructor
  · intro hv
    let m := NormalForm.groundOn X Q r d v
    apply (hn.2 m (NormalForm.groundOn_isNormal X Q hr hrTrue v hv)).covers X hn.1
    exact (X.holds_and _ _ _).mpr ⟨hrTrue v, X.groundOn_graph_holds Q _ v⟩
  · rintro ⟨w, hw, same⟩
    exact (X.holds_freeNames scope same).mp (hn.1.2.2.2 w hw)

/-- Hide precisely the implementation support of the output outside `u`.
Unlike the all-variable theorem below, this does not expose private parameters
as free variables of the input. -/
theorem NormalForm.principalOn_projected (Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {u : Names} {r d : X.Formula} {n : X.NormalForm}
    (hr : solved r) (hrTrue : ∀ v, X.holds r v)
    (scope : (X.freeNames d).Subset u) (hn : n.IsPrincipalOn u solved d) :
    X.Equivalent d (X.existsNames ((X.support n.formula).diff u) n.formula) := by
  let hidden := (X.support n.formula).diff u
  constructor
  · intro v hv
    obtain ⟨w, hw, same⟩ := (NormalForm.principalOn_solutions X Q hr hrTrue scope hn v).mp hv
    let z := v.patch w hidden
    apply (X.holds_exists _ _ _).mpr
    refine ⟨z, v.patch_agreeOutside w hidden, (X.holds_support n.formula z w ?_).mpr hw⟩
    constructor
    · intro i hi
      by_cases hu : i ∈ u.types
      · simpa [z, Valuation.patch, hidden, Names.diff, hu] using (same.1 i hu).symm
      · simp [z, Valuation.patch, hidden, Names.diff, hi, hu]
    · intro i hi
      by_cases hu : i ∈ u.effects
      · simpa [z, Valuation.patch, hidden, Names.diff, hu] using (same.2 i hu).symm
      · simp [z, Valuation.patch, hidden, Names.diff, hi, hu]
  · intro v hv
    obtain ⟨w, hw, holds⟩ := (X.holds_exists _ _ _).mp hv
    apply (NormalForm.principalOn_solutions X Q hr hrTrue scope hn v).mpr
    refine ⟨w, holds, ⟨?_, ?_⟩⟩
    · intro i hi
      exact hw.1 i (by simp [Names.diff, hi])
    · intro i hi
      exact hw.2 i (by simp [Names.diff, hi])

/-- Constraint-level normalization of a handler clause retains `forall rigid`
before all local existential witnesses. This proves equivalence of constraints,
not validity of the clause's typing derivation in the solved fragment. -/
theorem NormalForm.principalOn_clause (Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {u : Names} {r d : X.Formula} {n : X.NormalForm}
    (hr : solved r) (hrTrue : ∀ v, X.holds r v)
    (scope : (X.freeNames d).Subset u) (hn : n.IsPrincipalOn u solved d)
    (rigid locals : Names) :
    X.Equivalent (X.clause rigid locals d)
      (X.clause rigid (locals.union ((X.support n.formula).diff u)) n.formula) := by
  have h := X.clause_congr rigid locals (NormalForm.principalOn_projected X Q hr hrTrue scope hn)
  have j := X.clause_exists rigid locals ((X.support n.formula).diff u) n.formula
  exact ⟨X.entails_trans h.1 j.1, X.entails_trans j.2 h.2⟩

/-- Every solution is represented by a finite normal form, so principality
among normal forms covers all solutions, not just already-normalized ones. -/
theorem NormalForm.principal_equivalent (Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {r d : X.Formula} {n : X.NormalForm}
    (hr : solved r) (hrTrue : ∀ v, X.holds r v)
    (hn : n.IsPrincipal solved d) : X.Equivalent d n.formula := by
  refine ⟨?_, hn.1.2.2.2⟩
  intro v hv
  let m := NormalForm.groundOn X Q r d v
  obtain ⟨hf, he⟩ := (hn.2 m
    (NormalForm.groundOn_isNormal X Q hr hrTrue v hv)).canonical X hn.1
  have fixed := X.substitutionConstraint_fixed m.substitution v
    (X.groundOn_graph_holds Q _ v)
  have hR := (X.holds_subst _ _ v).mp (he v (hrTrue v))
  rw [fixed] at hR
  have nfixed : n.substitution.pullback v = v := by
    simpa only [fixed] using hf v
  apply (X.holds_and _ _ _).mpr
  refine ⟨hR, ?_⟩
  apply (X.holds_substitutionConstraint _ _).mpr
  exact ⟨fun i _ => (congrArg (fun w => w.types i) nfixed).symm,
    fun i _ => (congrArg (fun w => w.effects i) nfixed).symm⟩

theorem PrincipalNormalizer.success_of_satisfiable (Q : T.GroundRepresentation)
    (N : X.PrincipalNormalizer) {r d : X.Formula} (hr : N.solved r)
    (hrTrue : ∀ v, X.holds r v) (hd : X.Satisfiable d) :
    ∃ n, N.normalize (ConstraintProblem.initial X d) = some n := by
  obtain ⟨v, hv⟩ := hd
  cases hn : N.normalize (ConstraintProblem.initial X d) with
  | none =>
      exact False.elim ((N.failure (ConstraintProblem.initial X d)).mp hn
        ⟨NormalForm.groundOn X Q r d v, (NormalForm.isNormalOf_initial_iff X).mpr (NormalForm.groundOn_isNormal X Q hr hrTrue v hv)⟩)
  | some n => exact ⟨n, rfl⟩

theorem PrincipalNormalizer.success_iff_satisfiable (Q : T.GroundRepresentation)
    (N : X.PrincipalNormalizer) {r : X.Formula} (hr : N.solved r)
    (hrTrue : ∀ v, X.holds r v) (d : X.Formula) :
    (∃ n, N.normalize (ConstraintProblem.initial X d) = some n) ↔ X.Satisfiable d := by
  constructor
  · rintro ⟨n, hn⟩; exact N.success_has_solution X hn
  · exact N.success_of_satisfiable X Q hr hrTrue

/-- Adding a fresh, redundant effect parameter preserves admissibility whenever
the absorbed variable can be nonempty. The residual is arbitrary: no conjunction
closure is assumed. Singleton scope and two choices for the redundant parameter
force the auxiliary principal substitution to be the identity. -/
theorem PrincipalNormalizer.admissible_effect_absorb (P : X.PrincipalNormalizer)
    (Q : T.GroundRepresentation) {r c : X.Formula} {e : Effect} {j z : Nat}
    (hr : P.solved r) (hrTrue : ∀ v, X.holds r v)
    (hc : X.Admissible P.solved c) (fresh : X.Avoids c ⟨∅, {z}⟩)
    (hz : z ∉ e.vars) (hj : j ∈ e.vars)
    (nonempty : ∃ v, X.holds c v ∧ (v.effects j).Nonempty) :
    X.Admissible P.solved (X.and c (X.effectEq (Effect.var j ∪ Effect.var z) e)) := by
  classical
  have hjz : j ≠ z := fun h => hz (h ▸ hj)
  let d := X.and c (X.effectEq (Effect.var j ∪ Effect.var z) e)
  have included (v : Valuation T.Value) : v.effects j ⊆ e.eval v.effects :=
    fun _ hop => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, hop⟩)
  let set (v : Valuation T.Value) (a : Finset Op) : Valuation T.Value :=
    ⟨v.types, Function.update v.effects z a⟩
  have outside (v : Valuation T.Value) (a : Finset Op) :
      (set v a).AgreeOutside v ⟨∅, {z}⟩ := by
    refine ⟨fun _ _ => rfl, ?_⟩
    intro k hk
    have hkz : k ≠ z := by simpa using hk
    simp [set, hkz]
  have model (v : Valuation T.Value) (a : Finset Op) (hv : X.holds c v)
      (ha : v.effects j ∪ a = e.eval v.effects) : X.holds d (set v a) := by
    apply (X.holds_and _ _ _).mpr
    refine ⟨(X.holds_agreeOutside fresh (outside v a)).mpr hv, ?_⟩
    apply (X.holds_effectEq _ _ _).mpr
    have he : e.eval (set v a).effects = e.eval v.effects := by
      apply Effect.eval_support
      intro k hk
      have hkz : k ≠ z := fun h => hz (h ▸ hk)
      simp [set, hkz]
    simpa [Effect.eval, Effect.var, set, hjz] using ha.trans he.symm
  obtain ⟨v, hv, op, hop⟩ := nonempty
  let w := set v (e.eval v.effects)
  let u := set v ((e.eval v.effects).erase op)
  have hw : X.holds d w := model v _ hv (Finset.union_eq_right.mpr (included v))
  have hu : X.holds d u := by
    apply model v _ hv
    ext k
    simp only [Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (hk | ⟨_, hk⟩)
      · exact included v hk
      · exact hk
    · intro hk
      by_cases h : k = op
      · exact Or.inl (h ▸ hop)
      · exact Or.inr ⟨h, hk⟩
  obtain ⟨n, hn⟩ := P.success_of_satisfiable X Q hr hrTrue ⟨w, hw⟩
  have principal := P.principal_initial X hn
  let ρ : Substitution T := {
    domain := ⟨∅, {z}⟩
    types := T.var
    effects := fun k => if k = z then e else Effect.var k
    types_outside := fun _ _ => rfl
    effects_outside := by
      intro k hk
      have hkz : k ≠ z := by simpa using hk
      simp [hkz] }
  have hρ : ρ.Solved := by
    constructor
    · simp [ρ]
    · intro k hk
      have hkz : k = z := by simpa [ρ] using hk
      subst k; simpa [ρ] using hz
  have pullback (v : Valuation T.Value) : ρ.pullback v = set v (e.eval v.effects) := by
    apply congrArg₂ Valuation.mk
    · funext k; exact T.eval_var _ _
    · funext k
      by_cases h : k = z <;> simp [ρ, h, Effect.eval, Effect.var]
  obtain ⟨q, hq, equivalent⟩ := hc
  let m : X.NormalForm := ⟨q, ρ⟩
  have normal : m.IsNormal P.solved d := by
    refine ⟨hq, hρ, ⟨?_, ?_⟩, ?_⟩
    · intro v hv
      have h := equivalent.2 _ ((X.holds_subst _ _ _).mp hv)
      rw [pullback] at h
      exact equivalent.1 v ((X.holds_agreeOutside fresh (outside v _)).mp h)
    · intro v hv
      apply (X.holds_subst _ _ _).mpr
      rw [pullback]
      exact equivalent.1 _ ((X.holds_agreeOutside fresh (outside v _)).mpr (equivalent.2 v hv))
    · intro v hv
      obtain ⟨hc, hg⟩ := (X.holds_and _ _ _).mp hv
      have h := model v _ (equivalent.2 v hc) (Finset.union_eq_right.mpr (included v))
      rw [← pullback, X.substitutionConstraint_fixed ρ v hg] at h
      exact h
  obtain ⟨σ, hσ, scope, graph⟩ := Substitution.scope_singleton_effect X principal.1.2.1
    (Names.Subset.refl _) ((principal.2 m normal).canonical X principal.1).1
  have equiv := NormalForm.principal_equivalent X Q hr hrTrue principal
  have fixes (a : Valuation T.Value) (ha : X.holds d a) : σ.pullback a = a :=
    X.substitutionConstraint_fixed σ a (graph.1 a ((X.holds_and _ _ _).mp (equiv.1 a ha)).2)
  have unassigned : z ∉ σ.domain.effects := by
    intro assigned
    have same : w.AgreeOutside u σ.domain := by
      refine ⟨fun _ _ => rfl, ?_⟩
      intro k hk
      have hkz : k ≠ z := fun h => hk (h ▸ assigned)
      simp [w, u, set, hkz]
    have eq : w = u := (fixes w hw).symm.trans ((hσ.pullback_agreeOutside same).trans (fixes u hu))
    have eq' := congrArg (fun a => op ∈ a.effects z) eq
    simp [w, u, set, included v hop] at eq'
  have identity (a : Valuation T.Value) : σ.pullback a = a := by
    apply congrArg₂ Valuation.mk
    · funext k
      exact (σ.pullback_outside a).1 k (fun hk => Finset.notMem_empty k (scope.1 hk))
    · funext k
      apply (σ.pullback_outside a).2
      intro hk
      have hkz : k = z := by simpa using scope.2 hk
      exact unassigned (hkz ▸ hk)
  refine ⟨n.residual, principal.1.1, X.entails_trans equiv.1 (X.entails_left _ _), ?_⟩
  intro a ha
  apply equiv.2
  apply (X.holds_and _ _ _).mpr
  refine ⟨ha, graph.2 a ?_⟩
  rw [← identity a]
  exact X.substitutionConstraint_pullback σ hσ.idempotent a

private theorem NormalForm.IsPrincipal.effect_image_rigid
    {solved : X.Formula → Prop} {d c : X.Formula} {n : X.NormalForm}
    (hn : n.IsPrincipal solved d) {i : Nat} (hi : i ∈ n.substitution.domain.effects)
    (e : Effect) (he : Disjoint n.substitution.domain.effects e.vars)
    (hc : X.Admissible solved c) (fresh : X.Avoids c n.substitution.domain)
    (residual : X.Entails c n.residual)
    (eq : X.Entails c (X.effectEq (n.substitution.effects i) e)) :
    ∀ v : Valuation T.Value, (n.substitution.effects i).eval v.effects = e.eval v.effects := by
  classical
  let s := n.substitution
  let σ : Substitution T := {
    domain := s.domain
    types := s.types
    effects := Function.update s.effects i e
    types_outside := s.types_outside
    effects_outside := by
      intro j hj
      have hji : j ≠ i := fun h => hj (h ▸ hi)
      simp [hji, s.effects_outside j hj] }
  have hs := hn.1.2.1
  have hσ : σ.Solved := by
    refine ⟨hs.type_range, ?_⟩
    intro j hj
    by_cases hji : j = i
    · simpa [σ, hji] using he
    · simpa [σ, hji] using hs.effect_range j hj
  obtain ⟨q, hq, equiv⟩ := hc
  let m : X.NormalForm := ⟨q, σ⟩
  have normal : m.IsNormal solved d := by
    refine ⟨hq, hσ, ⟨?_, ?_⟩, ?_⟩
    · intro v hv
      exact equiv.1 v ((X.holds_agreeOutside fresh (σ.pullback_outside v)).mp
        (equiv.2 _ ((X.holds_subst _ _ _).mp hv)))
    · intro v hv
      exact (X.holds_subst _ _ _).mpr (equiv.1 _
        ((X.holds_agreeOutside fresh (σ.pullback_outside v)).mpr (equiv.2 v hv)))
    · intro v hv
      obtain ⟨hqv, hg⟩ := (X.holds_and _ _ _).mp hv
      have hcv := equiv.2 v hqv
      have graph := (X.holds_substitutionConstraint σ v).mp hg
      apply hn.1.2.2.2
      apply (X.holds_and _ _ _).mpr
      refine ⟨residual v hcv, (X.holds_substitutionConstraint s v).mpr ⟨graph.1, ?_⟩⟩
      intro j hj
      by_cases hji : j = i
      · subst j
        have h : v.effects i = e.eval v.effects := by simpa [σ] using graph.2 i hi
        exact h.trans ((X.holds_effectEq _ _ _).mp (eq v hcv)).symm
      · simpa [σ, hji] using graph.2 j hj
  intro v
  have factor := congrArg (fun w => w.effects i)
    (((hn.2 m normal).canonical X hn.1).1 v)
  have unchanged : (s.effects i).eval (σ.pullback v).effects = (s.effects i).eval v.effects := by
    apply Effect.eval_support
    intro j hj
    exact (σ.pullback_outside v).2 j
      (fun hd => Finset.disjoint_left.mp (hs.effect_range i hi) hd hj)
  have h : (s.effects i).eval (σ.pullback v).effects = e.eval v.effects := by
    change (s.effects i).eval (σ.pullback v).effects = (σ.effects i).eval v.effects at factor
    simpa only [σ, Function.update_self] using factor
  exact unchanged.symm.trans h

/-- Under global principal normalization, a label-free assigned effect cannot
retain effect variables. A fresh redundant parameter would otherwise supply
a normal competitor with strictly fewer unconditional equations. -/
theorem PrincipalNormalizer.effect_image_empty (P : X.PrincipalNormalizer)
    (Q : T.GroundRepresentation) {r d : X.Formula} {n : X.NormalForm}
    (hr : P.solved r) (hrTrue : ∀ v, X.holds r v) (hn : n.IsPrincipal P.solved d)
    {i : Nat} (hi : i ∈ n.substitution.domain.effects)
    (labels : (n.substitution.effects i).labels = ∅) :
    (n.substitution.effects i).vars = ∅ := by
  classical
  let e := n.substitution.effects i
  have range := hn.1.2.1.effect_range i hi
  have freshR := NormalForm.residual_avoids X hn.1
  have admissible : X.Admissible P.solved n.residual :=
    ⟨n.residual, hn.1.1, X.entails_refl _, X.entails_refl _⟩
  obtain ⟨base⟩ := T.value_nonempty
  by_cases has : ∃ j ∈ e.vars, ∃ v, X.holds n.residual v ∧ (v.effects j).Nonempty
  · obtain ⟨j, hj, nonempty⟩ := has
    let used := n.substitution.domain.effects ∪ e.vars ∪ (X.support n.residual).effects
    let z := used.sup id + 1
    have hz : z ∉ used := by
      intro h
      have bound := Finset.le_sup (f := id) h
      dsimp [z] at bound
      omega
    have hzD : z ∉ n.substitution.domain.effects := fun h => hz (by simp [used, h])
    have hzE : z ∉ e.vars := fun h => hz (by simp [used, h])
    have hzR : z ∉ (X.support n.residual).effects := fun h => hz (by simp [used, h])
    have hjD : j ∉ n.substitution.domain.effects :=
      fun h => Finset.disjoint_left.mp range h hj
    have freshZ : X.Avoids n.residual ⟨∅, {z}⟩ := by
      refine ⟨by simp, ?_⟩
      intro k hk hf
      have hkz : k = z := by simpa using hk
      exact hzR (hkz ▸ X.freeEffect_mem_support hf)
    let new := Effect.var j ∪ Effect.var z
    have newRange : Disjoint n.substitution.domain.effects new.vars := by
      simp [new, Effect.var, hjD, hzD]
    let c := X.and n.residual (X.effectEq new e)
    have hc : X.Admissible P.solved c :=
      P.admissible_effect_absorb X Q hr hrTrue admissible freshZ hzE hj nonempty
    have freshC : X.Avoids c n.substitution.domain := by
      apply X.avoids_of_transport
      intro v w outside hv
      obtain ⟨hR, heq⟩ := (X.holds_and _ _ _).mp hv
      apply (X.holds_and _ _ _).mpr
      refine ⟨(X.holds_agreeOutside freshR outside).mp hR, ?_⟩
      apply (X.holds_effectEq _ _ _).mpr
      have transport (a : Effect) (ha : Disjoint n.substitution.domain.effects a.vars) :
          a.eval v.effects = a.eval w.effects :=
        Effect.eval_support _ _ _ (fun k hk => outside.2 k
          (fun h => Finset.disjoint_left.mp ha h hk))
      rw [← transport new newRange, ← transport e range]
      exact (X.holds_effectEq _ _ _).mp heq
    have rigid := hn.effect_image_rigid X hi new newRange hc freshC
      (X.entails_left _ _) (fun v hv => (X.holds_effectEq _ _ _).mpr
        ((X.holds_effectEq _ _ _).mp ((X.holds_and _ _ _).mp hv).2).symm)
    let v : Valuation T.Value := ⟨fun _ => base, fun k => if k = z then {0} else ∅⟩
    have empty : e.eval v.effects = ∅ := by
      have eq := Effect.eval_support e v.effects (fun _ => ∅)
        (fun k hk => by simp [v, show k ≠ z from fun h => hzE (h ▸ hk)])
      rw [eq]
      ext k
      simp [Effect.eval, e, labels]
    have mem : 0 ∈ new.eval v.effects := by simp [new, Effect.eval, Effect.var, v]
    rw [← rigid v, empty] at mem
    exact False.elim (Finset.notMem_empty _ mem)
  · have forced : X.Entails n.residual (X.effectEq e ∅) := by
      intro v hv
      apply (X.holds_effectEq _ _ _).mpr
      have empty (j : Nat) (hj : j ∈ e.vars) : v.effects j = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro h
        exact has ⟨j, hj, v, hv, h⟩
      simp only [Effect.eval, e, labels, Effect.labels_empty, Effect.vars_empty,
        Finset.biUnion_congr rfl empty, Finset.empty_union, Finset.biUnion_empty]
      ext k
      simp
    have rigid := hn.effect_image_rigid X hi ∅ (by simp) admissible freshR
      (X.entails_refl _) forced
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    let v : Valuation T.Value := ⟨fun _ => base, fun _ => {0}⟩
    have mem : 0 ∈ e.eval v.effects :=
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, by simp [v]⟩)
    rw [rigid v] at mem
    simp [Effect.eval] at mem

/-- The effect part of a principal substitution already stays within the
domain of any scoped normal competitor. This is derived from global
normalization, and does not posit a scope-preserving solver interface. -/
theorem PrincipalNormalizer.scope_effects (P : X.PrincipalNormalizer)
    (Q : T.GroundRepresentation) {r d : X.Formula} {n m : X.NormalForm} {a : Names}
    (hr : P.solved r) (hrTrue : ∀ v, X.holds r v)
    (hn : n.IsPrincipal P.solved d) (hm : m.IsNormal P.solved d)
    (scope : m.substitution.domain.Subset a) : n.substitution.domain.effects ⊆ a.effects := by
  intro i hi
  by_contra outside
  obtain ⟨labels, nonempty, _⟩ := Substitution.factor_effect_support hn.1.2.1 scope
    ((hn.2 m hm).canonical X hn.1).1 hi outside
  rw [P.effect_image_empty X Q hr hrTrue hn hi labels] at nonempty
  exact Finset.not_nonempty_empty nonempty

private theorem fixed_of_avoids {d : X.Formula} {s ρ : Substitution T}
    (hs : s.Solved) (hd : X.Satisfiable d) (fresh : X.Avoids d ρ.domain)
    (fixed : ∀ v, X.holds d v → s.pullback v = v)
    (factor : ∀ v, s.pullback (ρ.pullback v) = ρ.pullback v) :
    ∀ v, s.pullback v = v := by
  obtain ⟨base, hb⟩ := hd
  have constant (v : Valuation T.Value) : base.patch v s.domain = base := by
    let w := base.patch v s.domain
    let y := ρ.pullback w
    let z := base.patch y ρ.domain
    have hyz : y.AgreeOutside z s.domain := by
      constructor
      · intro i hi
        by_cases hj : i ∈ ρ.domain.types
        · simp [z, Valuation.patch, hj]
        · simpa [y, z, w, Valuation.patch, hi, hj] using (ρ.pullback_outside w).1 i hj
      · intro i hi
        by_cases hj : i ∈ ρ.domain.effects
        · simp [z, Valuation.patch, hj]
        · simpa [y, z, w, Valuation.patch, hi, hj] using (ρ.pullback_outside w).2 i hj
    have hz : X.holds d z :=
      (X.holds_agreeOutside fresh (base.patch_agreeOutside y ρ.domain)).mpr hb
    have eq : y = z := (factor w).symm.trans ((hs.pullback_agreeOutside hyz).trans (fixed z hz))
    have outside : w.AgreeOutside base ρ.domain := by
      constructor
      · intro i hi
        have h := congrArg (fun v => v.types i) eq
        simpa [y, z, Valuation.patch, hi, (ρ.pullback_outside w).1 i hi] using h
      · intro i hi
        have h := congrArg (fun v => v.effects i) eq
        simpa [y, z, Valuation.patch, hi, (ρ.pullback_outside w).2 i hi] using h
    have hw := (X.holds_agreeOutside fresh outside).mpr hb
    exact (fixed w hw).symm.trans
      ((hs.pullback_agreeOutside (base.patch_agreeOutside v s.domain)).trans (fixed base hb))
  intro v
  have hv := constant v
  have hs' := constant (s.pullback v)
  apply congrArg₂ Valuation.mk
  · funext i
    by_cases hi : i ∈ s.domain.types
    · have h := congrArg (fun w => w.types i) (hs'.trans hv.symm)
      simpa [Valuation.patch, hi, Substitution.pullback] using h
    · exact (s.pullback_outside v).1 i hi
  · funext i
    by_cases hi : i ∈ s.domain.effects
    · have h := congrArg (fun w => w.effects i) (hs'.trans hv.symm)
      simpa [Valuation.patch, hi, Substitution.pullback] using h
    · exact (s.pullback_outside v).2 i hi

/-- Global principality forces admissibility to be closed under entailment,
provided ground representatives and a solved tautology are available. -/
theorem PrincipalNormalizer.admissible_of_entails (Q : T.GroundRepresentation)
    (N : X.PrincipalNormalizer) {r : X.Formula} (hr : N.solved r)
    (hrTrue : ∀ v, X.holds r v) {c d : X.Formula}
    (hc : X.Admissible N.solved c) (he : X.Entails c d) :
    X.Admissible N.solved d := by
  obtain ⟨s, hs, hcs, hsc⟩ := hc
  have hsd := X.entails_trans hsc he
  have hd := X.satisfiable_of_entails hsd (N.solved_satisfiable s hs)
  obtain ⟨n, hn⟩ := N.success_of_satisfiable X Q hr hrTrue hd
  have principal := N.principal_initial X hn
  let m : X.NormalForm := ⟨s, Substitution.identity T⟩
  have hm : m.IsNormal N.solved d := by
    refine ⟨hs, Substitution.identity_solved T, ⟨?_, ?_⟩, ?_⟩
    · intro v hv
      simpa only [m, X.holds_subst, Substitution.identity_pullback] using hv
    · intro v hv
      simpa only [m, X.holds_subst, Substitution.identity_pullback] using hv
    · intro v hv
      exact hsd v ((X.holds_and _ _ v).mp hv).1
  obtain ⟨factor, _⟩ := (principal.2 m hm).canonical X principal.1
  have fixed (v : Valuation T.Value) : n.substitution.pullback v = v := by
    simpa only [m, Substitution.identity_pullback] using factor v
  refine ⟨n.residual, principal.1.1, ?_, ?_⟩
  · exact X.entails_trans (NormalForm.principal_equivalent X Q hr hrTrue principal).1
      (X.entails_left _ _)
  · intro v hv
    have h := (X.holds_subst _ _ v).mp (NormalForm.reconstruct_entails X principal.1 v hv)
    simpa only [fixed] using h

theorem PrincipalNormalizer.admissible_exists (Q : T.GroundRepresentation)
    (N : X.PrincipalNormalizer) {r : X.Formula} (hr : N.solved r)
    (hrTrue : ∀ v, X.holds r v) {c : X.Formula}
    (hc : X.Admissible N.solved c) (a : Names) :
    X.Admissible N.solved (X.existsNames a c) :=
  N.admissible_of_entails X Q hr hrTrue hc (X.exists_intro a c)

/-- Global principal normalization supplies consistency of a reoriented
residual. No closure under substitution or renaming is imposed on `solved`. -/
theorem PrincipalNormalizer.admissible_reorient (P : X.PrincipalNormalizer)
    (Q : T.GroundRepresentation) {r d : X.Formula} {n : X.NormalForm}
    (hr : P.solved r) (hrTrue : ∀ v, X.holds r v) (hn : n.IsNormal P.solved d)
    (σ : Substitution T) (hs : σ.Solved)
    (graph : X.Equivalent (X.substitutionConstraint n.substitution)
      (X.substitutionConstraint σ)) :
    X.Admissible P.solved (X.subst σ n.residual) := by
  have competitor : n.IsNormal P.solved (X.subst σ n.residual) := by
    refine ⟨hn.1, hn.2.1, hn.2.2.1, ?_⟩
    intro v hv
    obtain ⟨hR, hg⟩ := (X.holds_and _ _ _).mp hv
    exact (X.holds_subst _ _ v).mpr
      (by rwa [X.substitutionConstraint_fixed σ v (graph.1 v hg)])
  obtain ⟨k, hk⟩ : ∃ k, P.normalize (ConstraintProblem.initial X (X.subst σ n.residual)) = some k := by
    cases h : P.normalize (ConstraintProblem.initial X (X.subst σ n.residual)) with
    | some k => exact ⟨k, rfl⟩
    | none => exact False.elim ((P.failure _).mp h
        ⟨n, (NormalForm.isNormalOf_initial_iff X).mpr competitor⟩)
  have principal := P.principal_initial X hk
  have equivalent := NormalForm.principal_equivalent X Q hr hrTrue principal
  have fresh : X.Avoids (X.subst σ n.residual) σ.domain := by
    apply X.avoids_of_transport
    intro v w hw hv
    exact (X.holds_subst _ _ w).mpr (by
      rw [← hs.pullback_agreeOutside hw]
      exact (X.holds_subst _ _ v).mp hv)
  have implies := ((NormalForm.moreGeneral_iff_entails X principal.1 competitor).mp
    (principal.2 n competitor)).1
  have fixed := fixed_of_avoids X principal.1.2.1 (P.success_has_solution X hk) fresh
    (fun v hv => X.substitutionConstraint_fixed _ v ((X.holds_and _ _ _).mp (equivalent.1 v hv)).2)
    (fun v => X.substitutionConstraint_fixed _ _
      (implies _ (graph.2 _ (X.substitutionConstraint_pullback σ hs.idempotent v))))
  refine ⟨k.residual, principal.1.1, X.entails_trans equivalent.1 (X.entails_left _ _), ?_⟩
  intro v hv
  have h := (X.holds_subst _ _ v).mp (NormalForm.reconstruct_entails X principal.1 v hv)
  simpa only [fixed] using h

private theorem admissible_freshen (P : X.PrincipalNormalizer)
    (Q : T.GroundRepresentation) {r c : X.Formula} (hr : P.solved r)
    (hrTrue : ∀ v, X.holds r v) (hc : X.Admissible P.solved c)
    (a : Names) (ft fe : Equiv.Perm Nat)
    (stable : ∀ v w, v.AgreeOn w a → (X.holds c v ↔ X.holds c w))
    (fresh : (Names.mk (a.types.image ft) (a.effects.image fe)).Disjoint a) :
    X.Admissible P.solved (X.subst (Substitution.freshen T a ft fe) c) := by
  let b : Names := ⟨a.types.image ft, a.effects.image fe⟩
  let σ := Substitution.freshen T a ft fe
  let θ := Substitution.freshen T b ft.symm fe.symm
  have hs : σ.Solved := by
    constructor
    · intro i hi
      change i ∈ a.types at hi
      have h := Finset.disjoint_left.mp fresh.1 (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      simpa [σ, Substitution.freshen, hi, T.support_var, Names.Disjoint] using h
    · intro i hi
      change i ∈ a.effects at hi
      have h := Finset.disjoint_left.mp fresh.2 (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      simpa [σ, Substitution.freshen, hi, Effect.var] using h
  have ht : θ.Solved := by
    constructor
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have h := Finset.disjoint_right.mp fresh.1 hj
      simpa [θ, Substitution.freshen, b, hj, T.support_var, Names.Disjoint] using h
    · intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have h := Finset.disjoint_right.mp fresh.2 hj
      simpa [θ, Substitution.freshen, b, hj, Effect.var] using h
  have graph : X.Equivalent (X.substitutionConstraint θ) (X.substitutionConstraint σ) := by
    have holds (v : Valuation T.Value) :
        X.holds (X.substitutionConstraint θ) v ↔ X.holds (X.substitutionConstraint σ) v := by
      rw [X.holds_substitutionConstraint, X.holds_substitutionConstraint]
      constructor
      · rintro ⟨ht, he⟩
        constructor
        · intro i hi
          change i ∈ a.types at hi
          have h := (ht (ft i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).symm
          simpa [θ, σ, Substitution.freshen, b, hi, T.eval_var] using h
        · intro i hi
          change i ∈ a.effects at hi
          have h := (he (fe i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).symm
          simpa [θ, σ, Substitution.freshen, b, hi, Effect.eval, Effect.var] using h
      · rintro ⟨ht, he⟩
        constructor
        · intro i hi
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          simpa [θ, σ, Substitution.freshen, b, hj, T.eval_var] using (ht j hj).symm
        · intro i hi
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          simpa [θ, σ, Substitution.freshen, b, hj, Effect.eval, Effect.var] using (he j hj).symm
    exact ⟨fun v => (holds v).mp, fun v => (holds v).mpr⟩
  have fixed (v : Valuation T.Value) : (θ.pullback v).AgreeOn v a :=
    ⟨fun i hi => (θ.pullback_outside v).1 i (Finset.disjoint_right.mp fresh.1 hi),
      fun i hi => (θ.pullback_outside v).2 i (Finset.disjoint_right.mp fresh.2 hi)⟩
  obtain ⟨s, hsolved, equivalent⟩ := hc
  have invariant : X.Equivalent (X.subst θ s) s := by
    have holds (v : Valuation T.Value) : X.holds (X.subst θ s) v ↔ X.holds s v := by
      rw [X.holds_subst]
      exact (show X.holds s (θ.pullback v) ↔ X.holds c (θ.pullback v) from
        ⟨equivalent.2 _, equivalent.1 _⟩).trans
        ((stable _ _ (fixed v)).trans ⟨equivalent.1 v, equivalent.2 v⟩)
    exact ⟨fun v => (holds v).mp, fun v => (holds v).mpr⟩
  have normal : (NormalForm.mk s θ).IsNormal P.solved X.top :=
    ⟨hsolved, ht, invariant, fun v _ => (X.holds_top v).mpr trivial⟩
  obtain ⟨q, hq, heq⟩ := P.admissible_reorient X Q hr hrTrue normal σ hs graph
  exact ⟨q, hq,
    fun v hv => heq.1 v ((X.holds_subst _ _ v).mpr (equivalent.1 _ ((X.holds_subst _ _ v).mp hv))),
    fun v hv => (X.holds_subst _ _ v).mpr (equivalent.2 _ ((X.holds_subst _ _ v).mp (heq.2 v hv)))⟩

/-- Admissibility is invariant under finite permutations. Two disjoint
renamings reduce the result to graph reorientation; no syntactic closure
of `solved` under renaming is assumed. -/
theorem PrincipalNormalizer.admissible_rename (P : X.PrincipalNormalizer)
    (Q : T.GroundRepresentation) {r c : X.Formula} (hr : P.solved r)
    (hrTrue : ∀ v, X.holds r v) (hc : X.Admissible P.solved c) (p : Renaming) :
    X.Admissible P.solved (X.subst (p.asSubstitution T) c) := by
  let a := X.support c
  let target : Names := ⟨a.types.image p.types, a.effects.image p.effects⟩
  obtain ⟨_, ft, _, ht, _⟩ := Renaming.freshPermutation a.types (a.types ∪ target.types)
  obtain ⟨_, fe, _, he, _⟩ := Renaming.freshPermutation a.effects (a.effects ∪ target.effects)
  let b : Names := ⟨a.types.image ft, a.effects.image fe⟩
  let σ := Substitution.freshen T a ft fe
  let c' := X.subst σ c
  have hc' : X.Admissible P.solved c' :=
    admissible_freshen X P Q hr hrTrue hc a ft fe (X.holds_support c)
      ⟨ht.mono_right Finset.subset_union_left, he.mono_right Finset.subset_union_left⟩
  have stable (v w : Valuation T.Value) (agree : v.AgreeOn w b) :
      X.holds c' v ↔ X.holds c' w := by
    simp only [c', X.holds_subst]
    apply X.holds_support
    constructor
    · intro i hi
      change i ∈ a.types at hi
      have h := agree.1 (ft i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      simpa [σ, Substitution.freshen, Substitution.pullback, hi, T.eval_var] using h
    · intro i hi
      change i ∈ a.effects at hi
      have h := agree.2 (fe i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      simpa [σ, Substitution.freshen, Substitution.pullback, hi, Effect.eval, Effect.var] using h
  let gt := ft.symm.trans p.types
  let ge := fe.symm.trans p.effects
  have fresh : (Names.mk (b.types.image gt) (b.effects.image ge)).Disjoint b := by
    have tb : b.types.image gt = target.types := by
      simp [b, gt, target, Finset.image_image, Function.comp_def]
    have eb : b.effects.image ge = target.effects := by
      simp [b, ge, target, Finset.image_image, Function.comp_def]
    rw [Names.Disjoint, tb, eb]
    exact ⟨(ht.mono_right Finset.subset_union_right).symm,
      (he.mono_right Finset.subset_union_right).symm⟩
  let η := Substitution.freshen T b gt ge
  have hc'' := admissible_freshen X P Q hr hrTrue hc' b gt ge stable fresh
  have equivalent (v : Valuation T.Value) :
      X.holds (X.subst η c') v ↔ X.holds (X.subst (p.asSubstitution T) c) v := by
    simp only [c', X.holds_subst]
    apply X.holds_support
    constructor
    · intro i hi
      change i ∈ a.types at hi
      have hb : ft i ∈ b.types := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      simp [σ, η, Substitution.freshen, Substitution.pullback, hi, hb,
        Renaming.asSubstitution, T.eval_var, gt]
    · intro i hi
      change i ∈ a.effects at hi
      have hb : fe i ∈ b.effects := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      simp [σ, η, Substitution.freshen, Substitution.pullback, hi, hb,
        Renaming.asSubstitution, Effect.eval, Effect.var, ge]
  obtain ⟨q, hq, eq⟩ := hc''
  exact ⟨q, hq, fun v hv => eq.1 v ((equivalent v).mpr hv),
    fun v hv => (equivalent v).mp (eq.2 v hv)⟩

theorem PrincipalNormalizer.admissible_rename_iff (P : X.PrincipalNormalizer)
    (Q : T.GroundRepresentation) {r c : X.Formula} (hr : P.solved r)
    (hrTrue : ∀ v, X.holds r v) (p : Renaming) :
    X.Admissible P.solved (X.subst (p.asSubstitution T) c) ↔ X.Admissible P.solved c := by
  refine ⟨?_, fun hc => P.admissible_rename X Q hr hrTrue hc p⟩
  intro hc
  let q : Renaming := {
    domain := p.domain
    types := p.types.symm
    effects := p.effects.symm
    types_outside := fun i hi => by
      simpa using (congrArg p.types.symm (p.types_outside i hi)).symm
    effects_outside := fun i hi => by
      simpa using (congrArg p.effects.symm (p.effects_outside i hi)).symm }
  have back := P.admissible_rename X Q hr hrTrue hc q
  apply P.admissible_of_entails X Q hr hrTrue back
  intro v hv
  simpa [X.holds_subst, Substitution.pullback, Renaming.asSubstitution, q,
    T.eval_var, Effect.eval, Effect.var] using hv

/-- Bound-name changes preserve qualifier validity for the normalizer's own
solved set, including type and effect variables and chains of alpha changes. -/
theorem PrincipalNormalizer.alpha_admissible_iff (P : X.PrincipalNormalizer)
    (Q : T.GroundRepresentation) {r : X.Formula} (hr : P.solved r)
    (hrTrue : ∀ v, X.holds r v) {s t : Scheme X} (h : Scheme.AlphaEquivalent X s t) :
    s.Admissible P.solved ↔ t.Admissible P.solved := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | rename p _ _ => exact (P.admissible_rename_iff X Q hr hrTrue p).symm

/-- Substituting the input by its principal normalizer gives exactly the solved
residual, including the reverse implication needed for qualifier consistency. -/
theorem NormalForm.subst_equivalent (Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {r d : X.Formula} {n : X.NormalForm}
    (hr : solved r) (hrTrue : ∀ v, X.holds r v)
    (hn : n.IsPrincipal solved d) :
    X.Equivalent (X.subst n.substitution d) n.residual := by
  refine ⟨?_, NormalForm.reconstruct_entails X hn.1⟩
  intro v hv
  have he := NormalForm.principal_equivalent X Q hr hrTrue hn
  have hR := ((X.holds_and _ _ _).mp (he.1 _ ((X.holds_subst _ _ _).mp hv))).1
  exact hn.1.2.2.1.1 v ((X.holds_subst _ _ v).mpr hR)

/-- Projecting all names changed by a principal substitution removes its graph,
without changing the solutions on the remaining names. -/
theorem NormalForm.project_equivalent (Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {r d : X.Formula} {n : X.NormalForm} {a : Names}
    (hr : solved r) (hrTrue : ∀ v, X.holds r v)
    (hn : n.IsPrincipal solved d) (scope : n.substitution.domain.Subset a) :
    X.Equivalent (X.existsNames a d) (X.existsNames a n.residual) := by
  refine ⟨X.exists_mono a (X.entails_trans
    (NormalForm.principal_equivalent X Q hr hrTrue hn).1 (X.entails_left _ _)), ?_⟩
  intro v hv
  obtain ⟨w, hw, hR⟩ := (X.holds_exists _ _ v).mp hv
  have outside := n.substitution.pullback_outside w
  exact (X.holds_exists _ _ v).mpr ⟨n.substitution.pullback w,
    ⟨fun i hi => (outside.1 i (fun hj => hi (scope.1 hj))).trans (hw.1 i hi),
      fun i hi => (outside.2 i (fun hj => hi (scope.2 hj))).trans (hw.2 i hi)⟩,
    (X.holds_subst _ _ w).mp (NormalForm.reconstruct_entails X hn.1 w hR)⟩

/-- The solved residual is exactly the input with assigned names hidden. -/
theorem NormalForm.residual_equivalent_projection (Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {r d : X.Formula} {n : X.NormalForm}
    (hr : solved r) (hrTrue : ∀ v, X.holds r v) (hn : n.IsPrincipal solved d) :
    X.Equivalent n.residual (X.existsNames n.substitution.domain d) := by
  have projection := NormalForm.project_equivalent X Q hr hrTrue hn (Names.Subset.refl _)
  refine ⟨X.entails_trans (X.exists_intro _ _) projection.2, ?_⟩
  intro v hv
  obtain ⟨w, hw, hR⟩ := (X.holds_exists _ _ v).mp (projection.1 v hv)
  exact (X.holds_agreeOutside (NormalForm.residual_avoids X hn.1) hw).mp hR

/-- A scoped principal substitution gives a solved-form approximation of the
generalized scheme, including all polymorphic targets. Scope is explicit:
this theorem does not assume that an arbitrary normalizer preserves it.
The normalized problem includes the ambient constraint, as in Theorem 7. -/
theorem NormalForm.generalized_approximation (Q : T.GroundRepresentation)
    {solved : X.Formula → Prop} {r c d : X.Formula} {n : X.NormalForm}
    {a : Names} {t : T.Term}
    (hr : solved r) (hrTrue : ∀ v, X.holds r v)
    (hn : n.IsPrincipal solved (X.and c d)) (scope : n.substitution.domain.Subset a)
    (fresh : X.Avoids c a) :
    let source : Scheme X := .qualified a d t
    let target : Scheme X := .qualified a n.residual (n.substitution.apply t)
    source.Approximates solved (X.and c (X.existsNames a d)) target := by
  let source : Scheme X := .qualified a d t
  let target : Scheme X := .qualified a n.residual (n.substitution.apply t)
  have equiv := NormalForm.principal_equivalent X Q hr hrTrue hn
  have residual : X.Entails (X.and c d) n.residual := X.entails_trans equiv.1 (X.entails_left _ _)
  have fixed (v : Valuation T.Value) (hv : X.holds (X.and c d) v) : n.substitution.pullback v = v :=
    X.substitutionConstraint_fixed n.substitution v ((X.holds_and _ _ _).mp (equiv.1 v hv)).2
  have sourceFresh : source.Avoids a := ⟨fun _ hi hf => hf.1 hi, fun _ hi hf => hf.1 hi⟩
  have targetFresh : target.Avoids a := ⟨fun _ hi hf => hf.1 hi, fun _ hi hf => hf.1 hi⟩
  have projection := NormalForm.project_equivalent X Q hr hrTrue hn scope
  have projected : X.Equivalent (X.and c (X.existsNames a d))
      (X.existsNames a n.residual) :=
    ⟨X.entails_trans (X.project_and_avoids fresh).2 projection.1,
      X.entails_trans projection.2 (X.project_and_avoids fresh).1⟩
  have forward : Instance X (X.and c (X.existsNames a d)) source target := by
    apply Instance.equivalent
      (show X.Equivalent (X.and c (X.existsNames a n.residual))
          (X.and c (X.existsNames a d)) from
        ⟨X.entails_trans (X.entails_right _ _) projected.2,
          fun v hv => (X.holds_and _ _ v).mpr
            ⟨((X.holds_and _ _ v).mp hv).1, projected.1 v hv⟩⟩)
    apply Instance.forallRight fresh sourceFresh
    apply Instance.forallLeft n.substitution scope.1 scope.2
    · intro v hv
      apply (X.holds_subst _ _ v).mpr
      exact ((X.holds_and _ _ _).mp ((X.holds_subst _ _ v).mp
        (NormalForm.reconstruct_entails X hn.1 v ((X.holds_and _ _ v).mp hv).2))).2
    · exact .sub (fun v _ => (X.holds_le _ _ v).mpr (O.refl _))
  have backward : Instance X (X.and c (X.existsNames a d)) target source := by
    apply Instance.forallRight fresh targetFresh
    apply Instance.forallLeft (Substitution.identity T)
      (by simp [Substitution.identity, Names.empty])
      (by simp [Substitution.identity, Names.empty])
    · intro v hv
      apply (X.holds_subst _ _ v).mpr
      rw [Substitution.identity_pullback]
      exact residual v hv
    · apply Instance.sub
      intro v hv
      apply (X.holds_le _ _ v).mpr
      rw [Substitution.eval_apply, Substitution.identity_pullback,
        Substitution.eval_apply, fixed v hv]
      exact O.refl _
  exact ⟨⟨n.residual, hn.1.1, X.entails_refl _, X.entails_refl _⟩,
    forward, fun _ _ hi => backward.trans hi⟩

end Constraints

/-- A scoped normal competitor determines a fully scoped principal
representative in the equality model. Type aliases are reoriented; global
principality already scopes the effect assignments. -/
theorem Constraints.PrincipalNormalizer.scope {O : TypeOrder equalityTypes}
    (X : Constraints equalityTypes O) (P : X.PrincipalNormalizer)
    {r d : X.Formula} {n m : X.NormalForm} {a : Names}
    (hr : P.solved r) (hrTrue : ∀ v, X.holds r v)
    (hn : n.IsPrincipal P.solved d) (hm : m.IsNormal P.solved d)
    (scope : m.substitution.domain.Subset a) :
    ∃ k : X.NormalForm, k.IsPrincipal P.solved d ∧ k.substitution.domain.Subset a := by
  have effects := P.scope_effects X equalityGroundRepresentation hr hrTrue hn hm scope
  obtain ⟨σ, hs, ht, he, graph⟩ := Substitution.scope_types X hn.1.2.1 scope
    ((hn.2 m hm).canonical X hn.1).1
  obtain ⟨k, hk, hσ, _⟩ := hn.reorient X σ hs graph
    (P.admissible_reorient X equalityGroundRepresentation hr hrTrue hn.1 σ hs graph)
  exact ⟨k, hk, by simpa only [hσ] using ht, by simpa only [hσ, he] using effects⟩

/-- Every uniformly realizable scheme has an approximation in the selected
solved set. Bound names are freshened first; a scoped principal representative
is constructed, not assumed. This theorem concerns schemes, not typing trees. -/
theorem Scheme.approximation_exists {O : TypeOrder equalityTypes}
    {X : Constraints equalityTypes O} (P : X.PrincipalNormalizer)
    {r c : X.Formula} (hr : P.solved r) (hrTrue : ∀ v, X.holds r v)
    (hc : X.Admissible P.solved c) {s : Scheme X} (real : s.Realizable c) :
    ∃ t, s.Approximates P.solved c t := by
  cases s with
  | mono t => exact ⟨.mono t, Scheme.Approximates.refl trivial real⟩
  | qualified a d t =>
      obtain ⟨b, q, u, alpha, disjoint⟩ := Scheme.fresh_alpha a d t (X.support c)
      have fresh : X.Avoids c b :=
        ⟨fun i hi hf => Finset.disjoint_left.mp disjoint.1 hi (X.freeType_mem_support hf),
          fun i hi hf => Finset.disjoint_left.mp disjoint.2 hi (X.freeEffect_mem_support hf)⟩
      have real' : (Scheme.qualified b q u).Realizable c := by
        obtain ⟨v, hv⟩ := real
        exact ⟨v, .alphaLeft alpha.symm hv⟩
      have project := Scheme.qualified_self_instance_iff.mp real'.self_instance
      let outer := X.and c (X.existsNames b q)
      have equivalent : X.Equivalent outer c :=
        ⟨X.entails_left _ _, fun v hv => (X.holds_and _ _ _).mpr ⟨hv, project v hv⟩⟩
      have admitted : X.Admissible P.solved outer := by
        obtain ⟨r, hr, hc⟩ := hc
        exact ⟨r, hr, X.entails_trans equivalent.1 hc.1, X.entails_trans hc.2 equivalent.2⟩
      obtain ⟨m, hm, scope, _⟩ := Constraints.NormalForm.exists_of_realizable X
        equalityGroundRepresentation admitted fresh (real'.weaken equivalent.1)
      obtain ⟨n, hn⟩ : ∃ n, P.normalize (Constraints.ConstraintProblem.initial X (X.and c q)) = some n := by
        cases h : P.normalize (Constraints.ConstraintProblem.initial X (X.and c q)) with
        | some n => exact ⟨n, rfl⟩
        | none => exact False.elim ((P.failure _).mp h
            ⟨m, (Constraints.NormalForm.isNormalOf_initial_iff X).mpr hm⟩)
      obtain ⟨n', principal, scopedDomain⟩ := P.scope X hr hrTrue
        (P.principal_initial X hn) hm scope
      have approx := Constraints.NormalForm.generalized_approximation X
        equalityGroundRepresentation hr hrTrue principal scopedDomain fresh (t := u)
      refine ⟨.qualified b n'.residual (n'.substitution.apply u), approx.1, ?_, ?_⟩
      · exact .alphaLeft alpha (.equivalent equivalent approx.2.1)
      · intro target ht inst
        exact .equivalent equivalent (approx.2.2 target ht
          (.equivalent ⟨equivalent.2, equivalent.1⟩ (.alphaLeft alpha.symm inst)))

end EHMX.HMX
