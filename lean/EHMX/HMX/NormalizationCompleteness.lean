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
 {S : X.Formula → Prop} {r d : X.Formula} {u : Names} {n : X.NormalForm}
 (hr : S r) (truth : ∀ v, X.holds r v)
 (scope : (X.freeNames d).Subset u) (hn : n.IsPrincipalOn u S d)
 (v : HMX.Valuation T.Value) :
 X.holds d v ↔ ∃ w, X.holds n.formula w ∧ w.AgreeOn v u := by
 constructor
 · intro hv
   let m := Constraints.NormalForm.groundOn X Q r d v
   obtain ⟨φ, factor⟩ := hn.2 m (Constraints.NormalForm.groundOn_isNormal X Q hr truth v hv)
   obtain ⟨same,res⟩ := factor v (truth v)
   refine ⟨n.substitution.pullback (φ.pullback v), (X.holds_and _ _ _).mpr ⟨?_,?_⟩,?_⟩
   · exact (X.holds_subst _ _ _).mp (hn.1.2.2.1.2 _ res)
   · exact X.substitutionConstraint_pullback _ hn.1.2.1.idempotent _
   · have graph := X.groundOn_graph_holds Q (X.support d) v
     change (n.substitution.pullback (φ.pullback v)).AgreeOn
       ((HMX.Substitution.groundOn Q (X.support d) v).pullback v) u at same
     simpa only [X.substitutionConstraint_fixed _ v graph] using same
 · rintro ⟨w,hw,same⟩
   exact (X.holds_freeNames scope same).mp (hn.1.2.2.2 w hw)

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

end Constraints
end EHMX.HMX
