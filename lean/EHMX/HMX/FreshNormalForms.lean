import EHMX.HMX.ScopedNormalization
import EHMX.HMX.ContextSubstitution

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

private def Substitution.freshImages (σ : Substitution T) (p : Renaming) (u : Names) :
    Substitution T where
  domain := u
  types := fun i => if i ∈ u.types then (p.asSubstitution T).apply (σ.types i) else T.var i
  effects := fun i => if i ∈ u.effects then (σ.effects i).subst (p.asSubstitution T).effects
    else Effect.var i
  types_outside := by intro i hi; simp [hi]
  effects_outside := by intro i hi; simp [hi]

private theorem permutation_inverse (p : Renaming) (v : Valuation T.Value) :
    (p.asSubstitution T).pullback ((p.inverse.asSubstitution T).pullback v) = v := by
  cases v
  simp [Substitution.pullback, Renaming.asSubstitution, Renaming.inverse,
    T.eval_var, Effect.eval, Effect.var]

/-- Freshen the target of an arbitrary finite solving substitution. This
constructs a solved competitor without assuming that the original substitution
is idempotent or that it leaves the target constraint invariant. Renaming
closure is a separate algebraic condition on admissibility. -/
theorem Constraints.exists_fresh_normal
    (solved : X.Formula → Prop)
    (rename : ∀ (p : Renaming) c, X.Admissible solved c →
      X.Admissible solved (X.subst (p.asSubstitution T) c))
    {u : Names} {d c : X.Formula} (scope : (X.freeNames d).Subset u)
    (σ : Substitution T) (hc : X.Admissible solved c)
    (entails : X.Entails c (X.subst σ d)) :
    ∃ (m : X.NormalForm) (p : Renaming), m.IsNormal solved d ∧
      (∀ v, (m.substitution.pullback ((p.inverse.asSubstitution T).pullback v)).AgreeOn
        (σ.pullback v) u) ∧
      X.Entails c (X.subst (p.inverse.asSubstitution T) m.residual) := by
  let a := (u.union σ.range).union (X.support c)
  obtain ⟨dt, pt, ht, freshT, _⟩ := Renaming.freshPermutation a.types u.types
  obtain ⟨de, pe, he, freshE, _⟩ := Renaming.freshPermutation a.effects u.effects
  let p : Renaming := ⟨⟨dt, de⟩, pt, pe, ht, he⟩
  let π := p.asSubstitution T
  let η := σ.freshImages p u
  have imageT {i : Nat} (hi : i ∈ a.types) : p.types i ∉ u.types :=
    fun h => Finset.disjoint_left.mp freshT (Finset.mem_image.mpr ⟨i, hi, rfl⟩) h
  have imageE {i : Nat} (hi : i ∈ a.effects) : p.effects i ∉ u.effects :=
    fun h => Finset.disjoint_left.mp freshE (Finset.mem_image.mpr ⟨i, hi, rfl⟩) h
  have solvedη : η.Solved := by
    constructor
    · intro i hi
      change i ∈ u.types at hi
      change u.Disjoint (T.support (if i ∈ u.types then π.apply (σ.types i) else T.var i))
      rw [ite_eq_left hi]
      apply T.support_subst_avoids
      · intro j hj
        have hja := (Names.subset_union_left (u.union σ.range) (X.support c)).1
          ((σ.type_support_subset u hi).1 hj)
        simpa [π, Renaming.asSubstitution, T.support_var, Names.Disjoint] using imageT hja
      · intro j hj
        have hja := (Names.subset_union_left (u.union σ.range) (X.support c)).2
          ((σ.type_support_subset u hi).2 hj)
        simpa [π, Renaming.asSubstitution, Effect.var] using imageE hja
    · intro i hi
      change i ∈ u.effects at hi
      change Disjoint u.effects
        (if i ∈ u.effects then (σ.effects i).subst π.effects else Effect.var i).vars
      rw [ite_eq_left hi]
      apply Finset.disjoint_left.mpr
      intro j hj hmem
      obtain ⟨k, hk, hkj⟩ := Finset.mem_biUnion.mp hmem
      have eq : j = p.effects k := by simpa [π, Renaming.asSubstitution, Effect.var] using hkj
      subst j
      exact imageE (Finset.mem_union_left _ (σ.effect_support_subset u hi hk)) hj
  have images (v : Valuation T.Value) :
      (η.pullback v).AgreeOn (σ.pullback (π.pullback v)) u := by
    constructor
    · intro i hi
      simp [η, Substitution.freshImages, Substitution.pullback, hi, π, Substitution.eval_apply]
    · intro i hi
      simp [η, Substitution.freshImages, Substitution.pullback, hi, π, Effect.eval_subst]
  have fixes (v : Valuation T.Value) :
      (π.pullback (η.pullback v)).AgreeOn (π.pullback v) (X.support c) := by
    constructor
    · intro i hi
      have outside := (η.pullback_outside v).1 (p.types i) (imageT (Finset.mem_union_right _ hi))
      simpa [π, Substitution.pullback, Renaming.asSubstitution, T.eval_var] using outside
    · intro i hi
      have outside := (η.pullback_outside v).2 (p.effects i) (imageE (Finset.mem_union_right _ hi))
      simpa [π, Substitution.pullback, Renaming.asSubstitution, Effect.eval, Effect.var] using outside
  obtain ⟨r, hr, forward, backward⟩ := rename p c hc
  let m : X.NormalForm := ⟨r, η⟩
  have invariant : X.Equivalent (X.subst η r) r := by
    constructor
    · intro v hv
      apply forward
      apply (X.holds_subst _ _ _).mpr
      apply (X.holds_support c _ _ (fixes v)).mp
      exact (X.holds_subst _ _ _).mp (backward _ ((X.holds_subst _ _ _).mp hv))
    · intro v hv
      apply (X.holds_subst _ _ _).mpr
      apply forward
      apply (X.holds_subst _ _ _).mpr
      exact (X.holds_support c _ _ (fixes v)).mpr ((X.holds_subst _ _ _).mp (backward v hv))
  refine ⟨m, p, ⟨hr, solvedη, invariant, ?_⟩, ?_, ?_⟩
  · intro v hv
    obtain ⟨hrv, graph⟩ := (X.holds_and _ _ _).mp hv
    have hd := (X.holds_subst _ _ _).mp (entails _ ((X.holds_subst _ _ _).mp (backward v hrv)))
    have same := images v
    have eq := X.substitutionConstraint_fixed η v graph
    rw [eq] at same
    exact (X.holds_freeNames scope same).mpr hd
  · intro v
    have same := images ((p.inverse.asSubstitution T).pullback v)
    simpa only [π, permutation_inverse] using same
  · intro v hv
    apply (X.holds_subst _ _ _).mpr
    apply forward
    apply (X.holds_subst _ _ _).mpr
    simpa only [permutation_inverse] using hv

/-- Complete normalization of arbitrary finite, uniformly solving target
substitutions. The single returned factor works at all valuations. -/
theorem Constraints.ScopedPrincipalNormalizer.complete_of_substitution
    (P : X.ScopedPrincipalNormalizer)
    (rename : ∀ (p : Renaming) c, X.Admissible P.solved c →
      X.Admissible P.solved (X.subst (p.asSubstitution T) c))
    {u : Names} {d c : X.Formula} (scope : (X.freeNames d).Subset u)
    (σ : Substitution T) (hc : X.Admissible P.solved c)
    (entails : X.Entails c (X.subst σ d)) :
    ∃ n, P.normalize u d = some n ∧ ∃ φ : Substitution T,
      (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) u) ∧
      X.Entails c (X.subst φ n.residual) := by
  obtain ⟨m, p, normal, images, residual⟩ := X.exists_fresh_normal P.solved rename scope σ hc entails
  obtain ⟨n, hn, θ, factor, hr⟩ := P.complete_of_competitor scope m normal
  let φ := (p.inverse.asSubstitution T).compose θ
  refine ⟨n, hn, φ, ?_, ?_⟩
  · intro v
    rw [Substitution.compose_pullback]
    exact (factor _).trans (images v)
  · intro v hv
    apply (X.holds_subst _ _ _).mpr
    rw [Substitution.compose_pullback]
    exact (X.holds_subst _ _ _).mp (hr _ ((X.holds_subst _ _ _).mp (residual v hv)))

end EHMX.HMX
