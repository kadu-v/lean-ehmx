import EHMX.HMX.FreshNormalForms

/-! Normalization for Theorem 7: retain effect assignments as constraints and protect
free environment names. The type-alias argument specializes to equalityTypes. -/

namespace EHMX.HMX
namespace EffectResidualNormalization
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

def typesOnly (s : Substitution T) : Substitution T where
  domain := ⟨s.domain.types, ∅⟩
  types := s.types
  effects := Effect.var
  types_outside := s.types_outside
  effects_outside := by intros; rfl

def effectsOnly (s : Substitution T) : Substitution T where
  domain := ⟨∅, s.domain.effects⟩
  types := T.var
  effects := s.effects
  types_outside := by intros; rfl
  effects_outside := s.effects_outside

theorem typesOnly_solved {s : Substitution T} (hs : s.Solved) :
    (typesOnly s).Solved := by
  refine ⟨fun i hi => ?_, ?_⟩
  exact ⟨(hs.type_range i hi).1, by simp [typesOnly]⟩
  simp [typesOnly]

theorem effectsOnly_solved {s : Substitution T} (hs : s.Solved) :
    (effectsOnly s).Solved := by
  refine ⟨?_, hs.effect_range⟩
  simp [effectsOnly]

theorem parts_compose {s : Substitution T} (hs : s.Solved) (v : Valuation T.Value) :
    (typesOnly s).pullback ((effectsOnly s).pullback v) = s.pullback v := by
  apply congrArg₂ Valuation.mk
  · funext i
    change T.eval ((effectsOnly s).pullback v) (s.types i) = T.eval v (s.types i)
    by_cases hi : i ∈ s.domain.types
    · apply T.eval_support
      refine ⟨?_, ?_⟩
      · intro j _; simp [effectsOnly, Substitution.pullback, T.eval_var]
      · intro j hj
        have outside : j ∉ s.domain.effects :=
          fun h => Finset.disjoint_left.mp (hs.type_range i hi).2 h hj
        simpa [effectsOnly, Substitution.pullback] using (s.pullback_outside v).2 j outside
    · simp [s.types_outside i hi, effectsOnly, Substitution.pullback, T.eval_var]
  · funext i
    simp [typesOnly, Substitution.pullback, effectsOnly, Effect.eval, Effect.var]

theorem split_graph (s : Substitution T) :
    X.Equivalent (X.substitutionConstraint s)
      (X.and (X.substitutionConstraint (effectsOnly s))
        (X.substitutionConstraint (typesOnly s))) := by
  constructor <;> intro v hv
  · obtain ⟨ht, he⟩ := (X.holds_substitutionConstraint _ _).mp hv
    apply (X.holds_and _ _ _).mpr
    exact ⟨(X.holds_substitutionConstraint _ _).mpr ⟨by simp [effectsOnly], he⟩,
      (X.holds_substitutionConstraint _ _).mpr ⟨ht, by simp [typesOnly]⟩⟩
  · obtain ⟨he, ht⟩ := (X.holds_and _ _ _).mp hv
    exact (X.holds_substitutionConstraint _ _).mpr
      ⟨((X.holds_substitutionConstraint _ _).mp ht).1,
        ((X.holds_substitutionConstraint _ _).mp he).2⟩

theorem retain_effect_assignments
    {S : X.Formula → Prop} (sound : ∀ r, S r → X.Satisfiable r)
    (allow : ∀ (r : X.Formula) (s : Substitution T), s.domain.types = ∅ →
      X.Admissible S r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible S (X.and r (X.substitutionConstraint s)))
    {d : X.Formula} {u : Names} {n : X.NormalForm}
    (hn : n.IsPrincipalOn u S d) :
    ∃ m : X.NormalForm, m.IsPrincipalOn u S d ∧
      m.substitution = typesOnly n.substitution ∧
      X.Equivalent m.formula n.formula := by
  let s := n.substitution
  let ts := typesOnly s
  let es := effectsOnly s
  let r := X.and n.residual (X.substitutionConstraint es)
  have solved := hn.1.2.1
  have avoid := Constraints.NormalForm.residual_avoids X hn.1
  have rt (v : Valuation T.Value) : X.holds n.residual (ts.pullback v) ↔
      X.holds n.residual v := by
    apply X.holds_agreeOutside avoid
    exact ⟨fun i hi => (ts.pullback_outside v).1 i hi,
      fun i _ => by simp [ts, typesOnly, Substitution.pullback, Effect.eval, Effect.var]⟩
  have re (v : Valuation T.Value) : X.holds n.residual (es.pullback v) ↔
      X.holds n.residual v := by
    apply X.holds_agreeOutside avoid
    exact ⟨fun i _ => by simp [es, effectsOnly, Substitution.pullback, T.eval_var],
      fun i hi => (es.pullback_outside v).2 i hi⟩
  have graph_t (v : Valuation T.Value) :
      X.holds (X.substitutionConstraint es) (ts.pullback v) ↔
        X.holds (X.substitutionConstraint es) v := by
    simp only [X.holds_substitutionConstraint, es, effectsOnly, ts, typesOnly,
      Substitution.pullback, Effect.eval, Effect.var]
    simp
  have rinv (v : Valuation T.Value) : X.holds r (ts.pullback v) ↔ X.holds r v := by
    simp only [r, X.holds_and, rt, graph_t]
  have sat : X.Satisfiable r := by
    obtain ⟨v, hv⟩ := sound _ hn.1.1
    exact ⟨es.pullback v, (X.holds_and _ _ _).mpr
      ⟨(re v).mpr hv, X.substitutionConstraint_pullback es (effectsOnly_solved solved).idempotent v⟩⟩
  obtain ⟨r', hr', forward, backward⟩ := allow n.residual es rfl
    ⟨n.residual, hn.1.1, X.entails_refl _, X.entails_refl _⟩ sat
  let m : X.NormalForm := ⟨r', ts⟩
  have formula : X.Equivalent m.formula n.formula := by
    constructor
    · intro v hv
      obtain ⟨hr, ht⟩ := (X.holds_and _ _ _).mp hv
      obtain ⟨hnr, he⟩ := (X.holds_and _ _ _).mp (backward v hr)
      exact (X.holds_and _ _ _).mpr
        ⟨hnr, (split_graph X s).2 v ((X.holds_and _ _ _).mpr ⟨he, ht⟩)⟩
    · intro v hv
      obtain ⟨hnr, hg⟩ := (X.holds_and _ _ _).mp hv
      obtain ⟨he, ht⟩ := (X.holds_and _ _ _).mp ((split_graph X s).1 v hg)
      exact (X.holds_and _ _ _).mpr
        ⟨forward v ((X.holds_and _ _ _).mpr ⟨hnr, he⟩), ht⟩
  have normal : m.IsNormal S d := by
    refine ⟨hr', typesOnly_solved solved, ⟨?_, ?_⟩,
      X.entails_trans formula.1 hn.1.2.2.2⟩
    · intro v hv
      exact forward v ((rinv v).mp (backward _ ((X.holds_subst _ _ _).mp hv)))
    · intro v hv
      exact (X.holds_subst _ _ _).mpr
        (forward _ ((rinv v).mpr (backward v hv)))
  have more : m.MoreGeneralOn u n := by
    refine ⟨es, ?_, ?_⟩
    · intro v
      change (ts.pullback (es.pullback v)).AgreeOn (s.pullback v) u
      rw [parts_compose solved]
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    · intro v hv
      exact (X.holds_subst _ _ _).mpr (forward _ ((X.holds_and _ _ _).mpr
        ⟨(re v).mpr hv,
          X.substitutionConstraint_pullback es (effectsOnly_solved solved).idempotent v⟩))
  exact ⟨m, ⟨normal, fun k hk => more.trans X (hn.2 k hk)⟩, rfl, formula⟩


end EffectResidualNormalization
end EHMX.HMX

namespace EHMX.HMX
namespace EffectResidualNormalization
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

def swapNames (i j : Nat) : Renaming where
  domain := ⟨{i, j}, ∅⟩
  types := Equiv.swap i j
  effects := Equiv.refl _
  types_outside := by intro k hk; simp at hk; simp [Equiv.swap_apply_def, hk.1, hk.2]
  effects_outside := by intros; rfl

theorem swap_twice (i j : Nat) (v : Valuation T.Value) :
    ((swapNames i j).asSubstitution T).pullback
      (((swapNames i j).asSubstitution T).pullback v) = v := by
  cases v
  simp [Substitution.pullback, Renaming.asSubstitution, swapNames, T.eval_var,
    Effect.eval, Effect.var]

theorem pivot_as_swap {s : Substitution T} (hs : s.Solved)
    {i j : Nat} (hi : i ∈ s.domain.types) (imageEq : s.types i = T.var j)
    (v : Valuation T.Value) :
    (s.pivot i j imageEq).pullback v =
      s.pullback (((swapNames i j).asSubstitution T).pullback v) := by
  rw [Substitution.pivot_pullback]
  apply hs.pullback_agreeOutside
  constructor
  · intro k hk
    have hki : k ≠ i := fun h => hk (h ▸ hi)
    by_cases hkj : k = j
    · subst k
      simp [Substitution.pullback, Renaming.asSubstitution, swapNames, T.eval_var]
    · simp [Substitution.pullback, Renaming.asSubstitution, swapNames, T.eval_var,
        Equiv.swap_apply_def, hki, hkj]
  · intro k _
    simp [Substitution.pullback, Renaming.asSubstitution, swapNames, Effect.eval, Effect.var]

theorem swap_fixed_of_graph {s : Substitution T} {i j : Nat}
    (hi : i ∈ s.domain.types) (imageEq : s.types i = T.var j)
    {v : Valuation T.Value} (graph : X.holds (X.substitutionConstraint s) v) :
    ((swapNames i j).asSubstitution T).pullback v = v := by
  have equal : v.types i = v.types j := by
    simpa [imageEq, T.eval_var] using ((X.holds_substitutionConstraint _ _).mp graph).1 i hi
  apply congrArg₂ Valuation.mk
  · funext k
    by_cases hki : k = i
    · subst k
      simpa [Substitution.pullback, Renaming.asSubstitution, swapNames, T.eval_var] using equal.symm
    · by_cases hkj : k = j
      · subst k
        simpa [Substitution.pullback, Renaming.asSubstitution, swapNames, T.eval_var] using equal
      · simp [Renaming.asSubstitution, swapNames, T.eval_var,
          Equiv.swap_apply_def, hki, hkj]
  · funext k
    simp [Renaming.asSubstitution, swapNames, Effect.eval, Effect.var]

theorem principal_pivot
    {S : X.Formula → Prop}
    (rename : ∀ (p : Renaming) c, X.Admissible S c →
      X.Admissible S (X.subst (p.asSubstitution T) c))
    {d : X.Formula} {u : Names} {n : X.NormalForm}
    (hn : n.IsPrincipalOn u S d)
    {i j : Nat} (hi : i ∈ n.substitution.domain.types)
    (imageEq : n.substitution.types i = T.var j) :
    ∃ m : X.NormalForm, m.IsPrincipalOn u S d ∧
      m.substitution = n.substitution.pivot i j imageEq ∧
      X.Equivalent m.formula n.formula := by
  let p := (swapNames i j).asSubstitution T
  let s := n.substitution.pivot i j imageEq
  have solved := hn.1.2.1
  have ss : s.Solved := solved.pivot hi imageEq
  obtain ⟨r, hr, forward, backward⟩ := rename (swapNames i j) n.residual
    ⟨n.residual, hn.1.1, X.entails_refl _, X.entails_refl _⟩
  let m : X.NormalForm := ⟨r, s⟩
  have graph := X.substitutionConstraint_pivot n.substitution solved hi imageEq
  have res (v : Valuation T.Value) : X.holds r v ↔ X.holds n.residual (p.pullback v) :=
    ⟨fun hv => (X.holds_subst _ _ _).mp (backward v hv),
      fun hv => forward v ((X.holds_subst _ _ _).mpr hv)⟩
  have inv (v : Valuation T.Value) : X.holds r (s.pullback v) ↔ X.holds r v := by
    rw [res, res, pivot_as_swap solved hi imageEq]
    have fixed := swap_fixed_of_graph X hi imageEq
      (X.substitutionConstraint_pullback n.substitution solved.idempotent (p.pullback v))
    change p.pullback (n.substitution.pullback (p.pullback v)) =
      n.substitution.pullback (p.pullback v) at fixed
    rw [fixed]
    exact ⟨fun h => hn.1.2.2.1.1 _ ((X.holds_subst _ _ _).mpr h),
      fun h => (X.holds_subst _ _ _).mp (hn.1.2.2.1.2 _ h)⟩
  have formula : X.Equivalent m.formula n.formula := by
    constructor
    · intro v hv
      obtain ⟨hR, hg⟩ := (X.holds_and _ _ _).mp hv
      have old := graph.2 v hg
      have fixed := swap_fixed_of_graph X hi imageEq old
      have rOld := (res v).mp hR
      change p.pullback v = v at fixed
      rw [fixed] at rOld
      exact (X.holds_and _ _ _).mpr ⟨rOld, old⟩
    · intro v hv
      obtain ⟨hR, hg⟩ := (X.holds_and _ _ _).mp hv
      have fixed := swap_fixed_of_graph X hi imageEq hg
      change p.pullback v = v at fixed
      exact (X.holds_and _ _ _).mpr ⟨(res v).mpr (by rwa [fixed]), graph.1 v hg⟩
  have normal : m.IsNormal S d := by
    refine ⟨hr, ss, ⟨?_, ?_⟩, X.entails_trans formula.1 hn.1.2.2.2⟩
    · intro v hv; exact (inv v).mp ((X.holds_subst _ _ _).mp hv)
    · intro v hv; exact (X.holds_subst _ _ _).mpr ((inv v).mpr hv)
  have more : m.MoreGeneralOn u n := by
    refine ⟨p, ?_, ?_⟩
    · intro v
      change (s.pullback (p.pullback v)).AgreeOn (n.substitution.pullback v) u
      rw [pivot_as_swap solved hi imageEq, swap_twice]
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    · intro v hv
      apply (X.holds_subst _ _ _).mpr
      apply (res _).mpr
      simpa only [p, swap_twice] using hv
  exact ⟨m, ⟨normal, fun k hk => more.trans X (hn.2 k hk)⟩, rfl, formula⟩


theorem fixed_type_is_alias
    {s φ : Substitution equalityTypes} (hs : s.Solved)
    {f : Finset Nat}
    (fixed : ∀ v : Valuation GroundTy, ∀ i ∈ f,
      (s.pullback (φ.pullback v)).types i = v.types i)
    {i : Nat} (hi : i ∈ s.domain.types) (fi : i ∈ f) :
    ∃ j, j ∉ f ∧ s.types i = Ty.var j := by
  have equal (v : Valuation GroundTy) :
      equalityTypes.eval (φ.pullback v) (s.types i) = v.types i := fixed v i fi
  cases imageEq : s.types i with
  | var j =>
    refine ⟨j, ?_, rfl⟩
    have outside : j ∉ s.domain.types := by
      have h := (hs.type_range i hi).1
      simpa [imageEq, equalityTypes, Ty.fvTypes] using h
    intro fj
    let v : Valuation GroundTy := ⟨GroundTy.atom, fun _ => ∅⟩
    have atI := equal v
    have atJ := fixed v j fj
    simp only [imageEq, equalityTypes, Ty.eval] at atI
    simp only [Substitution.pullback, s.types_outside j outside, equalityTypes, Ty.eval] at atJ
    have e : GroundTy.atom j = GroundTy.atom i := atJ.symm.trans atI
    have ji : j = i := GroundTy.atom.inj e
    exact outside (ji ▸ hi)
  | base b =>
    have bad := equal ⟨fun _ => .arr (.atom 0) ∅ (.atom 0), fun _ => ∅⟩
    cases b <;> simp [imageEq, equalityTypes, Ty.eval] at bad
  | arr a e b =>
    have bad := equal ⟨fun _ => .atom 0, fun _ => ∅⟩
    simp [imageEq, equalityTypes, Ty.eval] at bad

theorem protect_types {O : TypeOrder equalityTypes}
    (X : Constraints equalityTypes O) {S : X.Formula → Prop}
    (rename : ∀ (p : Renaming) c, X.Admissible S c →
      X.Admissible S (X.subst (p.asSubstitution equalityTypes) c))
    {d : X.Formula} {u : Names} {n : X.NormalForm}
    (hn : n.IsPrincipalOn u S d)
    (φ : Substitution equalityTypes) (f : Finset Nat) (fu : f ⊆ u.types)
    (fixed : ∀ v : Valuation GroundTy, ∀ i ∈ f,
      (n.substitution.pullback (φ.pullback v)).types i = v.types i) :
    ∃ m : X.NormalForm, m.IsPrincipalOn u S d ∧
      Disjoint m.substitution.domain.types f ∧
      m.substitution.effects = n.substitution.effects ∧
      X.Equivalent m.formula n.formula := by
  classical
  by_cases disjoint : Disjoint n.substitution.domain.types f
  · exact ⟨n, hn, disjoint, rfl, X.entails_refl _, X.entails_refl _⟩
  · have overlap : (n.substitution.domain.types ∩ f).Nonempty := by
      by_contra h
      exact disjoint (Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp h))
    obtain ⟨i, hi⟩ := overlap
    obtain ⟨ndi, fi⟩ := Finset.mem_inter.mp hi
    obtain ⟨j, jf, imageEq⟩ := fixed_type_is_alias hn.1.2.1 fixed ndi fi
    obtain ⟨m, hm, ms, equiv⟩ := principal_pivot X rename hn ndi imageEq
    obtain ⟨ρ, factor, _⟩ := hm.2 n hn.1
    have fixed' : ∀ v : Valuation GroundTy, ∀ k ∈ f,
        (m.substitution.pullback ((φ.compose ρ).pullback v)).types k = v.types k := by
      intro v k fk
      rw [Substitution.compose_pullback]
      exact ((factor (φ.pullback v)).1 k (fu fk)).trans (fixed v k fk)
    obtain ⟨k, hk, kd, ke, kf⟩ :=
      protect_types X rename hm (φ.compose ρ) f fu fixed'
    refine ⟨k, hk, kd, ?_, X.entails_trans kf.1 equiv.1, X.entails_trans equiv.2 kf.2⟩
    rw [ke, ms]
    rfl
termination_by (n.substitution.domain.types ∩ f).card
decreasing_by
  have shrink : m.substitution.domain.types ∩ f =
      (n.substitution.domain.types ∩ f).erase i := by
    rw [ms]
    ext k
    simp only [Substitution.pivot, Finset.mem_inter, Finset.mem_insert,
      Finset.mem_erase]
    aesop
  rw [shrink]
  exact Finset.card_erase_lt_of_mem hi



end EffectResidualNormalization
end EHMX.HMX


namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}
theorem scoped_lifting_factor
    (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution T, θ.domain.Subset a ∧ X.Admissible P.solved (X.subst θ d))
    {c d : X.Formula} {a u : Names}
    (fresh : X.Avoids c a)
    (outer : X.Admissible P.solved (X.and c (X.existsNames a d)))
    (observed : (X.freeNames (X.and c d)).Subset u) :
    ∃ (n : X.NormalForm) (θ φ : Substitution T),
      P.normalize u (X.and c d) = some n ∧
      θ.domain.Subset a ∧
      X.Admissible P.solved (X.subst θ (X.and c d)) ∧
      (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn (θ.pullback v) u) ∧
      (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn v (u.diff a)) ∧
      X.Entails (X.subst θ (X.and c d)) (X.subst φ n.residual) := by
  have projected : X.Admissible P.solved (X.existsNames a (X.and c d)) := by
    obtain ⟨s, hs, forward, backward⟩ := outer
    have eqv := X.project_and_avoids (d := d) fresh
    exact ⟨s, hs, X.entails_trans eqv.1 forward, X.entails_trans backward eqv.2⟩
  obtain ⟨θ, scope, admitted⟩ := lift a (X.and c d) projected
  obtain ⟨n, run, φ, factor, residual⟩ := P.complete_of_substitution closure.rename
    observed θ admitted (X.entails_refl _)
  refine ⟨n, θ, φ, run, scope, admitted, factor, ?_, residual⟩
  intro v
  constructor
  · intro i hi
    have h := Finset.mem_sdiff.mp hi
    exact ((factor v).1 i h.1).trans
      ((θ.pullback_outside v).1 i (fun hj => h.2 (scope.1 hj)))
  · intro i hi
    have h := Finset.mem_sdiff.mp hi
    exact ((factor v).2 i h.1).trans
      ((θ.pullback_outside v).2 i (fun hj => h.2 (scope.2 hj)))

end EHMX.HMX

namespace EHMX.HMX
namespace EffectResidualNormalization
variable {O : TypeOrder equalityTypes} (X : Constraints equalityTypes O)

theorem no_effect_domain {s : Substitution equalityTypes} (hs : s.Solved)
    (idEffects : s.effects = Effect.var) : s.domain.effects = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have h := hs.effect_range i hi
  simp [idEffects, Effect.var, hi] at h

theorem scoped_principal_with_effect_residual
    (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {c d : X.Formula} {a u : Names}
    (fresh : X.Avoids c a)
    (outer : X.Admissible P.solved (X.and c (X.existsNames a d)))
    (observed : (X.freeNames (X.and c d)).Subset u) :
    ∃ n : X.NormalForm, n.IsPrincipalOn u P.solved (X.and c d) ∧
      n.substitution.domain.Disjoint (u.diff a) ∧
      n.substitution.effects = Effect.var := by
  obtain ⟨n, θ, φ, run, _, _, _, fixed, _⟩ :=
    scoped_lifting_factor P closure lift fresh outer observed
  have hn := P.principal u (X.and c d) observed n run
  obtain ⟨m, hm, ms, _⟩ :=
    EffectResidualNormalization.retain_effect_assignments X P.solved_satisfiable allow hn
  obtain ⟨ρ, factor, _⟩ := hm.2 n hn.1
  have fixed' : ∀ v : Valuation GroundTy, ∀ i ∈ (u.diff a).types,
      (m.substitution.pullback ((φ.compose ρ).pullback v)).types i = v.types i := by
    intro v i hi
    rw [Substitution.compose_pullback]
    exact ((factor (φ.pullback v)).1 i (Finset.mem_sdiff.mp hi).1).trans
      ((fixed v).1 i hi)
  obtain ⟨k, hk, kt, ke, _⟩ := EffectResidualNormalization.protect_types X closure.rename hm
    (φ.compose ρ) (u.diff a).types (fun _ hi => (Finset.mem_sdiff.mp hi).1) fixed'
  have kid : k.substitution.effects = Effect.var := by
    rw [ke, ms]; rfl
  exact ⟨k, hk, ⟨kt, by simp [no_effect_domain hk.1.2.1 kid]⟩, kid⟩


end EffectResidualNormalization
end EHMX.HMX
