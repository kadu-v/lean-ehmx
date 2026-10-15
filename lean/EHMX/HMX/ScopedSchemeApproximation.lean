import EHMX.HMX.EffectResidualNormalization
import EHMX.HMX.ContextApproximation


/-! Construct generalized scheme approximations for the forall-introduction step.
Projection and the maximal instance comparison are proved, not assumed. -/

set_option maxHeartbeats 2000000

namespace EHMX.HMX.SchemeApproximation
open EHMX EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

theorem projected_residual
    (Q : T.GroundRepresentation)
    {S : X.Formula → Prop} {r d : X.Formula} {u a : Names} {n : X.NormalForm}
    (hr : S r) (truth : ∀ v, X.holds r v)
    (scope : (X.freeNames d).Subset u)
    (hn : n.IsPrincipalOn u S d)
    (protect : n.substitution.domain.Disjoint (u.diff a)) (extra : Names) :
    ∃ b : Names, a.Subset b ∧ n.substitution.domain.Subset b ∧
      b.Disjoint (u.diff a) ∧
      ((X.support n.residual).union extra).Subset ((u.diff a).union b) ∧
      X.Equivalent (X.existsNames a d) (X.existsNames b n.residual) := by
  classical
  let f := u.diff a
  let b := a.union ((((X.support n.residual).union n.substitution.domain).union extra).diff f)
  have ab : a.Subset b := Names.subset_union_left _ _
  have db : n.substitution.domain.Subset b := by
    constructor
    · intro i hi
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hi), fun hf => Finset.disjoint_left.mp protect.1 hi hf⟩)
    · intro i hi
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hi), fun hf => Finset.disjoint_left.mp protect.2 hi hf⟩)
  have bf : b.Disjoint f := by
    constructor <;> apply Finset.disjoint_left.mpr <;> intro i hi hf
    · rcases Finset.mem_union.mp hi with ha | hb
      · exact (Finset.mem_sdiff.mp hf).2 ha
      · exact (Finset.mem_sdiff.mp hb).2 hf
    · rcases Finset.mem_union.mp hi with ha | hb
      · exact (Finset.mem_sdiff.mp hf).2 ha
      · exact (Finset.mem_sdiff.mp hb).2 hf
  have covered : ((X.support n.residual).union extra).Subset (f.union b) := by
    constructor
    · intro i hi
      by_cases hf : i ∈ f.types
      · exact Finset.mem_union_left _ hf
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, hf⟩
        rcases Finset.mem_union.mp hi with hr | he
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hr)
        · exact Finset.mem_union_right _ he
    · intro i hi
      by_cases hf : i ∈ f.effects
      · exact Finset.mem_union_left _ hf
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_sdiff.mpr
        refine ⟨?_, hf⟩
        rcases Finset.mem_union.mp hi with hr | he
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hr)
        · exact Finset.mem_union_right _ he
  refine ⟨b, ab, db, bf, covered, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, outside, hd⟩ := (X.holds_exists _ _ _).mp hv
    obtain ⟨z, hz, same⟩ :=
      (Constraints.NormalForm.principalOn_solutions X Q hr truth scope hn w).mp hd
    let y := v.patch z b
    apply (X.holds_exists _ _ _).mpr
    refine ⟨y, v.patch_agreeOutside z b, (X.holds_support n.residual y z ?_).mpr
      ((X.holds_and _ _ _).mp hz).1⟩
    constructor
    · intro i hi
      by_cases hf : i ∈ f.types
      · have hnb : i ∉ b.types := fun hb => Finset.disjoint_left.mp bf.1 hb hf
        have h := (Finset.mem_sdiff.mp hf)
        simpa [y, Valuation.patch, hnb] using
          ((same.1 i h.1).trans (outside.1 i h.2)).symm
      · have hb : i ∈ b.types := Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hi), hf⟩)
        simp [y, Valuation.patch, hb]
    · intro i hi
      by_cases hf : i ∈ f.effects
      · have hnb : i ∉ b.effects := fun hb => Finset.disjoint_left.mp bf.2 hb hf
        have h := (Finset.mem_sdiff.mp hf)
        simpa [y, Valuation.patch, hnb] using
          ((same.2 i h.1).trans (outside.2 i h.2)).symm
      · have hb : i ∈ b.effects := Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hi), hf⟩)
        simp [y, Valuation.patch, hb]
  · intro v hv
    obtain ⟨w, outside, hR⟩ := (X.holds_exists _ _ _).mp hv
    have hd := (X.holds_subst _ _ _).mp
      (Constraints.NormalForm.reconstruct_entails X hn.1 w hR)
    let z := n.substitution.pullback w
    let y := v.patch z a
    apply (X.holds_exists _ _ _).mpr
    refine ⟨y, v.patch_agreeOutside z a, (X.holds_freeNames scope ?_).mpr hd⟩
    constructor
    · intro i hi
      by_cases ha : i ∈ a.types
      · simp [y, Valuation.patch, ha, z]
      · have hf : i ∈ f.types := Finset.mem_sdiff.mpr ⟨hi, ha⟩
        have hnd : i ∉ n.substitution.domain.types :=
          fun h => Finset.disjoint_left.mp protect.1 h hf
        have hnb : i ∉ b.types := fun h => Finset.disjoint_left.mp bf.1 h hf
        have h := ((n.substitution.pullback_outside w).1 i hnd).trans (outside.1 i hnb)
        simpa [y, Valuation.patch, ha, z] using h.symm
    · intro i hi
      by_cases ha : i ∈ a.effects
      · simp [y, Valuation.patch, ha, z]
      · have hf : i ∈ f.effects := Finset.mem_sdiff.mpr ⟨hi, ha⟩
        have hnd : i ∉ n.substitution.domain.effects :=
          fun h => Finset.disjoint_left.mp protect.2 h hf
        have hnb : i ∉ b.effects := fun h => Finset.disjoint_left.mp bf.2 h hf
        have h := ((n.substitution.pullback_outside w).2 i hnd).trans (outside.2 i hnb)
        simpa [y, Valuation.patch, ha, z] using h.symm


end EHMX.HMX.SchemeApproximation

namespace EHMX.HMX.SchemeApproximation
open EHMX EHMX.HMX
variable {O : TypeOrder equalityTypes} (X : Constraints equalityTypes O)

private theorem context_avoids_of_support {g : Context X} {f b : Names}
    (scope : g.support.Subset f) (fresh : b.Disjoint f) : g.Avoids b := by
  intro s hs
  have member : s.support.Subset g.support := by
    clear scope fresh
    induction g with
    | nil => cases hs
    | cons head tail ih =>
      rcases List.mem_cons.mp hs with rfl | hm
      · exact Names.subset_union_left _ _
      · exact (ih hm).trans (Names.subset_union_right _ _)
  exact ⟨fun i hi hf => Finset.disjoint_left.mp fresh.1 hi
      (scope.1 (member.1 (Scheme.freeType_mem_support hf))),
    fun i hi hf => Finset.disjoint_left.mp fresh.2 hi
      (scope.2 (member.2 (Scheme.freeEffect_mem_support hf)))⟩

end EHMX.HMX.SchemeApproximation
namespace EHMX.HMX.SchemeApproximation
open EHMX EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

theorem source_instance_candidate
    {S : X.Formula → Prop} {c d outer : X.Formula} {a b u : Names}
    {t : T.Term} {n : X.NormalForm}
    (normal : n.IsNormal S (X.and c d))
    (protect : n.substitution.domain.Disjoint (u.diff a))
    (fresh : b.Disjoint (u.diff a))
    (scopeD : (X.freeNames d).Subset u) (scopeT : (T.support t).Subset u)
    (projection : X.Equivalent outer (X.existsNames b n.residual)) :
    Instance X outer (.qualified a d t)
      (.qualified b n.residual (n.substitution.apply t)) := by
  let source : Scheme X := .qualified a d t
  have freshSource : source.Avoids b := by
    constructor
    · intro i hi hf
      apply Finset.disjoint_left.mp fresh.1 hi
      refine Finset.mem_sdiff.mpr ⟨?_, hf.1⟩
      rcases hf.2 with hd | ht
      · exact scopeD.1 ((X.mem_freeNames_types d i).mpr hd)
      · exact scopeT.1 ht
    · intro i hi hf
      apply Finset.disjoint_left.mp fresh.2 hi
      refine Finset.mem_sdiff.mpr ⟨?_, hf.1⟩
      rcases hf.2 with hd | ht
      · exact scopeD.2 ((X.mem_freeNames_effects d i).mpr hd)
      · exact scopeT.2 ht
  have freshOuter : X.Avoids outer b := by
    apply X.avoids_of_transport
    intro v w same hv
    exact projection.2 w ((X.holds_agreeOutside (X.exists_avoids b n.residual) same).mp
      (projection.1 v hv))
  have mono : Instance X (X.and outer n.residual) source
      (.mono (n.substitution.apply t)) := by
    apply Instance.forallLeft (Substitution.restrictTo n.substitution a)
      (Finset.Subset.refl _) (Finset.Subset.refl _)
    · intro v hv
      apply (X.holds_subst _ _ _).mpr
      have hn := (X.holds_subst _ _ _).mp
        (Constraints.NormalForm.reconstruct_entails X normal v
          ((X.holds_and _ _ _).mp hv).2)
      exact (X.holds_freeNames scopeD (Substitution.restrict_agrees protect v)).mpr
        ((X.holds_and _ _ _).mp hn).2
    · apply Instance.sub
      intro v _
      apply (X.holds_le _ _ _).mpr
      rw [Substitution.eval_apply, Substitution.eval_apply,
        T.eval_support _ _ t ((Substitution.restrict_agrees protect v).mono scopeT)]
      exact O.refl _
  have both := Instance.forallRight freshOuter freshSource mono
  exact both.equivalent
    ⟨X.entails_left _ _, fun v hv => (X.holds_and _ _ _).mpr ⟨hv, projection.1 v hv⟩⟩


end EHMX.HMX.SchemeApproximation

namespace EHMX.HMX.SchemeApproximation
open EHMX EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

theorem principal_finite_factor
    {S : X.Formula → Prop}
    (rename : ∀ (p : Renaming) c, X.Admissible S c →
      X.Admissible S (X.subst (p.asSubstitution T) c))
    {u : Names} {d c : X.Formula} {n : X.NormalForm}
    (scope : (X.freeNames d).Subset u) (hn : n.IsPrincipalOn u S d)
    (σ : Substitution T) (hc : X.Admissible S c)
    (entails : X.Entails c (X.subst σ d)) :
    ∃ φ : Substitution T,
      (∀ v, X.holds c v → (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) u) ∧
      X.Entails c (X.subst φ n.residual) := by
  obtain ⟨m, p, normal, images, residual⟩ := X.exists_fresh_normal S rename scope σ hc entails
  obtain ⟨θ, comp⟩ := hn.2 m normal
  let φ := (p.inverse.asSubstitution T).compose θ
  refine ⟨φ, ?_, ?_⟩
  · intro v hv
    rw [Substitution.compose_pullback]
    exact ((comp _ ((X.holds_subst _ _ _).mp (residual v hv))).1).trans (images v)
  · intro v hv
    apply (X.holds_subst _ _ _).mpr
    rw [Substitution.compose_pullback]
    exact (comp _ ((X.holds_subst _ _ _).mp (residual v hv))).2

theorem max_mono
    {S : X.Formula → Prop}
    (rename : ∀ (p : Renaming) c, X.Admissible S c →
      X.Admissible S (X.subst (p.asSubstitution T) c))
    {c d q : X.Formula} {a b u : Names} {n : X.NormalForm} {t target : T.Term}
    (scope : (X.freeNames (X.and c d)).Subset u)
    (scopeT : (T.support t).Subset u)
    (hn : n.IsPrincipalOn u S (X.and c d))
    (protect : n.substitution.domain.Disjoint (u.diff a))
    (covered : ((X.support n.residual).union (T.support (n.substitution.apply t))).Subset
      ((u.diff a).union b))
    (fresh : X.Avoids c a)
    (hq : X.Admissible S q) (qc : X.Entails q c)
    (inst : Instance X q (.qualified a d t) (.mono target)) :
    Instance X q (.qualified b n.residual (n.substitution.apply t)) (.mono target) := by
  obtain ⟨θ, θa, θd, θt⟩ := Instance.qualified_mono_iff.mp inst
  have solves : X.Entails q (X.subst θ (X.and c d)) := by
    intro v hv
    apply (X.holds_subst _ _ _).mpr
    apply (X.holds_and _ _ _).mpr
    refine ⟨?_, (X.holds_subst _ _ _).mp (θd v hv)⟩
    apply (X.holds_agreeOutside fresh ?_).mpr (qc v hv)
    exact ⟨fun i hi => (θ.pullback_outside v).1 i (fun h => hi (θa.1 h)),
      fun i hi => (θ.pullback_outside v).2 i (fun h => hi (θa.2 h))⟩
  obtain ⟨φ, factor, residual⟩ :=
    principal_finite_factor X rename scope hn θ hq solves
  have fixed (v : Valuation T.Value) (hv : X.holds q v) : (φ.pullback v).AgreeOn v (u.diff a) := by
    constructor
    · intro i hi
      have h := Finset.mem_sdiff.mp hi
      have outside : i ∉ n.substitution.domain.types :=
        fun hj => Finset.disjoint_left.mp protect.1 hj hi
      exact ((n.substitution.pullback_outside (φ.pullback v)).1 i outside).symm.trans
        (((factor v hv).1 i h.1).trans
          ((θ.pullback_outside v).1 i (fun hj => h.2 (θa.1 hj))))
    · intro i hi
      have h := Finset.mem_sdiff.mp hi
      have outside : i ∉ n.substitution.domain.effects :=
        fun hj => Finset.disjoint_left.mp protect.2 hj hi
      exact ((n.substitution.pullback_outside (φ.pullback v)).2 i outside).symm.trans
        (((factor v hv).2 i h.1).trans
          ((θ.pullback_outside v).2 i (fun hj => h.2 (θa.2 hj))))
  let η := Substitution.restrictTo φ b
  have same (v : Valuation T.Value) (hv : X.holds q v) : (η.pullback v).AgreeOn (φ.pullback v) ((u.diff a).union b) := by
    constructor
    · intro i hi
      by_cases hb : i ∈ b.types
      · simp [η, Substitution.restrictTo, Substitution.pullback, hb]
      · have hf := (Finset.mem_union.mp hi).resolve_right hb
        simpa [η, Substitution.restrictTo, Substitution.pullback,
          hb, T.eval_var] using ((fixed v hv).1 i hf).symm
    · intro i hi
      by_cases hb : i ∈ b.effects
      · simp [η, Substitution.restrictTo, Substitution.pullback, hb]
      · have hf := (Finset.mem_union.mp hi).resolve_right hb
        simpa [η, Substitution.restrictTo, Substitution.pullback,
          hb, Effect.eval, Effect.var] using ((fixed v hv).2 i hf).symm
  apply Instance.forallLeft η (Finset.Subset.refl _) (Finset.Subset.refl _)
  · intro v hv
    apply (X.holds_subst _ _ _).mpr
    exact (X.holds_support n.residual _ _
      ((same v hv).mono ((Names.subset_union_left _ _).trans covered))).mpr
      ((X.holds_subst _ _ _).mp (residual v hv))
  · apply Instance.sub
    intro v hv
    have h := (X.holds_le _ _ _).mp (θt v hv)
    apply (X.holds_le _ _ _).mpr
    have eqt : T.eval v (η.apply (n.substitution.apply t)) = T.eval v (θ.apply t) := by
      rw [Substitution.eval_apply,
        T.eval_support _ _ (n.substitution.apply t)
          ((same v hv).mono ((Names.subset_union_right _ _).trans covered)),
        Substitution.eval_apply, Substitution.eval_apply]
      exact T.eval_support _ _ t ((factor v hv).mono scopeT)
    rwa [eqt]

theorem approximation_of_admissible_mono
    {S : X.Formula → Prop} (sound : ∀ r, S r → X.Satisfiable r)
    (closure : X.SolvedClosure S)
    {c : X.Formula} {s s' : Scheme X}
    (hc : X.Admissible S c) (admitted : s'.Admissible S)
    (forward : Instance X c s s')
    (mono : ∀ q t, X.Admissible S q → X.Entails q c →
      Instance X q s (.mono t) → Instance X q s' (.mono t)) :
    s.Approximates S c s' := by
  refine ⟨admitted, forward, ?_⟩
  intro target targetAdm inst
  cases target with
  | mono t => exact mono c t hc (X.entails_refl _) inst
  | qualified b q t =>
    obtain ⟨b', q', t', alpha, disjoint⟩ :=
      Scheme.fresh_alpha b q t ((X.support c).union s'.support)
    have fc : X.Avoids c b' :=
      ⟨fun i hi hf => Finset.disjoint_left.mp disjoint.1 hi
        (Finset.mem_union_left _ (X.freeType_mem_support hf)),
       fun i hi hf => Finset.disjoint_left.mp disjoint.2 hi
        (Finset.mem_union_left _ (X.freeEffect_mem_support hf))⟩
    have fs' : s'.Avoids b' :=
      ⟨fun i hi hf => Finset.disjoint_left.mp disjoint.1 hi
        (Finset.mem_union_right _ (Scheme.freeType_mem_support hf)),
       fun i hi hf => Finset.disjoint_left.mp disjoint.2 hi
        (Finset.mem_union_right _ (Scheme.freeEffect_mem_support hf))⟩
    have inst' : Instance X c s (.qualified b' q' t') := .alphaRight alpha inst
    have cq : X.Entails c (X.existsNames b' q') := by
      intro v hv
      obtain ⟨_, w, hw, hq, _⟩ := inst'.target_nonempty hv
      exact (X.holds_exists _ _ _).mpr ⟨w, hw, hq⟩
    have hq : X.Admissible S q' := (alpha.admissible_of_rename closure.rename).mp targetAdm
    have jointSat : X.Satisfiable (X.and c q') := by
      obtain ⟨r, hr, _, back⟩ := hc
      obtain ⟨v, hv⟩ := sound r hr
      obtain ⟨w, hw, hq⟩ := (X.holds_exists _ _ _).mp (cq v (back v hv))
      exact ⟨w, (X.holds_and _ _ _).mpr
        ⟨(X.holds_agreeOutside fc hw).mpr (back v hv), hq⟩⟩
    have jointAdm := closure.conjoin c q' hc hq jointSat
    have eliminate : Instance X (X.and c q') (.qualified b' q' t') (.mono t') := by
      apply Instance.forallLeft (Substitution.identity T)
        (by simp [Substitution.identity, Names.empty])
        (by simp [Substitution.identity, Names.empty])
      · intro v hv
        simpa only [X.holds_subst, Substitution.identity_pullback] using
          ((X.holds_and _ _ _).mp hv).2
      · apply Instance.sub
        intro v _
        exact (X.holds_le _ _ _).mpr (by
          simpa only [Substitution.eval_apply, Substitution.identity_pullback] using O.refl (T.eval v t'))
    have got := mono (X.and c q') t' jointAdm (X.entails_left _ _)
      ((inst'.weaken (X.entails_left _ _)).trans eliminate)
    have result := Instance.forallRight fc fs' got
    have outer : X.Equivalent (X.and c (X.existsNames b' q')) c :=
      ⟨X.entails_left _ _, fun v hv => (X.holds_and _ _ _).mpr ⟨hv, cq v hv⟩⟩
    exact .alphaRight alpha.symm (result.equivalent outer)



end EHMX.HMX.SchemeApproximation

namespace EHMX.HMX.SchemeApproximation
open EHMX EHMX.HMX
variable {O : TypeOrder equalityTypes} (X : Constraints equalityTypes O)

theorem generalized_approximation
    (P : X.ScopedPrincipalNormalizer) (closure : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r c d : X.Formula} {a u : Names} {t : Ty} {g : Context X}
    (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (fresh : X.Avoids c a)
    (outer : X.Admissible P.solved (X.and c (X.existsNames a d)))
    (observed : (X.freeNames (X.and c d)).Subset u)
    (scopeD : (X.freeNames d).Subset u)
    (scopeT : (equalityTypes.support t).Subset u)
    (contextScope : g.support.Subset (u.diff a)) :
    ∃ (n : X.NormalForm) (b : Names),
      n.IsPrincipalOn u P.solved (X.and c d) ∧
      n.substitution.effects = Effect.var ∧
      n.substitution.domain.Disjoint (u.diff a) ∧ b.Disjoint (u.diff a) ∧
      n.substitution.domain.Subset b ∧
      g.Avoids n.substitution.domain ∧ g.Avoids b ∧
      (Scheme.qualified b n.residual (n.substitution.apply t)).support.Subset (u.diff a) ∧
      (Scheme.qualified a d t).Approximates P.solved
        (X.and c (X.existsNames a d))
        (.qualified b n.residual (n.substitution.apply t)) ∧
      X.Equivalent (X.and c (X.existsNames a d)) (X.existsNames b n.residual) := by
  obtain ⟨n, hn, protect, effects⟩ :=
    EHMX.HMX.EffectResidualNormalization.scoped_principal_with_effect_residual X P closure reflect allow lift
      fresh outer observed
  obtain ⟨b, _, db, bf, covered, projection⟩ :=
    EHMX.HMX.SchemeApproximation.projected_residual X equalityGroundRepresentation hr truth
      observed hn protect (equalityTypes.support (n.substitution.apply t))
  have equiv := X.project_and_avoids (d := d) fresh
  have projected : X.Equivalent (X.and c (X.existsNames a d)) (X.existsNames b n.residual) :=
    ⟨X.entails_trans equiv.2 projection.1, X.entails_trans projection.2 equiv.1⟩
  have forward := EHMX.HMX.SchemeApproximation.source_instance_candidate X hn.1 protect bf
    scopeD scopeT projected
  have admitted : (Scheme.qualified b n.residual (n.substitution.apply t)).Admissible P.solved :=
    ⟨n.residual, hn.1.1, X.entails_refl _, X.entails_refl _⟩
  have approx := EHMX.HMX.SchemeApproximation.approximation_of_admissible_mono X
    P.solved_satisfiable closure outer admitted forward
    (fun q target hq entails inst => EHMX.HMX.SchemeApproximation.max_mono X closure.rename
      observed scopeT hn protect covered fresh hq
      (X.entails_trans entails (X.entails_left _ _)) inst)
  have support : (Scheme.qualified b n.residual (n.substitution.apply t)).support.Subset
      (u.diff a) := by
    constructor
    · intro i hi
      obtain ⟨hi, outside⟩ := Finset.mem_sdiff.mp hi
      rcases Finset.mem_union.mp (covered.1 hi) with hf | hb
      · exact hf
      · exact False.elim (outside hb)
    · intro i hi
      obtain ⟨hi, outside⟩ := Finset.mem_sdiff.mp hi
      rcases Finset.mem_union.mp (covered.2 hi) with hf | hb
      · exact hf
      · exact False.elim (outside hb)
  exact ⟨n, b, hn, effects, protect, bf, db,
    context_avoids_of_support X contextScope protect,
    context_avoids_of_support X contextScope bf, support, approx, projected⟩


end EHMX.HMX.SchemeApproximation
