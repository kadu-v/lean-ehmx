import EHMX.HMX.ContextSubstitution
import EHMX.HMX.ScopedNormalization

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

/-- Pointwise approximation preserves the order and length of the environment.
This is a relation on whole schemes, not only their ground interpretations. -/
def Context.Approximates (solved : X.Formula → Prop) (c : X.Formula)
    (source target : Context X) : Prop :=
  List.Forall₂ (Scheme.Approximates solved c) source target

/-- Reflexivity only needs an instance at each valuation. It does not require
one finite substitution working uniformly at all valuations. -/
theorem Scheme.Approximates.refl_of_ground {S : X.Formula → Prop}
    {c : X.Formula} {s : Scheme X} (admitted : s.Admissible S)
    (inhabited : ∀ v, X.holds c v → ∃ t, s.GroundInstance v t) :
    s.Approximates S c s :=
  ⟨admitted, Instance.of_mono_targets inhabited (fun _ _ _ h => h), fun _ _ h => h⟩

/-- In particular, a result that is already admissible can be retained even
when it is not uniformly realizable. This applies to let-bound value schemes. -/
theorem Typing.result_approximates_self {sig : Signature T}
    {S S' : X.Formula → Prop} {c : X.Formula} {g : Context X}
    {e : Expr} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X S c g e s eff) (admitted : s.Admissible S')
    (inhabited : ∀ v, X.holds c v → g.GroundRealizable v) :
    s.Approximates S' c s := by
  obtain ⟨tree, _⟩ := typed
  exact Scheme.Approximates.refl_of_ground admitted
    (fun v hv => tree.groundInstance_exists v hv (inhabited v hv))

theorem Context.Approximates.refl_of_ground {S : X.Formula → Prop}
    {c : X.Formula} {g : Context X} (admitted : g.Admissible S)
    (inhabited : ∀ v, X.holds c v → g.GroundRealizable v) :
    g.Approximates S c g := by
  induction g with
  | nil => exact .nil
  | cons s g ih =>
      exact .cons
        (Scheme.Approximates.refl_of_ground (admitted s (by simp))
          (fun v hv => inhabited v hv s (by simp)))
        (ih (fun t ht => admitted t (List.mem_cons_of_mem _ ht))
          (fun v hv t ht => inhabited v hv t (List.mem_cons_of_mem _ ht)))

theorem Context.Approximates.admissible {S : X.Formula → Prop} {c : X.Formula}
    {g g' : Context X} (h : g.Approximates S c g') : g'.Admissible S := by
  induction h with
  | nil => intro s hs; cases hs
  | cons h _ ih => exact Context.admissible_cons ih h.1

theorem Context.Approximates.realizable {S : X.Formula → Prop} {c : X.Formula}
    {g g' : Context X} (h : g.Approximates S c g') (real : g.Realizable c) :
    g'.Realizable c := real.approximate h

/-- Approximation cannot repair the absence of a uniform instance: its
forward instance comparison also reflects realizability. -/
theorem Scheme.Approximates.realizable_iff {S : X.Formula → Prop} {c : X.Formula}
    {s t : Scheme X} (h : s.Approximates S c t) : s.Realizable c ↔ t.Realizable c := by
  refine ⟨h.realizable, ?_⟩
  rintro ⟨u, hu⟩
  exact ⟨u, h.2.1.trans hu⟩

theorem Context.Approximates.refl {S : X.Formula → Prop} {c : X.Formula}
    {g : Context X} (valid : g.Admissible S) (real : g.Realizable c) :
    g.Approximates S c g := by
  induction g with
  | nil => exact .nil
  | cons s g ih =>
      exact .cons (Scheme.Approximates.refl (valid s (by simp)) (real s (by simp)))
        (ih (fun s hs => valid s (List.mem_cons_of_mem _ hs))
          (fun s hs => real s (List.mem_cons_of_mem _ hs)))

theorem Scheme.Approximates.trans {S : X.Formula → Prop} {c : X.Formula}
    {s t u : Scheme X} (h : s.Approximates S c t) (k : t.Approximates S c u) :
    s.Approximates S c u :=
  ⟨k.1, h.2.1.trans k.2.1, fun v hv hi => k.2.2 v hv (h.2.2 v hv hi)⟩

theorem Context.Approximates.trans {S : X.Formula → Prop} {c : X.Formula}
    {g g' g'' : Context X} (h : g.Approximates S c g') (k : g'.Approximates S c g'') :
    g.Approximates S c g'' := by
  induction h generalizing g'' with
  | nil => cases k; exact .nil
  | cons hs _ ih =>
      cases k with
      | cons ks kg => exact .cons (hs.trans ks) (ih kg)

theorem Context.Approximates.lookup {S : X.Formula → Prop} {c : X.Formula}
    {g g' : Context X} (h : g.Approximates S c g') {i : Nat} {s : Scheme X}
    (found : g[i]? = some s) :
    ∃ t, g'[i]? = some t ∧ s.Approximates S c t := by
  induction h generalizing i with
  | nil => simp at found
  | cons hs _ ih =>
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                subst s
                exact ⟨_, rfl, hs⟩
      | succ i => exact ih found

/-- After environment approximation, a variable retains every admissible
uniform monotype instance. The target variable derivation is valid in S. -/
theorem Context.Approximates.variable {sig : Signature T}
    {S : X.Formula → Prop} {c : X.Formula} {g g' : Context X}
    (h : g.Approximates S c g') (hc : X.Admissible S c)
    {i : Nat} {s : Scheme X} {t : T.Term}
    (found : g[i]? = some s) (inst : Instance X c s (.mono t)) :
    Typing sig X S c g' (.var i) (.mono t) ∅ := by
  obtain ⟨s', found', approx⟩ := h.lookup found
  have typed : Typing sig X S c g' (.var i) s' ∅ :=
    ⟨.var found', hc, h.admissible, approx.1, trivial⟩
  exact typed.instance_mono (approx.2.2 (.mono t) trivial inst)

/-- Apply a syntactic instance comparison to a value, including a qualified
target. Freshening the target binder protects the environment. All newly
introduced constraints are admissible in the same solved set. -/
theorem Typing.instance_value {sig : Signature T} {S : X.Formula → Prop}
    (sound : ∀ d, S d → X.Satisfiable d) (closure : X.SolvedClosure S)
    {c : X.Formula} {g : Context X} {e : Expr} {s t : Scheme X}
    (typed : Typing sig X S c g e s ∅) (value : Value e)
    (inst : Instance X c s t) (admitted : t.Admissible S) :
    Typing sig X S c g e t ∅ := by
  cases t with
  | mono u => exact typed.instance_mono inst
  | qualified a d u =>
      obtain ⟨b, q, v, alpha, fresh⟩ :=
        Scheme.fresh_alpha a d u ((X.support c).union g.support)
      have hq : X.Admissible S q :=
        (alpha.admissible_of_rename closure.rename).mp admitted
      have hc : X.Avoids c b :=
        ⟨fun i hi hf => Finset.disjoint_left.mp fresh.1 hi
          (Finset.mem_union_left _ (X.freeType_mem_support hf)),
         fun i hi hf => Finset.disjoint_left.mp fresh.2 hi
          (Finset.mem_union_left _ (X.freeEffect_mem_support hf))⟩
      have hg : g.Avoids b := g.avoids_of_support_disjoint b
        (fresh.mono_right (Names.subset_union_right _ _))
      have inst' : Instance X c s (.qualified b q v) := .alphaRight alpha inst
      have project : X.Entails c (X.existsNames b q) := by
        intro w hw
        obtain ⟨_, z, hz, hq, _⟩ := inst'.target_nonempty hw
        exact (X.holds_exists _ _ _).mpr ⟨z, hz, hq⟩
      have equivalent : X.Equivalent (X.and c (X.existsNames b q)) c :=
        ⟨X.entails_left _ _, fun w hw => (X.holds_and _ _ _).mpr ⟨hw, project w hw⟩⟩
      have outer : X.Admissible S (X.and c (X.existsNames b q)) := by
        obtain ⟨r, hr, forward, backward⟩ := typed.root.1
        exact ⟨r, hr, X.entails_trans equivalent.1 forward,
          X.entails_trans backward equivalent.2⟩
      have sat : X.Satisfiable (X.and c q) := by
        obtain ⟨w, hw⟩ := (X.admissible_satisfiable_iff c).mp
          (typed.to_satisfiable sound).root.1
        obtain ⟨z, hz, hq⟩ := (X.holds_exists _ _ _).mp (project w hw)
        exact ⟨z, (X.holds_and _ _ _).mpr
          ⟨(X.holds_agreeOutside hc hz).mpr hw, hq⟩⟩
      have both := closure.conjoin c q typed.root.1 hq sat
      have eliminate : Instance X (X.and c q) (.qualified b q v) (.mono v) := by
        apply Instance.forallLeft (Substitution.identity T)
          (by simp [Substitution.identity, Names.empty])
          (by simp [Substitution.identity, Names.empty])
        · intro w hw
          simpa only [X.holds_subst, Substitution.identity_pullback] using
            ((X.holds_and _ _ _).mp hw).2
        · apply Instance.sub
          intro w _
          exact (X.holds_le _ _ _).mpr (by
            simpa only [Substitution.eval_apply, Substitution.identity_pullback] using
              O.refl (T.eval w v))
      have body := (typed.weaken both (X.entails_left _ _)).instance_mono
        ((inst'.weaken (X.entails_left _ _)).trans eliminate)
      obtain ⟨tree, valid⟩ := body
      have generalized : Typing sig X S (X.and c (X.existsNames b q)) g e
          (.qualified b q v) ∅ :=
        ⟨.forallIntro value hc hg tree, outer, typed.root.2.1, hq, valid⟩
      exact (generalized.weaken typed.root.1 equivalent.2).alpha alpha.symm admitted

/-- The variable case of Theorem 7 also preserves qualified admissible
targets; it is not restricted to monotype elimination. -/
theorem Context.Approximates.variable_scheme {sig : Signature T}
    {S : X.Formula → Prop} (sound : ∀ d, S d → X.Satisfiable d)
    (closure : X.SolvedClosure S) {c : X.Formula} {g g' : Context X}
    (h : g.Approximates S c g') (hc : X.Admissible S c)
    {i : Nat} {s t : Scheme X} (found : g[i]? = some s)
    (inst : Instance X c s t) (admitted : t.Admissible S) :
    Typing sig X S c g' (.var i) t ∅ := by
  obtain ⟨s', found', approx⟩ := h.lookup found
  have typed : Typing sig X S c g' (.var i) s' ∅ :=
    ⟨.var found', hc, h.admissible, approx.1, trivial⟩
  exact typed.instance_value sound closure (.var i) (approx.2.2 t admitted inst) admitted

end EHMX.HMX

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

theorem Scheme.Approximates.subst_congr {s s' : Scheme X}
    {S : X.Formula → Prop} {c : X.Formula} (σ τ : Substitution T)
    (ht : ∀ v i, s.FreeType i → (σ.pullback v).types i = (τ.pullback v).types i)
    (he : ∀ v i, s.FreeEffect i → (σ.pullback v).effects i = (τ.pullback v).effects i)
    (h : (s.subst σ).Approximates S c s') :
    (s.subst τ).Approximates S c s' := by
  refine ⟨h.1, Instance.subst_congr σ τ ht he h.2.1, ?_⟩
  intro target adm inst
  exact h.2.2 target adm (Instance.subst_congr τ σ
    (fun v i hi => (ht v i hi).symm) (fun v i hi => (he v i hi).symm) inst)

theorem Context.Approximates.subst_congr {g g' : Context X}
    {S : X.Formula → Prop} {c : X.Formula} (σ τ : Substitution T)
    (ht : ∀ s ∈ g, ∀ v i, s.FreeType i → (σ.pullback v).types i = (τ.pullback v).types i)
    (he : ∀ s ∈ g, ∀ v i, s.FreeEffect i → (σ.pullback v).effects i = (τ.pullback v).effects i)
    (h : (g.subst σ).Approximates S c g') :
    (g.subst τ).Approximates S c g' := by
  induction g generalizing g' with
  | nil => cases h; exact .nil
  | cons s g ih =>
    cases h with
    | cons hs hg =>
      exact .cons
        (Scheme.Approximates.subst_congr σ τ (ht s (by simp)) (he s (by simp)) hs)
        (ih (fun t hm => ht t (List.mem_cons_of_mem _ hm))
          (fun t hm => he t (List.mem_cons_of_mem _ hm)) hg)

private theorem member_support {g : Context X} {s : Scheme X} (hs : s ∈ g) :
    s.support.Subset g.support := by
  induction g with
  | nil => cases hs
  | cons head tail ih =>
    rcases List.mem_cons.mp hs with rfl | hm
    · exact Names.subset_union_left _ _
    · exact (ih hm).trans (Names.subset_union_right _ _)

theorem Context.Approximates.underBinder_compose {g g' : Context X}
    {S : X.Formula → Prop} {c : X.Formula}
    (θ κ : Substitution T) (a : Names) (ft fe : Nat → Nat)
    (fresh : g.Avoids a)
    (protect : κ.domain.Disjoint (g.support.union θ.range))
    (h : (g.subst θ).Approximates S c g') :
    (g.subst (κ.compose (θ.underBinder a ft fe))).Approximates S c g' := by
  apply Context.Approximates.subst_congr θ _ ?_ ?_ h
  · intro s hs v i hi
    have outside : i ∉ a.types := fun ha => (fresh s hs).1 i ha hi
    have si : i ∈ g.support.types :=
      (member_support hs).1 (Scheme.freeType_mem_support hi)
    have support := θ.type_support_subset g.support si
    have same : (κ.pullback v).AgreeOn v (T.support (θ.types i)) := by
      constructor
      · intro j hj
        exact (κ.pullback_outside v).1 j
          (fun hm => Finset.disjoint_left.mp protect.1 hm (support.1 hj))
      · intro j hj
        exact (κ.pullback_outside v).2 j
          (fun hm => Finset.disjoint_left.mp protect.2 hm (support.2 hj))
    rw [Substitution.compose_pullback]
    simpa only [Substitution.pullback,
      Substitution.underBinder, outside, ite_false] using
      (T.eval_support _ _ (θ.types i) same).symm
  · intro s hs v i hi
    have outside : i ∉ a.effects := fun ha => (fresh s hs).2 i ha hi
    have si : i ∈ g.support.effects :=
      (member_support hs).2 (Scheme.freeEffect_mem_support hi)
    have support := θ.effect_support_subset g.support si
    have same : ∀ j ∈ (θ.effects i).vars, (κ.pullback v).effects j = v.effects j := by
      intro j hj
      exact (κ.pullback_outside v).2 j
        (fun hm => Finset.disjoint_left.mp protect.2 hm (support hj))
    rw [Substitution.compose_pullback]
    simpa only [Substitution.pullback,
      Substitution.underBinder, outside, ite_false] using
      (Effect.eval_support (θ.effects i) _ _ same).symm



end EHMX.HMX
namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}
theorem Scheme.Approximates.project_mono {S : X.Formula → Prop}
    {c r : X.Formula} {a : Names} {s s' : Scheme X} {t : T.Term}
    (h : s.Approximates S c s') (hr : X.Admissible S r)
    (proj : X.Equivalent c (X.existsNames a r))
    (freshC : X.Avoids c a) (freshS : s.Avoids a)
    (inst : Instance X r s (.mono t)) : Instance X r s' (.mono t) := by
  have outer : X.Equivalent (X.and c (X.existsNames a r)) c :=
    ⟨X.entails_left _ _, fun v hv => (X.holds_and _ _ _).mpr ⟨hv, proj.1 v hv⟩⟩
  have package : Instance X c s (.qualified a r t) :=
    (Instance.forallRight freshC freshS (inst.weaken (X.entails_right _ _))).equivalent outer
  have got := h.2.2 (.qualified a r t) hr package
  have rToC : X.Entails r c := X.entails_trans (X.exists_intro a r) proj.2
  have elim : Instance X r (.qualified a r t) (.mono t) := by
    apply Instance.forallLeft (Substitution.identity T)
      (by simp [Substitution.identity, Names.empty])
      (by simp [Substitution.identity, Names.empty])
    · intro v hv
      simpa only [X.holds_subst, Substitution.identity_pullback] using hv
    · apply Instance.sub
      intro v _
      exact (X.holds_le _ _ _).mpr (by
        simpa only [Substitution.eval_apply, Substitution.identity_pullback] using O.refl (T.eval v t))
  exact (got.weaken rToC).trans elim

theorem Scheme.Approximates.project {S : X.Formula → Prop}
    (sound : ∀ d, S d → X.Satisfiable d) (closure : X.SolvedClosure S)
    {c r : X.Formula} {a : Names} {s s' : Scheme X}
    (h : s.Approximates S c s') (hr : X.Admissible S r)
    (proj : X.Equivalent c (X.existsNames a r))
    (freshC : X.Avoids c a) (freshS : s.Avoids a) :
    s.Approximates S r s' := by
  have rToC : X.Entails r c := X.entails_trans (X.exists_intro a r) proj.2
  refine ⟨h.1, h.2.1.weaken rToC, ?_⟩
  intro target admitted inst
  cases target with
  | mono t => exact Scheme.Approximates.project_mono h hr proj freshC freshS inst
  | qualified b q t =>
    let avoid := ((X.support c).union (X.support r)).union
      (s.support.union s'.support)
    obtain ⟨b', q', t', alpha, disjoint⟩ := Scheme.fresh_alpha b q t avoid
    have fc : X.Avoids c b' :=
      ⟨fun i hi hf => Finset.disjoint_left.mp disjoint.1 hi
        (Finset.mem_union_left _ (Finset.mem_union_left _ (X.freeType_mem_support hf))),
       fun i hi hf => Finset.disjoint_left.mp disjoint.2 hi
        (Finset.mem_union_left _ (Finset.mem_union_left _ (X.freeEffect_mem_support hf)))⟩
    have fr : X.Avoids r b' :=
      ⟨fun i hi hf => Finset.disjoint_left.mp disjoint.1 hi
        (Finset.mem_union_left _ (Finset.mem_union_right _ (X.freeType_mem_support hf))),
       fun i hi hf => Finset.disjoint_left.mp disjoint.2 hi
        (Finset.mem_union_left _ (Finset.mem_union_right _ (X.freeEffect_mem_support hf)))⟩
    have fs : s.Avoids b' :=
      ⟨fun i hi hf => Finset.disjoint_left.mp disjoint.1 hi
        (Finset.mem_union_right _ (Finset.mem_union_left _ (Scheme.freeType_mem_support hf))),
       fun i hi hf => Finset.disjoint_left.mp disjoint.2 hi
        (Finset.mem_union_right _ (Finset.mem_union_left _ (Scheme.freeEffect_mem_support hf)))⟩
    have fs' : s'.Avoids b' :=
      ⟨fun i hi hf => Finset.disjoint_left.mp disjoint.1 hi
        (Finset.mem_union_right _ (Finset.mem_union_right _ (Scheme.freeType_mem_support hf))),
       fun i hi hf => Finset.disjoint_left.mp disjoint.2 hi
        (Finset.mem_union_right _ (Finset.mem_union_right _ (Scheme.freeEffect_mem_support hf)))⟩
    have inst' : Instance X r s (.qualified b' q' t') := .alphaRight alpha inst
    have rq : X.Entails r (X.existsNames b' q') := by
      intro v hv
      obtain ⟨_, w, hw, hq, _⟩ := inst'.target_nonempty hv
      exact (X.holds_exists _ _ _).mpr ⟨w, hw, hq⟩
    have hq : X.Admissible S q' := (alpha.admissible_of_rename closure.rename).mp admitted
    have jointSat : X.Satisfiable (X.and r q') := by
      obtain ⟨rr, hrr, _, back⟩ := hr
      obtain ⟨v, hv⟩ := sound rr hrr
      obtain ⟨w, hw, hq⟩ := (X.holds_exists _ _ _).mp (rq v (back v hv))
      exact ⟨w, (X.holds_and _ _ _).mpr
        ⟨(X.holds_agreeOutside fr hw).mpr (back v hv), hq⟩⟩
    have jointAdm := closure.conjoin r q' hr hq jointSat
    have fcUnion : X.Avoids c (a.union b') := by
      constructor
      · intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact freshC.1 i hi
        · exact fc.1 i hi
      · intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact freshC.2 i hi
        · exact fc.2 i hi
    have fsUnion : s.Avoids (a.union b') := by
      constructor
      · intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact freshS.1 i hi
        · exact fs.1 i hi
      · intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · exact freshS.2 i hi
        · exact fs.2 i hi
    have projection : X.Equivalent c (X.existsNames (a.union b') (X.and r q')) := by
      constructor
      · intro v hv
        obtain ⟨w, hw, hwr⟩ := (X.holds_exists _ _ _).mp (proj.1 v hv)
        obtain ⟨z, hz, hzq⟩ := (X.holds_exists _ _ _).mp (rq w hwr)
        apply (X.holds_exists _ _ _).mpr
        refine ⟨z, ?_, (X.holds_and _ _ _).mpr
          ⟨(X.holds_agreeOutside fr hz).mpr hwr, hzq⟩⟩
        constructor
        · intro i hi
          have nots := Finset.notMem_union.mp hi
          exact (hz.1 i nots.2).trans (hw.1 i nots.1)
        · intro i hi
          have nots := Finset.notMem_union.mp hi
          exact (hz.2 i nots.2).trans (hw.2 i nots.1)
      · intro v hv
        obtain ⟨w, hw, hrq⟩ := (X.holds_exists _ _ _).mp hv
        exact (X.holds_agreeOutside fcUnion hw).mp
          (rToC w ((X.holds_and _ _ _).mp hrq).1)
    have eliminate : Instance X (X.and r q') (.qualified b' q' t') (.mono t') := by
      apply Instance.forallLeft (Substitution.identity T)
        (by simp [Substitution.identity, Names.empty])
        (by simp [Substitution.identity, Names.empty])
      · intro v hv
        simpa only [X.holds_subst, Substitution.identity_pullback] using
          ((X.holds_and _ _ _).mp hv).2
      · apply Instance.sub
        intro v _
        exact (X.holds_le _ _ _).mpr (by
          simpa only [Substitution.eval_apply, Substitution.identity_pullback]
            using O.refl (T.eval v t'))
    have mono := Scheme.Approximates.project_mono h jointAdm projection fcUnion fsUnion
      ((inst'.weaken (X.entails_left _ _)).trans eliminate)
    have result := Instance.forallRight fr fs' mono
    have outer : X.Equivalent (X.and r (X.existsNames b' q')) r :=
      ⟨X.entails_left _ _, fun v hv => (X.holds_and _ _ _).mpr ⟨hv, rq v hv⟩⟩
    exact .alphaRight alpha.symm (result.equivalent outer)
end EHMX.HMX

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

theorem Scheme.Approximates.subst_identity_iff {S : X.Formula → Prop} {c : X.Formula} (s target : Scheme X) :
    (s.subst (Substitution.identity T)).Approximates S c target ↔
      s.Approximates S c target := by
  constructor
  · intro h
    exact ⟨h.1, (Instance.subst_identity_iff s target).mp h.2.1,
      fun u hu hi => h.2.2 u hu ((Instance.subst_identity_iff s u).mpr hi)⟩
  · intro h
    exact ⟨h.1, (Instance.subst_identity_iff s target).mpr h.2.1,
      fun u hu hi => h.2.2 u hu ((Instance.subst_identity_iff s u).mp hi)⟩

theorem Context.Approximates.subst_identity {S : X.Formula → Prop} {c : X.Formula} {g g' : Context X}
    (h : g.Approximates S c g') :
    (g.subst (Substitution.identity T)).Approximates S c g' := by
  induction h with
  | nil => exact .nil
  | cons hs hg ih => exact .cons ((Scheme.Approximates.subst_identity_iff _ _).mpr hs) ih



end EHMX.HMX
