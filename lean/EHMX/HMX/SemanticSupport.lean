import EHMX.HMX.Generalization

namespace EHMX.HMX
namespace Constraints
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

theorem avoids_of_transport {c : X.Formula} {a : Names}
    (h : ∀ v w, v.AgreeOutside w a → X.holds c v → X.holds c w) : X.Avoids c a := by
  constructor
  · intro i hi hf
    apply hf
    refine ⟨?_, X.exists_intro _ _⟩
    intro v hv
    obtain ⟨w, hw, hc⟩ := (X.holds_exists _ _ v).mp hv
    apply h w v ⟨?_, ?_⟩ hc
    · intro j hj
      apply hw.1 j
      simpa only [Finset.mem_singleton] using fun he : j = i => hj (he ▸ hi)

    · intro j _; exact hw.2 j (by simp)
  · intro i hi hf
    apply hf
    refine ⟨?_, X.exists_intro _ _⟩
    intro v hv
    obtain ⟨w, hw, hc⟩ := (X.holds_exists _ _ v).mp hv
    apply h w v ⟨?_, ?_⟩ hc
    · intro j _; exact hw.1 j (by simp)
    · intro j hj
      apply hw.2 j
      simpa only [Finset.mem_singleton] using fun he : j = i => hj (he ▸ hi)

theorem exists_avoids (a : Names) (c : X.Formula) : X.Avoids (X.existsNames a c) a := by
  apply X.avoids_of_transport
  intro v w hvw hv
  obtain ⟨u, hu, hc⟩ := (X.holds_exists _ _ _).mp hv
  exact (X.holds_exists _ _ _).mpr ⟨u,
    ⟨fun i hi => (hu.1 i hi).trans (hvw.1 i hi),
      fun i hi => (hu.2 i hi).trans (hvw.2 i hi)⟩, hc⟩

theorem holds_update_type {c : X.Formula} {i : Nat}
    (hi : ¬ X.FreeType c i) (v : Valuation T.Value) (t : T.Value) :
    X.holds c ⟨Function.update v.types i t, v.effects⟩ ↔ X.holds c v := by
  classical
  have he : X.Equivalent (X.existsNames ⟨{i}, ∅⟩ c) c := Classical.not_not.mp hi
  constructor
  · intro hv
    apply he.1 v
    apply (X.holds_exists _ _ _).mpr
    refine ⟨⟨Function.update v.types i t, v.effects⟩, ⟨?_, ?_⟩, hv⟩
    · intro j hj
      exact Function.update_of_ne (by simpa using hj) _ _
    · intro j _; rfl
  · intro hv
    apply he.1
    apply (X.holds_exists _ _ _).mpr
    refine ⟨v, ⟨?_, ?_⟩, hv⟩
    · intro j hj
      exact (Function.update_of_ne (by simpa using hj) _ _).symm
    · intro j _; rfl

theorem holds_update_effect {c : X.Formula} {i : Nat}
    (hi : ¬ X.FreeEffect c i) (v : Valuation T.Value) (e : Finset Op) :
    X.holds c ⟨v.types, Function.update v.effects i e⟩ ↔ X.holds c v := by
  classical
  have he : X.Equivalent (X.existsNames ⟨∅, {i}⟩ c) c := Classical.not_not.mp hi
  constructor
  · intro hv
    apply he.1 v
    apply (X.holds_exists _ _ _).mpr
    refine ⟨⟨v.types, Function.update v.effects i e⟩, ⟨?_, ?_⟩, hv⟩
    · intro j _; rfl
    · intro j hj
      exact Function.update_of_ne (by simpa using hj) _ _
  · intro hv
    apply he.1
    apply (X.holds_exists _ _ _).mpr
    refine ⟨v, ⟨?_, ?_⟩, hv⟩
    · intro j _; rfl
    · intro j hj
      exact (Function.update_of_ne (by simpa using hj) _ _).symm

theorem holds_change_types {c : X.Formula} (a : Finset Nat)
    (ha : ∀ i ∈ a, ¬ X.FreeType c i) (v w : Valuation T.Value)
    (ht : ∀ i, i ∉ a → v.types i = w.types i) (he : v.effects = w.effects) :
    X.holds c v ↔ X.holds c w := by
  classical
  induction a using Finset.induction_on generalizing v with
  | empty =>
      have htypes : v.types = w.types := funext fun i => ht i (by simp)
      have hval : v = w := by cases v; cases w; simp_all
      rw [hval]
  | @insert i a hi ih =>
      let u : Valuation T.Value := ⟨Function.update v.types i (w.types i), v.effects⟩
      have hu : X.holds c u ↔ X.holds c v := X.holds_update_type (ha i (by simp)) v _
      apply hu.symm.trans
      apply ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)) u
      · intro j hj
        by_cases hji : j = i
        · subst j; simp [u]
        · exact (Function.update_of_ne hji _ _).trans (ht j (by simp [hji, hj]))
      · exact he

theorem holds_change_effects {c : X.Formula} (a : Finset Nat)
    (ha : ∀ i ∈ a, ¬ X.FreeEffect c i) (v w : Valuation T.Value)
    (ht : v.types = w.types) (he : ∀ i, i ∉ a → v.effects i = w.effects i) :
    X.holds c v ↔ X.holds c w := by
  classical
  induction a using Finset.induction_on generalizing v with
  | empty =>
      have heffects : v.effects = w.effects := funext fun i => he i (by simp)
      have hval : v = w := by cases v; cases w; simp_all
      rw [hval]
  | @insert i a hi ih =>
      let u : Valuation T.Value := ⟨v.types, Function.update v.effects i (w.effects i)⟩
      have hu : X.holds c u ↔ X.holds c v := X.holds_update_effect (ha i (by simp)) v _
      apply hu.symm.trans
      apply ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)) u ht
      intro j hj
      by_cases hji : j = i
      · subst j; simp [u]
      · exact (Function.update_of_ne hji _ _).trans (he j (by simp [hji, hj]))

/-- Independence uses semantic free names, not an implementation support bound. -/
theorem holds_agreeOutside {c : X.Formula} {a : Names}
    (ha : X.Avoids c a) {v w : Valuation T.Value} (hw : v.AgreeOutside w a) :
    X.holds c v ↔ X.holds c w :=
  (X.holds_change_types a.types ha.1 v ⟨w.types, v.effects⟩ hw.1 rfl).trans
    (X.holds_change_effects a.effects ha.2 ⟨w.types, v.effects⟩ w rfl hw.2)

theorem project_and_avoids {c d : X.Formula} {a : Names} (ha : X.Avoids c a) :
    X.Equivalent (X.existsNames a (X.and c d)) (X.and c (X.existsNames a d)) := by
  constructor
  · intro v hv
    obtain ⟨w, hw, hc⟩ := (X.holds_exists a _ v).mp hv
    obtain ⟨hc, hd⟩ := (X.holds_and c d w).mp hc
    exact (X.holds_and _ _ v).mpr ⟨(X.holds_agreeOutside ha hw).mp hc,
      (X.holds_exists a d v).mpr ⟨w, hw, hd⟩⟩
  · intro v hv
    obtain ⟨hc, hd⟩ := (X.holds_and _ _ v).mp hv
    obtain ⟨w, hw, hd⟩ := (X.holds_exists a d v).mp hd
    exact (X.holds_exists a _ v).mpr ⟨w, hw,
      (X.holds_and c d w).mpr ⟨(X.holds_agreeOutside ha hw).mpr hc, hd⟩⟩

/-- Existential witnesses may depend on each other in either order. This
commutation does not apply across the universal operation parameters. -/
theorem exists_comm (a b : Names) (c : X.Formula) :
    X.Equivalent (X.existsNames a (X.existsNames b c))
      (X.existsNames b (X.existsNames a c)) := by
  have forward (a b : Names) : X.Entails (X.existsNames a (X.existsNames b c))
      (X.existsNames b (X.existsNames a c)) := by
    intro v hv
    obtain ⟨w, hw, hbc⟩ := (X.holds_exists a _ v).mp hv
    obtain ⟨u, hu, hc⟩ := (X.holds_exists b c w).mp hbc
    let z : Valuation T.Value :=
      ⟨fun i => if i ∈ b.types then u.types i else v.types i,
        fun i => if i ∈ b.effects then u.effects i else v.effects i⟩
    have hz : z.AgreeOutside v b :=
      ⟨fun i hi => by simp [z, hi], fun i hi => by simp [z, hi]⟩
    have huz : u.AgreeOutside z a := by
      constructor
      · intro i hi
        by_cases hb : i ∈ b.types
        · simp [z, hb]
        · simpa [z, hb] using (hu.1 i hb).trans (hw.1 i hi)
      · intro i hi
        by_cases hb : i ∈ b.effects
        · simp [z, hb]
        · simpa [z, hb] using (hu.2 i hb).trans (hw.2 i hi)
    exact (X.holds_exists b _ v).mpr ⟨z, hz, (X.holds_exists a c z).mpr ⟨u, huz, hc⟩⟩
  exact ⟨forward a b, forward b a⟩

/-- Inner existential binders shadow all universal names they cover. This is
ordinary lexical scope, not commutation of a universal and an existential. -/
theorem clause_shadow {a b : Names} (hab : a.Subset b) (c : X.Formula) :
    X.Equivalent (X.clause a b c) (X.existsNames b c) := by
  constructor
  · intro v hv
    exact (X.holds_exists b c v).mpr
      ((X.holds_clause a b c v).mp hv v ⟨fun _ _ => rfl, fun _ _ => rfl⟩)
  · intro v hv
    obtain ⟨z, hz, hc⟩ := (X.holds_exists b c v).mp hv
    apply (X.holds_clause a b c v).mpr
    intro w hw
    exact ⟨z, ⟨fun i hi => (hz.1 i hi).trans (hw.1 i (fun ha => hi (hab.1 ha))).symm,
      fun i hi => (hz.2 i hi).trans (hw.2 i (fun ha => hi (hab.2 ha))).symm⟩, hc⟩

/-- Adding local witnesses stays inside the universal operation parameters.
No witnesses are chosen as type expressions, and the quantifier order is kept. -/
theorem clause_exists (rigid locals extra : Names) (c : X.Formula) :
    X.Equivalent (X.clause rigid locals (X.existsNames extra c))
      (X.clause rigid (locals.union extra) c) := by
  constructor
  · intro v hv
    apply (X.holds_clause _ _ _ _).mpr
    intro w hw
    obtain ⟨z, hz, hc⟩ := (X.holds_clause _ _ _ _).mp hv w hw
    obtain ⟨y, hy, hc⟩ := (X.holds_exists _ _ _).mp hc
    refine ⟨y, ⟨?_, ?_⟩, hc⟩
    · intro i hi
      have h := Finset.notMem_union.mp hi
      exact (hy.1 i h.2).trans (hz.1 i h.1)
    · intro i hi
      have h := Finset.notMem_union.mp hi
      exact (hy.2 i h.2).trans (hz.2 i h.1)
  · intro v hv
    apply (X.holds_clause _ _ _ _).mpr
    intro w hw
    obtain ⟨y, hy, hc⟩ := (X.holds_clause _ _ _ _).mp hv w hw
    let z := w.patch y locals
    refine ⟨z, w.patch_agreeOutside y locals, (X.holds_exists _ _ _).mpr ⟨y, ?_, hc⟩⟩
    constructor
    · intro i hi
      by_cases hj : i ∈ locals.types
      · simp [z, Valuation.patch, hj]
      · simpa [z, Valuation.patch, hj] using hy.1 i (Finset.notMem_union.mpr ⟨hj, hi⟩)
    · intro i hi
      by_cases hj : i ∈ locals.effects
      · simp [z, Valuation.patch, hj]
      · simpa [z, Valuation.patch, hj] using hy.2 i (Finset.notMem_union.mpr ⟨hj, hi⟩)

theorem clause_congr (rigid locals : Names) {c d : X.Formula}
    (h : X.Equivalent c d) : X.Equivalent (X.clause rigid locals c) (X.clause rigid locals d) := by
  have forward {c d : X.Formula} (h : X.Entails c d) :
      X.Entails (X.clause rigid locals c) (X.clause rigid locals d) := by
    intro v hv
    apply (X.holds_clause _ _ _ _).mpr
    intro w hw
    obtain ⟨z, hz, hc⟩ := (X.holds_clause _ _ _ _).mp hv w hw
    exact ⟨z, hz, h z hc⟩
  exact ⟨forward h.1, forward h.2⟩

/-- Semantic free names themselves support truth. The finite implementation
support is used only to reduce a possibly infinite valuation change to finitely
many changes at names that are semantically irrelevant. -/
theorem holds_semanticSupport (c : X.Formula) (v w : Valuation T.Value)
    (ht : ∀ i, X.FreeType c i → v.types i = w.types i)
    (he : ∀ i, X.FreeEffect c i → v.effects i = w.effects i) :
    X.holds c v ↔ X.holds c w := by
  classical
  let a : Names := ⟨(X.support c).types.filter (fun i => ¬ X.FreeType c i),
    (X.support c).effects.filter (fun i => ¬ X.FreeEffect c i)⟩
  let u : Valuation T.Value :=
    ⟨fun i => if i ∈ (X.support c).types then w.types i else v.types i,
      fun i => if i ∈ (X.support c).effects then w.effects i else v.effects i⟩
  have ha : X.Avoids c a := ⟨fun i hi => (Finset.mem_filter.mp hi).2,
    fun i hi => (Finset.mem_filter.mp hi).2⟩
  have hu : u.AgreeOutside v a := by
    constructor
    · intro i hi
      by_cases hs : i ∈ (X.support c).types
      · have hf : X.FreeType c i := by
          by_contra hn
          exact hi (Finset.mem_filter.mpr ⟨hs, hn⟩)
        simp [u, hs, ht i hf]
      · simp [u, hs]
    · intro i hi
      by_cases hs : i ∈ (X.support c).effects
      · have hf : X.FreeEffect c i := by
          by_contra hn
          exact hi (Finset.mem_filter.mpr ⟨hs, hn⟩)
        simp [u, hs, he i hf]
      · simp [u, hs]
  exact (X.holds_agreeOutside ha hu).symm.trans (X.holds_support c u w
    ⟨fun i hi => by simp [u, hi], fun i hi => by simp [u, hi]⟩)

/-- The exact finite semantic observation set. An implementation support can
retain projected names; filtering it prevents those names from being fixed by
the normal-form comparison. This is not a decidable free-variable algorithm. -/
noncomputable def freeNames (c : X.Formula) : Names := by
  classical
  exact ⟨(X.support c).types.filter (X.FreeType c),
    (X.support c).effects.filter (X.FreeEffect c)⟩

theorem mem_freeNames_types (c : X.Formula) (i : Nat) :
    i ∈ (X.freeNames c).types ↔ X.FreeType c i := by
  classical
  simp only [freeNames, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨X.freeType_mem_support h, h⟩⟩

theorem mem_freeNames_effects (c : X.Formula) (i : Nat) :
    i ∈ (X.freeNames c).effects ↔ X.FreeEffect c i := by
  classical
  simp only [freeNames, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨X.freeEffect_mem_support h, h⟩⟩

theorem holds_freeNames {c : X.Formula} {u : Names}
    (scope : (X.freeNames c).Subset u) {v w : Valuation T.Value}
    (same : v.AgreeOn w u) : X.holds c v ↔ X.holds c w :=
  X.holds_semanticSupport c v w
    (fun i hi => same.1 i (scope.1 ((X.mem_freeNames_types c i).mpr hi)))
    (fun i hi => same.2 i (scope.2 ((X.mem_freeNames_effects c i).mpr hi)))

theorem freeNames_exists_disjoint (a : Names) (c : X.Formula) :
    a.Disjoint (X.freeNames (X.existsNames a c)) :=
  ⟨Finset.disjoint_left.mpr (fun i hi hj =>
      (X.exists_avoids a c).1 i hi ((X.mem_freeNames_types _ i).mp hj)),
    Finset.disjoint_left.mpr (fun i hi hj =>
      (X.exists_avoids a c).2 i hi ((X.mem_freeNames_effects _ i).mp hj))⟩

end Constraints
end EHMX.HMX
