import EHMX.HMX.Declarative

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

theorem Constraints.top_avoids (X : Constraints T O) (a : Names) : X.Avoids X.top a := by
  constructor
  · intro i _ hfree
    apply hfree
    exact ⟨fun v _ => (X.holds_top v).mpr trivial, X.exists_intro _ _⟩
  · intro i _ hfree
    apply hfree
    exact ⟨fun v _ => (X.holds_top v).mpr trivial, X.exists_intro _ _⟩

theorem Constraints.freeType_mem_support (X : Constraints T O)
    {c : X.Formula} {i : Nat} (h : X.FreeType c i) : i ∈ (X.support c).types := by
  by_contra hi
  apply h
  refine ⟨?_, X.exists_intro _ _⟩
  intro v hv
  obtain ⟨w, hw, hc⟩ := (X.holds_exists _ _ _).mp hv
  apply (X.holds_support c w v ?_).mp hc
  constructor
  · intro j hj
    exact hw.1 j (by simpa using fun he : j = i => hi (he ▸ hj))
  · intro j _
    exact hw.2 j (by simp)

theorem Constraints.freeEffect_mem_support (X : Constraints T O)
    {c : X.Formula} {i : Nat} (h : X.FreeEffect c i) : i ∈ (X.support c).effects := by
  by_contra hi
  apply h
  refine ⟨?_, X.exists_intro _ _⟩
  intro v hv
  obtain ⟨w, hw, hc⟩ := (X.holds_exists _ _ _).mp hv
  apply (X.holds_support c w v ?_).mp hc
  constructor
  · intro j _
    exact hw.1 j (by simp)
  · intro j hj
    exact hw.2 j (by simpa using fun he : j = i => hi (he ▸ hj))

theorem Constraints.project_independent (X : Constraints T O) (a : Names)
    (c : X.Formula) (h : a.Disjoint (X.support c)) :
    X.Equivalent (X.existsNames a c) c := by
  refine ⟨?_, X.exists_intro a c⟩
  intro v hv
  obtain ⟨w, hw, hc⟩ := (X.holds_exists a c v).mp hv
  apply (X.holds_support c w v ?_).mp hc
  constructor
  · intro i hi
    exact hw.1 i (fun ha => Finset.disjoint_left.mp h.1 ha hi)
  · intro i hi
    exact hw.2 i (fun ha => Finset.disjoint_left.mp h.2 ha hi)

theorem Scheme.freeType_mem_support {X : Constraints T O}
    {s : Scheme X} {i : Nat} (h : s.FreeType i) : i ∈ s.support.types := by
  cases s with
  | mono t => exact h
  | qualified a c t =>
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr
        (h.2.imp (Constraints.freeType_mem_support X) id), h.1⟩

theorem Scheme.freeEffect_mem_support {X : Constraints T O}
    {s : Scheme X} {i : Nat} (h : s.FreeEffect i) : i ∈ s.support.effects := by
  cases s with
  | mono t => exact h
  | qualified a c t =>
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union.mpr
        (h.2.imp (Constraints.freeEffect_mem_support X) id), h.1⟩

/-- A finite support check is sufficient for logical freshness, even when
the implementation support strictly overapproximates semantic free names. -/
theorem Context.avoids_of_support_disjoint {X : Constraints T O}
    (g : Context X) (a : Names) (h : a.Disjoint g.support) : g.Avoids a := by
  induction g with
  | nil => intro s hs; cases hs
  | cons s g ih =>
      have hs : a.Disjoint s.support := ⟨
        Finset.disjoint_left.mpr fun i hi hj =>
          Finset.disjoint_left.mp h.1 hi (Finset.mem_union_left _ hj),
        Finset.disjoint_left.mpr fun i hi hj =>
          Finset.disjoint_left.mp h.2 hi (Finset.mem_union_left _ hj)⟩
      have hg : a.Disjoint (Context.support g) := ⟨
        Finset.disjoint_left.mpr fun i hi hj =>
          Finset.disjoint_left.mp h.1 hi (Finset.mem_union_right _ hj),
        Finset.disjoint_left.mpr fun i hi hj =>
          Finset.disjoint_left.mp h.2 hi (Finset.mem_union_right _ hj)⟩
      intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨fun i hi hf => Finset.disjoint_left.mp hs.1 hi (Scheme.freeType_mem_support hf),
          fun i hi hf => Finset.disjoint_left.mp hs.2 hi (Scheme.freeEffect_mem_support hf)⟩
      · exact ih hg t ht

/-- The executable choice: generalize the names of the qualification and type
that do not occur in the environment's finite support. -/
def Context.generalizationNames {X : Constraints T O}
    (g : Context X) (c : X.Formula) (t : T.Term) : Names :=
  ((X.support c).union (T.support t)).diff g.support

theorem Context.generalizationNames_avoids {X : Constraints T O}
    (g : Context X) (c : X.Formula) (t : T.Term) :
    g.Avoids (g.generalizationNames c t) := by
  apply g.avoids_of_support_disjoint
  exact ⟨Finset.disjoint_left.mpr fun _ hi hg => (Finset.mem_sdiff.mp hi).2 hg,
    Finset.disjoint_left.mpr fun _ hi hg => (Finset.mem_sdiff.mp hi).2 hg⟩

/-- Canonical generalization is derived from ForallIntro with the prefix `top`.
The complete qualification `c` is retained before existential projection. -/
def Derivation.generalize {sig : Signature T} {X : Constraints T O}
    {c : X.Formula} {g : Context X} {v : Expr} {t : T.Term}
    (tree : Derivation sig X c g v (.mono t) ∅)
    (hv : Value v) (a : Names) (fresh : g.Avoids a) :
    Derivation sig X (X.existsNames a c) g v (.qualified a c t) ∅ := by
  have base : Derivation sig X (X.and X.top c) g v (.mono t) ∅ :=
    .weaken tree (X.entails_right _ _)
  have generalized := Derivation.forallIntro hv (X.top_avoids a) fresh base
  exact .weaken generalized (fun v hc =>
    (X.holds_and _ _ v).mpr ⟨(X.holds_top v).mpr trivial, hc⟩)

/-- The normalized qualification must remain equivalent *before* projection.
This is a lemma about actual typing derivations, not a new solver axiom. -/
def Derivation.generalize_normalized {sig : Signature T} {X : Constraints T O}
    {c : X.Formula} {g : Context X} {v : Expr} {t : T.Term}
    (tree : Derivation sig X c g v (.mono t) ∅)
    (hv : Value v) (N : X.Simplifier) (a : Names) (fresh : g.Avoids a) :
    Derivation sig X (X.existsNames a (N.run c)) g v
      (.qualified a (N.run c) t) ∅ :=
  (Derivation.weaken tree (N.equivalent c).1).generalize hv a fresh

end EHMX.HMX
