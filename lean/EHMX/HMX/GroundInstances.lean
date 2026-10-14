import EHMX.HMX.Validity

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

/-- A value scheme denotes its instances and their admissible supertypes. -/
def Scheme.GroundInstance {X : Constraints T O} : Scheme X → Valuation T.Value → T.Value → Prop
  | .mono t, v, u => O.le (T.eval v t) u
  | .qualified a c t, v, u =>
      ∃ w, w.AgreeOutside v a ∧ X.holds c w ∧ O.le (T.eval w t) u

theorem Scheme.groundInstance_transport {X : Constraints T O}
    (s : Scheme X) (v w : Valuation T.Value)
    (ht : ∀ i, s.FreeType i → v.types i = w.types i)
    (he : ∀ i, s.FreeEffect i → v.effects i = w.effects i)
    {u : T.Value} (hu : s.GroundInstance v u) : s.GroundInstance w u := by
  cases s with
  | mono t =>
      change O.le (T.eval w t) u
      rw [← T.eval_support v w t ⟨ht, he⟩]
      exact hu
  | qualified a c t =>
      obtain ⟨z, hz, hc, hu⟩ := hu
      have hat (i : Nat) (hi : i ∉ a.types)
          (hf : X.FreeType c i ∨ i ∈ (T.support t).types) : z.types i = w.types i :=
        (hz.1 i hi).trans (ht i ⟨hi, hf⟩)
      have hae (i : Nat) (hi : i ∉ a.effects)
          (hf : X.FreeEffect c i ∨ i ∈ (T.support t).effects) : z.effects i = w.effects i :=
        (hz.2 i hi).trans (he i ⟨hi, hf⟩)
      have hct (i : Nat) (hi : X.FreeType c i) : z.types i = (w.patch z a).types i := by
        by_cases ha : i ∈ a.types
        · simp [Valuation.patch, ha]
        · simpa [Valuation.patch, ha] using hat i ha (Or.inl hi)
      have hce (i : Nat) (hi : X.FreeEffect c i) : z.effects i = (w.patch z a).effects i := by
        by_cases ha : i ∈ a.effects
        · simp [Valuation.patch, ha]
        · simpa [Valuation.patch, ha] using hae i ha (Or.inl hi)
      have hval : T.eval z t = T.eval (w.patch z a) t := by
        apply T.eval_support
        constructor
        · intro i hi
          by_cases ha : i ∈ a.types
          · simp [Valuation.patch, ha]
          · simpa [Valuation.patch, ha] using hat i ha (Or.inr hi)
        · intro i hi
          by_cases ha : i ∈ a.effects
          · simp [Valuation.patch, ha]
          · simpa [Valuation.patch, ha] using hae i ha (Or.inr hi)
      exact ⟨w.patch z a, w.patch_agreeOutside z a,
        (X.holds_semanticSupport c z _ hct hce).mp hc, hval ▸ hu⟩

theorem Scheme.groundInstance_support {X : Constraints T O}
    (s : Scheme X) (v w : Valuation T.Value)
    (ht : ∀ i, s.FreeType i → v.types i = w.types i)
    (he : ∀ i, s.FreeEffect i → v.effects i = w.effects i) (u : T.Value) :
    s.GroundInstance v u ↔ s.GroundInstance w u :=
  ⟨s.groundInstance_transport v w ht he,
    s.groundInstance_transport w v (fun i hi => (ht i hi).symm)
      (fun i hi => (he i hi).symm)⟩

theorem Scheme.groundInstance_avoids {X : Constraints T O}
    {s : Scheme X} {a : Names} (hs : s.Avoids a)
    {v w : Valuation T.Value} (hw : v.AgreeOutside w a) (u : T.Value) :
    s.GroundInstance v u ↔ s.GroundInstance w u :=
  s.groundInstance_support v w
    (fun i hi => hw.1 i (fun ha => hs.1 i ha hi))
    (fun i hi => hw.2 i (fun ha => hs.2 i ha hi)) u

theorem Scheme.groundInstance_sub {X : Constraints T O} {s : Scheme X}
    {v : Valuation T.Value} {a b : T.Value} (h : s.GroundInstance v a) (hab : O.le a b) :
    s.GroundInstance v b := by
  cases s with
  | mono t => exact O.trans h hab
  | qualified names c t =>
      obtain ⟨w, hw, hc, ht⟩ := h
      exact ⟨w, hw, hc, O.trans ht hab⟩

theorem Scheme.qualifiedInstance_of_free_agreement {X : Constraints T O}
    {a : Names} {c : X.Formula} {t : T.Term} {v w : Valuation T.Value} {u : T.Value}
    (ht : ∀ i, (Scheme.qualified a c t).FreeType i → w.types i = v.types i)
    (he : ∀ i, (Scheme.qualified a c t).FreeEffect i → w.effects i = v.effects i)
    (hc : X.holds c w) (hu : O.le (T.eval w t) u) :
    (Scheme.qualified a c t).GroundInstance v u :=
  (Scheme.qualified a c t).groundInstance_transport w v ht he
    ⟨w, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, hc, hu⟩

theorem Scheme.groundInstance_rename {X : Constraints T O}
    (p : Renaming) {a : Names} {c : X.Formula} {t : T.Term}
    (ht : ∀ i, (Scheme.qualified a c t).FreeType i → p.types i = i)
    (he : ∀ i, (Scheme.qualified a c t).FreeEffect i → p.effects i = i)
    (v : Valuation T.Value) (u : T.Value) :
    (Scheme.qualified a c t).GroundInstance v u ↔
    (Scheme.qualified ⟨a.types.image p.types, a.effects.image p.effects⟩
      (X.subst (p.asSubstitution T) c) (T.rename p.types p.effects t)).GroundInstance v u := by
  constructor
  · rintro ⟨z, hz, hc, hu⟩
    let b : Names := ⟨a.types.image p.types, a.effects.image p.effects⟩
    let inv : Valuation T.Value := ⟨z.types ∘ p.types.symm, z.effects ∘ p.effects.symm⟩
    let w := v.patch inv b
    have htypes (i : Nat) (hi : X.FreeType c i ∨ i ∈ (T.support t).types) :
        ((p.asSubstitution T).pullback w).types i = z.types i := by
      by_cases ha : i ∈ a.types
      · have hb : p.types i ∈ b.types := Finset.mem_image.mpr ⟨i, ha, rfl⟩
        simp [Substitution.pullback, Renaming.asSubstitution, T.eval_var,
          w, Valuation.patch, hb, inv]
      · have hp := ht i ⟨ha, hi⟩
        have hb : p.types i ∉ b.types := by
          rintro hi
          obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
          exact ha ((p.types.injective hji) ▸ hj)
        have hb' : i ∉ b.types := by simpa only [hp] using hb
        simpa [Substitution.pullback, Renaming.asSubstitution, T.eval_var,
          w, Valuation.patch, hp, hb'] using (hz.1 i ha).symm
    have heffects (i : Nat) (hi : X.FreeEffect c i ∨ i ∈ (T.support t).effects) :
        ((p.asSubstitution T).pullback w).effects i = z.effects i := by
      by_cases ha : i ∈ a.effects
      · have hb : p.effects i ∈ b.effects := Finset.mem_image.mpr ⟨i, ha, rfl⟩
        simp [Substitution.pullback, Renaming.asSubstitution, Effect.eval,
          Effect.var, w, Valuation.patch, hb, inv]
      · have hp := he i ⟨ha, hi⟩
        have hb : p.effects i ∉ b.effects := by
          rintro hi
          obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
          exact ha ((p.effects.injective hji) ▸ hj)
        have hb' : i ∉ b.effects := by simpa only [hp] using hb
        simpa [Substitution.pullback, Renaming.asSubstitution, Effect.eval,
          Effect.var, w, Valuation.patch, hp, hb'] using (hz.2 i ha).symm
    have hc' : X.holds (X.subst (p.asSubstitution T) c) w := by
      apply (X.holds_subst _ _ _).mpr
      exact (X.holds_semanticSupport c _ z (fun i hi => htypes i (.inl hi))
        (fun i hi => heffects i (.inl hi))).mpr hc
    have hval : T.eval w (T.rename p.types p.effects t) = T.eval z t := by
      rw [T.eval_rename]
      have hpb : (p.asSubstitution T).pullback w = ⟨w.types ∘ p.types, w.effects ∘ p.effects⟩ := by
        simp [Substitution.pullback, Renaming.asSubstitution, T.eval_var,
          Effect.eval, Effect.var, Function.comp_def]
      rw [← hpb]
      exact T.eval_support _ z t ⟨fun i hi => htypes i (.inr hi),
        fun i hi => heffects i (.inr hi)⟩
    exact ⟨w, v.patch_agreeOutside inv b, hc', hval.symm ▸ hu⟩
  · rintro ⟨z, hz, hc, hu⟩
    let w := (p.asSubstitution T).pullback z
    apply Scheme.qualifiedInstance_of_free_agreement (w := w)
    · intro i hi
      have hp := ht i hi
      have ha : i ∉ a.types.image p.types := by
        intro hmem
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hmem
        exact hi.1 ((p.types.injective (hji.trans hp.symm)) ▸ hj)
      simpa [w, Substitution.pullback, Renaming.asSubstitution, T.eval_var, hp] using hz.1 i ha
    · intro i hi
      have hp := he i hi
      have ha : i ∉ a.effects.image p.effects := by
        intro hmem
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hmem
        exact hi.1 ((p.effects.injective (hji.trans hp.symm)) ▸ hj)
      simpa [w, Substitution.pullback, Renaming.asSubstitution,
        Effect.eval, Effect.var, hp] using hz.2 i ha
    · exact (X.holds_subst _ _ _).mp hc
    · simpa [w, T.eval_rename, Substitution.pullback, Renaming.asSubstitution,
        T.eval_var, Effect.eval, Effect.var, Function.comp_def] using hu

theorem Scheme.AlphaEquivalent.groundInstance_iff {X : Constraints T O}
    {s t : Scheme X} (h : Scheme.AlphaEquivalent X s t) (v : Valuation T.Value) (u : T.Value) :
    s.GroundInstance v u ↔ t.GroundInstance v u := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | rename p ht he => exact Scheme.groundInstance_rename p ht he v u

def Scheme.MoreGeneralAt {X : Constraints T O}
    (s t : Scheme X) (v w : Valuation T.Value) : Prop :=
  ∀ a, t.GroundInstance w a → s.GroundInstance v a

def Context.MoreGeneralAt {X : Constraints T O}
    (g d : Context X) (v w : Valuation T.Value) : Prop :=
  List.Forall₂ (fun s t => s.MoreGeneralAt t v w) g d

/-- A syntactic instance is covered by its source scheme at every solution of
the ambient constraint. The direction is inclusion of the target's instances. -/
theorem Instance.groundInstance {X : Constraints T O} {c s t}
    (h : Instance X c s t) {v : Valuation T.Value} (hc : X.holds c v)
    {u : T.Value} (hu : t.GroundInstance v u) : s.GroundInstance v u := by
  induction h generalizing v with
  | sub he =>
      exact O.trans ((X.holds_le _ _ v).mp (he v hc)) hu
  | @forallLeft c a d t t' sub ht he hd _ ih =>
      have htype := ih hc hu
      refine ⟨sub.pullback v, ⟨?_, ?_⟩, (X.holds_subst _ _ v).mp (hd v hc), ?_⟩
      · intro i hi
        exact (sub.pullback_outside v).1 i (fun hm => hi (ht hm))
      · intro i hi
        exact (sub.pullback_outside v).2 i (fun hm => hi (he hm))
      · simpa only [Scheme.GroundInstance, sub.eval_apply] using htype
  | forallRight hca hsa _ ih =>
      obtain ⟨w, hw, hd, htype⟩ := hu
      have hcbase := ((X.holds_and _ _ v).mp hc).1
      have hc' := (X.holds_agreeOutside hca hw).mpr hcbase
      have hsource := ih ((X.holds_and _ _ w).mpr ⟨hc', hd⟩) htype
      exact (Scheme.groundInstance_avoids hsa hw u).mp hsource
  | equivalent he _ ih => exact ih (he.2 v hc) hu
  | alphaLeft he _ ih => exact (he.groundInstance_iff v u).mpr (ih hc hu)
  | alphaRight he _ ih => exact ih hc ((he.groundInstance_iff v u).mpr hu)

theorem Scheme.Realizable.groundInstance {X : Constraints T O} {c : X.Formula}
    {s : Scheme X} (h : s.Realizable c) {v : Valuation T.Value} (hc : X.holds c v) :
    ∃ u, s.GroundInstance v u := by
  obtain ⟨t, ht⟩ := h
  exact ⟨T.eval v t, ht.groundInstance hc (O.refl _)⟩

/-- The instance rules require the target qualifier to be inhabited at every
solution of the ambient constraint, including when that constraint is true. -/
theorem Instance.target_nonempty {X : Constraints T O} {c s t}
    (h : Instance X c s t) {v : Valuation T.Value} (hc : X.holds c v) :
    ∃ u, t.GroundInstance v u := by
  induction h generalizing v with
  | sub => exact ⟨_, O.refl _⟩
  | forallLeft => exact ⟨_, O.refl _⟩
  | forallRight =>
      obtain ⟨w, hw, hd⟩ := (X.holds_exists _ _ _).mp ((X.holds_and _ _ _).mp hc).2
      exact ⟨_, w, hw, hd, O.refl _⟩
  | equivalent he _ ih => exact ih (he.2 v hc)
  | alphaLeft _ _ ih => exact ih hc
  | alphaRight he _ ih =>
      obtain ⟨u, hu⟩ := ih hc
      exact ⟨u, (he.groundInstance_iff v u).mp hu⟩

end EHMX.HMX
