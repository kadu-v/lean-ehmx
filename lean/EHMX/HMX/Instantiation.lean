import EHMX.HMX.GroundInstances

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

private noncomputable def assignImage {A : Type} (bound : Finset Nat)
    (rename : Nat → Nat) (values original : Nat → A) (j : Nat) : A :=
  if h : ∃ i, i ∈ bound ∧ rename i = j then values (Classical.choose h) else original j

private theorem assignImage_mem {A : Type} (bound : Finset Nat) (rename : Nat → Nat)
    (hinj : Set.InjOn rename bound) (values original : Nat → A) (i : Nat) (hi : i ∈ bound) :
    assignImage bound rename values original (rename i) = values i := by
  let h : ∃ k, k ∈ bound ∧ rename k = rename i := ⟨i, hi, rfl⟩
  have hc := Classical.choose_spec h
  have hki : Classical.choose h = i := hinj hc.1 hi hc.2
  simp [assignImage, h, hki]

private theorem assignImage_not_mem {A : Type} (bound : Finset Nat) (rename : Nat → Nat)
    (values original : Nat → A) (j : Nat) (hj : j ∉ bound.image rename) :
    assignImage bound rename values original j = original j := by
  have hnone : ¬ ∃ i, i ∈ bound ∧ rename i = j := by
    rintro ⟨i, hi, rfl⟩
    exact hj (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  simp [assignImage, hnone]

/-- Rename precisely the quantified variables by a finite simultaneous
substitution; the maps need only be injective on their finite domains. -/
def Substitution.freshen (T : TypeDomain) (a : Names) (ft fe : Nat → Nat) : Substitution T where
  domain := a
  types := fun i => if i ∈ a.types then T.var (ft i) else T.var i
  effects := fun i => if i ∈ a.effects then Effect.var (fe i) else Effect.var i
  types_outside := by intro i hi; simp [hi]
  effects_outside := by intro i hi; simp [hi]

noncomputable def Valuation.assignImages {V : Type} (v z : Valuation V) (a : Names)
    (ft fe : Nat → Nat) : Valuation V :=
  ⟨assignImage a.types ft z.types v.types, assignImage a.effects fe z.effects v.effects⟩

theorem Valuation.assignImages_types {V : Type} (v z : Valuation V) (a : Names)
    (ft fe : Nat → Nat) (ht : Set.InjOn ft a.types) (i : Nat) (hi : i ∈ a.types) :
    (v.assignImages z a ft fe).types (ft i) = z.types i :=
  assignImage_mem a.types ft ht z.types v.types i hi

theorem Valuation.assignImages_effects {V : Type} (v z : Valuation V) (a : Names)
    (ft fe : Nat → Nat) (he : Set.InjOn fe a.effects) (i : Nat) (hi : i ∈ a.effects) :
    (v.assignImages z a ft fe).effects (fe i) = z.effects i :=
  assignImage_mem a.effects fe he z.effects v.effects i hi

theorem Valuation.assignImages_agree {V : Type} (v z : Valuation V) (a : Names)
    (ft fe : Nat → Nat) (fixed : Names)
    (ht : Disjoint (a.types.image ft) fixed.types)
    (he : Disjoint (a.effects.image fe) fixed.effects) :
    (v.assignImages z a ft fe).AgreeOn v fixed :=
  ⟨fun i hi => assignImage_not_mem _ _ _ _ i (fun hm => Finset.disjoint_left.mp ht hm hi),
    fun i hi => assignImage_not_mem _ _ _ _ i (fun hm => Finset.disjoint_left.mp he hm hi)⟩

theorem Valuation.assignImages_pullback (v z : Valuation T.Value) (a : Names)
    (ft fe : Nat → Nat) (ht : Set.InjOn ft a.types) (he : Set.InjOn fe a.effects) :
    ((Substitution.freshen T a ft fe).pullback (v.assignImages z a ft fe)).AgreeOn z a := by
  constructor
  · intro i hi
    simp [Substitution.pullback, Substitution.freshen, hi, T.eval_var,
      Valuation.assignImages, assignImage_mem a.types ft ht z.types v.types i hi]
  · intro i hi
    simp [Substitution.pullback, Substitution.freshen, hi, Effect.eval, Effect.var,
      Valuation.assignImages, assignImage_mem a.effects fe he z.effects v.effects i hi]

/-- A single fresh instantiation covers every ground instance, while
preserving any finite set of names disjoint from the chosen fresh names. -/
theorem Scheme.freshen_covers {X : Constraints T O} {a : Names} {c : X.Formula}
    {t : T.Term} (ft fe : Nat → Nat) (hinjT : Set.InjOn ft a.types)
    (hinjE : Set.InjOn fe a.effects) (fixed : Names)
    (hfT : ∀ i, (Scheme.qualified a c t).FreeType i → i ∈ fixed.types)
    (hfE : ∀ i, (Scheme.qualified a c t).FreeEffect i → i ∈ fixed.effects)
    (hdT : Disjoint (a.types.image ft) fixed.types)
    (hdE : Disjoint (a.effects.image fe) fixed.effects)
    (v : Valuation T.Value) (u : T.Value)
    (hu : (Scheme.qualified a c t).GroundInstance v u) :
    ∃ w, w.AgreeOn v fixed ∧ X.holds (X.subst (Substitution.freshen T a ft fe) c) w ∧
      O.le (T.eval w ((Substitution.freshen T a ft fe).apply t)) u := by
  obtain ⟨z, hz, hc, ht⟩ := hu
  let w := v.assignImages z a ft fe
  have hfixed : w.AgreeOn v fixed := v.assignImages_agree z a ft fe fixed hdT hdE
  let s := Substitution.freshen T a ft fe
  have htypes (i : Nat) (hi : X.FreeType c i ∨ i ∈ (T.support t).types) :
      (s.pullback w).types i = z.types i := by
    by_cases ha : i ∈ a.types
    · simp [s, Substitution.pullback, Substitution.freshen, ha, T.eval_var, w, Valuation.assignImages,
        assignImage_mem a.types ft hinjT z.types v.types i ha]
    · simpa [s, Substitution.pullback, Substitution.freshen, ha, T.eval_var] using
        (hfixed.1 i (hfT i ⟨ha, hi⟩)).trans (hz.1 i ha).symm
  have heffects (i : Nat) (hi : X.FreeEffect c i ∨ i ∈ (T.support t).effects) :
      (s.pullback w).effects i = z.effects i := by
    by_cases ha : i ∈ a.effects
    · simp [s, Substitution.pullback, Substitution.freshen, ha, Effect.eval,
        Effect.var, w, Valuation.assignImages, assignImage_mem a.effects fe hinjE z.effects v.effects i ha]
    · simpa [s, Substitution.pullback, Substitution.freshen, ha, Effect.eval,
        Effect.var] using (hfixed.2 i (hfE i ⟨ha, hi⟩)).trans (hz.2 i ha).symm
  refine ⟨w, hfixed, (X.holds_subst _ _ w).mpr ?_, ?_⟩
  · exact (X.holds_semanticSupport c _ z (fun i hi => htypes i (.inl hi))
      (fun i hi => heffects i (.inl hi))).mpr hc
  · rw [s.eval_apply, T.eval_support (s.pullback w) z t
      ⟨fun i hi => htypes i (.inr hi), fun i hi => heffects i (.inr hi)⟩]
    exact ht

def Names.shiftTypes (fixed : Names) (i : Nat) : Nat := fixed.types.sup id + 1 + i
def Names.shiftEffects (fixed : Names) (i : Nat) : Nat := fixed.effects.sup id + 1 + i

theorem Names.shiftTypes_injective (fixed : Names) : Function.Injective fixed.shiftTypes := by
  intro i j h
  simpa [Names.shiftTypes] using h

theorem Names.shiftEffects_injective (fixed : Names) : Function.Injective fixed.shiftEffects := by
  intro i j h
  simpa [Names.shiftEffects] using h

theorem Names.shiftTypes_disjoint (fixed a : Names) :
    _root_.Disjoint (a.types.image fixed.shiftTypes) fixed.types := by
  apply Finset.disjoint_left.mpr
  intro i hi hf
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  have hle := Finset.le_sup (f := id) hf
  simp only [id_eq, Names.shiftTypes] at hle
  omega

theorem Names.shiftEffects_disjoint (fixed a : Names) :
    _root_.Disjoint (a.effects.image fixed.shiftEffects) fixed.effects := by
  apply Finset.disjoint_left.mpr
  intro i hi hf
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  have hle := Finset.le_sup (f := id) hf
  simp only [id_eq, Names.shiftEffects] at hle
  omega

theorem Renaming.freshPermutation (a fixed : Finset Nat) :
    ∃ (domain : Finset Nat) (p : Equiv.Perm Nat),
      (∀ i, i ∉ domain → p i = i) ∧ Disjoint (a.image p) fixed ∧
      (∀ i, i ∈ fixed → i ∉ a → p i = i) := by
  classical
  let shift := fun i : Nat => (a ∪ fixed).sup id + 1 + i
  have fresh (i j : Nat) (hj : j ∈ a ∪ fixed) : shift i ≠ j := by
    have := Finset.le_sup (f := id) hj
    dsimp [shift] at *
    omega
  let f : a ⊕ a → Nat := Sum.elim Subtype.val (fun i => shift i.val)
  have injective : Function.Injective f := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext h)
      | inr y => exact False.elim (fresh y x (Finset.mem_union_left _ x.property) h.symm)
    | inr x =>
      cases y with
      | inl y => exact False.elim (fresh x y (Finset.mem_union_left _ y.property) h)
      | inr y =>
        apply congrArg Sum.inr
        apply Subtype.ext
        dsimp [f, shift] at h
        omega
  let p := Equiv.Perm.extendDomain (Equiv.sumComm a a) (Equiv.ofInjective f injective)
  have moved (i : Nat) (hi : i ∈ a) : p i = shift i := by
    exact Equiv.Perm.extendDomain_apply_image (Equiv.sumComm a a)
      (Equiv.ofInjective f injective) (.inl ⟨i, hi⟩)
  have outside (i : Nat) (hi : i ∉ a ∪ a.image shift) : p i = i := by
    apply Equiv.Perm.extendDomain_apply_not_subtype
    rintro ⟨x, hx⟩
    apply hi
    cases x with
    | inl x => exact hx ▸ Finset.mem_union_left _ x.property
    | inr x => exact hx ▸ Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, x.property, rfl⟩)
  refine ⟨a ∪ a.image shift, p, outside, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    rintro j hj hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact fresh i (p i) (Finset.mem_union_right _ hf) (moved i hi).symm
  · intro i hi ha
    apply outside
    simp only [Finset.mem_union, Finset.mem_image, not_or]
    refine ⟨ha, ?_⟩
    rintro ⟨j, _, hj⟩
    exact fresh j i (Finset.mem_union_right _ hi) hj
/-- Rename all bound names away from any finite set, fixing the free names.
The renaming is a finite permutation, so this is the existing alpha relation. -/
theorem Scheme.fresh_alpha {X : Constraints T O} (a : Names) (c : X.Formula)
    (t : T.Term) (fixed : Names) :
    ∃ b d u, Scheme.AlphaEquivalent X (.qualified a c t) (.qualified b d u) ∧
      b.Disjoint fixed := by
  let avoid := fixed.union (Scheme.qualified a c t).support
  obtain ⟨dt, pt, ht, hdT, hfT⟩ := Renaming.freshPermutation a.types avoid.types
  obtain ⟨de, pe, he, hdE, hfE⟩ := Renaming.freshPermutation a.effects avoid.effects
  let p : Renaming := ⟨⟨dt, de⟩, pt, pe, ht, he⟩
  refine ⟨_, _, _, .rename p ?_ ?_, ?_⟩
  · intro i hi
    exact hfT i (Finset.mem_union_right _ (Scheme.freeType_mem_support hi)) hi.1
  · intro i hi
    exact hfE i (Finset.mem_union_right _ (Scheme.freeEffect_mem_support hi)) hi.1
  · exact ⟨hdT.mono_right Finset.subset_union_left, hdE.mono_right Finset.subset_union_left⟩

private def Scheme.MonoWitness {X : Constraints T O} (c : X.Formula)
    (target : T.Term) : Scheme X → Prop
  | .mono t => X.Entails c (X.le t target)
  | .qualified a d t => ∃ θ : Substitution T,
      θ.domain.Subset a ∧ X.Entails c (X.subst θ d) ∧
        X.Entails c (X.le (θ.apply t) target)

private def Substitution.reindex (θ : Substitution T) (a : Names)
    (ft fe : Nat → Nat) : Substitution T where
  domain := a
  types := fun i => if i ∈ a.types then θ.types (ft i) else T.var i
  effects := fun i => if i ∈ a.effects then θ.effects (fe i) else Effect.var i
  types_outside := by intro i hi; simp [hi]
  effects_outside := by intro i hi; simp [hi]

private theorem Scheme.monoWitness_rename {X : Constraints T O}
    (p : Renaming) {a : Names} {d c : X.Formula} {t target : T.Term}
    (ht : ∀ i, (Scheme.qualified (X := X) a d t).FreeType i → p.types i = i)
    (he : ∀ i, (Scheme.qualified (X := X) a d t).FreeEffect i → p.effects i = i) :
    (Scheme.qualified a d t).MonoWitness c target ↔
      (Scheme.qualified ⟨a.types.image p.types, a.effects.image p.effects⟩
        (X.subst (p.asSubstitution T) d) (T.rename p.types p.effects t)).MonoWitness c target := by
  let b : Names := ⟨a.types.image p.types, a.effects.image p.effects⟩
  have compare (v : Valuation T.Value) (θ η : Substitution T)
      (hT : ∀ i, X.FreeType d i ∨ i ∈ (T.support t).types →
        (θ.pullback v).types i = (η.pullback v).types (p.types i))
      (hE : ∀ i, X.FreeEffect d i ∨ i ∈ (T.support t).effects →
        (θ.pullback v).effects i = (η.pullback v).effects (p.effects i)) :
      (X.holds (X.subst θ d) v ↔
        X.holds (X.subst η (X.subst (p.asSubstitution T) d)) v) ∧
      T.eval v (θ.apply t) = T.eval v (η.apply (T.rename p.types p.effects t)) := by
    constructor
    · simp only [X.holds_subst]
      apply X.holds_semanticSupport
      · intro i hi
        simpa [Substitution.pullback, Renaming.asSubstitution, T.eval_var] using hT i (.inl hi)
      · intro i hi
        simpa [Substitution.pullback, Renaming.asSubstitution, Effect.eval, Effect.var] using hE i (.inl hi)
    · simp only [Substitution.eval_apply, T.eval_rename]
      exact T.eval_support _ _ t ⟨fun i hi => hT i (.inr hi), fun i hi => hE i (.inr hi)⟩
  constructor
  · rintro ⟨θ, hθ, hd, htype⟩
    let η := θ.reindex b p.types.symm p.effects.symm
    have agree (v : Valuation T.Value) := compare v θ η
    have eqs (v : Valuation T.Value) :
        (X.holds (X.subst θ d) v ↔
          X.holds (X.subst η (X.subst (p.asSubstitution T) d)) v) ∧
        T.eval v (θ.apply t) = T.eval v (η.apply (T.rename p.types p.effects t)) := by
      apply agree
      · intro i hi
        by_cases ha : i ∈ a.types
        · have hb : p.types i ∈ b.types := Finset.mem_image.mpr ⟨i, ha, rfl⟩
          simp [η, Substitution.reindex, Substitution.pullback, hb]
        · have hp := ht i ⟨ha, hi⟩
          have hb : p.types i ∉ b.types := by
            simpa [b] using ha
          have hb' : i ∉ b.types := hp ▸ hb
          simp [η, Substitution.reindex, Substitution.pullback, hb',
            θ.types_outside i (fun h => ha (hθ.1 h)), T.eval_var, hp]
      · intro i hi
        by_cases ha : i ∈ a.effects
        · have hb : p.effects i ∈ b.effects := Finset.mem_image.mpr ⟨i, ha, rfl⟩
          simp [η, Substitution.reindex, Substitution.pullback, hb]
        · have hp := he i ⟨ha, hi⟩
          have hb : p.effects i ∉ b.effects := by
            simpa [b] using ha
          have hb' : i ∉ b.effects := hp ▸ hb
          simp [η, Substitution.reindex, Substitution.pullback, hb',
            θ.effects_outside i (fun h => ha (hθ.2 h)), Effect.eval, Effect.var, hp]
    refine ⟨η, Names.Subset.refl b, fun v hv => (eqs v).1.mp (hd v hv), ?_⟩
    intro v hv
    exact (X.holds_le _ _ _).mpr ((eqs v).2 ▸ (X.holds_le _ _ _).mp (htype v hv))
  · rintro ⟨η, hη, hd, htype⟩
    let θ := η.reindex a p.types p.effects
    have eqs (v : Valuation T.Value) :
        (X.holds (X.subst θ d) v ↔
          X.holds (X.subst η (X.subst (p.asSubstitution T) d)) v) ∧
        T.eval v (θ.apply t) = T.eval v (η.apply (T.rename p.types p.effects t)) := by
      apply compare
      · intro i hi
        by_cases ha : i ∈ a.types
        · simp [θ, Substitution.reindex, Substitution.pullback, ha]
        · have hp := ht i ⟨ha, hi⟩
          have hb : p.types i ∉ b.types := by simpa [b] using ha
          have hb' : i ∉ b.types := hp ▸ hb
          simp [θ, Substitution.reindex, Substitution.pullback, ha,
            η.types_outside i (fun h => hb' (hη.1 h)), T.eval_var, hp]
      · intro i hi
        by_cases ha : i ∈ a.effects
        · simp [θ, Substitution.reindex, Substitution.pullback, ha]
        · have hp := he i ⟨ha, hi⟩
          have hb : p.effects i ∉ b.effects := by simpa [b] using ha
          have hb' : i ∉ b.effects := hp ▸ hb
          simp [θ, Substitution.reindex, Substitution.pullback, ha,
            η.effects_outside i (fun h => hb' (hη.2 h)), Effect.eval, Effect.var, hp]
    refine ⟨θ, Names.Subset.refl a, fun v hv => (eqs v).1.mpr (hd v hv), ?_⟩
    intro v hv
    exact (X.holds_le _ _ _).mpr ((eqs v).2.symm ▸ (X.holds_le _ _ _).mp (htype v hv))

private theorem Scheme.AlphaEquivalent.monoWitness_iff {X : Constraints T O}
    {s u : Scheme X} (h : Scheme.AlphaEquivalent X s u) (c : X.Formula) (t : T.Term) :
    s.MonoWitness c t ↔ u.MonoWitness c t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | rename p ht he => exact Scheme.monoWitness_rename p ht he

private theorem Scheme.AlphaEquivalent.mono_eq_iff {X : Constraints T O}
    {s u : Scheme X} (h : Scheme.AlphaEquivalent X s u) (t : T.Term) :
    s = .mono t ↔ u = .mono t := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | rename => simp

private theorem Instance.monoWitness {X : Constraints T O} {c : X.Formula}
    {s : Scheme X} {t : T.Term} (h : Instance X c s (.mono t)) :
    s.MonoWitness c t := by
  have go {c : X.Formula} {s u : Scheme X} (h : Instance X c s u) :
      ∀ t, u = .mono t → s.MonoWitness c t := by
    induction h with
    | sub he => intro t ht; cases ht; exact he
    | forallLeft θ ht he hd _ ih =>
        intro t h; cases h
        exact ⟨θ, ⟨ht, he⟩, hd, ih _ rfl⟩
    | forallRight => intro t h; cases h
    | @equivalent c d s u he _ ih =>
        intro t ht
        have hw := ih t ht
        cases s with
        | mono => exact X.entails_trans he.2 hw
        | qualified a q v =>
            obtain ⟨θ, hθ, hq, hv⟩ := hw
            exact ⟨θ, hθ, X.entails_trans he.2 hq, X.entails_trans he.2 hv⟩
    | alphaLeft he _ ih =>
        intro t ht
        exact (he.monoWitness_iff _ t).mpr (ih t ht)
    | alphaRight he _ ih =>
        intro t ht
        exact ih t ((he.mono_eq_iff t).mpr ht)
  exact go h t rfl

/-- A monotype instance has one finite witness on the original bound names;
alpha-converted intermediate qualifiers need not be admitted by the solved set. -/
theorem Instance.qualified_mono_iff {X : Constraints T O}
    {c d : X.Formula} {a : Names} {t u : T.Term} :
    Instance X c (.qualified a d t) (.mono u) ↔
      ∃ θ : Substitution T, θ.domain.Subset a ∧
        X.Entails c (X.subst θ d) ∧ X.Entails c (X.le (θ.apply t) u) := by
  refine ⟨fun h => h.monoWitness, ?_⟩
  rintro ⟨θ, hθ, hd, ht⟩
  exact .forallLeft θ hθ.1 hθ.2 hd (.sub ht)

/-- Eliminate a syntactic instance without assuming that arbitrary alpha-renamed
qualifiers are admissible. Validity is preserved for the same chosen solved set. -/
theorem Typing.instance_mono {sig : Signature T} {X : Constraints T O}
    {solved : X.Formula → Prop} {c g e s t eff}
    (typed : Typing sig X solved c g e s eff) (hi : Instance X c s (.mono t)) :
    Typing sig X solved c g e (.mono t) eff := by
  cases s with
  | mono u => exact typed.sub hi.monoWitness
  | qualified a d u =>
      obtain ⟨θ, hθ, hd, ht⟩ := Instance.qualified_mono_iff.mp hi
      exact (typed.forallElim θ hθ.1 hθ.2 hd).sub ht

private theorem Instance.post_sub {X : Constraints T O} {c : X.Formula}
    {s : Scheme X} {t u : T.Term} (h : Instance X c s (.mono t))
    (he : X.Entails c (X.le t u)) : Instance X c s (.mono u) := by
  cases s with
  | mono v =>
      exact .sub (fun w hw => (X.holds_le _ _ w).mpr
        (O.trans (h.groundInstance hw (O.refl _)) ((X.holds_le _ _ w).mp (he w hw))))
  | qualified a d v =>
      obtain ⟨θ, hθ, hd, ht⟩ := Instance.qualified_mono_iff.mp h
      exact Instance.qualified_mono_iff.mpr ⟨θ, hθ, hd, fun w hw =>
        (X.holds_le _ _ w).mpr (O.trans ((X.holds_le _ _ w).mp (ht w hw))
          ((X.holds_le _ _ w).mp (he w hw)))⟩

private theorem Instance.substitute_mono {X : Constraints T O} {c d : X.Formula}
    {s : Scheme X} {t : T.Term} (h : Instance X c s (.mono t))
    (θ : Substitution T) (hs : s.Avoids θ.domain) (hd : X.Entails d (X.subst θ c)) :
    Instance X d s (.mono (θ.apply t)) := by
  cases s with
  | mono u =>
      apply Instance.sub
      intro v hv
      have hc := (X.holds_subst _ _ v).mp (hd v hv)
      have hu := h.groundInstance hc (O.refl (T.eval (θ.pullback v) t))
      have fixed : T.eval (θ.pullback v) u = T.eval v u :=
        T.eval_support _ _ u
          ⟨fun i hi => (θ.pullback_outside v).1 i (fun hd => hs.1 i hd hi),
            fun i hi => (θ.pullback_outside v).2 i (fun hd => hs.2 i hd hi)⟩
      apply (X.holds_le _ _ v).mpr
      simpa only [Substitution.eval_apply, Scheme.GroundInstance, fixed] using hu
  | qualified a q u =>
      obtain ⟨ρ, hρ, hq, hu⟩ := Instance.qualified_mono_iff.mp h
      let η : Substitution T := {
        domain := a
        types := fun i => if i ∈ a.types then θ.apply (ρ.types i) else T.var i
        effects := fun i => if i ∈ a.effects then (ρ.effects i).subst θ.effects else Effect.var i
        types_outside := by intro i hi; simp [hi]
        effects_outside := by intro i hi; simp [hi] }
      have agreeT (v : Valuation T.Value) (i : Nat)
          (hi : X.FreeType q i ∨ i ∈ (T.support u).types) :
          (η.pullback v).types i = (ρ.pullback (θ.pullback v)).types i := by
        by_cases ha : i ∈ a.types
        · simp [η, Substitution.pullback, ha, Substitution.eval_apply]
        · have hθ : i ∉ θ.domain.types := fun hd => hs.1 i hd ⟨ha, hi⟩
          simp [η, Substitution.pullback, ha, ρ.types_outside i (fun h => ha (hρ.1 h)),
            θ.types_outside i hθ, T.eval_var]
      have agreeE (v : Valuation T.Value) (i : Nat)
          (hi : X.FreeEffect q i ∨ i ∈ (T.support u).effects) :
          (η.pullback v).effects i = (ρ.pullback (θ.pullback v)).effects i := by
        by_cases ha : i ∈ a.effects
        · simp [η, Substitution.pullback, ha, Effect.eval_subst]
        · have hθ : i ∉ θ.domain.effects := fun hd => hs.2 i hd ⟨ha, hi⟩
          simp [η, Substitution.pullback, ha, ρ.effects_outside i (fun h => ha (hρ.2 h)),
            θ.effects_outside i hθ, Effect.eval, Effect.var]
      apply Instance.qualified_mono_iff.mpr
      refine ⟨η, Names.Subset.refl a, ?_, ?_⟩
      · intro v hv
        apply (X.holds_subst _ _ v).mpr
        apply (X.holds_semanticSupport q _ _
          (fun i hi => agreeT v i (.inl hi)) (fun i hi => agreeE v i (.inl hi))).mpr
        exact (X.holds_subst _ _ _).mp (hq _ ((X.holds_subst _ _ v).mp (hd v hv)))
      · intro v hv
        apply (X.holds_le _ _ v).mpr
        rw [Substitution.eval_apply, Substitution.eval_apply,
          T.eval_support _ _ u ⟨fun i hi => agreeT v i (.inr hi), fun i hi => agreeE v i (.inr hi)⟩]
        simpa only [Substitution.eval_apply] using
          (X.holds_le _ _ _).mp (hu _ ((X.holds_subst _ _ v).mp (hd v hv)))

private theorem Instance.trans_mono_under {X : Constraints T O} {c d : X.Formula}
    {s u : Scheme X} {t : T.Term} (h : Instance X c s u)
    (hd : X.Entails d c) (k : Instance X d u (.mono t)) : Instance X d s (.mono t) := by
  induction h generalizing d t with
  | sub he =>
      exact (Instance.sub (X.entails_trans hd he)).post_sub
        (fun v hv => (X.holds_le _ _ v).mpr (k.groundInstance hv (O.refl _)))
  | forallLeft θ ht he hq _ ih =>
      exact .forallLeft θ ht he (X.entails_trans hd hq) (ih hd k)
  | @forallRight c a q v s freshC freshS premise ih =>
      obtain ⟨θ, hθ, hq, ht⟩ := Instance.qualified_mono_iff.mp k
      have fresh : s.Avoids θ.domain :=
        ⟨fun i hi => freshS.1 i (hθ.1 hi), fun i hi => freshS.2 i (hθ.2 hi)⟩
      have entails : X.Entails d (X.subst θ (X.and c q)) := by
        intro v hv
        apply (X.holds_subst _ _ v).mpr
        apply (X.holds_and _ _ _).mpr
        have outside : (θ.pullback v).AgreeOutside v a :=
          ⟨fun i hi => (θ.pullback_outside v).1 i (fun h => hi (hθ.1 h)),
            fun i hi => (θ.pullback_outside v).2 i (fun h => hi (hθ.2 h))⟩
        exact ⟨(X.holds_agreeOutside freshC outside).mpr ((X.holds_and _ _ v).mp (hd v hv)).1,
          (X.holds_subst _ _ v).mp (hq v hv)⟩
      exact (premise.substitute_mono θ fresh entails).post_sub ht
  | equivalent he _ ih => exact ih (X.entails_trans hd he.2) k
  | alphaLeft he _ ih => exact .alphaLeft he (ih hd k)
  | alphaRight he _ ih => exact ih hd (.alphaLeft he k)

private theorem Instance.of_mono_targets {X : Constraints T O} {c : X.Formula}
    {s u : Scheme X}
    (inhabited : ∀ v, X.holds c v → ∃ t, u.GroundInstance v t)
    (cover : ∀ d t, X.Entails d c → Instance X d u (.mono t) → Instance X d s (.mono t)) :
    Instance X c s u := by
  cases u with
  | mono t => exact cover c t (X.entails_refl _) (.sub (fun v _ => (X.holds_le _ _ v).mpr (O.refl _)))
  | qualified a q t =>
      obtain ⟨b, r, v, alpha, fresh⟩ := Scheme.fresh_alpha a q t ((X.support c).union s.support)
      have hc : X.Avoids c b :=
        ⟨fun i hi hf => Finset.disjoint_left.mp fresh.1 hi (Finset.mem_union_left _ (X.freeType_mem_support hf)),
          fun i hi hf => Finset.disjoint_left.mp fresh.2 hi (Finset.mem_union_left _ (X.freeEffect_mem_support hf))⟩
      have hs : s.Avoids b :=
        ⟨fun i hi hf => Finset.disjoint_left.mp fresh.1 hi (Finset.mem_union_right _ (Scheme.freeType_mem_support hf)),
          fun i hi hf => Finset.disjoint_left.mp fresh.2 hi (Finset.mem_union_right _ (Scheme.freeEffect_mem_support hf))⟩
      have projected : X.Entails c (X.existsNames b r) := by
        intro w hw
        obtain ⟨t', ht'⟩ := inhabited w hw
        obtain ⟨z, hz, hr, _⟩ := (alpha.groundInstance_iff w t').mp ht'
        exact (X.holds_exists _ _ w).mpr ⟨z, hz, hr⟩
      have instantiate : Instance X (X.and c r) (.qualified a q t) (.mono v) := by
        apply Instance.alphaLeft alpha
        apply Instance.forallLeft (Substitution.identity T)
          (by simp [Substitution.identity, Names.empty])
          (by simp [Substitution.identity, Names.empty])
        · intro w hw
          simpa only [X.holds_subst, Substitution.identity_pullback] using (X.holds_and _ _ w).mp hw |>.2
        · apply Instance.sub
          intro w _
          apply (X.holds_le _ _ w).mpr
          simpa only [Substitution.eval_apply, Substitution.identity_pullback] using O.refl (T.eval w v)
      apply Instance.alphaRight (.symm alpha)
      apply Instance.equivalent
        ⟨X.entails_left _ _, fun w hw => (X.holds_and _ _ w).mpr ⟨hw, projected w hw⟩⟩
      exact .forallRight hc hs (cover _ _ (X.entails_left _ _) instantiate)

/-- The primitive instance rules are closed under strengthening, including
polymorphic targets whose bound names clash with the stronger constraint. -/
theorem Instance.weaken {X : Constraints T O} {c d : X.Formula} {s t : Scheme X}
    (h : Instance X c s t) (hd : X.Entails d c) : Instance X d s t := by
  apply Instance.of_mono_targets (fun v hv => h.target_nonempty (hd v hv))
  intro q u hq hu
  exact h.trans_mono_under (X.entails_trans hq hd) hu

/-- Transitivity is derived from the primitive rules, not added as a constructor. -/
theorem Instance.trans {X : Constraints T O} {c : X.Formula} {s t u : Scheme X}
    (h : Instance X c s t) (k : Instance X c t u) : Instance X c s u := by
  apply Instance.of_mono_targets (fun _ hv => k.target_nonempty hv)
  intro d v hd hv
  exact h.trans_mono_under hd (k.trans_mono_under hd hv)

/-- Exact side condition missing from the unconditional Ref-σ rule. -/
theorem Scheme.qualified_self_instance_iff
    {X : Constraints T O} {c d : X.Formula} {a : Names} {t : T.Term} :
    Instance X c (.qualified a d t) (.qualified a d t) ↔
      X.Entails c (X.existsNames a d) := by
  constructor
  · intro h v hv
    obtain ⟨u, w, hw, hd, _⟩ := h.target_nonempty hv
    exact (X.holds_exists _ _ _).mpr ⟨w, hw, hd⟩
  · intro h
    apply Instance.of_mono_targets
    · intro v hv
      obtain ⟨w, hw, hd⟩ := (X.holds_exists _ _ _).mp (h v hv)
      exact ⟨T.eval w t, w, hw, hd, O.refl _⟩
    · intro _ _ _ hi; exact hi

/-- Realizability is a sufficient condition for constraint-relative reflexivity. -/
theorem Scheme.Realizable.self_instance {X : Constraints T O} {c : X.Formula} {s : Scheme X}
    (h : s.Realizable c) : Instance X c s s :=
  Instance.of_mono_targets (fun _ hv => h.groundInstance hv) (fun _ _ _ hi => hi)

/-- A representable scheme approximates itself at its realizability constraint. -/
theorem Scheme.Approximates.refl {X : Constraints T O} {solved : X.Formula → Prop}
    {c : X.Formula} {s : Scheme X} (hs : s.Admissible solved) (hr : s.Realizable c) :
    s.Approximates solved c s := ⟨hs, hr.self_instance, fun _ _ h => h⟩

/-- The replacement environment retains every uniform monotype instance.
This lemma is independent of the choice of solved constraints. -/
theorem Scheme.Approximates.realizable {X : Constraints T O} {solved : X.Formula → Prop}
    {c : X.Formula} {s t : Scheme X} (h : s.Approximates solved c t)
    (hr : s.Realizable c) : t.Realizable c := by
  obtain ⟨u, hu⟩ := hr
  exact ⟨u, h.2.2 (.mono u) trivial hu⟩

theorem Context.Realizable.approximate {X : Constraints T O} {solved : X.Formula → Prop}
    {c : X.Formula} {g g' : Context X} (hr : g.Realizable c)
    (h : List.Forall₂ (Scheme.Approximates solved c) g g') : g'.Realizable c := by
  induction h with
  | nil => intro s hs; cases hs
  | @cons s t g g' h hs ih =>
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact h.realizable (hr s (by simp))
      · exact ih (fun s hs => hr s (List.mem_cons_of_mem _ hs)) u hu

theorem Scheme.Realizable.weaken {X : Constraints T O} {c d : X.Formula}
    {s : Scheme X} (h : s.Realizable c) (hd : X.Entails d c) : s.Realizable d := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, ht.weaken hd⟩

theorem Context.Realizable.weaken {X : Constraints T O} {c d : X.Formula}
    {g : Context X} (h : g.Realizable c) (hd : X.Entails d c) : g.Realizable d :=
  fun s hs => (h s hs).weaken hd

/-- The variable case of the solved-form transformation, including every
monotype use of a polymorphic assumption in the replacement environment. -/
theorem Typing.variable_approximate {sig : Signature T} {X : Constraints T O}
    {solved : X.Formula → Prop} {c : X.Formula} {g g' : Context X}
    {i : Nat} {s : Scheme X} {t : T.Term}
    (hc : X.Admissible solved c)
    (hg : List.Forall₂ (Scheme.Approximates solved c) g g')
    (found : g[i]? = some s) (hi : Instance X c s (.mono t)) :
    Typing sig X solved c g' (.var i) (.mono t) ∅ := by
  have admissible : g'.Admissible solved := by
    clear found
    induction hg with
    | nil => intro s hs; cases hs
    | cons h hs ih => exact Context.admissible_cons ih h.1
  have entry : ∃ s', g'[i]? = some s' ∧ s.Approximates solved c s' := by
    clear admissible
    induction hg generalizing i with
    | nil => simp at found
    | @cons u v g g' h hs ih =>
        cases i with
        | zero =>
            have : u = s := by simpa using found
            subst s
            exact ⟨v, rfl, h⟩
        | succ i => exact ih (by simpa using found)
  obtain ⟨s', found', hs'⟩ := entry
  have typed : Typing sig X solved c g' (.var i) s' ∅ :=
    ⟨.var found', hc, admissible, hs'.1, trivial⟩
  exact typed.instance_mono (hs'.2.2 (.mono t) trivial hi)

/-- Complete variable inference uses one substitution for all solutions,
not a substitution chosen after the target ground type is known. -/
def Constraints.instantiateConstraint (X : Constraints T O) (c : X.Formula)
    (s : Scheme X) (expected : T.Term) (eff : Effect) (fixed : Names) : X.Formula :=
  match s with
  | .mono t => X.checked c X.top t expected ∅ eff
  | .qualified a d t =>
      let sub := Substitution.freshen T a fixed.shiftTypes fixed.shiftEffects
      X.checked c (X.subst sub d) (sub.apply t) expected ∅ eff

theorem Inference.variable_complete {sig : Signature T} {X : Constraints T O}
    {N : X.Simplifier} {c : X.Formula} {g : Context X} {i : Nat} {s : Scheme X}
    (found : g[i]? = some s) (expected : T.Term) (eff : Effect) (fixed : Names)
    (hct : (X.support c).types ⊆ fixed.types)
    (hce : (X.support c).effects ⊆ fixed.effects)
    (htt : (T.support expected).types ⊆ fixed.types)
    (hte : (T.support expected).effects ⊆ fixed.effects)
    (hee : eff.vars ⊆ fixed.effects)
    (hst : ∀ j, s.FreeType j → j ∈ fixed.types)
    (hse : ∀ j, s.FreeEffect j → j ∈ fixed.effects) :
    ∃ d, d = X.instantiateConstraint c s expected eff fixed ∧ Inference sig X N c g (.var i) expected eff d ∧
      ∀ v, X.holds c v → s.GroundInstance v (T.eval v expected) → eff.eval v.effects = ∅ →
      ∃ w, w.AgreeOn v fixed ∧ X.holds d w := by
  have checked (actual : T.Term) (d : X.Formula) (v w : Valuation T.Value)
      (hw : w.AgreeOn v fixed) (hc : X.holds c v) (hd : X.holds d w)
      (ht : O.le (T.eval w actual) (T.eval v expected)) (he : eff.eval v.effects = ∅) :
      X.holds (X.checked c d actual expected ∅ eff) w := by
    have hcw := (X.holds_support c w v ⟨fun i hi => hw.1 i (hct hi),
      fun i hi => hw.2 i (hce hi)⟩).mpr hc
    have htw := T.eval_support w v expected
      ⟨fun i hi => hw.1 i (htt hi), fun i hi => hw.2 i (hte hi)⟩
    have hew : eff.eval w.effects = eff.eval v.effects := by
      unfold Effect.eval
      congr 1
      exact Finset.biUnion_congr rfl (fun i hi => hw.2 i (hee hi))
    apply (X.holds_conjunction _ w).mpr
    simp only [List.mem_cons, forall_eq_or_imp]
    refine ⟨hcw, hd, (X.holds_le _ _ w).mpr ?_, (X.holds_effectEq _ _ w).mpr ?_, by simp⟩
    · simpa only [htw] using ht
    · rw [hew, he]; rfl
  cases s with
  | mono t =>
      refine ⟨_, rfl, .varMono found, ?_⟩
      intro v hc ht he
      exact ⟨v, ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
        checked t X.top v v ⟨fun _ _ => rfl, fun _ _ => rfl⟩ hc
          ((X.holds_top v).mpr trivial) ht he⟩
  | qualified a d t =>
      let sub := Substitution.freshen T a fixed.shiftTypes fixed.shiftEffects
      refine ⟨_, rfl, .varPoly sub found (fun _ h => h) (fun _ h => h), ?_⟩
      intro v hc ht he
      obtain ⟨w, hw, hd, htype⟩ := Scheme.freshen_covers fixed.shiftTypes fixed.shiftEffects
        fixed.shiftTypes_injective.injOn fixed.shiftEffects_injective.injOn fixed hst hse
        (fixed.shiftTypes_disjoint a) (fixed.shiftEffects_disjoint a) v (T.eval v expected) ht
      exact ⟨w, hw, checked (sub.apply t) (X.subst sub d) v w hw hc hd htype he⟩

end EHMX.HMX
