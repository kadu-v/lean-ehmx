import EHMX.Syntax

namespace EHMX.HMX

/-- The two sorts of names used by the effect extension. -/
structure Names where
  types : Finset Nat
  effects : Finset Nat
  deriving DecidableEq

def Names.empty : Names := ⟨∅, ∅⟩
def Names.union (a b : Names) : Names :=
  ⟨a.types ∪ b.types, a.effects ∪ b.effects⟩
def Names.diff (a b : Names) : Names :=
  ⟨a.types \ b.types, a.effects \ b.effects⟩
def Names.Disjoint (a b : Names) : Prop :=
  _root_.Disjoint a.types b.types ∧ _root_.Disjoint a.effects b.effects

structure Valuation (Value : Type) where
  types : Nat → Value
  effects : Nat → Finset Op

def Valuation.AgreeOn {V : Type} (v w : Valuation V) (a : Names) : Prop :=
  (∀ i ∈ a.types, v.types i = w.types i) ∧
  (∀ i ∈ a.effects, v.effects i = w.effects i)

def Valuation.AgreeOutside {V : Type} (v w : Valuation V) (a : Names) : Prop :=
  (∀ i, i ∉ a.types → v.types i = w.types i) ∧
  (∀ i, i ∉ a.effects → v.effects i = w.effects i)

def Valuation.patch {V : Type} (outer witness : Valuation V) (a : Names) : Valuation V :=
  ⟨fun i => if i ∈ a.types then witness.types i else outer.types i,
    fun i => if i ∈ a.effects then witness.effects i else outer.effects i⟩

theorem Valuation.patch_agreeOutside {V : Type} (v w : Valuation V) (a : Names) :
    (v.patch w a).AgreeOutside v a :=
  ⟨fun i hi => by simp [Valuation.patch, hi], fun i hi => by simp [Valuation.patch, hi]⟩

def Names.Subset (a b : Names) : Prop := a.types ⊆ b.types ∧ a.effects ⊆ b.effects

theorem Names.Subset.refl (a : Names) : a.Subset a := ⟨fun _ h => h, fun _ h => h⟩

theorem Names.Subset.trans {a b c : Names} (h : a.Subset b) (k : b.Subset c) :
    a.Subset c := ⟨h.1.trans k.1, h.2.trans k.2⟩

theorem Names.Subset.union {a b c : Names} (h : a.Subset c) (k : b.Subset c) :
    (a.union b).Subset c := ⟨Finset.union_subset h.1 k.1, Finset.union_subset h.2 k.2⟩

theorem Names.Disjoint.mono_right {a b c : Names} (h : a.Disjoint c) (k : b.Subset c) :
    a.Disjoint b :=
  ⟨Finset.disjoint_left.mpr (fun _ hi hj => Finset.disjoint_left.mp h.1 hi (k.1 hj)),
    Finset.disjoint_left.mpr (fun _ hi hj => Finset.disjoint_left.mp h.2 hi (k.2 hj))⟩

theorem Names.subset_union_left (a b : Names) : a.Subset (a.union b) :=
  ⟨Finset.subset_union_left, Finset.subset_union_left⟩

theorem Names.subset_union_right (a b : Names) : b.Subset (a.union b) :=
  ⟨Finset.subset_union_right, Finset.subset_union_right⟩

theorem Valuation.AgreeOn.mono {V : Type} {v w : Valuation V} {a b : Names}
    (h : v.AgreeOn w b) (hab : a.Subset b) : v.AgreeOn w a :=
  ⟨fun i hi => h.1 i (hab.1 hi), fun i hi => h.2 i (hab.2 hi)⟩

theorem Valuation.AgreeOn.trans {V : Type} {v w z : Valuation V} {a : Names}
    (h : v.AgreeOn w a) (k : w.AgreeOn z a) : v.AgreeOn z a :=
  ⟨fun i hi => (h.1 i hi).trans (k.1 i hi),
    fun i hi => (h.2 i hi).trans (k.2 i hi)⟩

/-- The type algebra is a parameter. In particular no elimination principle
for `Term`, injectivity of arrows, or exhaustiveness of the three constructors
below is assumed. Additional constructors and equational theories are allowed.
The fields after `eval` are the usual laws of substitution and finite support. -/
structure TypeDomain where
  Term : Type
  Value : Type
  value_nonempty : Nonempty Value
  var : Nat → Term
  literal : BaseTy → Term
  arrow : Term → Effect → Term → Term
  groundLiteral : BaseTy → Value
  groundArrow : Value → Finset Op → Value → Value
  rename : (Nat → Nat) → (Nat → Nat) → Term → Term
  subst : (Nat → Term) → (Nat → Effect) → Term → Term
  subst_var : ∀ f g i, subst f g (var i) = f i
  support : Term → Names
  support_var : ∀ i, support (var i) = ⟨{i}, ∅⟩
  subst_eq_self : ∀ f g t,
    (∀ i ∈ (support t).types, f i = var i) →
    (∀ i ∈ (support t).effects, g i = Effect.var i) → subst f g t = t
  support_subst_avoids : ∀ (f : Nat → Term) (g : Nat → Effect) t (a : Names),
    (∀ i ∈ (support t).types, a.Disjoint (support (f i))) →
    (∀ i ∈ (support t).effects, Disjoint a.effects (g i).vars) →
    a.Disjoint (support (subst f g t))
  eval : Valuation Value → Term → Value
  eval_var : ∀ v i, eval v (var i) = v.types i
  eval_literal : ∀ v b, eval v (literal b) = groundLiteral b
  eval_arrow : ∀ v a e b, eval v (arrow a e b) =
    groundArrow (eval v a) (e.eval v.effects) (eval v b)
  eval_rename : ∀ v f g t, eval v (rename f g t) =
    eval ⟨v.types ∘ f, v.effects ∘ g⟩ t
  eval_subst : ∀ v f g t, eval v (subst f g t) =
    eval ⟨fun i => eval v (f i), fun i => (g i).eval v.effects⟩ t
  eval_support : ∀ v w t, v.AgreeOn w (support t) → eval v t = eval w t

/-- A substitution changes only finitely many names. Unlike a valuation, it
is not an arbitrary assignment of ground types to infinitely many names. -/
structure Substitution (T : TypeDomain) where
  domain : Names
  types : Nat → T.Term
  effects : Nat → Effect
  types_outside : ∀ i, i ∉ domain.types → types i = T.var i
  effects_outside : ∀ i, i ∉ domain.effects → effects i = Effect.var i

def Substitution.identity (T : TypeDomain) : Substitution T where
  domain := Names.empty
  types := T.var
  effects := Effect.var
  types_outside := by intros; rfl
  effects_outside := by intros; rfl

def Substitution.apply {T : TypeDomain} (s : Substitution T) (t : T.Term) : T.Term :=
  T.subst s.types s.effects t

def Substitution.pullback {T : TypeDomain} (s : Substitution T)
    (v : Valuation T.Value) : Valuation T.Value :=
  ⟨fun i => T.eval v (s.types i), fun i => (s.effects i).eval v.effects⟩

theorem Substitution.identity_pullback {T : TypeDomain} (v : Valuation T.Value) :
    (Substitution.identity T).pullback v = v := by
  cases v
  simp [Substitution.identity, Substitution.pullback, T.eval_var, Effect.eval, Effect.var]

/-- Apply `s` first and then `r`. Comparison factors are finite substitutions,
but need not be solved: solved substitutions are not closed under composition. -/
def Substitution.compose {T : TypeDomain} (r s : Substitution T) : Substitution T where
  domain := r.domain.union s.domain
  types := fun i => r.apply (s.types i)
  effects := fun i => (s.effects i).subst r.effects
  types_outside := by
    intro i hi
    have h := Finset.notMem_union.mp hi
    simp [Substitution.apply, s.types_outside i h.2, T.subst_var, r.types_outside i h.1]
  effects_outside := by
    intro i hi
    have h := Finset.notMem_union.mp hi
    simp [s.effects_outside i h.2, Effect.subst, Effect.var, r.effects_outside i h.1]

theorem Substitution.compose_pullback {T : TypeDomain} (r s : Substitution T)
    (v : Valuation T.Value) :
    (r.compose s).pullback v = s.pullback (r.pullback v) := by
  apply congrArg₂ Valuation.mk
  · funext i
    exact T.eval_subst v r.types r.effects (s.types i)
  · funext i
    exact Effect.eval_subst (s.effects i) r.effects v.effects

/-- Idempotence on represented terms. For set-normalized effects this alone
does not imply the domain/codomain separation used in dissertation Lemma 4. -/
def Substitution.Idempotent {T : TypeDomain} (s : Substitution T) : Prop :=
  (∀ i, s.apply (s.types i) = s.types i) ∧
  (∀ i, (s.effects i).subst s.effects = s.effects i)

/-- The solved-substitution convention of Definition 6 and Lemma 4: images of
assigned variables contain no assigned variables. Raw finite maps remain useful
for renaming and instantiation; normalization uses this stronger contract. -/
structure Substitution.Solved {T : TypeDomain} (s : Substitution T) : Prop where
  type_range : ∀ i ∈ s.domain.types, s.domain.Disjoint (T.support (s.types i))
  effect_range : ∀ i ∈ s.domain.effects, Disjoint s.domain.effects (s.effects i).vars

/-- Instantiate the two output slots of constraint generation. The type and
effect indices belong to different sorts and may have the same numeral. -/
def Substitution.outputs {T : TypeDomain} (a b : Nat) (t : T.Term)
    (eff : Effect) : Substitution T where
  domain := ⟨{a}, {b}⟩
  types := fun i => if i = a then t else T.var i
  effects := fun i => if i = b then eff else Effect.var i
  types_outside := by intro i hi; simp only [Finset.mem_singleton] at hi; simp [hi]
  effects_outside := by intro i hi; simp only [Finset.mem_singleton] at hi; simp [hi]

theorem Substitution.outputs_solved {T : TypeDomain} (a b : Nat) (t : T.Term)
    (eff : Effect) (ht : (Names.mk {a} {b}).Disjoint (T.support t))
    (he : b ∉ eff.vars) : (Substitution.outputs a b t eff).Solved := by
  constructor
  · intro i hi
    have : i = a := Finset.mem_singleton.mp hi
    simpa [outputs, this] using ht
  · intro i hi
    have : i = b := Finset.mem_singleton.mp hi
    simpa [outputs, this] using he

theorem Substitution.Solved.idempotent {T : TypeDomain} {s : Substitution T}
    (hs : s.Solved) : s.Idempotent := by
  constructor
  · intro i
    by_cases hi : i ∈ s.domain.types
    · exact T.subst_eq_self _ _ _
        (fun j hj => s.types_outside j
          (fun hd => Finset.disjoint_left.mp (hs.type_range i hi).1 hd hj))
        (fun j hj => s.effects_outside j
          (fun hd => Finset.disjoint_left.mp (hs.type_range i hi).2 hd hj))
    · simp [Substitution.apply, s.types_outside i hi, T.subst_var]
  · intro i
    by_cases hi : i ∈ s.domain.effects
    · exact Effect.subst_eq_self _ _ (fun j hj => s.effects_outside j
        (fun hd => Finset.disjoint_left.mp (hs.effect_range i hi) hd hj))
    · simp [s.effects_outside i hi, Effect.subst, Effect.var]

theorem Substitution.idempotent_pullback {T : TypeDomain} {s : Substitution T}
    (hs : s.Idempotent) (v : Valuation T.Value) :
    s.pullback (s.pullback v) = s.pullback v := by
  apply congrArg₂ Valuation.mk
  · funext i
    exact (T.eval_subst v s.types s.effects (s.types i)).symm.trans
      (congrArg (T.eval v) (hs.1 i))
  · funext i
    exact (Effect.eval_subst (s.effects i) s.effects v.effects).symm.trans
      (congrArg (Effect.eval v.effects) (hs.2 i))

theorem Substitution.identity_solved (T : TypeDomain) :
    (Substitution.identity T).Solved :=
  ⟨by simp [Substitution.identity, Names.empty],
    by simp [Substitution.identity, Names.empty]⟩

/-- A solved substitution erases dependence on its assigned variables. -/
theorem Substitution.Solved.pullback_agreeOutside {T : TypeDomain} {s : Substitution T}
    (hs : s.Solved) {v w : Valuation T.Value} (h : v.AgreeOutside w s.domain) :
    s.pullback v = s.pullback w := by
  apply congrArg₂ Valuation.mk
  · funext i
    by_cases hi : i ∈ s.domain.types
    · apply T.eval_support
      exact ⟨fun j hj => h.1 j (fun hd => Finset.disjoint_left.mp (hs.type_range i hi).1 hd hj),
        fun j hj => h.2 j (fun hd => Finset.disjoint_left.mp (hs.type_range i hi).2 hd hj)⟩
    · simp only [s.types_outside i hi, T.eval_var]
      exact h.1 i hi
  · funext i
    by_cases hi : i ∈ s.domain.effects
    · exact Effect.eval_support _ _ _
        (fun j hj => h.2 j (fun hd => Finset.disjoint_left.mp (hs.effect_range i hi) hd hj))
    · simpa [s.effects_outside i hi, Effect.eval, Effect.var] using h.2 i hi

theorem Substitution.eval_apply {T : TypeDomain} (s : Substitution T)
    (v : Valuation T.Value) (t : T.Term) :
    T.eval v (s.apply t) = T.eval (s.pullback v) t :=
  T.eval_subst v s.types s.effects t

theorem Substitution.pullback_outside {T : TypeDomain} (s : Substitution T)
    (v : Valuation T.Value) : (s.pullback v).AgreeOutside v s.domain := by
  constructor
  · intro i hi
    simp [pullback, s.types_outside i hi, T.eval_var]
  · intro i hi
    simp [pullback, s.effects_outside i hi, Effect.eval, Effect.var]

/-- Reverse the assignment `i ↦ j`, substituting `i` for `j` in every other
image. This removes `i` from the domain without introducing fresh variables. -/
def Substitution.pivot {T : TypeDomain} (s : Substitution T) (i j : Nat)
    (hi : s.types i = T.var j) : Substitution T where
  domain := ⟨insert j (s.domain.types.erase i), s.domain.effects⟩
  types := fun k => T.subst (Function.update T.var j (T.var i)) Effect.var (s.types k)
  effects := s.effects
  types_outside := by
    intro k hk
    have hk' : k ≠ j ∧ (k ≠ i → k ∉ s.domain.types) := by simpa using hk
    by_cases hki : k = i
    · subst k; simp [hi, T.subst_var]
    · simp [s.types_outside k (hk'.2 hki), T.subst_var, hk'.1]
  effects_outside := s.effects_outside

theorem Substitution.pivot_pullback {T : TypeDomain} (s : Substitution T) (i j : Nat)
    (hi : s.types i = T.var j) (v : Valuation T.Value) :
    (s.pivot i j hi).pullback v =
      s.pullback ⟨Function.update v.types j (v.types i), v.effects⟩ := by
  apply congrArg₂ Valuation.mk
  · funext k
    change T.eval v (T.subst _ _ _) = _
    rw [T.eval_subst]
    congr 1
    apply congrArg₂ Valuation.mk
    · funext l
      by_cases h : l = j <;> simp [h, T.eval_var]
    · funext l
      simp [Effect.eval, Effect.var]
  · rfl

theorem Substitution.Solved.pivot {T : TypeDomain} {s : Substitution T}
    (hs : s.Solved) {i j : Nat} (hi : i ∈ s.domain.types)
    (heq : s.types i = T.var j) : (s.pivot i j heq).Solved := by
  have hj : j ∉ s.domain.types := by
    have h := (hs.type_range i hi).1
    simpa [heq, T.support_var] using h
  have hji : j ≠ i := fun h => hj (h ▸ hi)
  constructor
  · intro k hk
    have old : s.domain.Disjoint (T.support (s.types k)) := by
      rcases Finset.mem_insert.mp hk with hk | hk
      · rw [hk, s.types_outside j hj]
        simp [T.support_var, Names.Disjoint, hj]
      · exact hs.type_range k (Finset.mem_erase.mp hk).2
    apply T.support_subst_avoids
    · intro l hl
      have hld : l ∉ s.domain.types := fun h => Finset.disjoint_left.mp old.1 h hl
      by_cases h : l = j
      · simp [h, Names.Disjoint, Substitution.pivot, T.support_var, hji.symm]
      · simp [h, Names.Disjoint, Substitution.pivot, T.support_var, hld]
    · intro l hl
      have hld : l ∉ s.domain.effects := fun h => Finset.disjoint_left.mp old.2 h hl
      simpa [Substitution.pivot, Effect.var] using hld
  · exact hs.effect_range

/-- Reverse an effect-variable alias, including its occurrences inside types. -/
def Substitution.pivotEffect {T : TypeDomain} (s : Substitution T) (i j : Nat)
    (hi : s.effects i = Effect.var j) : Substitution T where
  domain := ⟨s.domain.types, insert j (s.domain.effects.erase i)⟩
  types := fun k => T.subst T.var (Function.update Effect.var j (Effect.var i)) (s.types k)
  effects := fun k => (s.effects k).subst (Function.update Effect.var j (Effect.var i))
  types_outside := by intro k hk; simp [s.types_outside k hk, T.subst_var]
  effects_outside := by
    intro k hk
    have hk' : k ≠ j ∧ (k ≠ i → k ∉ s.domain.effects) := by simpa using hk
    by_cases hki : k = i
    · subst k; simp [hi, Effect.subst, Effect.var]
    · simp [s.effects_outside k (hk'.2 hki), Effect.subst, Effect.var, hk'.1]

theorem Substitution.pivotEffect_pullback {T : TypeDomain} (s : Substitution T) (i j : Nat)
    (hi : s.effects i = Effect.var j) (v : Valuation T.Value) :
    (s.pivotEffect i j hi).pullback v =
      s.pullback ⟨v.types, Function.update v.effects j (v.effects i)⟩ := by
  have effects : (fun k => (Function.update Effect.var j (Effect.var i) k).eval v.effects) =
      Function.update v.effects j (v.effects i) := by
    funext k; by_cases h : k = j <;> simp [h, Effect.eval, Effect.var]
  apply congrArg₂ Valuation.mk
  · funext k
    change T.eval v (T.subst _ _ _) = _
    rw [T.eval_subst]
    simp only [T.eval_var, effects]
  · funext k
    change Effect.eval _ (Effect.subst _ _) = _
    rw [Effect.eval_subst, effects]

theorem Substitution.Solved.pivotEffect {T : TypeDomain} {s : Substitution T}
    (hs : s.Solved) {i j : Nat} (hi : i ∈ s.domain.effects)
    (heq : s.effects i = Effect.var j) : (s.pivotEffect i j heq).Solved := by
  have hj : j ∉ s.domain.effects := by
    simpa [heq, Effect.var] using hs.effect_range i hi
  have hji : j ≠ i := fun h => hj (h ▸ hi)
  have avoids (l : Nat) (hl : l ∉ s.domain.effects) :
      Disjoint (insert j (s.domain.effects.erase i))
        (Function.update Effect.var j (Effect.var i) l).vars := by
    by_cases h : l = j
    · simp [h, Effect.var, hji.symm]
    · simp [h, Effect.var, hl]
  constructor
  · intro k hk
    have old := hs.type_range k hk
    apply T.support_subst_avoids
    · intro l hl
      have hld : l ∉ s.domain.types := fun h => Finset.disjoint_left.mp old.1 h hl
      simp [Substitution.pivotEffect, T.support_var, Names.Disjoint, hld]
    · intro l hl
      exact avoids l (fun h => Finset.disjoint_left.mp old.2 h hl)
  · intro k hk
    have old : Disjoint s.domain.effects (s.effects k).vars := by
      rcases Finset.mem_insert.mp hk with hk | hk
      · rw [hk, s.effects_outside j hj]; simpa [Effect.var] using hj
      · exact hs.effect_range k (Finset.mem_erase.mp hk).2
    apply Finset.disjoint_left.mpr
    intro l hl hm
    obtain ⟨k, hk, hkl⟩ := Finset.mem_biUnion.mp hm
    exact Finset.disjoint_left.mp
      (avoids k (fun h => Finset.disjoint_left.mp old h hk)) hl hkl

/-- A change of bound names is a finite permutation. Its inverse exists;
arbitrary non-injective renaming is not alpha conversion. -/
structure Renaming where
  domain : Names
  types : Equiv.Perm Nat
  effects : Equiv.Perm Nat
  types_outside : ∀ i, i ∉ domain.types → types i = i
  effects_outside : ∀ i, i ∉ domain.effects → effects i = i

def Renaming.asSubstitution (p : Renaming) (T : TypeDomain) : Substitution T where
  domain := p.domain
  types := fun i => T.var (p.types i)
  effects := fun i => Effect.var (p.effects i)
  types_outside := by intro i hi; rw [p.types_outside i hi]
  effects_outside := by intro i hi; rw [p.effects_outside i hi]

def Renaming.inverse (p : Renaming) : Renaming where
  domain := p.domain
  types := p.types.symm
  effects := p.effects.symm
  types_outside := by
    intro i hi
    exact (p.types.symm_apply_apply i).symm.trans
      (congrArg p.types.symm (p.types_outside i hi)) |>.symm
  effects_outside := by
    intro i hi
    exact (p.effects.symm_apply_apply i).symm.trans
      (congrArg p.effects.symm (p.effects_outside i hi)) |>.symm

theorem Renaming.pullback_inverse (p : Renaming) (v : Valuation T.Value) :
    (p.asSubstitution T).pullback
      ⟨v.types ∘ p.types.symm, v.effects ∘ p.effects.symm⟩ = v := by
  cases v
  simp [Substitution.pullback, Renaming.asSubstitution, T.eval_var,
    Effect.eval, Effect.var, Function.comp_def]

end EHMX.HMX
