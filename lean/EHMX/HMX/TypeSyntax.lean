import EHMX.Syntax
import Mathlib.Data.Fintype.Basic

namespace EHMX.HMX

/-- The two sorts of names used by the effect extension. -/
@[ext] structure Names where
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

theorem Names.Disjoint.mono_left {a b c : Names} (h : c.Disjoint a) (k : b.Subset c) :
    b.Disjoint a := ⟨h.1.mono_left k.1, h.2.mono_left k.2⟩

theorem Names.subset_union_left (a b : Names) : a.Subset (a.union b) :=
  ⟨Finset.subset_union_left, Finset.subset_union_left⟩

theorem Names.subset_union_right (a b : Names) : b.Subset (a.union b) :=
  ⟨Finset.subset_union_right, Finset.subset_union_right⟩

/-- Open constructor signature. A nullary constructor is not required. -/
structure TypeSignature where
  Symbol : Type
  typeArity : Symbol → Nat
  effectArity : Symbol → Nat

inductive TypeTerm (K : TypeSignature) where
  | var : Nat → TypeTerm K
  | arrow : TypeTerm K → Effect → TypeTerm K → TypeTerm K
  | con (k : K.Symbol) : (Fin (K.typeArity k) → TypeTerm K) →
      (Fin (K.effectArity k) → Effect) → TypeTerm K

def TypeTerm.subst {K : TypeSignature} (f : Nat → TypeTerm K) (g : Nat → Effect) :
    TypeTerm K → TypeTerm K
  | .var i => f i
  | .arrow a e b => .arrow (a.subst f g) (e.subst g) (b.subst f g)
  | .con k ts es => .con k (fun i => (ts i).subst f g) (fun i => (es i).subst g)

def TypeTerm.support {K : TypeSignature} : TypeTerm K → Names
  | .var i => ⟨{i}, ∅⟩
  | .arrow a e b => ⟨a.support.types ∪ b.support.types,
      a.support.effects ∪ e.vars ∪ b.support.effects⟩
  | .con _ ts es => ⟨Finset.univ.biUnion (fun i => (ts i).support.types),
      Finset.univ.biUnion (fun i => (ts i).support.effects) ∪
        Finset.univ.biUnion (fun i => (es i).vars)⟩

/-- A representation of a free term algebra, not a ground interpretation.
Representation laws specify syntax operations, not conditions on a solver. -/
structure TypeSyntax where
  signature : TypeSignature
  Term : Type
  representation : Term ≃ TypeTerm signature
  var : Nat → Term
  arrow : Term → Effect → Term → Term
  representation_var : ∀ i, representation (var i) = .var i
  representation_arrow : ∀ a e b, representation (arrow a e b) =
    .arrow (representation a) e (representation b)
  subst : (Nat → Term) → (Nat → Effect) → Term → Term
  representation_subst : ∀ f g t, representation (subst f g t) =
    (representation t).subst (fun i => representation (f i)) g
  subst_var : ∀ f g i, subst f g (var i) = f i
  subst_arrow : ∀ f g a e b, subst f g (arrow a e b) =
    arrow (subst f g a) (e.subst g) (subst f g b)
  support : Term → Names
  representation_support : ∀ t, support t = (representation t).support
  support_var : ∀ i, support (var i) = ⟨{i}, ∅⟩
  support_arrow : ∀ a e b, support (arrow a e b) =
    ⟨(support a).types ∪ (support b).types,
      (support a).effects ∪ e.vars ∪ (support b).effects⟩
  support_subst_types : ∀ f g t, (support (subst f g t)).types =
    (support t).types.biUnion (fun i => (support (f i)).types)
  support_subst_effects : ∀ f g t, (support (subst f g t)).effects =
    (support t).types.biUnion (fun i => (support (f i)).effects) ∪
      (support t).effects.biUnion (fun i => (g i).vars)
  subst_eq_self : ∀ f g t,
    (∀ i ∈ (support t).types, f i = var i) →
    (∀ i ∈ (support t).effects, g i = Effect.var i) → subst f g t = t
  subst_compose : ∀ f g f' g' t,
    subst (fun i => subst f g (f' i)) (fun i => (g' i).subst g) t =
      subst f g (subst f' g' t)

/-- Renaming is substitution by variables, rather than a separate operation. -/
def TypeSyntax.rename (T : TypeSyntax) (f g : Nat → Nat) (t : T.Term) : T.Term :=
  T.subst (fun i => T.var (f i)) (fun i => Effect.var (g i)) t

theorem TypeSyntax.rename_identity (T : TypeSyntax) (t : T.Term) :
    T.rename id id t = t :=
  T.subst_eq_self _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

theorem TypeSyntax.rename_compose (T : TypeSyntax) (f g f' g' : Nat → Nat) (t : T.Term) :
    T.rename f g (T.rename f' g' t) = T.rename (f ∘ f') (g ∘ g') t := by
  rw [TypeSyntax.rename, TypeSyntax.rename, ← T.subst_compose]
  simp [T.subst_var, Effect.subst, Effect.var, TypeSyntax.rename]

theorem TypeSyntax.support_rename (T : TypeSyntax) (f g : Nat → Nat) (t : T.Term) :
    T.support (T.rename f g t) =
      ⟨(T.support t).types.image f, (T.support t).effects.image g⟩ := by
  apply Names.ext
  · ext i
    simp [TypeSyntax.rename, T.support_subst_types, T.support_var, eq_comm]
  · ext i
    simp [TypeSyntax.rename, T.support_subst_effects, T.support_var, Effect.var, eq_comm]

theorem TypeSyntax.support_subst_avoids (T : TypeSyntax)
    (f : Nat → T.Term) (g : Nat → Effect) (t : T.Term) (a : Names)
    (ht : ∀ i ∈ (T.support t).types, a.Disjoint (T.support (f i)))
    (he : ∀ i ∈ (T.support t).effects, Disjoint a.effects (g i).vars) :
    a.Disjoint (T.support (T.subst f g t)) := by
  constructor
  · rw [T.support_subst_types]
    exact (Finset.disjoint_biUnion_right _ _ _).mpr (fun i hi => (ht i hi).1)
  · rw [T.support_subst_effects]
    exact Finset.disjoint_union_right.mpr
      ⟨(Finset.disjoint_biUnion_right _ _ _).mpr (fun i hi => (ht i hi).2),
       (Finset.disjoint_biUnion_right _ _ _).mpr he⟩

/-- A substitution changes only finitely many names. Unlike a valuation, it
is not an arbitrary assignment of ground types to infinitely many names. -/
structure FiniteSubstitution (T : TypeSyntax) where
  /-- A finite upper bound, not the set of names actually changed. -/
  supportBound : Names
  types : Nat → T.Term
  effects : Nat → Effect
  types_outside : ∀ i, i ∉ supportBound.types → types i = T.var i
  effects_outside : ∀ i, i ∉ supportBound.effects → effects i = Effect.var i

def FiniteSubstitution.identity (T : TypeSyntax) : FiniteSubstitution T where
  supportBound := Names.empty
  types := T.var
  effects := Effect.var
  types_outside := by intros; rfl
  effects_outside := by intros; rfl

def FiniteSubstitution.apply {T : TypeSyntax} (s : FiniteSubstitution T) (t : T.Term) : T.Term :=
  T.subst s.types s.effects t

theorem FiniteSubstitution.apply_identity {T : TypeSyntax} (t : T.Term) :
    (FiniteSubstitution.identity T).apply t = t :=
  T.subst_eq_self _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

/-- Apply `s` first and then `r`. Comparison factors are finite substitutions,
but need not be solved: solved substitutions are not closed under composition. -/
def FiniteSubstitution.compose {T : TypeSyntax} (r s : FiniteSubstitution T) : FiniteSubstitution T where
  supportBound := r.supportBound.union s.supportBound
  types := fun i => r.apply (s.types i)
  effects := fun i => (s.effects i).subst r.effects
  types_outside := by
    intro i hi
    have h := Finset.notMem_union.mp hi
    simp [FiniteSubstitution.apply, s.types_outside i h.2, T.subst_var, r.types_outside i h.1]
  effects_outside := by
    intro i hi
    have h := Finset.notMem_union.mp hi
    simp [s.effects_outside i h.2, Effect.subst, Effect.var, r.effects_outside i h.1]

theorem FiniteSubstitution.apply_compose {T : TypeSyntax} (σ θ : FiniteSubstitution T) (t : T.Term) :
    (σ.compose θ).apply t = σ.apply (θ.apply t) :=
  T.subst_compose σ.types σ.effects θ.types θ.effects t

/-- Idempotence on represented terms. For set-normalized effects this alone
does not imply the domain/codomain separation used in dissertation Lemma 4. -/
def FiniteSubstitution.Idempotent {T : TypeSyntax} (s : FiniteSubstitution T) : Prop :=
  (∀ i, s.apply (s.types i) = s.types i) ∧
  (∀ i, (s.effects i).subst s.effects = s.effects i)

theorem FiniteSubstitution.identity_idempotent (T : TypeSyntax) :
    (FiniteSubstitution.identity T).Idempotent := by
  constructor
  · intro i
    exact T.subst_eq_self _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)
  · intro i
    rfl

/-- A change of bound names is a finite permutation. Its inverse exists;
arbitrary non-injective renaming is not alpha conversion. -/
structure Renaming where
  supportBound : Names
  types : Equiv.Perm Nat
  effects : Equiv.Perm Nat
  types_outside : ∀ i, i ∉ supportBound.types → types i = i
  effects_outside : ∀ i, i ∉ supportBound.effects → effects i = i

def Renaming.asFiniteSubstitution (p : Renaming) (T : TypeSyntax) : FiniteSubstitution T where
  supportBound := p.supportBound
  types := fun i => T.var (p.types i)
  effects := fun i => Effect.var (p.effects i)
  types_outside := by intro i hi; rw [p.types_outside i hi]
  effects_outside := by intro i hi; rw [p.effects_outside i hi]

def Renaming.inverse (p : Renaming) : Renaming where
  supportBound := p.supportBound
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

theorem Renaming.apply_inverse (p : Renaming) (T : TypeSyntax) (t : T.Term) :
    T.rename p.inverse.types p.inverse.effects (T.rename p.types p.effects t) = t := by
  rw [T.rename_compose]
  have ht : p.inverse.types ∘ p.types = id := funext p.types.symm_apply_apply
  have he : p.inverse.effects ∘ p.effects = id := funext p.effects.symm_apply_apply
  rw [ht, he, T.rename_identity]

def FiniteSubstitution.singleType (T : TypeSyntax) (i : Nat) (t : T.Term) : FiniteSubstitution T where
  supportBound := ⟨{i}, ∅⟩
  types := fun j => if j = i then t else T.var j
  effects := Effect.var
  types_outside := by intro j hj; simp only [Finset.mem_singleton] at hj; simp [hj]
  effects_outside := by intros; rfl

namespace FiniteSubstitution
variable {T : TypeSyntax}

def restrict (σ : FiniteSubstitution T) (u : Names) : FiniteSubstitution T where
  supportBound := u
  types := fun i => if i ∈ u.types then σ.types i else T.var i
  effects := fun i => if i ∈ u.effects then σ.effects i else Effect.var i
  types_outside := by intro i hi; simp [hi]
  effects_outside := by intro i hi; simp [hi]

/-- Definition 20's syntactic domain, independent of the stored bound. -/
noncomputable def changedNames (σ : FiniteSubstitution T) : Names := by
  classical
  exact ⟨σ.supportBound.types.filter (fun i => σ.types i ≠ T.var i),
    σ.supportBound.effects.filter (fun i => σ.effects i ≠ Effect.var i)⟩

@[simp] theorem mem_changedTypes (σ : FiniteSubstitution T) (i : Nat) :
    i ∈ σ.changedNames.types ↔ σ.types i ≠ T.var i := by
  classical
  simp only [changedNames, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨by_contra fun hi => h (σ.types_outside i hi), h⟩⟩

@[simp] theorem mem_changedEffects (σ : FiniteSubstitution T) (i : Nat) :
    i ∈ σ.changedNames.effects ↔ σ.effects i ≠ Effect.var i := by
  classical
  simp only [changedNames, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨by_contra fun hi => h (σ.effects_outside i hi), h⟩⟩

theorem changedNames_ext {σ θ : FiniteSubstitution T}
    (ht : ∀ i, σ.types i = θ.types i) (he : ∀ i, σ.effects i = θ.effects i) :
    σ.changedNames = θ.changedNames := by
  apply Names.ext <;> ext i
  · simp only [mem_changedTypes, ht]
  · simp only [mem_changedEffects, he]

@[simp] theorem changedNames_identity : (identity T).changedNames = Names.empty := by
  apply Names.ext <;> ext i <;> simp [identity, Names.empty]

def singleEffect (T : TypeSyntax) (i : Nat) (e : Effect) : FiniteSubstitution T where
  supportBound := ⟨∅, {i}⟩
  types := T.var
  effects := fun j => if j = i then e else Effect.var j
  types_outside := by intros; rfl
  effects_outside := by intro j hj; simp only [Finset.mem_singleton] at hj; simp [hj]

end FiniteSubstitution

/-- Definition 6. Raw finite maps do not implicitly acquire idempotence. -/
structure Substitution (T : TypeSyntax) extends FiniteSubstitution T where
  idempotent : toFiniteSubstitution.Idempotent

instance {T : TypeSyntax} : Coe (Substitution T) (FiniteSubstitution T) :=
  ⟨Substitution.toFiniteSubstitution⟩

def Substitution.identity (T : TypeSyntax) : Substitution T :=
  ⟨FiniteSubstitution.identity T, FiniteSubstitution.identity_idempotent T⟩

/-- Figure 3.4's restriction applies to type positions, not predicate arguments. -/
inductive TypeSyntax.InConstraintForm (T : TypeSyntax) : T.Term → Prop where
  | var (i) : T.InConstraintForm (T.var i)
  | arrow {a b} (e) : T.InConstraintForm a → T.InConstraintForm b →
      T.InConstraintForm (T.arrow a e b)

noncomputable def FiniteSubstitution.codomain {T : TypeSyntax}
    (σ : FiniteSubstitution T) : Names :=
  ⟨σ.changedNames.types.biUnion (fun i => (T.support (σ.types i)).types),
    σ.changedNames.types.biUnion (fun i => (T.support (σ.types i)).effects) ∪
    σ.changedNames.effects.biUnion (fun i => (σ.effects i).vars)⟩

end EHMX.HMX
