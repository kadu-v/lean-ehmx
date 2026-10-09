import SystemFXi.EHMX.GenericPrincipal

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

/-- An abstract X formula used as one atom of the already verified syntax.
The two maps are delayed renamings. Storing them lets the atom domain obey
HM(X)'s arbitrary-renaming law without requiring non-injective renaming of
formulas with internal binders. -/
structure Atom (X : ConstraintSystem) where
  formula : X.Formula
  types : Nat → Nat
  effects : Nat → Nat

def Atom.embed {X : ConstraintSystem} (c : X.Formula) : Atom X :=
  ⟨c, id, id⟩

def atomDomain (X : ConstraintSystem) : Domain where
  Pred := Atom X
  rename := fun ft fe p =>
    ⟨p.formula, ft ∘ p.types, fe ∘ p.effects⟩
  holds := fun v p =>
    X.holds p.formula (v.pullback p.types p.effects)
  fvTypes := fun p => (X.freeTypes p.formula).image p.types
  fvEffects := fun p => (X.freeEffects p.formula).image p.effects

theorem atomDomain_lawfulRename (X : ConstraintSystem) :
    LawfulRename (atomDomain X) := by
  constructor
  intro ft fe p v
  rfl

theorem atomDomain_lawfulSupport (X : ConstraintSystem) :
    LawfulSupport (atomDomain X) := by
  constructor
  intro p v w ht he
  apply X.free_support p.formula
    (v.pullback p.types p.effects)
    (w.pullback p.types p.effects)
  · intro i hi
    exact ht (p.types i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · intro i hi
    exact he (p.effects i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem atomDomain_lawfulFVRename (X : ConstraintSystem) :
    LawfulFVRename (atomDomain X) := by
  constructor
  · intro ft fe p i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨p.types j,
      Finset.mem_image.mpr ⟨j, hj, rfl⟩, rfl⟩
  · intro ft fe p i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨p.effects j,
      Finset.mem_image.mpr ⟨j, hj, rfl⟩, rfl⟩

theorem atomDomain_embed_holds (X : ConstraintSystem)
    (c : X.Formula) (v : Valuation) :
    (atomDomain X).holds v (Atom.embed c) ↔ X.holds c v := by
  rfl

theorem atomDomain_embed_freeTypes (X : ConstraintSystem)
    (c : X.Formula) :
    (atomDomain X).fvTypes (Atom.embed c) = X.freeTypes c := by
  simp [atomDomain, Atom.embed]

theorem atomDomain_embed_freeEffects (X : ConstraintSystem)
    (c : X.Formula) :
    (atomDomain X).fvEffects (Atom.embed c) = X.freeEffects c := by
  simp [atomDomain, Atom.embed]

def embedScheme {X : ConstraintSystem} (σ : Generic.Scheme X) :
    SystemFXi.EHMX.Scheme (atomDomain X) :=
  ⟨σ.typeVars, σ.effectVars, .predicate (Atom.embed σ.condition), σ.result⟩

def embedContext {X : ConstraintSystem} (Γ : Generic.Context X) :
    SystemFXi.EHMX.Context (atomDomain X) :=
  Γ.map embedScheme

theorem embedScheme_fvTypes {X : ConstraintSystem}
    (σ : Generic.Scheme X) :
    (embedScheme σ).fvTypes = σ.freeTypes := by
  simp [embedScheme, SystemFXi.EHMX.Scheme.fvTypes,
    Generic.Scheme.freeTypes, Constraint.fvTypes, atomDomain, Atom.embed]

theorem embedScheme_fvEffects {X : ConstraintSystem}
    (σ : Generic.Scheme X) :
    (embedScheme σ).fvEffects = σ.freeEffects := by
  simp [embedScheme, SystemFXi.EHMX.Scheme.fvEffects,
    Generic.Scheme.freeEffects, Constraint.fvEffects, atomDomain, Atom.embed]

theorem embedContext_fvTypes {X : ConstraintSystem}
    (Γ : Generic.Context X) :
    (embedContext Γ).fvTypes = Γ.freeTypes := by
  have aux : ∀ (xs : Generic.Context X) (acc : Finset Nat),
      (xs.map embedScheme).foldl (fun a σ => a ∪ σ.fvTypes) acc =
        xs.foldl (fun a σ => a ∪ σ.freeTypes) acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons σ rest ih =>
        intro acc
        simp only [List.map_cons, List.foldl_cons]
        rw [embedScheme_fvTypes]
        exact ih _
  exact aux Γ ∅

theorem embedContext_fvEffects {X : ConstraintSystem}
    (Γ : Generic.Context X) :
    (embedContext Γ).fvEffects = Γ.freeEffects := by
  have aux : ∀ (xs : Generic.Context X) (acc : Finset Nat),
      (xs.map embedScheme).foldl (fun a σ => a ∪ σ.fvEffects) acc =
        xs.foldl (fun a σ => a ∪ σ.freeEffects) acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons σ rest ih =>
        intro acc
        simp only [List.map_cons, List.foldl_cons]
        rw [embedScheme_fvEffects]
        exact ih _
  exact aux Γ ∅

end SystemFXi.EHMX.Generic
