import SystemFXi.EHMX.Syntax
import Mathlib.Data.Finset.Sort

namespace SystemFXi.EHMX

private theorem eval_union (ρ : Nat → Finset Op) (ε η : Effect) :
    (ε ∪ η).eval ρ = ε.eval ρ ∪ η.eval ρ := by
  ext op
  simp only [Poly.Effect.eval, Poly.Effect.labels_union, Poly.Effect.vars_union,
    Finset.mem_union, Finset.mem_biUnion]
  aesop

private theorem eval_singleton (ρ : Nat → Finset Op) (op : Op) :
    (Poly.Effect.singleton op).eval ρ = {op} := by
  simp [Poly.Effect.eval, Poly.Effect.singleton]

/-- The three primitive constraints characterize exact removal of one operation. -/
theorem Constraint.split_iff {X : Domain} (ρ : Valuation)
    (op : Op) (ε δ : Effect) :
    (Constraint.split (X := X) op ε δ).holds ρ ↔
      δ.eval ρ.effects = ε.eval ρ.effects \ {op} := by
  rw [Constraint.split]
  change (δ.eval ρ.effects ⊆ ε.eval ρ.effects ∧
      ε.eval ρ.effects ⊆ (Poly.Effect.singleton op ∪ δ).eval ρ.effects ∧
      op ∉ δ.eval ρ.effects) ↔ _
  rw [eval_union, eval_singleton]
  constructor
  · rintro ⟨hde, hed, hnot⟩
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro hx
      exact ⟨hde hx, by
        intro heq
        subst x
        exact hnot hx⟩
    · rintro ⟨hx, hneq⟩
      rcases Finset.mem_union.mp (hed hx) with hop | hδ
      · exact False.elim (hneq (Finset.mem_singleton.mp hop))
      · exact hδ
  · intro heq
    constructor
    · intro x hx
      rw [heq] at hx
      exact (Finset.mem_sdiff.mp hx).1
    constructor
    · intro x hx
      by_cases hxo : x = op
      · subst x
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self op))
      · apply Finset.mem_union.mpr
        right
        rw [heq]
        exact Finset.mem_sdiff.mpr ⟨hx, by simpa using hxo⟩
    · intro hop
      rw [heq] at hop
      exact (Finset.mem_sdiff.mp hop).2 (Finset.mem_singleton_self op)

/-- Closing a clause constraint over a rigid type variable still implies its
instance at the current valuation. -/
theorem Constraint.allTy_current {X : Domain} (i : Nat) (c : Constraint X) :
    (Constraint.allTy i c).Entails c := by
  intro ρ h
  have hi := h (ρ.types i)
  simpa [Constraint.holds] using hi

theorem Constraint.allEff_current {X : Domain} (i : Nat) (c : Constraint X) :
    (Constraint.allEff i c).Entails c := by
  intro ρ h
  have hi := h (ρ.effects i)
  simpa [Constraint.holds] using hi

def Constraint.closeTypes {X : Domain} (vars : List Nat) (c : Constraint X) :
    Constraint X := vars.foldr Constraint.allTy c

def Constraint.closeEffects {X : Domain} (vars : List Nat) (c : Constraint X) :
    Constraint X := vars.foldr Constraint.allEff c

def Constraint.close {X : Domain} (types effects : Finset Nat)
    (c : Constraint X) : Constraint X :=
  Constraint.closeTypes (types.sort (· ≤ ·))
    (Constraint.closeEffects (effects.sort (· ≤ ·)) c)

theorem Constraint.closeTypes_current {X : Domain} (vars : List Nat)
    (c : Constraint X) : (Constraint.closeTypes vars c).Entails c := by
  induction vars with
  | nil => exact Constraint.entails_refl c
  | cons i rest ih =>
      exact Constraint.entails_trans (Constraint.allTy_current i _ ) ih

theorem Constraint.closeEffects_current {X : Domain} (vars : List Nat)
    (c : Constraint X) : (Constraint.closeEffects vars c).Entails c := by
  induction vars with
  | nil => exact Constraint.entails_refl c
  | cons i rest ih =>
      exact Constraint.entails_trans (Constraint.allEff_current i _) ih

theorem Constraint.close_current {X : Domain} (types effects : Finset Nat)
    (c : Constraint X) : (Constraint.close types effects c).Entails c := by
  exact Constraint.entails_trans
    (Constraint.closeTypes_current (types.sort (· ≤ ·)) _)
    (Constraint.closeEffects_current (effects.sort (· ≤ ·)) c)

/-- A rigid operation type variable cannot equal an independent fixed type
variable at every instantiation. -/
theorem Constraint.rigid_var_eq_unsat {X : Domain} (i j : Nat)
    (hij : i ≠ j) (ρ : Valuation) :
    ¬ (Constraint.allTy (X := X) i (.typeEq (.var i) (.var j))).holds ρ := by
  intro h
  have h0 := h (.atom 0)
  have h1 := h (.atom 1)
  have hji : j ≠ i := Ne.symm hij
  simp [Constraint.holds, Ty.eval, hji] at h0 h1
  have h01 := h0.trans h1.symm
  cases h01

end SystemFXi.EHMX
