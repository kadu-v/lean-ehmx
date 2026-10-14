import EHMX.TypeClasses.Unification

namespace EHMX.TypeClasses
open HMX

def effectBinding {K} (i : Nat) (e : Effect) : HMX.Substitution (types K) where
  domain := ⟨∅, {i}⟩
  types := Ty.var
  effects := fun j => if j = i then e else Effect.var j
  types_outside := by intros; rfl
  effects_outside := by intro j hj; simp_all

theorem effectBinding_solved {K} (i : Nat) (e : Effect) (occurs : i ∉ e.vars) :
    (effectBinding (K := K) i e).Solved := by
  constructor
  · simp [effectBinding]
  · intro j hj
    have eq : j = i := Finset.mem_singleton.mp hj
    subst j
    simp [effectBinding, occurs]

theorem effectBinding_fixed {K} (i : Nat) (e : Effect) (v : Valuation (Ground K))
    (h : v.effects i = e.eval v.effects) : (effectBinding i e).pullback v = v := by
  apply congrArg₂ Valuation.mk
  · rfl
  · funext j
    by_cases eq : j = i
    · subst j; simpa [effectBinding, Substitution.pullback] using h.symm
    · simp [effectBinding, eq, Effect.eval, Effect.var]

structure EffectBinding {K} (E : ClassEnv K) (c : Formula K E.count) where
  name : Nat
  value : Effect
  occurs : name ∉ value.vars
  forced : ∀ v, Formula.Holds E c v → v.effects name = value.eval v.effects

def effectAssignment (allowed : Finset Nat) (a b : Effect) : Option {i : Nat // a = Effect.var i ∧ i ∉ b.vars} :=
  (a.vars.sort (· ≤ ·)).findSome? (fun i =>
    if i ∈ allowed then
      if h : a = Effect.var i ∧ i ∉ b.vars then some ⟨i, h⟩ else none
    else none)

def effectPair {K} (E : ClassEnv K) (allowed : Finset Nat) (a b : Effect) :
    Option (EffectBinding E (.and (.effectLe a b) (.effectLe b a))) := by
  match effectAssignment allowed a b with
  | some p =>
    exact some ⟨p.val, b, p.property.2, fun v h => by
      have eq := Finset.Subset.antisymm h.1 h.2
      simpa [p.property.1, Effect.eval, Effect.var] using eq⟩
  | none =>
    match effectAssignment allowed b a with
    | some p =>
      exact some ⟨p.val, a, p.property.2, fun v h => by
        have eq := Finset.Subset.antisymm h.2 h.1
        simpa [p.property.1, Effect.eval, Effect.var] using eq⟩
    | none => exact none

def findEffectBinding {K} (E : ClassEnv K) (allowed : Finset Nat) : (c : Formula K E.count) → Option (EffectBinding E c)
  | .and (.effectLe a b) (.effectLe c d) =>
    if h : a = d ∧ b = c then by
      rcases h with ⟨rfl, rfl⟩
      exact effectPair E allowed a b
    else none
  | .and a b =>
    match findEffectBinding E allowed a with
    | some r => some ⟨r.name, r.value, r.occurs, fun v h => r.forced v h.1⟩
    | none => match findEffectBinding E allowed b with
      | some r => some ⟨r.name, r.value, r.occurs, fun v h => r.forced v h.2⟩
      | none => none
  | _ => none

theorem eliminate_effect {K} (E : ClassEnv K) (a : Names) (c : Formula K E.count)
    (b : EffectBinding E c) (inside : b.name ∈ a.effects) (v) :
    Formula.Holds E (.ex (a.diff ⟨∅, {b.name}⟩)
      (simplify E (push E (effectBinding b.name b.value) c))) v ↔ Formula.Holds E (.ex a c) v := by
  let s := effectBinding (K := K) b.name b.value
  have solved : s.Solved := effectBinding_solved _ _ b.occurs
  have same w : Formula.Holds E (simplify E (push E s c)) w ↔ Formula.Holds E c (s.pullback w) :=
    (simplify_correct E _ w).trans (push_correct E s c w)
  rw [holds_ex, holds_ex]
  constructor
  · rintro ⟨w, outside, hw⟩
    refine ⟨s.pullback w, ⟨?_, ?_⟩, (same w).mp hw⟩
    · intro i hi
      exact outside.1 i (by simpa [Names.diff] using hi)
    · intro i hi
      have ne : i ≠ b.name := fun eq => hi (eq ▸ inside)
      have equal := outside.2 i (by simp [Names.diff, hi])
      simpa [s, effectBinding, Substitution.pullback, ne, Effect.eval, Effect.var] using equal
  · rintro ⟨w, outside, hw⟩
    let u : Valuation (Ground K) := ⟨w.types, Function.update w.effects b.name (v.effects b.name)⟩
    have sameOutside : u.AgreeOutside w s.domain := by
      constructor
      · intro i _; rfl
      · intro i hi
        have ne : i ≠ b.name := by simpa [s, effectBinding] using hi
        simp [u, ne]
    have fixed := effectBinding_fixed b.name b.value w (b.forced w hw)
    refine ⟨u, ⟨?_, ?_⟩, (same u).mpr ?_⟩
    · intro i hi
      exact outside.1 i (by simpa [Names.diff] using hi)
    · intro i hi
      by_cases eq : i = b.name
      · subst i; simp [u]
      · have hn : i ∉ a.effects := by simpa [Names.diff, eq] using hi
        simpa [u, eq] using outside.2 i hn
    · rwa [solved.pullback_agreeOutside sameOutside, fixed]

end EHMX.TypeClasses
