import EHMX.TypeClasses.Decision
import EHMX.TypeClasses.EffectUnification

namespace EHMX.TypeClasses
open HMX

theorem eliminate_bound {K} (E : ClassEnv K) (a : Names) (c : Formula K E.count)
    (b : Binding E c) (inside : b.name ∈ a.types) (v) :
    Formula.Holds E (.ex (a.diff ⟨{b.name}, ∅⟩)
      (simplify E (push E (binding b.name b.value) c))) v ↔ Formula.Holds E (.ex a c) v := by
  let s := binding b.name b.value
  have solved : s.Solved := binding_solved _ _ b.occurs
  have same w : Formula.Holds E (simplify E (push E s c)) w ↔ Formula.Holds E c (s.pullback w) :=
    (simplify_correct E _ w).trans (push_correct E s c w)
  rw [holds_ex, holds_ex]
  constructor
  · rintro ⟨w, outside, hw⟩
    refine ⟨s.pullback w, ⟨?_, ?_⟩, (same w).mp hw⟩
    · intro i hi
      have ne : i ≠ b.name := fun eq => hi (eq ▸ inside)
      have equal := outside.1 i (by simp [Names.diff, hi])
      simpa [s, binding, Substitution.pullback, ne, Ty.eval] using equal
    · intro i hi
      simpa [s, binding, Substitution.pullback, Effect.eval, Effect.var] using
        outside.2 i (by simpa [Names.diff] using hi)
  · rintro ⟨w, outside, hw⟩
    let u : Valuation (Ground K) := ⟨Function.update w.types b.name (v.types b.name), w.effects⟩
    have sameOutside : u.AgreeOutside w s.domain := by
      constructor
      · intro i hi
        have ne : i ≠ b.name := by simpa [s, binding] using hi
        simp [u, ne]
      · intro i _; rfl
    have fixed := binding_fixed b.name b.value w (b.forced w hw)
    refine ⟨u, ⟨?_, ?_⟩, (same u).mpr ?_⟩
    · intro i hi
      by_cases eq : i = b.name
      · subst i; simp [u]
      · have hn : i ∉ a.types := by simpa [Names.diff, eq] using hi
        simpa [u, eq] using outside.1 i hn
    · intro i hi
      exact outside.2 i (by simpa [Names.diff] using hi)
    · rwa [solved.pullback_agreeOutside sameOutside, fixed]

theorem closed_projection {K} (E : ClassEnv K) (a : Names) (c : Formula K E.count)
    (closed : ((constraints E).support c).Subset a) (v) :
    Formula.Holds E (.ex a c) v ↔ (constraints E).Satisfiable c := by
  rw [holds_ex]
  constructor
  · rintro ⟨w, _, hw⟩; exact ⟨w, hw⟩
  · rintro ⟨w, hw⟩
    refine ⟨v.patch w a, Valuation.patch_agreeOutside _ _ _, ?_⟩
    apply ((constraints E).holds_support c _ w ?_).mpr hw
    constructor
    · intro i hi; simp [Valuation.patch, closed.1 hi]
    · intro i hi; simp [Valuation.patch, closed.2 hi]

def closedProject {K} (E : ClassEnv K) (a : Names) (c : Formula K E.count) :
    {d : Formula K E.count // ∀ v, Formula.Holds E d v ↔ Formula.Holds E (.ex a c) v} := by
  if fresh : Disjoint a.types ((constraints E).support c).types ∧
      Disjoint a.effects ((constraints E).support c).effects then
    refine ⟨c, ?_⟩
    intro v
    rw [holds_ex]
    constructor
    · intro h; exact ⟨v, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, h⟩
    · rintro ⟨w, outside, hw⟩
      apply ((constraints E).holds_support c w v ?_).mp hw
      constructor
      · intro i hi
        exact outside.1 i (fun inside => Finset.disjoint_left.mp fresh.1 inside hi)
      · intro i hi
        exact outside.2 i (fun inside => Finset.disjoint_left.mp fresh.2 inside hi)
  else
    exact closedProjectCore E a c

where
  closedProjectCore {K} (E : ClassEnv K) (a : Names) (c : Formula K E.count) :
      {d : Formula K E.count // ∀ v, Formula.Holds E d v ↔ Formula.Holds E (.ex a c) v} := by
    if closed : ((constraints E).support c).types ⊆ a.types ∧
      ((constraints E).support c).effects ⊆ a.effects then
      match decideConstraint E c with
      | .sat h => exact ⟨.top, fun v => by simp only [holds_top, true_iff]; exact (closed_projection E a c closed v).mpr h⟩
      | .unsat h => exact ⟨.bot, fun v => by simp only [holds_bot, false_iff]; exact fun hv => h ((closed_projection E a c closed v).mp hv)⟩
      | .unknown => exact ⟨smartEx E a c, smartEx_correct E a c⟩
    else exact ⟨smartEx E a c, smartEx_correct E a c⟩

def projectWith {K} (E : ClassEnv K) (fuel : Nat) (a : Names) (c : Formula K E.count) :
    {d : Formula K E.count // ∀ v, Formula.Holds E d v ↔ Formula.Holds E (.ex a c) v} := by
  match fuel with
  | 0 => exact closedProject E a c
  | fuel + 1 =>
    let effects :=
      match findEffectBinding E a.effects c with
      | none => closedProject E a c
      | some b =>
        if inside : b.name ∈ a.effects then
          let next := projectWith E fuel (a.diff ⟨∅, {b.name}⟩)
            (simplify E (push E (effectBinding b.name b.value) c))
          ⟨next.val, fun v => (next.property v).trans (eliminate_effect E a c b inside v)⟩
        else closedProject E a c
    match findBinding E (((constraints E).support c).types \ a.types) c with
    | none => exact effects
    | some b =>
      if inside : b.name ∈ a.types then
        let next := projectWith E fuel (a.diff ⟨{b.name}, ∅⟩) (simplify E (push E (binding b.name b.value) c))
        exact ⟨next.val, fun v => (next.property v).trans (eliminate_bound E a c b inside v)⟩
      else exact effects

def project {K} (E : ClassEnv K) (a : Names) (c : Formula K E.count) :=
  projectWith E (a.types.card + a.effects.card) a c

end EHMX.TypeClasses
