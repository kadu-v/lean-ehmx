import EHMX.TypeClasses.Simplifier

namespace EHMX.TypeClasses
open HMX

def binding {K} (i : Nat) (t : Ty K) : HMX.Substitution (types K) where
  domain := ⟨{i}, ∅⟩
  types := fun j => if j = i then t else .var j
  effects := Effect.var
  types_outside := by intro j hj; simp_all
  effects_outside := by intros; rfl

theorem binding_solved {K} (i : Nat) (t : Ty K) (occurs : i ∉ t.types) :
    (binding i t).Solved := by
  constructor
  · intro j hj
    have eq : j = i := Finset.mem_singleton.mp hj
    subst j
    simp [binding, Names.Disjoint, occurs]
  · simp [binding]

theorem binding_fixed {K} (i : Nat) (t : Ty K) (v : Valuation (Ground K))
    (h : v.types i = t.eval v) : (binding i t).pullback v = v := by
  apply congrArg₂ Valuation.mk
  · funext j
    by_cases eq : j = i
    · subst j; simpa [binding, Substitution.pullback] using h.symm
    · simp [binding, eq, Ty.eval]
  · funext j; simp [binding, Effect.eval, Effect.var]

structure Binding {K} (E : ClassEnv K) (c : Formula K E.count) where
  name : Nat
  value : Ty K
  occurs : name ∉ value.types
  forced : ∀ v, Formula.Holds E c v → v.types name = value.eval v

def findBinding {K} (E : ClassEnv K) (keep : Finset Nat) :
    (c : Formula K E.count) → Option (Binding E c)
  | .eq (.var i) (.var j) =>
    if h : i ≠ j ∧ i ∉ keep then
      some ⟨i, .var j, by simpa [Ty.types] using h.1, fun _ h => h⟩
    else if h : j ≠ i ∧ j ∉ keep then
      some ⟨j, .var i, by simpa [Ty.types] using h.1, fun _ h => h.symm⟩
    else none
  | .eq (.var i) t =>
    if h : i ∉ t.types ∧ i ∉ keep then
      some ⟨i, t, h.1, fun _ h => h⟩ else none
  | .eq t (.var i) =>
    if h : i ∉ t.types ∧ i ∉ keep then
      some ⟨i, t, h.1, fun _ h => h.symm⟩ else none
  | .and a b =>
    match findBinding E keep a with
    | some r => some ⟨r.name, r.value, r.occurs, fun v h => r.forced v h.1⟩
    | none => match findBinding E keep b with
      | some r => some ⟨r.name, r.value, r.occurs, fun v h => r.forced v h.2⟩
      | none => none
  | _ => none

theorem findBinding_protected {K} (E : ClassEnv K) (p c r)
    (h : findBinding E p c = some r) : r.name ∉ p := by
  fun_induction findBinding E p c <;> simp_all <;> subst r <;> simp_all

theorem Binding.sat_iff {K} {E : ClassEnv K} {c : Formula K E.count} (b : Binding E c) :
    (constraints E).Satisfiable (simplify E (push E (binding b.name b.value) c)) ↔
      (constraints E).Satisfiable c := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨_, (push_correct E _ c v).mp ((simplify_correct E _ v).mp hv)⟩
  · rintro ⟨v, hv⟩
    refine ⟨v, (simplify_correct E _ v).mpr ((push_correct E _ c v).mpr ?_)⟩
    rwa [binding_fixed b.name b.value v (b.forced v hv)]

theorem binding_guessFree {K} (E : ClassEnv K) (g c : Formula K E.count)
    (b : Binding E c) (fresh : b.name ∉ ((constraints E).support g).types) :
    (⟨simplify E (push E (binding b.name b.value) c), binding b.name b.value⟩ :
      (constraints E).NormalForm).GuessFreeSolution g c := by
  let X := constraints E
  let s := binding b.name b.value
  have solved : s.Solved := binding_solved _ _ b.occurs
  have same v : Formula.Holds E (simplify E (push E s c)) v ↔ Formula.Holds E c (s.pullback v) :=
    (simplify_correct E _ v).trans (push_correct E s c v)
  constructor
  · refine ⟨solved, ?_, ?_, ?_⟩
    · apply X.avoids_of_transport
      intro v w outside hv
      apply (X.holds_support g v w ?_).mp hv
      constructor
      · intro i hi
        exact outside.1 i (by simpa [s, binding] using fun eq : i = b.name => fresh (eq ▸ hi))
      · intro i _; exact outside.2 i (by simp [binding])
    · apply X.avoids_of_transport
      intro v w outside hv
      apply (same w).mpr
      rw [← solved.pullback_agreeOutside outside]
      exact (same v).mp hv
    · intro v hv
      exact (X.holds_subst _ _ _).mpr ((same v).mp hv.2)
  · intro v hv
    have fixed : s.pullback v = v := binding_fixed _ _ v (b.forced v hv.2)
    refine (X.holds_and _ _ _).mpr ⟨(same v).mpr (by rw [fixed]; exact hv.2), ?_⟩
    have graph := X.substitutionConstraint_pullback s solved.idempotent v
    rwa [fixed] at graph

end EHMX.TypeClasses
