import EHMX.TypeClasses.Constraints
import EHMX.TypeClasses.Automaton
import Mathlib.Data.List.FinRange

namespace EHMX.TypeClasses
open HMX

def Formula.all {K n} (cs : List (Formula K n)) : Formula K n := cs.foldr .and .top

theorem holds_all {K} (E : ClassEnv K) (cs v) :
    Formula.Holds E (Formula.all cs) v ↔ ∀ c ∈ cs, Formula.Holds E c v := by
  induction cs with
  | nil => simp [Formula.all, holds_top]
  | cons c cs ih =>
    change Formula.Holds E (.and c (Formula.all cs)) v ↔ _
    rw [holds_and E, ih]
    simp

def reducePred {K} (E : ClassEnv K) (t : Ty K) (c : Fin E.count) : Formula K E.count :=
  match t with
  | .var i => .pred c (.var i)
  | .base b => if (c, b) ∈ E.bases then .top else .bot
  | .arr _ _ _ => .bot
  | .con k args => match E.rules c k with
    | none => .bot
    | some req => Formula.all ((List.finRange (K.arity k)).flatMap (fun i =>
        ((List.finRange E.count).filter (fun d => d ∈ req i)).map (fun d => reducePred E (args i) d)))

theorem reducePred_correct {K} (E : ClassEnv K) (t c v) :
    Formula.Holds E (reducePred E t c) v ↔ Formula.Holds E (.pred c t) v := by
  induction t generalizing c with
  | var i => rfl
  | base b =>
    simp only [reducePred, holds_pred, Ty.eval, Ground.classes, Finset.mem_filter, Finset.mem_univ, true_and]
    split <;> simp_all [holds_top, holds_bot]
  | arr a e b ha hb => simp [reducePred, holds_bot, holds_pred, Ty.eval, Ground.classes]
  | con k args ih =>
    rw [holds_pred]
    simp only [Ty.eval, reducePred]
    cases hr : E.rules c k with
    | none => simp [hr, holds_bot, Ground.classes]
    | some req =>
      simp only [holds_all, List.mem_flatMap, List.mem_finRange, true_and,
        List.mem_map, List.mem_filter]
      simp only [Ground.classes, Finset.mem_filter, Finset.mem_univ, true_and, hr, decide_eq_true_eq]
      constructor
      · intro h i d hd
        exact (ih i d).mp (h _ ⟨i, _, ⟨hd, rfl⟩⟩)
      · intro h f hf
        obtain ⟨i, d, hd, rfl⟩ := hf
        exact (ih i d).mpr (h i hd)

def smartAnd {K n} : Formula K n → Formula K n → Formula K n
  | .top, b => b
  | a, .top => a
  | .bot, _ | _, .bot => .bot
  | a, b => .and a b

theorem smartAnd_correct {K} (E : ClassEnv K) (a b v) :
    Formula.Holds E (smartAnd a b) v ↔
      Formula.Holds E a v ∧ Formula.Holds E b v := by
  cases a <;> cases b <;> simp [smartAnd, holds_top,
    holds_and E, holds_bot]

/-- The class automaton discharges an internal existential, without an
assignment to the visible type variables. -/
def projectPred {K} (E : ClassEnv K) (bound : Names) (c : Fin E.count) (i : Nat) : Formula K E.count :=
  if i ∈ bound.types then
    if inhabited E {c} then .top else .bot
  else .ex bound (.pred c (.var i))

theorem projectPred_correct {K} (E : ClassEnv K) (bound c i v) :
    Formula.Holds E (projectPred E bound c i) v ↔
      Formula.Holds E (.ex bound (.pred c (.var i))) v := by
  unfold projectPred
  split
  next inside =>
    have iff : Formula.Holds E (.ex bound (.pred c (.var i))) v ↔ inhabited E {c} = true := by
      rw [holds_ex E, inhabited_iff]
      constructor
      · rintro ⟨w, _, hw⟩
        exact ⟨w.types i, Finset.singleton_subset_iff.mpr hw⟩
      · rintro ⟨t, ht⟩
        let w : Valuation (Ground K) := ⟨Function.update v.types i t, v.effects⟩
        refine ⟨w, ⟨?_, fun _ _ => rfl⟩, ?_⟩
        · intro j hj
          have ne : j ≠ i := fun eq => hj (eq ▸ inside)
          simp [w, Function.update_of_ne ne]
        · change c ∈ (w.types i).classes E
          simpa [w] using Finset.singleton_subset_iff.mp ht
    split <;> simp_all [holds_top, holds_bot]
  next outside => rfl

end EHMX.TypeClasses
