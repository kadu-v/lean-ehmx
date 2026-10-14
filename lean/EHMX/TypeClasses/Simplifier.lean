import EHMX.TypeClasses.Reduction
import EHMX.TypeClasses.Equations
import EHMX.TypeClasses.Occurs

namespace EHMX.TypeClasses
open HMX

def variableEquation {K n} (i : Nat) (t : Ty K) : Formula K n :=
  if _h : i ∈ t.types ∧ t ≠ .var i then .bot else equations (.var i) t

theorem variableEquation_correct {K} (E : ClassEnv K) (i t v) :
    Formula.Holds E (variableEquation i t) v ↔ v.types i = t.eval v := by
  unfold variableEquation
  split
  · rename_i h
    simp only [holds_bot, false_iff]
    exact t.occurs_impossible i h.1 h.2 v
  · exact equations_correct E (.var i) t v

def reduceEq {K n} : Ty K → Ty K → Formula K n
  | .var i, t => variableEquation i t
  | t, .var i => variableEquation i t
  | a, b => equations a b

theorem reduceEq_correct {K} (E : ClassEnv K) (a b v) :
    Formula.Holds E (reduceEq a b) v ↔ a.eval v = b.eval v := by
  cases a <;> cases b <;>
    simp only [reduceEq, variableEquation_correct, equations_correct, Ty.eval]
  all_goals exact eq_comm

def reduceEffectLe {K n} (a b : Effect) : Formula K n := if a = b then .top else .effectLe a b

theorem reduceEffectLe_correct {K} (E : ClassEnv K) (a b v) :
    Formula.Holds E (reduceEffectLe a b) v ↔ a.eval v.effects ⊆ b.eval v.effects := by
  unfold reduceEffectLe
  split <;> simp_all

def push {K} (E : ClassEnv K) (s : HMX.Substitution (types K)) : Formula K E.count → Formula K E.count
  | .top => .top
  | .bot => .bot
  | .and a b => smartAnd (push E s a) (push E s b)
  | .eq a b => reduceEq (s.apply a) (s.apply b)
  | .pred c t => reducePred E (s.apply t) c
  | .effectLe a b => reduceEffectLe (a.subst s.effects) (b.subst s.effects)
  | .lacks op a => .lacks op (a.subst s.effects)
  | .subst r c => .subst (s.compose r) c
  | c => .subst s c

theorem push_correct {K} (E : ClassEnv K) (s c v) :
    Formula.Holds E (push E s c) v ↔ Formula.Holds E c (s.pullback v) := by
  induction c with
  | top => simp [push]
  | bot => simp [push]
  | and a b ha hb => simp only [push, smartAnd_correct, ha, hb, holds_and]
  | eq a b => simp only [push, reduceEq_correct, holds_eq, eval_apply]
  | pred c t => simp only [push, reducePred_correct, holds_pred, eval_apply]
  | effectLe a b =>
    simp only [push, reduceEffectLe_correct, Effect.eval_subst]
    rfl
  | lacks op a =>
    change op ∉ (a.subst s.effects).eval v.effects ↔ _
    simp only [Effect.eval_subst]
    rfl
  | subst r c ih => simp only [push, holds_subst, Substitution.compose_pullback]
  | ex a c ih => rfl
  | clause a b c ih => rfl

def smartExCore {K} (E : ClassEnv K) (a : Names) : Formula K E.count → Formula K E.count
  | .top => .top
  | .bot => .bot
  | .pred c (.var i) => projectPred E a c i
  | c => .ex a c

theorem smartExCore_correct {K} (E : ClassEnv K) (a c v) :
    Formula.Holds E (smartExCore E a c) v ↔ Formula.Holds E (.ex a c) v := by
  cases c with
  | top =>
    simp only [smartExCore, holds_top, holds_ex, and_true, true_iff]
    exact ⟨v, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  | bot => simp [smartExCore]
  | pred c t => cases t <;> first | exact projectPred_correct E a c _ v | rfl
  | _ => rfl

def smartEx {K} (E : ClassEnv K) (a : Names) (c : Formula K E.count) : Formula K E.count :=
  if a = Names.empty then c else smartExCore E a c

theorem smartEx_correct {K} (E : ClassEnv K) (a c v) :
    Formula.Holds E (smartEx E a c) v ↔ Formula.Holds E (.ex a c) v := by
  unfold smartEx
  split
  next h =>
    subst a
    rw [holds_ex]
    constructor
    · intro hc; exact ⟨v, ⟨fun _ _ => rfl, fun _ _ => rfl⟩, hc⟩
    · rintro ⟨w, hw, hc⟩
      have eq : w = v := by
        apply congrArg₂ Valuation.mk
        · funext i; exact hw.1 i (by simp [Names.empty])
        · funext i; exact hw.2 i (by simp [Names.empty])
      rwa [eq] at hc
  next _ => exact smartExCore_correct E a c v

def smartClause {K n} (rigid witnesses : Names) : Formula K n → Formula K n
  | .top => .top
  | .bot => .bot
  | c => .clause rigid witnesses c

theorem smartClause_correct {K} (E : ClassEnv K) (a b c v) :
    Formula.Holds E (smartClause a b c) v ↔ Formula.Holds E (.clause a b c) v := by
  cases c with
  | top =>
    rw [show smartClause a b (.top : Formula K E.count) = .top from rfl, holds_top,
      holds_clause]
    simp only [holds_top, and_true, true_iff]
    intro w _
    exact ⟨w, ⟨fun _ _ => rfl, fun _ _ => rfl⟩⟩
  | bot =>
    simp only [smartClause, holds_bot, false_iff]
    intro h
    obtain ⟨u, _, hu⟩ := (holds_clause E a b .bot v).mp h v ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    exact holds_bot E u hu
  | _ => rfl

def simplify {K} (E : ClassEnv K) : Formula K E.count → Formula K E.count
  | .top => .top
  | .bot => .bot
  | .and a b => smartAnd (simplify E a) (simplify E b)
  | .eq a b => reduceEq a b
  | .pred c t => reducePred E t c
  | .effectLe a b => reduceEffectLe a b
  | .ex a c => smartEx E a (simplify E c)
  | .clause a b c => smartClause a b (simplify E c)
  | .subst s c => push E s (simplify E c)
  | c => c

theorem simplify_correct {K} (E : ClassEnv K) (c v) :
    Formula.Holds E (simplify E c) v ↔ Formula.Holds E c v := by
  induction c generalizing v with
  | top => rfl
  | bot => rfl
  | and a b ha hb => simp only [simplify, smartAnd_correct, ha, hb, holds_and]
  | eq a b => exact reduceEq_correct E a b v
  | pred c t => exact reducePred_correct E t c v
  | effectLe a b => exact reduceEffectLe_correct E a b v
  | lacks op a => rfl
  | ex a c ih => simp only [simplify, smartEx_correct, holds_ex, ih]
  | clause a b c ih =>
    simp only [simplify, smartClause_correct, holds_clause, ih]
  | subst s c ih => simp only [simplify, push_correct, holds_subst, ih]

def simplifier {K} (E : ClassEnv K) : (constraints E).Simplifier where
  run := simplify E
  equivalent := fun c => ⟨fun v => (simplify_correct E c v).mp, fun v => (simplify_correct E c v).mpr⟩

end EHMX.TypeClasses
