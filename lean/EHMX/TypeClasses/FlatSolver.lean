import EHMX.TypeClasses.Simplifier
import EHMX.TypeClasses.EffectPropagation

namespace EHMX.TypeClasses
open HMX

structure Flat (K : Constructors) (n : Nat) where
  predicates : List (Fin n × Nat)
  effects : List EffectAtom

def predVars {n} (ps : List (Fin n × Nat)) := ps.toFinset.image Prod.snd
def requirements {n} (ps : List (Fin n × Nat)) (i : Nat) : Finset (Fin n) :=
  (ps.toFinset.filter (fun p => p.2 = i)).image Prod.fst

theorem mem_requirements {n} (ps : List (Fin n × Nat)) (i c) :
    c ∈ requirements ps i ↔ (c, i) ∈ ps := by
  simp [requirements]

def predicatesSat {K} (E : ClassEnv K) (ps : List (Fin E.count × Nat)) : Bool :=
  decide (∀ i ∈ predVars ps, inhabited E (requirements ps i) = true)

theorem predicatesSat_iff {K} (E : ClassEnv K) (ps) :
    predicatesSat E ps = true ↔ ∃ v : Nat → Ground K, ∀ p ∈ ps, p.1 ∈ (v p.2).classes E := by
  classical
  simp only [predicatesSat, decide_eq_true_eq]
  constructor
  · intro h
    have witnesses (i : Nat) : ∃ t : Ground K, ∀ c, (c, i) ∈ ps → c ∈ t.classes E := by
      by_cases hi : i ∈ predVars ps
      · obtain ⟨t, ht⟩ := (inhabited_iff E _).mp (h i hi)
        exact ⟨t, fun c hc => ht ((mem_requirements ps i c).mpr hc)⟩
      · refine ⟨.base .int, ?_⟩
        intro c hc
        exact False.elim (hi (Finset.mem_image.mpr ⟨(c, i), List.mem_toFinset.mpr hc, rfl⟩))
    choose v hv using witnesses
    exact ⟨v, fun p hp => hv p.2 p.1 hp⟩
  · rintro ⟨v, hv⟩ i _
    apply (inhabited_iff E _).mpr
    exact ⟨v i, fun c hc => hv (c, i) ((mem_requirements ps i c).mp hc)⟩

def collect {K n} : Formula K n → Option (Flat K n)
  | .top => some ⟨[], []⟩
  | .and a b => do
      let a ← collect a
      let b ← collect b
      pure ⟨a.predicates ++ b.predicates, a.effects ++ b.effects⟩
  | .pred c (.var i) => some ⟨[(c, i)], []⟩
  | .effectLe a b => some ⟨[], [.le a b]⟩
  | .lacks op a => some ⟨[], [.lacks op a]⟩
  | _ => none

theorem collect_correct {K} (E : ClassEnv K) (c f)
    (hc : collect c = some f) (v) :
    Formula.Holds E c v ↔
      (∀ p ∈ f.predicates, p.1 ∈ (v.types p.2).classes E) ∧
      ∀ a ∈ f.effects, a.Holds v.effects := by
  induction c generalizing f with
  | top => cases hc; simp at *
  | and a b ha hb =>
    cases hfa : collect a with
    | none => simp [collect, hfa] at hc
    | some fa =>
      cases hfb : collect b with
      | none => simp [collect, hfa, hfb] at hc
      | some fb =>
        have eq : f = ⟨fa.predicates ++ fb.predicates, fa.effects ++ fb.effects⟩ := by
          simpa [collect, hfa, hfb] using hc.symm
        subst f
        rw [holds_and, ha _ hfa, hb _ hfb]
        simp only [List.mem_append, or_imp, forall_and]
        tauto
  | pred c t =>
    cases t <;> simp only [collect, Option.some.injEq, reduceCtorEq] at hc
    subst f
    simp [Ty.eval]
  | effectLe a b => cases hc; simp [EffectAtom.Holds] at *
  | lacks op a => cases hc; simp [EffectAtom.Holds] at *
  | _ => simp [collect] at hc

def flatSat {K} (E : ClassEnv K) (f : Flat K E.count) : Bool :=
  predicatesSat E f.predicates && propagationSat f.effects

theorem flatSat_iff {K} (E : ClassEnv K) (c f) (hc : collect c = some f) :
    flatSat E f = true ↔ (constraints E).Satisfiable c := by
  rw [flatSat, Bool.and_eq_true, predicatesSat_iff, propagationSat_iff]
  constructor
  · rintro ⟨⟨vt, ht⟩, ve, he⟩
    exact ⟨⟨vt, ve⟩, (collect_correct E c f hc _).mpr ⟨ht, he⟩⟩
  · rintro ⟨v, hv⟩
    obtain ⟨ht, he⟩ := (collect_correct E c f hc v).mp hv
    exact ⟨⟨v.types, ht⟩, v.effects, he⟩

end EHMX.TypeClasses
