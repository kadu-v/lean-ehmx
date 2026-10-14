import EHMX.TypeClasses.Types
import Mathlib.Data.Fintype.Powerset

namespace EHMX.TypeClasses

/-- Canonical instance table: at most one head for each class/constructor.
Each premise refers to one strict constructor argument. -/
structure ClassEnv (K : Constructors) where
  count : Nat
  supers : Fin count → Finset (Fin count)
  bases : Finset (Fin count × BaseTy)
  rules : (c : Fin count) → (k : Fin K.count) →
    Option (Fin (K.arity k) → Finset (Fin count))

def ClassEnv.covers {K} (E : ClassEnv K) (given wanted : Finset (Fin E.count)) : Prop :=
  ∀ d ∈ wanted, ∃ c ∈ given, d = c ∨ d ∈ E.supers c

instance {K} (E : ClassEnv K) (g w) : Decidable (E.covers g w) := by
  unfold ClassEnv.covers
  infer_instance

def ClassEnv.compatible {K} (E : ClassEnv K) (c s : Fin E.count) (k : Fin K.count) : Bool :=
  match E.rules c k with
  | none => true
  | some req => match E.rules s k with
    | none => false
    | some wanted => decide (∀ i, E.covers (req i) (wanted i))

/-- Superclass compatibility is checked for every instance, not postulated. -/
def ClassEnv.WellFormed {K} (E : ClassEnv K) : Prop :=
  (∀ c, ∀ s ∈ E.supers c, s.val < c.val ∧ E.supers s ⊆ E.supers c) ∧
  (∀ p ∈ E.bases, ∀ s ∈ E.supers p.1, (s, p.2) ∈ E.bases) ∧
  (∀ c, ∀ s ∈ E.supers c, ∀ k, E.compatible c s k = true)

instance {K} (E : ClassEnv K) : Decidable E.WellFormed := by
  unfold ClassEnv.WellFormed
  infer_instance

def ClassEnv.checked {K} (E : ClassEnv K) : Option {e : ClassEnv K // e.WellFormed} :=
  if h : E.WellFormed then some ⟨E, h⟩ else none

/-- Bottom-up evaluation of all class predicates, with structural recursion. -/
def Ground.classes {K} (E : ClassEnv K) : Ground K → Finset (Fin E.count)
  | .base b => Finset.univ.filter (fun c => (c, b) ∈ E.bases)
  | .arr _ _ _ => ∅
  | .con k args => Finset.univ.filter (fun c =>
    (match E.rules c k with
    | none => false
    | some req => decide (∀ i, req i ⊆ (args i).classes E) : Bool) = true)

theorem Ground.classes_supers {K} (E : ClassEnv K) (wf : E.WellFormed)
    (t : Ground K) : ∀ c ∈ t.classes E, E.supers c ⊆ t.classes E := by
  induction t with
  | base b =>
    intro c hc s hs
    simpa [classes] using wf.2.1 (c, b) (by simpa [classes] using hc) s hs
  | arr a e b ha hb => simp [classes]
  | con k args ih =>
    intro c hc s hs
    simp only [classes, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    cases hr : E.rules c k with
    | none => simp [hr] at hc
    | some req =>
      have compat := wf.2.2 c s hs k
      cases hw : E.rules s k with
      | none => simp [ClassEnv.compatible, hr, hw] at compat
      | some wanted =>
        simp only [ClassEnv.compatible, hr, hw, decide_eq_true_eq] at compat
        simp only [decide_eq_true_eq]
        simp only [hr, decide_eq_true_eq] at hc
        intro i d hd
        obtain ⟨q, hq, eq | sup⟩ := compat i d hd
        · subst d; exact hc i hq
        · exact ih i q (hc i hq) sup

/-- Declarative class derivability, independent of the evaluator. -/
inductive Holds {K} (E : ClassEnv K) : Fin E.count → Ground K → Prop
  | base {c b} : (c, b) ∈ E.bases → Holds E c (.base b)
  | con {c k args req} : E.rules c k = some req →
      (∀ i, ∀ d ∈ req i, Holds E d (args i)) → Holds E c (.con k args)
  | super {c s t} : Holds E c t → s ∈ E.supers c → Holds E s t

theorem Holds.classes {K} {E : ClassEnv K} (wf : E.WellFormed)
    {c t} (h : Holds E c t) : c ∈ t.classes E := by
  induction h with
  | base h => simpa [Ground.classes] using h
  | @con c k args req hr _ ih =>
    simpa [Ground.classes, hr] using (show ∀ i, req i ⊆ (args i).classes E from fun i d hd => ih i d hd)
  | super _ hs ih => exact Ground.classes_supers E wf _ _ ih hs

theorem Ground.classes_holds {K} (E : ClassEnv K) (t : Ground K) :
    ∀ c ∈ t.classes E, Holds E c t := by
  induction t with
  | base b => intro c hc; exact .base (by simpa [classes] using hc)
  | arr a e b ha hb => simp [classes]
  | con k args ih =>
    intro c hc
    simp only [classes, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    cases hr : E.rules c k with
    | none => simp [hr] at hc
    | some req =>
      simp only [hr, decide_eq_true_eq] at hc
      exact .con hr (fun i d hd => ih i d (hc i hd))

theorem holds_iff {K} (E : ClassEnv K) (wf : E.WellFormed) (c t) :
    Holds E c t ↔ c ∈ t.classes E :=
  ⟨Holds.classes wf, Ground.classes_holds E t c⟩

end EHMX.TypeClasses
