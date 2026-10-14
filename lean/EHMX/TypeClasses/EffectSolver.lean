import EHMX.TypeClasses.Types
import Mathlib.Data.Fintype.Powerset

namespace EHMX.TypeClasses

inductive EffectAtom where
  | le : Effect → Effect → EffectAtom
  | lacks : Op → Effect → EffectAtom
  deriving DecidableEq

def EffectAtom.labels : EffectAtom → Finset Op
  | .le a b => a.labels ∪ b.labels
  | .lacks op a => insert op a.labels

def EffectAtom.vars : EffectAtom → Finset Nat
  | .le a b => a.vars ∪ b.vars
  | .lacks _ a => a.vars

def EffectAtom.Holds (v : Nat → Finset Op) : EffectAtom → Prop
  | .le a b => a.eval v ⊆ b.eval v
  | .lacks op a => op ∉ a.eval v

instance (v a) : Decidable (EffectAtom.Holds v a) := by
  cases a <;> unfold EffectAtom.Holds <;> infer_instance

def effectLabels (cs : List EffectAtom) := cs.toFinset.biUnion EffectAtom.labels
def effectVars (cs : List EffectAtom) := cs.toFinset.biUnion EffectAtom.vars

def finiteEffects (vars labels : Finset Nat) (f : vars → Finset labels) (i : Nat) : Finset Op :=
  if h : i ∈ vars then (f ⟨i, h⟩).image Subtype.val else ∅

def effectSat (cs : List EffectAtom) : Bool :=
  decide (∃ f : effectVars cs → Finset (effectLabels cs),
    ∀ a ∈ cs, a.Holds (finiteEffects (effectVars cs) (effectLabels cs) f))

theorem eval_trim (e : Effect) (labels : Finset Op) (v)
    (hl : e.labels ⊆ labels) :
    e.eval (fun i => v i ∩ labels) = e.eval v ∩ labels := by
  ext op
  simp only [Effect.eval, Finset.mem_union, Finset.mem_biUnion, Finset.mem_inter]
  constructor
  · rintro (h | ⟨i, hi, h, hl⟩)
    · exact ⟨Or.inl h, hl h⟩
    · exact ⟨Or.inr ⟨i, hi, h⟩, hl⟩
  · rintro ⟨h | ⟨i, hi, h⟩, hl⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, h, hl⟩

theorem EffectAtom.holds_trim (a : EffectAtom) (labels : Finset Op) (v)
    (hl : a.labels ⊆ labels) (h : a.Holds v) : a.Holds (fun i => v i ∩ labels) := by
  cases a with
  | le a b =>
    change a.eval _ ⊆ b.eval _
    rw [eval_trim a labels v (fun _ hi => hl (Finset.mem_union_left _ hi)),
      eval_trim b labels v (fun _ hi => hl (Finset.mem_union_right _ hi))]
    exact Finset.inter_subset_inter_right h
  | lacks op a =>
    change op ∉ a.eval _
    rw [eval_trim a labels v (fun _ hi => hl (Finset.mem_insert_of_mem hi))]
    exact fun mem => h (Finset.mem_inter.mp mem).1

theorem EffectAtom.holds_support (a : EffectAtom) (v w)
    (h : ∀ i ∈ a.vars, v i = w i) : a.Holds v ↔ a.Holds w := by
  cases a with
  | le a b =>
    change a.eval v ⊆ b.eval v ↔ a.eval w ⊆ b.eval w
    rw [Effect.eval_support a v w (fun i hi => h i (Finset.mem_union_left _ hi)),
      Effect.eval_support b v w (fun i hi => h i (Finset.mem_union_right _ hi))]
  | lacks op a =>
    change op ∉ a.eval v ↔ op ∉ a.eval w
    rw [Effect.eval_support a v w h]

theorem effectSat_iff (cs) : effectSat cs = true ↔ ∃ v, ∀ a ∈ cs, EffectAtom.Holds v a := by
  simp only [effectSat, decide_eq_true_eq]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨_, hf⟩
  · rintro ⟨v, hv⟩
    let f : effectVars cs → Finset (effectLabels cs) :=
      fun i => Finset.univ.filter (fun op => op.val ∈ v i.val)
    refine ⟨f, ?_⟩
    intro a ha
    have truncated := a.holds_trim (effectLabels cs) v
      (fun _ hx => Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr ha, hx⟩) (hv a ha)
    apply (a.holds_support (fun i => v i ∩ effectLabels cs) _ ?_).mp truncated
    intro i hi
    have mem : i ∈ effectVars cs := Finset.mem_biUnion.mpr ⟨a, List.mem_toFinset.mpr ha, hi⟩
    simp only [finiteEffects, dite_eq_left mem]
    ext op
    simp [f, and_comm]

end EHMX.TypeClasses
