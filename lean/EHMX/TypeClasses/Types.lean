import EHMX.HMX.TypeDomain
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi

namespace EHMX.TypeClasses

/-- A finite, ranked signature for first-order data type constructors. -/
structure Constructors where
  count : Nat
  arity : Fin count → Nat

inductive Ty (K : Constructors) where
  | var : Nat → Ty K
  | base : BaseTy → Ty K
  | arr : Ty K → Effect → Ty K → Ty K
  | con (k : Fin K.count) : (Fin (K.arity k) → Ty K) → Ty K

inductive Ground (K : Constructors) where
  | base : BaseTy → Ground K
  | arr : Ground K → Finset Op → Ground K → Ground K
  | con (k : Fin K.count) : (Fin (K.arity k) → Ground K) → Ground K

def Ty.decEq {K} : (a b : Ty K) → Decidable (a = b)
  | .var i, .var j => decidable_of_iff (i = j) (by simp)
  | .base i, .base j => decidable_of_iff (i = j) (by simp)
  | .arr a e c, .arr d f q => by
      letI := Ty.decEq a d
      letI := Ty.decEq c q
      exact decidable_of_iff (a = d ∧ e = f ∧ c = q) (by simp)
  | .con k args, .con l bs => by
      if h : k = l then
        subst l
        letI : ∀ i, Decidable (args i = bs i) := fun i => Ty.decEq (args i) (bs i)
        exact decidable_of_iff (∀ i, args i = bs i) (by simp [funext_iff])
      else exact isFalse (by intro eq; cases eq; exact h rfl)
  | .var _, .base _ => isFalse (by intro h; cases h)
  | .var _, .arr _ _ _ => isFalse (by intro h; cases h)
  | .var _, .con _ _ => isFalse (by intro h; cases h)
  | .base _, .var _ => isFalse (by intro h; cases h)
  | .base _, .arr _ _ _ => isFalse (by intro h; cases h)
  | .base _, .con _ _ => isFalse (by intro h; cases h)
  | .arr _ _ _, .var _ => isFalse (by intro h; cases h)
  | .arr _ _ _, .base _ => isFalse (by intro h; cases h)
  | .arr _ _ _, .con _ _ => isFalse (by intro h; cases h)
  | .con _ _, .var _ => isFalse (by intro h; cases h)
  | .con _ _, .base _ => isFalse (by intro h; cases h)
  | .con _ _, .arr _ _ _ => isFalse (by intro h; cases h)
termination_by structural a _ => a

instance {K} : DecidableEq (Ty K) := Ty.decEq

def Ground.decEq {K} : (a b : Ground K) → Decidable (a = b)
  | .base i, .base j => decidable_of_iff (i = j) (by simp)
  | .arr a e c, .arr d f q => by
      letI := Ground.decEq a d
      letI := Ground.decEq c q
      exact decidable_of_iff (a = d ∧ e = f ∧ c = q) (by simp)
  | .con k args, .con l bs => by
      if h : k = l then
        subst l
        letI : ∀ i, Decidable (args i = bs i) := fun i => Ground.decEq (args i) (bs i)
        exact decidable_of_iff (∀ i, args i = bs i) (by simp [funext_iff])
      else exact isFalse (by intro eq; cases eq; exact h rfl)
  | .base _, .arr _ _ _ => isFalse (by intro h; cases h)
  | .base _, .con _ _ => isFalse (by intro h; cases h)
  | .arr _ _ _, .base _ => isFalse (by intro h; cases h)
  | .arr _ _ _, .con _ _ => isFalse (by intro h; cases h)
  | .con _ _, .base _ => isFalse (by intro h; cases h)
  | .con _ _, .arr _ _ _ => isFalse (by intro h; cases h)
termination_by structural a _ => a

instance {K} : DecidableEq (Ground K) := Ground.decEq

def Ty.rename {K} (f g : Nat → Nat) : Ty K → Ty K
  | .var i => .var (f i)
  | .base b => .base b
  | .arr a e b => .arr (a.rename f g) (e.rename g) (b.rename f g)
  | .con k args => .con k (fun i => (args i).rename f g)

def Ty.subst {K} (f : Nat → Ty K) (g : Nat → Effect) : Ty K → Ty K
  | .var i => f i
  | .base b => .base b
  | .arr a e b => .arr (a.subst f g) (e.subst g) (b.subst f g)
  | .con k args => .con k (fun i => (args i).subst f g)

def Ty.eval {K} (v : HMX.Valuation (Ground K)) : Ty K → Ground K
  | .var i => v.types i
  | .base b => .base b
  | .arr a e b => .arr (a.eval v) (e.eval v.effects) (b.eval v)
  | .con k args => .con k (fun i => (args i).eval v)

def Ty.types {K} : Ty K → Finset Nat
  | .var i => {i}
  | .base _ => ∅
  | .arr a _ b => a.types ∪ b.types
  | .con _ args => Finset.univ.biUnion (fun i => (args i).types)

def Ty.effects {K} : Ty K → Finset Nat
  | .var _ | .base _ => ∅
  | .arr a e b => a.effects ∪ e.vars ∪ b.effects
  | .con _ args => Finset.univ.biUnion (fun i => (args i).effects)

theorem Ty.eval_subst {K} (t : Ty K) (v : HMX.Valuation (Ground K)) f g :
    (t.subst f g).eval v = t.eval ⟨fun i => (f i).eval v, fun i => (g i).eval v.effects⟩ := by
  induction t with
  | var i => rfl
  | base b => rfl
  | arr a e b ha hb => simp [subst, eval, ha, hb, Effect.eval_subst]
  | con k args ih => simp only [subst, eval]; congr; funext i; exact ih i

theorem Ty.eval_rename {K} (t : Ty K) (v : HMX.Valuation (Ground K)) f g :
    (t.rename f g).eval v = t.eval ⟨v.types ∘ f, v.effects ∘ g⟩ := by
  have eff (e : Effect) : (e.rename g).eval v.effects = e.eval (v.effects ∘ g) := by
    ext op
    simp [Effect.eval, Effect.rename, Finset.mem_biUnion, Finset.mem_image]
  induction t with
  | var i => rfl
  | base b => rfl
  | arr a e b ha hb => simp [rename, eval, ha, hb, eff]
  | con k args ih => simp only [rename, eval]; congr; funext i; exact ih i

theorem Ty.eval_support {K} (t : Ty K) (v w : HMX.Valuation (Ground K))
    (ht : ∀ i ∈ t.types, v.types i = w.types i)
    (he : ∀ i ∈ t.effects, v.effects i = w.effects i) : t.eval v = t.eval w := by
  induction t with
  | var i => exact ht i (by simp [types])
  | base b => rfl
  | arr a e b ha hb =>
    simp only [eval]
    congr 1
    · exact ha (fun i hi => ht i (by simp [types, hi]))
        (fun i hi => he i (by simp [effects, hi]))
    · exact Effect.eval_support e _ _ (fun i hi => he i (by simp [effects, hi]))
    · exact hb (fun i hi => ht i (by simp [types, hi]))
        (fun i hi => he i (by simp [effects, hi]))
  | con k args ih =>
    simp only [eval]
    congr; funext j
    exact ih j (fun i hi => ht i (by simp only [types]; exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩))
      (fun i hi => he i (by simp only [effects]; exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩))

theorem Ty.subst_self {K} (t : Ty K) f g
    (ht : ∀ i ∈ t.types, f i = Ty.var i)
    (he : ∀ i ∈ t.effects, g i = Effect.var i) : t.subst f g = t := by
  induction t with
  | var i => exact ht i (by simp [types])
  | base b => rfl
  | arr a e b ha hb =>
    simp only [subst]
    rw [ha (fun i hi => ht i (by simp [types, hi])) (fun i hi => he i (by simp [effects, hi])),
      hb (fun i hi => ht i (by simp [types, hi])) (fun i hi => he i (by simp [effects, hi])),
      e.subst_eq_self g (fun i hi => he i (by simp [effects, hi]))]
  | con k args ih =>
    simp only [subst]
    congr; funext j
    exact ih j (fun i hi => ht i (by simp only [types]; exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩))
      (fun i hi => he i (by simp only [effects]; exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩))

theorem Ty.subst_avoids {K} (t : Ty K) f g (a : HMX.Names)
    (ht : ∀ i ∈ t.types, a.Disjoint ⟨(f i).types, (f i).effects⟩)
    (he : ∀ i ∈ t.effects, Disjoint a.effects (g i).vars) :
    a.Disjoint ⟨(t.subst f g).types, (t.subst f g).effects⟩ := by
  induction t with
  | var i => exact ht i (by simp [types])
  | base b => simp [subst, types, effects, HMX.Names.Disjoint]
  | arr u e v hu hv =>
    have left := hu (fun i hi => ht i (by simp [types, hi]))
      (fun i hi => he i (by simp [effects, hi]))
    have right := hv (fun i hi => ht i (by simp [types, hi]))
      (fun i hi => he i (by simp [effects, hi]))
    have eff : Disjoint a.effects (e.subst g).vars := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hj
      exact Finset.disjoint_left.mp (he j (by simp [effects, hj])) hi hij
    exact ⟨Finset.disjoint_union_right.mpr ⟨left.1, right.1⟩,
      Finset.disjoint_union_right.mpr ⟨Finset.disjoint_union_right.mpr ⟨left.2, eff⟩, right.2⟩⟩
  | con k args ih =>
    have each j := ih j
      (fun i hi => ht i (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩))
      (fun i hi => he i (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩))
    constructor <;> apply Finset.disjoint_left.mpr
    · intro i hi hj
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hj
      exact Finset.disjoint_left.mp (each j).1 hi hj
    · intro i hi hj
      obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hj
      exact Finset.disjoint_left.mp (each j).2 hi hj

abbrev types (K : Constructors) : HMX.TypeDomain where
  Term := Ty K
  Value := Ground K
  value_nonempty := ⟨.base .int⟩
  var := Ty.var
  literal := Ty.base
  arrow := Ty.arr
  groundLiteral := Ground.base
  groundArrow := Ground.arr
  rename := Ty.rename
  subst := Ty.subst
  subst_var := by intros; rfl
  support := fun t => ⟨t.types, t.effects⟩
  support_var := by intros; rfl
  subst_eq_self := fun f g t => t.subst_self f g
  support_subst_avoids := fun f g t a => t.subst_avoids f g a
  eval := Ty.eval
  eval_var := by intros; rfl
  eval_literal := by intros; rfl
  eval_arrow := by intros; rfl
  eval_rename := fun v f g t => t.eval_rename v f g
  eval_subst := fun v f g t => t.eval_subst v f g
  eval_support := fun v w t h => t.eval_support v w h.1 h.2

end EHMX.TypeClasses
