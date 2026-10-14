import EHMX.TypeClasses.Classes

namespace EHMX.TypeClasses

inductive InstanceDecl (K : Constructors) (n : Nat) where
  | base : Fin n → BaseTy → InstanceDecl K n
  | con (c : Fin n) (k : Fin K.count) :
      (Fin (K.arity k) → Finset (Fin n)) → InstanceDecl K n

def InstanceDecl.key {K n} : InstanceDecl K n → Fin n × (BaseTy ⊕ Fin K.count)
  | .base c b => (c, .inl b)
  | .con c k _ => (c, .inr k)

def baseDeclarations {K n} (ds : List (InstanceDecl K n)) : Finset (Fin n × BaseTy) :=
  (ds.filterMap (fun d => match d with | .base c b => some (c, b) | _ => none)).toFinset

def lookupInstance {K n} (c : Fin n) (k : Fin K.count) :
    List (InstanceDecl K n) → Option (Fin (K.arity k) → Finset (Fin n))
  | [] => none
  | .base _ _ :: ds => lookupInstance c k ds
  | .con d l req :: ds =>
    if d = c then
      if h : l = k then some (h ▸ req) else lookupInstance c k ds
    else lookupInstance c k ds

/-- Class indices are topologically ordered (superclasses precede subclasses).
Premise indices and constructor arities are checked by their finite types. -/
structure Declarations (K : Constructors) where
  count : Nat
  supers : Fin count → Finset (Fin count)
  instances : List (InstanceDecl K count)

def Declarations.environment {K} (ds : Declarations K) : ClassEnv K :=
  ⟨ds.count, ds.supers, baseDeclarations ds.instances, fun c k => lookupInstance c k ds.instances⟩

def Declarations.valid {K} (ds : Declarations K) : Bool :=
  decide (ds.instances.map InstanceDecl.key).Nodup && decide ds.environment.WellFormed

def Declarations.check {K} (ds : Declarations K) : Option {e : ClassEnv K // e.WellFormed} :=
  if decide (ds.instances.map InstanceDecl.key).Nodup then ds.environment.checked else none

theorem Declarations.check_iff {K} (ds : Declarations K) :
    ds.check.isSome = true ↔ ds.valid = true := by
  simp only [check, valid, ClassEnv.checked]
  split
  · split <;> simp_all
  · simp_all

theorem Declarations.check_no_overlap {K} (ds : Declarations K) (e)
    (h : ds.check = some e) : (ds.instances.map InstanceDecl.key).Nodup := by
  unfold check at h
  split at h
  · simpa using ‹decide (ds.instances.map InstanceDecl.key).Nodup = true›
  · contradiction

end EHMX.TypeClasses
