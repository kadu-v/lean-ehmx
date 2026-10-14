import EHMX.HMX.ContextSubstitution
import EHMX.HMX.EqualityModel
import EHMX.HMX.OpenCompleteness

/-! Finite supports for generalization after reconstruction. Constraint supports
may be overapproximations; only the images of input environment names are kept. -/
namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

/-- Images of precisely the observed names, rather than the entire substitution. -/
def Substitution.imageSupport (σ : Substitution T) (u : Names) : Names :=
  ⟨u.types.biUnion (fun i => (T.support (σ.types i)).types),
   u.types.biUnion (fun i => (T.support (σ.types i)).effects) ∪
     u.effects.biUnion (fun i => (σ.effects i).vars)⟩

theorem Substitution.imageSupport_mono (σ : Substitution T) {u w : Names}
    (h : u.Subset w) : (σ.imageSupport u).Subset (σ.imageSupport w) := by
  constructor
  · exact Finset.biUnion_subset_biUnion_of_subset_left _ h.1
  · exact Finset.union_subset_union
      (Finset.biUnion_subset_biUnion_of_subset_left _ h.1)
      (Finset.biUnion_subset_biUnion_of_subset_left _ h.2)

theorem Substitution.imageSupport_type (σ : Substitution T) {u : Names}
    {i : Nat} (hi : i ∈ u.types) : (T.support (σ.types i)).Subset (σ.imageSupport u) :=
  ⟨fun _ hj => Finset.mem_biUnion.mpr ⟨i, hi, hj⟩,
   fun _ hj => Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩)⟩

theorem Substitution.imageSupport_effect (σ : Substitution T) {u : Names}
    {i : Nat} (hi : i ∈ u.effects) : (σ.effects i).vars ⊆ (σ.imageSupport u).effects :=
  fun _ hj => Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩)

theorem Scheme.subst_avoids_imageSupport {X : Constraints T O} (s : Scheme X)
    (σ : Substitution T) (a : Names) (fresh : a.Disjoint (σ.imageSupport s.support)) :
    (s.subst σ).Avoids a :=
  s.subst_avoids_of_images σ a
    (fun hi => fresh.mono_right (σ.imageSupport_type hi))
    (fun hi => fresh.2.mono_right (σ.imageSupport_effect hi))

theorem Context.subst_avoids_imageSupport {X : Constraints T O} (g : Context X)
    (σ : Substitution T) (a : Names) (fresh : a.Disjoint (σ.imageSupport g.support)) :
    (g.subst σ).Avoids a := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  apply t.subst_avoids_imageSupport σ a
  apply fresh.mono_right (σ.imageSupport_mono ?_)
  clear fresh hs
  induction g with
  | nil => cases ht
  | cons head tail ih =>
      rcases List.mem_cons.mp ht with rfl | hm
      · exact Names.subset_union_left _ _
      · exact (ih hm).trans (Names.subset_union_right _ _)

/-- Generalization with an explicitly justified environment support. -/
def ComputationScheme.generalizeWithSupport {X : Constraints T O}
    (keep : Names) (c : X.Formula) (t : T.Term) (eff : Effect) : ComputationScheme X :=
  ⟨(((X.support c).union (T.support t)).union ⟨∅, eff.vars⟩).diff keep, c, t, eff⟩

theorem ComputationScheme.generalizeWithSupport_support {X : Constraints T O}
    (keep : Names) (c : X.Formula) (t : T.Term) (eff : Effect) :
    (ComputationScheme.generalizeWithSupport keep c t eff).valueScheme.support.Subset keep := by
  constructor <;> intro i hi <;>
    simp only [ComputationScheme.valueScheme, Scheme.support, generalizeWithSupport,
      Names.diff, Names.union, Finset.mem_sdiff, Finset.mem_union] at hi <;> aesop

theorem ComputationScheme.generalizeWithSupport_avoids {X : Constraints T O}
    (g : Context X) (σ : Substitution T) (c : X.Formula) (t : T.Term) (eff : Effect) :
    (g.subst σ).Avoids
      (ComputationScheme.generalizeWithSupport (σ.imageSupport g.support) c t eff).bound := by
  apply g.subst_avoids_imageSupport σ
  exact ⟨Finset.disjoint_left.mpr fun _ hi hg => (Finset.mem_sdiff.mp hi).2 hg,
    Finset.disjoint_left.mpr fun _ hi hg => (Finset.mem_sdiff.mp hi).2 hg⟩


namespace ReconstructionSupport

theorem effect_vars_of_eval_eq (a b : Effect)
    (equal : ∀ v : Nat → Finset Op, a.eval v = b.eval v) :
    a.vars ⊆ b.vars := by
  intro i hi
  let k := b.labels.sup id + 1
  have hk : k ∉ b.labels := by
    intro h
    have le : b.labels.sup id + 1 ≤ b.labels.sup id := Finset.le_sup (f := id) h
    exact (Nat.not_succ_le_self _) le
  let v : Nat → Finset Op := fun j => if j = i then {k} else ∅
  have member : k ∈ a.eval v := by
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨i, hi, by simp [v]⟩
  rw [equal v] at member
  rcases Finset.mem_union.mp member with hl | hv
  · exact (hk hl).elim
  · obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hv
    have eq : j = i := by
      by_contra hne
      simp [v, hne] at hkj
    simpa only [eq] using hj


/-- The concrete free type algebra does not hide occurrences under evaluation.
No corresponding converse is assumed for arbitrary abstract type domains. -/
theorem type_support_of_eval_eq (a target : Ty)
    (equal : ∀ v : Valuation GroundTy, equalityTypes.eval v a = equalityTypes.eval v target) :
    (equalityTypes.support a).Subset (equalityTypes.support target) := by
  induction a generalizing target with
  | var i =>
      cases target with
      | var j =>
          have ij : i = j := by
            by_contra ne
            have h := equal ⟨Function.update (fun _ => .atom 0) i (.atom 1), fun _ => ∅⟩
            simp [equalityTypes, Ty.eval, Function.update, Ne.symm ne] at h
          subst j
          exact Names.Subset.refl _
      | base b =>
          have h := equal ⟨fun _ => .arr (.atom 0) ∅ (.atom 0), fun _ => ∅⟩
          cases b <;> simp [equalityTypes, Ty.eval] at h
      | arr x e y =>
          have h := equal ⟨fun _ => .atom 0, fun _ => ∅⟩
          simp [equalityTypes, Ty.eval] at h
  | base b => exact ⟨Finset.empty_subset _, Finset.empty_subset _⟩
  | arr a e b iha ihb =>
      cases target with
      | var i =>
          have h := equal ⟨fun _ => .atom 0, fun _ => ∅⟩
          simp [equalityTypes, Ty.eval] at h
      | base k =>
          have h := equal ⟨fun _ => .atom 0, fun _ => ∅⟩
          cases k <;> simp [equalityTypes, Ty.eval] at h
      | arr c f d =>
          have h (v : Valuation GroundTy) := GroundTy.arr.inj (equal v)
          have ha := iha c (fun v => (h v).1)
          have hb := ihb d (fun v => (h v).2.2)
          have he := effect_vars_of_eval_eq e f
            (fun v => (h ⟨fun _ => .atom 0, v⟩).2.1)
          exact ⟨Finset.union_subset_union ha.1 hb.1,
            Finset.union_subset_union (Finset.union_subset_union ha.2 he) hb.2⟩

theorem support_apply (σ : Substitution equalityTypes) (t : Ty) :
    equalityTypes.support (σ.apply t) = σ.imageSupport (equalityTypes.support t) := by
  induction t with
  | var i =>
      simp [Substitution.apply, equalityTypes, Ty.subst, Ty.fvTypes, Ty.fvEffects,
        Substitution.imageSupport]
  | base b =>
      simp [Substitution.apply, equalityTypes, Ty.subst, Ty.fvTypes, Ty.fvEffects,
        Substitution.imageSupport]
  | arr a e b iha ihb =>
      have ht := congrArg Names.types iha
      have he := congrArg Names.effects iha
      have kt := congrArg Names.types ihb
      have ke := congrArg Names.effects ihb
      simp only [Substitution.apply, equalityTypes, Ty.subst] at *
      apply congrArg₂ Names.mk
      · simp only [Ty.fvTypes]
        rw [ht, kt]
        simp [Substitution.imageSupport, Finset.union_biUnion]
      · simp only [Ty.fvEffects]
        rw [he, ke]
        simp [Substitution.imageSupport, Ty.fvTypes, Finset.union_biUnion,
          Effect.subst, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]


theorem imageSupport_compose (φ ψ : Substitution equalityTypes) (u : Names) :
    φ.imageSupport (ψ.imageSupport u) = (φ.compose ψ).imageSupport u := by
  have ht (t : Ty) : (φ.apply t).fvTypes = (φ.imageSupport (equalityTypes.support t)).types :=
    congrArg Names.types (support_apply φ t)
  have he (t : Ty) : (φ.apply t).fvEffects = (φ.imageSupport (equalityTypes.support t)).effects :=
    congrArg Names.effects (support_apply φ t)
  apply congrArg₂ Names.mk
  · simp only [Substitution.imageSupport, Substitution.compose, ht]
    ext j
    simp only [Finset.mem_biUnion]
    aesop
  · simp only [Substitution.imageSupport, Substitution.compose, he, Effect.subst]
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_union]
    aesop

/-- The global comparison factor preserves occurrence bounds on observed input
names. This is where the concrete free type algebra is essential. -/
theorem imageSupport_of_factor {ψ φ σ : Substitution equalityTypes} {u : Names}
    (factor : ∀ v, (ψ.pullback (φ.pullback v)).AgreeOn (σ.pullback v) u) :
    (φ.imageSupport (ψ.imageSupport u)).Subset (σ.imageSupport u) := by
  rw [imageSupport_compose]
  have ht {i} (hi : i ∈ u.types) :
      (equalityTypes.support ((φ.compose ψ).types i)).Subset
        (equalityTypes.support (σ.types i)) := by
    apply type_support_of_eval_eq
    intro v
    change equalityTypes.eval v (φ.apply (ψ.types i)) = equalityTypes.eval v (σ.types i)
    rw [φ.eval_apply]
    exact (factor v).1 i hi
  have he {i} (hi : i ∈ u.effects) :
      ((φ.compose ψ).effects i).vars ⊆ (σ.effects i).vars := by
    apply effect_vars_of_eval_eq
    intro v
    change ((ψ.effects i).subst φ.effects).eval v = (σ.effects i).eval v
    rw [Effect.eval_subst]
    exact (factor ⟨fun _ => .atom 0, v⟩).2 i hi
  constructor
  · intro j hj
    obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
    exact Finset.mem_biUnion.mpr ⟨i, hi, (ht hi).1 hj⟩
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, (ht hi).2 hj⟩)
    · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi, he hi hj⟩)

end ReconstructionSupport


theorem Substitution.imageSupport_bound (σ : Substitution T) (u : Names) :
    (σ.imageSupport u).Subset (u.union σ.range) := by
  constructor
  · intro j hj
    obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
    exact (σ.type_support_subset u hi).1 hj
  · intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
      exact (σ.type_support_subset u hi).2 hj
    · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
      exact σ.effect_support_subset u hi hj

theorem ComputationScheme.generalizeWithSupport_subst_avoids
    {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
    (g : Context X) (ψ φ σ : Substitution equalityTypes)
    (c : X.Formula) (t : Ty) (eff : Effect) (b : Names)
    (factor : ∀ v, (ψ.pullback (φ.pullback v)).AgreeOn (σ.pullback v) g.support)
    (fresh : b.Disjoint (g.support.union σ.range)) :
    ((ComputationScheme.generalizeWithSupport (ψ.imageSupport g.support) c t eff).valueScheme.subst φ).Avoids b := by
  apply Scheme.subst_avoids_imageSupport
  exact fresh.mono_right ((φ.imageSupport_mono
    (ComputationScheme.generalizeWithSupport_support _ _ _ _)).trans
    ((ReconstructionSupport.imageSupport_of_factor factor).trans (σ.imageSupport_bound _)))

end EHMX.HMX
