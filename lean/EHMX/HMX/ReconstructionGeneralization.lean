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

end EHMX.HMX
