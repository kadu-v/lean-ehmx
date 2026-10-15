import EHMX.HMX.ReconstructionGeneralization
import EHMX.HMX.VariableEqualityReflection

set_option maxHeartbeats 2000000

/-! Repair a single finite comparison factor under the target constraint.
The repaired type and effect images avoid the freshly quantified names. -/

namespace EHMX.HMX.ReconstructionFactor
open EHMX EHMX.HMX
abbrev T := equalityTypes
inductive VariableEffects : Ty → Prop where
 | var (i) : VariableEffects (.var i)
 | base (b) : VariableEffects (.base b)
 | arr {a b} (ha : VariableEffects a) (i : Nat) (hb : VariableEffects b) :
     VariableEffects (.arr a (Effect.var i) b)
variable {O : TypeOrder T} {X : Constraints T O}
def Represented (c : X.Formula) (φ : HMX.Substitution T) (a b : Ty) : Prop :=
 (∀ i ∈ a.fvTypes, ∃ t : Ty, (T.support t).Subset (T.support b) ∧
    ∀ v, X.holds c v → T.eval v (φ.types i) = T.eval v t) ∧
 (∀ i ∈ a.fvEffects, ∃ e : Effect, e.vars ⊆ b.fvEffects ∧
    ∀ v, X.holds c v → (φ.effects i).eval v.effects = e.eval v.effects)
theorem left_support (a b : Ty) (e : Effect) :
 (T.support a).Subset (T.support (.arr a e b)) := by
 constructor <;> intro i hi <;>
   simp_all [T, equalityTypes, Ty.fvTypes, Ty.fvEffects]
theorem right_support (a b : Ty) (e : Effect) :
 (T.support b).Subset (T.support (.arr a e b)) := by
 constructor <;> intro i hi <;>
   simp_all [T, equalityTypes, Ty.fvTypes, Ty.fvEffects]
theorem represented_mono {c : X.Formula} {φ : HMX.Substitution T} {a b d : Ty}
 (h : Represented c φ a b) (sub : (T.support b).Subset (T.support d)) :
 Represented c φ a d := by
 constructor
 · intro i hi
   obtain ⟨t, ht, eq⟩ := h.1 i hi
   exact ⟨t, ht.trans sub, eq⟩
 · intro i hi
   obtain ⟨e, he, eq⟩ := h.2 i hi
   exact ⟨e, he.trans sub.2, eq⟩
theorem represent_images {c : X.Formula} (sat : X.Satisfiable c)
 (reflect : ∀ i t, X.Entails c (X.eq (.var i) t) → t = .var i) (φ : HMX.Substitution T)
 {a : Ty} (shape : VariableEffects a) (b : Ty)
 (equal : ∀ v, X.holds c v → T.eval (φ.pullback v) a = T.eval v b) :
 Represented c φ a b := by
 induction shape generalizing b with
 | var i =>
   constructor
   · intro j hj
     have ji : j = i := by simpa [Ty.fvTypes] using hj
     subst j
     exact ⟨b, Names.Subset.refl _, fun v hv => equal v hv⟩
   · intro j hj; simp [Ty.fvEffects] at hj
 | base k =>
   constructor
   · intro i hi; simp [Ty.fvTypes] at hi
   · intro i hi; simp [Ty.fvEffects] at hi
 | @arr a z ha i hz iha ihz =>
   cases b with
   | var j =>
     have bad : φ.apply (.arr a (Effect.var i) z) = Ty.var j := by
       apply reflect j
       intro v hv
       apply (X.holds_eq _ _ _).mpr
       rw [HMX.Substitution.eval_apply]
       exact (equal v hv).symm
     simp [HMX.Substitution.apply, equalityTypes, Ty.subst] at bad
   | base k =>
     obtain ⟨v, hv⟩ := sat
     have bad := equal v hv
     cases k <;> simp [T, equalityTypes, Ty.eval] at bad
   | arr x e y =>
     have parts (v : HMX.Valuation GroundTy) (hv : X.holds c v) :
       T.eval (φ.pullback v) a = T.eval v x ∧
       (φ.effects i).eval v.effects = e.eval v.effects ∧
       T.eval (φ.pullback v) z = T.eval v y := by
       have h := equal v hv
       simpa [T, equalityTypes, Ty.eval, HMX.Substitution.pullback, Effect.eval, Effect.var] using h
     have left := represented_mono (iha x (fun v hv => (parts v hv).1)) (left_support x y e)
     have right := represented_mono (ihz y (fun v hv => (parts v hv).2.2)) (right_support x y e)
     constructor
     · intro j hj
       simp only [Ty.fvTypes, Finset.mem_union] at hj
       rcases hj with hj | hj
       · exact left.1 j hj
       · exact right.1 j hj
     · intro j hj
       simp only [Ty.fvEffects, Effect.var, Finset.mem_union, Finset.mem_singleton] at hj
       rcases hj with (hj | rfl) | hj
       · exact left.2 j hj
       · exact ⟨e, fun k hk => by simp [Ty.fvEffects, hk], fun v hv => (parts v hv).2.1⟩
       · exact right.2 j hj
end EHMX.HMX.ReconstructionFactor

namespace EHMX.HMX.ReconstructionFactor
open EHMX EHMX.HMX
variable {O : TypeOrder T} {X : Constraints T O}
theorem assemble {c : X.Formula} (φ : HMX.Substitution T) (u w : Names)
 (ht : ∀ i ∈ u.types, ∃ t : Ty, (T.support t).Subset w ∧
    ∀ v, X.holds c v → T.eval v (φ.types i) = T.eval v t)
 (he : ∀ i ∈ u.effects, ∃ e : Effect, e.vars ⊆ w.effects ∧
    ∀ v, X.holds c v → (φ.effects i).eval v.effects = e.eval v.effects) :
 ∃ ρ : HMX.Substitution T, (ρ.imageSupport u).Subset w ∧
   ∀ v, X.holds c v → ρ.pullback v = φ.pullback v := by
 classical
 let ts (i : Nat) : Ty := if hi : i ∈ u.types then (ht i hi).choose else φ.types i
 let es (i : Nat) : Effect := if hi : i ∈ u.effects then (he i hi).choose else φ.effects i
 let ρ : HMX.Substitution T := {
   domain := u.union φ.domain
   types := ts
   effects := es
   types_outside := by
     intro i hi
     obtain ⟨hu, hd⟩ := Finset.notMem_union.mp hi
     simp [ts, hu, φ.types_outside i hd]
   effects_outside := by
     intro i hi
     obtain ⟨hu, hd⟩ := Finset.notMem_union.mp hi
     simp [es, hu, φ.effects_outside i hd]
 }
 have hts (i) (hi : i ∈ u.types) : (T.support (ρ.types i)).Subset w := by
   simpa [ρ, ts, hi] using (ht i hi).choose_spec.1
 have hes (i) (hi : i ∈ u.effects) : (ρ.effects i).vars ⊆ w.effects := by
   simpa [ρ, es, hi] using (he i hi).choose_spec.1
 refine ⟨ρ, ?_, ?_⟩
 · constructor
   · intro j hj
     obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
     exact (hts i hi).1 hj
   · intro j hj
     rcases Finset.mem_union.mp hj with hj | hj
     · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
       exact (hts i hi).2 hj
     · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
       exact hes i hi hj
 · intro v hv
   apply congrArg₂ HMX.Valuation.mk
   · funext i
     by_cases hi : i ∈ u.types
     · simpa [ρ, HMX.Substitution.pullback, ts, hi] using
         ((ht i hi).choose_spec.2 v hv).symm
     · simp [ρ, HMX.Substitution.pullback, ts, hi]
   · funext i
     by_cases hi : i ∈ u.effects
     · simpa [ρ, HMX.Substitution.pullback, es, hi] using
         ((he i hi).choose_spec.2 v hv).symm
     · simp [ρ, HMX.Substitution.pullback, es, hi]
end EHMX.HMX.ReconstructionFactor

namespace EHMX.HMX.ReconstructionFactor
open EHMX EHMX.HMX
variable {O : TypeOrder T} {X : Constraints T O}
theorem repair_factor {c : X.Formula} (sat : X.Satisfiable c)
 (reflect : ∀ i t, X.Entails c (X.eq (.var i) t) → t = .var i)
 (ψ φ σ : HMX.Substitution T) (u : Names)
 (shape : ∀ i ∈ u.types, VariableEffects (ψ.types i))
 (effects : ∀ i ∈ u.effects, ψ.effects i = Effect.var i)
 (factor : ∀ v, X.holds c v →
   (ψ.pullback (φ.pullback v)).AgreeOn (σ.pullback v) u) :
 ∃ ρ : HMX.Substitution T,
   (ρ.imageSupport (ψ.imageSupport u)).Subset (σ.imageSupport u) ∧
   ∀ v, X.holds c v → ρ.pullback v = φ.pullback v := by
 have typed (i) (hi : i ∈ u.types) :
     Represented c φ (ψ.types i) (σ.types i) :=
   represent_images sat reflect φ (shape i hi) (σ.types i)
     (fun v hv => (factor v hv).1 i hi)
 apply assemble φ (ψ.imageSupport u) (σ.imageSupport u)
 · intro j hj
   obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
   obtain ⟨t, ht, eq⟩ := (typed i hi).1 j hj
   exact ⟨t, ht.trans (σ.imageSupport_type hi), eq⟩
 · intro j hj
   rcases Finset.mem_union.mp hj with hj | hj
   · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
     obtain ⟨e, he, eq⟩ := (typed i hi).2 j hj
     exact ⟨e, he.trans (σ.imageSupport_type hi).2, eq⟩
   · obtain ⟨i, hi, hj⟩ := Finset.mem_biUnion.mp hj
     have ji : j = i := by simpa [effects i hi, Effect.var] using hj
     subst j
     refine ⟨σ.effects i, σ.imageSupport_effect hi, ?_⟩
     intro v hv
     have eq := (factor v hv).2 i hi
     simpa [HMX.Substitution.pullback, effects i hi, Effect.eval, Effect.var] using eq
end EHMX.HMX.ReconstructionFactor

namespace EHMX.HMX.ReconstructionFactor
open EHMX EHMX.HMX
variable {O : TypeOrder T} {X : Constraints T O}
theorem repair_factor_avoids {c : X.Formula} (sat : X.Satisfiable c)
 (reflect : ∀ i t, X.Entails c (X.eq (.var i) t) → t = .var i)
 (ψ φ σ : HMX.Substitution T) (u : Names)
 (shape : ∀ i ∈ u.types, VariableEffects (ψ.types i))
 (effects : ∀ i ∈ u.effects, ψ.effects i = Effect.var i)
 (factor : ∀ v, X.holds c v →
   (ψ.pullback (φ.pullback v)).AgreeOn (σ.pullback v) u)
 (s : Scheme X) (hs : s.support.Subset (ψ.imageSupport u))
 (b : Names) (fresh : b.Disjoint (σ.imageSupport u)) :
 ∃ ρ : HMX.Substitution T, (s.subst ρ).Avoids b ∧
   ∀ v, X.holds c v → ρ.pullback v = φ.pullback v := by
 obtain ⟨ρ, hρ, eq⟩ := repair_factor sat reflect ψ φ σ u shape effects factor
 exact ⟨ρ, s.subst_avoids_imageSupport ρ b
   (fresh.mono_right ((ρ.imageSupport_mono hs).trans hρ)), eq⟩
end EHMX.HMX.ReconstructionFactor
