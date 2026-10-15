import EHMX.HMX.ReconstructionFactor
import EHMX.HMX.EffectResidualNormalization

set_option maxHeartbeats 2000000

/-! Construct variable effect annotations and identity effect substitutions
while preserving the residual-relative principal normal form and solved set. -/

namespace EHMX.HMX.NormalFormShape
open EHMX EHMX.HMX EHMX.HMX.ReconstructionFactor
def annotations : Ty → Finset Effect
 | .var _ => ∅
 | .base _ => ∅
 | .arr a e b => (annotations a ∪ {e}) ∪ annotations b
def flatten (k : Effect → Nat) : Ty → Ty
 | .var i => .var i
 | .base b => .base b
 | .arr a e b => .arr (flatten k a) (Effect.var (k e)) (flatten k b)
theorem flatten_shape (k : Effect → Nat) (t : Ty) : VariableEffects (flatten k t) := by
 induction t with
 | var i => exact .var i
 | base b => exact .base b
 | arr a e b ha hb => exact .arr ha _ hb
theorem flatten_types (k : Effect → Nat) (t : Ty) : (flatten k t).fvTypes = t.fvTypes := by
 induction t <;> simp_all [flatten, Ty.fvTypes]
theorem flatten_eval (k : Effect → Nat) (t : Ty) (v w : Valuation GroundTy)
 (ht : v.types = w.types)
 (he : ∀ e ∈ annotations t, v.effects (k e) = e.eval w.effects) :
 equalityTypes.eval v (flatten k t) = equalityTypes.eval w t := by
 induction t with
 | var i => exact congrFun ht i
 | base b => cases b <;> rfl
 | arr a e b ha hb =>
   have ae := ha (fun f hf => he f (by simp [annotations, hf]))
   have be := hb (fun f hf => he f (by simp [annotations, hf]))
   have ee := he e (by simp [annotations])
   simpa [flatten, equalityTypes, Ty.eval, Effect.eval, Effect.var] using
     And.intro ae (And.intro ee be)
-- finite effect names and a simultaneous substitution recovering all annotations
theorem fresh_tags (es : Finset Effect) (avoid : Finset Nat) :
 ∃ (k : Effect → Nat) (δ : HMX.Substitution equalityTypes),
   δ.domain.types = ∅ ∧ δ.types = equalityTypes.var ∧
   Disjoint δ.domain.effects avoid ∧
   (∀ e ∈ es, k e ∈ δ.domain.effects ∧ δ.effects (k e) = e) ∧
   (∀ i ∈ δ.domain.effects, ∃ e ∈ es, δ.effects i = e) := by
 classical
 let f := Fintype.equivFin es
 let offset := avoid.sup id + 1
 let k (e : Effect) := if h : e ∈ es then offset + (f ⟨e,h⟩).val else offset
 have kinj {e d : Effect} (he : e ∈ es) (hd : d ∈ es) (h : k e = k d) : e = d := by
   have h' : (f ⟨e,he⟩).val = (f ⟨d,hd⟩).val := by
     simpa [k, he, hd] using h
   exact congrArg Subtype.val (f.injective (Fin.ext h'))
 have outside (e : Effect) (he : e ∈ es) : k e ∉ avoid := by
   intro hk
   have le : k e ≤ avoid.sup id := Finset.le_sup (f := id) hk
   have ge : offset ≤ k e := by simp [k, he]
   dsimp [offset] at ge
   omega
 let pick (i : Nat) : Effect := if h : ∃ e ∈ es, k e = i then h.choose else Effect.var i
 have recover (e : Effect) (he : e ∈ es) : pick (k e) = e := by
   have h : ∃ d ∈ es, k d = k e := ⟨e,he,rfl⟩
   simp only [pick, dif_pos h]
   exact kinj h.choose_spec.1 he h.choose_spec.2
 let δ : HMX.Substitution equalityTypes := {
   domain := ⟨∅, es.image k⟩
   types := equalityTypes.var
   effects := pick
   types_outside := by intros; rfl
   effects_outside := by
     intro i hi
     have h : ¬∃ e ∈ es, k e = i := by simpa using hi
     simp [pick, h]
 }
 refine ⟨k, δ, rfl, rfl, ?_, ?_, ?_⟩
 · apply Finset.disjoint_left.mpr
   intro i hi ha
   obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
   exact outside e he ha
 · intro e he
   exact ⟨Finset.mem_image.mpr ⟨e,he,rfl⟩, recover e he⟩
 · intro i hi
   obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
   exact ⟨e,he,recover e he⟩
end EHMX.HMX.NormalFormShape

namespace EHMX.HMX.NormalFormShape
open EHMX EHMX.HMX EHMX.HMX.ReconstructionFactor
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
theorem reshape {S : X.Formula → Prop}
 (sound : ∀ r, S r → X.Satisfiable r)
 (allow : ∀ (r : X.Formula) (s : HMX.Substitution equalityTypes), s.domain.types = ∅ →
   X.Admissible S r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
   X.Admissible S (X.and r (X.substitutionConstraint s)))
 {d : X.Formula} {n : X.NormalForm} (u : Names)
 (hn : n.IsNormal S d)
 (hid : n.substitution.effects = Effect.var) :
 ∃ m : X.NormalForm, m.IsNormal S d ∧
   Constraints.NormalForm.MoreGeneralOn u m n ∧
   (∀ i, VariableEffects (m.substitution.types i)) ∧
   m.substitution.effects = Effect.var := by
 classical
 let es := n.substitution.domain.types.biUnion (fun i => annotations (n.substitution.types i))
 let avoid := (u.effects ∪ (X.support n.residual).effects) ∪ es.biUnion Effect.vars
 obtain ⟨k, δ, dt, dtypes, disj, tags, ranges⟩ := fresh_tags es avoid
 have sub_u : u.effects ⊆ avoid := fun i hi => Finset.mem_union_left _ (Finset.mem_union_left _ hi)
 have sub_r : (X.support n.residual).effects ⊆ avoid :=
   fun i hi => Finset.mem_union_left _ (Finset.mem_union_right _ hi)
 have old_res (v : Valuation GroundTy) : X.holds n.residual (δ.pullback v) ↔ X.holds n.residual v := by
   apply X.holds_support
   constructor
   · intro i _
     simp [Substitution.pullback, dtypes, equalityTypes, Ty.eval]
   · intro i hi
     exact (δ.pullback_outside v).2 i
       (fun hd => Finset.disjoint_left.mp disj hd (sub_r hi))
 have solvedδ : δ.Solved := by
   constructor
   · intro i hi; simp [dt] at hi
   · intro i hi
     obtain ⟨e, he, eq⟩ := ranges i hi
     rw [eq]
     exact disj.mono_right (fun j hj => Finset.mem_union_right _
       (Finset.mem_biUnion.mpr ⟨e, he, hj⟩))
 let ψ : HMX.Substitution equalityTypes := {
   domain := ⟨n.substitution.domain.types, ∅⟩
   types := fun i => flatten k (n.substitution.types i)
   effects := Effect.var
   types_outside := by intro i hi; rw [n.substitution.types_outside i hi]; rfl
   effects_outside := by intros; rfl
 }
 have solvedψ : ψ.Solved := by
   constructor
   · intro i hi
     constructor
     · change Disjoint n.substitution.domain.types (flatten k (n.substitution.types i)).fvTypes
       rw [flatten_types]
       exact (hn.2.1.type_range i hi).1
     · simp [ψ]
   · simp [ψ]
 have graph_only : EffectResiduals.EffectOnly X (X.substitutionConstraint δ) := by
   intro v w same
   simp only [X.holds_substitutionConstraint, dt, Finset.notMem_empty, false_implies,
     implies_true, true_and, same]
 let q := X.and n.residual (X.substitutionConstraint δ)
 have sat : X.Satisfiable q := by
   obtain ⟨v, hv⟩ := sound _ hn.1
   exact ⟨δ.pullback v, (X.holds_and _ _ _).mpr
     ⟨(old_res v).mpr hv, X.substitutionConstraint_pullback δ solvedδ.idempotent v⟩⟩
 have invR (v : Valuation GroundTy) : X.holds n.residual (ψ.pullback v) ↔ X.holds n.residual v := by
   apply X.holds_agreeOutside (Constraints.NormalForm.residual_avoids X hn)
   constructor
   · intro i hi
     exact (ψ.pullback_outside v).1 i hi
   · intro i _
     simp [ψ, Substitution.pullback, Effect.eval, Effect.var]
 have invG (v : Valuation GroundTy) :
     X.holds (X.substitutionConstraint δ) (ψ.pullback v) ↔ X.holds (X.substitutionConstraint δ) v :=
   graph_only _ _ (by funext i; simp [ψ, Substitution.pullback, Effect.eval, Effect.var])
 have inv (v : Valuation GroundTy) : X.holds q (ψ.pullback v) ↔ X.holds q v := by
   simp only [q, X.holds_and, invR, invG]
 obtain ⟨r, hr, forward, backward⟩ := allow n.residual δ dt
   ⟨n.residual,hn.1,X.entails_refl _,X.entails_refl _⟩ sat
 let m : X.NormalForm := ⟨r, ψ⟩
 have flat_graph (i : Nat) (v : Valuation GroundTy)
     (hg : X.holds (X.substitutionConstraint δ) v) :
     equalityTypes.eval v (ψ.types i) = equalityTypes.eval v (n.substitution.types i) := by
   apply flatten_eval k _ v v rfl
   intro e he
   have ein : e ∈ es := by
     by_cases hi : i ∈ n.substitution.domain.types
     · exact Finset.mem_biUnion.mpr ⟨i,hi,he⟩
     · rw [n.substitution.types_outside i hi] at he
       simp [equalityTypes, annotations] at he
   have eq := ((X.holds_substitutionConstraint _ _).mp hg).2 (k e) (tags e ein).1
   simpa [(tags e ein).2] using eq
 have normal : m.IsNormal S d := by
   refine ⟨hr, solvedψ, ⟨?_, ?_⟩, ?_⟩
   · intro v hv
     exact forward v ((inv v).mp (backward _ ((X.holds_subst _ _ _).mp hv)))
   · intro v hv
     exact (X.holds_subst _ _ _).mpr (forward _ ((inv v).mpr (backward v hv)))
   · intro v hv
     obtain ⟨hq, hp⟩ := (X.holds_and _ _ _).mp hv
     obtain ⟨hr, hg⟩ := (X.holds_and _ _ _).mp (backward v hq)
     apply hn.2.2.2
     apply (X.holds_and _ _ _).mpr
     refine ⟨hr, (X.holds_substitutionConstraint _ _).mpr ⟨?_, ?_⟩⟩
     · intro i hi
       exact (((X.holds_substitutionConstraint _ _).mp hp).1 i hi).trans (flat_graph i v hg)
     · intro i _
       simp [hid, Effect.eval, Effect.var]
 have flat_pull (i : Nat) (v : Valuation GroundTy) :
     equalityTypes.eval (δ.pullback v) (ψ.types i) = equalityTypes.eval v (n.substitution.types i) := by
   apply flatten_eval k _ _ v
   · funext j; simp [Substitution.pullback, dtypes, equalityTypes, Ty.eval]
   · intro e he
     have ein : e ∈ es := by
       by_cases hi : i ∈ n.substitution.domain.types
       · exact Finset.mem_biUnion.mpr ⟨i,hi,he⟩
       · rw [n.substitution.types_outside i hi] at he
         simp [equalityTypes, annotations] at he
     change (δ.effects (k e)).eval v.effects = e.eval v.effects
     rw [(tags e ein).2]
 refine ⟨m, normal, ⟨δ, ?_⟩, fun i => flatten_shape k _, rfl⟩
 intro v hv
 constructor
 · constructor
   · intro i _; exact flat_pull i v
   · intro i hi
     have outside : i ∉ δ.domain.effects := fun hd => Finset.disjoint_left.mp disj hd (sub_u hi)
     simpa [m, ψ, Substitution.pullback, hid, Effect.eval, Effect.var] using
       (δ.pullback_outside v).2 i outside
 · exact forward _ ((X.holds_and _ _ _).mpr
     ⟨(old_res v).mpr hv, X.substitutionConstraint_pullback δ solvedδ.idempotent v⟩)

theorem principal_shape {S : X.Formula → Prop}
 (sound : ∀ r, S r → X.Satisfiable r)
 (allow : ∀ (r : X.Formula) (s : HMX.Substitution equalityTypes), s.domain.types = ∅ →
   X.Admissible S r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
   X.Admissible S (X.and r (X.substitutionConstraint s)))
 {u : Names} {d : X.Formula} {n : X.NormalForm}
 (hn : n.IsPrincipalOn u S d) :
 ∃ m : X.NormalForm, m.IsPrincipalOn u S d ∧
   (∀ i, EHMX.HMX.ReconstructionFactor.VariableEffects (m.substitution.types i)) ∧
   m.substitution.effects = Effect.var := by
 obtain ⟨p,hp,eqp,_⟩ := EHMX.HMX.EffectResidualNormalization.retain_effect_assignments X sound allow hn
 have pid : p.substitution.effects = Effect.var := by rw [eqp]; rfl
 obtain ⟨m,hm,more,shape,mid⟩ := reshape sound allow u hp.1 pid
 exact ⟨m,⟨hm,fun k hk => Constraints.NormalForm.MoreGeneralOn.trans more (hp.2 k hk)⟩,shape,mid⟩
end EHMX.HMX.NormalFormShape
