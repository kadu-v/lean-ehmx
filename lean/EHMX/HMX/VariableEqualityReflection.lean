import EHMX.HMX.EffectResiduals


/-! An explicit sufficient condition for residual-relative reconstruction.
Admissible constraints may constrain effects, but may not force a type variable
to equal a syntactically different type term. The effect-only model satisfies it. -/

namespace EHMX.HMX.EffectResidualNormalization
open EHMX EHMX.HMX
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}
def VariableEqualityReflection (S : X.Formula → Prop) : Prop :=
 ∀ c, X.Admissible S c → ∀ i t,
   X.Entails c (X.eq (.var i) t) → t = .var i

theorem effectOnly_reflection :
 VariableEqualityReflection (X := X) (EffectResiduals.Solved X) := by
 intro c hc i t ent
 have only := EffectResiduals.effectOnly_of_admissible hc
 obtain ⟨r, ⟨⟨v,hv⟩,_⟩,_,back⟩ := hc
 have cv := back v hv
 have probe (f : Nat → GroundTy) : equalityTypes.eval ⟨f, v.effects⟩ t = f i := by
   exact ((X.holds_eq _ _ _).mp (ent _ ((only v ⟨f,v.effects⟩ rfl).mp cv))).symm
 cases t with
 | var j =>
   have ij : j = i := GroundTy.atom.inj (probe GroundTy.atom)
   exact congrArg Ty.var ij
 | base b =>
   have bad := probe (fun _ => .arr (.atom 0) ∅ (.atom 0))
   cases b <;> simp [equalityTypes, Ty.eval] at bad
 | arr a e b =>
   have bad := probe (fun _ => .atom 0)
   simp [equalityTypes, Ty.eval] at bad

theorem fixed_type_is_alias {S : X.Formula → Prop}
 (reflect : VariableEqualityReflection (X := X) S)
 {c : X.Formula} (hc : X.Admissible S c)
 {s φ : HMX.Substitution equalityTypes} (hs : s.Solved)
 {f : Finset Nat}
 (fixed : ∀ v, X.holds c v → ∀ i ∈ f,
    (s.pullback (φ.pullback v)).types i = v.types i)
 {i : Nat} (hi : i ∈ s.domain.types) (fi : i ∈ f) :
 ∃ j, j ∉ f ∧ s.types i = Ty.var j := by
 have equal (k : Nat) (hk : k ∈ f) : φ.apply (s.types k) = Ty.var k := by
   apply reflect c hc k
   intro v hv
   apply (X.holds_eq _ _ _).mpr
   rw [HMX.Substitution.eval_apply]
   exact (fixed v hv k hk).symm
 have ei := equal i fi
 cases image : s.types i with
 | var j =>
   refine ⟨j, ?_, rfl⟩
   have outside : j ∉ s.domain.types := by
     have h := (hs.type_range i hi).1
     simpa [image, equalityTypes, Ty.fvTypes] using h
   intro fj
   have ej := equal j fj
   rw [image] at ei
   rw [s.types_outside j outside] at ej
   have ji : j = i := Ty.var.inj (ej.symm.trans ei)
   exact outside (ji ▸ hi)
 | base b => simp [image, HMX.Substitution.apply, equalityTypes, Ty.subst] at ei
 | arr a e b => simp [image, HMX.Substitution.apply, equalityTypes, Ty.subst] at ei
end EHMX.HMX.EffectResidualNormalization
