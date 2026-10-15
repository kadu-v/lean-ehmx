import EHMX.HMX.NormalFormShape


/-! Prepare principal outputs without changing the solved set or success domain.
This is a noncomputable existence construction, not an executable solver. -/

namespace EHMX.HMX.Constraints.ScopedPrincipalNormalizer
open EHMX EHMX.HMX
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}

def PreparedForm (P : X.ScopedPrincipalNormalizer) (u : Names) (d : X.Formula) (n : X.NormalForm) : Prop :=
 n.IsPrincipalOn u P.solved d ∧
 (∀ i, EHMX.HMX.ReconstructionFactor.VariableEffects (n.substitution.types i)) ∧
 n.substitution.effects = Effect.var

noncomputable def prepare (P : X.ScopedPrincipalNormalizer)
 (allow : ∀ (r : X.Formula) (s : HMX.Substitution equalityTypes), s.domain.types = ∅ →
   X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
   X.Admissible P.solved (X.and r (X.substitutionConstraint s))) : X.ScopedPrincipalNormalizer := by
 classical
 let choose (u : Names) (d : X.Formula) : Option X.NormalForm :=
   if h : ∃ n, PreparedForm P u d n then some h.choose else none
 refine ⟨P.solved,P.solved_satisfiable,choose,?_,?_⟩
 · intro u d _ n hn
   dsimp [choose] at hn
   split at hn
   · cases Option.some.inj hn
     exact Exists.choose_spec ‹∃ n, PreparedForm P u d n› |>.1
   · contradiction
 · intro u d scope
   constructor
   · intro hn normal
     obtain ⟨n,run⟩ := P.exists_of_normal scope normal
     obtain ⟨m,hm⟩ := EHMX.HMX.NormalFormShape.principal_shape P.solved_satisfiable allow
       (P.principal u d scope n run)
     have ex : ∃ m, PreparedForm P u d m := ⟨m,hm⟩
     simp [choose,ex] at hn
   · intro noNormal
     have noGood : ¬ ∃ n, PreparedForm P u d n := fun ⟨n,hn⟩ => noNormal ⟨n,hn.1.1⟩
     simp [choose,noGood]

theorem prepare_solved (P : X.ScopedPrincipalNormalizer) (allow) :
 (prepare P allow).solved = P.solved := rfl

theorem prepare_shape (P : X.ScopedPrincipalNormalizer) (allow) (u d n)
 (hn : (prepare P allow).normalize u d = some n) :
 (∀ i, EHMX.HMX.ReconstructionFactor.VariableEffects (n.substitution.types i)) ∧
 n.substitution.effects = Effect.var := by
 classical
 change (if h : ∃ n, PreparedForm P u d n then some h.choose else none) = some n at hn
 split at hn
 · cases Option.some.inj hn
   exact Exists.choose_spec ‹∃ n, PreparedForm P u d n› |>.2
 · contradiction

end EHMX.HMX.Constraints.ScopedPrincipalNormalizer
