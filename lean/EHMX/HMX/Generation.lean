import EHMX.HMX.Algorithm
import EHMX.HMX.Normalization

namespace EHMX.HMX
variable {T : TypeSyntax}

/-- Freshness is semantic FV freshness; storage bounds are an allocation
strategy of the implementation, not an extra condition on the relation. -/
def GenerationFresh {X : Theory T} (g : Context X) (i : Nat) (eff : Effect) : Prop :=
  (⟨{i}, eff.vars⟩ : Names).Disjoint g.freeNames

def GenerationLocals {X : Theory T} (g : Context X) (i : Nat) (eff : Effect)
    (a : Names) : Prop := a.Disjoint (g.freeNames.union ⟨{i}, eff.vars⟩)

/-- Figure 4.4 as an inductive relation. `equ` can occur at any stage.
Each recursive child has its own result variable. This relation does not call
`generate` and does not require a particular simplifier. -/
inductive Generates (fragment : Fragment) (sig : Signature T) (X : Theory T) :
    Context X → Expr → Nat → Effect → X.Formula → Type where
  | var {g k s i eff} (avoid : Names) :
      g.locals[k]? = some s → GenerationFresh g i eff →
      (g.support.union ⟨{i}, eff.vars⟩).Subset avoid →
      Generates fragment sig X g (.var k) i eff
        (X.instantiateConstraint X.top s (T.var i) eff avoid)
  | const {g k s i eff} (avoid : Names) :
      g.lookupConstant k = some s → GenerationFresh g i eff →
      (g.support.union ⟨{i}, eff.vars⟩).Subset avoid →
      Generates fragment sig X g (.const k) i eff
        (X.instantiateConstraint X.top s (T.var i) eff avoid)
  | lam {g body i eff a b μ d} :
      GenerationFresh g i eff → a ≠ b →
      GenerationLocals g i eff ⟨{a,b}, {μ}⟩ →
      Generates fragment sig X (g.extend (.mono (T.var a))) body b (Effect.var μ) d →
      Generates fragment sig X g (.lam body) i eff
        (X.existsNames ⟨{a,b}, {μ}⟩
          (X.checked X.top d (T.arrow (T.var a) (Effect.var μ) (T.var b)) (T.var i) ∅ eff))
  | app {g f x i eff a b μ ν ρ df dx} :
      GenerationFresh g i eff → a ≠ b → [μ,ν,ρ].Nodup →
      GenerationLocals g i eff ⟨{a,b}, {μ,ν,ρ}⟩ →
      Generates fragment sig X g f a (Effect.var μ) df →
      Generates fragment sig X g x b (Effect.var ν) dx →
      Generates fragment sig X g (.app f x) i eff
        (X.existsNames ⟨{a,b}, {μ,ν,ρ}⟩ (X.conjunction [X.top, df, dx,
          X.le (T.var a) (T.arrow (T.var b) (Effect.var ρ) (T.var i)),
          X.effectEq (Effect.var μ ∪ Effect.var ν ∪ Effect.var ρ) eff]))
  | letVal {g v body i eff a dv db} :
      Value v → GenerationFresh g i eff → GenerationLocals g i eff ⟨{a}, ∅⟩ →
      Generates fragment sig X g v a ∅ dv →
      Generates fragment sig X (g.extend (.qualified ⟨{a}, ∅⟩ dv (T.var a))) body i eff db →
      Generates fragment sig X g (.letE v body) i eff
        (X.conjunction [X.top, X.existsNames ⟨{a}, ∅⟩ dv, db])
  | letMono {g v body i eff a μ ν dv db} :
      ¬ Value v → GenerationFresh g i eff → μ ≠ ν →
      GenerationLocals g i eff ⟨{a}, {μ,ν}⟩ →
      Generates fragment sig X g v a (Effect.var μ) dv →
      Generates fragment sig X (g.extend (.mono (T.var a))) body i (Effect.var ν) db →
      Generates fragment sig X g (.letE v body) i eff
        (X.existsNames ⟨{a}, {μ,ν}⟩ (X.conjunction [X.top, dv, db,
          X.effectEq (Effect.var μ ∪ Effect.var ν) eff]))
  | perform {g op arg i eff raw decl a μ d} : fragment = .handlers →
      sig op = some raw → raw.Closed → raw.FreshInstance decl →
      GenerationFresh g i eff →
      GenerationLocals g i eff (decl.bound.union ⟨{a}, {μ}⟩) →
      decl.bound.Disjoint ⟨{a}, {μ}⟩ →
      Generates fragment sig X g arg a (Effect.var μ) d →
      Generates fragment sig X g (.perform op arg) i eff
        (X.existsNames (decl.bound.union ⟨{a}, {μ}⟩)
          (X.checked X.top (X.and d (X.le (T.var a) decl.input)) decl.output (T.var i)
            (Effect.singleton op ∪ Effect.var μ) eff))
  | handle {g body op ret clause i out raw decl a b r k μ ν ρ ω db dr dc} :
      fragment = .handlers → sig op = some raw → raw.Closed → raw.FreshInstance decl →
      GenerationFresh g i out → [a,b,r,k].Nodup → [μ,ν,ρ,ω].Nodup →
      GenerationLocals g i out (decl.bound.union ⟨{a,b,r,k}, {μ,ν,ρ,ω}⟩) →
      decl.bound.Disjoint ⟨{a,b,r,k}, {μ,ν,ρ,ω}⟩ →
      Generates fragment sig X g body a (Effect.var μ) db →
      Generates fragment sig X (g.extend (.mono (T.var a))) ret r (Effect.var ν) dr →
      Generates fragment sig X ((g.extend (.mono decl.input)).extend
        (.mono (T.arrow decl.output out (T.var b)))) clause k (Effect.var ω) dc →
      Generates fragment sig X g (.handle body op ret clause) i out
        (X.existsNames ⟨{a,b,r}, {μ,ν,ρ}⟩
          (X.checked X.top (X.handler X.top db dr dc decl op (T.var r) (T.var k)
            (T.var b) (Effect.var μ) (Effect.var ν) (Effect.var ω) (Effect.var ρ) out
            ⟨{k}, {ω}⟩) (T.var b) (T.var i) out out))
  | equ {g e i eff c d} : Generates fragment sig X g e i eff c →
      X.Equivalent c d → Generates fragment sig X g e i eff d

/-- Reconstruction normalizes once, at the boundary. ψ is restricted to FV Γ.
The exported finite map is kept separate from an idempotent substitution:
restriction/composition do not silently inherit an idempotence proof. -/
inductive Reconstructs (fragment : Fragment) (sig : Signature T) (X : Theory T)
    (S : X.Formula → Prop) :
    Context X → Expr → FiniteSubstitution T → X.Formula → T.Term → Effect → Type where
  | finish {g e i eff c n} : Generates fragment sig X g e i eff c →
      Logical.ConstraintProblem.IsPrincipal S (Logical.ConstraintProblem.identityProblem c) n →
      Reconstructs fragment sig X S g e (n.substitution.restrict g.freeNames)
        n.constraint (n.substitution.types i) (eff.subst n.substitution.effects)

end EHMX.HMX
