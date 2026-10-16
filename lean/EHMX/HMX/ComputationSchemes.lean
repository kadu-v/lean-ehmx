import EHMX.HMX.Declarative

namespace EHMX.HMX
variable {T : TypeSyntax}

/-- EHMX computation schemes keep the immediate effect separate from value
schemes. This does not relax the value restriction. -/
structure ComputationScheme (X : Theory T) where
  bound : Names
  condition : X.Formula
  result : T.Term
  effect : Effect

def ComputationScheme.valueScheme {X : Theory T} (s : ComputationScheme X) : Scheme X :=
  .qualified s.bound s.condition s.result

def ComputationScheme.outer {X : Theory T} (s : ComputationScheme X) : X.Formula :=
  X.existsNames s.bound s.condition

/-- The existing target-constraint-relative instance condition is retained. -/
def ComputationScheme.FiniteInstance {X : Theory T} (s : ComputationScheme X)
    (c : X.Formula) (t : T.Term) (eff : Effect) : Prop :=
  ∃ θ : Substitution T, (X.domain θ).Subset s.bound ∧
    X.Entails c (X.subst θ s.condition) ∧ X.Entails c (X.le (θ.apply s.result) t) ∧
    X.Entails c (X.effectEq (s.effect.subst θ.effects) eff)

def ComputationTyping (sig : Signature T) (X : Theory T) (S : X.Formula → Prop)
    (c : X.Formula) (g : Context X) (e : Expr) (s : ComputationScheme X) : Prop :=
  g.Avoids s.bound ∧ X.Entails c s.outer ∧
    Typing .term .handlers sig X S s.condition g e (.mono s.result) s.effect

def PrincipalComputationScheme (sig : Signature T) (X : Theory T)
    (S : X.Formula → Prop) (g : Context X) (e : Expr) (s : ComputationScheme X) : Prop :=
  ComputationTyping sig X S X.top g e s ∧
    ∀ c t eff, Typing .term .handlers sig X S c g e (.mono t) eff → s.FiniteInstance c t eff

end EHMX.HMX
