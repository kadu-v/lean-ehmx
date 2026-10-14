import EHMX.HMX.Schemes

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

structure Operation (T : TypeDomain) where
  bound : Names
  input : T.Term
  output : T.Term

def Operation.Closed (d : Operation T) : Prop :=
  (T.support d.input).types ∪ (T.support d.output).types ⊆ d.bound.types ∧
  (T.support d.input).effects ∪ (T.support d.output).effects ⊆ d.bound.effects

abbrev Signature (T : TypeDomain) := Op → Option (Operation T)

def Signature.Closed (sig : Signature T) : Prop :=
  ∀ op d, sig op = some d → d.Closed

def Operation.rename (d : Operation T) (f g : Nat → Nat) : Operation T :=
  ⟨⟨d.bound.types.image f, d.bound.effects.image g⟩,
    T.rename f g d.input, T.rename f g d.output⟩

def Operation.FreshInstance (raw d : Operation T) : Prop :=
  ∃ f g, Set.InjOn f raw.bound.types ∧ Set.InjOn g raw.bound.effects ∧
    d = raw.rename f g

def Context.Avoids {X : Constraints T O} (g : Context X) (a : Names) : Prop :=
  ∀ s ∈ g, s.Avoids a

def Context.Admissible {X : Constraints T O} (g : Context X)
    (solved : X.Formula → Prop) : Prop := ∀ s ∈ g, s.Admissible solved

def Constraints.split (X : Constraints T O) (op : Op) (input rest : Effect) : X.Formula :=
  X.and (X.effectLe rest input)
    (X.and (X.effectLe input (Effect.singleton op ∪ rest)) (X.lacks op rest))

structure Operation.Scoped (d : Operation T) (X : Constraints T O)
    (c : X.Formula) (g : Context X) (input result : T.Term)
    (ein er rest out : Effect) (witnesses : Names) : Prop where
  context : g.Avoids d.bound
  rigid_types : d.bound.Disjoint ((T.support input).union (T.support result))
  rigid_effects : Disjoint d.bound.effects (ein.vars ∪ er.vars ∪ rest.vars ∪ out.vars)
  witness_scope : witnesses.Disjoint (g.support.union
    (((T.support input).union (T.support result)).union
      (((T.support d.input).union (T.support d.output)).union d.bound)))
  witness_constraint : X.Avoids c witnesses
  witness_effects : Disjoint witnesses.effects (ein.vars ∪ er.vars ∪ rest.vars ∪ out.vars)

/-- Derivation trees are data so that validity can check constraints at *every*
node, as required in §3.2 of Sulzmann's dissertation.
`forallIntro` has the agreed value restriction. Effects are not subsumed by Sub.
`existsIntro` is an additional projection rule, not a rule of dissertation Figure 3.1;
the dissertation's transformation theorem therefore does not directly cover it.
-/
inductive Derivation (sig : Signature T) (X : Constraints T O) :
    X.Formula → Context X → Expr → Scheme X → Effect → Type where
  | var {c g i s} : g[i]? = some s → Derivation sig X c g (.var i) s ∅
  | int {c g} (n : Int) : Derivation sig X c g (.int n) (.mono (T.literal .int)) ∅
  | bool {c g} (b : Bool) : Derivation sig X c g (.bool b) (.mono (T.literal .bool)) ∅
  | lam {c g e a b eff} :
      Derivation sig X c (.mono a :: g) e (.mono b) eff →
      Derivation sig X c g (.lam e) (.mono (T.arrow a eff b)) ∅
  | app {c g f x a b ef ex latent} :
      Derivation sig X c g f (.mono (T.arrow a latent b)) ef →
      Derivation sig X c g x (.mono a) ex →
      Derivation sig X c g (.app f x) (.mono b) (ef ∪ ex ∪ latent)
  | letVal {c g v e s t eff} : Value v →
      Derivation sig X c g v s ∅ →
      Derivation sig X c (s :: g) e (.mono t) eff →
      Derivation sig X c g (.letE v e) (.mono t) eff
  | letMono {c g v e a b ev ee} : ¬ Value v →
      Derivation sig X c g v (.mono a) ev →
      Derivation sig X c (.mono a :: g) e (.mono b) ee →
      Derivation sig X c g (.letE v e) (.mono b) (ev ∪ ee)
  | sub {c g e a b eff} :
      Derivation sig X c g e (.mono a) eff → X.Entails c (X.le a b) →
      Derivation sig X c g e (.mono b) eff
  | forallIntro {c d g e a t} : Value e →
      X.Avoids c a → g.Avoids a →
      Derivation sig X (X.and c d) g e (.mono t) ∅ →
      Derivation sig X (X.and c (X.existsNames a d)) g e (.qualified a d t) ∅
  | forallElim {c d g e a t eff} (s : Substitution T) :
      s.domain.types ⊆ a.types → s.domain.effects ⊆ a.effects →
      Derivation sig X c g e (.qualified a d t) eff →
      X.Entails c (X.subst s d) →
      Derivation sig X c g e (.mono (s.apply t)) eff
  | existsIntro {c g e a s eff} :
      g.Avoids a → s.Avoids a → Disjoint a.effects eff.vars →
      Derivation sig X c g e s eff →
      Derivation sig X (X.existsNames a c) g e s eff
  | weaken {c d g e s eff} :
      Derivation sig X c g e s eff → X.Entails d c →
      Derivation sig X d g e s eff
  | effectEq {c g e s eff eff'} :
      Derivation sig X c g e s eff → X.Entails c (X.effectEq eff eff') →
      Derivation sig X c g e s eff'
  | alpha {c g e s s' eff} :
      Derivation sig X c g e s eff → Scheme.AlphaEquivalent X s s' →
      Derivation sig X c g e s' eff
  | perform {c g op raw arg eff} (s : Substitution T) :
      sig op = some raw → raw.Closed →
      s.domain.types ⊆ raw.bound.types → s.domain.effects ⊆ raw.bound.effects →
      Derivation sig X c g arg (.mono (s.apply raw.input)) eff →
      Derivation sig X c g (.perform op arg) (.mono (s.apply raw.output))
        (Effect.singleton op ∪ eff)
  | handle {c d g body op ret clause raw decl input result clauseTy
      ein er eo rest out witnesses} :
      sig op = some raw → raw.Closed → raw.FreshInstance decl →
      g.Avoids decl.bound →
      decl.bound.Disjoint ((T.support input).union (T.support result)) →
      Disjoint decl.bound.effects (ein.vars ∪ er.vars ∪ rest.vars ∪ out.vars) →
      witnesses.Disjoint (g.support.union
        (((T.support input).union (T.support result)).union
          (((T.support decl.input).union (T.support decl.output)).union decl.bound))) →
      X.Avoids c witnesses →
      Disjoint witnesses.effects (ein.vars ∪ er.vars ∪ rest.vars ∪ out.vars) →
      Derivation sig X c g body (.mono input) ein →
      Derivation sig X c (.mono input :: g) ret (.mono result) er →
      Derivation sig X d
        (.mono (T.arrow decl.output out result) :: .mono decl.input :: g)
        clause (.mono clauseTy) eo →
      X.Entails c (X.clause decl.bound witnesses
        (X.and d (X.and (X.le clauseTy result) (X.effectLe eo out)))) →
      X.Entails c (X.split op ein rest) →
      X.Entails c (X.effectLe rest out) → X.Entails c (X.effectLe er out) →
      Derivation sig X c g (.handle body op ret clause) (.mono result) out

/-- Each rule application is checked, including assumptions in operation
clauses and qualifiers in contexts. This avoids adding a separate `hTrue`
premise to the final principal-type statement. -/
def Derivation.Valid {sig : Signature T} {X : Constraints T O}
    (solved : X.Formula → Prop) {c g e s eff}
    (tree : Derivation sig X c g e s eff) : Prop :=
  X.Admissible solved c ∧ g.Admissible solved ∧ s.Admissible solved ∧
    match tree with
    | .var _ | .int _ | .bool _ => True
    | .lam body => body.Valid solved
    | .app f x => f.Valid solved ∧ x.Valid solved
    | .letVal _ v b => v.Valid solved ∧ b.Valid solved
    | .letMono _ v b => v.Valid solved ∧ b.Valid solved
    | .sub body _ => body.Valid solved
    | .forallIntro _ _ _ body => body.Valid solved
    | .forallElim _ _ _ body _ => body.Valid solved
    | .existsIntro _ _ _ body => body.Valid solved
    | .weaken body _ => body.Valid solved
    | .effectEq body _ => body.Valid solved
    | .alpha body _ => body.Valid solved
    | .perform _ _ _ _ _ body => body.Valid solved
    | .handle _ _ _ _ _ _ _ _ _ body ret clause _ _ _ _ =>
        body.Valid solved ∧ ret.Valid solved ∧ clause.Valid solved

def Typing (sig : Signature T) (X : Constraints T O) (solved : X.Formula → Prop)
    (c : X.Formula) (g : Context X) (e : Expr) (s : Scheme X) (eff : Effect) : Prop :=
  ∃ tree : Derivation sig X c g e s eff, tree.Valid solved

end EHMX.HMX
