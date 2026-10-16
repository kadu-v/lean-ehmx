import EHMX.HMX.Schemes

namespace EHMX.HMX
variable {T : TypeSyntax}

structure Operation (T : TypeSyntax) where
  bound : Names
  input : T.Term
  output : T.Term

def Operation.Closed (d : Operation T) : Prop :=
  (T.support d.input).types ∪ (T.support d.output).types ⊆ d.bound.types ∧
  (T.support d.input).effects ∪ (T.support d.output).effects ⊆ d.bound.effects

abbrev Signature (T : TypeSyntax) := Op → Option (Operation T)

def Signature.Closed (sig : Signature T) : Prop :=
  ∀ op d, sig op = some d → d.Closed

def Operation.rename (d : Operation T) (f g : Nat → Nat) : Operation T :=
  ⟨⟨d.bound.types.image f, d.bound.effects.image g⟩,
    T.rename f g d.input, T.rename f g d.output⟩

def Operation.FreshInstance (raw d : Operation T) : Prop :=
  ∃ f g, Set.InjOn f raw.bound.types ∧ Set.InjOn g raw.bound.effects ∧
    d = raw.rename f g

/-- Exact free-name computation preserves closed operation signatures under
renaming, for any type syntax, independently of its interpretation. -/
theorem Operation.rename_closed {d : Operation T} (closed : d.Closed) (f g : Nat → Nat) :
    (d.rename f g).Closed := by
  unfold Operation.Closed Operation.rename
  simp only [TypeSyntax.support_rename]
  constructor
  · rw [← Finset.image_union]
    exact Finset.image_subset_image closed.1
  · rw [← Finset.image_union]
    exact Finset.image_subset_image closed.2

theorem Operation.FreshInstance.closed {raw d : Operation T}
    (fresh : raw.FreshInstance d) (closed : raw.Closed) : d.Closed := by
  obtain ⟨f, g, _, _, rfl⟩ := fresh
  exact Operation.rename_closed closed f g

structure Operation.Scoped (d : Operation T) (X : Theory T)
    (c : X.Formula) (g : Context X) (input result : T.Term)
    (ein er rest out : Effect) (witnesses : Names) : Prop where
  context : g.Avoids d.bound
  rigid_types : d.bound.Disjoint ((T.support input).union (T.support result))
  rigid_effects : Disjoint d.bound.effects (ein.vars ∪ er.vars ∪ rest.vars ∪ out.vars)
  witness_scope : witnesses.Disjoint (g.freeNames.union
    (((T.support input).union (T.support result)).union
      (((T.support d.input).union (T.support d.output)).union d.bound)))
  witness_constraint : X.Avoids c witnesses
  witness_effects : Disjoint witnesses.effects (ein.vars ∪ er.vars ∪ rest.vars ∪ out.vars)

/-- Figures 3.1 and 3.4 are separate presentations, independently of S.
`existsIntro` belongs to Figure 3.4. Effects, value restriction and handler
rules are EHMX extensions. Weakening expresses admissibility per rule rather
than assuming closure of S under arbitrary conjunction. -/
inductive Derivation (p : Presentation) (fragment : Fragment) (sig : Signature T) (X : Theory T) :
    X.Formula → Context X → Expr → Scheme X → Effect → Type where
  | var {c g i s} : g.locals[i]? = some s → Derivation p fragment sig X c g (.var i) s ∅
  | const {c g k s} : g.lookupConstant k = some s →
      Derivation p fragment sig X c g (.const k) s ∅
  | lam {c g e a b eff} :
      Derivation p fragment sig X c (g.extend (.mono a)) e (.mono b) eff →
      Derivation p fragment sig X c g (.lam e) (.mono (T.arrow a eff b)) ∅
  | app {c g f x a b ef ex latent} :
      Derivation p fragment sig X c g f (.mono (T.arrow a latent b)) ef →
      Derivation p fragment sig X c g x (.mono a) ex →
      Derivation p fragment sig X c g (.app f x) (.mono b) (ef ∪ ex ∪ latent)
  | letVal {c g v e s t eff} : Value v →
      Derivation p fragment sig X c g v s ∅ →
      Derivation p fragment sig X c (g.extend s) e (.mono t) eff →
      Derivation p fragment sig X c g (.letE v e) (.mono t) eff
  | letMono {c g v e a b ev ee} : ¬ Value v →
      Derivation p fragment sig X c g v (.mono a) ev →
      Derivation p fragment sig X c (g.extend (.mono a)) e (.mono b) ee →
      Derivation p fragment sig X c g (.letE v e) (.mono b) (ev ∪ ee)
  | sub {c g e a b eff} :
      Derivation p fragment sig X c g e (.mono a) eff → X.Entails c (X.le a b) →
      Derivation p fragment sig X c g e (.mono b) eff
  | forallIntro {c d g e a t} : Value e →
      X.Avoids c a → g.Avoids a →
      Derivation p fragment sig X (X.and c d) g e (.mono t) ∅ →
      Derivation p fragment sig X (X.and c (X.existsNames a d)) g e (.qualified a d t) ∅
  | forallElimSubst {c d g e a t eff} (s : Substitution T) :
      p = .term → (X.domain s).Subset a →
      Derivation p fragment sig X c g e (.qualified a d t) eff →
      X.Entails c (X.subst s d) →
      Derivation p fragment sig X c g e (.mono (s.apply t)) eff
  | forallElimConstraint {c d g e a t eff} : p = .constraint →
      Derivation p fragment sig X c g e (.qualified a d t) eff →
      X.Entails c (X.existsNames a d) →
      Derivation p fragment sig X (X.and c d) g e (.mono t) eff
  | existsIntro {c g e a s eff} : p = .constraint →
      g.Avoids a → s.Avoids a → Disjoint a.effects eff.vars →
      Derivation p fragment sig X c g e s eff →
      Derivation p fragment sig X (X.existsNames a c) g e s eff
  | weaken {c d g e s eff} :
      Derivation p fragment sig X c g e s eff → X.Entails d c →
      Derivation p fragment sig X d g e s eff
  | effectEq {c g e s eff eff'} :
      Derivation p fragment sig X c g e s eff → X.Entails c (X.effectEq eff eff') →
      Derivation p fragment sig X c g e s eff'
  | schemeEquivalent {c g e s s' eff} :
      Derivation p fragment sig X c g e s eff → Scheme.Equivalent X s s' →
      Derivation p fragment sig X c g e s' eff
  | contextEquivalent {c g h e s eff} : Context.Equivalent g h →
      Derivation p fragment sig X c g e s eff → Derivation p fragment sig X c h e s eff
  | perform {c g op raw arg eff} (s : Substitution T) :
      fragment = .handlers → sig op = some raw → raw.Closed →
      (X.domain s).Subset raw.bound →
      Derivation p fragment sig X c g arg (.mono (s.apply raw.input)) eff →
      Derivation p fragment sig X c g (.perform op arg) (.mono (s.apply raw.output))
        (Effect.singleton op ∪ eff)
  | handle {c d g body op ret clause raw decl input result clauseTy
      ein er eo rest out witnesses} :
      fragment = .handlers → sig op = some raw → raw.Closed → raw.FreshInstance decl →
      Operation.Scoped decl X c g input result ein er rest out witnesses →
      Derivation p fragment sig X c g body (.mono input) ein →
      Derivation p fragment sig X c (g.extend (.mono input)) ret (.mono result) er →
      Derivation p fragment sig X d
        ((g.extend (.mono decl.input)).extend (.mono (T.arrow decl.output out result)))
        clause (.mono clauseTy) eo →
      X.Entails c (X.clause decl.bound witnesses
        (X.and d (X.and (X.le clauseTy result) (X.effectLe eo out)))) →
      X.Entails c (X.split op ein rest) →
      X.Entails c (X.effectLe rest out) → X.Entails c (X.effectLe er out) →
      Derivation p fragment sig X c g (.handle body op ret clause) (.mono result) out

/-- S-admissibility and presentation restrictions are checked at every node.
The fragment parameter restricts both input and output derivations. -/
def Derivation.Valid {p : Presentation} {fragment : Fragment} {sig : Signature T} {X : Theory T}
    (solved : X.Formula → Prop) {c g e s eff}
    (tree : Derivation p fragment sig X c g e s eff) : Prop :=
  X.Admissible solved c ∧ g.Admissible solved ∧ s.Admissible solved ∧
  g.InPresentation p ∧ s.InPresentation p ∧
    match tree with
    | .var _ | .const _ => True
    | .lam body => body.Valid solved
    | .app f x => f.Valid solved ∧ x.Valid solved
    | .letVal _ v b => v.Valid solved ∧ b.Valid solved
    | .letMono _ v b => v.Valid solved ∧ b.Valid solved
    | .sub body _ => body.Valid solved
    | .forallIntro _ _ _ body => body.Valid solved
    | .forallElimSubst _ _ _ body _ => body.Valid solved
    | .forallElimConstraint _ body _ => body.Valid solved
    | .existsIntro _ _ _ _ body => body.Valid solved
    | .weaken body _ => body.Valid solved
    | .effectEq body _ => body.Valid solved
    | .schemeEquivalent body _ => body.Valid solved
    | .contextEquivalent _ body => body.Valid solved
    | .perform _ _ _ _ _ body => body.Valid solved
    | .handle _ _ _ _ _ body ret clause _ _ _ _ =>
        body.Valid solved ∧ ret.Valid solved ∧ clause.Valid solved

def Typing (p : Presentation) (fragment : Fragment) (sig : Signature T) (X : Theory T)
    (solved : X.Formula → Prop) (c : X.Formula) (g : Context X)
    (e : Expr) (s : Scheme X) (eff : Effect) : Prop :=
  ∃ tree : Derivation p fragment sig X c g e s eff, tree.Valid solved

/-- Closedness of Γ alone does not assert closedness of a judgment. -/
def ClosedJudgment {X : Theory T} (c : X.Formula) (g : Context X)
    (s : Scheme X) (eff : Effect) : Prop :=
  X.freeNames c = Names.empty ∧ g.Closed ∧ s.Closed ∧ eff.vars = ∅

end EHMX.HMX
