import SystemFXi.EHMX.GenericFullCompleteness
import SystemFXi.EHMX.Solver

set_option linter.unusedSimpArgs false

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

/-- An interleaved constraint-form simplification policy. Its output must
represent the same valuations as its input. Thus substitutions eliminated
by simplification must be retained in the returned constraint; in particular,
equations about free variables of the environment cannot be discarded.
Principal normal-form computation is a separate `X.PrincipalNormalizer`. -/
structure SequentialNormalizer (X : ConstraintSystem) where
  normalize : X.Formula → X.NormalForm
  reify : X.NormalForm → X.Formula
  normalize_iff : ∀ c v, X.holds (reify (normalize c)) v ↔ X.holds c v

/-- An equivalent simplification policy exists for every X. A concrete
solver can replace this policy with a nontrivial equivalent rewrite. -/
def SequentialNormalizer.identity (X : ConstraintSystem) :
    SequentialNormalizer X where
  normalize c := ⟨c, ⟨Ty.var, Poly.Effect.var⟩⟩
  reify n := n.residual
  normalize_iff _ _ := Iff.rfl

/-- The existing executable simplifier is a nontrivial interleaved policy for
the syntactic constraint system. Its equivalence theorem supplies the only
normalization law used by the generic sequential proof. -/
def SequentialNormalizer.syntax
    (D : Domain) (h : LawfulSupport D) :
    SequentialNormalizer (syntaxConstraintSystem D h) where
  normalize c := ⟨simplifyTotal c,
    ⟨Ty.var, Poly.Effect.var⟩⟩
  reify n := n.residual
  normalize_iff c v := (simplifyTotal_equiv c v).symm

def SequentialNormalizer.constraint {X : ConstraintSystem}
    (N : SequentialNormalizer X) (c : X.Formula) : X.Formula :=
  N.reify (N.normalize c)

theorem SequentialNormalizer.constraint_equivalent
    {X : ConstraintSystem} (N : SequentialNormalizer X)
    (c : X.Formula) : X.Equivalent (N.constraint c) c := by
  constructor
  · intro v h
    exact (N.normalize_iff c v).mp h
  · intro v h
    exact (N.normalize_iff c v).mpr h

theorem SequentialNormalizer.constraint_sound
    {X : ConstraintSystem} (N : SequentialNormalizer X)
    (c : X.Formula) (v : Valuation)
    (h : X.holds (N.constraint c) v) : X.holds c v :=
  (N.normalize_iff c v).mp h

theorem SequentialNormalizer.constraint_complete
    {X : ConstraintSystem} (N : SequentialNormalizer X)
    (c : X.Formula) (v : Valuation)
    (h : X.holds c v) : X.holds (N.constraint c) v :=
  (N.normalize_iff c v).mpr h

/-- The normalizer's substitution may solve a free name in the environment,
but its reified constraint retains that relation at the original valuation. -/
theorem SequentialNormalizer.preserves_environment_equation
    {X : ConstraintSystem} (N : SequentialNormalizer X)
    (c : X.Formula) (a b : Ty) (v : Valuation)
    (heq : X.Entails c (X.equalType a b))
    (h : X.holds (N.constraint c) v) : a.eval v = b.eval v := by
  exact (X.equalType_iff a b v).mp
    (heq v (N.constraint_sound c v h))

def Scheme.replaceCondition {X : ConstraintSystem}
    (σ : Scheme X) (d : X.Formula) : Scheme X :=
  { σ with condition := d }

/-- Replacing a scheme's predicate by an equivalent normalized predicate
preserves all its ground instances, including quantified type/effect names. -/
theorem Scheme.groundInstance_replaceCondition_iff
    {X : ConstraintSystem} (σ : Scheme X) (d : X.Formula)
    (h : X.Equivalent d σ.condition)
    (ρ : Valuation) (t : GroundTy) :
    (σ.replaceCondition d).GroundInstance ρ t ↔
      σ.GroundInstance ρ t := by
  constructor
  · rintro ⟨ft, fe, hft, hfe, hd, ht⟩
    exact ⟨ft, fe, hft, hfe, h.1 ⟨ft, fe⟩ hd, ht⟩
  · rintro ⟨ft, fe, hft, hfe, hc, ht⟩
    exact ⟨ft, fe, hft, hfe, h.2 ⟨ft, fe⟩ hc, ht⟩

theorem Scheme.replaceCondition_moreGeneralAt
    {X : ConstraintSystem} (σ : Scheme X) (d : X.Formula)
    (h : X.Equivalent d σ.condition) (ρ : Valuation) :
    (σ.replaceCondition d).MoreGeneralAt σ ρ ρ ∧
      σ.MoreGeneralAt (σ.replaceCondition d) ρ ρ := by
  constructor
  · intro t ht
    exact (σ.groundInstance_replaceCondition_iff d h ρ t).mpr ht
  · intro t ht
    exact (σ.groundInstance_replaceCondition_iff d h ρ t).mp ht

theorem ConstraintSystem.project_entails
    (X : ConstraintSystem) {c d : X.Formula}
    (bt be : Finset Nat) (h : X.Entails c d) :
    X.Entails (X.project bt be c) (X.project bt be d) := by
  intro v hv
  obtain ⟨ft, fe, hft, hfe, hc⟩ :=
    (X.projection_iff bt be c v).mp hv
  exact (X.projection_iff bt be d v).mpr
    ⟨ft, fe, hft, hfe, h ⟨ft, fe⟩ hc⟩

theorem ConstraintSystem.project_equivalent
    (X : ConstraintSystem) {c d : X.Formula}
    (bt be : Finset Nat) (h : X.Equivalent c d) :
    X.Equivalent (X.project bt be c) (X.project bt be d) :=
  ⟨ConstraintSystem.project_entails X bt be h.1,
    ConstraintSystem.project_entails X bt be h.2⟩

theorem ConstraintSystem.combine_equivalent
    (X : ConstraintSystem) {a b c d : X.Formula}
    (hab : X.Equivalent a b) (hcd : X.Equivalent c d) :
    X.Equivalent (X.combine a c) (X.combine b d) := by
  constructor
  · intro v h
    obtain ⟨ha, hc⟩ := (X.combine_iff a c v).mp h
    exact (X.combine_iff b d v).mpr
      ⟨hab.1 v ha, hcd.1 v hc⟩
  · intro v h
    obtain ⟨hb, hd⟩ := (X.combine_iff b d v).mp h
    exact (X.combine_iff a c v).mpr
      ⟨hab.2 v hb, hcd.2 v hd⟩

theorem ConstraintSystem.equivalent_trans
    (X : ConstraintSystem) {a b c : X.Formula}
    (hab : X.Equivalent a b) (hbc : X.Equivalent b c) :
    X.Equivalent a c :=
  ⟨X.entails_trans hab.1 hbc.1,
    X.entails_trans hbc.2 hab.2⟩

theorem ConstraintSystem.handlerClause_equivalent
    (X : ConstraintSystem) {c d : X.Formula}
    (bt be lt le : Finset Nat) (h : X.Equivalent c d) :
    X.Equivalent
      (X.handlerClause bt be lt le c)
      (X.handlerClause bt be lt le d) :=
  ⟨X.handlerClause_mono bt be lt le h.1,
    X.handlerClause_mono bt be lt le h.2⟩

theorem Scheme.instantiateProjected_replaceCondition_equivalent
    {X : ConstraintSystem} (σ : Scheme X) (d : X.Formula)
    (h : X.Equivalent d σ.condition) (ft fe : Nat → Nat) :
    ((σ.replaceCondition d).instantiateProjected ft fe).1 =
      (σ.instantiateProjected ft fe).1 ∧
    X.Equivalent
      ((σ.replaceCondition d).instantiateProjected ft fe).2
      (σ.instantiateProjected ft fe).2 := by
  constructor
  · rfl
  · apply ConstraintSystem.project_equivalent X σ.typeVars σ.effectVars
    exact ConstraintSystem.combine_equivalent X h
      ⟨X.entails_refl _, X.entails_refl _⟩

theorem handlerCondition_equivalent
    {X : ConstraintSystem} (op : Op) (decl : OpDecl)
    {Cin Cin' Cr Cr' Co Co' : X.Formula}
    (hIn : X.Equivalent Cin Cin')
    (hRet : X.Equivalent Cr Cr')
    (hClause : X.Equivalent Co Co')
    (τr τo a : Ty) (εin εr εo δ χ : Effect)
    (lt le : Finset Nat) :
    X.Equivalent
      (handlerCondition X op decl Cin Cr Co τr τo a
        εin εr εo δ χ lt le)
      (handlerCondition X op decl Cin' Cr' Co' τr τo a
        εin εr εo δ χ lt le) := by
  unfold handlerCondition
  apply ConstraintSystem.combine_equivalent X
  · exact ConstraintSystem.combine_equivalent X hIn hRet
  apply ConstraintSystem.combine_equivalent X
  · exact ⟨X.entails_refl _, X.entails_refl _⟩
  apply ConstraintSystem.combine_equivalent X
  · apply ConstraintSystem.handlerClause_equivalent X
    exact ConstraintSystem.combine_equivalent X hClause
      ⟨X.entails_refl _, X.entails_refl _⟩
  · exact ⟨X.entails_refl _, X.entails_refl _⟩

/-- The first scheme is the declarative shadow used to track the original
generalization boundary; the second is the constraint-form normal form used
for subsequent inference. Both are computed in one structural traversal. -/
abbrev SequentialContext (X : ConstraintSystem) :=
  List (Scheme X × Scheme X)

def SequentialContext.raw {X : ConstraintSystem}
    (Γ : SequentialContext X) : Context X := Γ.map Prod.fst

def SequentialContext.current {X : ConstraintSystem}
    (Γ : SequentialContext X) : Context X := Γ.map Prod.snd

def SequentialContext.initial {X : ConstraintSystem}
    (Γ : Context X) : SequentialContext X := Γ.map (fun σ => (σ, σ))

structure SequentialOutput (X : ConstraintSystem) where
  raw : Output X
  current : Output X

def Scheme.Matches {X : ConstraintSystem}
    (raw current : Scheme X) : Prop :=
  ∃ d, current = raw.replaceCondition d ∧
    X.Equivalent d raw.condition

def SequentialContext.Matches {X : ConstraintSystem}
    (Γ : SequentialContext X) : Prop :=
  ∀ (i : Nat) (p : Scheme X × Scheme X),
    Γ[i]? = some p → p.1.Matches p.2

theorem SequentialContext.initial_matches {X : ConstraintSystem}
    (Γ : Context X) :
    SequentialContext.Matches (SequentialContext.initial Γ) := by
  intro i p hp
  simp only [SequentialContext.initial, List.getElem?_map] at hp
  cases hσ : Γ[i]? with
  | none => simp [hσ] at hp
  | some σ =>
      simp [hσ] at hp
      cases hp
      exact ⟨σ.condition, rfl,
        ⟨X.entails_refl _, X.entails_refl _⟩⟩

theorem SequentialContext.cons_matches {X : ConstraintSystem}
    {Γ : SequentialContext X} {raw current : Scheme X}
    (hhead : raw.Matches current)
    (htail : SequentialContext.Matches Γ) :
    SequentialContext.Matches ((raw, current) :: Γ) := by
  intro i p hp
  cases i with
  | zero =>
      simp at hp
      cases hp
      exact hhead
  | succ j =>
      exact htail j p (by simpa using hp)

def SequentialOutput.Matches {X : ConstraintSystem}
    (r : SequentialOutput X) : Prop :=
  r.raw.ty = r.current.ty ∧
  r.raw.effect = r.current.effect ∧
  r.raw.next = r.current.next ∧
  X.Equivalent r.current.condition r.raw.condition

theorem SequentialOutput.current_typing_of_raw
    {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {e : Expr} {r : SequentialOutput X}
    (h : r.Matches)
    (ht : Typing sig X r.raw.condition Γ e
      r.raw.ty r.raw.effect) :
    Typing sig X r.current.condition Γ e
      r.current.ty r.current.effect := by
  rcases h with ⟨hty, heff, _, hcond⟩
  rw [← hty, ← heff]
  exact Typing.weaken ht hcond.1

/-- Interleaved constraint-form inference. At a value `let`, the normalized
constraint is passed to the bound scheme before the body is inferred. The
raw shadow makes generalization use the same binders as the declarative rule;
it is not consulted to solve the body. -/
def generateSequential (sig : Signature) (X : ConstraintSystem)
    (N : SequentialNormalizer X) (Γ : SequentialContext X) :
    Expr → Supply → Option (SequentialOutput X)
  | .var i, s => do
      let (σraw, σcur) ← Γ[i]?
      let ft := renameBound σraw.typeVars s.types
      let fe := renameBound σraw.effectVars s.effects
      letI : Decidable (σraw.FreshRename ft fe) := by
        dsimp [Scheme.FreshRename]
        infer_instance
      if σraw.FreshRename ft fe then
        let (τraw, Craw) := σraw.instantiateProjected ft fe
        let (τcur, Ccur) := σcur.instantiateProjected ft fe
        let next := s.advance σraw.typeVars σraw.effectVars
        some ⟨⟨τraw, ∅, Craw, next⟩,
          ⟨τcur, ∅, Ccur, next⟩⟩
      else none
  | .int _, s =>
      some ⟨⟨.base .int, ∅, X.trivial, s⟩,
        ⟨.base .int, ∅, X.trivial, s⟩⟩
  | .bool _, s =>
      some ⟨⟨.base .bool, ∅, X.trivial, s⟩,
        ⟨.base .bool, ∅, X.trivial, s⟩⟩
  | .lam body, s => do
      let a := Ty.var s.types
      let r ← generateSequential sig X N
        ((Scheme.mono a, Scheme.mono a) :: Γ) body
        {s with types := s.types + 1}
      some ⟨⟨.arr a r.raw.effect r.raw.ty, ∅,
          r.raw.condition, r.raw.next⟩,
        ⟨.arr a r.current.effect r.current.ty, ∅,
          r.current.condition, r.current.next⟩⟩
  | .app f x, s => do
      let rf ← generateSequential sig X N Γ f s
      let rx ← generateSequential sig X N Γ x rf.raw.next
      let b := Ty.var rx.raw.next.types
      let η := Poly.Effect.var rx.raw.next.effects
      let next : Supply :=
        ⟨rx.raw.next.types + 1, rx.raw.next.effects + 1⟩
      some ⟨⟨b, rf.raw.effect ∪ rx.raw.effect ∪ η,
          X.combine (X.combine rf.raw.condition rx.raw.condition)
            (X.equalType rf.raw.ty (.arr rx.raw.ty η b)), next⟩,
        ⟨b, rf.current.effect ∪ rx.current.effect ∪ η,
          X.combine (X.combine rf.current.condition rx.current.condition)
            (X.equalType rf.current.ty (.arr rx.current.ty η b)), next⟩⟩
  | .letE bound body, s => do
      let r₁ ← generateSequential sig X N Γ bound s
      if bound.isValue then
        let σraw := Scheme.generalize Γ.raw r₁.raw.condition r₁.raw.ty
        let σcur := σraw.replaceCondition
          (N.constraint r₁.current.condition)
        let r₂ ← generateSequential sig X N
          ((σraw, σcur) :: Γ) body r₁.raw.next
        some ⟨⟨r₂.raw.ty, r₂.raw.effect,
            X.combine (Scheme.residual Γ.raw r₁.raw.condition
              r₁.raw.ty) r₂.raw.condition, r₂.raw.next⟩,
          ⟨r₂.current.ty, r₂.current.effect,
            X.combine
              (X.project σraw.typeVars σraw.effectVars
                (N.constraint r₁.current.condition))
              r₂.current.condition, r₂.current.next⟩⟩
      else
        let r₂ ← generateSequential sig X N
          ((Scheme.mono r₁.raw.ty,
            Scheme.mono r₁.current.ty) :: Γ) body r₁.raw.next
        some ⟨⟨r₂.raw.ty, r₁.raw.effect ∪ r₂.raw.effect,
            X.combine r₁.raw.condition r₂.raw.condition,
            r₂.raw.next⟩,
          ⟨r₂.current.ty,
            r₁.current.effect ∪ r₂.current.effect,
            X.combine r₁.current.condition r₂.current.condition,
            r₂.current.next⟩⟩
  | .perform op e, s => do
      let decl ← sig op
      let ft := renameBound decl.typeVars s.types
      let fe := renameBound decl.effectVars s.effects
      let r ← generateSequential sig X N Γ e
        (s.advance decl.typeVars decl.effectVars)
      let out := decl.output.rename ft fe
      let effect := Poly.Effect.singleton op
      some ⟨⟨out, effect ∪ r.raw.effect,
          X.combine r.raw.condition
            (X.equalType r.raw.ty (decl.input.rename ft fe)),
          r.raw.next⟩,
        ⟨out, effect ∪ r.current.effect,
          X.combine r.current.condition
            (X.equalType r.current.ty (decl.input.rename ft fe)),
          r.current.next⟩⟩
  | .handle body op ret clause, s => do
      let raw ← sig op
      let rb ← generateSequential sig X N Γ body s
      let ft := renameBound raw.typeVars rb.raw.next.types
      let fe := renameBound raw.effectVars rb.raw.next.effects
      let decl := raw.alphaRename ft fe
      let sb := rb.raw.next.advance raw.typeVars raw.effectVars
      let a := Ty.var sb.types
      let δ := Poly.Effect.var sb.effects
      let χ := Poly.Effect.var (sb.effects + 1)
      let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
      let rr ← generateSequential sig X N
        ((Scheme.mono rb.raw.ty, Scheme.mono rb.current.ty) :: Γ)
        ret sr
      let rc ← generateSequential sig X N
        ((Scheme.mono (.arr decl.output χ a),
            Scheme.mono (.arr decl.output χ a)) ::
          (Scheme.mono decl.input, Scheme.mono decl.input) :: Γ)
        clause rr.raw.next
      let localTypes :=
        Finset.range rc.raw.next.types \ Finset.range rr.raw.next.types
      let localEffects :=
        Finset.range rc.raw.next.effects \ Finset.range rr.raw.next.effects
      let Craw := handlerCondition X op decl rb.raw.condition
        rr.raw.condition rc.raw.condition rr.raw.ty rc.raw.ty a
        rb.raw.effect rr.raw.effect rc.raw.effect δ χ
        localTypes localEffects
      let Ccur := handlerCondition X op decl rb.current.condition
        rr.current.condition rc.current.condition rr.current.ty
        rc.current.ty a rb.current.effect rr.current.effect
        rc.current.effect δ χ localTypes localEffects
      letI : Decidable
          (Generic.OpDecl.HandlerScope decl Γ.raw rb.raw.ty a
            rb.raw.effect rr.raw.effect δ χ) := by
        dsimp [Generic.OpDecl.HandlerScope]
        infer_instance
      letI : Decidable
          (Generic.OpDecl.ClauseScope decl Γ.raw Craw rb.raw.ty a
            rb.raw.effect rr.raw.effect δ χ localTypes
            localEffects) := by
        dsimp [Generic.OpDecl.ClauseScope]
        infer_instance
      letI : Decidable (raw.AlphaSafe ft fe) := by
        dsimp [OpDecl.AlphaSafe]
        infer_instance
      if raw.AlphaSafe ft fe then
        if Generic.OpDecl.HandlerScope decl Γ.raw rb.raw.ty a
            rb.raw.effect rr.raw.effect δ χ then
          if Generic.OpDecl.ClauseScope decl Γ.raw Craw rb.raw.ty a
              rb.raw.effect rr.raw.effect δ χ localTypes
              localEffects then
            some ⟨⟨a, χ, Craw, rc.raw.next⟩,
              ⟨a, χ, Ccur, rc.current.next⟩⟩
          else none
        else none
      else none

def generateSequentialFresh (sig : Signature) (X : ConstraintSystem)
    (N : SequentialNormalizer X) (Γ : Context X)
    (e : Expr) (s : Supply) : Option (SequentialOutput X) :=
  generateSequential sig X N (SequentialContext.initial Γ) e
    (Supply.seed s sig Γ e)

theorem generateSequential_correct
    {sig : Signature} {X : ConstraintSystem}
    (N : SequentialNormalizer X)
    {Γ : SequentialContext X} {e : Expr} {s : Supply}
    {r : SequentialOutput X}
    (hctx : SequentialContext.Matches Γ)
    (hr : generateSequential sig X N Γ e s = some r) :
    generate sig X Γ.raw e s = some r.raw ∧ r.Matches := by
  induction e generalizing Γ s r with
  | var i =>
      cases hp : Γ[i]? with
      | none => simp [generateSequential, hp] at hr
      | some p =>
          obtain ⟨d, hcur, hequiv⟩ := hctx i p hp
          rcases p with ⟨σraw, σcur⟩
          simp only at hcur
          subst σcur
          let ft := renameBound σraw.typeVars s.types
          let fe := renameBound σraw.effectVars s.effects
          by_cases hf : σraw.FreshRename ft fe
          · simp [generateSequential, hp, ft, fe, hf] at hr
            cases hr
            constructor
            · simp [generate, SequentialContext.raw,
                List.getElem?_map, hp, ft, fe, hf]
            · constructor
              · rfl
              constructor
              · rfl
              constructor
              · rfl
              · exact (σraw.instantiateProjected_replaceCondition_equivalent
                  d hequiv ft fe).2
          · simp [generateSequential, hp, ft, fe, hf] at hr
  | int n =>
      simp [generateSequential] at hr
      cases hr
      exact ⟨by simp [generate, SequentialContext.raw],
        rfl, rfl, rfl,
        ⟨X.entails_refl _, X.entails_refl _⟩⟩
  | bool b =>
      simp [generateSequential] at hr
      cases hr
      exact ⟨by simp [generate, SequentialContext.raw],
        rfl, rfl, rfl,
        ⟨X.entails_refl _, X.entails_refl _⟩⟩
  | lam body ih =>
      let a := Ty.var s.types
      let inner : SequentialContext X :=
        (Scheme.mono a, Scheme.mono a) :: Γ
      let sb : Supply := {s with types := s.types + 1}
      cases hb : generateSequential sig X N inner body sb with
      | none => simp [generateSequential, inner, a, sb, hb] at hr
      | some rb =>
          have hm : SequentialContext.Matches inner := by
            apply SequentialContext.cons_matches
            · exact ⟨X.trivial, rfl,
                ⟨X.entails_refl _, X.entails_refl _⟩⟩
            · exact hctx
          obtain ⟨hraw, hrel⟩ := ih hm hb
          simp [generateSequential, inner, a, sb, hb] at hr
          cases hr
          rcases hrel with ⟨hty, heff, hnext, hcond⟩
          constructor
          · have hraw' : generate sig X
                (Scheme.mono (Ty.var s.types) :: Γ.raw)
                body {s with types := s.types + 1} =
                some rb.raw := by
              simpa only [inner, SequentialContext.raw,
                List.map_cons] using hraw
            simp [generate, hraw']
          · exact ⟨by simp [hty, heff], rfl, hnext, hcond⟩
  | app f x ihf ihx =>
      cases hf : generateSequential sig X N Γ f s with
      | none => simp [generateSequential, hf] at hr
      | some rf =>
          obtain ⟨hrf, hrelf⟩ := ihf hctx hf
          cases hx : generateSequential sig X N Γ x rf.raw.next with
          | none => simp [generateSequential, hf, hx] at hr
          | some rx =>
              obtain ⟨hrx, hrelx⟩ := ihx hctx hx
              simp [generateSequential, hf, hx] at hr
              cases hr
              rcases hrelf with ⟨htf, hef, _, hcf⟩
              rcases hrelx with ⟨htx, hex, hnx, hcx⟩
              constructor
              · simp only [SequentialContext.raw] at hrf hrx ⊢
                simp [generate, hrf, hrx]
              · refine ⟨rfl, ?_, rfl, ?_⟩
                · simp [hef, hex]
                · rw [← htf, ← htx]
                  exact ConstraintSystem.combine_equivalent X
                    (ConstraintSystem.combine_equivalent X
                      hcf hcx)
                    ⟨X.entails_refl _, X.entails_refl _⟩
  | letE bound body ihBound ihBody =>
      cases h₁ : generateSequential sig X N Γ bound s with
      | none => simp [generateSequential, h₁] at hr
      | some r₁ =>
          obtain ⟨hraw₁, hrel₁⟩ := ihBound hctx h₁
          cases hv : bound.isValue with
          | true =>
              let σraw := Scheme.generalize Γ.raw
                r₁.raw.condition r₁.raw.ty
              let d := N.constraint r₁.current.condition
              let σcur := σraw.replaceCondition d
              have hd : X.Equivalent d r₁.raw.condition :=
                ConstraintSystem.equivalent_trans X
                  (N.constraint_equivalent r₁.current.condition)
                  hrel₁.2.2.2
              have hctx' : SequentialContext.Matches
                  ((σraw, σcur) :: Γ) :=
                SequentialContext.cons_matches ⟨d, rfl, hd⟩ hctx
              cases h₂ : generateSequential sig X N
                  ((σraw, σcur) :: Γ) body r₁.raw.next with
              | none =>
                  simp [generateSequential, h₁, hv, σraw,
                    σcur, d, h₂] at hr
              | some r₂ =>
                  obtain ⟨hraw₂, hrel₂⟩ := ihBody hctx' h₂
                  simp [generateSequential, h₁, hv,
                    σraw, σcur, d, h₂] at hr
                  cases hr
                  constructor
                  · simp only [SequentialContext.raw] at hraw₁ hraw₂ ⊢
                    simp only [List.map_cons, Prod.fst] at hraw₂
                    change generate sig X (σraw :: Γ.raw) body
                      r₁.raw.next = some r₂.raw at hraw₂
                    simp only [generate, hraw₁, Option.bind_some,
                      hv, Bool.false_eq_true, ↓reduceIte]
                    change (generate sig X (σraw :: Γ.raw)
                      body r₁.raw.next).bind
                        (fun out => some (Output.mk out.ty out.effect
                          (X.combine
                            (Scheme.residual Γ.raw r₁.raw.condition
                              r₁.raw.ty) out.condition)
                          out.next)) =
                      some (Output.mk r₂.raw.ty r₂.raw.effect
                        (X.combine
                          (Scheme.residual Γ.raw r₁.raw.condition
                            r₁.raw.ty) r₂.raw.condition)
                        r₂.raw.next)
                    rw [hraw₂]
                    rfl
                  · rcases hrel₂ with
                      ⟨hty₂, heff₂, hnext₂, hcond₂⟩
                    refine ⟨hty₂, heff₂, hnext₂, ?_⟩
                    exact ConstraintSystem.combine_equivalent X
                      (ConstraintSystem.project_equivalent X
                        σraw.typeVars σraw.effectVars hd)
                      hcond₂
          | false =>
              let σraw : Scheme X := Scheme.mono r₁.raw.ty
              let σcur : Scheme X := Scheme.mono r₁.current.ty
              have hty₁ := hrel₁.1
              have hctx' : SequentialContext.Matches
                  ((σraw, σcur) :: Γ) := by
                apply SequentialContext.cons_matches
                · have hσ : σraw = σcur := by
                    simp [σraw, σcur, hty₁]
                  rw [← hσ]
                  exact ⟨X.trivial, rfl,
                    ⟨X.entails_refl _, X.entails_refl _⟩⟩
                · exact hctx
              cases h₂ : generateSequential sig X N
                  ((σraw, σcur) :: Γ) body r₁.raw.next with
              | none =>
                  simp [generateSequential, h₁, hv,
                    σraw, σcur, h₂] at hr
              | some r₂ =>
                  obtain ⟨hraw₂, hrel₂⟩ := ihBody hctx' h₂
                  simp [generateSequential, h₁, hv,
                    σraw, σcur, h₂] at hr
                  cases hr
                  constructor
                  · simp only [SequentialContext.raw] at hraw₁ hraw₂ ⊢
                    simp only [List.map_cons, Prod.fst] at hraw₂
                    change generate sig X (σraw :: Γ.raw) body
                      r₁.raw.next = some r₂.raw at hraw₂
                    simp only [generate, hraw₁, hv, ↓reduceIte]
                    change (generate sig X (σraw :: Γ.raw)
                      body r₁.raw.next).bind
                        (fun out => some (Output.mk out.ty
                          (r₁.raw.effect ∪ out.effect)
                          (X.combine r₁.raw.condition out.condition)
                          out.next)) =
                      some (Output.mk r₂.raw.ty
                        (r₁.raw.effect ∪ r₂.raw.effect)
                        (X.combine r₁.raw.condition r₂.raw.condition)
                        r₂.raw.next)
                    rw [hraw₂]
                    rfl
                  · rcases hrel₁ with
                      ⟨hty₁', heff₁, _, hcond₁⟩
                    rcases hrel₂ with
                      ⟨hty₂, heff₂, hnext₂, hcond₂⟩
                    refine ⟨hty₂, ?_, hnext₂, ?_⟩
                    · simp [heff₁, heff₂]
                    · exact ConstraintSystem.combine_equivalent X
                        hcond₁ hcond₂
  | perform op arg ih =>
      cases hd : sig op with
      | none => simp [generateSequential, hd] at hr
      | some decl =>
          let sb := s.advance decl.typeVars decl.effectVars
          cases ha : generateSequential sig X N Γ arg sb with
          | none =>
              simp [generateSequential, hd, sb, ha] at hr
          | some ra =>
              obtain ⟨hraw, hrel⟩ := ih hctx ha
              simp [generateSequential, hd, sb, ha] at hr
              cases hr
              rcases hrel with ⟨hty, heff, hnext, hcond⟩
              constructor
              · simp only [SequentialContext.raw] at hraw ⊢
                simp [generate, hd, sb, hraw]
              · refine ⟨rfl, ?_, hnext, ?_⟩
                · simp [heff]
                · rw [← hty]
                  exact ConstraintSystem.combine_equivalent X
                    hcond ⟨X.entails_refl _, X.entails_refl _⟩
  | handle body op ret clause ihBody ihRet ihClause =>
      cases hd : sig op with
      | none => simp [generateSequential, hd] at hr
      | some raw =>
          cases hb : generateSequential sig X N Γ body s with
          | none => simp [generateSequential, hd, hb] at hr
          | some rb =>
              obtain ⟨hrawB, hrelB⟩ := ihBody hctx hb
              let ft := renameBound raw.typeVars rb.raw.next.types
              let fe := renameBound raw.effectVars rb.raw.next.effects
              let decl := raw.alphaRename ft fe
              let sb := rb.raw.next.advance raw.typeVars raw.effectVars
              let a := Ty.var sb.types
              let δ := Poly.Effect.var sb.effects
              let χ := Poly.Effect.var (sb.effects + 1)
              let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
              let Γr : SequentialContext X :=
                (Scheme.mono rb.raw.ty,
                  Scheme.mono rb.current.ty) :: Γ
              have hΓr : SequentialContext.Matches Γr := by
                apply SequentialContext.cons_matches
                · have heq : rb.raw.ty = rb.current.ty := hrelB.1
                  have hσ : Scheme.mono (X := X) rb.raw.ty =
                      Scheme.mono rb.current.ty := by
                    simp [heq]
                  rw [← hσ]
                  exact ⟨X.trivial, rfl,
                    ⟨X.entails_refl _, X.entails_refl _⟩⟩
                · exact hctx
              cases hrRet : generateSequential sig X N Γr ret sr with
              | none =>
                  simp [generateSequential, hd, hb, Γr,
                    ft, fe, decl, sb, a, δ, χ, sr, hrRet] at hr
              | some rr =>
                  obtain ⟨hrawR, hrelR⟩ := ihRet hΓr hrRet
                  let Γc : SequentialContext X :=
                    (Scheme.mono (.arr decl.output χ a),
                      Scheme.mono (.arr decl.output χ a)) ::
                    (Scheme.mono decl.input,
                      Scheme.mono decl.input) :: Γ
                  have hΓc : SequentialContext.Matches Γc := by
                    apply SequentialContext.cons_matches
                    · exact ⟨X.trivial, rfl,
                        ⟨X.entails_refl _, X.entails_refl _⟩⟩
                    apply SequentialContext.cons_matches
                    · exact ⟨X.trivial, rfl,
                        ⟨X.entails_refl _, X.entails_refl _⟩⟩
                    · exact hctx
                  cases hrClause : generateSequential sig X N Γc
                      clause rr.raw.next with
                  | none =>
                      simp [generateSequential, hd, hb, hrRet,
                        Γr, Γc, ft, fe, decl, sb, a, δ, χ, sr,
                        hrClause] at hr
                  | some rc =>
                      obtain ⟨hrawC, hrelC⟩ :=
                        ihClause hΓc hrClause
                      let lt := Finset.range rc.raw.next.types \
                        Finset.range rr.raw.next.types
                      let le := Finset.range rc.raw.next.effects \
                        Finset.range rr.raw.next.effects
                      let Craw := handlerCondition X op decl
                        rb.raw.condition rr.raw.condition
                        rc.raw.condition rr.raw.ty rc.raw.ty a
                        rb.raw.effect rr.raw.effect rc.raw.effect
                        δ χ lt le
                      let Ccur := handlerCondition X op decl
                        rb.current.condition rr.current.condition
                        rc.current.condition rr.current.ty
                        rc.current.ty a rb.current.effect
                        rr.current.effect rc.current.effect δ χ lt le
                      let scope := Generic.OpDecl.HandlerScope decl
                        Γ.raw rb.raw.ty a rb.raw.effect rr.raw.effect
                        δ χ
                      let clauseScope := Generic.OpDecl.ClauseScope
                        decl Γ.raw Craw rb.raw.ty a rb.raw.effect
                        rr.raw.effect δ χ lt le
                      by_cases hsafe : raw.AlphaSafe ft fe
                      · by_cases hs : scope
                        · by_cases hc : clauseScope
                          · simp [generateSequential, hd, hb,
                              hrRet, hrClause, hsafe, hs, hc,
                              ft, fe, decl, sb, a, δ, χ, sr,
                              Γr, Γc, lt, le, Craw, Ccur,
                              scope, clauseScope] at hr
                            cases hr
                            rcases hrelB with
                              ⟨htB, heB, hnB, hcondB⟩
                            rcases hrelR with
                              ⟨htR, heR, hnR, hcondR⟩
                            rcases hrelC with
                              ⟨htC, heC, hnC, hcondC⟩
                            constructor
                            · have hrawR' : generate sig X
                                  (Scheme.mono rb.raw.ty :: Γ.raw)
                                  ret sr = some rr.raw := by
                                simpa only [Γr,
                                  SequentialContext.raw,
                                  List.map_cons] using hrawR
                              have hrawC' : generate sig X
                                  (Scheme.mono (.arr decl.output χ a) ::
                                    Scheme.mono decl.input :: Γ.raw)
                                  clause rr.raw.next =
                                  some rc.raw := by
                                simpa only [Γc,
                                  SequentialContext.raw,
                                  List.map_cons] using hrawC
                              simp only [SequentialContext.raw] at hrawB hrawR' hrawC' ⊢
                              simp [generate, hd, hrawB,
                                hrawR', hrawC', hsafe,
                                hs, hc, scope, clauseScope,
                                ft, fe, decl, sb, a, δ, χ,
                                sr, lt, le, Craw]
                              exact ⟨hs, hc⟩
                            · refine ⟨rfl, rfl, hnC, ?_⟩
                              rw [← htR, ← htC, ← heB,
                                ← heR, ← heC]
                              exact handlerCondition_equivalent
                                op decl hcondB hcondR hcondC
                                rr.raw.ty rc.raw.ty a
                                rb.raw.effect rr.raw.effect
                                rc.raw.effect δ χ lt le
                          · simp [generateSequential, hd, hb,
                              hrRet, hrClause, hsafe, hs, hc,
                              scope, clauseScope, ft, fe,
                              decl, sb, a, δ, χ, sr,
                              Γr, Γc, lt, le, Craw] at hr
                        · simp [generateSequential, hd, hb,
                            hrRet, hrClause, hsafe, hs,
                            scope, ft, fe, decl, sb, a,
                            δ, χ, sr, Γr, Γc, lt, le] at hr
                      · simp [generateSequential, hd, hb,
                          hrRet, hrClause, hsafe,
                          ft, fe, decl, sb, a, δ, χ, sr,
                          Γr, Γc, lt, le] at hr

/-- The sequential traversal has exactly the same success and failure cases
as the original generator. Normalization is total in constraint form. -/
theorem generateSequential_raw
    {sig : Signature} {X : ConstraintSystem}
    (N : SequentialNormalizer X) (Γ : SequentialContext X)
    (e : Expr) (s : Supply) :
    (generateSequential sig X N Γ e s).map SequentialOutput.raw =
      generate sig X Γ.raw e s := by
  induction e generalizing Γ s with
  | var i =>
      cases hp : Γ[i]? with
      | none => simp [generateSequential, generate,
          SequentialContext.raw, List.getElem?_map, hp]
      | some p =>
          rcases p with ⟨σraw, σcur⟩
          let ft := renameBound σraw.typeVars s.types
          let fe := renameBound σraw.effectVars s.effects
          by_cases hf : σraw.FreshRename ft fe
          · simp [generateSequential, generate,
              SequentialContext.raw, List.getElem?_map,
              hp, ft, fe, hf]
          · simp [generateSequential, generate,
              SequentialContext.raw, List.getElem?_map,
              hp, ft, fe, hf]
  | int n => simp [generateSequential, generate]
  | bool b => simp [generateSequential, generate]
  | lam body ih =>
      let a := Ty.var s.types
      let inner : SequentialContext X :=
        (Scheme.mono a, Scheme.mono a) :: Γ
      let sb : Supply := {s with types := s.types + 1}
      cases hb : generateSequential sig X N inner body sb with
      | none =>
          have hraw := ih inner sb
          rw [hb] at hraw
          simp at hraw
          have hchild : generate sig X
              (Scheme.mono a :: Γ.raw) body sb = none := by
            simpa only [inner, SequentialContext.raw,
              List.map_cons] using hraw.symm
          simp [generateSequential, generate, inner,
            a, sb, hb, hchild]
      | some rb =>
          have hraw := ih inner sb
          rw [hb] at hraw
          simp at hraw
          have hchild : generate sig X
              (Scheme.mono a :: Γ.raw) body sb =
              some rb.raw := by
            simpa only [inner, SequentialContext.raw,
              List.map_cons] using hraw.symm
          simp [generateSequential, generate, inner,
            a, sb, hb, hchild]
  | app f x ihf ihx =>
      cases hf : generateSequential sig X N Γ f s with
      | none =>
          have hrawf := ihf Γ s
          rw [hf] at hrawf
          simp at hrawf
          simp only [SequentialContext.raw] at hrawf ⊢
          simp [generateSequential, generate, hf]
          rw [← hrawf]
          rfl
      | some rf =>
          have hrawf := ihf Γ s
          rw [hf] at hrawf
          simp at hrawf
          cases hx : generateSequential sig X N Γ x rf.raw.next with
          | none =>
              have hrawx := ihx Γ rf.raw.next
              rw [hx] at hrawx
              simp at hrawx
              simp only [SequentialContext.raw] at hrawf hrawx ⊢
              simp [generateSequential, generate, hf, hx]
              rw [← hrawf]
              simp only [Option.bind_some]
              rw [← hrawx]
              rfl
          | some rx =>
              have hrawx := ihx Γ rf.raw.next
              rw [hx] at hrawx
              simp at hrawx
              simp only [SequentialContext.raw] at hrawf hrawx ⊢
              simp [generateSequential, generate, hf, hx]
              rw [← hrawf]
              simp only [Option.bind_some]
              rw [← hrawx]
              rfl
  | letE bound body ihBound ihBody =>
      cases h₁ : generateSequential sig X N Γ bound s with
      | none =>
          have hraw₁ := ihBound Γ s
          rw [h₁] at hraw₁
          simp at hraw₁
          simp only [SequentialContext.raw] at hraw₁ ⊢
          simp [generateSequential, generate, h₁]
          rw [← hraw₁]
          rfl
      | some r₁ =>
          have hraw₁ := ihBound Γ s
          rw [h₁] at hraw₁
          simp at hraw₁
          cases hv : bound.isValue with
          | true =>
              let σraw := Scheme.generalize Γ.raw
                r₁.raw.condition r₁.raw.ty
              let σcur := σraw.replaceCondition
                (N.constraint r₁.current.condition)
              let inner : SequentialContext X :=
                (σraw, σcur) :: Γ
              cases h₂ : generateSequential sig X N inner
                  body r₁.raw.next with
              | none =>
                  have hraw₂ := ihBody inner r₁.raw.next
                  rw [h₂] at hraw₂
                  simp at hraw₂
                  have hchild : generate sig X
                      (σraw :: Γ.raw) body r₁.raw.next =
                      none := by
                    simpa only [inner, SequentialContext.raw,
                      List.map_cons] using hraw₂.symm
                  simp only [SequentialContext.raw] at hraw₁ ⊢
                  simp [generateSequential, generate, h₁, h₂,
                    hraw₁, hchild, hv, σraw, σcur, inner]
                  rw [← hraw₁]
                  simp only [Option.bind_some]
                  change none =
                    (generate sig X (σraw :: Γ.raw) body
                      r₁.raw.next).bind _
                  rw [hchild]
                  rfl
              | some r₂ =>
                  have hraw₂ := ihBody inner r₁.raw.next
                  rw [h₂] at hraw₂
                  simp at hraw₂
                  have hchild : generate sig X
                      (σraw :: Γ.raw) body r₁.raw.next =
                      some r₂.raw := by
                    simpa only [inner, SequentialContext.raw,
                      List.map_cons] using hraw₂.symm
                  simp only [SequentialContext.raw] at hraw₁ ⊢
                  simp [generateSequential, generate, h₁, h₂,
                    hraw₁, hchild, hv, σraw, σcur, inner]
                  rw [← hraw₁]
                  simp only [Option.bind_some]
                  change some _ =
                    (generate sig X (σraw :: Γ.raw) body
                      r₁.raw.next).bind _
                  rw [hchild]
                  rfl
          | false =>
              let inner : SequentialContext X :=
                (Scheme.mono r₁.raw.ty,
                  Scheme.mono r₁.current.ty) :: Γ
              cases h₂ : generateSequential sig X N inner
                  body r₁.raw.next with
              | none =>
                  have hraw₂ := ihBody inner r₁.raw.next
                  rw [h₂] at hraw₂
                  simp at hraw₂
                  have hchild : generate sig X
                      (Scheme.mono r₁.raw.ty :: Γ.raw)
                      body r₁.raw.next = none := by
                    simpa only [inner, SequentialContext.raw,
                      List.map_cons] using hraw₂.symm
                  simp only [SequentialContext.raw] at hraw₁ ⊢
                  simp [generateSequential, generate, h₁, h₂,
                    hraw₁, hchild, hv, inner]
                  rw [← hraw₁]
                  simp only [Option.bind_some]
                  change none =
                    (generate sig X
                      (Scheme.mono r₁.raw.ty :: Γ.raw) body
                      r₁.raw.next).bind _
                  rw [hchild]
                  rfl
              | some r₂ =>
                  have hraw₂ := ihBody inner r₁.raw.next
                  rw [h₂] at hraw₂
                  simp at hraw₂
                  have hchild : generate sig X
                      (Scheme.mono r₁.raw.ty :: Γ.raw)
                      body r₁.raw.next = some r₂.raw := by
                    simpa only [inner, SequentialContext.raw,
                      List.map_cons] using hraw₂.symm
                  simp only [SequentialContext.raw] at hraw₁ ⊢
                  simp [generateSequential, generate, h₁, h₂,
                    hraw₁, hchild, hv, inner]
                  rw [← hraw₁]
                  simp only [Option.bind_some]
                  change some _ =
                    (generate sig X
                      (Scheme.mono r₁.raw.ty :: Γ.raw) body
                      r₁.raw.next).bind _
                  rw [hchild]
                  rfl
  | perform op arg ih =>
      cases hd : sig op with
      | none => simp [generateSequential, generate, hd]
      | some decl =>
          let sb := s.advance decl.typeVars decl.effectVars
          cases ha : generateSequential sig X N Γ arg sb with
          | none =>
              have hraw := ih Γ sb
              rw [ha] at hraw
              simp at hraw
              simp only [SequentialContext.raw] at hraw ⊢
              simp [generateSequential, generate, hd, ha,
                sb]
              rw [← hraw]
              rfl
          | some ra =>
              have hraw := ih Γ sb
              rw [ha] at hraw
              simp at hraw
              simp only [SequentialContext.raw] at hraw ⊢
              simp [generateSequential, generate, hd, ha,
                sb]
              rw [← hraw]
              rfl
  | handle body op ret clause ihBody ihRet ihClause =>
      cases hd : sig op with
      | none => simp [generateSequential, generate, hd]
      | some raw =>
          cases hb : generateSequential sig X N Γ body s with
          | none =>
              have hraw := ihBody Γ s
              rw [hb] at hraw
              simp at hraw
              simp only [SequentialContext.raw] at hraw ⊢
              simp [generateSequential, generate, hd, hb]
              rw [← hraw]
              rfl
          | some rb =>
              have hrawB := ihBody Γ s
              rw [hb] at hrawB
              simp at hrawB
              let ft := renameBound raw.typeVars rb.raw.next.types
              let fe := renameBound raw.effectVars rb.raw.next.effects
              let decl := raw.alphaRename ft fe
              let sb := rb.raw.next.advance raw.typeVars raw.effectVars
              let a := Ty.var sb.types
              let δ := Poly.Effect.var sb.effects
              let χ := Poly.Effect.var (sb.effects + 1)
              let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
              let Γr : SequentialContext X :=
                (Scheme.mono rb.raw.ty,
                  Scheme.mono rb.current.ty) :: Γ
              cases hrRet : generateSequential sig X N Γr ret sr with
              | none =>
                  have hrawR := ihRet Γr sr
                  rw [hrRet] at hrawR
                  simp at hrawR
                  have hchild : generate sig X
                      (Scheme.mono rb.raw.ty :: Γ.raw)
                      ret sr = none := by
                    simpa only [Γr, SequentialContext.raw,
                      List.map_cons] using hrawR.symm
                  simp only [SequentialContext.raw] at hrawB ⊢
                  simp [generateSequential, generate, hd,
                    hb, hrRet]
                  rw [← hrawB]
                  change (generateSequential sig X N Γr ret sr).bind _ =
                    (generate sig X (Scheme.mono rb.raw.ty :: Γ.raw)
                      ret sr).bind _
                  rw [hrRet, hchild]
                  rfl
              | some rr =>
                  have hrawR := ihRet Γr sr
                  rw [hrRet] at hrawR
                  simp at hrawR
                  let Γc : SequentialContext X :=
                    (Scheme.mono (.arr decl.output χ a),
                      Scheme.mono (.arr decl.output χ a)) ::
                    (Scheme.mono decl.input,
                      Scheme.mono decl.input) :: Γ
                  cases hrClause : generateSequential sig X N Γc
                      clause rr.raw.next with
                  | none =>
                      have hrawC := ihClause Γc rr.raw.next
                      rw [hrClause] at hrawC
                      simp at hrawC
                      have hchildR : generate sig X
                          (Scheme.mono rb.raw.ty :: Γ.raw)
                          ret sr = some rr.raw := by
                        simpa only [Γr, SequentialContext.raw,
                          List.map_cons] using hrawR.symm
                      have hchildC : generate sig X
                          (Scheme.mono (.arr decl.output χ a) ::
                            Scheme.mono decl.input :: Γ.raw)
                          clause rr.raw.next = none := by
                        simpa only [Γc, SequentialContext.raw,
                          List.map_cons] using hrawC.symm
                      simp only [SequentialContext.raw] at hrawB ⊢
                      simp [generateSequential, generate, hd,
                        hb, hrRet, hrClause]
                      rw [← hrawB]
                      change (generateSequential sig X N Γr ret sr).bind _ =
                        (generate sig X (Scheme.mono rb.raw.ty :: Γ.raw)
                          ret sr).bind _
                      rw [hrRet, hchildR]
                      change (generateSequential sig X N Γc
                        clause rr.raw.next).bind _ =
                        (generate sig X
                          (Scheme.mono (.arr decl.output χ a) ::
                            Scheme.mono decl.input :: Γ.raw)
                          clause rr.raw.next).bind _
                      rw [hrClause, hchildC]
                      rfl
                  | some rc =>
                      have hrawC := ihClause Γc rr.raw.next
                      rw [hrClause] at hrawC
                      simp at hrawC
                      have hchildR : generate sig X
                          (Scheme.mono rb.raw.ty :: Γ.raw)
                          ret sr = some rr.raw := by
                        simpa only [Γr, SequentialContext.raw,
                          List.map_cons] using hrawR.symm
                      have hchildC : generate sig X
                          (Scheme.mono (.arr decl.output χ a) ::
                            Scheme.mono decl.input :: Γ.raw)
                          clause rr.raw.next = some rc.raw := by
                        simpa only [Γc, SequentialContext.raw,
                          List.map_cons] using hrawC.symm
                      simp only [SequentialContext.raw] at hrawB ⊢
                      simp [generateSequential, generate, hd, hb,
                        hrRet, hrClause]
                      rw [← hrawB]
                      change (generateSequential sig X N Γr ret sr).bind _ =
                        (generate sig X (Scheme.mono rb.raw.ty :: Γ.raw)
                          ret sr).bind _
                      rw [hrRet, hchildR]
                      change (generateSequential sig X N Γc
                        clause rr.raw.next).bind _ =
                        (generate sig X
                          (Scheme.mono (.arr decl.output χ a) ::
                            Scheme.mono decl.input :: Γ.raw)
                          clause rr.raw.next).bind _
                      rw [hrClause, hchildC]
                      simp [Option.map, SequentialContext.raw]
                      by_cases hsafe : raw.AlphaSafe ft fe
                      · by_cases hs : Generic.OpDecl.HandlerScope decl
                          Γ.raw rb.raw.ty a rb.raw.effect rr.raw.effect δ χ
                        · by_cases hc : Generic.OpDecl.ClauseScope decl
                            Γ.raw (handlerCondition X op decl
                              rb.raw.condition rr.raw.condition
                              rc.raw.condition rr.raw.ty rc.raw.ty a
                              rb.raw.effect rr.raw.effect rc.raw.effect
                              δ χ
                              (Finset.range rc.raw.next.types \
                                Finset.range rr.raw.next.types)
                              (Finset.range rc.raw.next.effects \
                                Finset.range rr.raw.next.effects))
                            rb.raw.ty a rb.raw.effect rr.raw.effect δ χ
                            (Finset.range rc.raw.next.types \
                              Finset.range rr.raw.next.types)
                            (Finset.range rc.raw.next.effects \
                              Finset.range rr.raw.next.effects)
                          · simp only [ft, fe, decl, sb, a, δ, χ,
                              SequentialContext.raw] at hs hc
                            simp only [ft, fe] at hsafe
                            simp [hsafe, hs, hc, SequentialOutput.raw]
                          · simp only [ft, fe, decl, sb, a, δ, χ,
                              SequentialContext.raw] at hs hc
                            simp [hs, hc, SequentialOutput.raw]
                        · simp only [ft, fe, decl, sb, a, δ, χ,
                            SequentialContext.raw] at hs
                          simp [hs, SequentialOutput.raw]
                      · simp [ft, fe, hsafe, SequentialOutput.raw]

theorem generateSequentialFresh_raw
    {sig : Signature} {X : ConstraintSystem}
    (N : SequentialNormalizer X) (Γ : Context X)
    (e : Expr) (s : Supply) :
    (generateSequentialFresh sig X N Γ e s).map
      SequentialOutput.raw = generateFresh sig X Γ e s := by
  have hinit : (SequentialContext.initial Γ).raw = Γ := by
    simp [SequentialContext.initial, SequentialContext.raw,
      List.map_map, Function.comp_def]
  simpa [generateSequentialFresh, generateFresh,
    hinit] using
    generateSequential_raw (sig := sig) N
      (SequentialContext.initial Γ) e
      (Supply.seed s sig Γ e)

theorem generateSequentialFresh_correct
    {sig : Signature} {X : ConstraintSystem}
    (N : SequentialNormalizer X) (Γ : Context X)
    (e : Expr) (s : Supply) (r : SequentialOutput X)
    (hr : generateSequentialFresh sig X N Γ e s = some r) :
    generateFresh sig X Γ e s = some r.raw ∧ r.Matches := by
  have hinit : (SequentialContext.initial Γ).raw = Γ := by
    simp [SequentialContext.initial, SequentialContext.raw,
      List.map_map, Function.comp_def]
  simpa [generateSequentialFresh, generateFresh,
    hinit] using
    generateSequential_correct N
      (SequentialContext.initial_matches Γ) hr

theorem SequentialOutput.current_moreGeneralThan_of_raw
    {X : ConstraintSystem} {Γ : Context X}
    {r : SequentialOutput X} {C : X.Formula}
    {τ : Ty} {ε : Effect}
    (hm : r.Matches)
    (hp : r.raw.MoreGeneralThan Γ C τ ε) :
    r.current.MoreGeneralThan Γ C τ ε := by
  intro v hv
  obtain ⟨w, hft, hfe, hc, ht, he⟩ := hp v hv
  rcases hm with ⟨hτ, hε, _, hcond⟩
  refine ⟨w, hft, hfe, hcond.2 w hc, ?_, ?_⟩
  · rw [← hτ]; exact ht
  · rw [← hε]; exact he

/-- Soundness of the interleaved generator. -/
theorem generateSequentialFresh_sound
    {sig : Signature} {X : ConstraintSystem}
    (N : SequentialNormalizer X) (Γ : Context X)
    (e : Expr) (s : Supply) (r : SequentialOutput X)
    (hr : generateSequentialFresh sig X N Γ e s = some r) :
    Typing sig X r.current.condition Γ e
      r.current.ty r.current.effect := by
  obtain ⟨hraw, hm⟩ :=
    generateSequentialFresh_correct N Γ e s r hr
  exact SequentialOutput.current_typing_of_raw hm
    (generateFresh_sound hraw)

/-- Every declarative derivation is represented by the result of the
interleaved generator. -/
theorem Typing.generateSequentialFresh_principal
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed) (N : SequentialNormalizer X)
    (Γ : Context X) (e : Expr) (s : Supply)
    {C₀ : X.Formula} {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀) :
    ∃ r : SequentialOutput X,
      generateSequentialFresh sig X N Γ e s = some r ∧
      Typing sig X r.current.condition Γ e
        r.current.ty r.current.effect ∧
      ∀ (C : X.Formula) (τ : Ty) (ε : Effect),
        Typing sig X C Γ e τ ε →
        r.current.MoreGeneralThan Γ C τ ε := by
  obtain ⟨q, hq, _, hp⟩ :=
    h₀.generateFresh_principal hFV hAtom hClosed Γ e s
  have hmap := generateSequentialFresh_raw (sig := sig) N Γ e s
  rw [hq] at hmap
  cases hs : generateSequentialFresh sig X N Γ e s with
  | none => simp [hs] at hmap
  | some r =>
      simp [hs] at hmap
      cases hmap
      obtain ⟨_, hm⟩ :=
        generateSequentialFresh_correct N Γ e s r hs
      exact ⟨r, rfl,
        generateSequentialFresh_sound N Γ e s r hs,
        fun C τ ε ht =>
          SequentialOutput.current_moreGeneralThan_of_raw hm
            (hp C τ ε ht)⟩

/-- The computation scheme reconstructed from the sequential result is
principal whenever the chosen X supplies its principal normal form. -/
theorem Typing.inferSequential_principal_scheme
    {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (hClosed : sig.Closed)
    (N : SequentialNormalizer X) (M : X.PrincipalNormalizer)
    (hTrue : ∃ R, M.solved R ∧ ∀ v, X.holds R v)
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (s : Supply)
    {C₀ : X.Formula} {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀)
    (v : Valuation) (hv : X.holds C₀ v) :
    ∃ (r : SequentialOutput X) (n : X.NormalForm)
      (σo : X.ComputationScheme),
      generateSequentialFresh sig X N Γ e s = some r ∧
      M.normalize r.current.canonicalCondition = some n ∧
      σo = ComputationScheme.generalize Γ n.residual
        (NormalForm.reconstruct n r.current.canonical).ty
        (NormalForm.reconstruct n r.current.canonical).effect ∧
      ComputationScheme.freeTypes σo = ∅ ∧
      ComputationScheme.freeEffects σo = ∅ ∧
      ComputationSchemeTyping sig X Γ e σo ∧
      (∀ σ' : X.ComputationScheme,
        ComputationSchemeTyping sig X Γ e σ' →
        σo.Subsumes σ') ∧
      ∃ ρ t η, σo.GroundInstance ρ t η := by
  obtain ⟨r, hr, htyping, hmono⟩ :=
    h₀.generateSequentialFresh_principal hFV hAtom hClosed
      N Γ e s
  obtain ⟨w, _, _, hw, _, _⟩ :=
    hmono C₀ τ₀ ε₀ h₀ v hv
  have hcanon : X.holds r.current.canonicalCondition
      (r.current.extendResult w) :=
    r.current.extendResult_solution w hw
  obtain ⟨n, hn⟩ :=
    PrincipalNormalizer.normalize_some_of_solution M hTrue
      r.current.canonicalCondition (r.current.extendResult w)
      hcanon
  obtain ⟨hp, hq⟩ :=
    r.current.normalized_principal_of_mono M hTrue Γ
      hΓClosed e n hmono hn
  let q := NormalForm.reconstruct n r.current.canonical
  let σo := ComputationScheme.generalize Γ n.residual
    q.ty q.effect
  obtain ⟨wr, hwr⟩ :=
    M.solved_satisfiable n.residual hp.1.1
  let u := wr.pullbackSubst n.subst
  have hD : X.holds r.current.canonicalCondition u :=
    hp.1.2 u ⟨wr, hwr, rfl⟩
  have hrawC : X.holds r.current.condition u :=
    (r.current.canonicalCondition_iff u).mp hD |>.1
  have hraw : ComputationSchemeTyping sig X Γ e
      (ComputationScheme.generalize Γ r.current.condition
        r.current.ty r.current.effect) :=
    .generalize htyping
      (Γ.realizableConstraint_of_closed hΓClosed
        r.current.condition ⟨u, hrawC⟩)
  have hrawSub :
      (ComputationScheme.generalize Γ r.current.condition
        r.current.ty r.current.effect).Subsumes σo :=
    r.current.moreGeneralThan_generalize Γ n.residual
      q.ty q.effect
      (NormalForm.raw_moreGeneralThan_reconstruction Γ
        hΓClosed r.current n hp.1.2)
  have hσoReal : ∃ ρ t η, σo.GroundInstance ρ t η := by
    refine ⟨wr, q.ty.eval wr, q.effect.eval wr.effects, ?_⟩
    exact ComputationScheme.generalize_instance_of_solution
      Γ n.residual q.ty q.effect wr wr _ _
      (by intro _ _; rfl) (by intro _ _; rfl)
      hwr rfl rfl
  have hσo : ComputationSchemeTyping sig X Γ e σo :=
    .subsume hraw hrawSub hσoReal
  have hprincipal : ∀ σ' : X.ComputationScheme,
      ComputationSchemeTyping sig X Γ e σ' →
      σo.Subsumes σ' := by
    intro σ' hσ'
    exact hσ'.principal_of_mono Γ e q
      (fun C τ ε h => hq C τ ε h)
  have hclosed := ComputationScheme.generalize_closed Γ
    hΓClosed n.residual q.ty q.effect
  exact ⟨r, n, σo, hr, hn, rfl, hclosed.1, hclosed.2,
    hσo, hprincipal, hσoReal⟩

/-- In the Eq/Show class domain, the sequential generator can use the
verified concrete syntactic simplifier. -/
theorem Typing.classSequentialFresh_principal
    {sig : Signature} (I : ClassEnv)
    (hClosed : sig.Closed)
    (Γ : Context (classConstraintSystem I))
    (e : Expr) (s : Supply)
    {C₀ : (classConstraintSystem I).Formula}
    {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig (classConstraintSystem I)
      C₀ Γ e τ₀ ε₀) :
    ∃ r : SequentialOutput (classConstraintSystem I),
      generateSequentialFresh sig (classConstraintSystem I)
        (SequentialNormalizer.syntax (classDomain I)
          (classDomain_lawfulSupport I)) Γ e s = some r ∧
      Typing sig (classConstraintSystem I)
        r.current.condition Γ e r.current.ty r.current.effect ∧
      ∀ (C : (classConstraintSystem I).Formula)
        (τ : Ty) (ε : Effect),
        Typing sig (classConstraintSystem I) C Γ e τ ε →
        r.current.MoreGeneralThan Γ C τ ε := by
  exact h₀.generateSequentialFresh_principal
    (syntaxSystem_lawfulFV (classDomain I)
      (classDomain_lawfulSupport I))
    (syntaxSystem_lawfulGeneratedFV (classDomain I)
      (classDomain_lawfulSupport I))
    hClosed
    (SequentialNormalizer.syntax (classDomain I)
      (classDomain_lawfulSupport I)) Γ e s

end SystemFXi.EHMX.Generic
