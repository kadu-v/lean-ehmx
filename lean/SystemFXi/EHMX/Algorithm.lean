import SystemFXi.EHMX.Inference

namespace SystemFXi.EHMX

structure Supply where
  types : Nat
  effects : Nat

structure Output (X : Domain) where
  ty : Ty
  effect : Effect
  constraints : Constraint X
  next : Supply

/-- Only quantified names are renamed. Completeness additionally needs an
initial supply above all names already in the context and signature. -/
def renameBound (bound : Finset Nat) (base : Nat) (i : Nat) : Nat :=
  if i ∈ bound then base + i + 1 else i

theorem renameBound_fixed (bound : Finset Nat) (base : Nat) :
    ∀ i ∉ bound, renameBound bound base i = i := by
  intro i hi
  simp [renameBound, hi]

theorem renameBound_injOn (bound : Finset Nat) (base : Nat) :
    Set.InjOn (renameBound bound base) bound := by
  intro i hi j hj heq
  change i ∈ bound at hi
  change j ∈ bound at hj
  change (if i ∈ bound then base + i + 1 else i) =
    (if j ∈ bound then base + j + 1 else j) at heq
  simp [hi, hj] at heq
  omega

theorem Scheme.renameBound_safe {X : Domain} (σ : Scheme X)
    (typeBase effectBase : Nat)
    (ht : ∀ i ∈ σ.fvTypes ∪ σ.predicates.boundTypes, i ≤ typeBase)
    (he : ∀ i ∈ σ.fvEffects ∪ σ.predicates.boundEffects, i ≤ effectBase) :
    σ.SafeRename (renameBound σ.typeVars typeBase)
      (renameBound σ.effectVars effectBase) := by
  refine ⟨Finset.card_image_of_injOn (renameBound_injOn _ _),
    Finset.card_image_of_injOn (renameBound_injOn _ _), ?_, ?_⟩
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro j hj hused
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    have hle := ht _ hused
    simp [renameBound, hi] at hle
    omega
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro j hj hused
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    have hle := he _ hused
    simp [renameBound, hi] at hle
    omega

theorem OpDecl.renameBound_alphaSafe (decl : OpDecl)
    (typeBase effectBase : Nat)
    (ht : ∀ i ∈ (decl.input.fvTypes ∪ decl.output.fvTypes) \ decl.typeVars,
      i ≤ typeBase)
    (he : ∀ i ∈ (decl.input.fvEffects ∪ decl.output.fvEffects) \
        decl.effectVars, i ≤ effectBase) :
    decl.AlphaSafe (renameBound decl.typeVars typeBase)
      (renameBound decl.effectVars effectBase) := by
  refine ⟨Finset.card_image_of_injOn (renameBound_injOn _ _),
    Finset.card_image_of_injOn (renameBound_injOn _ _), ?_, ?_⟩
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro j hj hused
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    have hle := ht _ hused
    simp [renameBound, hi] at hle
    omega
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro j hj hused
    rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
    have hle := he _ hused
    simp [renameBound, hi] at hle
    omega

def Supply.advance (s : Supply) (types effects : Finset Nat) : Supply :=
  ⟨s.types + types.sup id + 2, s.effects + effects.sup id + 2⟩

theorem Supply.advance_mono (s : Supply) (types effects : Finset Nat) :
    s.types < (s.advance types effects).types ∧
      s.effects < (s.advance types effects).effects := by
  constructor <;> dsimp [Supply.advance] <;> omega

theorem Supply.advance_above_renamed (s : Supply)
    (types effects : Finset Nat) :
    (∀ i ∈ types, renameBound types s.types i <
      (s.advance types effects).types) ∧
    (∀ i ∈ effects, renameBound effects s.effects i <
      (s.advance types effects).effects) := by
  constructor
  · intro i hi
    have hsup : i ≤ types.sup id := Finset.le_sup (f := id) hi
    simp [renameBound, hi, Supply.advance]
    omega
  · intro i hi
    have hsup : i ≤ effects.sup id := Finset.le_sup (f := id) hi
    simp [renameBound, hi, Supply.advance]
    omega

def Scheme.usedTypes {X : Domain} (σ : Scheme X) : Finset Nat :=
  σ.typeVars ∪ σ.result.fvTypes ∪ σ.predicates.fvTypes ∪
    σ.predicates.boundTypes

def Scheme.usedEffects {X : Domain} (σ : Scheme X) : Finset Nat :=
  σ.effectVars ∪ σ.result.fvEffects ∪ σ.predicates.fvEffects ∪
    σ.predicates.boundEffects

def OpDecl.usedTypes (decl : OpDecl) : Finset Nat :=
  decl.typeVars ∪ decl.input.fvTypes ∪ decl.output.fvTypes

def OpDecl.usedEffects (decl : OpDecl) : Finset Nat :=
  decl.effectVars ∪ decl.input.fvEffects ∪ decl.output.fvEffects

def Expr.ops : Expr → Finset Op
  | .var _ | .int _ | .bool _ => ∅
  | .lam body => body.ops
  | .app f x | .letE f x => f.ops ∪ x.ops
  | .perform op e => insert op e.ops
  | .handle body op ret clause =>
      insert op (body.ops ∪ ret.ops ∪ clause.ops)

def Supply.seed {X : Domain} (s : Supply) (sig : Signature)
    (Γ : Context X) (e : Expr) (A : List X.Pred) : Supply :=
  let contextTypes := Γ.foldl (fun names σ => names ∪ σ.usedTypes) ∅
  let contextEffects := Γ.foldl (fun names σ => names ∪ σ.usedEffects) ∅
  let signatureTypes := e.ops.biUnion (fun op =>
    (sig op).elim ∅ OpDecl.usedTypes)
  let signatureEffects := e.ops.biUnion (fun op =>
    (sig op).elim ∅ OpDecl.usedEffects)
  let assumptionTypes := A.foldl (fun names p => names ∪ X.fvTypes p) ∅
  let assumptionEffects := A.foldl (fun names p => names ∪ X.fvEffects p) ∅
  let types := contextTypes ∪ signatureTypes ∪ assumptionTypes
  let effects := contextEffects ∪ signatureEffects ∪ assumptionEffects
  ⟨max s.types (types.sup id + 1), max s.effects (effects.sup id + 1)⟩

theorem Supply.seed_above_inputs {X : Domain} (s : Supply)
    (sig : Signature) (Γ : Context X) (e : Expr) (A : List X.Pred) :
    (∀ i ∈
      (Γ.foldl (fun names σ => names ∪ σ.usedTypes) ∅) ∪
        (e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedTypes)) ∪
        (A.foldl (fun names p => names ∪ X.fvTypes p) ∅),
      i < (s.seed sig Γ e A).types) ∧
    (∀ i ∈
      (Γ.foldl (fun names σ => names ∪ σ.usedEffects) ∅) ∪
        (e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedEffects)) ∪
        (A.foldl (fun names p => names ∪ X.fvEffects p) ∅),
      i < (s.seed sig Γ e A).effects) := by
  constructor
  · intro i hi
    have hsup := Finset.le_sup (f := id) hi
    simp only [id_eq] at hsup
    simp only [Supply.seed]
    omega
  · intro i hi
    have hsup := Finset.le_sup (f := id) hi
    simp only [id_eq] at hsup
    simp only [Supply.seed]
    omega

/-- Executable, syntax-directed constraint generation. It deliberately returns
symbolic effect constraints; it does not choose a least handler effect. -/
def generate (sig : Signature) (X : Domain) (Γ : Context X) :
    Expr → Supply → Option (Output X)
  | .var i, s => do
      let σ ← Γ[i]?
      let ρ := renameBound σ.typeVars s.types
      let η := renameBound σ.effectVars s.effects
      let (τ, C) := σ.instantiate ρ η
      letI : Decidable (σ.SafeRename ρ η) := by
        dsimp [Scheme.SafeRename]
        infer_instance
      if σ.SafeRename ρ η then
        some ⟨τ, ∅, C, s.advance σ.typeVars σ.effectVars⟩
      else none
  | .int _, s => some ⟨.base .int, ∅, .top, s⟩
  | .bool _, s => some ⟨.base .bool, ∅, .top, s⟩
  | .lam body, s => do
      let a := Ty.var s.types
      let r ← generate sig X (Scheme.mono a :: Γ) body
        {s with types := s.types + 1}
      some ⟨.arr a r.effect r.ty, ∅, r.constraints, r.next⟩
  | .app f x, s => do
      let rf ← generate sig X Γ f s
      let rx ← generate sig X Γ x rf.next
      let b := Ty.var rx.next.types
      let η := Poly.Effect.var rx.next.effects
      let C := Constraint.and
        (.and rf.constraints rx.constraints)
        (.typeEq rf.ty (.arr rx.ty η b))
      some ⟨b, rf.effect ∪ rx.effect ∪ η, C,
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩
  | .letE e₁ e₂, s => do
      let r₁ ← generate sig X Γ e₁ s
      if e₁.isValue then
        let σ := Scheme.generalize Γ r₁.constraints r₁.ty
        let r₂ ← generate sig X (σ :: Γ) e₂ r₁.next
        some ⟨r₂.ty, r₂.effect,
          .and (Scheme.residual Γ r₁.constraints r₁.ty) r₂.constraints,
          r₂.next⟩
      else
        let r₂ ← generate sig X (Scheme.mono r₁.ty :: Γ) e₂ r₁.next
        some ⟨r₂.ty, r₁.effect ∪ r₂.effect,
          .and r₁.constraints r₂.constraints, r₂.next⟩
  | .perform op e, s => do
      let decl ← sig op
      let ρ := renameBound decl.typeVars s.types
      let η := renameBound decl.effectVars s.effects
      let r ← generate sig X Γ e (s.advance decl.typeVars decl.effectVars)
      some ⟨decl.output.rename ρ η, Poly.Effect.singleton op ∪ r.effect,
        .and r.constraints (.typeEq r.ty (decl.input.rename ρ η)), r.next⟩
  | .handle body op ret clause, s => do
      let raw ← sig op
      let rb ← generate sig X Γ body s
      let ρ := renameBound raw.typeVars rb.next.types
      let η := renameBound raw.effectVars rb.next.effects
      let decl := raw.alphaRename ρ η
      let sb := rb.next.advance raw.typeVars raw.effectVars
      let a := Ty.var sb.types
      let δ := Poly.Effect.var sb.effects
      let χ := Poly.Effect.var (sb.effects + 1)
      let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
      let rr ← generate sig X (Scheme.mono rb.ty :: Γ) ret sr
      let rc ← generate sig X
        (Scheme.mono (.arr decl.output χ a) ::
          Scheme.mono decl.input :: Γ) clause rr.next
      let localTypes := Finset.range rc.next.types \ Finset.range rr.next.types
      let localEffects := Finset.range rc.next.effects \ Finset.range rr.next.effects
      let C := Constraint.handler op decl rb.constraints rr.constraints rc.constraints
        rr.ty rc.ty a rb.effect rr.effect rc.effect δ χ localTypes localEffects
      letI : Decidable (decl.HandlerScope Γ rb.ty a rb.effect rr.effect δ χ) := by
        dsimp [OpDecl.HandlerScope]
        infer_instance
      letI : Decidable
          (decl.ClauseScope Γ C rb.ty a rb.effect rr.effect δ χ
            localTypes localEffects) := by
        dsimp [OpDecl.ClauseScope]
        infer_instance
      letI : Decidable (raw.AlphaSafe ρ η) := by
        dsimp [OpDecl.AlphaSafe]
        infer_instance
      if raw.AlphaSafe ρ η then
        if decl.HandlerScope Γ rb.ty a rb.effect rr.effect δ χ then
          if decl.ClauseScope Γ C rb.ty a rb.effect rr.effect δ χ
              localTypes localEffects then
            some ⟨a, χ, C, rc.next⟩
          else none
        else none
      else none

/-- Public entry point: start above names already present in the input. -/
def generateFresh (sig : Signature) (X : Domain) (Γ : Context X)
    (e : Expr) (s : Supply) : Option (Output X) :=
  generate sig X Γ e (s.seed sig Γ e [])

/-- Every successful execution of `generate` instantiates the formal generation
rules, including the universally closed operation clause. -/
theorem generate_sound {sig : Signature} {X : Domain} {Γ : Context X} {e : Expr}
    {s : Supply} {r : Output X}
    (h : generate sig X Γ e s = some r) :
    Generate sig X Γ e r.ty r.effect r.constraints := by
  fun_induction generate sig X Γ e s generalizing r with
  | case1 Γ i s =>
      cases hσ : Γ[i]? with
      | none => simp [hσ] at h
      | some σ =>
          by_cases hsafe : σ.SafeRename
              (renameBound σ.typeVars s.types)
              (renameBound σ.effectVars s.effects)
          · simp [hσ, hsafe] at h
            cases h
            exact Generate.var hσ
              ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩ hsafe
          · simp [hσ, hsafe] at h
  | case2 Γ n s =>
      cases h
      exact Generate.int n
  | case3 Γ b s =>
      cases h
      exact Generate.bool b
  | case4 Γ body s a ih =>
      cases hr : generate sig X (Scheme.mono a :: Γ) body
          {s with types := s.types + 1} with
      | none => simp [hr] at h
      | some rb =>
          simp [hr] at h
          cases h
          exact Generate.lam (ih hr)
  | case5 Γ f x s ihf ihx =>
      cases hf : generate sig X Γ f s with
      | none => simp [hf] at h
      | some rf =>
          cases hx : generate sig X Γ x rf.next with
          | none => simp [hf, hx] at h
          | some rx =>
              simp [hf, hx] at h
              cases h
              exact Generate.app (ihf hf) (ihx rf hx)
  | case6 Γ e₁ e₂ s ihBound ihVal ihMono =>
      cases h₁ : generate sig X Γ e₁ s with
      | none => simp [h₁] at h
      | some r₁ =>
          cases hv : e₁.isValue with
          | true =>
              cases h₂ : generate sig X
                  (Scheme.generalize Γ r₁.constraints r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  have hvgen := ihBound h₁
                  have heff := hvgen.value_effect (Expr.isValue_iff.mp hv)
                  rw [heff] at hvgen
                  exact Generate.letVal (Expr.isValue_iff.mp hv)
                    hvgen (ihVal r₁ h₂)
          | false =>
              cases h₂ : generate sig X (Scheme.mono r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  have hnv : ¬ Value e₁ := by
                    intro hv'
                    have := Expr.isValue_iff.mpr hv'
                    simp [hv] at this
                  exact Generate.letMono hnv (ihBound h₁) (ihMono r₁ h₂)
  | case7 Γ op e s ih =>
      cases hd : sig op with
      | none => simp [hd] at h
      | some decl =>
          cases he : generate sig X Γ e (s.advance decl.typeVars decl.effectVars) with
          | none => simp [hd, he] at h
          | some re =>
              simp [hd, he] at h
              cases h
              exact Generate.perform hd
                ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩ (ih decl he)
  | case8 Γ body op ret clause s ihBody ihRet ihClause =>
      cases hd : sig op with
      | none => simp [hd] at h
      | some raw =>
          cases hb : generate sig X Γ body s with
          | none => simp [hd, hb] at h
          | some rb =>
              let ρ := renameBound raw.typeVars rb.next.types
              let η := renameBound raw.effectVars rb.next.effects
              let decl := raw.alphaRename ρ η
              let sb := rb.next.advance raw.typeVars raw.effectVars
              let a := Ty.var sb.types
              let δ := Poly.Effect.var sb.effects
              let χ := Poly.Effect.var (sb.effects + 1)
              let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
              cases hr : generate sig X (Scheme.mono rb.ty :: Γ) ret sr with
              | none => simp [hd, hb, hr, sb, sr] at h
              | some rr =>
                  cases hc : generate sig X
                      (Scheme.mono (.arr decl.output χ a) ::
                        Scheme.mono decl.input :: Γ) clause rr.next with
                  | none => simp [hd, hb, hr, hc, ρ, η, decl, sb, a, χ, sr] at h
                  | some rc =>
                      let localTypes := Finset.range rc.next.types \ Finset.range rr.next.types
                      let localEffects := Finset.range rc.next.effects \ Finset.range rr.next.effects
                      let C := Constraint.handler op decl rb.constraints rr.constraints
                        rc.constraints rr.ty rc.ty a rb.effect rr.effect rc.effect δ χ
                        localTypes localEffects
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hs : decl.HandlerScope Γ rb.ty a rb.effect rr.effect δ χ
                        · by_cases hcs : decl.ClauseScope Γ C rb.ty a rb.effect
                            rr.effect δ χ localTypes localEffects
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr, localTypes, localEffects, C] at h
                            cases h
                            exact Generate.handle hd
                              ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩
                              hsafe rfl hs hcs (ihBody hb)
                              (ihRet raw rb hr) (ihClause raw rb rr hc)
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr, localTypes, localEffects, C] at h
                        · simp [hd, hb, hr, hc, hsafe, hs,
                            ρ, η, decl, sb, a, δ, χ, sr] at h
                      · simp [hd, hb, hr, hsafe, ρ, η, sb, sr] at h

/-- Recursive generation never reuses a number below its input supply. -/
theorem generate_next_mono {sig : Signature} {X : Domain} {Γ : Context X}
    {e : Expr} {s : Supply} {r : Output X}
    (h : generate sig X Γ e s = some r) :
    s.types ≤ r.next.types ∧ s.effects ≤ r.next.effects := by
  fun_induction generate sig X Γ e s generalizing r with
  | case1 Γ i s =>
      cases hσ : Γ[i]? with
      | none => simp [hσ] at h
      | some σ =>
          by_cases hsafe : σ.SafeRename
              (renameBound σ.typeVars s.types)
              (renameBound σ.effectVars s.effects)
          · simp [hσ, hsafe] at h
            cases h
            have hadvance := s.advance_mono σ.typeVars σ.effectVars
            exact ⟨Nat.le_of_lt hadvance.1, Nat.le_of_lt hadvance.2⟩
          · simp [hσ, hsafe] at h
  | case2 Γ n s => cases h; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | case3 Γ b s => cases h; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | case4 Γ body s a ih =>
      cases hr : generate sig X (Scheme.mono a :: Γ) body
          {s with types := s.types + 1} with
      | none => simp [hr] at h
      | some rb =>
          simp [hr] at h
          cases h
          have hm := ih hr
          dsimp at hm
          change s.types ≤ rb.next.types ∧ s.effects ≤ rb.next.effects
          exact ⟨by omega, hm.2⟩
  | case5 Γ f x s ihf ihx =>
      cases hf : generate sig X Γ f s with
      | none => simp [hf] at h
      | some rf =>
          cases hx : generate sig X Γ x rf.next with
          | none => simp [hf, hx] at h
          | some rx =>
              simp [hf, hx] at h
              cases h
              have hmf := ihf hf
              have hmx := ihx rf hx
              change s.types ≤ rx.next.types + 1 ∧
                s.effects ≤ rx.next.effects + 1
              constructor <;> omega
  | case6 Γ e₁ e₂ s ihBound ihVal ihMono =>
      cases h₁ : generate sig X Γ e₁ s with
      | none => simp [h₁] at h
      | some r₁ =>
          cases hv : e₁.isValue with
          | true =>
              cases h₂ : generate sig X
                  (Scheme.generalize Γ r₁.constraints r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  have hm₁ := ihBound h₁
                  have hm₂ := ihVal r₁ h₂
                  exact ⟨hm₁.1.trans hm₂.1, hm₁.2.trans hm₂.2⟩
          | false =>
              cases h₂ : generate sig X (Scheme.mono r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  have hm₁ := ihBound h₁
                  have hm₂ := ihMono r₁ h₂
                  exact ⟨hm₁.1.trans hm₂.1, hm₁.2.trans hm₂.2⟩
  | case7 Γ op e s ih =>
      cases hd : sig op with
      | none => simp [hd] at h
      | some decl =>
          cases he : generate sig X Γ e (s.advance decl.typeVars decl.effectVars) with
          | none => simp [hd, he] at h
          | some re =>
              simp [hd, he] at h
              cases h
              have hadvance := s.advance_mono decl.typeVars decl.effectVars
              have hm := ih decl he
              exact ⟨(Nat.le_of_lt hadvance.1).trans hm.1,
                (Nat.le_of_lt hadvance.2).trans hm.2⟩
  | case8 Γ body op ret clause s ihBody ihRet ihClause =>
      cases hd : sig op with
      | none => simp [hd] at h
      | some raw =>
          cases hb : generate sig X Γ body s with
          | none => simp [hd, hb] at h
          | some rb =>
              let ρ := renameBound raw.typeVars rb.next.types
              let η := renameBound raw.effectVars rb.next.effects
              let decl := raw.alphaRename ρ η
              let sb := rb.next.advance raw.typeVars raw.effectVars
              let a := Ty.var sb.types
              let δ := Poly.Effect.var sb.effects
              let χ := Poly.Effect.var (sb.effects + 1)
              let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
              cases hr : generate sig X (Scheme.mono rb.ty :: Γ) ret sr with
              | none => simp [hd, hb, hr, sb, sr] at h
              | some rr =>
                  cases hc : generate sig X
                      (Scheme.mono (.arr decl.output χ a) ::
                        Scheme.mono decl.input :: Γ) clause rr.next with
                  | none => simp [hd, hb, hr, hc, ρ, η, decl, sb, a, χ, sr] at h
                  | some rc =>
                      let localTypes := Finset.range rc.next.types \
                        Finset.range rr.next.types
                      let localEffects := Finset.range rc.next.effects \
                        Finset.range rr.next.effects
                      let C := Constraint.handler op decl rb.constraints rr.constraints
                        rc.constraints rr.ty rc.ty a rb.effect rr.effect rc.effect δ χ
                        localTypes localEffects
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hs : decl.HandlerScope Γ rb.ty a rb.effect rr.effect δ χ
                        · by_cases hcs : decl.ClauseScope Γ C rb.ty a rb.effect
                            rr.effect δ χ localTypes localEffects
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr, localTypes, localEffects, C] at h
                            cases h
                            have hmBody := ihBody hb
                            have hmAdvance := rb.next.advance_mono raw.typeVars raw.effectVars
                            have hmRet := ihRet raw rb hr
                            have hmClause := ihClause raw rb rr hc
                            change s.types ≤ rc.next.types ∧
                              s.effects ≤ rc.next.effects
                            dsimp [sb, sr] at hmRet
                            constructor <;> omega
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr, localTypes, localEffects, C] at h
                        · simp [hd, hb, hr, hc, hsafe, hs,
                            ρ, η, decl, sb, a, δ, χ, sr] at h
                      · simp [hd, hb, hr, hsafe, ρ, η, sb, sr] at h

/-- The seeded entry point obeys the same formal generation rules. -/
theorem generateFresh_sound {sig : Signature} {X : Domain}
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (h : generateFresh sig X Γ e s = some r) :
    Generate sig X Γ e r.ty r.effect r.constraints := by
  exact generate_sound h

/-- Soundness of the executable generator under any sound residualization. -/
theorem generate_residual_sound {sig : Signature} {X : Domain}
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    {R : Constraint X} (h : generate sig X Γ e s = some r)
    (hsolve : R.Entails r.constraints) :
    Typing sig X R Γ e r.ty r.effect :=
  (generate_sound h).residual_sound hsolve

end SystemFXi.EHMX
