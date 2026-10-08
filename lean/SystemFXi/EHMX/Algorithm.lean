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

def Supply.advance (s : Supply) (types effects : Finset Nat) : Supply :=
  ⟨s.types + types.sup id + 2, s.effects + effects.sup id + 2⟩

/-- Executable, syntax-directed constraint generation. It deliberately returns
symbolic effect constraints; it does not choose a least handler effect. -/
def generate (sig : Signature) (X : Domain) (Γ : Context X) :
    Expr → Supply → Option (Output X)
  | .var i, s => do
      let σ ← Γ[i]?
      let ρ := renameBound σ.typeVars s.types
      let η := renameBound σ.effectVars s.effects
      let (τ, C) := σ.instantiate ρ η
      some ⟨τ, ∅, C, s.advance σ.typeVars σ.effectVars⟩
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
        some ⟨r₂.ty, r₂.effect, r₂.constraints, r₂.next⟩
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
      let decl ← sig op
      let rb ← generate sig X Γ body s
      let a := Ty.var rb.next.types
      let δ := Poly.Effect.var rb.next.effects
      let χ := Poly.Effect.var (rb.next.effects + 1)
      let sr : Supply := ⟨rb.next.types + 1, rb.next.effects + 2⟩
      let rr ← generate sig X (Scheme.mono rb.ty :: Γ) ret sr
      let rc ← generate sig X
        (Scheme.mono (.arr decl.output χ a) ::
          Scheme.mono decl.input :: Γ) clause rr.next
      letI : Decidable (decl.HandlerScope Γ rb.ty a rb.effect rr.effect δ χ) := by
        dsimp [OpDecl.HandlerScope]
        infer_instance
      if decl.HandlerScope Γ rb.ty a rb.effect rr.effect δ χ then
        let C := Constraint.and (.and rb.constraints rr.constraints)
          (.and (.typeEq rr.ty a)
            (.and (Constraint.close decl.typeVars decl.effectVars
                (.and rc.constraints
                  (.and (.typeEq rc.ty a) (.effectLe rc.effect χ))))
              (.and (Constraint.split op rb.effect δ)
                (.and (.effectLe δ χ) (.effectLe rr.effect χ)))))
        some ⟨a, χ, C, rc.next⟩
      else none

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
          simp [hσ] at h
          cases h
          exact Generate.var hσ ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩
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
      | some decl =>
          cases hb : generate sig X Γ body s with
          | none => simp [hd, hb] at h
          | some rb =>
              let a := Ty.var rb.next.types
              let δ := Poly.Effect.var rb.next.effects
              let χ := Poly.Effect.var (rb.next.effects + 1)
              let sr : Supply := ⟨rb.next.types + 1, rb.next.effects + 2⟩
              cases hr : generate sig X (Scheme.mono rb.ty :: Γ) ret sr with
              | none => simp [hd, hb, hr, sr] at h
              | some rr =>
                  cases hc : generate sig X
                      (Scheme.mono (.arr decl.output χ a) ::
                        Scheme.mono decl.input :: Γ) clause rr.next with
                  | none => simp [hd, hb, hr, hc, a, χ, sr] at h
                  | some rc =>
                      by_cases hs : decl.HandlerScope Γ rb.ty a rb.effect rr.effect δ χ
                      · simp [hd, hb, hr, hc, hs, a, δ, χ, sr] at h
                        cases h
                        exact Generate.handle hd hs (ihBody hb)
                          (ihRet rb hr) (ihClause decl rb rr hc)
                      · simp [hd, hb, hr, hc, hs, a, δ, χ, sr] at h

/-- Soundness of the executable generator under any sound residualization. -/
theorem generate_residual_sound {sig : Signature} {X : Domain}
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    {R : Constraint X} (h : generate sig X Γ e s = some r)
    (hsolve : R.Entails r.constraints) :
    Typing sig X R Γ e r.ty r.effect :=
  (generate_sound h).residual_sound hsolve

end SystemFXi.EHMX
