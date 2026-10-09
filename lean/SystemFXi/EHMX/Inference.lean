import SystemFXi.EHMX.Constraints

namespace SystemFXi.EHMX

def Constraint.handler {X : Domain} (op : Op) (decl : OpDecl)
    (Cin Cr Co : Constraint X) (τr τo a : Ty)
    (εin εr εo δ χ : Effect) (localTypes localEffects : Finset Nat) :
    Constraint X :=
  .and (.and Cin Cr)
    (.and (.typeEq τr a)
      (.and (Constraint.close decl.typeVars decl.effectVars
          (Constraint.project localTypes localEffects
            (.and Co (.and (.typeEq τo a) (.effectLe εo χ)))))
        (.and (Constraint.split op εin δ)
          (.and (.effectLe δ χ) (.effectLe εr χ)))))

/-- Qualified declarative typing. Constraint implication is semantic, relative to
all valuations; it is not `Poly.Effect.Subset`, which quantifies independently. -/
inductive Typing (sig : Signature) (X : Domain) :
    Constraint X → Context X → Expr → Ty → Effect → Prop where
  | var {C Γ i σ ρ η} :
      Γ[i]? = some σ →
      σ.AdmissibleRename ρ η →
      σ.SafeRename ρ η →
      C.Entails (σ.instantiate ρ η).2 →
      Typing sig X C Γ (.var i) (σ.instantiate ρ η).1 ∅
  | int {C Γ} (n : Int) : Typing sig X C Γ (.int n) (.base .int) ∅
  | bool {C Γ} (b : Bool) : Typing sig X C Γ (.bool b) (.base .bool) ∅
  | lam {C Γ e a b ε} :
      Typing sig X C (Scheme.mono a :: Γ) e b ε →
      Typing sig X C Γ (.lam e) (.arr a ε b) ∅
  | app {C Γ f x a b εf εx η} :
      Typing sig X C Γ f (.arr a η b) εf →
      Typing sig X C Γ x a εx →
      Typing sig X C Γ (.app f x) b (εf ∪ εx ∪ η)
  | perform {C Γ op decl ρ η e ε} :
      sig op = some decl →
      decl.AdmissibleRename ρ η →
      Typing sig X C Γ e (decl.input.rename ρ η) ε →
      Typing sig X C Γ (.perform op e)
        (decl.output.rename ρ η) (Poly.Effect.singleton op ∪ ε)
  | letVal {C₁ C₂ Γ v e τ₁ τ₂ ε₂} :
      Value v →
      Typing sig X C₁ Γ v τ₁ ∅ →
      Typing sig X C₂ (Scheme.generalize Γ C₁ τ₁ :: Γ) e τ₂ ε₂ →
      Typing sig X (.and (Scheme.residual Γ C₁ τ₁) C₂)
        Γ (.letE v e) τ₂ ε₂
  | letMono {C Γ e₁ e₂ τ₁ τ₂ ε₁ ε₂} :
      ¬ Value e₁ →
      Typing sig X C Γ e₁ τ₁ ε₁ →
      Typing sig X C (Scheme.mono τ₁ :: Γ) e₂ τ₂ ε₂ →
      Typing sig X C Γ (.letE e₁ e₂) τ₂ (ε₁ ∪ ε₂)
  | handle {C D Γ body op ret clause raw decl ρ η τin a τo εin εr εo δ χ
      localTypes localEffects} :
      sig op = some raw →
      raw.AdmissibleRename ρ η →
      raw.AlphaSafe ρ η →
      decl = raw.alphaRename ρ η →
      decl.HandlerScope Γ τin a εin εr δ χ →
      decl.ClauseScope Γ C τin a εin εr δ χ localTypes localEffects →
      Typing sig X C Γ body τin εin →
      Typing sig X C (Scheme.mono τin :: Γ) ret a εr →
      Typing sig X D
        (Scheme.mono (.arr decl.output χ a) ::
          Scheme.mono decl.input :: Γ) clause τo εo →
      C.Entails (Constraint.close decl.typeVars decl.effectVars
        (Constraint.project localTypes localEffects
          (.and D (.and (.typeEq τo a) (.effectLe εo χ))))) →
      C.Entails (Constraint.split op εin δ) →
      C.Entails (.effectLe δ χ) →
      C.Entails (.effectLe εr χ) →
      Typing sig X C Γ (.handle body op ret clause) a χ
  | conv {C Γ e τ τ' ε} :
      Typing sig X C Γ e τ ε →
      C.Entails (.typeEq τ τ') →
      Typing sig X C Γ e τ' ε
  | weaken {C D Γ e τ ε} :
      Typing sig X C Γ e τ ε →
      D.Entails C →
      Typing sig X D Γ e τ ε

/-- Syntax-directed constraint generation. Fresh names are parameters of its
rules; freshness is needed for completeness, not for this soundness theorem. -/
inductive Generate (sig : Signature) (X : Domain) :
    Context X → Expr → Ty → Effect → Constraint X → Prop where
  | var {Γ i σ ρ η} :
      Γ[i]? = some σ →
      σ.AdmissibleRename ρ η →
      σ.SafeRename ρ η →
      Generate sig X Γ (.var i) (σ.instantiate ρ η).1 ∅
        (σ.instantiate ρ η).2
  | int {Γ} (n : Int) : Generate sig X Γ (.int n) (.base .int) ∅ .top
  | bool {Γ} (b : Bool) : Generate sig X Γ (.bool b) (.base .bool) ∅ .top
  | lam {Γ e a b ε C} :
      Generate sig X (Scheme.mono a :: Γ) e b ε C →
      Generate sig X Γ (.lam e) (.arr a ε b) ∅ C
  | app {Γ f x τf τx b εf εx η Cf Cx} :
      Generate sig X Γ f τf εf Cf →
      Generate sig X Γ x τx εx Cx →
      Generate sig X Γ (.app f x) b (εf ∪ εx ∪ η)
        (.and (.and Cf Cx) (.typeEq τf (.arr τx η b)))
  | perform {Γ op decl ρ η e τ ε C} :
      sig op = some decl →
      decl.AdmissibleRename ρ η →
      Generate sig X Γ e τ ε C →
      Generate sig X Γ (.perform op e)
        (decl.output.rename ρ η) (Poly.Effect.singleton op ∪ ε)
        (.and C (.typeEq τ (decl.input.rename ρ η)))
  | letVal {Γ v e τ₁ τ₂ ε₂ C₁ C₂} :
      Value v →
      Generate sig X Γ v τ₁ ∅ C₁ →
      Generate sig X (Scheme.generalize Γ C₁ τ₁ :: Γ) e τ₂ ε₂ C₂ →
      Generate sig X Γ (.letE v e) τ₂ ε₂
        (.and (Scheme.residual Γ C₁ τ₁) C₂)
  | letMono {Γ e₁ e₂ τ₁ τ₂ ε₁ ε₂ C₁ C₂} :
      ¬ Value e₁ →
      Generate sig X Γ e₁ τ₁ ε₁ C₁ →
      Generate sig X (Scheme.mono τ₁ :: Γ) e₂ τ₂ ε₂ C₂ →
      Generate sig X Γ (.letE e₁ e₂) τ₂ (ε₁ ∪ ε₂) (.and C₁ C₂)
  | handle {Γ body op ret clause raw decl ρ η τin a τr τo εin εr εo
      δ χ Cin Cr Co localTypes localEffects} :
      sig op = some raw →
      raw.AdmissibleRename ρ η →
      raw.AlphaSafe ρ η →
      decl = raw.alphaRename ρ η →
      decl.HandlerScope Γ τin a εin εr δ χ →
      decl.ClauseScope Γ
        (Constraint.handler op decl Cin Cr Co τr τo a εin εr εo δ χ
          localTypes localEffects)
        τin a εin εr δ χ localTypes localEffects →
      Generate sig X Γ body τin εin Cin →
      Generate sig X (Scheme.mono τin :: Γ) ret τr εr Cr →
      Generate sig X
        (Scheme.mono (.arr decl.output χ a) ::
          Scheme.mono decl.input :: Γ) clause τo εo Co →
      Generate sig X Γ (.handle body op ret clause) a χ
        (Constraint.handler op decl Cin Cr Co τr τo a εin εr εo δ χ
          localTypes localEffects)

theorem Generate.value_effect {sig : Signature} {X : Domain}
    {Γ : Context X} {v : Expr} {τ : Ty} {ε : Effect} {C : Constraint X}
    (h : Generate sig X Γ v τ ε C) (hv : Value v) : ε = ∅ := by
  cases hv with
  | var _ => cases h; rfl
  | int _ => cases h; rfl
  | bool _ => cases h; rfl
  | lam _ => cases h; rfl

theorem Generate.sound {sig : Signature} {X : Domain}
    {Γ : Context X} {e : Expr} {τ : Ty} {ε : Effect} {C : Constraint X}
    (h : Generate sig X Γ e τ ε C) : Typing sig X C Γ e τ ε := by
  induction h with
  | var hlookup hadm hsafe =>
      exact Typing.var hlookup hadm hsafe (Constraint.entails_refl _)
  | int n => exact Typing.int n
  | bool b => exact Typing.bool b
  | lam _ ih =>
      exact Typing.lam ih
  | app hf hx ihf ihx =>
      apply Typing.app
      · apply Typing.conv
        · exact Typing.weaken ihf (by intro ρ h; exact h.1.1)
        · intro ρ h
          exact h.2
      · exact Typing.weaken ihx (by intro ρ h; exact h.1.2)
  | perform hsig hadm _ ih =>
      apply Typing.perform hsig hadm
      apply Typing.conv
      · exact Typing.weaken ih (by intro ρ h; exact h.1)
      · intro ρ h
        exact h.2
  | letVal hv _ _ ihv ihe =>
      exact Typing.letVal hv ihv ihe
  | letMono hnv _ _ ih₁ ih₂ =>
      apply Typing.letMono hnv
      · exact Typing.weaken ih₁ (by intro ρ h; exact h.1)
      · exact Typing.weaken ih₂ (by intro ρ h; exact h.2)
  | handle hsig hadm hsafe hren hscope hclause _ _ _ ihb ihr ihc =>
      unfold Constraint.handler
      apply Typing.handle hsig hadm hsafe hren hscope hclause
      · exact Typing.weaken ihb (by intro ρ h; exact h.1.1)
      · apply Typing.conv
        · exact Typing.weaken ihr (by intro ρ h; exact h.1.2)
        · intro ρ h
          exact h.2.1
      · exact ihc
      · intro ρ h
        exact h.2.2.1
      · intro ρ h
        exact h.2.2.2.1
      · intro ρ h
        exact h.2.2.2.2.1
      · intro ρ h
        exact h.2.2.2.2.2

/-- Any residual constraint that implies the generated one suffices for typing. -/
theorem Generate.residual_sound {sig : Signature} {X : Domain}
    {Γ : Context X} {e : Expr} {τ : Ty} {ε : Effect}
    {C R : Constraint X} (h : Generate sig X Γ e τ ε C)
    (hsolve : R.Entails C) : Typing sig X R Γ e τ ε :=
  Typing.weaken h.sound hsolve

end SystemFXi.EHMX
