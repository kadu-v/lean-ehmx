import SystemFXi.EHMX.ConstraintSystem

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

structure Scheme (X : ConstraintSystem) where
  typeVars : Finset Nat
  effectVars : Finset Nat
  condition : X.Formula
  result : Ty

abbrev Context (X : ConstraintSystem) := List (Scheme X)

def Scheme.mono {X : ConstraintSystem} (τ : Ty) : Scheme X :=
  ⟨∅, ∅, X.trivial, τ⟩

def Scheme.freeTypes {X : ConstraintSystem} (σ : Scheme X) : Finset Nat :=
  (σ.result.fvTypes ∪ X.freeTypes σ.condition) \ σ.typeVars

def Scheme.freeEffects {X : ConstraintSystem} (σ : Scheme X) : Finset Nat :=
  (σ.result.fvEffects ∪ X.freeEffects σ.condition) \ σ.effectVars

def Context.freeTypes {X : ConstraintSystem} (Γ : Context X) : Finset Nat :=
  Γ.foldl (fun acc σ => acc ∪ σ.freeTypes) ∅

def Context.freeEffects {X : ConstraintSystem} (Γ : Context X) : Finset Nat :=
  Γ.foldl (fun acc σ => acc ∪ σ.freeEffects) ∅

def Scheme.generalize {X : ConstraintSystem} (Γ : Context X)
    (c : X.Formula) (τ : Ty) : Scheme X :=
  { typeVars := (τ.fvTypes ∪ X.freeTypes c) \ Γ.freeTypes
    effectVars := (τ.fvEffects ∪ X.freeEffects c) \ Γ.freeEffects
    condition := c
    result := τ }

def Scheme.residual {X : ConstraintSystem} (Γ : Context X)
    (c : X.Formula) (τ : Ty) : X.Formula :=
  let σ := Scheme.generalize Γ c τ
  X.project σ.typeVars σ.effectVars c

theorem Scheme.residual_free_context {X : ConstraintSystem}
    (hFV : X.LawfulFV) (Γ : Context X)
    (c : X.Formula) (τ : Ty) :
    X.freeTypes (Scheme.residual Γ c τ) ⊆ Γ.freeTypes ∧
    X.freeEffects (Scheme.residual Γ c τ) ⊆ Γ.freeEffects := by
  constructor
  · intro i hi
    have hp := hFV.project_types
      (Scheme.generalize Γ c τ).typeVars
      (Scheme.generalize Γ c τ).effectVars c
    have hi' := hp (by simpa [Scheme.residual] using hi)
    rcases Finset.mem_sdiff.mp hi' with ⟨hic, hnot⟩
    by_contra hΓ
    apply hnot
    simp [Scheme.generalize, hic, hΓ]

  · intro i hi
    have hp := hFV.project_effects
      (Scheme.generalize Γ c τ).typeVars
      (Scheme.generalize Γ c τ).effectVars c
    have hi' := hp (by simpa [Scheme.residual] using hi)
    rcases Finset.mem_sdiff.mp hi' with ⟨hic, hnot⟩
    by_contra hΓ
    apply hnot
    simp [Scheme.generalize, hic, hΓ]

theorem Scheme.residual_current {X : ConstraintSystem}
    (Γ : Context X) (c : X.Formula) (τ : Ty) :
    X.Entails c (Scheme.residual Γ c τ) := by
  intro v hc
  unfold Scheme.residual ConstraintSystem.project
  apply (X.projection_iff _ _ c v).2
  exact ⟨v.types, v.effects, (by intros; rfl),
    (by intros; rfl), hc⟩

def Scheme.AdmissibleRename {X : ConstraintSystem} (σ : Scheme X)
    (ft fe : Nat → Nat) : Prop :=
  (∀ i ∉ σ.typeVars, ft i = i) ∧
  (∀ i ∉ σ.effectVars, fe i = i)

def Scheme.FreshRename {X : ConstraintSystem} (σ : Scheme X)
    (ft fe : Nat → Nat) : Prop :=
  (∀ i ∈ σ.typeVars, ft i ∉ σ.typeVars) ∧
  (∀ i ∈ σ.effectVars, fe i ∉ σ.effectVars)

/-- Link each quantified type name to its fresh instance name.  The
constraint carried by the scheme is left untouched. -/
def typeLinks (X : ConstraintSystem) (names : List Nat)
    (fresh : Nat → Nat) : X.Formula :=
  names.foldr (fun i c =>
    X.combine (X.equalType (.var i) (.var (fresh i))) c) X.trivial

def effectLinks (X : ConstraintSystem) (names : List Nat)
    (fresh : Nat → Nat) : X.Formula :=
  names.foldr (fun i c =>
    X.combine (X.equalEffect (Poly.Effect.var i)
      (Poly.Effect.var (fresh i))) c) X.trivial

/-- HM(X)-style instantiation: diagonal equalities followed by projection.
No renaming is applied inside the opaque formula supplied by X. -/
def Scheme.instantiateProjected {X : ConstraintSystem} (σ : Scheme X)
    (ft fe : Nat → Nat) : Ty × X.Formula :=
  (σ.result.rename ft fe,
    X.project σ.typeVars σ.effectVars
      (X.combine σ.condition
        (X.combine
          (typeLinks X (σ.typeVars.sort (· ≤ ·)) ft)
          (effectLinks X (σ.effectVars.sort (· ≤ ·)) fe))))

def Scheme.GroundInstance {X : ConstraintSystem} (σ : Scheme X)
    (ρ : Valuation) (t : GroundTy) : Prop :=
  ∃ ft : Nat → GroundTy, ∃ fe : Nat → Finset Op,
    (∀ i, i ∉ σ.typeVars → ft i = ρ.types i) ∧
    (∀ i, i ∉ σ.effectVars → fe i = ρ.effects i) ∧
    X.holds σ.condition ⟨ft, fe⟩ ∧ σ.result.eval ⟨ft, fe⟩ = t

def Scheme.MoreGeneralAt {X : ConstraintSystem} (σg σd : Scheme X)
    (ρg ρd : Valuation) : Prop :=
  ∀ t, σd.GroundInstance ρd t → σg.GroundInstance ρg t

def Context.MoreGeneralAt {X : ConstraintSystem} (Γg Γd : Context X)
    (ρg ρd : Valuation) : Prop :=
  List.Forall₂ (fun σg σd => σg.MoreGeneralAt σd ρg ρd) Γg Γd

noncomputable def assignImage {α : Type}
    (bound : Finset Nat) (rename : Nat → Nat)
    (values original : Nat → α) (j : Nat) : α :=
  if h : ∃ i, i ∈ bound ∧ rename i = j then
    values (Classical.choose h)
  else original j

theorem assignImage_mem {α : Type}
    (bound : Finset Nat) (rename : Nat → Nat)
    (hinj : Set.InjOn rename bound)
    (values original : Nat → α) (i : Nat) (hi : i ∈ bound) :
    assignImage bound rename values original (rename i) = values i := by
  let h : ∃ k, k ∈ bound ∧ rename k = rename i := ⟨i, hi, rfl⟩
  have hc := Classical.choose_spec h
  have hki : Classical.choose h = i := hinj hc.1 hi hc.2
  simp [assignImage, h, hki]

theorem assignImage_not_mem {α : Type}
    (bound : Finset Nat) (rename : Nat → Nat)
    (values original : Nat → α) (j : Nat)
    (hj : j ∉ bound.image rename) :
    assignImage bound rename values original j = original j := by
  have hnone : ¬ ∃ i, i ∈ bound ∧ rename i = j := by
    rintro ⟨i, hi, rfl⟩
    exact hj (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  simp [assignImage, hnone]

def OpDecl.HandlerScope {X : ConstraintSystem} (decl : OpDecl)
    (Γ : Context X) (τin a : Ty) (εin εr δ χ : Effect) : Prop :=
  Disjoint decl.typeVars (Γ.freeTypes ∪ τin.fvTypes ∪ a.fvTypes) ∧
  Disjoint decl.effectVars
    (Γ.freeEffects ∪ τin.fvEffects ∪ a.fvEffects ∪
      εin.vars ∪ εr.vars ∪ δ.vars ∪ χ.vars)

def OpDecl.ClauseScope {X : ConstraintSystem} (decl : OpDecl)
    (Γ : Context X) (outer : X.Formula) (τin a : Ty)
    (εin εr δ χ : Effect) (localTypes localEffects : Finset Nat) : Prop :=
  Disjoint decl.typeVars (X.freeTypes outer) ∧
  Disjoint decl.effectVars (X.freeEffects outer) ∧
  Disjoint localTypes
    (Γ.freeTypes ∪ X.freeTypes outer ∪ τin.fvTypes ∪ a.fvTypes ∪
      decl.typeVars ∪ decl.input.fvTypes ∪ decl.output.fvTypes) ∧
  Disjoint localEffects
    (Γ.freeEffects ∪ X.freeEffects outer ∪ τin.fvEffects ∪ a.fvEffects ∪
      εin.vars ∪ εr.vars ∪ δ.vars ∪ χ.vars ∪ decl.effectVars ∪
      decl.input.fvEffects ∪ decl.output.fvEffects)

def handlerCondition (X : ConstraintSystem) (op : Op) (decl : OpDecl)
    (Cin Cr Co : X.Formula) (τr τo a : Ty)
    (εin εr εo δ χ : Effect) (localTypes localEffects : Finset Nat) :
    X.Formula :=
  X.combine (X.combine Cin Cr)
    (X.combine (X.equalType τr a)
      (X.combine
        (X.handlerClause decl.typeVars decl.effectVars
          localTypes localEffects
          (X.combine Co (X.combine (X.equalType τo a)
            (X.includedEffect εo χ))))
        (X.combine (X.split op εin δ)
          (X.combine (X.includedEffect δ χ)
            (X.includedEffect εr χ)))))

inductive Typing (sig : Signature) (X : ConstraintSystem) :
    X.Formula → Context X → Expr → Ty → Effect → Prop where
  | var {C Γ i σ ft fe} :
      Γ[i]? = some σ →
      σ.AdmissibleRename ft fe →
      σ.FreshRename ft fe →
      X.Entails C (σ.instantiateProjected ft fe).2 →
      Typing sig X C Γ (.var i) (σ.instantiateProjected ft fe).1 ∅
  | int {C Γ} (n : Int) : Typing sig X C Γ (.int n) (.base .int) ∅
  | bool {C Γ} (b : Bool) : Typing sig X C Γ (.bool b) (.base .bool) ∅
  | lam {C Γ e a b ε} :
      Typing sig X C (Scheme.mono a :: Γ) e b ε →
      Typing sig X C Γ (.lam e) (.arr a ε b) ∅
  | app {C Γ f x a b εf εx η} :
      Typing sig X C Γ f (.arr a η b) εf →
      Typing sig X C Γ x a εx →
      Typing sig X C Γ (.app f x) b (εf ∪ εx ∪ η)
  | perform {C Γ op decl ft fe e ε} :
      sig op = some decl →
      decl.AdmissibleRename ft fe →
      Typing sig X C Γ e (decl.input.rename ft fe) ε →
      Typing sig X C Γ (.perform op e)
        (decl.output.rename ft fe) (Poly.Effect.singleton op ∪ ε)
  | letVal {C₁ C₂ Γ v e τ₁ τ₂ ε₂} :
      Value v →
      Typing sig X C₁ Γ v τ₁ ∅ →
      Typing sig X C₂ (Scheme.generalize Γ C₁ τ₁ :: Γ) e τ₂ ε₂ →
      Typing sig X (X.combine (Scheme.residual Γ C₁ τ₁) C₂)
        Γ (.letE v e) τ₂ ε₂
  | letMono {C Γ e₁ e₂ τ₁ τ₂ ε₁ ε₂} :
      ¬ Value e₁ →
      Typing sig X C Γ e₁ τ₁ ε₁ →
      Typing sig X C (Scheme.mono τ₁ :: Γ) e₂ τ₂ ε₂ →
      Typing sig X C Γ (.letE e₁ e₂) τ₂ (ε₁ ∪ ε₂)
  | handle {C D Γ body op ret clause raw decl ft fe τin a τo
      εin εr εo δ χ localTypes localEffects} :
      sig op = some raw →
      raw.AdmissibleRename ft fe →
      raw.AlphaSafe ft fe →
      decl = raw.alphaRename ft fe →
      Generic.OpDecl.HandlerScope decl Γ τin a εin εr δ χ →
      Generic.OpDecl.ClauseScope decl Γ C τin a εin εr δ χ
        localTypes localEffects →
      Typing sig X C Γ body τin εin →
      Typing sig X C (Scheme.mono τin :: Γ) ret a εr →
      Typing sig X D
        (Scheme.mono (.arr decl.output χ a) ::
          Scheme.mono decl.input :: Γ) clause τo εo →
      X.Entails C
        (X.handlerClause decl.typeVars decl.effectVars
          localTypes localEffects
          (X.combine D (X.combine (X.equalType τo a)
            (X.includedEffect εo χ)))) →
      X.Entails C (X.split op εin δ) →
      X.Entails C (X.includedEffect δ χ) →
      X.Entails C (X.includedEffect εr χ) →
      Typing sig X C Γ (.handle body op ret clause) a χ
  | conv {C Γ e τ τ' ε} :
      Typing sig X C Γ e τ ε →
      X.Entails C (X.equalType τ τ') →
      Typing sig X C Γ e τ' ε
  | weaken {C D Γ e τ ε} :
      Typing sig X C Γ e τ ε →
      X.Entails D C →
      Typing sig X D Γ e τ ε

inductive Generate (sig : Signature) (X : ConstraintSystem) :
    Context X → Expr → Ty → Effect → X.Formula → Prop where
  | var {Γ i σ ft fe} :
      Γ[i]? = some σ →
      σ.AdmissibleRename ft fe →
      σ.FreshRename ft fe →
      Generate sig X Γ (.var i) (σ.instantiateProjected ft fe).1 ∅
        (σ.instantiateProjected ft fe).2
  | int {Γ} (n : Int) :
      Generate sig X Γ (.int n) (.base .int) ∅ X.trivial
  | bool {Γ} (b : Bool) :
      Generate sig X Γ (.bool b) (.base .bool) ∅ X.trivial
  | lam {Γ e a b ε C} :
      Generate sig X (Scheme.mono a :: Γ) e b ε C →
      Generate sig X Γ (.lam e) (.arr a ε b) ∅ C
  | app {Γ f x τf τx b εf εx η Cf Cx} :
      Generate sig X Γ f τf εf Cf →
      Generate sig X Γ x τx εx Cx →
      Generate sig X Γ (.app f x) b (εf ∪ εx ∪ η)
        (X.combine (X.combine Cf Cx)
          (X.equalType τf (.arr τx η b)))
  | perform {Γ op decl ft fe e τ ε C} :
      sig op = some decl →
      decl.AdmissibleRename ft fe →
      Generate sig X Γ e τ ε C →
      Generate sig X Γ (.perform op e)
        (decl.output.rename ft fe) (Poly.Effect.singleton op ∪ ε)
        (X.combine C (X.equalType τ (decl.input.rename ft fe)))
  | letVal {Γ v e τ₁ τ₂ ε₂ C₁ C₂} :
      Value v →
      Generate sig X Γ v τ₁ ∅ C₁ →
      Generate sig X (Scheme.generalize Γ C₁ τ₁ :: Γ) e τ₂ ε₂ C₂ →
      Generate sig X Γ (.letE v e) τ₂ ε₂
        (X.combine (Scheme.residual Γ C₁ τ₁) C₂)
  | letMono {Γ e₁ e₂ τ₁ τ₂ ε₁ ε₂ C₁ C₂} :
      ¬ Value e₁ →
      Generate sig X Γ e₁ τ₁ ε₁ C₁ →
      Generate sig X (Scheme.mono τ₁ :: Γ) e₂ τ₂ ε₂ C₂ →
      Generate sig X Γ (.letE e₁ e₂) τ₂ (ε₁ ∪ ε₂)
        (X.combine C₁ C₂)
  | handle {Γ body op ret clause raw decl ft fe τin a τr τo
      εin εr εo δ χ Cin Cr Co localTypes localEffects} :
      sig op = some raw →
      raw.AdmissibleRename ft fe →
      raw.AlphaSafe ft fe →
      decl = raw.alphaRename ft fe →
      Generic.OpDecl.HandlerScope decl Γ τin a εin εr δ χ →
      Generic.OpDecl.ClauseScope decl Γ
        (handlerCondition X op decl Cin Cr Co τr τo a
          εin εr εo δ χ localTypes localEffects)
        τin a εin εr δ χ localTypes localEffects →
      Generate sig X Γ body τin εin Cin →
      Generate sig X (Scheme.mono τin :: Γ) ret τr εr Cr →
      Generate sig X
        (Scheme.mono (.arr decl.output χ a) ::
          Scheme.mono decl.input :: Γ) clause τo εo Co →
      Generate sig X Γ (.handle body op ret clause) a χ
        (handlerCondition X op decl Cin Cr Co τr τo a
          εin εr εo δ χ localTypes localEffects)

theorem Generate.sound {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {e : Expr} {τ : Ty} {ε : Effect} {C : X.Formula}
    (h : Generate sig X Γ e τ ε C) : Typing sig X C Γ e τ ε := by
  induction h with
  | var hlookup hadm hfresh =>
      exact Typing.var hlookup hadm hfresh (X.entails_refl _)
  | int n => exact Typing.int n
  | bool b => exact Typing.bool b
  | lam _ ih => exact Typing.lam ih
  | app hf hx ihf ihx =>
      apply Typing.app
      · apply Typing.conv
        · exact Typing.weaken ihf
            (by intro v h
                have h' := (X.combine_iff _ _ v).1 h
                exact ((X.combine_iff _ _ v).1 h'.1).1)
        · intro v h
          exact (X.combine_iff _ _ v).1 h |>.2
      · exact Typing.weaken ihx
          (by intro v h
              have h' := (X.combine_iff _ _ v).1 h
              exact ((X.combine_iff _ _ v).1 h'.1).2)
  | perform hsig hadm _ ih =>
      apply Typing.perform hsig hadm
      apply Typing.conv
      · exact Typing.weaken ih
          (by intro v h; exact (X.combine_iff _ _ v).1 h |>.1)
      · intro v h
        exact (X.combine_iff _ _ v).1 h |>.2
  | letVal hv _ _ ihv ihe =>
      exact Typing.letVal hv ihv ihe
  | letMono hnv _ _ ih₁ ih₂ =>
      apply Typing.letMono hnv
      · exact Typing.weaken ih₁
          (by intro v h; exact (X.combine_iff _ _ v).1 h |>.1)
      · exact Typing.weaken ih₂
          (by intro v h; exact (X.combine_iff _ _ v).1 h |>.2)
  | handle hsig hadm hsafe hren hscope hclause _ _ _ ihb ihr ihc =>
      unfold handlerCondition
      apply Typing.handle hsig hadm hsafe hren hscope hclause
      · exact Typing.weaken ihb (by
          intro v h
          simp only [handlerCondition, X.combine_iff] at h
          exact h.1.1)
      · apply Typing.conv
        · exact Typing.weaken ihr (by
            intro v h
            simp only [handlerCondition, X.combine_iff] at h
            exact h.1.2)
        · intro v h
          simp only [handlerCondition, X.combine_iff] at h
          exact h.2.1
      · exact ihc
      · intro v h
        simp only [handlerCondition, X.combine_iff] at h
        exact h.2.2.1
      · intro v h
        simp only [handlerCondition, X.combine_iff] at h
        exact h.2.2.2.1
      · intro v h
        simp only [handlerCondition, X.combine_iff] at h
        exact h.2.2.2.2.1
      · intro v h
        simp only [handlerCondition, X.combine_iff] at h
        exact h.2.2.2.2.2

theorem Generate.residual_sound {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {e : Expr} {τ : Ty} {ε : Effect}
    {generated residual : X.Formula}
    (h : Generate sig X Γ e τ ε generated)
    (hsolve : X.Entails residual generated) :
    Typing sig X residual Γ e τ ε :=
  Typing.weaken h.sound hsolve

theorem Generate.value_effect {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {v : Expr} {τ : Ty} {ε : Effect}
    {C : X.Formula} (h : Generate sig X Γ v τ ε C)
    (hv : Value v) : ε = ∅ := by
  cases hv with
  | var _ => cases h; rfl
  | int _ => cases h; rfl
  | bool _ => cases h; rfl
  | lam _ => cases h; rfl

structure Output (X : ConstraintSystem) where
  ty : Ty
  effect : Effect
  condition : X.Formula
  next : Supply

def Scheme.usedTypes {X : ConstraintSystem} (σ : Scheme X) : Finset Nat :=
  σ.typeVars ∪ σ.result.fvTypes ∪ X.freeTypes σ.condition

def Scheme.usedEffects {X : ConstraintSystem} (σ : Scheme X) : Finset Nat :=
  σ.effectVars ∪ σ.result.fvEffects ∪ X.freeEffects σ.condition

def Supply.seed {X : ConstraintSystem} (s : Supply) (sig : Signature)
    (Γ : Context X) (e : Expr) : Supply :=
  let contextTypes := Γ.foldl (fun names σ => names ∪ σ.usedTypes) ∅
  let contextEffects := Γ.foldl (fun names σ => names ∪ σ.usedEffects) ∅
  let signatureTypes := e.ops.biUnion (fun op =>
    (sig op).elim ∅ OpDecl.usedTypes)
  let signatureEffects := e.ops.biUnion (fun op =>
    (sig op).elim ∅ OpDecl.usedEffects)
  ⟨max s.types ((contextTypes ∪ signatureTypes).sup id + 1),
   max s.effects ((contextEffects ∪ signatureEffects).sup id + 1)⟩

/-- Executable generation into the carrier of the supplied constraint
system. No constructor of the old `Constraint` syntax occurs here. -/
def generate (sig : Signature) (X : ConstraintSystem) (Γ : Context X) :
    Expr → Supply → Option (Output X)
  | .var i, s => do
      let σ ← Γ[i]?
      let ft := renameBound σ.typeVars s.types
      let fe := renameBound σ.effectVars s.effects
      letI : Decidable (σ.FreshRename ft fe) := by
        dsimp [Scheme.FreshRename]
        infer_instance
      if σ.FreshRename ft fe then
        let (τ, C) := σ.instantiateProjected ft fe
        some ⟨τ, ∅, C, s.advance σ.typeVars σ.effectVars⟩
      else none
  | .int _, s => some ⟨.base .int, ∅, X.trivial, s⟩
  | .bool _, s => some ⟨.base .bool, ∅, X.trivial, s⟩
  | .lam body, s => do
      let a := Ty.var s.types
      let r ← generate sig X (Scheme.mono a :: Γ) body
        {s with types := s.types + 1}
      some ⟨.arr a r.effect r.ty, ∅, r.condition, r.next⟩
  | .app f x, s => do
      let rf ← generate sig X Γ f s
      let rx ← generate sig X Γ x rf.next
      let b := Ty.var rx.next.types
      let η := Poly.Effect.var rx.next.effects
      let C := X.combine (X.combine rf.condition rx.condition)
        (X.equalType rf.ty (.arr rx.ty η b))
      some ⟨b, rf.effect ∪ rx.effect ∪ η, C,
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩
  | .letE e₁ e₂, s => do
      let r₁ ← generate sig X Γ e₁ s
      if e₁.isValue then
        let σ := Scheme.generalize Γ r₁.condition r₁.ty
        let r₂ ← generate sig X (σ :: Γ) e₂ r₁.next
        some ⟨r₂.ty, r₂.effect,
          X.combine (Scheme.residual Γ r₁.condition r₁.ty) r₂.condition,
          r₂.next⟩
      else
        let r₂ ← generate sig X (Scheme.mono r₁.ty :: Γ) e₂ r₁.next
        some ⟨r₂.ty, r₁.effect ∪ r₂.effect,
          X.combine r₁.condition r₂.condition, r₂.next⟩
  | .perform op e, s => do
      let decl ← sig op
      let ft := renameBound decl.typeVars s.types
      let fe := renameBound decl.effectVars s.effects
      let r ← generate sig X Γ e (s.advance decl.typeVars decl.effectVars)
      some ⟨decl.output.rename ft fe, Poly.Effect.singleton op ∪ r.effect,
        X.combine r.condition
          (X.equalType r.ty (decl.input.rename ft fe)), r.next⟩
  | .handle body op ret clause, s => do
      let raw ← sig op
      let rb ← generate sig X Γ body s
      let ft := renameBound raw.typeVars rb.next.types
      let fe := renameBound raw.effectVars rb.next.effects
      let decl := raw.alphaRename ft fe
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
      let C := handlerCondition X op decl rb.condition rr.condition rc.condition
        rr.ty rc.ty a rb.effect rr.effect rc.effect δ χ
        localTypes localEffects
      letI : Decidable
          (Generic.OpDecl.HandlerScope decl Γ rb.ty a
            rb.effect rr.effect δ χ) := by
        dsimp [Generic.OpDecl.HandlerScope]
        infer_instance
      letI : Decidable
          (Generic.OpDecl.ClauseScope decl Γ C rb.ty a
            rb.effect rr.effect δ χ localTypes localEffects) := by
        dsimp [Generic.OpDecl.ClauseScope]
        infer_instance
      letI : Decidable (raw.AlphaSafe ft fe) := by
        dsimp [OpDecl.AlphaSafe]
        infer_instance
      if raw.AlphaSafe ft fe then
        if Generic.OpDecl.HandlerScope decl Γ rb.ty a
            rb.effect rr.effect δ χ then
          if Generic.OpDecl.ClauseScope decl Γ C rb.ty a
              rb.effect rr.effect δ χ localTypes localEffects then
            some ⟨a, χ, C, rc.next⟩
          else none
        else none
      else none

def generateFresh (sig : Signature) (X : ConstraintSystem)
    (Γ : Context X) (e : Expr) (s : Supply) : Option (Output X) :=
  generate sig X Γ e (Generic.Supply.seed s sig Γ e)

theorem generate_sound {sig : Signature} {X : ConstraintSystem} {Γ : Context X} {e : Expr}
    {s : Supply} {r : Output X}
    (h : generate sig X Γ e s = some r) :
    Generate sig X Γ e r.ty r.effect r.condition := by
  fun_induction generate sig X Γ e s generalizing r with
  | case1 Γ i s =>
      cases hσ : Γ[i]? with
      | none => simp [hσ] at h
      | some σ =>
          by_cases hfresh : σ.FreshRename
              (renameBound σ.typeVars s.types)
              (renameBound σ.effectVars s.effects)
          · simp [hσ, hfresh] at h
            cases h
            exact Generate.var hσ
              ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩ hfresh
          · simp [hσ, hfresh] at h
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
                  (Scheme.generalize Γ r₁.condition r₁.ty :: Γ) e₂ r₁.next with
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
                      let C := handlerCondition X op decl rb.condition rr.condition
                        rc.condition rr.ty rc.ty a rb.effect rr.effect rc.effect δ χ
                        localTypes localEffects
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hs : Generic.OpDecl.HandlerScope decl Γ rb.ty a rb.effect rr.effect δ χ
                        · by_cases hcs : Generic.OpDecl.ClauseScope decl Γ C rb.ty a rb.effect
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

theorem generateFresh_sound {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (h : generateFresh sig X Γ e s = some r) :
    Typing sig X r.condition Γ e r.ty r.effect :=
  (generate_sound h).sound

/-- A generated constraint covers a declarative judgement at every valuation.
The core fragment has no let binding or handler clause, so its proof uses only
the cylindric constraint operations of X. -/
def GeneratedCovers {X : ConstraintSystem} (C Cg : X.Formula)
    (τg τ : Ty) (εg ε : Effect) : Prop :=
  ∀ v, X.holds C v →
    X.holds Cg v ∧ τg.eval v = τ.eval v ∧
      εg.eval v.effects = ε.eval v.effects

theorem Typing.core_generate_complete {sig : Signature}
    {X : ConstraintSystem} {C : X.Formula} {Γ : Context X}
    {e : Expr} {τ : Ty} {ε : Effect}
    (h : Typing sig X C Γ e τ ε) (hc : e.Core) :
    ∃ τg εg Cg, Generate sig X Γ e τg εg Cg ∧
      GeneratedCovers C Cg τg τ εg ε := by
  induction h with
  | var hlookup hadm hfresh hent =>
      refine ⟨_, _, _, Generate.var hlookup hadm hfresh, ?_⟩
      intro v hv
      exact ⟨hent v hv, rfl, rfl⟩
  | int n =>
      refine ⟨_, _, _, Generate.int n, ?_⟩
      intro v _
      exact ⟨(X.trivial_iff v).2 trivial, rfl, rfl⟩
  | bool b =>
      refine ⟨_, _, _, Generate.bool b, ?_⟩
      intro v _
      exact ⟨(X.trivial_iff v).2 trivial, rfl, rfl⟩
  | lam _ ih =>
      obtain ⟨bg, ηg, Cg, hg, hcov⟩ := ih hc
      refine ⟨.arr _ ηg bg, ∅, Cg, Generate.lam hg, ?_⟩
      intro v hv
      obtain ⟨hCg, ht, he⟩ := hcov v hv
      exact ⟨hCg, by simp [Ty.eval, ht, he], rfl⟩
  | app _ _ ihf ihx =>
      rename_i fExpr xExpr aTy bTy effF effX eta hproofF hproofX
      obtain ⟨hcf, hcx⟩ := hc
      obtain ⟨τfg, εfg, Cfg, hgf, hcovf⟩ := ihf hcf
      obtain ⟨τxg, εxg, Cxg, hgx, hcovx⟩ := ihx hcx
      refine ⟨bTy, εfg ∪ εxg ∪ eta,
        X.combine (X.combine Cfg Cxg)
          (X.equalType τfg (.arr τxg eta bTy)),
        Generate.app hgf hgx, ?_⟩
      intro v hv
      obtain ⟨hCf, htf, hef⟩ := hcovf v hv
      obtain ⟨hCx, htx, hex⟩ := hcovx v hv
      refine ⟨(X.combine_iff _ _ _).2
        ⟨(X.combine_iff _ _ _).2 ⟨hCf, hCx⟩, ?_⟩,
        rfl, ?_⟩
      · apply (X.equalType_iff _ _ _).2
        simp [Ty.eval, htf, htx]
      · simp [Effect.eval_union, hef, hex]
  | perform hsig hadm _ ih =>
      obtain ⟨τg, εg, Cg, hg, hcov⟩ := ih hc
      refine ⟨_, _, _, Generate.perform hsig hadm hg, ?_⟩
      intro v hv
      obtain ⟨hCg, ht, he⟩ := hcov v hv
      refine ⟨(X.combine_iff _ _ _).2 ⟨hCg, ?_⟩,
        rfl, ?_⟩
      · exact (X.equalType_iff _ _ _).2 ht
      · simp [Effect.eval_union, he]
  | letVal => simp [Expr.Core] at hc
  | letMono => simp [Expr.Core] at hc
  | handle => simp [Expr.Core] at hc
  | conv _ hconv ih =>
      obtain ⟨τg, εg, Cg, hg, hcov⟩ := ih hc
      refine ⟨τg, εg, Cg, hg, ?_⟩
      intro v hv
      obtain ⟨hCg, ht, he⟩ := hcov v hv
      exact ⟨hCg, ht.trans ((X.equalType_iff _ _ _).1 (hconv v hv)), he⟩
  | weaken _ hent ih =>
      obtain ⟨τg, εg, Cg, hg, hcov⟩ := ih hc
      refine ⟨τg, εg, Cg, hg, ?_⟩
      intro v hv
      exact hcov v (hent v hv)

/-- Semantic comparison used for principal computation schemes. The generated
valuation may assign fresh names, but it agrees with the declared valuation
on every name free in the context. -/
def Output.MoreGeneralThan {X : ConstraintSystem}
    (Γ : Context X) (r : Output X)
    (C : X.Formula) (τ : Ty) (ε : Effect) : Prop :=
  ∀ v, X.holds C v →
    ∃ w : Valuation,
      (∀ i ∈ Γ.freeTypes, w.types i = v.types i) ∧
      (∀ i ∈ Γ.freeEffects, w.effects i = v.effects i) ∧
      X.holds r.condition w ∧
      r.ty.eval w = τ.eval v ∧
      r.effect.eval w.effects = ε.eval v.effects

def ComputationScheme.generalize {X : ConstraintSystem}
    (Γ : Context X) (C : X.Formula) (τ : Ty) (ε : Effect) :
    X.ComputationScheme :=
  { typeVars := (X.freeTypes C ∪ τ.fvTypes) \ Γ.freeTypes
    effectVars := (X.freeEffects C ∪ τ.fvEffects ∪ ε.vars) \ Γ.freeEffects
    condition := C
    result := τ
    effect := ε }

/-- A solution of the generated constraint gives a ground instance of the
scheme obtained by generalizing over the context. -/
theorem ComputationScheme.generalize_instance_of_solution
    {X : ConstraintSystem}
    (Γ : Context X) (C : X.Formula) (τ : Ty) (ε : Effect)
    (ρ w : Valuation) (t : GroundTy) (η : Finset Op)
    (hct : ∀ i ∈ Γ.freeTypes, w.types i = ρ.types i)
    (hce : ∀ i ∈ Γ.freeEffects, w.effects i = ρ.effects i)
    (hC : X.holds C w) (ht : τ.eval w = t)
    (he : ε.eval w.effects = η) :
    (ComputationScheme.generalize Γ C τ ε).GroundInstance ρ t η := by
  let σ := ComputationScheme.generalize Γ C τ ε
  let ft : Nat → GroundTy := fun i =>
    if i ∈ σ.typeVars then w.types i else ρ.types i
  let fe : Nat → Finset Op := fun i =>
    if i ∈ σ.effectVars then w.effects i else ρ.effects i
  let u : Valuation := ⟨ft, fe⟩
  have hty : ∀ i ∈ X.freeTypes C ∪ τ.fvTypes,
      w.types i = u.types i := by
    intro i hi
    by_cases hb : i ∈ σ.typeVars
    · simp [u, ft, hb]
    · have hΓ : i ∈ Γ.freeTypes := by
        by_contra hn
        exact hb (by simp [σ, ComputationScheme.generalize, hi, hn])
      simp [u, ft, hb, hct i hΓ]
  have heff : ∀ i ∈ X.freeEffects C ∪ τ.fvEffects ∪ ε.vars,
      w.effects i = u.effects i := by
    intro i hi
    by_cases hb : i ∈ σ.effectVars
    · simp [u, fe, hb]
    · have hΓ : i ∈ Γ.freeEffects := by
        by_contra hn
        apply hb
        simp only [σ, ComputationScheme.generalize,
          Finset.mem_sdiff, Finset.mem_union] at hi ⊢
        exact ⟨by tauto, hn⟩
      simp [u, fe, hb, hce i hΓ]
  refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change i ∉ σ.typeVars at hi
    simp [u, ft, hi]
  · intro i hi
    change i ∉ σ.effectVars at hi
    simp [u, fe, hi]
  · exact (X.free_support C w u
      (by intro i hi; exact hty i (by simp [hi]))
      (by intro i hi; exact heff i (by simp [hi]))).mp hC
  · exact (Ty.eval_support τ w u
      (by intro i hi; exact hty i (by simp [hi]))
      (by intro i hi; exact heff i (by simp [hi]))).symm ▸ ht
  · exact (Effect.eval_support ε w u
      (by intro i hi; exact heff i (by simp [hi]))).symm ▸ he

theorem Output.moreGeneralThan_generalize {X : ConstraintSystem}
    (Γ : Context X) (r : Output X)
    (C : X.Formula) (τ : Ty) (ε : Effect)
    (h : r.MoreGeneralThan Γ C τ ε) :
    (ComputationScheme.generalize Γ r.condition r.ty r.effect).Subsumes
      (ComputationScheme.generalize Γ C τ ε) := by
  intro ρ t η hi
  obtain ⟨v, hvt, hve, hC, ht, he⟩ := hi
  obtain ⟨w, hct, hce, hR, hty, heff⟩ := h v hC
  apply ComputationScheme.generalize_instance_of_solution
    Γ r.condition r.ty r.effect ρ w t η
    (by
      intro i hiΓ
      exact (hct i hiΓ).trans (hvt i (by
        simp [ComputationScheme.generalize, hiΓ])))
    (by
      intro i hiΓ
      exact (hce i hiΓ).trans (hve i (by
        simp [ComputationScheme.generalize, hiΓ])))
    hR
  · exact hty.trans ht
  · exact heff.trans he


end SystemFXi.EHMX.Generic
