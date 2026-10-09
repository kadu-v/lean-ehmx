import SystemFXi.EHMX.NormalForm

namespace SystemFXi.EHMX

/-- A qualified computation scheme records both the result type and effect. -/
structure ComputationScheme (X : Domain) where
  typeVars : Finset Nat
  effectVars : Finset Nat
  predicates : Constraint X
  result : Ty
  effect : Effect

def ComputationScheme.fvTypes {X : Domain}
    (σ : ComputationScheme X) : Finset Nat :=
  (σ.predicates.fvTypes ∪ σ.result.fvTypes) \ σ.typeVars

def ComputationScheme.fvEffects {X : Domain}
    (σ : ComputationScheme X) : Finset Nat :=
  (σ.predicates.fvEffects ∪ σ.result.fvEffects ∪ σ.effect.vars) \
    σ.effectVars

def ComputationScheme.generalize {X : Domain}
    (Γ : Context X) (C : Constraint X) (τ : Ty) (ε : Effect) :
    ComputationScheme X :=
  { typeVars := (C.fvTypes ∪ τ.fvTypes) \ Γ.fvTypes
    effectVars := (C.fvEffects ∪ τ.fvEffects ∪ ε.vars) \ Γ.fvEffects
    predicates := C
    result := τ
    effect := ε }

theorem ComputationScheme.generalize_closed {X : Domain}
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (C : Constraint X) (τ : Ty) (ε : Effect) :
    (ComputationScheme.generalize Γ C τ ε).fvTypes = ∅ ∧
    (ComputationScheme.generalize Γ C τ ε).fvEffects = ∅ := by
  constructor
  · simp [ComputationScheme.fvTypes,
      ComputationScheme.generalize, hΓClosed.1]
  · simp [ComputationScheme.fvEffects,
      ComputationScheme.generalize, hΓClosed.2]

def Scheme.asComputation {X : Domain} (σ : Scheme X) :
    ComputationScheme X :=
  ⟨σ.typeVars, σ.effectVars, σ.predicates, σ.result, ∅⟩

/-- A ground instance chooses the quantified names and holds all others fixed. -/
def ComputationScheme.GroundInstance {X : Domain}
    (σ : ComputationScheme X) (ρ : Valuation)
    (t : GroundTy) (η : Finset Op) : Prop :=
  ∃ v : Valuation,
    (∀ i, i ∉ σ.typeVars → v.types i = ρ.types i) ∧
    (∀ i, i ∉ σ.effectVars → v.effects i = ρ.effects i) ∧
    σ.predicates.holds v ∧
    σ.result.eval v = t ∧
    σ.effect.eval v.effects = η

theorem Scheme.groundInstance_asComputation_iff {X : Domain}
    (σ : Scheme X) (ρ : Valuation) (t : GroundTy) :
    σ.GroundInstance ρ t ↔
      σ.asComputation.GroundInstance ρ t ∅ := by
  constructor
  · rintro ⟨ft, fe, ht, he, hp, hr⟩
    exact ⟨⟨ft, fe⟩, ht, he, hp, hr, by
      simp [Scheme.asComputation, Poly.Effect.eval]⟩
  · rintro ⟨v, ht, he, hp, hr, _⟩
    exact ⟨v.types, v.effects, ht, he, hp, hr⟩

/-- HM(X)'s scheme instance order, extended with the result effect. -/
def ComputationScheme.Subsumes {X : Domain}
    (σg σd : ComputationScheme X) : Prop :=
  ∀ ρ t η, σd.GroundInstance ρ t η →
    σg.GroundInstance ρ t η

/-- The residual of generalization is valid in the ambient context. -/
def Context.RealizableConstraint {X : Domain}
    (Γ : Context X) (C : Constraint X) : Prop :=
  ∀ ρ : Valuation, ∃ w : Valuation,
    (∀ i ∈ Γ.fvTypes, w.types i = ρ.types i) ∧
    (∀ i ∈ Γ.fvEffects, w.effects i = ρ.effects i) ∧
    C.holds w

theorem Context.realizableConstraint_of_closed {X : Domain}
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (C : Constraint X) (hC : ∃ w, C.holds w) :
    Γ.RealizableConstraint C := by
  obtain ⟨w, hw⟩ := hC
  intro ρ
  refine ⟨w, ?_, ?_, hw⟩
  · intro i hi
    simp [hΓClosed.1] at hi
  · intro i hi
    simp [hΓClosed.2] at hi

theorem ComputationScheme.subsumes_refl {X : Domain}
    (σ : ComputationScheme X) : σ.Subsumes σ :=
  fun _ _ _ h => h

theorem ComputationScheme.subsumes_trans {X : Domain}
    {σ₁ σ₂ σ₃ : ComputationScheme X}
    (h₁₂ : σ₁.Subsumes σ₂) (h₂₃ : σ₂.Subsumes σ₃) :
    σ₁.Subsumes σ₃ :=
  fun ρ t η h => h₁₂ ρ t η (h₂₃ ρ t η h)

/-- Lift a solution to an instance of the scheme generalized over Γ. -/
theorem ComputationScheme.generalize_instance_of_solution {X : Domain}
    (hSupport : LawfulSupport X)
    (Γ : Context X) (C : Constraint X) (τ : Ty) (ε : Effect)
    (ρ w : Valuation) (t : GroundTy) (η : Finset Op)
    (hct : ∀ i ∈ Γ.fvTypes, w.types i = ρ.types i)
    (hce : ∀ i ∈ Γ.fvEffects, w.effects i = ρ.effects i)
    (hC : C.holds w) (ht : τ.eval w = t)
    (he : ε.eval w.effects = η) :
    (ComputationScheme.generalize Γ C τ ε).GroundInstance ρ t η := by
  let σ := ComputationScheme.generalize Γ C τ ε
  let ft : Nat → GroundTy := fun i =>
    if i ∈ σ.typeVars then w.types i else ρ.types i
  let fe : Nat → Finset Op := fun i =>
    if i ∈ σ.effectVars then w.effects i else ρ.effects i
  let u : Valuation := ⟨ft, fe⟩
  have hty : ∀ i ∈ C.fvTypes ∪ τ.fvTypes,
      w.types i = u.types i := by
    intro i hi
    by_cases hb : i ∈ σ.typeVars
    · simp [u, ft, hb]
    · have hΓ : i ∈ Γ.fvTypes := by
        by_contra hn
        exact hb (by simp [σ, ComputationScheme.generalize, hi, hn])
      simp [u, ft, hb, hct i hΓ]
  have heff : ∀ i ∈ C.fvEffects ∪ τ.fvEffects ∪ ε.vars,
      w.effects i = u.effects i := by
    intro i hi
    by_cases hb : i ∈ σ.effectVars
    · simp [u, fe, hb]
    · have hΓ : i ∈ Γ.fvEffects := by
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
  · exact (Constraint.holds_support hSupport C w u
      (by intro i hi; exact hty i (by simp [hi]))
      (by intro i hi; exact heff i (by simp [hi]))).mp hC
  · exact (Ty.eval_support τ w u
      (by intro i hi; exact hty i (by simp [hi]))
      (by intro i hi; exact heff i (by simp [hi]))).symm ▸ ht
  · exact (Effect.eval_support ε w u
      (by intro i hi; exact heff i (by simp [hi]))).symm ▸ he

/-- A result scheme is derivable by generalization and semantic subsumption.
The latter includes qualified scheme instantiation. -/
inductive ComputationSchemeTyping (sig : Signature) (X : Domain)
    (Γ : Context X) (e : Expr) : ComputationScheme X → Prop where
  | generalize {C τ ε} :
      Typing sig X C Γ e τ ε →
      Γ.RealizableConstraint C →
      ComputationSchemeTyping sig X Γ e
        (ComputationScheme.generalize Γ C τ ε)
  | subsume {σg σd} :
      ComputationSchemeTyping sig X Γ e σg →
      σg.Subsumes σd →
      (∃ ρ t η, σd.GroundInstance ρ t η) →
      ComputationSchemeTyping sig X Γ e σd

/-- Ground uses of a scheme typing have a declarative monotype witness. -/
theorem ComputationSchemeTyping.ground_sound
    {sig : Signature} {X : Domain} {Γ : Context X} {e : Expr}
    {σ : ComputationScheme X}
    (h : ComputationSchemeTyping sig X Γ e σ)
    (ρ : Valuation) (t : GroundTy) (η : Finset Op)
    (hi : σ.GroundInstance ρ t η) :
    ∃ (C : Constraint X) (τ : Ty) (ε : Effect) (v : Valuation),
      Typing sig X C Γ e τ ε ∧ C.holds v ∧
      τ.eval v = t ∧ ε.eval v.effects = η := by
  induction h with
  | generalize ht _ =>
      obtain ⟨v, _, _, hC, hty, heff⟩ := hi
      exact ⟨_, _, _, v, ht, hC, hty, heff⟩
  | subsume _ hsub _ ih =>
      exact ih (hsub ρ t η hi)

theorem ComputationSchemeTyping.has_instance
    {sig : Signature} {X : Domain} {Γ : Context X} {e : Expr}
    {σ : ComputationScheme X}
    (hSupport : LawfulSupport X)
    (h : ComputationSchemeTyping sig X Γ e σ) :
    ∃ ρ t η, σ.GroundInstance ρ t η := by
  induction h with
  | generalize ht hreal =>
      let ρ : Valuation := ⟨fun _ => .atom 0, fun _ => ∅⟩
      obtain ⟨w, hct, hce, hC⟩ := hreal ρ
      exact ⟨ρ, _, _,
        ComputationScheme.generalize_instance_of_solution
          hSupport Γ _ _ _ ρ w _ _ hct hce hC rfl rfl⟩
  | subsume _ _ hreal _ =>
      exact hreal

theorem Output.moreGeneralThan_generalize {X : Domain}
    (hSupport : LawfulSupport X)
    (Γ : Context X) (r : Output X)
    (C : Constraint X) (τ : Ty) (ε : Effect)
    (h : r.MoreGeneralThan Γ C τ ε) :
    (ComputationScheme.generalize Γ r.constraints r.ty r.effect).Subsumes
      (ComputationScheme.generalize Γ C τ ε) := by
  intro ρ t η hi
  obtain ⟨v, hvt, hve, hC, ht, he⟩ := hi
  obtain ⟨w, hct, hce, hR, hty, heff⟩ := h v hC
  apply ComputationScheme.generalize_instance_of_solution
    hSupport Γ r.constraints r.ty r.effect ρ w t η
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

theorem NormalForm.raw_moreGeneralThan_reconstruction {X : Domain}
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (r : Output X) (n : NormalForm X)
    (h : n.SoundFor r.canonicalConstraint) :
    r.MoreGeneralThan Γ n.residual
      (n.reconstruct r.canonical).ty
      (n.reconstruct r.canonical).effect := by
  intro v hv
  let u := v.pullbackSubst n.subst
  obtain ⟨hD, ht, he⟩ :=
    n.reconstruct_sound r.canonical h v hv
  obtain ⟨hC, hresT, hresE⟩ :=
    (r.canonicalConstraint_holds_iff u).mp hD
  refine ⟨u, ?_, ?_, hC, ?_, ?_⟩
  · intro i hi
    simp [hΓClosed.1] at hi
  · intro i hi
    simp [hΓClosed.2] at hi
  · calc
      r.ty.eval u = u.types r.resultTypeName := hresT.symm
      _ = r.canonical.ty.eval u := rfl
      _ = (n.reconstruct r.canonical).ty.eval v := ht.symm
  · calc
      r.effect.eval u.effects = u.effects r.resultEffectName := hresE.symm
      _ = r.canonical.effect.eval u.effects := by
        simp [Output.canonical, Poly.Effect.eval, Poly.Effect.var]
      _ = (n.reconstruct r.canonical).effect.eval v.effects := he.symm

theorem ComputationSchemeTyping.principal_of_mono
    {sig : Signature} {X : Domain}
    (hSupport : LawfulSupport X)
    (Γ : Context X) (e : Expr) (r : Output X)
    (hmono : ∀ (C : Constraint X) (τ : Ty) (ε : Effect),
      Typing sig X C Γ e τ ε → r.MoreGeneralThan Γ C τ ε)
    (σ : ComputationScheme X)
    (hσ : ComputationSchemeTyping sig X Γ e σ) :
    (ComputationScheme.generalize Γ r.constraints r.ty r.effect).Subsumes σ := by
  induction hσ with
  | generalize ht _ =>
      exact r.moreGeneralThan_generalize hSupport Γ _ _ _
        (hmono _ _ _ ht)
  | subsume _ hsub _ ih =>
      intro ρ t η hi
      exact ih ρ t η (hsub ρ t η hi)

/-- EHM(X)'s principal computation-scheme theorem for a closed, realizable
judgment under the true ambient constraint. -/
theorem ComputationSchemeTyping.infer_principal_scheme
    {sig : Signature} {X : Domain} [DecidableEq X.Pred]
    (hRename : LawfulRename X)
    (hSupport : LawfulSupport X)
    (hFVRename : LawfulFVRename X)
    (hSigClosed : sig.Closed)
    (N : PrincipalNormalizer X)
    (hTrue : ∃ R, N.solved R ∧ ∀ v, R.holds v)
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (s : Supply)
    (σ : ComputationScheme X)
    (hσ : ComputationSchemeTyping sig X Γ e σ) :
    ∃ (r : Output X) (n : NormalForm X)
      (σo : ComputationScheme X),
      inferQualifiedTotal sig X [] Γ e s = some r ∧
      N.normalize r.canonicalConstraint = some n ∧
      σo = ComputationScheme.generalize Γ n.residual
        (n.reconstruct r.canonical).ty
        (n.reconstruct r.canonical).effect ∧
      σo.fvTypes = ∅ ∧ σo.fvEffects = ∅ ∧
      N.solved n.residual ∧
      ComputationSchemeTyping sig X Γ e σo ∧
      (∀ σ' : ComputationScheme X,
        ComputationSchemeTyping sig X Γ e σ' →
        σo.Subsumes σ') ∧
      ∃ ρ t η, σo.GroundInstance ρ t η := by
  obtain ⟨ρ, t, η, hreal⟩ := hσ.has_instance hSupport
  obtain ⟨C₀, τ₀, ε₀, v, h₀, hC₀, _, _⟩ :=
    hσ.ground_sound ρ t η hreal
  obtain ⟨r, n, hr, hn, hp, hs, hq⟩ :=
    h₀.inferQualifiedTotal_normalized_exists
      hRename hSupport hFVRename hSigClosed
      N hTrue [] Γ hΓClosed e s v ⟨trivial, hC₀⟩
  let q := n.reconstruct r.canonical
  let σo := ComputationScheme.generalize Γ n.residual q.ty q.effect
  obtain ⟨wr, hwr⟩ := N.solved_satisfiable n.residual hp.1.1
  let u := wr.pullbackSubst n.subst
  have hD : r.canonicalConstraint.holds u :=
    hs u ⟨wr, hwr, rfl⟩
  have hrawC : r.constraints.holds u :=
    (r.canonicalConstraint_holds_iff u).mp hD |>.1
  have hraw : ComputationSchemeTyping sig X Γ e
      (ComputationScheme.generalize Γ r.constraints r.ty r.effect) :=
    .generalize (inferQualifiedTotal_sound hr)
      (Γ.realizableConstraint_of_closed hΓClosed r.constraints
        ⟨u, hrawC⟩)
  have hrawSub :
      (ComputationScheme.generalize Γ r.constraints r.ty r.effect).Subsumes σo :=
    r.moreGeneralThan_generalize hSupport Γ n.residual q.ty q.effect
      (n.raw_moreGeneralThan_reconstruction Γ hΓClosed r hs)
  have hσoReal : ∃ ρ t η, σo.GroundInstance ρ t η := by
    refine ⟨wr, q.ty.eval wr, q.effect.eval wr.effects, ?_⟩
    exact ComputationScheme.generalize_instance_of_solution
      hSupport Γ n.residual q.ty q.effect
      wr wr _ _
      (by intro _ _; rfl) (by intro _ _; rfl)
      hwr rfl rfl
  have hσo : ComputationSchemeTyping sig X Γ e σo :=
    .subsume hraw hrawSub hσoReal
  have hprincipal : ∀ σ' : ComputationScheme X,
      ComputationSchemeTyping sig X Γ e σ' →
      σo.Subsumes σ' := by
    intro σ' hσ'
    apply hσ'.principal_of_mono hSupport Γ e q
    intro C τ ε htyping vd hC
    exact hq C τ ε htyping vd ⟨trivial, hC⟩
  have hσoClosed := ComputationScheme.generalize_closed Γ hΓClosed
    n.residual q.ty q.effect
  exact ⟨r, n, σo, hr, hn, rfl,
    hσoClosed.1, hσoClosed.2, hp.1.1,
    hσo, hprincipal, ρ, t, η, hprincipal σ hσ ρ t η hreal⟩

end SystemFXi.EHMX
