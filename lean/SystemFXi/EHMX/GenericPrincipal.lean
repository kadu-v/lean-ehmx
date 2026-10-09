import SystemFXi.EHMX.GenericLogicalInstantiation

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

theorem Scheme.mono_groundInstance_iff {X : ConstraintSystem}
    (τ : Ty) (ρ : Valuation) (t : GroundTy) :
    (Scheme.mono (X := X) τ).GroundInstance ρ t ↔
      τ.eval ρ = t := by
  constructor
  · rintro ⟨ft, fe, hft, hfe, _, ht⟩
    have hft' : ft = ρ.types := funext (fun i => hft i (by simp [Scheme.mono]))
    have hfe' : fe = ρ.effects := funext (fun i => hfe i (by simp [Scheme.mono]))
    simpa [hft', hfe', Scheme.mono] using ht
  · intro ht
    exact ⟨ρ.types, ρ.effects, by simp [Scheme.mono],
      by simp [Scheme.mono], (X.trivial_iff ρ).2 trivial, ht⟩

theorem Scheme.mono_moreGeneralAt_iff {X : ConstraintSystem}
    (τg τd : Ty) (ρg ρd : Valuation) :
    (Scheme.mono (X := X) τg).MoreGeneralAt
      (Scheme.mono τd) ρg ρd ↔ τg.eval ρg = τd.eval ρd := by
  constructor
  · intro h
    exact (Scheme.mono_groundInstance_iff τg ρg _).mp
      (h _ ((Scheme.mono_groundInstance_iff τd ρd _).mpr rfl))
  · intro heq t ht
    apply (Scheme.mono_groundInstance_iff τg ρg t).mpr
    exact heq.trans ((Scheme.mono_groundInstance_iff τd ρd t).mp ht)

theorem Context.moreGeneralAt_refl {X : ConstraintSystem}
    (Γ : Context X) (ρ : Valuation) : Γ.MoreGeneralAt Γ ρ ρ := by
  induction Γ with
  | nil => exact List.Forall₂.nil
  | cons σ rest ih =>
      exact List.Forall₂.cons (by intro t h; exact h) ih

theorem Context.lookup_of_length_eq {X : ConstraintSystem}
    (Γg Γd : Context X) (i : Nat)
    (hlen : Γg.length = Γd.length)
    (σd : Scheme X) (hd : Γd[i]? = some σd) :
    ∃ σg, Γg[i]? = some σg := by
  cases hg : Γg[i]? with
  | some σg => exact ⟨σg, rfl⟩
  | none =>
      have hgi : Γg.length ≤ i :=
        (List.getElem?_eq_none_iff).mp hg
      have hdi : i < Γd.length := by
        by_contra h
        have : Γd[i]? = none :=
          (List.getElem?_eq_none_iff).mpr (by omega)
        rw [hd] at this
        cases this
      omega

theorem Context.moreGeneralAt_lookup {X : ConstraintSystem}
    {Γg Γd : Context X} {ρg ρd : Valuation}
    (h : Γg.MoreGeneralAt Γd ρg ρd)
    {i : Nat} {σg σd : Scheme X}
    (hg : Γg[i]? = some σg) (hd : Γd[i]? = some σd) :
    σg.MoreGeneralAt σd ρg ρd := by
  induction h generalizing i σg σd with
  | nil => simp at hg
  | cons hhead htail ih =>
      cases i with
      | zero =>
          simp at hg hd
          cases hg
          cases hd
          exact hhead
      | succ j =>
          exact ih (by simpa using hg) (by simpa using hd)

/-- Variable completeness for diagonal-equality instantiation. The proof
needs no renaming law or bound-name metadata for the opaque X formula. -/
theorem Context.variable_complete_projected {X : ConstraintSystem}
    {Γg Γd : Context X} {σg σd : Scheme X} {i : Nat}
    (hg : Γg[i]? = some σg) (hd : Γd[i]? = some σd)
    (ρd ηd ρg ηg : Nat → Nat)
    (hadmD : σd.AdmissibleRename ρd ηd)
    (hfreshD : σd.FreshRename ρd ηd)
    (hadmG : σg.AdmissibleRename ρg ηg)
    (hinjT : Set.InjOn ρg σg.typeVars)
    (hinjE : Set.InjOn ηg σg.effectVars)
    (hfreshG : σg.FreshRename ρg ηg)
    (fixedTypes fixedEffects : Finset Nat)
    (hfreeT : σg.freeTypes ⊆ fixedTypes)
    (hfreeE : σg.freeEffects ⊆ fixedEffects)
    (hdisjT : (σg.typeVars.image ρg) ∩ fixedTypes = ∅)
    (hdisjE : (σg.effectVars.image ηg) ∩ fixedEffects = ∅)
    (vg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd)
    (hp : X.holds (σd.instantiateProjected ρd ηd).2 vd) :
    ∃ w : Valuation,
      (∀ j ∈ fixedTypes, w.types j = vg.types j) ∧
      (∀ j ∈ fixedEffects, w.effects j = vg.effects j) ∧
      X.holds (σg.instantiateProjected ρg ηg).2 w ∧
      (σg.instantiateProjected ρg ηg).1.eval w =
        (σd.instantiateProjected ρd ηd).1.eval vd := by
  have hdinst : σd.GroundInstance vd
      ((σd.instantiateProjected ρd ηd).1.eval vd) :=
    σd.instantiateProjected_groundInstance ρd ηd hadmD
      hfreshD.1 hfreshD.2 vd hp
  have hginst := (Context.moreGeneralAt_lookup hctx hg hd) _ hdinst
  rcases σg.groundInstance_realizable_projected ρg ηg hadmG
      (hinjT) (hinjE) hfreshG.1 hfreshG.2
      fixedTypes fixedEffects hfreeT hfreeE hdisjT hdisjE
      vg _ hginst with ⟨w, hT, hE, hC, ht⟩
  exact ⟨w, hT, hE, hC, ht⟩

theorem Scheme.groundInstance_support {X : ConstraintSystem}
    (σ : Scheme X) (v w : Valuation)
    (ht : ∀ i ∈ σ.freeTypes, v.types i = w.types i)
    (he : ∀ i ∈ σ.freeEffects, v.effects i = w.effects i)
    (t : GroundTy) :
    σ.GroundInstance v t ↔ σ.GroundInstance w t := by
  have forward (v w : Valuation)
      (ht : ∀ i ∈ σ.freeTypes, v.types i = w.types i)
      (he : ∀ i ∈ σ.freeEffects, v.effects i = w.effects i)
      (h : σ.GroundInstance v t) : σ.GroundInstance w t := by
    rcases h with ⟨ft, fe, hft, hfe, hp, hr⟩
    let wt : Nat → GroundTy := fun i =>
      if i ∈ σ.typeVars then ft i else w.types i
    let we : Nat → Finset Op := fun i =>
      if i ∈ σ.effectVars then fe i else w.effects i
    have hty : ∀ i ∈ σ.result.fvTypes ∪ X.freeTypes σ.condition,
        ft i = wt i := by
      intro i hi
      by_cases hb : i ∈ σ.typeVars
      · simp [wt, hb]
      · have hf : i ∈ σ.freeTypes := Finset.mem_sdiff.mpr ⟨hi, hb⟩
        simp [wt, hb, hft i hb, ht i hf]
    have heff : ∀ i ∈ σ.result.fvEffects ∪ X.freeEffects σ.condition,
        fe i = we i := by
      intro i hi
      by_cases hb : i ∈ σ.effectVars
      · simp [we, hb]
      · have hf : i ∈ σ.freeEffects := Finset.mem_sdiff.mpr ⟨hi, hb⟩
        simp [we, hb, hfe i hb, he i hf]
    refine ⟨wt, we, ?_, ?_, ?_, ?_⟩
    · intro i hi; simp [wt, hi]
    · intro i hi; simp [we, hi]
    · exact (X.free_support σ.condition ⟨ft, fe⟩ ⟨wt, we⟩
        (fun i hi => hty i (Finset.mem_union_right _ hi))
        (fun i hi => heff i (Finset.mem_union_right _ hi))).mp hp
    · exact (Ty.eval_support σ.result ⟨ft, fe⟩ ⟨wt, we⟩
        (fun i hi => hty i (Finset.mem_union_left _ hi))
        (fun i hi => heff i (Finset.mem_union_left _ hi))).symm ▸ hr
  constructor
  · exact forward v w ht he
  · exact forward w v
      (fun i hi => (ht i hi).symm)
      (fun i hi => (he i hi).symm)

/-- The residual of a value binding is exactly the existence of a ground
instance of its generalized scheme. This uses X's existential projection,
independently of the syntax used to represent its formulas. -/
theorem Scheme.generalize_instance_iff_residual {X : ConstraintSystem}
    (Γ : Context X) (c : X.Formula) (τ : Ty) (ρ : Valuation) :
    (∃ t, (Scheme.generalize Γ c τ).GroundInstance ρ t) ↔
      X.holds (Scheme.residual Γ c τ) ρ := by
  rw [Scheme.residual]
  unfold ConstraintSystem.project
  rw [X.projection_iff]
  constructor
  · rintro ⟨t, ft, fe, hft, hfe, hc, _⟩
    exact ⟨ft, fe, hft, hfe, hc⟩
  · rintro ⟨ft, fe, hft, hfe, hc⟩
    exact ⟨τ.eval ⟨ft, fe⟩, ft, fe, hft, hfe, hc, rfl⟩

theorem Scheme.moreGeneralAt_support {X : ConstraintSystem}
    (σg σd : Scheme X) (vg wg vd wd : Valuation)
    (h : σg.MoreGeneralAt σd vg vd)
    (hgt : ∀ i ∈ σg.freeTypes, vg.types i = wg.types i)
    (hge : ∀ i ∈ σg.freeEffects, vg.effects i = wg.effects i)
    (hdt : ∀ i ∈ σd.freeTypes, vd.types i = wd.types i)
    (hde : ∀ i ∈ σd.freeEffects, vd.effects i = wd.effects i) :
    σg.MoreGeneralAt σd wg wd := by
  intro t hd
  have hd' := (σd.groundInstance_support vd wd hdt hde t).mpr hd
  have hg' := h t hd'
  exact (σg.groundInstance_support vg wg hgt hge t).mp hg'

theorem Context.moreGeneralAt_support {X : ConstraintSystem}
    (Γg Γd : Context X) (vg wg vd wd : Valuation)
    (h : Γg.MoreGeneralAt Γd vg vd)
    (hgt : ∀ σ ∈ Γg, ∀ i ∈ σ.freeTypes, vg.types i = wg.types i)
    (hge : ∀ σ ∈ Γg, ∀ i ∈ σ.freeEffects, vg.effects i = wg.effects i)
    (hdt : ∀ σ ∈ Γd, ∀ i ∈ σ.freeTypes, vd.types i = wd.types i)
    (hde : ∀ σ ∈ Γd, ∀ i ∈ σ.freeEffects, vd.effects i = wd.effects i) :
    Γg.MoreGeneralAt Γd wg wd := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons σg σd Γg Γd hhead htail ih =>
      apply List.Forall₂.cons
      · exact σg.moreGeneralAt_support σd vg wg vd wd hhead
          (hgt σg (by simp)) (hge σg (by simp))
          (hdt σd (by simp)) (hde σd (by simp))
      · apply ih
        · intro σ hs i hi; exact hgt σ (by simp [hs]) i hi
        · intro σ hs i hi; exact hge σ (by simp [hs]) i hi
        · intro σ hs i hi; exact hdt σ (by simp [hs]) i hi
        · intro σ hs i hi; exact hde σ (by simp [hs]) i hi

/-- Semantic comparison of results inferred under different value contexts.
This is the relation needed to induct over polymorphic value bindings. -/
def GeneratedCoversAcross {X : ConstraintSystem}
    (Γg Γd : Context X) (Cd Cg : X.Formula)
    (τg τd : Ty) (εg εd : Effect) : Prop :=
  ∀ vg vd, Γg.MoreGeneralAt Γd vg vd → X.holds Cd vd →
    ∃ wg : Valuation,
      (∀ i ∈ Γg.freeTypes, wg.types i = vg.types i) ∧
      (∀ i ∈ Γg.freeEffects, wg.effects i = vg.effects i) ∧
      X.holds Cg wg ∧ τg.eval wg = τd.eval vd ∧
        εg.eval wg.effects = εd.eval vd.effects

private theorem foldl_union_mem {α : Type}
    (f : α → Finset Nat) (xs : List α) (acc : Finset Nat) (i : Nat) :
    i ∈ xs.foldl (fun names x => names ∪ f x) acc ↔
      i ∈ acc ∨ ∃ x ∈ xs, i ∈ f x := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
      aesop

/-- The public seed exceeds every name in any scheme selected from the
environment. This is the executable variable case's freshness invariant. -/
theorem Supply.seed_above_lookup {X : ConstraintSystem}
    (s : Supply) (sig : Signature) (Γ : Context X) (e : Expr)
    (i : Nat) (σ : Scheme X) (hlookup : Γ[i]? = some σ) :
    (∀ j ∈ σ.usedTypes, j < (Supply.seed s sig Γ e).types) ∧
    (∀ j ∈ σ.usedEffects, j < (Supply.seed s sig Γ e).effects) := by
  have hmem : σ ∈ Γ := List.mem_of_getElem? hlookup
  constructor
  · intro j hj
    have hfold : j ∈ Γ.foldl (fun names σ => names ∪ σ.usedTypes) ∅ :=
      (foldl_union_mem Scheme.usedTypes Γ ∅ j).mpr
        (Or.inr ⟨σ, hmem, hj⟩)
    have hsup : j ≤
        ((Γ.foldl (fun names σ => names ∪ σ.usedTypes) ∅) ∪
          e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedTypes)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_left _ hfold)
    dsimp [Supply.seed]
    omega
  · intro j hj
    have hfold : j ∈ Γ.foldl (fun names σ => names ∪ σ.usedEffects) ∅ :=
      (foldl_union_mem Scheme.usedEffects Γ ∅ j).mpr
        (Or.inr ⟨σ, hmem, hj⟩)
    have hsup : j ≤
        ((Γ.foldl (fun names σ => names ∪ σ.usedEffects) ∅) ∪
          e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedEffects)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_left _ hfold)
    dsimp [Supply.seed]
    omega

theorem generateFresh_var_success {X : ConstraintSystem}
    (sig : Signature) (Γ : Context X) (s : Supply)
    (i : Nat) (σ : Scheme X) (hlookup : Γ[i]? = some σ) :
    ∃ r : Output X,
      generateFresh sig X Γ (.var i) s = some r := by
  let seed := Supply.seed s sig Γ (.var i)
  let ρ := renameBound σ.typeVars seed.types
  let η := renameBound σ.effectVars seed.effects
  have hb := Generic.Supply.seed_above_lookup s sig Γ (.var i) i σ hlookup
  have hfresh : σ.FreshRename ρ η :=
    σ.renameBound_fresh seed.types seed.effects
      (fun j hj => hb.1 j (by simp [Scheme.usedTypes, hj]))
      (fun j hj => hb.2 j (by simp [Scheme.usedEffects, hj]))
  refine ⟨⟨(σ.instantiateProjected ρ η).1, ∅,
    (σ.instantiateProjected ρ η).2,
      seed.advance σ.typeVars σ.effectVars⟩, ?_⟩
  simp [generateFresh, generate, seed, hlookup, ρ, η, hfresh]

theorem Scheme.freeTypes_subset_usedTypes {X : ConstraintSystem}
    (σ : Scheme X) : σ.freeTypes ⊆ σ.usedTypes := by
  intro i hi
  simp [Scheme.freeTypes, Scheme.usedTypes] at hi ⊢
  aesop

theorem Scheme.freeEffects_subset_usedEffects {X : ConstraintSystem}
    (σ : Scheme X) : σ.freeEffects ⊆ σ.usedEffects := by
  intro i hi
  simp [Scheme.freeEffects, Scheme.usedEffects] at hi ⊢
  aesop

theorem Supply.seed_context_free_below {X : ConstraintSystem}
    (s : Supply) (sig : Signature) (Γ : Context X) (e : Expr) :
    (∀ j ∈ Γ.freeTypes, j < (Supply.seed s sig Γ e).types) ∧
    (∀ j ∈ Γ.freeEffects, j < (Supply.seed s sig Γ e).effects) := by
  constructor
  · intro j hj
    rcases (foldl_union_mem Scheme.freeTypes Γ ∅ j).mp hj with
      hnil | ⟨σ, hσ, hf⟩
    · simp at hnil
    · have hfold : j ∈ Γ.foldl (fun names σ => names ∪ σ.usedTypes) ∅ :=
        (foldl_union_mem Scheme.usedTypes Γ ∅ j).mpr
          (Or.inr ⟨σ, hσ, σ.freeTypes_subset_usedTypes hf⟩)
      have hsup : j ≤
          ((Γ.foldl (fun names σ => names ∪ σ.usedTypes) ∅) ∪
            e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedTypes)).sup id :=
        Finset.le_sup (f := id) (Finset.mem_union_left _ hfold)
      dsimp [Supply.seed]
      omega
  · intro j hj
    rcases (foldl_union_mem Scheme.freeEffects Γ ∅ j).mp hj with
      hnil | ⟨σ, hσ, hf⟩
    · simp at hnil
    · have hfold : j ∈ Γ.foldl (fun names σ => names ∪ σ.usedEffects) ∅ :=
        (foldl_union_mem Scheme.usedEffects Γ ∅ j).mpr
          (Or.inr ⟨σ, hσ, σ.freeEffects_subset_usedEffects hf⟩)
      have hsup : j ≤
          ((Γ.foldl (fun names σ => names ∪ σ.usedEffects) ∅) ∪
            e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedEffects)).sup id :=
        Finset.le_sup (f := id) (Finset.mem_union_left _ hfold)
      dsimp [Supply.seed]
      omega

private theorem renameBound_image_disjoint_below
    (bound fixed : Finset Nat) (base : Nat)
    (hbelow : ∀ j ∈ fixed, j < base) :
    (bound.image (renameBound bound base)) ∩ fixed = ∅ := by
  rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
  intro j hj hfixed
  rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
  have hlt := hbelow _ hfixed
  simp [renameBound, hi] at hlt
  omega

/-- The executable fresh-variable branch is principal among declarative
variable uses, including qualified schemes in the context. -/
theorem generateFresh_var_principal {X : ConstraintSystem}
    (sig : Signature) (Γ : Context X) (s : Supply)
    (C : X.Formula) (i : Nat) (σ : Scheme X)
    (hlookup : Γ[i]? = some σ)
    (ft fe : Nat → Nat)
    (hadm : σ.AdmissibleRename ft fe)
    (hfreshD : σ.FreshRename ft fe)
    (hent : X.Entails C (σ.instantiateProjected ft fe).2) :
    ∃ r : Output X,
      generateFresh sig X Γ (.var i) s = some r ∧
      r.MoreGeneralThan Γ C (σ.instantiateProjected ft fe).1 ∅ := by
  let seed := Supply.seed s sig Γ (.var i)
  let ρ := renameBound σ.typeVars seed.types
  let η := renameBound σ.effectVars seed.effects
  have hb := Generic.Supply.seed_above_lookup s sig Γ (.var i) i σ hlookup
  have hfreshG : σ.FreshRename ρ η :=
    σ.renameBound_fresh seed.types seed.effects
      (fun j hj => hb.1 j (by simp [Scheme.usedTypes, hj]))
      (fun j hj => hb.2 j (by simp [Scheme.usedEffects, hj]))
  have hbelow := Generic.Supply.seed_context_free_below
    s sig Γ (.var i)
  have hmem : σ ∈ Γ := List.mem_of_getElem? hlookup
  have hfreeT : σ.freeTypes ⊆ Γ.freeTypes := by
    intro j hj
    exact (foldl_union_mem Scheme.freeTypes Γ ∅ j).mpr
      (Or.inr ⟨σ, hmem, hj⟩)
  have hfreeE : σ.freeEffects ⊆ Γ.freeEffects := by
    intro j hj
    exact (foldl_union_mem Scheme.freeEffects Γ ∅ j).mpr
      (Or.inr ⟨σ, hmem, hj⟩)
  have hdisjT : (σ.typeVars.image ρ) ∩ Γ.freeTypes = ∅ :=
    renameBound_image_disjoint_below σ.typeVars Γ.freeTypes
      seed.types hbelow.1
  have hdisjE : (σ.effectVars.image η) ∩ Γ.freeEffects = ∅ :=
    renameBound_image_disjoint_below σ.effectVars Γ.freeEffects
      seed.effects hbelow.2
  refine ⟨⟨(σ.instantiateProjected ρ η).1, ∅,
    (σ.instantiateProjected ρ η).2,
      seed.advance σ.typeVars σ.effectVars⟩,
    ?_, ?_⟩
  · simp [generateFresh, generate, seed, hlookup, ρ, η, hfreshG]
  · intro v hv
    rcases Context.variable_complete_projected
      hlookup hlookup ft fe ρ η hadm hfreshD
      ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩
      (renameBound_injOn _ _) (renameBound_injOn _ _) hfreshG
      Γ.freeTypes Γ.freeEffects hfreeT hfreeE hdisjT hdisjE v v
      (Context.moreGeneralAt_refl Γ v) (hent v hv) with
      ⟨w, hT, hE, hC, ht⟩
    exact ⟨w, hT, hE, hC, ht, rfl⟩

theorem Context.freeTypes_of_mem {X : ConstraintSystem}
    (Γ : Context X) (σ : Scheme X) (h : σ ∈ Γ) :
    σ.freeTypes ⊆ Γ.freeTypes := by
  intro i hi
  exact (foldl_union_mem Scheme.freeTypes Γ ∅ i).mpr
    (Or.inr ⟨σ, h, hi⟩)

theorem Context.freeEffects_of_mem {X : ConstraintSystem}
    (Γ : Context X) (σ : Scheme X) (h : σ ∈ Γ) :
    σ.freeEffects ⊆ Γ.freeEffects := by
  intro i hi
  exact (foldl_union_mem Scheme.freeEffects Γ ∅ i).mpr
    (Or.inr ⟨σ, h, hi⟩)

theorem Context.freeTypes_subset_cons {X : ConstraintSystem}
    (σ : Scheme X) (Γ : Context X) :
    Γ.freeTypes ⊆ Context.freeTypes (σ :: Γ) := by
  intro i hi
  rcases (foldl_union_mem Scheme.freeTypes Γ ∅ i).mp hi with
    h | ⟨x, hx, hix⟩
  · simp at h
  · exact (foldl_union_mem Scheme.freeTypes (σ :: Γ) ∅ i).mpr
      (Or.inr ⟨x, by simp [hx], hix⟩)

theorem Context.freeEffects_subset_cons {X : ConstraintSystem}
    (σ : Scheme X) (Γ : Context X) :
    Γ.freeEffects ⊆ Context.freeEffects (σ :: Γ) := by
  intro i hi
  rcases (foldl_union_mem Scheme.freeEffects Γ ∅ i).mp hi with
    h | ⟨x, hx, hix⟩
  · simp at h
  · exact (foldl_union_mem Scheme.freeEffects (σ :: Γ) ∅ i).mpr
      (Or.inr ⟨x, by simp [hx], hix⟩)

/-- A generated solution agreeing on the context gives an instance of the
generalized value scheme. -/
theorem Scheme.generalize_groundInstance_of_solution {X : ConstraintSystem}
    (Γ : Context X) (C : X.Formula) (τ : Ty)
    (v w : Valuation) (t : GroundTy)
    (hct : ∀ i ∈ Γ.freeTypes, w.types i = v.types i)
    (hce : ∀ i ∈ Γ.freeEffects, w.effects i = v.effects i)
    (hC : X.holds C w) (ht : τ.eval w = t) :
    (Scheme.generalize Γ C τ).GroundInstance v t := by
  let σ := Scheme.generalize Γ C τ
  let wt : Nat → GroundTy := fun i =>
    if i ∈ σ.typeVars then w.types i else v.types i
  let we : Nat → Finset Op := fun i =>
    if i ∈ σ.effectVars then w.effects i else v.effects i
  have hty : ∀ i ∈ τ.fvTypes ∪ X.freeTypes C,
      w.types i = wt i := by
    intro i hi
    by_cases hb : i ∈ σ.typeVars
    · simp [wt, hb]
    · have hΓ : i ∈ Γ.freeTypes := by
        by_contra hn
        exact hb (by simp [σ, Scheme.generalize, hi, hn])
      simp [wt, hb, hct i hΓ]
  have heff : ∀ i ∈ τ.fvEffects ∪ X.freeEffects C,
      w.effects i = we i := by
    intro i hi
    by_cases hb : i ∈ σ.effectVars
    · simp [we, hb]
    · have hΓ : i ∈ Γ.freeEffects := by
        by_contra hn
        exact hb (by simp [σ, Scheme.generalize, hi, hn])
      simp [we, hb, hce i hΓ]
  refine ⟨wt, we, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change i ∉ σ.typeVars at hi
    simp [wt, hi]
  · intro i hi
    change i ∉ σ.effectVars at hi
    simp [we, hi]
  · exact (X.free_support C w ⟨wt, we⟩
      (fun i hi => hty i (Finset.mem_union_right _ hi))
      (fun i hi => heff i (Finset.mem_union_right _ hi))).mp hC
  · exact (Ty.eval_support τ w ⟨wt, we⟩
      (fun i hi => hty i (Finset.mem_union_left _ hi))
      (fun i hi => heff i (Finset.mem_union_left _ hi))).symm ▸ ht

/-- Generalization respects semantic instances even when the two contexts
have different schemes. -/
theorem Scheme.generalize_moreGeneralAt_across {X : ConstraintSystem}
    (Γg Γd : Context X) (Cd Cg : X.Formula)
    (τd τg : Ty) (εd εg : Effect)
    (hcov : GeneratedCoversAcross Γg Γd Cd Cg τg τd εg εd)
    (vg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd) :
    (Scheme.generalize Γg Cg τg).MoreGeneralAt
      (Scheme.generalize Γd Cd τd) vg vd := by
  intro t hinst
  rcases hinst with ⟨ft, fe, hft, hfe, hCd, ht⟩
  let vd' : Valuation := ⟨ft, fe⟩
  have hctx' : Γg.MoreGeneralAt Γd vg vd' := by
    apply Context.moreGeneralAt_support Γg Γd vg vg vd vd' hctx
    · intro σ _ i _; rfl
    · intro σ _ i _; rfl
    · intro σ hσ i hi
      have hΓ := Context.freeTypes_of_mem Γd σ hσ hi
      have hnot : i ∉ (Scheme.generalize Γd Cd τd).typeVars := by
        simp [Scheme.generalize, hΓ]
      exact (hft i hnot).symm
    · intro σ hσ i hi
      have hΓ := Context.freeEffects_of_mem Γd σ hσ hi
      have hnot : i ∉ (Scheme.generalize Γd Cd τd).effectVars := by
        simp [Scheme.generalize, hΓ]
      exact (hfe i hnot).symm
  rcases hcov vg vd' hctx' hCd with
    ⟨wg, hgt, hge, hCg, hty, _⟩
  exact Scheme.generalize_groundInstance_of_solution
    Γg Cg τg vg wg t hgt hge hCg (hty.trans ht)

theorem Scheme.residual_across {X : ConstraintSystem}
    (Γg Γd : Context X) (Cd Cg : X.Formula)
    (τd τg : Ty) (εd εg : Effect)
    (hcov : GeneratedCoversAcross Γg Γd Cd Cg τg τd εg εd)
    (vg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd)
    (hres : X.holds (Scheme.residual Γd Cd τd) vd) :
    X.holds (Scheme.residual Γg Cg τg) vg := by
  rcases (Scheme.generalize_instance_iff_residual Γd Cd τd vd).mpr
    hres with ⟨t, hinst⟩
  apply (Scheme.generalize_instance_iff_residual Γg Cg τg vg).mp
  exact ⟨t, (Scheme.generalize_moreGeneralAt_across Γg Γd Cd Cg
    τd τg εd εg hcov vg vd hctx) t hinst⟩

/-- The semantic value-let step. The first generated constraint is projected
outside the binding, while its generalized scheme is available in the body. -/
theorem GeneratedCoversAcross.letVal {X : ConstraintSystem}
    (hFV : X.LawfulFV)
    (Γg Γd : Context X)
    (C₁ Cg C₂ C₂g : X.Formula)
    (τ₁ τg τ₂ τ₂g : Ty)
    (ε₁ εg ε₂ ε₂g : Effect)
    (hfirst : GeneratedCoversAcross Γg Γd C₁ Cg τg τ₁ εg ε₁)
    (hbody : GeneratedCoversAcross
      (Scheme.generalize Γg Cg τg :: Γg)
      (Scheme.generalize Γd C₁ τ₁ :: Γd)
      C₂ C₂g τ₂g τ₂ ε₂g ε₂) :
    GeneratedCoversAcross Γg Γd
      (X.combine (Scheme.residual Γd C₁ τ₁) C₂)
      (X.combine (Scheme.residual Γg Cg τg) C₂g)
      τ₂g τ₂ ε₂g ε₂ := by
  intro vg vd hctx hC
  rcases (X.combine_iff _ _ _).mp hC with ⟨hresD, hC₂⟩
  have hgen := Scheme.generalize_moreGeneralAt_across Γg Γd
    C₁ Cg τ₁ τg ε₁ εg hfirst vg vd hctx
  have hresG := Scheme.residual_across Γg Γd
    C₁ Cg τ₁ τg ε₁ εg hfirst vg vd hctx hresD
  have hctxBody : Context.MoreGeneralAt
      (Scheme.generalize Γg Cg τg :: Γg)
      (Scheme.generalize Γd C₁ τ₁ :: Γd) vg vd :=
    List.Forall₂.cons hgen hctx
  rcases hbody vg vd hctxBody hC₂ with
    ⟨wg, hbt, hbe, hCg₂, hty, heff⟩
  have hct : ∀ i ∈ Γg.freeTypes, wg.types i = vg.types i := by
    intro i hi
    exact hbt i (Context.freeTypes_subset_cons _ Γg hi)
  have hce : ∀ i ∈ Γg.freeEffects, wg.effects i = vg.effects i := by
    intro i hi
    exact hbe i (Context.freeEffects_subset_cons _ Γg hi)
  have hresW : X.holds (Scheme.residual Γg Cg τg) wg := by
    have hs := Scheme.residual_free_context hFV Γg Cg τg
    exact (X.free_support (Scheme.residual Γg Cg τg) vg wg
      (fun i hi => (hct i (hs.1 hi)).symm)
      (fun i hi => (hce i (hs.2 hi)).symm)).mp hresG
  exact ⟨wg, hct, hce, (X.combine_iff _ _ _).mpr ⟨hresW, hCg₂⟩,
    hty, heff⟩

/-- The generated operation-clause body preserves the required result type
and effect bound through the handler's universal/existential binder. -/
theorem GeneratedCovers.handlerClause
    {X : ConstraintSystem}
    (bt be lt le : Finset Nat)
    (Co Cg : X.Formula) (τo τg a : Ty)
    (εo εg χ : Effect)
    (hcov : GeneratedCovers Co Cg τg τo εg εo) :
    X.Entails
      (X.handlerClause bt be lt le
        (X.combine Co
          (X.combine (X.equalType τo a)
            (X.includedEffect εo χ))))
      (X.handlerClause bt be lt le
        (X.combine Cg
          (X.combine (X.equalType τg a)
            (X.includedEffect εg χ)))) := by
  apply X.handlerClause_mono bt be lt le
  intro v hv
  obtain ⟨hCo, hrest⟩ := (X.combine_iff _ _ _).1 hv
  obtain ⟨htau, heps⟩ := (X.combine_iff _ _ _).1 hrest
  obtain ⟨hCg, ht, he⟩ := hcov v hCo
  apply (X.combine_iff _ _ _).2
  refine ⟨hCg, (X.combine_iff _ _ _).2 ⟨?_, ?_⟩⟩
  · apply (X.equalType_iff _ _ _).2
    exact ht.trans ((X.equalType_iff _ _ _).1 htau)
  · apply (X.includedEffect_iff _ _ _).2
    rw [he]
    exact (X.includedEffect_iff _ _ _).1 heps

/-- Names in the inferred result that must be preserved when adding the two
output equations used by HM(X) normalization. -/
def Output.supportTypes {X : ConstraintSystem} (r : Output X) : Finset Nat :=
  r.ty.fvTypes ∪ X.freeTypes r.condition

def Output.supportEffects {X : ConstraintSystem} (r : Output X) : Finset Nat :=
  r.ty.fvEffects ∪ r.effect.vars ∪ X.freeEffects r.condition

def Output.resultTypeName {X : ConstraintSystem} (r : Output X) : Nat :=
  max r.next.types (r.supportTypes.sup id + 1)

def Output.resultEffectName {X : ConstraintSystem} (r : Output X) : Nat :=
  max r.next.effects (r.supportEffects.sup id + 1)

theorem Output.resultTypeName_fresh {X : ConstraintSystem}
    (r : Output X) (i : Nat) (hi : i ∈ r.supportTypes) :
    i < r.resultTypeName := by
  have hs : i ≤ r.supportTypes.sup id := Finset.le_sup (f := id) hi
  simp only [Output.resultTypeName]
  omega

theorem Output.resultEffectName_fresh {X : ConstraintSystem}
    (r : Output X) (i : Nat) (hi : i ∈ r.supportEffects) :
    i < r.resultEffectName := by
  have hs : i ≤ r.supportEffects.sup id := Finset.le_sup (f := id) hi
  simp only [Output.resultEffectName]
  omega

def Output.extendResult {X : ConstraintSystem} (r : Output X)
    (v : Valuation) : Valuation :=
  { types := Function.update v.types r.resultTypeName (r.ty.eval v)
    effects := Function.update v.effects r.resultEffectName
      (r.effect.eval v.effects) }

def Output.canonicalCondition {X : ConstraintSystem} (r : Output X) :
    X.Formula :=
  X.combine r.condition
    (X.combine (X.equalType (.var r.resultTypeName) r.ty)
      (X.equalEffect (Poly.Effect.var r.resultEffectName) r.effect))

theorem Output.canonicalCondition_iff {X : ConstraintSystem}
    (r : Output X) (v : Valuation) :
    X.holds r.canonicalCondition v ↔
      X.holds r.condition v ∧
      v.types r.resultTypeName = r.ty.eval v ∧
      v.effects r.resultEffectName = r.effect.eval v.effects := by
  simp [Output.canonicalCondition, X.combine_iff, X.equalType_iff,
    X.equalEffect_iff, Ty.eval, Poly.Effect.eval, Poly.Effect.var]

theorem Output.extendResult_agrees {X : ConstraintSystem}
    (r : Output X) (v : Valuation) :
    (∀ i ∈ r.supportTypes,
      (r.extendResult v).types i = v.types i) ∧
    (∀ i ∈ r.supportEffects,
      (r.extendResult v).effects i = v.effects i) := by
  constructor
  · intro i hi
    have hne : i ≠ r.resultTypeName :=
      Nat.ne_of_lt (r.resultTypeName_fresh i hi)
    simp [Output.extendResult, Function.update, hne]
  · intro i hi
    have hne : i ≠ r.resultEffectName :=
      Nat.ne_of_lt (r.resultEffectName_fresh i hi)
    simp [Output.extendResult, Function.update, hne]

theorem Output.extendResult_solution {X : ConstraintSystem}
    (r : Output X) (v : Valuation)
    (hv : X.holds r.condition v) :
    X.holds r.canonicalCondition (r.extendResult v) := by
  have ha := r.extendResult_agrees v
  have hC : X.holds r.condition (r.extendResult v) :=
    (X.free_support r.condition v (r.extendResult v)
      (by intro i hi; exact (ha.1 i (by
        simp [Output.supportTypes, hi])).symm)
      (by intro i hi; exact (ha.2 i (by
        simp [Output.supportEffects, hi])).symm)).mp hv
  have hT : r.ty.eval (r.extendResult v) = r.ty.eval v :=
    Ty.eval_support r.ty (r.extendResult v) v
      (by intro i hi; exact ha.1 i (by
        simp [Output.supportTypes, hi]))
      (by intro i hi; exact ha.2 i (by
        simp [Output.supportEffects, hi]))
  have hE : r.effect.eval (r.extendResult v).effects =
      r.effect.eval v.effects :=
    Effect.eval_support r.effect (r.extendResult v) v
      (by intro i hi; exact ha.2 i (by
        simp [Output.supportEffects, hi]))
  apply (r.canonicalCondition_iff (r.extendResult v)).2
  refine ⟨hC, ?_, ?_⟩
  · calc
      (r.extendResult v).types r.resultTypeName = r.ty.eval v := by
        simp [Output.extendResult, Function.update]
      _ = r.ty.eval (r.extendResult v) := hT.symm
  · calc
      (r.extendResult v).effects r.resultEffectName =
          r.effect.eval v.effects := by
        simp [Output.extendResult, Function.update]
      _ = r.effect.eval (r.extendResult v).effects := hE.symm

def Output.canonical {X : ConstraintSystem} (r : Output X) : Output X :=
  { ty := .var r.resultTypeName
    effect := Poly.Effect.var r.resultEffectName
    condition := r.canonicalCondition
    next := ⟨r.resultTypeName + 1, r.resultEffectName + 1⟩ }

def Context.Closed {X : ConstraintSystem} (Γ : Context X) : Prop :=
  Γ.freeTypes = ∅ ∧ Γ.freeEffects = ∅

theorem Output.canonical_principal {X : ConstraintSystem}
    (Γ : Context X) (hClosed : Γ.Closed)
    (r : Output X) (C : X.Formula) (τ : Ty) (ε : Effect)
    (h : r.MoreGeneralThan Γ C τ ε) :
    r.canonical.MoreGeneralThan Γ C τ ε := by
  intro vd hC
  obtain ⟨wg, _, _, hwg, hty, heff⟩ := h vd hC
  let w := r.extendResult wg
  have hw : X.holds r.canonicalCondition w :=
    r.extendResult_solution wg hwg
  refine ⟨w, ?_, ?_, hw, ?_, ?_⟩
  · intro i hi
    simp [hClosed.1] at hi
  · intro i hi
    simp [hClosed.2] at hi
  · change w.types r.resultTypeName = τ.eval vd
    calc
      w.types r.resultTypeName = r.ty.eval wg := by
        simp [w, Output.extendResult, Function.update]
      _ = τ.eval vd := hty
  · have hresult : w.effects r.resultEffectName = ε.eval vd.effects := by
      calc
        w.effects r.resultEffectName = r.effect.eval wg.effects := by
          simp [w, Output.extendResult, Function.update]
        _ = ε.eval vd.effects := heff
    simpa [Output.canonical, Poly.Effect.eval, Poly.Effect.var] using hresult

/-- Both output names are semantically observable in a satisfiable canonical
constraint. This is the step needed to recover the output type and effect
after principal normalization. -/
theorem Output.resultTypeName_semFree {X : ConstraintSystem}
    (r : Output X) (v : Valuation)
    (hv : X.holds r.canonicalCondition v) :
    X.SemFreeType r.canonicalCondition r.resultTypeName := by
  let t : GroundTy := if v.types r.resultTypeName = .atom 0 then
    .atom 1 else .atom 0
  have htne : t ≠ v.types r.resultTypeName := by
    simp only [t]
    split_ifs with h
    · rw [h]; decide
    · exact Ne.symm h
  let bad : Valuation :=
    { v with types := Function.update v.types r.resultTypeName t }
  have hEval : r.ty.eval bad = r.ty.eval v := by
    apply Ty.eval_support r.ty bad v
    · intro i hi
      have hne : i ≠ r.resultTypeName :=
        Nat.ne_of_lt (r.resultTypeName_fresh i (by
          simp [Output.supportTypes, hi]))
      simp [bad, Function.update, hne]
    · intro i _
      rfl
  have hfail : ¬ X.holds r.canonicalCondition bad := by
    intro hb
    have hbt := (r.canonicalCondition_iff bad).mp hb |>.2.1
    have hvt := (r.canonicalCondition_iff v).mp hv |>.2.1
    have heq : t = v.types r.resultTypeName := by
      calc
        t = bad.types r.resultTypeName := by
          simp [bad, Function.update]
        _ = r.ty.eval bad := hbt
        _ = r.ty.eval v := hEval
        _ = v.types r.resultTypeName := hvt.symm
    exact htne heq
  refine ⟨bad, v.types r.resultTypeName, hfail, ?_⟩
  have hrestore :
      {bad with types := (Function.update bad.types
        r.resultTypeName (v.types r.resultTypeName))} = v := by
    cases v with
    | mk vt ve =>
        simp only [bad]
        congr 1
        funext i
        by_cases hi : i = r.resultTypeName
        · subst i; simp [Function.update]
        · simp [Function.update, hi]
  rw [hrestore]
  exact hv

theorem Output.resultEffectName_semFree {X : ConstraintSystem}
    (r : Output X) (v : Valuation)
    (hv : X.holds r.canonicalCondition v) :
    X.SemFreeEffect r.canonicalCondition r.resultEffectName := by
  let εbad : Finset Op :=
    if 0 ∈ v.effects r.resultEffectName then ∅ else {0}
  have hene : εbad ≠ v.effects r.resultEffectName := by
    by_cases h0 : 0 ∈ v.effects r.resultEffectName
    · simp only [εbad, h0, ↓reduceIte]
      intro he
      rw [← he] at h0
      simp at h0
    · simp only [εbad, h0, ↓reduceIte]
      intro he
      apply h0
      rw [← he]
      simp
  let bad : Valuation :=
    { v with effects := Function.update v.effects r.resultEffectName εbad }
  have hEval : r.effect.eval bad.effects = r.effect.eval v.effects := by
    apply Effect.eval_support r.effect bad v
    intro i hi
    have hne : i ≠ r.resultEffectName :=
      Nat.ne_of_lt (r.resultEffectName_fresh i (by
        simp [Output.supportEffects, hi]))
    simp [bad, Function.update, hne]
  have hfail : ¬ X.holds r.canonicalCondition bad := by
    intro hb
    have hbe := (r.canonicalCondition_iff bad).mp hb |>.2.2
    have hve := (r.canonicalCondition_iff v).mp hv |>.2.2
    have heq : εbad = v.effects r.resultEffectName := by
      calc
        εbad = bad.effects r.resultEffectName := by
          simp [bad, Function.update]
        _ = r.effect.eval bad.effects := hbe
        _ = r.effect.eval v.effects := hEval
        _ = v.effects r.resultEffectName := hve.symm
    exact hene heq
  refine ⟨bad, v.effects r.resultEffectName, hfail, ?_⟩
  have hrestore :
      {bad with effects := (Function.update bad.effects
        r.resultEffectName (v.effects r.resultEffectName))} = v := by
    cases v with
    | mk vt ve =>
        simp only [bad]
        congr 1
        funext i
        by_cases hi : i = r.resultEffectName
        · subst i; simp [Function.update]
        · simp [Function.update, hi]
  rw [hrestore]
  exact hv

def NormalForm.groundWith {X : ConstraintSystem}
    (R : X.Formula) (v : Valuation) : X.NormalForm :=
  ⟨R, v.groundSubst⟩

theorem NormalForm.groundWith_represents {X : ConstraintSystem}
    (R : X.Formula) (hR : ∀ w, X.holds R w)
    (v : Valuation) :
    (NormalForm.groundWith R v).Represents v := by
  exact ⟨v, hR v, (v.groundSubst_pullback v).symm⟩

theorem NormalForm.groundWith_soundFor {X : ConstraintSystem}
    (R D : X.Formula) (v : Valuation) (hv : X.holds D v) :
    (NormalForm.groundWith R v).SoundFor D := by
  intro u hu
  obtain ⟨w, _, he⟩ := hu
  change u = w.pullbackSubst v.groundSubst at he
  rw [v.groundSubst_pullback w] at he
  subst u
  exact hv

/-- HM(X)'s principal constraint property gives projection completeness on
every semantically free name, using a valid solved form as the comparison
normal form. -/
theorem NormalForm.principal_projects_solution {X : ConstraintSystem}
    (Solved : X.Formula → Prop)
    (hTrue : ∃ R, Solved R ∧ ∀ v, X.holds R v)
    (D : X.Formula) (n : X.NormalForm)
    (hp : n.IsPrincipal Solved D)
    (v : Valuation) (hv : X.holds D v) :
    ∃ u, n.Represents u ∧
      (∀ i, X.SemFreeType D i → u.types i = v.types i) ∧
      (∀ i, X.SemFreeEffect D i → u.effects i = v.effects i) := by
  obtain ⟨R, hR, hvalid⟩ := hTrue
  have hm : (NormalForm.groundWith R v).IsNormalForm Solved D :=
    ⟨hR, NormalForm.groundWith_soundFor R D v hv⟩
  exact hp.2 (NormalForm.groundWith R v) hm v
    (NormalForm.groundWith_represents R hvalid v)

def NormalForm.reconstruct {X : ConstraintSystem}
    (n : X.NormalForm) (r : Output X) : Output X :=
  { ty := r.ty.subst n.subst
    effect := r.effect.subst n.subst.effects
    condition := n.residual
    next := r.next }

theorem NormalForm.reconstruct_sound {X : ConstraintSystem}
    (n : X.NormalForm) (r : Output X)
    (h : n.SoundFor r.condition) (w : Valuation)
    (hw : X.holds n.residual w) :
    X.holds r.condition (w.pullbackSubst n.subst) ∧
    (NormalForm.reconstruct n r).ty.eval w =
      r.ty.eval (w.pullbackSubst n.subst) ∧
    (NormalForm.reconstruct n r).effect.eval w.effects =
      r.effect.eval (w.pullbackSubst n.subst).effects := by
  constructor
  · exact h _ ⟨w, hw, rfl⟩
  constructor
  · exact Ty.eval_subst r.ty n.subst w
  · exact Effect.eval_subst r.effect n.subst.effects w.effects

/-- The normalization step preserves the principal result type and effect.
This theorem is fully parametric in X; it assumes only the principal normal
form property used by HM(X). -/
theorem NormalForm.reconstruct_canonical_principal
    {X : ConstraintSystem}
    (Solved : X.Formula → Prop)
    (hTrue : ∃ R, Solved R ∧ ∀ v, X.holds R v)
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (r : Output X) (n : X.NormalForm)
    (hp : n.IsPrincipal Solved r.canonicalCondition)
    (C : X.Formula) (τ : Ty) (ε : Effect)
    (hr : r.canonical.MoreGeneralThan Γ C τ ε) :
    (NormalForm.reconstruct n r.canonical).MoreGeneralThan Γ C τ ε := by
  intro vd hC
  obtain ⟨vg, _, _, hg, ht, he⟩ := hr vd hC
  obtain ⟨u, hu, hut, hue⟩ :=
    NormalForm.principal_projects_solution Solved hTrue
      r.canonicalCondition n hp vg hg
  obtain ⟨w, hw, huw⟩ := hu
  refine ⟨w, ?_, ?_, hw, ?_, ?_⟩
  · intro i hi
    simp [hΓClosed.1] at hi
  · intro i hi
    simp [hΓClosed.2] at hi
  · change ((Ty.var r.resultTypeName).subst n.subst).eval w =
      τ.eval vd
    calc
      ((Ty.var r.resultTypeName).subst n.subst).eval w =
          (Ty.var r.resultTypeName).eval
            (w.pullbackSubst n.subst) :=
        Ty.eval_subst _ _ _
      _ = u.types r.resultTypeName := by rw [← huw]; rfl
      _ = vg.types r.resultTypeName :=
        hut _ (r.resultTypeName_semFree vg hg)
      _ = τ.eval vd := ht
  · change ((Poly.Effect.var r.resultEffectName).subst
      n.subst.effects).eval w.effects = ε.eval vd.effects
    calc
      ((Poly.Effect.var r.resultEffectName).subst
          n.subst.effects).eval w.effects =
          (Poly.Effect.var r.resultEffectName).eval
            (w.pullbackSubst n.subst).effects :=
        Effect.eval_subst _ _ _
      _ = u.effects r.resultEffectName := by
        rw [← huw]
        simp [Poly.Effect.eval, Poly.Effect.var]
      _ = vg.effects r.resultEffectName :=
        hue _ (r.resultEffectName_semFree vg hg)
      _ = ε.eval vd.effects := by
        simpa [Output.canonical, Poly.Effect.eval,
          Poly.Effect.var] using he

/-- Conditional form of the full principal inference theorem: once the
generated result is principal for all declarative typings, principal HM(X)
normalization gives a principal reconstructed result. -/
theorem Output.normalized_principal_of_mono
    {sig : Signature} {X : ConstraintSystem}
    (N : X.PrincipalNormalizer)
    (hTrue : ∃ R, N.solved R ∧ ∀ v, X.holds R v)
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (r : Output X) (n : X.NormalForm)
    (hMono : ∀ (C : X.Formula) (τ : Ty) (ε : Effect),
      Typing sig X C Γ e τ ε → r.MoreGeneralThan Γ C τ ε)
    (hn : N.normalize r.canonicalCondition = some n) :
    n.IsPrincipal N.solved r.canonicalCondition ∧
    ∀ (C : X.Formula) (τ : Ty) (ε : Effect),
      Typing sig X C Γ e τ ε →
      (NormalForm.reconstruct n r.canonical).MoreGeneralThan Γ C τ ε := by
  have hp := N.principal_result r.canonicalCondition n hn
  refine ⟨hp, ?_⟩
  intro C τ ε h
  exact NormalForm.reconstruct_canonical_principal
    N.solved hTrue Γ hΓClosed r n hp C τ ε
    (r.canonical_principal Γ hΓClosed C τ ε (hMono C τ ε h))

def ComputationScheme.freeTypes {X : ConstraintSystem}
    (σ : X.ComputationScheme) : Finset Nat :=
  (X.freeTypes σ.condition ∪ σ.result.fvTypes) \ σ.typeVars

def ComputationScheme.freeEffects {X : ConstraintSystem}
    (σ : X.ComputationScheme) : Finset Nat :=
  (X.freeEffects σ.condition ∪ σ.result.fvEffects ∪ σ.effect.vars) \
    σ.effectVars

theorem ComputationScheme.generalize_closed {X : ConstraintSystem}
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (C : X.Formula) (τ : Ty) (ε : Effect) :
    ComputationScheme.freeTypes (ComputationScheme.generalize Γ C τ ε) = ∅ ∧
    ComputationScheme.freeEffects (ComputationScheme.generalize Γ C τ ε) = ∅ := by
  constructor
  · simp [ComputationScheme.freeTypes,
      ComputationScheme.generalize, hΓClosed.1]
  · simp [ComputationScheme.freeEffects,
      ComputationScheme.generalize, hΓClosed.2]

def Context.RealizableConstraint {X : ConstraintSystem}
    (Γ : Context X) (C : X.Formula) : Prop :=
  ∀ ρ : Valuation, ∃ w : Valuation,
    (∀ i ∈ Γ.freeTypes, w.types i = ρ.types i) ∧
    (∀ i ∈ Γ.freeEffects, w.effects i = ρ.effects i) ∧
    X.holds C w

theorem Context.realizableConstraint_of_closed {X : ConstraintSystem}
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (C : X.Formula) (hC : ∃ w, X.holds C w) :
    Γ.RealizableConstraint C := by
  obtain ⟨w, hw⟩ := hC
  intro ρ
  refine ⟨w, ?_, ?_, hw⟩
  · intro i hi
    simp [hΓClosed.1] at hi
  · intro i hi
    simp [hΓClosed.2] at hi

inductive ComputationSchemeTyping (sig : Signature)
    (X : ConstraintSystem) (Γ : Context X) (e : Expr) :
    X.ComputationScheme → Prop where
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

theorem ComputationSchemeTyping.ground_sound
    {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {e : Expr} {σ : X.ComputationScheme}
    (h : ComputationSchemeTyping sig X Γ e σ)
    (ρ : Valuation) (t : GroundTy) (η : Finset Op)
    (hi : σ.GroundInstance ρ t η) :
    ∃ (C : X.Formula) (τ : Ty) (ε : Effect) (v : Valuation),
      Typing sig X C Γ e τ ε ∧ X.holds C v ∧
      τ.eval v = t ∧ ε.eval v.effects = η := by
  induction h with
  | generalize ht _ =>
      obtain ⟨v, _, _, hC, hty, heff⟩ := hi
      exact ⟨_, _, _, v, ht, hC, hty, heff⟩
  | subsume _ hsub _ ih =>
      exact ih (hsub ρ t η hi)

theorem ComputationSchemeTyping.has_instance
    {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {e : Expr} {σ : X.ComputationScheme}
    (h : ComputationSchemeTyping sig X Γ e σ) :
    ∃ ρ t η, σ.GroundInstance ρ t η := by
  induction h with
  | generalize ht hreal =>
      let ρ : Valuation := ⟨fun _ => .atom 0, fun _ => ∅⟩
      obtain ⟨w, hct, hce, hC⟩ := hreal ρ
      exact ⟨ρ, _, _,
        ComputationScheme.generalize_instance_of_solution
          Γ _ _ _ ρ w _ _ hct hce hC rfl rfl⟩
  | subsume _ _ hreal _ =>
      exact hreal

theorem ComputationSchemeTyping.principal_of_mono
    {sig : Signature} {X : ConstraintSystem}
    (Γ : Context X) (e : Expr) (r : Output X)
    (hMono : ∀ (C : X.Formula) (τ : Ty) (ε : Effect),
      Typing sig X C Γ e τ ε → r.MoreGeneralThan Γ C τ ε)
    (σ : X.ComputationScheme)
    (hσ : ComputationSchemeTyping sig X Γ e σ) :
    (ComputationScheme.generalize Γ r.condition r.ty r.effect).Subsumes σ := by
  induction hσ with
  | generalize ht _ =>
      exact r.moreGeneralThan_generalize Γ _ _ _
        (hMono _ _ _ ht)
  | subsume _ hsub _ ih =>
      intro ρ t η hi
      exact ih ρ t η (hsub ρ t η hi)

theorem NormalForm.raw_moreGeneralThan_reconstruction
    {X : ConstraintSystem}
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (r : Output X) (n : X.NormalForm)
    (h : n.SoundFor r.canonicalCondition) :
    r.MoreGeneralThan Γ n.residual
      (NormalForm.reconstruct n r.canonical).ty
      (NormalForm.reconstruct n r.canonical).effect := by
  intro v hv
  let u := v.pullbackSubst n.subst
  obtain ⟨hD, ht, he⟩ :=
    NormalForm.reconstruct_sound n r.canonical h v hv
  obtain ⟨hC, hresT, hresE⟩ :=
    (r.canonicalCondition_iff u).mp hD
  refine ⟨u, ?_, ?_, hC, ?_, ?_⟩
  · intro i hi
    simp [hΓClosed.1] at hi
  · intro i hi
    simp [hΓClosed.2] at hi
  · calc
      r.ty.eval u = u.types r.resultTypeName := hresT.symm
      _ = r.canonical.ty.eval u := rfl
      _ = (NormalForm.reconstruct n r.canonical).ty.eval v := ht.symm
  · calc
      r.effect.eval u.effects = u.effects r.resultEffectName := hresE.symm
      _ = r.canonical.effect.eval u.effects := by
        simp [Output.canonical, Poly.Effect.eval, Poly.Effect.var]
      _ = (NormalForm.reconstruct n r.canonical).effect.eval v.effects := he.symm

/-- The HM(X) step from a principal generated monotype to a principal
normalized computation scheme. The remaining premise is precisely full
completeness/principality of the generic generator, not an extra solver law. -/
theorem ComputationSchemeTyping.infer_principal_scheme_of_mono
    {sig : Signature} {X : ConstraintSystem}
    (N : X.PrincipalNormalizer)
    (hTrue : ∃ R, N.solved R ∧ ∀ v, X.holds R v)
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (s : Supply) (r : Output X) (n : X.NormalForm)
    (hr : generateFresh sig X Γ e s = some r)
    (hMono : ∀ (C : X.Formula) (τ : Ty) (ε : Effect),
      Typing sig X C Γ e τ ε → r.MoreGeneralThan Γ C τ ε)
    (hn : N.normalize r.canonicalCondition = some n) :
    ∃ σo : X.ComputationScheme,
      σo = ComputationScheme.generalize Γ n.residual
        (NormalForm.reconstruct n r.canonical).ty
        (NormalForm.reconstruct n r.canonical).effect ∧
      ComputationScheme.freeTypes σo = ∅ ∧
      ComputationScheme.freeEffects σo = ∅ ∧
      N.solved n.residual ∧
      ComputationSchemeTyping sig X Γ e σo ∧
      (∀ σ' : X.ComputationScheme,
        ComputationSchemeTyping sig X Γ e σ' →
        σo.Subsumes σ') ∧
      ∃ ρ t η, σo.GroundInstance ρ t η := by
  obtain ⟨hp, hq⟩ := r.normalized_principal_of_mono
    N hTrue Γ hΓClosed e n hMono hn
  let q := NormalForm.reconstruct n r.canonical
  let σo := ComputationScheme.generalize Γ n.residual q.ty q.effect
  obtain ⟨wr, hwr⟩ := N.solved_satisfiable n.residual hp.1.1
  let u := wr.pullbackSubst n.subst
  have hD : X.holds r.canonicalCondition u :=
    hp.1.2 u ⟨wr, hwr, rfl⟩
  have hrawC : X.holds r.condition u :=
    (r.canonicalCondition_iff u).mp hD |>.1
  have hraw : ComputationSchemeTyping sig X Γ e
      (ComputationScheme.generalize Γ r.condition r.ty r.effect) :=
    .generalize (generateFresh_sound hr)
      (Γ.realizableConstraint_of_closed hΓClosed r.condition
        ⟨u, hrawC⟩)
  have hrawSub :
      (ComputationScheme.generalize Γ r.condition r.ty r.effect).Subsumes σo :=
    r.moreGeneralThan_generalize Γ n.residual q.ty q.effect
      (NormalForm.raw_moreGeneralThan_reconstruction Γ hΓClosed r n hp.1.2)
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
      (fun C τ ε htyping => hq C τ ε htyping)
  have hσoClosed := ComputationScheme.generalize_closed Γ hΓClosed
    n.residual q.ty q.effect
  exact ⟨σo, rfl, hσoClosed.1, hσoClosed.2, hp.1.1,
    hσo, hprincipal, hσoReal⟩

theorem PrincipalNormalizer.normalize_some_of_solution
    {X : ConstraintSystem}
    (N : X.PrincipalNormalizer)
    (hTrue : ∃ R, N.solved R ∧ ∀ v, X.holds R v)
    (D : X.Formula) (v : Valuation) (hv : X.holds D v) :
    ∃ n : X.NormalForm, N.normalize D = some n := by
  obtain ⟨R, hR, _⟩ := hTrue
  have hform : ∃ n : X.NormalForm,
      n.IsNormalForm N.solved D :=
    ⟨NormalForm.groundWith R v, hR,
      NormalForm.groundWith_soundFor R D v hv⟩
  have hnotnone : N.normalize D ≠ none := by
    intro hn
    exact (N.failure D).mp hn hform
  cases hn : N.normalize D with
  | none => exact False.elim (hnotnone hn)
  | some n => exact ⟨n, rfl⟩

/-- Once generic monotype completeness is available, no further constraint
assumptions are needed to obtain the full principal computation scheme. -/
theorem ComputationSchemeTyping.infer_principal_scheme_exists_of_mono
    {sig : Signature} {X : ConstraintSystem}
    (N : X.PrincipalNormalizer)
    (hTrue : ∃ R, N.solved R ∧ ∀ v, X.holds R v)
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (s : Supply) (r : Output X)
    (hr : generateFresh sig X Γ e s = some r)
    (hMono : ∀ (C : X.Formula) (τ : Ty) (ε : Effect),
      Typing sig X C Γ e τ ε → r.MoreGeneralThan Γ C τ ε)
    (C₀ : X.Formula) (τ₀ : Ty) (ε₀ : Effect)
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀)
    (v : Valuation) (hv : X.holds C₀ v) :
    ∃ (n : X.NormalForm) (σo : X.ComputationScheme),
      N.normalize r.canonicalCondition = some n ∧
      σo = ComputationScheme.generalize Γ n.residual
        (NormalForm.reconstruct n r.canonical).ty
        (NormalForm.reconstruct n r.canonical).effect ∧
      ComputationScheme.freeTypes σo = ∅ ∧
      ComputationScheme.freeEffects σo = ∅ ∧
      ComputationSchemeTyping sig X Γ e σo ∧
      (∀ σ' : X.ComputationScheme,
        ComputationSchemeTyping sig X Γ e σ' →
        σo.Subsumes σ') ∧
      ∃ ρ t η, σo.GroundInstance ρ t η := by
  obtain ⟨w, _, _, hw, _, _⟩ := hMono C₀ τ₀ ε₀ h₀ v hv
  have hcanon : X.holds r.canonicalCondition (r.extendResult w) :=
    r.extendResult_solution w hw
  obtain ⟨n, hn⟩ := PrincipalNormalizer.normalize_some_of_solution
    N hTrue r.canonicalCondition (r.extendResult w) hcanon
  obtain ⟨σo, hσ, hft, hfe, _, htyping, hprincipal, hreal⟩ :=
    ComputationSchemeTyping.infer_principal_scheme_of_mono
      N hTrue Γ hΓClosed e s r n hr hMono hn
  exact ⟨n, σo, hn, hσ, hft, hfe, htyping, hprincipal, hreal⟩

end SystemFXi.EHMX.Generic
