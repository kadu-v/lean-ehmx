import SystemFXi.EHMX.GenericPrincipal

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

/-- The supply is above all names already used by the generated context and
by operation declarations that the expression can encounter. -/
structure BoundedInputs (sig : Signature) (X : ConstraintSystem)
    (Γ : Context X) (ops : Finset Op) (s : Supply) : Prop where
  contextTypes : ∀ σ ∈ Γ, ∀ i ∈ σ.usedTypes, i < s.types
  contextEffects : ∀ σ ∈ Γ, ∀ i ∈ σ.usedEffects, i < s.effects
  signatureTypes : ∀ op ∈ ops, ∀ decl, sig op = some decl →
    ∀ i ∈ decl.usedTypes, i < s.types
  signatureEffects : ∀ op ∈ ops, ∀ decl, sig op = some decl →
    ∀ i ∈ decl.usedEffects, i < s.effects

theorem BoundedInputs.mono {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {ops : Finset Op} {s t : Supply}
    (h : BoundedInputs sig X Γ ops s)
    (hst : s.types ≤ t.types ∧ s.effects ≤ t.effects) :
    BoundedInputs sig X Γ ops t := by
  constructor
  · intro σ hσ i hi
    exact lt_of_lt_of_le (h.contextTypes σ hσ i hi) hst.1
  · intro σ hσ i hi
    exact lt_of_lt_of_le (h.contextEffects σ hσ i hi) hst.2
  · intro op hop decl hdecl i hi
    exact lt_of_lt_of_le
      (h.signatureTypes op hop decl hdecl i hi) hst.1
  · intro op hop decl hdecl i hi
    exact lt_of_lt_of_le
      (h.signatureEffects op hop decl hdecl i hi) hst.2

theorem BoundedInputs.signature {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (h : BoundedInputs sig X Γ ops s)
    (op : Op) (hop : op ∈ ops) (decl : OpDecl)
    (hd : sig op = some decl) :
    (∀ i ∈ decl.usedTypes, i < s.types) ∧
    (∀ i ∈ decl.usedEffects, i < s.effects) :=
  ⟨h.signatureTypes op hop decl hd,
    h.signatureEffects op hop decl hd⟩

private theorem foldl_union_mem {α : Type}
    (f : α → Finset Nat) (xs : List α) (acc : Finset Nat) (i : Nat) :
    i ∈ xs.foldl (fun names x => names ∪ f x) acc ↔
      i ∈ acc ∨ ∃ x ∈ xs, i ∈ f x := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
      aesop

theorem BoundedInputs.seed {sig : Signature} {X : ConstraintSystem}
    (Γ : Context X) (e : Expr) (s : Supply) :
    BoundedInputs sig X Γ e.ops (Supply.seed s sig Γ e) := by
  constructor
  · intro σ hσ i hi
    have hm : i ∈ Γ.foldl (fun a σ => a ∪ σ.usedTypes) ∅ :=
      (foldl_union_mem Scheme.usedTypes Γ ∅ i).mpr
        (Or.inr ⟨σ, hσ, hi⟩)
    have hs : i ≤
        ((Γ.foldl (fun a σ => a ∪ σ.usedTypes) ∅) ∪
          e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedTypes)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_left _ hm)
    dsimp [Supply.seed]
    omega

  · intro σ hσ i hi
    have hm : i ∈ Γ.foldl (fun a σ => a ∪ σ.usedEffects) ∅ :=
      (foldl_union_mem Scheme.usedEffects Γ ∅ i).mpr
        (Or.inr ⟨σ, hσ, hi⟩)
    have hs : i ≤
        ((Γ.foldl (fun a σ => a ∪ σ.usedEffects) ∅) ∪
          e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedEffects)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_left _ hm)
    dsimp [Supply.seed]
    omega

  · intro op hop decl hd i hi
    have hm : i ∈ e.ops.biUnion
        (fun op => (sig op).elim ∅ OpDecl.usedTypes) :=
      Finset.mem_biUnion.mpr ⟨op, hop, by simp [hd, hi]⟩
    have hs : i ≤
        ((Γ.foldl (fun a σ => a ∪ σ.usedTypes) ∅) ∪
          e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedTypes)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_right _ hm)
    dsimp [Supply.seed]
    omega
  · intro op hop decl hd i hi
    have hm : i ∈ e.ops.biUnion
        (fun op => (sig op).elim ∅ OpDecl.usedEffects) :=
      Finset.mem_biUnion.mpr ⟨op, hop, by simp [hd, hi]⟩
    have hs : i ≤
        ((Γ.foldl (fun a σ => a ∪ σ.usedEffects) ∅) ∪
          e.ops.biUnion (fun op => (sig op).elim ∅ OpDecl.usedEffects)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_right _ hm)
    dsimp [Supply.seed]
    omega

theorem BoundedInputs.context_free_below
    {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (hb : BoundedInputs sig X Γ ops s) :
    (∀ i ∈ Γ.freeTypes, i < s.types) ∧
    (∀ i ∈ Γ.freeEffects, i < s.effects) := by
  constructor
  · intro i hi
    rcases (foldl_union_mem Scheme.freeTypes Γ ∅ i).mp hi with
      hnil | ⟨σ, hσ, hfv⟩
    · simp at hnil
    · exact hb.contextTypes σ hσ i
        (σ.freeTypes_subset_usedTypes hfv)
  · intro i hi
    rcases (foldl_union_mem Scheme.freeEffects Γ ∅ i).mp hi with
      hnil | ⟨σ, hσ, hfv⟩
    · simp at hnil
    · exact hb.contextEffects σ hσ i
        (σ.freeEffects_subset_usedEffects hfv)

theorem BoundedInputs.consMono
    {sig : Signature} {X : ConstraintSystem}
    (hAtom : X.LawfulGeneratedFV)
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (hb : BoundedInputs sig X Γ ops s) (τ : Ty)
    (ht : ∀ i ∈ τ.fvTypes, i < s.types)
    (he : ∀ i ∈ τ.fvEffects, i < s.effects) :
    BoundedInputs sig X (Scheme.mono τ :: Γ) ops s := by
  constructor
  · intro σ hσ i hi
    rcases List.mem_cons.mp hσ with rfl | hΓ
    · simp [Scheme.usedTypes, Scheme.mono,
        hAtom.trivial_types] at hi
      exact ht i hi
    · exact hb.contextTypes σ hΓ i hi
  · intro σ hσ i hi
    rcases List.mem_cons.mp hσ with rfl | hΓ
    · simp [Scheme.usedEffects, Scheme.mono,
        hAtom.trivial_effects] at hi
      exact he i hi
    · exact hb.contextEffects σ hΓ i hi
  · exact hb.signatureTypes
  · exact hb.signatureEffects

theorem BoundedInputs.consGeneralize
    {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (hb : BoundedInputs sig X Γ ops s)
    (c : X.Formula) (τ : Ty)
    (ht : ∀ i ∈ τ.fvTypes ∪ X.freeTypes c, i < s.types)
    (he : ∀ i ∈ τ.fvEffects ∪ X.freeEffects c,
      i < s.effects) :
    BoundedInputs sig X
      (Scheme.generalize Γ c τ :: Γ) ops s := by
  constructor
  · intro σ hσ i hi
    rcases List.mem_cons.mp hσ with rfl | hΓ
    · have h : i ∈ τ.fvTypes ∪ X.freeTypes c := by
        simp [Scheme.usedTypes, Scheme.generalize] at hi ⊢
        aesop
      exact ht i h
    · exact hb.contextTypes σ hΓ i hi
  · intro σ hσ i hi
    rcases List.mem_cons.mp hσ with rfl | hΓ
    · have h : i ∈ τ.fvEffects ∪ X.freeEffects c := by
        simp [Scheme.usedEffects, Scheme.generalize] at hi ⊢
        aesop
      exact he i h
    · exact hb.contextEffects σ hΓ i hi
  · exact hb.signatureTypes
  · exact hb.signatureEffects

theorem Context.moreGeneralAt_below
    {sig : Signature} {X : ConstraintSystem}
    (Γg Γd : Context X) (ops : Finset Op) (s : Supply)
    (hb : BoundedInputs sig X Γg ops s)
    (vg wg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd)
    (ht : ∀ i, i < s.types → vg.types i = wg.types i)
    (he : ∀ i, i < s.effects → vg.effects i = wg.effects i) :
    Γg.MoreGeneralAt Γd wg vd := by
  apply Context.moreGeneralAt_support Γg Γd vg wg vd vd hctx
  · intro σ hσ i hi
    exact ht i (hb.contextTypes σ hσ i
      (σ.freeTypes_subset_usedTypes hi))
  · intro σ hσ i hi
    exact he i (hb.contextEffects σ hσ i
      (σ.freeEffects_subset_usedEffects hi))
  · intro σ hσ i hi; rfl
  · intro σ hσ i hi; rfl

/-- Supply-indexed semantic completeness. Generation may assign fresh names
but keeps all assignments below its starting supply unchanged. -/
def Output.CoversAt {X : ConstraintSystem} (Γg Γd : Context X)
    (C : X.Formula) (s : Supply) (r : Output X)
    (τ : Ty) (ε : Effect) : Prop :=
  ∀ vg vd, Γg.MoreGeneralAt Γd vg vd → X.holds C vd →
    ∃ wg : Valuation,
      (∀ i, i < s.types → vg.types i = wg.types i) ∧
      (∀ i, i < s.effects → vg.effects i = wg.effects i) ∧
      X.holds r.condition wg ∧
      r.ty.eval wg = τ.eval vd ∧
      r.effect.eval wg.effects = ε.eval vd.effects

theorem Output.CoversAt.toAcross
    {sig : Signature} {X : ConstraintSystem}
    (Γg Γd : Context X) (C : X.Formula)
    (ops : Finset Op) (s : Supply) (r : Output X)
    (τ : Ty) (ε : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (h : r.CoversAt Γg Γd C s τ ε) :
    GeneratedCoversAcross Γg Γd C r.condition
      r.ty τ r.effect ε := by
  intro vg vd hctx hC
  rcases h vg vd hctx hC with
    ⟨wg, ht, he, hCg, hTy, hEff⟩
  have hbelow := hb.context_free_below
  exact ⟨wg, (fun i hi => (ht i (hbelow.1 i hi)).symm),
    (fun i hi => (he i (hbelow.2 i hi)).symm),
    hCg, hTy, hEff⟩

/-- Lambda case of generic supply-indexed completeness. -/
theorem Output.CoversAt.lam {sig : Signature} {X : ConstraintSystem}
    (Γg Γd : Context X) (C : X.Formula)
    (ops : Finset Op) (s : Supply)
    (rb : Output X) (a b : Ty) (ε : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (hbody : rb.CoversAt
      (Scheme.mono (.var s.types) :: Γg)
      (Scheme.mono a :: Γd) C
      {s with types := s.types + 1} b ε) :
    (⟨.arr (.var s.types) rb.effect rb.ty, ∅,
      rb.condition, rb.next⟩ : Output X).CoversAt
      Γg Γd C s (.arr a ε b) ∅ := by
  intro vg vd hctx hC
  let v' : Valuation :=
    { vg with types := Function.update vg.types s.types (a.eval vd) }
  have hfixedT : ∀ i, i < s.types →
      vg.types i = v'.types i := by
    intro i hi
    have hne : i ≠ s.types := by omega
    simp [v', Function.update, hne]
  have hfixedE : ∀ i, i < s.effects →
      vg.effects i = v'.effects i := by
    intro i hi
    rfl
  have hctx' := Context.moreGeneralAt_below
    Γg Γd ops s hb vg v' vd hctx hfixedT hfixedE
  have hmono :
      (Scheme.mono (X := X) (.var s.types)).MoreGeneralAt
        (Scheme.mono a) v' vd := by
    apply (Scheme.mono_moreGeneralAt_iff _ _ v' vd).mpr
    simp [Ty.eval, v']
  have hctxBody : Context.MoreGeneralAt
      (Scheme.mono (.var s.types) :: Γg)
      (Scheme.mono a :: Γd) v' vd :=
    List.Forall₂.cons hmono hctx'
  rcases hbody v' vd hctxBody hC with
    ⟨w, hbt, hbe, hCb, hTb, hEb⟩
  refine ⟨w, ?_, ?_, hCb, ?_, rfl⟩
  · intro i hi
    exact (hfixedT i hi).trans
      (hbt i (by dsimp; omega))
  · intro i hi
    exact (hfixedE i hi).trans
      (hbe i (by dsimp; omega))
  · have hparam : w.types s.types = a.eval vd := by
      have hkeep := hbt s.types (by dsimp; omega)
      have hset : v'.types s.types = a.eval vd := by
        simp [v']
      exact hkeep.symm.trans hset
    simp [Ty.eval, hparam, hTb, hEb]

/-- Later assignments preserving a result's free names preserve its
constraint, inferred type, and inferred effect. -/
theorem Output.semantic_frame {X : ConstraintSystem}
    (r : Output X) (v w : Valuation)
    (ht : ∀ i ∈ r.supportTypes, v.types i = w.types i)
    (he : ∀ i ∈ r.supportEffects, v.effects i = w.effects i) :
    (X.holds r.condition v ↔ X.holds r.condition w) ∧
      r.ty.eval v = r.ty.eval w ∧
      r.effect.eval v.effects = r.effect.eval w.effects := by
  constructor
  · exact X.free_support r.condition v w
      (fun i hi => ht i (Finset.mem_union_right _ hi))
      (fun i hi => he i (by
        simp [Output.supportEffects, hi]))
  constructor
  · exact Ty.eval_support r.ty v w
      (fun i hi => ht i (Finset.mem_union_left _ hi))
      (fun i hi => he i (by simp [Output.supportEffects, hi]))
  · exact Effect.eval_support r.effect v w
      (fun i hi => he i (by simp [Output.supportEffects, hi]))

theorem Output.semantic_frame_of_below {X : ConstraintSystem}
    (r : Output X) (v w : Valuation)
    (hboundT : ∀ i ∈ r.supportTypes, i < r.next.types)
    (hboundE : ∀ i ∈ r.supportEffects, i < r.next.effects)
    (hfixedT : ∀ i, i < r.next.types → v.types i = w.types i)
    (hfixedE : ∀ i, i < r.next.effects → v.effects i = w.effects i) :
    (X.holds r.condition v ↔ X.holds r.condition w) ∧
      r.ty.eval v = r.ty.eval w ∧
      r.effect.eval v.effects = r.effect.eval w.effects :=
  r.semantic_frame v w
    (fun i hi => hfixedT i (hboundT i hi))
    (fun i hi => hfixedE i (hboundE i hi))

/-- Restrict a clause solution to the names allocated after the clause
started, preserving the ground result and effect. -/
theorem Output.localize_solution {X : ConstraintSystem}
    (r : Output X) (s : Supply) (base w : Valuation)
    (hboundT : ∀ i ∈ r.supportTypes, i < r.next.types)
    (hboundE : ∀ i ∈ r.supportEffects, i < r.next.effects)
    (hbelowT : ∀ i, i < s.types → base.types i = w.types i)
    (hbelowE : ∀ i, i < s.effects → base.effects i = w.effects i)
    (hC : X.holds r.condition w) :
    let localTypes := Finset.range r.next.types \ Finset.range s.types
    let localEffects := Finset.range r.next.effects \ Finset.range s.effects
    ∃ v : Valuation,
      (∀ i, i ∉ localTypes → v.types i = base.types i) ∧
      (∀ i, i ∉ localEffects → v.effects i = base.effects i) ∧
      X.holds r.condition v ∧
      r.ty.eval v = r.ty.eval w ∧
      r.effect.eval v.effects = r.effect.eval w.effects := by
  dsimp
  let localTypes := Finset.range r.next.types \ Finset.range s.types
  let localEffects := Finset.range r.next.effects \ Finset.range s.effects
  let v : Valuation :=
    ⟨fun i => if i ∈ localTypes then w.types i else base.types i,
      fun i => if i ∈ localEffects then w.effects i else base.effects i⟩
  have hAgreeT : ∀ i, i < r.next.types →
      v.types i = w.types i := by
    intro i hi
    by_cases hlow : i < s.types
    · have hnot : i ∉ localTypes := by
        simp [localTypes, hlow]
      simpa [v, hnot] using hbelowT i hlow
    · have hmem : i ∈ localTypes := by
        simp [localTypes, hi]
        omega
      simp [v, hmem]
  have hAgreeE : ∀ i, i < r.next.effects →
      v.effects i = w.effects i := by
    intro i hi
    by_cases hlow : i < s.effects
    · have hnot : i ∉ localEffects := by
        simp [localEffects, hlow]
      simpa [v, hnot] using hbelowE i hlow
    · have hmem : i ∈ localEffects := by
        simp [localEffects, hi]
        omega
      simp [v, hmem]
  have hframe := r.semantic_frame_of_below w v
    hboundT hboundE
    (fun i hi => (hAgreeT i hi).symm)
    (fun i hi => (hAgreeE i hi).symm)
  refine ⟨v, ?_, ?_, hframe.1.mp hC,
    hframe.2.1.symm, hframe.2.2.symm⟩
  · intro i hi
    change i ∉ localTypes at hi
    simp [v, hi]
  · intro i hi
    change i ∉ localEffects at hi
    simp [v, hi]

/-- One declarative operation-clause instance yields the projected generated
clause constraint. Only names allocated within the clause may vary. -/
theorem Output.CoversAt.project_clause {X : ConstraintSystem}
    (Γg Γd : Context X) (D : X.Formula)
    (s : Supply) (r : Output X) (τ a : Ty) (ε χ : Effect)
    (hboundT : ∀ i ∈ r.supportTypes, i < r.next.types)
    (hboundE : ∀ i ∈ r.supportEffects, i < r.next.effects)
    (haT : ∀ i ∈ a.fvTypes, i < s.types)
    (haE : ∀ i ∈ a.fvEffects, i < s.effects)
    (hχ : ∀ i ∈ χ.vars, i < s.effects)
    (hcov : r.CoversAt Γg Γd D s τ ε)
    (vg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd)
    (hD : X.holds D vd)
    (htarget : τ.eval vd = a.eval vg)
    (heffect : ε.eval vd.effects ⊆ χ.eval vg.effects) :
    X.holds
      (X.project
        (Finset.range r.next.types \ Finset.range s.types)
        (Finset.range r.next.effects \ Finset.range s.effects)
        (X.combine r.condition
          (X.combine (X.equalType r.ty a)
            (X.includedEffect r.effect χ)))) vg := by
  rcases hcov vg vd hctx hD with
    ⟨w, hbelowT, hbelowE, hC, hTy, hEff⟩
  rcases r.localize_solution s vg w
      hboundT hboundE hbelowT hbelowE hC with
    ⟨v, hlocalT, hlocalE, hCv, hTyV, hEffV⟩
  have ha : a.eval v = a.eval vg :=
    Ty.eval_support a v vg
      (by
        intro i hi
        apply hlocalT i
        have hs := haT i hi
        simp only [Finset.mem_sdiff, Finset.mem_range]
        omega)
      (by
        intro i hi
        apply hlocalE i
        have hs := haE i hi
        simp only [Finset.mem_sdiff, Finset.mem_range]
        omega)
  have hχV : χ.eval v.effects = χ.eval vg.effects :=
    Effect.eval_support χ v vg (by
      intro i hi
      apply hlocalE i
      have hs := hχ i hi
      simp only [Finset.mem_sdiff, Finset.mem_range]
      omega)
  apply (X.projection_iff _ _ _ vg).mpr
  refine ⟨v.types, v.effects, hlocalT, hlocalE,
    (X.combine_iff _ _ _).2 ⟨hCv,
      (X.combine_iff _ _ _).2 ⟨?_, ?_⟩⟩⟩
  · apply (X.equalType_iff _ _ _).2
    exact hTyV.trans (hTy.trans (htarget.trans ha.symm))
  · apply (X.includedEffect_iff _ _ _).2
    rw [hEffV, hEff, hχV]
    exact heffect

def Valuation.assignAt (v : Valuation) (s : Supply)
    (t : GroundTy) (ε : Finset Op) : Valuation :=
  ⟨Function.update v.types s.types t,
    Function.update v.effects s.effects ε⟩

theorem Valuation.assignAt_preserves_below (v : Valuation)
    (s : Supply) (t : GroundTy) (ε : Finset Op) :
    (∀ i, i < s.types →
      v.types i = (Generic.Valuation.assignAt v s t ε).types i) ∧
    (∀ i, i < s.effects →
      v.effects i = (Generic.Valuation.assignAt v s t ε).effects i) := by
  constructor
  · intro i hi
    have hne : i ≠ s.types := by omega
    simp [Generic.Valuation.assignAt, Function.update, hne]
  · intro i hi
    have hne : i ≠ s.effects := by omega
    simp [Generic.Valuation.assignAt, Function.update, hne]

/-- Application extends the two subexpression solutions with its fresh
result-type and latent-effect assignments. -/
theorem Output.app_solution_extend {X : ConstraintSystem}
    (rf rx : Output X)
    (hfBound : (∀ i ∈ rf.supportTypes, i < rf.next.types) ∧
      (∀ i ∈ rf.supportEffects, i < rf.next.effects))
    (hxBound : (∀ i ∈ rx.supportTypes, i < rx.next.types) ∧
      (∀ i ∈ rx.supportEffects, i < rx.next.effects))
    (hnext : rf.next.types ≤ rx.next.types ∧
      rf.next.effects ≤ rx.next.effects)
    (v w : Valuation)
    (hfixedT : ∀ i, i < rf.next.types → v.types i = w.types i)
    (hfixedE : ∀ i, i < rf.next.effects → v.effects i = w.effects i)
    (hf : X.holds rf.condition v) (hx : X.holds rx.condition w)
    (a b : GroundTy) (η : Finset Op)
    (hfun : rf.ty.eval v = .arr a η b)
    (harg : rx.ty.eval w = a) :
    let u := Generic.Valuation.assignAt w rx.next b η
    let out : Output X :=
      ⟨.var rx.next.types,
        rf.effect ∪ rx.effect ∪ Poly.Effect.var rx.next.effects,
        X.combine (X.combine rf.condition rx.condition)
          (X.equalType rf.ty
            (.arr rx.ty (Poly.Effect.var rx.next.effects)
              (.var rx.next.types))),
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩
    (∀ i, i < rx.next.types → w.types i = u.types i) ∧
      (∀ i, i < rx.next.effects → w.effects i = u.effects i) ∧
      X.holds out.condition u ∧
      out.ty.eval u = b ∧
      out.effect.eval u.effects =
        rf.effect.eval v.effects ∪ rx.effect.eval w.effects ∪ η := by
  dsimp
  let u := Generic.Valuation.assignAt w rx.next b η
  have hwu := Generic.Valuation.assignAt_preserves_below w rx.next b η
  have hrfVW := rf.semantic_frame_of_below v w
    hfBound.1 hfBound.2 hfixedT hfixedE
  have hrfWU := rf.semantic_frame_of_below w u
    hfBound.1 hfBound.2
    (fun i hi => hwu.1 i (lt_of_lt_of_le hi hnext.1))
    (fun i hi => hwu.2 i (lt_of_lt_of_le hi hnext.2))
  have hrxWU := rx.semantic_frame_of_below w u
    hxBound.1 hxBound.2 hwu.1 hwu.2
  have hnewT : (Ty.var rx.next.types).eval u = b := by
    simp [Ty.eval, u, Generic.Valuation.assignAt]
  have hnewE :
      (Poly.Effect.var rx.next.effects).eval u.effects = η := by
    simp [Poly.Effect.eval, Poly.Effect.var, u, Generic.Valuation.assignAt]
  refine ⟨hwu.1, hwu.2, ?_, hnewT, ?_⟩
  · apply (X.combine_iff _ _ _).2
    refine ⟨(X.combine_iff _ _ _).2
      ⟨hrfWU.1.mp (hrfVW.1.mp hf), hrxWU.1.mp hx⟩, ?_⟩
    apply (X.equalType_iff _ _ _).2
    change rf.ty.eval u =
      (Ty.arr rx.ty (Poly.Effect.var rx.next.effects)
        (Ty.var rx.next.types)).eval u
    simp only [Ty.eval]
    rw [← hrfWU.2.1, ← hrfVW.2.1, hfun,
      ← hrxWU.2.1, harg, hnewE]
    exact congrArg (GroundTy.arr a η) hnewT.symm
  · change (rf.effect ∪ rx.effect ∪
      Poly.Effect.var rx.next.effects).eval u.effects =
        rf.effect.eval v.effects ∪ rx.effect.eval w.effects ∪ η
    simp only [Effect.eval_union, hnewE]
    rw [← hrfWU.2.2, ← hrfVW.2.2, ← hrxWU.2.2]

/-- The application constructor preserves the support bound whenever the
two subresults do. -/
theorem Output.app_support_below {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (rf rx : Output X)
    (hfT : ∀ i ∈ rf.supportTypes, i < rf.next.types)
    (hfE : ∀ i ∈ rf.supportEffects, i < rf.next.effects)
    (hxT : ∀ i ∈ rx.supportTypes, i < rx.next.types)
    (hxE : ∀ i ∈ rx.supportEffects, i < rx.next.effects)
    (hnext : rf.next.types ≤ rx.next.types ∧
      rf.next.effects ≤ rx.next.effects) :
    let b := Ty.var rx.next.types
    let η := Poly.Effect.var rx.next.effects
    let r : Output X :=
      ⟨b, rf.effect ∪ rx.effect ∪ η,
        X.combine (X.combine rf.condition rx.condition)
          (X.equalType rf.ty (.arr rx.ty η b)),
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i ∈ insert rx.next.types
        (rf.supportTypes ∪ rx.supportTypes) := by
      simp only [Output.supportTypes, Ty.fvTypes, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      rcases hi with rfl | hcon
      · exact Or.inl rfl
      · have hsplit := hFV.combine_types _ _ hcon
        rcases Finset.mem_union.mp hsplit with hleft | heq
        · rcases Finset.mem_union.mp (hFV.combine_types _ _ hleft) with
            hf | hx
          · exact Or.inr (Or.inl (Or.inr hf))
          · exact Or.inr (Or.inr (Or.inr hx))
        · have hty := hAtom.equalType_types _ _ heq
          simp [Ty.fvTypes] at hty
          rcases hty with hnew | hf | hx
          · exact Or.inl hnew
          · exact Or.inr (Or.inl (Or.inl hf))
          · exact Or.inr (Or.inr (Or.inl hx))
    rcases Finset.mem_insert.mp hsub with hnew | hprev
    · omega
    · rcases Finset.mem_union.mp hprev with hf | hx
      · have := hfT i hf
        omega
      · have := hxT i hx
        omega
  · intro i hi
    have hsub : i ∈ insert rx.next.effects
        (rf.supportEffects ∪ rx.supportEffects) := by
      have hbase := hFV.combine_effects
        (X.combine rf.condition rx.condition)
        (X.equalType rf.ty
          (.arr rx.ty (Poly.Effect.var rx.next.effects)
            (.var rx.next.types)))
      have hinner := hFV.combine_effects rf.condition rx.condition
      have heq := hAtom.equalType_effects rf.ty
        (.arr rx.ty (Poly.Effect.var rx.next.effects)
          (.var rx.next.types))
      simp [Output.supportEffects, Ty.fvEffects,
        Poly.Effect.vars_union, Poly.Effect.var] at hi ⊢
      rcases hi with hnew | hf | hx | hc
      · exact Or.inl hnew
      · exact Or.inr (Or.inr (Or.inl hf))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))
      · rcases Finset.mem_union.mp (hbase hc) with hinnerM | heqM
        · rcases Finset.mem_union.mp (hinner hinnerM) with hfC | hxC
          · exact Or.inr (Or.inr (Or.inr (Or.inl hfC)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hxC)))))
        · have ht := heq heqM
          simp [Ty.fvEffects] at ht
          rcases ht with hfTy | hxTy | hnew
          · exact Or.inr (Or.inl hfTy)
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxTy))))
          · exact Or.inl (by simpa [Poly.Effect.var] using hnew)
    rcases Finset.mem_insert.mp hsub with hnew | hprev
    · omega
    · rcases Finset.mem_union.mp hprev with hf | hx
      · have := hfE i hf
        omega
      · have := hxE i hx
        omega

/-- Projection-based variable instantiation remains within the allocated
supply and does not inspect binders inside X formulas. -/
theorem Output.variable_support_below {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (σ : Scheme X) (s : Supply)
    (husedT : ∀ i ∈ σ.usedTypes, i < s.types)
    (husedE : ∀ i ∈ σ.usedEffects, i < s.effects) :
    let ft := renameBound σ.typeVars s.types
    let fe := renameBound σ.effectVars s.effects
    let r : Output X :=
      ⟨(σ.instantiateProjected ft fe).1, ∅,
        (σ.instantiateProjected ft fe).2,
        s.advance σ.typeVars σ.effectVars⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  let ft := renameBound σ.typeVars s.types
  let fe := renameBound σ.effectVars s.effects
  have hadm : σ.AdmissibleRename ft fe :=
    ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩
  constructor
  · intro i hi
    have hs := σ.instantiateProjected_supportTypes hFV hAtom
      ft fe hadm
    have h : i ∈ σ.freeTypes ∪ σ.typeVars.image ft :=
      hs (by simpa [Output.supportTypes, ft, fe] using hi)
    rcases Finset.mem_union.mp h with hfree | hnew
    · exact lt_of_lt_of_le
        (husedT i (σ.freeTypes_subset_usedTypes hfree))
        (Nat.le_of_lt (s.advance_mono
          σ.typeVars σ.effectVars).1)
    · rcases Finset.mem_image.mp hnew with ⟨j, hj, rfl⟩
      exact (s.advance_above_renamed σ.typeVars σ.effectVars).1 j hj
  · intro i hi
    have hs := σ.instantiateProjected_supportEffects hFV hAtom
      ft fe hadm
    have h : i ∈ σ.freeEffects ∪ σ.effectVars.image fe :=
      hs (by simpa [Output.supportEffects, ft, fe] using hi)
    rcases Finset.mem_union.mp h with hfree | hnew
    · exact lt_of_lt_of_le
        (husedE i (σ.freeEffects_subset_usedEffects hfree))
        (Nat.le_of_lt (s.advance_mono
          σ.typeVars σ.effectVars).2)
    · rcases Finset.mem_image.mp hnew with ⟨j, hj, rfl⟩
      exact (s.advance_above_renamed σ.typeVars σ.effectVars).2 j hj

theorem Output.lam_support_below {X : ConstraintSystem}
    (s : Supply) (rb : Output X)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hnext : s.types < rb.next.types) :
    let r : Output X :=
      ⟨.arr (.var s.types) rb.effect rb.ty, ∅,
        rb.condition, rb.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i = s.types ∨ i ∈ rb.supportTypes := by
      simp [Output.supportTypes, Ty.fvTypes] at hi ⊢
      aesop
    rcases hsub with rfl | h
    · exact hnext
    · exact hbT i h
  · intro i hi
    have hsub : i ∈ rb.supportEffects := by
      simp [Output.supportEffects, Ty.fvEffects] at hi ⊢
      aesop
    exact hbE i hsub

theorem Output.letMono_support_below {X : ConstraintSystem}
    (hFV : X.LawfulFV) (r₁ r₂ : Output X)
    (h₁T : ∀ i ∈ r₁.supportTypes, i < r₁.next.types)
    (h₁E : ∀ i ∈ r₁.supportEffects, i < r₁.next.effects)
    (h₂T : ∀ i ∈ r₂.supportTypes, i < r₂.next.types)
    (h₂E : ∀ i ∈ r₂.supportEffects, i < r₂.next.effects)
    (hnext : r₁.next.types ≤ r₂.next.types ∧
      r₁.next.effects ≤ r₂.next.effects) :
    let r : Output X :=
      ⟨r₂.ty, r₁.effect ∪ r₂.effect,
        X.combine r₁.condition r₂.condition, r₂.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i ∈ r₁.supportTypes ∪ r₂.supportTypes := by
      simp only [Output.supportTypes, Finset.mem_union] at hi ⊢
      rcases hi with hty | hc
      · exact Or.inr (Or.inl hty)
      · rcases Finset.mem_union.mp (hFV.combine_types _ _ hc) with
            h₁ | h₂
        · exact Or.inl (Or.inr h₁)
        · exact Or.inr (Or.inr h₂)
    rcases Finset.mem_union.mp hsub with h₁ | h₂
    · exact lt_of_lt_of_le (h₁T i h₁) hnext.1
    · exact h₂T i h₂
  · intro i hi
    have hsub : i ∈ r₁.supportEffects ∪ r₂.supportEffects := by
      have hsplit := hFV.combine_effects r₁.condition r₂.condition
      simp [Output.supportEffects, Poly.Effect.vars_union] at hi ⊢
      rcases hi with hty | heff₁ | heff₂ | hc
      · aesop
      · aesop
      · aesop
      · rcases Finset.mem_union.mp (hsplit hc) with hc₁ | hc₂
        · aesop
        · aesop
    rcases Finset.mem_union.mp hsub with h₁ | h₂
    · exact lt_of_lt_of_le (h₁E i h₁) hnext.2
    · exact h₂E i h₂

theorem Output.letVal_support_below {X : ConstraintSystem}
    (hFV : X.LawfulFV) (Γ : Context X) (r₁ r₂ : Output X)
    (h₁T : ∀ i ∈ r₁.supportTypes, i < r₁.next.types)
    (h₁E : ∀ i ∈ r₁.supportEffects, i < r₁.next.effects)
    (h₂T : ∀ i ∈ r₂.supportTypes, i < r₂.next.types)
    (h₂E : ∀ i ∈ r₂.supportEffects, i < r₂.next.effects)
    (hnext : r₁.next.types ≤ r₂.next.types ∧
      r₁.next.effects ≤ r₂.next.effects) :
    let r : Output X :=
      ⟨r₂.ty, r₂.effect,
        X.combine (Scheme.residual Γ r₁.condition r₁.ty)
          r₂.condition, r₂.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  have hresT : X.freeTypes
      (Scheme.residual Γ r₁.condition r₁.ty) ⊆
      X.freeTypes r₁.condition := by
    intro i hi
    have hp := hFV.project_types
      (Scheme.generalize Γ r₁.condition r₁.ty).typeVars
      (Scheme.generalize Γ r₁.condition r₁.ty).effectVars
      r₁.condition
    exact (Finset.mem_sdiff.mp (hp (by
      simpa [Scheme.residual] using hi))).1
  have hresE : X.freeEffects
      (Scheme.residual Γ r₁.condition r₁.ty) ⊆
      X.freeEffects r₁.condition := by
    intro i hi
    have hp := hFV.project_effects
      (Scheme.generalize Γ r₁.condition r₁.ty).typeVars
      (Scheme.generalize Γ r₁.condition r₁.ty).effectVars
      r₁.condition
    exact (Finset.mem_sdiff.mp (hp (by
      simpa [Scheme.residual] using hi))).1
  constructor
  · intro i hi
    have hsplit : i ∈ r₁.supportTypes ∪ r₂.supportTypes := by
      have hc := hFV.combine_types
        (Scheme.residual Γ r₁.condition r₁.ty) r₂.condition
      simp [Output.supportTypes] at hi ⊢
      rcases hi with hty | hcond
      · aesop
      · rcases Finset.mem_union.mp (hc hcond) with hr | h₂
        · have h₁ := hresT hr
          aesop
        · aesop
    rcases Finset.mem_union.mp hsplit with h₁ | h₂
    · exact lt_of_lt_of_le (h₁T i h₁) hnext.1
    · exact h₂T i h₂
  · intro i hi
    have hsplit : i ∈ r₁.supportEffects ∪ r₂.supportEffects := by
      have hc := hFV.combine_effects
        (Scheme.residual Γ r₁.condition r₁.ty) r₂.condition
      simp [Output.supportEffects] at hi ⊢
      rcases hi with hty | heff | hcond
      · aesop
      · aesop
      · rcases Finset.mem_union.mp (hc hcond) with hr | h₂
        · have h₁ := hresE hr
          aesop
        · aesop
    rcases Finset.mem_union.mp hsplit with h₁ | h₂
    · exact lt_of_lt_of_le (h₁E i h₁) hnext.2
    · exact h₂E i h₂

theorem Output.perform_support_below {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (s : Supply) (decl : OpDecl) (op : Op) (re : Output X)
    (hdeclT : ∀ i ∈ decl.usedTypes, i < s.types)
    (hdeclE : ∀ i ∈ decl.usedEffects, i < s.effects)
    (heT : ∀ i ∈ re.supportTypes, i < re.next.types)
    (heE : ∀ i ∈ re.supportEffects, i < re.next.effects)
    (hnext : (s.advance decl.typeVars decl.effectVars).types ≤
        re.next.types ∧
      (s.advance decl.typeVars decl.effectVars).effects ≤
        re.next.effects) :
    let ρ := renameBound decl.typeVars s.types
    let η := renameBound decl.effectVars s.effects
    let r : Output X :=
      ⟨decl.output.rename ρ η,
        Poly.Effect.singleton op ∪ re.effect,
        X.combine re.condition
          (X.equalType re.ty (decl.input.rename ρ η)), re.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  let ρ := renameBound decl.typeVars s.types
  let η := renameBound decl.effectVars s.effects
  constructor
  · intro i hi
    have hsub : i ∈ re.supportTypes ∪ decl.usedTypes.image ρ := by
      have hc := hFV.combine_types re.condition
        (X.equalType re.ty (decl.input.rename ρ η))
      have heq := hAtom.equalType_types re.ty
        (decl.input.rename ρ η)
      simp [Output.supportTypes, Ty.fvTypes_rename,
        OpDecl.usedTypes, ρ] at hi ⊢
      rcases hi with hout | hcond
      · aesop
      · rcases Finset.mem_union.mp (hc hcond) with hr | hEq
        · aesop
        · rcases Finset.mem_union.mp (heq hEq) with ht | hin
          · aesop
          · rw [Ty.fvTypes_rename] at hin
            aesop
    rcases Finset.mem_union.mp hsub with he | hd
    · exact heT i he
    · rcases Finset.mem_image.mp hd with ⟨j, hj, rfl⟩
      have hlt := s.renameBound_types_below_advance
        decl.typeVars decl.effectVars decl.usedTypes hdeclT j hj
      exact lt_of_lt_of_le (by simpa [ρ] using hlt) hnext.1
  · intro i hi
    have hsub : i ∈ re.supportEffects ∪ decl.usedEffects.image η := by
      have hc := hFV.combine_effects re.condition
        (X.equalType re.ty (decl.input.rename ρ η))
      have heq := hAtom.equalType_effects re.ty
        (decl.input.rename ρ η)
      simp [Output.supportEffects, Ty.fvEffects_rename,
        OpDecl.usedEffects, Poly.Effect.vars_union,
        η] at hi ⊢
      rcases hi with hout | heff | hcond
      · aesop
      · aesop
      · rcases Finset.mem_union.mp (hc hcond) with hr | hEq
        · aesop
        · rcases Finset.mem_union.mp (heq hEq) with ht | hin
          · aesop
          · rw [Ty.fvEffects_rename] at hin
            aesop
    rcases Finset.mem_union.mp hsub with he | hd
    · exact heE i he
    · rcases Finset.mem_image.mp hd with ⟨j, hj, rfl⟩
      have hlt := s.renameBound_effects_below_advance
        decl.typeVars decl.effectVars decl.usedEffects hdeclE j hj
      exact lt_of_lt_of_le (by simpa [η] using hlt) hnext.2

theorem ConstraintSystem.split_freeTypes {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (op : Op) (input rest : Effect) :
    X.freeTypes (X.split op input rest) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have h₁ := hFV.combine_types _ _ hi
  rcases Finset.mem_union.mp h₁ with ha | h₂
  · rw [hAtom.includedEffect_types] at ha
    simp at ha
  · have h₃ := hFV.combine_types _ _ h₂
    rcases Finset.mem_union.mp h₃ with hb | hl
    · rw [hAtom.includedEffect_types] at hb
      simp at hb
    · rw [hAtom.excludes_types] at hl
      simp at hl

theorem ConstraintSystem.split_freeEffects {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (op : Op) (input rest : Effect) :
    X.freeEffects (X.split op input rest) ⊆
      input.vars ∪ rest.vars := by
  intro i hi
  have h₁ := hFV.combine_effects _ _ hi
  rcases Finset.mem_union.mp h₁ with ha | h₂
  · have h := hAtom.includedEffect_effects _ _ ha
    simp at h ⊢
    aesop
  · have h₃ := hFV.combine_effects _ _ h₂
    rcases Finset.mem_union.mp h₃ with hb | hl
    · have h := hAtom.includedEffect_effects _ _ hb
      simp at h ⊢
      aesop
    · have h := hAtom.excludes_effects _ _ hl
      exact Finset.mem_union_right _ h

theorem handlerCondition_freeTypes {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (op : Op) (decl : OpDecl)
    (Cin Cr Co : X.Formula) (τr τo a : Ty)
    (εin εr εo δ χ : Effect)
    (localTypes localEffects : Finset Nat) :
    X.freeTypes (handlerCondition X op decl Cin Cr Co τr τo a
      εin εr εo δ χ localTypes localEffects) ⊆
      X.freeTypes Cin ∪ X.freeTypes Cr ∪ X.freeTypes Co ∪
        τr.fvTypes ∪ τo.fvTypes ∪ a.fvTypes := by
  intro i hi
  unfold handlerCondition at hi
  have h₀ := hFV.combine_types _ _ hi
  rcases Finset.mem_union.mp h₀ with hstart | hrest
  · have h₁ := hFV.combine_types _ _ hstart
    rcases Finset.mem_union.mp h₁ with hc | hr
    · simp [hc]
    · simp [hr]
  · have h₁ := hFV.combine_types _ _ hrest
    rcases Finset.mem_union.mp h₁ with hret | htail
    · have heq := hAtom.equalType_types τr a hret
      simp [Finset.mem_union] at heq ⊢
      aesop
    · have h₂ := hFV.combine_types _ _ htail
      rcases Finset.mem_union.mp h₂ with hclause | heffects
      · have hclause' := hFV.handler_types decl.typeVars
          decl.effectVars localTypes localEffects
          (X.combine Co
            (X.combine (X.equalType τo a)
              (X.includedEffect εo χ))) hclause
        have hinner := (Finset.mem_sdiff.mp hclause').1
        have h₃ := hFV.combine_types _ _ hinner
        rcases Finset.mem_union.mp h₃ with hco | hresult
        · simp [hco]
        · have h₄ := hFV.combine_types _ _ hresult
          rcases Finset.mem_union.mp h₄ with hty | heff
          · have heq := hAtom.equalType_types τo a hty
            simp [Finset.mem_union] at heq ⊢
            aesop
          · rw [hAtom.includedEffect_types] at heff
            simp at heff
      · have h₃ := hFV.combine_types _ _ heffects
        rcases Finset.mem_union.mp h₃ with hsplit | hmore
        · rw [ConstraintSystem.split_freeTypes hFV hAtom op εin δ] at hsplit
          simp at hsplit
        · have h₄ := hFV.combine_types _ _ hmore
          rcases Finset.mem_union.mp h₄ with hδ | hε
          · rw [hAtom.includedEffect_types] at hδ
            simp at hδ
          · rw [hAtom.includedEffect_types] at hε
            simp at hε

theorem handlerCondition_freeEffects {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (op : Op) (decl : OpDecl)
    (Cin Cr Co : X.Formula) (τr τo a : Ty)
    (εin εr εo δ χ : Effect)
    (localTypes localEffects : Finset Nat) :
    X.freeEffects (handlerCondition X op decl Cin Cr Co τr τo a
      εin εr εo δ χ localTypes localEffects) ⊆
      X.freeEffects Cin ∪ X.freeEffects Cr ∪ X.freeEffects Co ∪
        τr.fvEffects ∪ τo.fvEffects ∪ a.fvEffects ∪
        εin.vars ∪ εr.vars ∪ εo.vars ∪ δ.vars ∪ χ.vars := by
  intro i hi
  unfold handlerCondition at hi
  have h₀ := hFV.combine_effects _ _ hi
  rcases Finset.mem_union.mp h₀ with hstart | hrest
  · have h₁ := hFV.combine_effects _ _ hstart
    rcases Finset.mem_union.mp h₁ with hc | hr
    · simp [hc]
    · simp [hr]
  · have h₁ := hFV.combine_effects _ _ hrest
    rcases Finset.mem_union.mp h₁ with hret | htail
    · have heq := hAtom.equalType_effects τr a hret
      simp [Finset.mem_union] at heq ⊢
      aesop
    · have h₂ := hFV.combine_effects _ _ htail
      rcases Finset.mem_union.mp h₂ with hclause | heffects
      · have hclause' := hFV.handler_effects decl.typeVars
          decl.effectVars localTypes localEffects
          (X.combine Co
            (X.combine (X.equalType τo a)
              (X.includedEffect εo χ))) hclause
        have hinner := (Finset.mem_sdiff.mp hclause').1
        have h₃ := hFV.combine_effects _ _ hinner
        rcases Finset.mem_union.mp h₃ with hco | hresult
        · simp [hco]
        · have h₄ := hFV.combine_effects _ _ hresult
          rcases Finset.mem_union.mp h₄ with hty | heff
          · have heq := hAtom.equalType_effects τo a hty
            simp [Finset.mem_union] at heq ⊢
            aesop
          · have h := hAtom.includedEffect_effects εo χ heff
            simp [Finset.mem_union] at h ⊢
            aesop
      · have h₃ := hFV.combine_effects _ _ heffects
        rcases Finset.mem_union.mp h₃ with hsplit | hmore
        · have h := ConstraintSystem.split_freeEffects hFV hAtom
            op εin δ hsplit
          simp [Finset.mem_union] at h ⊢
          aesop
        · have h₄ := hFV.combine_effects _ _ hmore
          rcases Finset.mem_union.mp h₄ with hδ | hε
          · have h := hAtom.includedEffect_effects δ χ hδ
            simp [Finset.mem_union] at h ⊢
            aesop
          · have h := hAtom.includedEffect_effects εr χ hε
            simp [Finset.mem_union] at h ⊢
            aesop

theorem Output.handler_support_below {X : ConstraintSystem}
    (hFV : X.LawfulFV) (hAtom : X.LawfulGeneratedFV)
    (op : Op) (decl : OpDecl) (sb : Supply)
    (rb rr rc : Output X) (localTypes localEffects : Finset Nat)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hrT : ∀ i ∈ rr.supportTypes, i < rr.next.types)
    (hrE : ∀ i ∈ rr.supportEffects, i < rr.next.effects)
    (hcT : ∀ i ∈ rc.supportTypes, i < rc.next.types)
    (hcE : ∀ i ∈ rc.supportEffects, i < rc.next.effects)
    (hnextB : rb.next.types ≤ rc.next.types ∧
      rb.next.effects ≤ rc.next.effects)
    (hnextR : rr.next.types ≤ rc.next.types ∧
      rr.next.effects ≤ rc.next.effects)
    (ha : sb.types < rc.next.types)
    (hδ : sb.effects < rc.next.effects)
    (hχ : sb.effects + 1 < rc.next.effects) :
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    let C := handlerCondition X op decl rb.condition rr.condition
      rc.condition rr.ty rc.ty a rb.effect rr.effect rc.effect
      δ χ localTypes localEffects
    let r : Output X := ⟨a, χ, C, rc.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    simp only [Output.supportTypes, Ty.fvTypes,
      Finset.mem_union, Finset.mem_singleton] at hi
    rcases hi with hnew | hC
    · omega
    have h := handlerCondition_freeTypes hFV hAtom op decl
      rb.condition rr.condition rc.condition rr.ty rc.ty
      (.var sb.types) rb.effect rr.effect rc.effect
      (Poly.Effect.var sb.effects)
      (Poly.Effect.var (sb.effects + 1))
      localTypes localEffects hC
    simp only [Finset.mem_union, Ty.fvTypes,
      Finset.mem_singleton] at h
    have hbC : i ∈ X.freeTypes rb.condition → i < rc.next.types :=
      fun hm => lt_of_lt_of_le
        (hbT i (Finset.mem_union_right _ hm)) hnextB.1
    have hrC : i ∈ X.freeTypes rr.condition → i < rc.next.types :=
      fun hm => lt_of_lt_of_le
        (hrT i (Finset.mem_union_right _ hm)) hnextR.1
    have hcC : i ∈ X.freeTypes rc.condition → i < rc.next.types :=
      fun hm => hcT i (Finset.mem_union_right _ hm)
    have hrTy : i ∈ rr.ty.fvTypes → i < rc.next.types :=
      fun hm => lt_of_lt_of_le
        (hrT i (Finset.mem_union_left _ hm)) hnextR.1
    have hcTy : i ∈ rc.ty.fvTypes → i < rc.next.types :=
      fun hm => hcT i (Finset.mem_union_left _ hm)
    aesop
  · intro i hi
    have hmem : i = sb.effects + 1 ∨
        i ∈ X.freeEffects (handlerCondition X op decl
          rb.condition rr.condition rc.condition rr.ty rc.ty
          (.var sb.types) rb.effect rr.effect rc.effect
          (Poly.Effect.var sb.effects)
          (Poly.Effect.var (sb.effects + 1))
          localTypes localEffects) := by
      simpa [Output.supportEffects, Ty.fvEffects,
        Poly.Effect.var] using hi
    rcases hmem with hnew | hC
    · omega
    have h := handlerCondition_freeEffects hFV hAtom op decl
      rb.condition rr.condition rc.condition rr.ty rc.ty
      (.var sb.types) rb.effect rr.effect rc.effect
      (Poly.Effect.var sb.effects)
      (Poly.Effect.var (sb.effects + 1))
      localTypes localEffects hC
    simp only [Finset.mem_union, Ty.fvEffects,
      Poly.Effect.var, Finset.mem_singleton] at h
    have hbC : i ∈ X.freeEffects rb.condition → i < rc.next.effects :=
      fun hm => lt_of_lt_of_le
        (hbE i (by simp [Output.supportEffects, hm])) hnextB.2
    have hrC : i ∈ X.freeEffects rr.condition → i < rc.next.effects :=
      fun hm => lt_of_lt_of_le
        (hrE i (by simp [Output.supportEffects, hm])) hnextR.2
    have hcC : i ∈ X.freeEffects rc.condition → i < rc.next.effects :=
      fun hm => hcE i (by simp [Output.supportEffects, hm])
    have hrTy : i ∈ rr.ty.fvEffects → i < rc.next.effects :=
      fun hm => lt_of_lt_of_le
        (hrE i (by simp [Output.supportEffects, hm])) hnextR.2
    have hcTy : i ∈ rc.ty.fvEffects → i < rc.next.effects :=
      fun hm => hcE i (by simp [Output.supportEffects, hm])
    have hbEff : i ∈ rb.effect.vars → i < rc.next.effects :=
      fun hm => lt_of_lt_of_le
        (hbE i (by simp [Output.supportEffects, hm])) hnextB.2
    have hrEff : i ∈ rr.effect.vars → i < rc.next.effects :=
      fun hm => lt_of_lt_of_le
        (hrE i (by simp [Output.supportEffects, hm])) hnextR.2
    have hcEff : i ∈ rc.effect.vars → i < rc.next.effects :=
      fun hm => hcE i (by simp [Output.supportEffects, hm])
    aesop

/-- Application branch of generic supply-indexed completeness. -/
theorem Output.CoversAt.app {sig : Signature} {X : ConstraintSystem}
    (Γg Γd : Context X) (C : X.Formula)
    (ops : Finset Op) (s : Supply)
    (rf rx : Output X) (a b : Ty) (η εf εx : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (hfBound : (∀ i ∈ rf.supportTypes, i < rf.next.types) ∧
      (∀ i ∈ rf.supportEffects, i < rf.next.effects))
    (hxBound : (∀ i ∈ rx.supportTypes, i < rx.next.types) ∧
      (∀ i ∈ rx.supportEffects, i < rx.next.effects))
    (hstart : s.types ≤ rf.next.types ∧
      s.effects ≤ rf.next.effects)
    (hnext : rf.next.types ≤ rx.next.types ∧
      rf.next.effects ≤ rx.next.effects)
    (hf : rf.CoversAt Γg Γd C s (.arr a η b) εf)
    (hx : rx.CoversAt Γg Γd C rf.next a εx) :
    (⟨.var rx.next.types,
      rf.effect ∪ rx.effect ∪ Poly.Effect.var rx.next.effects,
      X.combine (X.combine rf.condition rx.condition)
        (X.equalType rf.ty
          (.arr rx.ty (Poly.Effect.var rx.next.effects)
            (.var rx.next.types))),
      ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩ : Output X).CoversAt
      Γg Γd C s b (εf ∪ εx ∪ η) := by
  intro vg vd hctx hC
  rcases hf vg vd hctx hC with
    ⟨w₁, h₁T, h₁E, hCf, hTf, hEf⟩
  have hctx₁ := Context.moreGeneralAt_below
    Γg Γd ops s hb vg w₁ vd hctx h₁T h₁E
  rcases hx w₁ vd hctx₁ hC with
    ⟨w₂, h₂T, h₂E, hCx, hTx, hEx⟩
  have hsolution := Output.app_solution_extend rf rx
    hfBound hxBound hnext w₁ w₂ h₂T h₂E hCf hCx
    (a.eval vd) (b.eval vd) (η.eval vd.effects)
    (by simpa [Ty.eval] using hTf) hTx
  let w₃ := Generic.Valuation.assignAt w₂ rx.next
    (b.eval vd) (η.eval vd.effects)
  have h₃T := hsolution.1
  have h₃E := hsolution.2.1
  have hCg := hsolution.2.2.1
  have hTg := hsolution.2.2.2.1
  have hEg := hsolution.2.2.2.2
  refine ⟨w₃, ?_, ?_, hCg, hTg, ?_⟩
  · intro i hi
    exact (h₁T i hi).trans
      ((h₂T i (lt_of_lt_of_le hi hstart.1)).trans
        (h₃T i (by omega)))
  · intro i hi
    exact (h₁E i hi).trans
      ((h₂E i (lt_of_lt_of_le hi hstart.2)).trans
        (h₃E i (by omega)))
  · simpa [Effect.eval_union, hEf, hEx] using hEg

/-- Monomorphic let retains the first solution while checking the body. -/
theorem Output.CoversAt.letMono {sig : Signature} {X : ConstraintSystem}
    (Γg Γd : Context X) (C : X.Formula)
    (ops : Finset Op) (s : Supply)
    (r₁ r₂ : Output X) (τ₁ τ₂ : Ty) (ε₁ ε₂ : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (h₁Bound : (∀ i ∈ r₁.supportTypes, i < r₁.next.types) ∧
      (∀ i ∈ r₁.supportEffects, i < r₁.next.effects))
    (hstart : s.types ≤ r₁.next.types ∧
      s.effects ≤ r₁.next.effects)
    (hfirst : r₁.CoversAt Γg Γd C s τ₁ ε₁)
    (hbody : r₂.CoversAt
      (Scheme.mono r₁.ty :: Γg)
      (Scheme.mono τ₁ :: Γd) C r₁.next τ₂ ε₂) :
    (⟨r₂.ty, r₁.effect ∪ r₂.effect,
      X.combine r₁.condition r₂.condition, r₂.next⟩ : Output X).CoversAt
      Γg Γd C s τ₂ (ε₁ ∪ ε₂) := by
  intro vg vd hctx hC
  rcases hfirst vg vd hctx hC with
    ⟨w₁, h₁T, h₁E, hC₁, hTy₁, hEff₁⟩
  have hctx₁ := Context.moreGeneralAt_below
    Γg Γd ops s hb vg w₁ vd hctx h₁T h₁E
  have hmono :
      (Scheme.mono (X := X) r₁.ty).MoreGeneralAt
        (Scheme.mono τ₁) w₁ vd :=
    (Scheme.mono_moreGeneralAt_iff r₁.ty τ₁ w₁ vd).mpr hTy₁
  have hctxBody : Context.MoreGeneralAt
      (Scheme.mono r₁.ty :: Γg)
      (Scheme.mono τ₁ :: Γd) w₁ vd :=
    List.Forall₂.cons hmono hctx₁
  rcases hbody w₁ vd hctxBody hC with
    ⟨w₂, h₂T, h₂E, hC₂, hTy₂, hEff₂⟩
  have hframe := r₁.semantic_frame_of_below w₁ w₂
    h₁Bound.1 h₁Bound.2 h₂T h₂E
  refine ⟨w₂, ?_, ?_, (X.combine_iff _ _ _).2
    ⟨hframe.1.mp hC₁, hC₂⟩, hTy₂, ?_⟩
  · intro i hi
    exact (h₁T i hi).trans (h₂T i (lt_of_lt_of_le hi hstart.1))
  · intro i hi
    exact (h₁E i hi).trans (h₂E i (lt_of_lt_of_le hi hstart.2))
  · simp [Effect.eval_union, ← hframe.2.2, hEff₁, hEff₂]

/-- Polymorphic value let preserves its residual obligation through the
body's fresh-name assignments. -/
theorem Output.CoversAt.letVal {sig : Signature} {X : ConstraintSystem}
    (hFV : X.LawfulFV)
    (Γg Γd : Context X) (C₁ C₂ : X.Formula)
    (ops : Finset Op) (s : Supply)
    (r₁ r₂ : Output X) (τ₁ τ₂ : Ty) (ε₂ : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (hstart : s.types ≤ r₁.next.types ∧
      s.effects ≤ r₁.next.effects)
    (hfirst : r₁.CoversAt Γg Γd C₁ s τ₁ ∅)
    (hbody : r₂.CoversAt
      (Scheme.generalize Γg r₁.condition r₁.ty :: Γg)
      (Scheme.generalize Γd C₁ τ₁ :: Γd)
      C₂ r₁.next τ₂ ε₂) :
    (⟨r₂.ty, r₂.effect,
      X.combine (Scheme.residual Γg r₁.condition r₁.ty)
        r₂.condition, r₂.next⟩ : Output X).CoversAt
      Γg Γd (X.combine (Scheme.residual Γd C₁ τ₁) C₂)
      s τ₂ ε₂ := by
  intro vg vd hctx hC
  rcases (X.combine_iff _ _ _).1 hC with ⟨hresD, hC₂⟩
  have hfirstAcross := hfirst.toAcross Γg Γd C₁ ops s
    r₁ τ₁ ∅ hb
  have hgen := Scheme.generalize_moreGeneralAt_across
    Γg Γd C₁ r₁.condition τ₁ r₁.ty ∅ r₁.effect
    hfirstAcross vg vd hctx
  have hresG := Scheme.residual_across
    Γg Γd C₁ r₁.condition τ₁ r₁.ty ∅ r₁.effect
    hfirstAcross vg vd hctx hresD
  have hctxBody : Context.MoreGeneralAt
      (Scheme.generalize Γg r₁.condition r₁.ty :: Γg)
      (Scheme.generalize Γd C₁ τ₁ :: Γd) vg vd :=
    List.Forall₂.cons hgen hctx
  rcases hbody vg vd hctxBody hC₂ with
    ⟨w₂, h₂T, h₂E, hC₂g, hTy₂, hEff₂⟩
  have hct : ∀ i ∈ Γg.freeTypes, w₂.types i = vg.types i := by
    intro i hi
    exact (h₂T i (lt_of_lt_of_le
      (hb.context_free_below.1 i hi) hstart.1)).symm
  have hce : ∀ i ∈ Γg.freeEffects, w₂.effects i = vg.effects i := by
    intro i hi
    exact (h₂E i (lt_of_lt_of_le
      (hb.context_free_below.2 i hi) hstart.2)).symm
  have hresW : X.holds
      (Scheme.residual Γg r₁.condition r₁.ty) w₂ := by
    have hs := Scheme.residual_free_context hFV
      Γg r₁.condition r₁.ty
    exact (X.free_support _ vg w₂
      (fun i hi => (hct i (hs.1 hi)).symm)
      (fun i hi => (hce i (hs.2 hi)).symm)).mp hresG
  refine ⟨w₂, ?_, ?_,
    (X.combine_iff _ _ _).2 ⟨hresW, hC₂g⟩, hTy₂, hEff₂⟩
  · intro i hi
    exact h₂T i (lt_of_lt_of_le hi hstart.1)
  · intro i hi
    exact h₂E i (lt_of_lt_of_le hi hstart.2)

/-- Closed operation declarations let the perform branch choose fresh
signature parameters without changing the surrounding context. -/
theorem Output.CoversAt.perform {sig : Signature} {X : ConstraintSystem}
    (Γg Γd : Context X) (C : X.Formula)
    (ops : Finset Op) (s : Supply)
    (op : Op) (raw : OpDecl) (ρd ηd : Nat → Nat)
    (re : Output X) (ε : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (hop : op ∈ ops) (hd : sig op = some raw)
    (hc : raw.Closed)
    (hadmD : raw.AdmissibleRename ρd ηd)
    (hbody : re.CoversAt Γg Γd C
      (s.advance raw.typeVars raw.effectVars)
      (raw.input.rename ρd ηd) ε) :
    let ρg := renameBound raw.typeVars s.types
    let ηg := renameBound raw.effectVars s.effects
    (⟨raw.output.rename ρg ηg,
      Poly.Effect.singleton op ∪ re.effect,
      X.combine re.condition
        (X.equalType re.ty (raw.input.rename ρg ηg)),
      re.next⟩ : Output X).CoversAt
      Γg Γd C s (raw.output.rename ρd ηd)
      (Poly.Effect.singleton op ∪ ε) := by
  dsimp
  intro vg vd hctx hC
  have hraw := hb.signature op hop raw hd
  rcases raw.rename_realizable s ρd ηd hadmD vg vd
      hraw.1 hraw.2
      (by
        intro i hi hnot
        exact False.elim (hnot (raw.closed_usedTypes hc hi)))
      (by
        intro i hi hnot
        exact False.elim (hnot (raw.closed_usedEffects hc hi))) with
    ⟨v', hfixedT, hfixedE, hInput, hOutput⟩
  have hctx' := Context.moreGeneralAt_below
    Γg Γd ops s hb vg v' vd hctx hfixedT hfixedE
  rcases hbody v' vd hctx' hC with
    ⟨w, hwt, hwe, hCg, hTy, hEff⟩
  have hframe := raw.renamed_eval_frame s v' w
    hraw.1 hraw.2 hwt hwe
  refine ⟨w, ?_, ?_, (X.combine_iff _ _ _).2 ⟨hCg, ?_⟩,
    ?_, ?_⟩
  · intro i hi
    exact (hfixedT i hi).trans
      (hwt i (lt_of_lt_of_le hi
        (Nat.le_of_lt (s.advance_mono
          raw.typeVars raw.effectVars).1)))
  · intro i hi
    exact (hfixedE i hi).trans
      (hwe i (lt_of_lt_of_le hi
        (Nat.le_of_lt (s.advance_mono
          raw.typeVars raw.effectVars).2)))
  · apply (X.equalType_iff _ _ _).2
    exact hTy.trans (hInput.symm.trans hframe.1)
  · exact hframe.2.symm.trans hOutput
  · rw [Effect.eval_union, Effect.eval_union]
    have hopW : (Poly.Effect.singleton op).eval w.effects = {op} := by
      simp [Poly.Effect.eval, Poly.Effect.singleton]
    have hopD : (Poly.Effect.singleton op).eval vd.effects = {op} := by
      simp [Poly.Effect.eval, Poly.Effect.singleton]
    rw [hopW, hopD, hEff]

theorem Output.CoversAt.conv {X : ConstraintSystem}
    (Γg Γd : Context X) (C : X.Formula)
    (s : Supply) (r : Output X) (τ τ' : Ty) (ε : Effect)
    (h : r.CoversAt Γg Γd C s τ ε)
    (hEq : X.Entails C (X.equalType τ τ')) :
    r.CoversAt Γg Γd C s τ' ε := by
  intro vg vd hctx hC
  rcases h vg vd hctx hC with
    ⟨w, ht, he, hCg, hTy, hEff⟩
  exact ⟨w, ht, he, hCg,
    hTy.trans ((X.equalType_iff _ _ _).1 (hEq vd hC)), hEff⟩

theorem Output.CoversAt.weaken {X : ConstraintSystem}
    (Γg Γd : Context X) (C D : X.Formula)
    (s : Supply) (r : Output X) (τ : Ty) (ε : Effect)
    (h : r.CoversAt Γg Γd C s τ ε)
    (hEnt : X.Entails D C) :
    r.CoversAt Γg Γd D s τ ε := by
  intro vg vd hctx hD
  exact h vg vd hctx (hEnt vd hD)

/-- Successful generic generation never decreases its supply. -/
theorem generate_next_mono {sig : Signature} {X : ConstraintSystem}
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (h : generate sig X Γ e s = some r) :
    s.types ≤ r.next.types ∧ s.effects ≤ r.next.effects := by
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
            have hadvance := s.advance_mono σ.typeVars σ.effectVars
            exact ⟨Nat.le_of_lt hadvance.1,
              Nat.le_of_lt hadvance.2⟩
          · simp [hσ, hfresh] at h
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
                  (Scheme.generalize Γ r₁.condition r₁.ty :: Γ)
                  e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  have hm₁ := ihBound h₁
                  have hm₂ := ihVal r₁ h₂
                  exact ⟨hm₁.1.trans hm₂.1,
                    hm₁.2.trans hm₂.2⟩
          | false =>
              cases h₂ : generate sig X
                  (Scheme.mono r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  have hm₁ := ihBound h₁
                  have hm₂ := ihMono r₁ h₂
                  exact ⟨hm₁.1.trans hm₂.1,
                    hm₁.2.trans hm₂.2⟩
  | case7 Γ op e s ih =>
      cases hd : sig op with
      | none => simp [hd] at h
      | some decl =>
          cases he : generate sig X Γ e
              (s.advance decl.typeVars decl.effectVars) with
          | none => simp [hd, he] at h
          | some re =>
              simp [hd, he] at h
              cases h
              have hadvance := s.advance_mono
                decl.typeVars decl.effectVars
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
              cases hr : generate sig X
                  (Scheme.mono rb.ty :: Γ) ret sr with
              | none => simp [hd, hb, hr, sb, sr] at h
              | some rr =>
                  cases hc : generate sig X
                      (Scheme.mono (.arr decl.output χ a) ::
                        Scheme.mono decl.input :: Γ)
                      clause rr.next with
                  | none =>
                      simp [hd, hb, hr, hc, ρ, η, decl,
                        sb, a, χ, sr] at h
                  | some rc =>
                      let localTypes := Finset.range rc.next.types \
                        Finset.range rr.next.types
                      let localEffects := Finset.range rc.next.effects \
                        Finset.range rr.next.effects
                      let C := handlerCondition X op decl
                        rb.condition rr.condition rc.condition
                        rr.ty rc.ty a rb.effect rr.effect rc.effect
                        δ χ localTypes localEffects
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hs : Generic.OpDecl.HandlerScope decl Γ rb.ty a
                            rb.effect rr.effect δ χ
                        · by_cases hcs : Generic.OpDecl.ClauseScope decl Γ C rb.ty a
                              rb.effect rr.effect δ χ
                              localTypes localEffects
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at h
                            cases h
                            have hmBody := ihBody hb
                            have hmAdvance := rb.next.advance_mono
                              raw.typeVars raw.effectVars
                            have hmRet := ihRet raw rb hr
                            have hmClause := ihClause raw rb rr hc
                            change s.types ≤ rc.next.types ∧
                              s.effects ≤ rc.next.effects
                            dsimp [sb, sr] at hmRet
                            constructor <;> omega
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at h
                        · simp [hd, hb, hr, hsafe, hs,
                            ρ, η, decl, sb, a, δ, χ, sr] at h
                      · simp [hd, hb, hr, hsafe, ρ, η, sb, sr] at h

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

/-- Variable branch of the full generic completeness induction. -/
theorem generate_var_coversAt {sig : Signature} {X : ConstraintSystem}
    {Γg Γd : Context X} {σg σd : Scheme X} {i : Nat}
    (hg : Γg[i]? = some σg) (hd : Γd[i]? = some σd)
    (ft fe : Nat → Nat)
    (hadmD : σd.AdmissibleRename ft fe)
    (hfreshD : σd.FreshRename ft fe)
    (C : X.Formula)
    (hent : X.Entails C (σd.instantiateProjected ft fe).2)
    (ops : Finset Op) (s : Supply)
    (hb : BoundedInputs sig X Γg ops s) :
    ∃ r : Output X,
      generate sig X Γg (.var i) s = some r ∧
      r.CoversAt Γg Γd C s
        (σd.instantiateProjected ft fe).1 ∅ := by
  let ρ := renameBound σg.typeVars s.types
  let η := renameBound σg.effectVars s.effects
  have hmem : σg ∈ Γg := List.mem_of_getElem? hg
  have hfreshG : σg.FreshRename ρ η :=
    σg.renameBound_fresh s.types s.effects
      (fun j hj => hb.contextTypes σg hmem j
        (by simp [Scheme.usedTypes, hj]))
      (fun j hj => hb.contextEffects σg hmem j
        (by simp [Scheme.usedEffects, hj]))
  have hfreeT : σg.freeTypes ⊆ Finset.range s.types := by
    intro j hj
    exact Finset.mem_range.mpr (hb.contextTypes σg hmem j
      (σg.freeTypes_subset_usedTypes hj))
  have hfreeE : σg.freeEffects ⊆ Finset.range s.effects := by
    intro j hj
    exact Finset.mem_range.mpr (hb.contextEffects σg hmem j
      (σg.freeEffects_subset_usedEffects hj))
  have hdisjT : (σg.typeVars.image ρ) ∩ Finset.range s.types = ∅ :=
    renameBound_image_disjoint_below σg.typeVars
      (Finset.range s.types) s.types
      (fun j hj => Finset.mem_range.mp hj)
  have hdisjE : (σg.effectVars.image η) ∩ Finset.range s.effects = ∅ :=
    renameBound_image_disjoint_below σg.effectVars
      (Finset.range s.effects) s.effects
      (fun j hj => Finset.mem_range.mp hj)
  refine ⟨⟨(σg.instantiateProjected ρ η).1, ∅,
    (σg.instantiateProjected ρ η).2,
      s.advance σg.typeVars σg.effectVars⟩,
    ?_, ?_⟩
  · simp [generate, hg, ρ, η, hfreshG]
  · intro vg vd hctx hC
    rcases Context.variable_complete_projected
      hg hd ft fe ρ η hadmD hfreshD
      ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩
      (renameBound_injOn _ _) (renameBound_injOn _ _) hfreshG
      (Finset.range s.types) (Finset.range s.effects)
      hfreeT hfreeE hdisjT hdisjE vg vd hctx (hent vd hC) with
      ⟨wg, hT, hE, hCg, ht⟩
    exact ⟨wg,
      (fun j hj => (hT j (Finset.mem_range.mpr hj)).symm),
      (fun j hj => (hE j (Finset.mem_range.mpr hj)).symm),
      hCg, ht, rfl⟩

end SystemFXi.EHMX.Generic
