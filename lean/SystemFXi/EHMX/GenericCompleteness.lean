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
          by_cases hsafe : σ.SafeRename
              (renameBound σ.typeVars s.types)
              (renameBound σ.effectVars s.effects)
          · simp [hσ, hsafe] at h
            cases h
            have hadvance := s.advance_mono σ.typeVars σ.effectVars
            exact ⟨Nat.le_of_lt hadvance.1,
              Nat.le_of_lt hadvance.2⟩
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
    (hRename : X.LawfulSafeRename)
    {Γg Γd : Context X} {σg σd : Scheme X} {i : Nat}
    (hg : Γg[i]? = some σg) (hd : Γd[i]? = some σd)
    (ft fe : Nat → Nat)
    (hadmD : σd.AdmissibleRename ft fe)
    (hsafeD : σd.SafeRename ft fe)
    (C : X.Formula) (hent : X.Entails C (σd.instantiate ft fe).2)
    (ops : Finset Op) (s : Supply)
    (hb : BoundedInputs sig X Γg ops s) :
    ∃ r : Output X,
      generate sig X Γg (.var i) s = some r ∧
      r.CoversAt Γg Γd C s (σd.instantiate ft fe).1 ∅ := by
  let ρ := renameBound σg.typeVars s.types
  let η := renameBound σg.effectVars s.effects
  have hmem : σg ∈ Γg := List.mem_of_getElem? hg
  have hsafeG : σg.SafeRename ρ η := by
    apply σg.renameBound_safe
    · intro j hj
      have hused : j ∈ σg.usedTypes := by
        simp [Scheme.usedTypes, Scheme.freeTypes] at hj ⊢
        aesop
      exact Nat.le_of_lt (hb.contextTypes σg hmem j hused)
    · intro j hj
      have hused : j ∈ σg.usedEffects := by
        simp [Scheme.usedEffects, Scheme.freeEffects] at hj ⊢
        aesop
      exact Nat.le_of_lt (hb.contextEffects σg hmem j hused)
  have hdisjT : (σg.typeVars.image ρ) ∩ Finset.range s.types = ∅ :=
    renameBound_image_disjoint_below σg.typeVars
      (Finset.range s.types) s.types
      (fun j hj => Finset.mem_range.mp hj)
  have hdisjE : (σg.effectVars.image η) ∩ Finset.range s.effects = ∅ :=
    renameBound_image_disjoint_below σg.effectVars
      (Finset.range s.effects) s.effects
      (fun j hj => Finset.mem_range.mp hj)
  refine ⟨⟨(σg.instantiate ρ η).1, ∅,
    (σg.instantiate ρ η).2, s.advance σg.typeVars σg.effectVars⟩,
    ?_, ?_⟩
  · simp [generate, hg, ρ, η, hsafeG]
  · intro vg vd hctx hC
    rcases Context.variable_complete_at hRename
      hg hd ft fe ρ η hadmD hsafeD
      ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩ hsafeG
      (Finset.range s.types) (Finset.range s.effects)
      hdisjT hdisjE vg vd hctx (hent vd hC) with
      ⟨wg, hT, hE, hCg, ht⟩
    exact ⟨wg,
      (fun j hj => (hT j (Finset.mem_range.mpr hj)).symm),
      (fun j hj => (hE j (Finset.mem_range.mpr hj)).symm),
      hCg, ht, rfl⟩

end SystemFXi.EHMX.Generic
