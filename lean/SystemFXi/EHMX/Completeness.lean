import SystemFXi.EHMX.Algorithm

namespace SystemFXi.EHMX

/-- Names whose values determine an executable inference result. -/
def Output.supportTypes {X : Domain} (r : Output X) : Finset Nat :=
  r.ty.fvTypes ∪ r.constraints.usedTypes

def Output.supportEffects {X : Domain} (r : Output X) : Finset Nat :=
  r.ty.fvEffects ∪ r.effect.vars ∪ r.constraints.usedEffects

/-- A supply is above every scheme in the current context and every
operation declaration that the whole expression may use. -/
structure BoundedInputs (sig : Signature) (X : Domain)
    (Γ : Context X) (ops : Finset Op) (s : Supply) : Prop where
  contextTypes : ∀ σ ∈ Γ, ∀ i ∈ σ.usedTypes, i < s.types
  contextEffects : ∀ σ ∈ Γ, ∀ i ∈ σ.usedEffects, i < s.effects
  signatureTypes : ∀ op ∈ ops, ∀ decl, sig op = some decl →
    ∀ i ∈ decl.usedTypes, i < s.types
  signatureEffects : ∀ op ∈ ops, ∀ decl, sig op = some decl →
    ∀ i ∈ decl.usedEffects, i < s.effects

theorem Scheme.fvTypes_subset_usedTypes {X : Domain}
    (σ : Scheme X) : σ.fvTypes ⊆ σ.usedTypes := by
  intro i hi
  simp [Scheme.fvTypes, Scheme.usedTypes] at hi ⊢
  aesop

theorem Scheme.fvEffects_subset_usedEffects {X : Domain}
    (σ : Scheme X) : σ.fvEffects ⊆ σ.usedEffects := by
  intro i hi
  simp [Scheme.fvEffects, Scheme.usedEffects] at hi ⊢
  aesop

theorem BoundedInputs.mono {sig : Signature} {X : Domain}
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

theorem BoundedInputs.cons {sig : Signature} {X : Domain}
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (h : BoundedInputs sig X Γ ops s) (σ : Scheme X)
    (ht : ∀ i ∈ σ.usedTypes, i < s.types)
    (he : ∀ i ∈ σ.usedEffects, i < s.effects) :
    BoundedInputs sig X (σ :: Γ) ops s := by
  constructor
  · intro σ' hσ i hi
    rcases List.mem_cons.mp hσ with rfl | hmem
    · exact ht i hi
    · exact h.contextTypes σ' hmem i hi
  · intro σ' hσ i hi
    rcases List.mem_cons.mp hσ with rfl | hmem
    · exact he i hi
    · exact h.contextEffects σ' hmem i hi
  · exact h.signatureTypes
  · exact h.signatureEffects

theorem BoundedInputs.signature {sig : Signature} {X : Domain}
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
      simp only [List.foldl_cons, ih, Finset.mem_union,
        List.mem_cons]
      aesop

theorem BoundedInputs.seed {sig : Signature} {X : Domain}
    (Γ : Context X) (e : Expr) (s : Supply) :
    BoundedInputs sig X Γ e.ops (s.seed sig Γ e []) := by
  have hs := s.seed_above_inputs sig Γ e []
  constructor
  · intro σ hσ i hi
    apply hs.1 i
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact (foldl_union_mem Scheme.usedTypes Γ ∅ i).mpr
      (Or.inr ⟨σ, hσ, hi⟩)
  · intro σ hσ i hi
    apply hs.2 i
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact (foldl_union_mem Scheme.usedEffects Γ ∅ i).mpr
      (Or.inr ⟨σ, hσ, hi⟩)
  · intro op hop decl hd i hi
    apply hs.1 i
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr
      ⟨op, hop, by simp [hd, hi]⟩
  · intro op hop decl hd i hi
    apply hs.2 i
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr
      ⟨op, hop, by simp [hd, hi]⟩

theorem BoundedInputs.contextFVBelow {sig : Signature} {X : Domain}
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (h : BoundedInputs sig X Γ ops s) :
    (∀ i ∈ Γ.fvTypes, i < s.types) ∧
      (∀ i ∈ Γ.fvEffects, i < s.effects) := by
  constructor
  · intro i hi
    rcases (foldl_union_mem Scheme.fvTypes Γ ∅ i).mp
      (by simpa [Context.fvTypes] using hi) with hf | ⟨σ, hσ, hfv⟩
    · simp at hf
    · exact h.contextTypes σ hσ i
        (Scheme.fvTypes_subset_usedTypes σ hfv)
  · intro i hi
    rcases (foldl_union_mem Scheme.fvEffects Γ ∅ i).mp
      (by simpa [Context.fvEffects] using hi) with hf | ⟨σ, hσ, hfv⟩
    · simp at hf
    · exact h.contextEffects σ hσ i
        (Scheme.fvEffects_subset_usedEffects σ hfv)


/-- A later assignment preserving the support of an earlier result cannot
invalidate its constraint or change its inferred type and effect. -/
theorem Output.semantic_frame {X : Domain}
    (hX : LawfulSupport X) (r : Output X) (v w : Valuation)
    (ht : ∀ i ∈ r.supportTypes, v.types i = w.types i)
    (he : ∀ i ∈ r.supportEffects, v.effects i = w.effects i) :
    (r.constraints.holds v ↔ r.constraints.holds w) ∧
      r.ty.eval v = r.ty.eval w ∧
      r.effect.eval v.effects = r.effect.eval w.effects := by
  constructor
  · exact Constraint.holds_support hX r.constraints v w
      (fun i hi => ht i (by
        simp [Output.supportTypes, Constraint.usedTypes, hi]))
      (fun i hi => he i (by
        simp [Output.supportEffects, Constraint.usedEffects, hi]))
  constructor
  · exact Ty.eval_support r.ty v w
      (fun i hi => ht i (Finset.mem_union_left _ hi))
      (fun i hi => he i (by
        simp [Output.supportEffects, hi]))
  · exact Effect.eval_support r.effect v w
      (fun i hi => he i (by
        simp [Output.supportEffects, hi]))

theorem Output.semantic_frame_of_below {X : Domain}
    (hX : LawfulSupport X) (r : Output X) (v w : Valuation)
    (hboundT : ∀ i ∈ r.supportTypes, i < r.next.types)
    (hboundE : ∀ i ∈ r.supportEffects, i < r.next.effects)
    (hfixedT : ∀ i, i < r.next.types → v.types i = w.types i)
    (hfixedE : ∀ i, i < r.next.effects → v.effects i = w.effects i) :
    (r.constraints.holds v ↔ r.constraints.holds w) ∧
      r.ty.eval v = r.ty.eval w ∧
      r.effect.eval v.effects = r.effect.eval w.effects :=
  r.semantic_frame hX v w
    (fun i hi => hfixedT i (hboundT i hi))
    (fun i hi => hfixedE i (hboundE i hi))

/-- A generated solution can be confined to names allocated for one
subexpression. This supplies the existential witness for a handler clause. -/
theorem Output.localize_solution {X : Domain}
    (hX : LawfulSupport X) (r : Output X) (s : Supply)
    (base w : Valuation)
    (hboundT : ∀ i ∈ r.supportTypes, i < r.next.types)
    (hboundE : ∀ i ∈ r.supportEffects, i < r.next.effects)
    (hbelowT : ∀ i, i < s.types → base.types i = w.types i)
    (hbelowE : ∀ i, i < s.effects → base.effects i = w.effects i)
    (hC : r.constraints.holds w) :
    let localTypes := Finset.range r.next.types \ Finset.range s.types
    let localEffects := Finset.range r.next.effects \ Finset.range s.effects
    ∃ v : Valuation,
      (∀ i, i ∉ localTypes → v.types i = base.types i) ∧
      (∀ i, i ∉ localEffects → v.effects i = base.effects i) ∧
      r.constraints.holds v ∧
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
  have hframe := r.semantic_frame_of_below hX w v
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

/-- The application constructor preserves the supply bound once both
subresults do. -/
theorem Output.app_support_below {X : Domain}
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
        .and (.and rf.constraints rx.constraints)
          (.typeEq rf.ty (.arr rx.ty η b)),
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i ∈ insert rx.next.types
        (rf.supportTypes ∪ rx.supportTypes) := by
      simp [Output.supportTypes, Constraint.usedTypes,
        Constraint.fvTypes, Constraint.boundTypes, Ty.fvTypes] at hi ⊢
      aesop
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
      simp [Output.supportEffects, Constraint.usedEffects,
        Constraint.fvEffects, Constraint.boundEffects, Ty.fvEffects,
        Poly.Effect.var] at hi ⊢
      aesop
    rcases Finset.mem_insert.mp hsub with hnew | hprev
    · omega
    · rcases Finset.mem_union.mp hprev with hf | hx
      · have := hfE i hf
        omega
      · have := hxE i hx
        omega

/-- Assign the result type and latent effect introduced by an
application after both subexpressions have been generated. -/
def Valuation.assignAt (v : Valuation) (s : Supply)
    (t : GroundTy) (ε : Finset Op) : Valuation :=
  ⟨Function.update v.types s.types t,
    Function.update v.effects s.effects ε⟩

theorem Valuation.assignAt_preserves_below (v : Valuation)
    (s : Supply) (t : GroundTy) (ε : Finset Op) :
    (∀ i, i < s.types →
      v.types i = (v.assignAt s t ε).types i) ∧
    (∀ i, i < s.effects →
      v.effects i = (v.assignAt s t ε).effects i) := by
  constructor
  · intro i hi
    have hne : i ≠ s.types := by omega
    simp [Valuation.assignAt, Function.update, hne]
  · intro i hi
    have hne : i ≠ s.effects := by omega
    simp [Valuation.assignAt, Function.update, hne]

/-- Combining the two subexpression solutions in the application case.
The fresh result names receive the declarative result and latent effect. -/
theorem Output.app_solution_extend {X : Domain}
    (hX : LawfulSupport X) (rf rx : Output X)
    (hfBound : (∀ i ∈ rf.supportTypes, i < rf.next.types) ∧
      (∀ i ∈ rf.supportEffects, i < rf.next.effects))
    (hxBound : (∀ i ∈ rx.supportTypes, i < rx.next.types) ∧
      (∀ i ∈ rx.supportEffects, i < rx.next.effects))
    (hnext : rf.next.types ≤ rx.next.types ∧
      rf.next.effects ≤ rx.next.effects)
    (v w : Valuation)
    (hfixedT : ∀ i, i < rf.next.types → v.types i = w.types i)
    (hfixedE : ∀ i, i < rf.next.effects → v.effects i = w.effects i)
    (hf : rf.constraints.holds v) (hx : rx.constraints.holds w)
    (a b : GroundTy) (η : Finset Op)
    (hfun : rf.ty.eval v = .arr a η b)
    (harg : rx.ty.eval w = a) :
    let u := w.assignAt rx.next b η
    let out : Output X :=
      ⟨.var rx.next.types,
        rf.effect ∪ rx.effect ∪ Poly.Effect.var rx.next.effects,
        .and (.and rf.constraints rx.constraints)
          (.typeEq rf.ty
            (.arr rx.ty (Poly.Effect.var rx.next.effects)
              (.var rx.next.types))),
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩
    (∀ i, i < rx.next.types → w.types i = u.types i) ∧
      (∀ i, i < rx.next.effects → w.effects i = u.effects i) ∧
      out.constraints.holds u ∧
      out.ty.eval u = b ∧
      out.effect.eval u.effects =
        rf.effect.eval v.effects ∪ rx.effect.eval w.effects ∪ η := by
  dsimp
  let u := w.assignAt rx.next b η
  have hwu := w.assignAt_preserves_below rx.next b η
  have hrfVW := rf.semantic_frame_of_below hX v w
    hfBound.1 hfBound.2 hfixedT hfixedE
  have hrfWU := rf.semantic_frame_of_below hX w u
    hfBound.1 hfBound.2
    (fun i hi => hwu.1 i (lt_of_lt_of_le hi hnext.1))
    (fun i hi => hwu.2 i (lt_of_lt_of_le hi hnext.2))
  have hrxWU := rx.semantic_frame_of_below hX w u
    hxBound.1 hxBound.2 hwu.1 hwu.2
  have hnewT : (Ty.var rx.next.types).eval u = b := by
    simp [Ty.eval, u, Valuation.assignAt]
  have hnewE :
      (Poly.Effect.var rx.next.effects).eval u.effects = η := by
    simp [Poly.Effect.eval, Poly.Effect.var,
      u, Valuation.assignAt]
  refine ⟨hwu.1, hwu.2, ?_, hnewT, ?_⟩
  · refine ⟨⟨hrfWU.1.mp (hrfVW.1.mp hf),
      hrxWU.1.mp hx⟩, ?_⟩
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

theorem Output.letMono_support_below {X : Domain}
    (r₁ r₂ : Output X)
    (h₁T : ∀ i ∈ r₁.supportTypes, i < r₁.next.types)
    (h₁E : ∀ i ∈ r₁.supportEffects, i < r₁.next.effects)
    (h₂T : ∀ i ∈ r₂.supportTypes, i < r₂.next.types)
    (h₂E : ∀ i ∈ r₂.supportEffects, i < r₂.next.effects)
    (hnext : r₁.next.types ≤ r₂.next.types ∧
      r₁.next.effects ≤ r₂.next.effects) :
    let r : Output X :=
      ⟨r₂.ty, r₁.effect ∪ r₂.effect,
        .and r₁.constraints r₂.constraints, r₂.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i ∈ r₁.supportTypes ∪ r₂.supportTypes := by
      simp [Output.supportTypes, Constraint.usedTypes,
        Constraint.fvTypes, Constraint.boundTypes] at hi ⊢
      aesop
    rcases Finset.mem_union.mp hsub with h₁ | h₂
    · have := h₁T i h₁
      omega
    · exact h₂T i h₂
  · intro i hi
    have hsub : i ∈ r₁.supportEffects ∪ r₂.supportEffects := by
      simp [Output.supportEffects, Constraint.usedEffects,
        Constraint.fvEffects, Constraint.boundEffects] at hi ⊢
      aesop
    rcases Finset.mem_union.mp hsub with h₁ | h₂
    · have := h₁E i h₁
      omega
    · exact h₂E i h₂

theorem Output.lam_support_below {X : Domain}
    (s : Supply) (rb : Output X)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hnext : s.types < rb.next.types) :
    let r : Output X :=
      ⟨.arr (.var s.types) rb.effect rb.ty, ∅,
        rb.constraints, rb.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i = s.types ∨ i ∈ rb.supportTypes := by
      simp [Output.supportTypes, Constraint.usedTypes,
        Ty.fvTypes] at hi ⊢
      aesop
    rcases hsub with rfl | h
    · exact hnext
    · exact hbT i h
  · intro i hi
    have hsub : i ∈ rb.supportEffects := by
      simp [Output.supportEffects, Constraint.usedEffects,
        Ty.fvEffects] at hi ⊢
      aesop
    exact hbE i hsub

theorem Supply.renameBound_types_below_advance
    (s : Supply) (bound effectBound used : Finset Nat)
    (hbelow : ∀ i ∈ used, i < s.types) :
    ∀ i ∈ used,
      renameBound bound s.types i <
        (s.advance bound effectBound).types := by
  intro i hi
  by_cases hb : i ∈ bound
  · exact (s.advance_above_renamed bound effectBound).1 i hb
  · rw [renameBound_fixed bound s.types i hb]
    exact lt_of_lt_of_le (hbelow i hi)
      (Nat.le_of_lt (s.advance_mono bound effectBound).1)

theorem Supply.renameBound_effects_below_advance
    (s : Supply) (typeBound bound used : Finset Nat)
    (hbelow : ∀ i ∈ used, i < s.effects) :
    ∀ i ∈ used,
      renameBound bound s.effects i <
        (s.advance typeBound bound).effects := by
  intro i hi
  by_cases hb : i ∈ bound
  · exact (s.advance_above_renamed typeBound bound).2 i hb
  · rw [renameBound_fixed bound s.effects i hb]
    exact lt_of_lt_of_le (hbelow i hi)
      (Nat.le_of_lt (s.advance_mono typeBound bound).2)

theorem Output.perform_support_below {X : Domain}
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
        .and re.constraints
          (.typeEq re.ty (decl.input.rename ρ η)), re.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i ∈ re.supportTypes ∪
        decl.usedTypes.image (renameBound decl.typeVars s.types) := by
      simp [Output.supportTypes,
        Constraint.usedTypes, Constraint.fvTypes,
        Constraint.boundTypes, Ty.fvTypes_rename,
        OpDecl.usedTypes] at hi ⊢
      aesop
    rcases Finset.mem_union.mp hsub with he | hd
    · exact heT i he
    · rcases Finset.mem_image.mp hd with ⟨j, hj, rfl⟩
      have hlt := s.renameBound_types_below_advance
        decl.typeVars decl.effectVars decl.usedTypes hdeclT j hj
      omega
  · intro i hi
    have hsub : i ∈ re.supportEffects ∪
        decl.usedEffects.image (renameBound decl.effectVars s.effects) := by
      simp [Output.supportEffects,
        Constraint.usedEffects, Constraint.fvEffects,
        Constraint.boundEffects, Ty.fvEffects_rename,
        OpDecl.usedEffects] at hi ⊢
      aesop
    rcases Finset.mem_union.mp hsub with he | hd
    · exact heE i he
    · rcases Finset.mem_image.mp hd with ⟨j, hj, rfl⟩
      have hlt := s.renameBound_effects_below_advance
        decl.typeVars decl.effectVars decl.usedEffects hdeclE j hj
      omega

theorem Scheme.instantiate_supportTypes_subset {X : Domain}
    (hX : LawfulFVRename X) (σ : Scheme X)
    (ρ η : Nat → Nat) :
    (σ.instantiate ρ η).1.fvTypes ∪
      (σ.instantiate ρ η).2.usedTypes ⊆
        σ.usedTypes.image ρ := by
  intro i hi
  rcases Finset.mem_union.mp hi with ht | hc
  · rw [Scheme.instantiate, Ty.fvTypes_rename] at ht
    rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr
      ⟨j, by simp [Scheme.usedTypes, hj], rfl⟩
  · have hsub := σ.predicates.usedTypes_rename_subset hX ρ η
    have hc' : i ∈ (σ.predicates.rename ρ η).usedTypes := by
      simpa [Scheme.instantiate] using hc
    rcases Finset.mem_image.mp (hsub hc') with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr
      ⟨j, by
        rcases Finset.mem_union.mp hj with hf | hb
        · simp [Scheme.usedTypes, hf]
        · simp [Scheme.usedTypes, hb], rfl⟩

theorem Scheme.instantiate_supportEffects_subset {X : Domain}
    (hX : LawfulFVRename X) (σ : Scheme X)
    (ρ η : Nat → Nat) :
    (σ.instantiate ρ η).1.fvEffects ∪
      (σ.instantiate ρ η).2.usedEffects ⊆
        σ.usedEffects.image η := by
  intro i hi
  rcases Finset.mem_union.mp hi with ht | hc
  · rw [Scheme.instantiate, Ty.fvEffects_rename] at ht
    rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr
      ⟨j, by simp [Scheme.usedEffects, hj], rfl⟩
  · have hsub := σ.predicates.usedEffects_rename_subset hX ρ η
    have hc' : i ∈ (σ.predicates.rename ρ η).usedEffects := by
      simpa [Scheme.instantiate] using hc
    rcases Finset.mem_image.mp (hsub hc') with ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr
      ⟨j, by
        rcases Finset.mem_union.mp hj with hf | hb
        · simp [Scheme.usedEffects, hf]
        · simp [Scheme.usedEffects, hb], rfl⟩

/-- Generalization introduces no name outside the value result's support. -/
theorem Scheme.generalize_usedTypes_subset {X : Domain}
    (Γ : Context X) (c : Constraint X) (τ : Ty) :
    (Scheme.generalize Γ c τ).usedTypes ⊆
      τ.fvTypes ∪ c.usedTypes := by
  intro i hi
  simp [Scheme.usedTypes, Scheme.generalize,
    Constraint.usedTypes] at hi ⊢
  aesop

theorem Scheme.generalize_usedEffects_subset {X : Domain}
    (Γ : Context X) (c : Constraint X) (τ : Ty) :
    (Scheme.generalize Γ c τ).usedEffects ⊆
      τ.fvEffects ∪ c.usedEffects := by
  intro i hi
  simp [Scheme.usedEffects, Scheme.generalize,
    Constraint.usedEffects] at hi ⊢
  aesop

theorem BoundedInputs.consMono {sig : Signature} {X : Domain}
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (h : BoundedInputs sig X Γ ops s) (τ : Ty)
    (ht : ∀ i ∈ τ.fvTypes, i < s.types)
    (he : ∀ i ∈ τ.fvEffects, i < s.effects) :
    BoundedInputs sig X (Scheme.mono τ :: Γ) ops s := by
  apply h.cons (Scheme.mono τ)
  · simpa [Scheme.usedTypes, Scheme.mono,
      Constraint.fvTypes, Constraint.boundTypes] using ht
  · simpa [Scheme.usedEffects, Scheme.mono,
      Constraint.fvEffects, Constraint.boundEffects] using he

theorem BoundedInputs.consGeneralize {sig : Signature} {X : Domain}
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (h : BoundedInputs sig X Γ ops s) (c : Constraint X) (τ : Ty)
    (ht : ∀ i ∈ τ.fvTypes ∪ c.usedTypes, i < s.types)
    (he : ∀ i ∈ τ.fvEffects ∪ c.usedEffects, i < s.effects) :
    BoundedInputs sig X (Scheme.generalize Γ c τ :: Γ) ops s := by
  apply h.cons (Scheme.generalize Γ c τ)
  · intro i hi
    exact ht i (Scheme.generalize_usedTypes_subset Γ c τ hi)
  · intro i hi
    exact he i (Scheme.generalize_usedEffects_subset Γ c τ hi)

theorem Scheme.residual_supportTypes_subset {X : Domain}
    (Γ : Context X) (c : Constraint X) (τ : Ty) :
    (Scheme.residual Γ c τ).usedTypes ⊆
      τ.fvTypes ∪ c.usedTypes := by
  intro i hi
  have hs := Constraint.project_usedTypes_subset
    (Scheme.generalize Γ c τ).typeVars
    (Scheme.generalize Γ c τ).effectVars c
  rcases Finset.mem_union.mp (hs (by
    simpa [Scheme.residual] using hi)) with hc | hbound
  · exact Finset.mem_union_right _ hc
  · simp [Scheme.generalize] at hbound
    rcases hbound.1 with ht | hc
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ hc)

theorem Scheme.residual_supportEffects_subset {X : Domain}
    (Γ : Context X) (c : Constraint X) (τ : Ty) :
    (Scheme.residual Γ c τ).usedEffects ⊆
      τ.fvEffects ∪ c.usedEffects := by
  intro i hi
  have hs := Constraint.project_usedEffects_subset
    (Scheme.generalize Γ c τ).typeVars
    (Scheme.generalize Γ c τ).effectVars c
  rcases Finset.mem_union.mp (hs (by
    simpa [Scheme.residual] using hi)) with hc | hbound
  · exact Finset.mem_union_right _ hc
  · simp [Scheme.generalize] at hbound
    rcases hbound.1 with ht | hc
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _
        (Finset.mem_union_left _ hc)

theorem Constraint.handler_usedTypes_subset {X : Domain}
    (op : Op) (decl : OpDecl)
    (Cin Cr Co : Constraint X) (τr τo a : Ty)
    (εin εr εo δ χ : Effect)
    (localTypes localEffects : Finset Nat) :
    (Constraint.handler op decl Cin Cr Co τr τo a
      εin εr εo δ χ localTypes localEffects).usedTypes ⊆
      Cin.usedTypes ∪ Cr.usedTypes ∪ Co.usedTypes ∪
      τr.fvTypes ∪ τo.fvTypes ∪ a.fvTypes ∪
      decl.typeVars ∪ localTypes := by
  intro i hi
  have hProj :
      i ∈ (Constraint.project localTypes localEffects
        (.and Co (.and (.typeEq τo a) (.effectLe εo χ)))).usedTypes →
      i ∈ Co.usedTypes ∨ i ∈ τo.fvTypes ∨
        i ∈ a.fvTypes ∨ i ∈ localTypes := by
    intro hp
    have hs := Constraint.project_usedTypes_subset
      localTypes localEffects
      (.and Co (.and (.typeEq τo a) (.effectLe εo χ))) hp
    simp [Constraint.usedTypes,
      Constraint.fvTypes, Constraint.boundTypes] at hs ⊢
    aesop
  have hClose : i ∈ (Constraint.close decl.typeVars decl.effectVars
      (Constraint.project localTypes localEffects
        (.and Co (.and (.typeEq τo a) (.effectLe εo χ))))).usedTypes →
      i ∈ Co.usedTypes ∨ i ∈ τo.fvTypes ∨ i ∈ a.fvTypes ∨
        i ∈ decl.typeVars ∨ i ∈ localTypes := by
    intro hc
    rw [Constraint.close_usedTypes] at hc
    rcases Finset.mem_union.mp hc with hp | hd
    · rcases hProj hp with hCo | hτ | ha | hlocal
      · exact Or.inl hCo
      · exact Or.inr (Or.inl hτ)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hlocal)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
  have hSplit : (Constraint.split (X := X) op εin δ).usedTypes = ∅ := by
    simp [Constraint.split,
      Constraint.usedTypes, Constraint.fvTypes, Constraint.boundTypes]
  have hLe₁ : (Constraint.effectLe δ χ : Constraint X).usedTypes = ∅ := rfl
  have hLe₂ : (Constraint.effectLe εr χ : Constraint X).usedTypes = ∅ := rfl
  simp only [Constraint.handler, Constraint.usedTypes_and,
    hSplit, hLe₁, hLe₂, Finset.mem_union] at hi
  simp at hi
  simp only [Finset.mem_union] at ⊢
  have hEq : i ∈ (Constraint.typeEq (X := X) τr a).usedTypes →
      i ∈ τr.fvTypes ∨ i ∈ a.fvTypes := by
    simp [Constraint.usedTypes, Constraint.fvTypes,
      Constraint.boundTypes]
  aesop

theorem Constraint.handler_usedEffects_subset {X : Domain}
    (op : Op) (decl : OpDecl)
    (Cin Cr Co : Constraint X) (τr τo a : Ty)
    (εin εr εo δ χ : Effect)
    (localTypes localEffects : Finset Nat) :
    (Constraint.handler op decl Cin Cr Co τr τo a
      εin εr εo δ χ localTypes localEffects).usedEffects ⊆
      Cin.usedEffects ∪ Cr.usedEffects ∪ Co.usedEffects ∪
      τr.fvEffects ∪ τo.fvEffects ∪ a.fvEffects ∪
      εin.vars ∪ εr.vars ∪ εo.vars ∪ δ.vars ∪ χ.vars ∪
      decl.effectVars ∪ localEffects := by
  intro i hi
  have hProj :
      i ∈ (Constraint.project localTypes localEffects
        (.and Co (.and (.typeEq τo a) (.effectLe εo χ)))).usedEffects →
      i ∈ Co.usedEffects ∨ i ∈ τo.fvEffects ∨
        i ∈ a.fvEffects ∨ i ∈ εo.vars ∨ i ∈ χ.vars ∨
        i ∈ localEffects := by
    intro hp
    have hs := Constraint.project_usedEffects_subset
      localTypes localEffects
      (.and Co (.and (.typeEq τo a) (.effectLe εo χ))) hp
    simp [Constraint.usedEffects,
      Constraint.fvEffects, Constraint.boundEffects] at hs ⊢
    aesop
  have hClose : i ∈ (Constraint.close decl.typeVars decl.effectVars
      (Constraint.project localTypes localEffects
        (.and Co (.and (.typeEq τo a) (.effectLe εo χ))))).usedEffects →
      i ∈ Co.usedEffects ∨ i ∈ τo.fvEffects ∨ i ∈ a.fvEffects ∨
        i ∈ εo.vars ∨ i ∈ χ.vars ∨ i ∈ decl.effectVars ∨
        i ∈ localEffects := by
    intro hc
    rw [Constraint.close_usedEffects] at hc
    rcases Finset.mem_union.mp hc with hp | hd
    · rcases hProj hp with hCo | hτ | ha | hε | hχ | hlocal
      · exact Or.inl hCo
      · exact Or.inr (Or.inl hτ)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hε)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hχ))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlocal)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hd)))))
  simp only [Constraint.handler, Constraint.usedEffects_and,
    Finset.mem_union] at hi ⊢
  have hEqR : i ∈ (Constraint.typeEq (X := X) τr a).usedEffects →
      i ∈ τr.fvEffects ∨ i ∈ a.fvEffects := by
    simp [Constraint.usedEffects, Constraint.fvEffects,
      Constraint.boundEffects]
  have hSplit : i ∈ (Constraint.split (X := X) op εin δ).usedEffects →
      i ∈ εin.vars ∨ i ∈ δ.vars := by
    simp [Constraint.split, Constraint.usedEffects,
      Constraint.fvEffects, Constraint.boundEffects]
    aesop
  have hLe₁ : i ∈ (Constraint.effectLe (X := X) δ χ).usedEffects →
      i ∈ δ.vars ∨ i ∈ χ.vars := by
    simp [Constraint.usedEffects, Constraint.fvEffects,
      Constraint.boundEffects]
  have hLe₂ : i ∈ (Constraint.effectLe (X := X) εr χ).usedEffects →
      i ∈ εr.vars ∨ i ∈ χ.vars := by
    simp [Constraint.usedEffects, Constraint.fvEffects,
      Constraint.boundEffects]
  aesop

/-- The handler constructor keeps every constraint name inside its returned supply. -/
theorem Output.handler_support_below {X : Domain}
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
    (hdeclT : ∀ i ∈ decl.typeVars, i < rc.next.types)
    (hdeclE : ∀ i ∈ decl.effectVars, i < rc.next.effects)
    (ha : sb.types < rc.next.types)
    (hδ : sb.effects < rc.next.effects)
    (hχ : sb.effects + 1 < rc.next.effects)
    (hlocalT : ∀ i ∈ localTypes, i < rc.next.types)
    (hlocalE : ∀ i ∈ localEffects, i < rc.next.effects) :
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    let C := Constraint.handler op decl
      rb.constraints rr.constraints rc.constraints
      rr.ty rc.ty a rb.effect rr.effect rc.effect δ χ
      localTypes localEffects
    let r : Output X := ⟨a, χ, C, rc.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    have hs := Constraint.handler_usedTypes_subset op decl
      rb.constraints rr.constraints rc.constraints
      rr.ty rc.ty (Ty.var sb.types) rb.effect rr.effect rc.effect
      (Poly.Effect.var sb.effects)
      (Poly.Effect.var (sb.effects + 1)) localTypes localEffects
    simp only [Output.supportTypes, Ty.fvTypes,
      Finset.mem_union, Finset.mem_singleton] at hi
    rcases hi with hnew | hC
    · omega
    have h := hs hC
    simp only [Finset.mem_union, Ty.fvTypes,
      Finset.mem_singleton] at h
    have hbC : i ∈ rb.constraints.usedTypes → i < rc.next.types :=
      fun hm => lt_of_lt_of_le
        (hbT i (Finset.mem_union_right _ hm)) hnextB.1
    have hrC : i ∈ rr.constraints.usedTypes → i < rc.next.types :=
      fun hm => lt_of_lt_of_le
        (hrT i (Finset.mem_union_right _ hm)) hnextR.1
    have hcC : i ∈ rc.constraints.usedTypes → i < rc.next.types :=
      fun hm => hcT i (Finset.mem_union_right _ hm)
    have hrTy : i ∈ rr.ty.fvTypes → i < rc.next.types :=
      fun hm => lt_of_lt_of_le
        (hrT i (Finset.mem_union_left _ hm)) hnextR.1
    have hcTy : i ∈ rc.ty.fvTypes → i < rc.next.types :=
      fun hm => hcT i (Finset.mem_union_left _ hm)
    aesop
  · intro i hi
    have hs := Constraint.handler_usedEffects_subset op decl
      rb.constraints rr.constraints rc.constraints
      rr.ty rc.ty (Ty.var sb.types) rb.effect rr.effect rc.effect
      (Poly.Effect.var sb.effects)
      (Poly.Effect.var (sb.effects + 1)) localTypes localEffects
    have hmem : i = sb.effects + 1 ∨
        i ∈ (Constraint.handler op decl
          rb.constraints rr.constraints rc.constraints
          rr.ty rc.ty (Ty.var sb.types) rb.effect rr.effect rc.effect
          (Poly.Effect.var sb.effects)
          (Poly.Effect.var (sb.effects + 1))
          localTypes localEffects).usedEffects := by
      simpa [Output.supportEffects, Ty.fvEffects,
        Poly.Effect.var] using hi
    rcases hmem with hnew | hC
    · omega
    have h := hs hC
    simp only [Finset.mem_union, Ty.fvEffects,
      Poly.Effect.var, Finset.mem_singleton] at h
    have hbC : i ∈ rb.constraints.usedEffects → i < rc.next.effects :=
      fun hm => lt_of_lt_of_le
        (hbE i (by simp [Output.supportEffects, hm])) hnextB.2
    have hrC : i ∈ rr.constraints.usedEffects → i < rc.next.effects :=
      fun hm => lt_of_lt_of_le
        (hrE i (by simp [Output.supportEffects, hm])) hnextR.2
    have hcC : i ∈ rc.constraints.usedEffects → i < rc.next.effects :=
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

/-- Fresh operation binders lie below the supply used to start the
return clause. -/
theorem OpDecl.alphaRename_binders_below_advance
    (raw : OpDecl) (s : Supply) :
    let ρ := renameBound raw.typeVars s.types
    let η := renameBound raw.effectVars s.effects
    let decl := raw.alphaRename ρ η
    let sb := s.advance raw.typeVars raw.effectVars
    (∀ i ∈ decl.typeVars, i < sb.types) ∧
      (∀ i ∈ decl.effectVars, i < sb.effects) := by
  dsimp [OpDecl.alphaRename]
  constructor
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact (s.advance_above_renamed raw.typeVars raw.effectVars).1 j hj
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact (s.advance_above_renamed raw.typeVars raw.effectVars).2 j hj

theorem OpDecl.alphaRename_used_below_advance
    (raw : OpDecl) (s : Supply)
    (ht : ∀ i ∈ raw.usedTypes, i < s.types)
    (he : ∀ i ∈ raw.usedEffects, i < s.effects) :
    let ρ := renameBound raw.typeVars s.types
    let η := renameBound raw.effectVars s.effects
    let decl := raw.alphaRename ρ η
    let sb := s.advance raw.typeVars raw.effectVars
    (∀ i ∈ decl.usedTypes, i < sb.types) ∧
      (∀ i ∈ decl.usedEffects, i < sb.effects) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i ∈ raw.usedTypes.image
        (renameBound raw.typeVars s.types) := by
      simp [OpDecl.usedTypes, OpDecl.alphaRename,
        Ty.fvTypes_rename, Finset.image_union] at hi ⊢
      aesop
    rcases Finset.mem_image.mp hsub with ⟨j, hj, rfl⟩
    exact s.renameBound_types_below_advance
      raw.typeVars raw.effectVars raw.usedTypes ht j hj
  · intro i hi
    have hsub : i ∈ raw.usedEffects.image
        (renameBound raw.effectVars s.effects) := by
      simp [OpDecl.usedEffects, OpDecl.alphaRename,
        Ty.fvEffects_rename, Finset.image_union] at hi ⊢
      aesop
    rcases Finset.mem_image.mp hsub with ⟨j, hj, rfl⟩
    exact s.renameBound_effects_below_advance
      raw.typeVars raw.effectVars raw.usedEffects he j hj

/-- Clause-local names selected from the final supply interval are below
the returned supply. -/
theorem Supply.local_interval_below (s t : Supply) :
    (∀ i ∈ Finset.range t.types \ Finset.range s.types,
      i < t.types) ∧
    (∀ i ∈ Finset.range t.effects \ Finset.range s.effects,
      i < t.effects) := by
  constructor
  · intro i hi
    exact Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1
  · intro i hi
    exact Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1

theorem Output.letVal_support_below {X : Domain}
    (Γ : Context X) (r₁ r₂ : Output X)
    (h₁T : ∀ i ∈ r₁.supportTypes, i < r₁.next.types)
    (h₁E : ∀ i ∈ r₁.supportEffects, i < r₁.next.effects)
    (h₂T : ∀ i ∈ r₂.supportTypes, i < r₂.next.types)
    (h₂E : ∀ i ∈ r₂.supportEffects, i < r₂.next.effects)
    (hnext : r₁.next.types ≤ r₂.next.types ∧
      r₁.next.effects ≤ r₂.next.effects) :
    let r : Output X :=
      ⟨r₂.ty, r₂.effect,
        .and (Scheme.residual Γ r₁.constraints r₁.ty)
          r₂.constraints, r₂.next⟩
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i ∈ r₁.supportTypes ∪ r₂.supportTypes := by
      simp only [Output.supportTypes, Constraint.usedTypes_and,
        Finset.mem_union] at hi ⊢
      rcases hi with hty | hres | hC₂
      · exact Or.inr (Or.inl hty)
      · rcases Finset.mem_union.mp
          (Scheme.residual_supportTypes_subset Γ r₁.constraints r₁.ty
            hres) with hty | hC
        · exact Or.inl (Or.inl hty)
        · exact Or.inl (Or.inr hC)
      · exact Or.inr (Or.inr hC₂)
    rcases Finset.mem_union.mp hsub with h₁ | h₂
    · have := h₁T i h₁
      omega
    · exact h₂T i h₂
  · intro i hi
    have hsub : i ∈ r₁.supportEffects ∪ r₂.supportEffects := by
      have hres := Scheme.residual_supportEffects_subset
        Γ r₁.constraints r₁.ty
      have hresImp : i ∈ (Scheme.residual Γ r₁.constraints r₁.ty).usedEffects →
          i ∈ r₁.ty.fvEffects ∨ i ∈ r₁.constraints.usedEffects := by
        intro h
        exact Finset.mem_union.mp (hres h)
      simp only [Output.supportEffects, Constraint.usedEffects_and,
        Finset.mem_union] at hi ⊢
      aesop
    rcases Finset.mem_union.mp hsub with h₁ | h₂
    · have := h₁E i h₁
      omega
    · exact h₂E i h₂

/-- The value-let residual remains true when the body solver changes only
names allocated after the bound expression. -/
theorem Output.letVal_residual_frame {X : Domain}
    (hX : LawfulSupport X) (Γ : Context X) (r₁ : Output X)
    (hboundT : ∀ i ∈ r₁.supportTypes, i < r₁.next.types)
    (hboundE : ∀ i ∈ r₁.supportEffects, i < r₁.next.effects)
    (v w : Valuation)
    (hRes : (Scheme.residual Γ r₁.constraints r₁.ty).holds v)
    (ht : ∀ i, i < r₁.next.types → v.types i = w.types i)
    (he : ∀ i, i < r₁.next.effects → v.effects i = w.effects i) :
    (Scheme.residual Γ r₁.constraints r₁.ty).holds w := by
  have hst : ∀ i ∈ (Scheme.residual Γ r₁.constraints r₁.ty).fvTypes,
      v.types i = w.types i := by
    intro i hi
    have hu : i ∈ (Scheme.residual Γ r₁.constraints r₁.ty).usedTypes :=
      Finset.mem_union_left _ hi
    have hs := Scheme.residual_supportTypes_subset Γ
      r₁.constraints r₁.ty hu
    exact ht i (hboundT i hs)
  have hse : ∀ i ∈ (Scheme.residual Γ r₁.constraints r₁.ty).fvEffects,
      v.effects i = w.effects i := by
    intro i hi
    have hu : i ∈ (Scheme.residual Γ r₁.constraints r₁.ty).usedEffects :=
      Finset.mem_union_left _ hi
    have hs := Scheme.residual_supportEffects_subset Γ
      r₁.constraints r₁.ty hu
    exact he i (hboundE i (by
      simp [Output.supportEffects] at hs ⊢
      aesop))
  exact (Constraint.holds_support hX
    (Scheme.residual Γ r₁.constraints r₁.ty) v w hst hse).mp hRes

/-- Every successful recursive call stays within the supply allocated for it. -/
theorem generate_support_below {sig : Signature} {X : Domain}
    (hX : LawfulFVRename X)
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (hrun : generate sig X Γ e s = some r) :
    ∀ ops : Finset Op, e.ops ⊆ ops →
      BoundedInputs sig X Γ ops s →
      (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  fun_induction generate sig X Γ e s generalizing r with
  | case1 Γ i s =>
      intro ops hops hb
      cases hσ : Γ[i]? with
      | none => simp [hσ] at hrun
      | some σ =>
          by_cases hsafe : σ.SafeRename
              (renameBound σ.typeVars s.types)
              (renameBound σ.effectVars s.effects)
          · simp [hσ, hsafe] at hrun
            cases hrun
            have hmem : σ ∈ Γ := List.mem_of_getElem? hσ
            have ht := hb.contextTypes σ hmem
            have he := hb.contextEffects σ hmem
            constructor
            · intro j hj
              have hs := Scheme.instantiate_supportTypes_subset hX σ
                (renameBound σ.typeVars s.types)
                (renameBound σ.effectVars s.effects)
              have hj' : j ∈ σ.usedTypes.image
                  (renameBound σ.typeVars s.types) := hs (by
                simpa [Output.supportTypes] using hj)
              rcases Finset.mem_image.mp hj' with ⟨k, hk, rfl⟩
              exact s.renameBound_types_below_advance
                σ.typeVars σ.effectVars σ.usedTypes ht k hk
            · intro j hj
              have hs := Scheme.instantiate_supportEffects_subset hX σ
                (renameBound σ.typeVars s.types)
                (renameBound σ.effectVars s.effects)
              have hj' : j ∈ σ.usedEffects.image
                  (renameBound σ.effectVars s.effects) := hs (by
                simpa [Output.supportEffects] using hj)
              rcases Finset.mem_image.mp hj' with ⟨k, hk, rfl⟩
              exact s.renameBound_effects_below_advance
                σ.typeVars σ.effectVars σ.usedEffects he k hk
          · simp [hσ, hsafe] at hrun
  | case2 Γ n s =>
      intro ops hops hb
      cases hrun
      constructor <;> intro i hi <;>
        simp [Output.supportTypes, Output.supportEffects,
          Constraint.usedTypes, Constraint.usedEffects,
          Constraint.fvTypes, Constraint.fvEffects,
          Constraint.boundTypes, Constraint.boundEffects,
          Ty.fvTypes, Ty.fvEffects] at hi
  | case3 Γ b s =>
      intro ops hops hb
      cases hrun
      constructor <;> intro i hi <;>
        simp [Output.supportTypes, Output.supportEffects,
          Constraint.usedTypes, Constraint.usedEffects,
          Constraint.fvTypes, Constraint.fvEffects,
          Constraint.boundTypes, Constraint.boundEffects,
          Ty.fvTypes, Ty.fvEffects] at hi
  | case4 Γ body s a ih =>
      intro ops hops hb
      cases hr : generate sig X (Scheme.mono a :: Γ) body
          {s with types := s.types + 1} with
      | none => simp [hr] at hrun
      | some rb =>
          simp [hr] at hrun
          cases hrun
          have hbodyOps : body.ops ⊆ ops := by
            intro op hop
            exact hops (by simpa [Expr.ops] using hop)
          have hbase : BoundedInputs sig X Γ ops
              {s with types := s.types + 1} :=
            hb.mono (by dsimp; omega)
          have hchild : BoundedInputs sig X (Scheme.mono a :: Γ) ops
              {s with types := s.types + 1} := by
            apply hbase.consMono a
            · intro i hi
              simp [a, Ty.fvTypes] at hi
              dsimp
              omega
            · intro i hi
              simp [a, Ty.fvEffects] at hi
          have hsup := ih hr ops hbodyOps hchild
          have hm := generate_next_mono hr
          have hnext : s.types < rb.next.types := by
            dsimp at hm
            omega
          exact Output.lam_support_below s rb hsup.1 hsup.2 hnext
  | case5 Γ f x s ihf ihx =>
      intro ops hops hb
      cases hf : generate sig X Γ f s with
      | none => simp [hf] at hrun
      | some rf =>
          cases hx : generate sig X Γ x rf.next with
          | none => simp [hf, hx] at hrun
          | some rx =>
              simp [hf, hx] at hrun
              cases hrun
              have hfOps : f.ops ⊆ ops := by
                intro op hop
                exact hops (by simp [Expr.ops, hop])
              have hxOps : x.ops ⊆ ops := by
                intro op hop
                exact hops (by simp [Expr.ops, hop])
              have hsf := ihf hf ops hfOps hb
              have hmx := generate_next_mono hf
              have hsx := ihx rf hx ops hxOps (hb.mono hmx)
              have hnext := generate_next_mono hx
              exact Output.app_support_below rf rx
                hsf.1 hsf.2 hsx.1 hsx.2 hnext
  | case6 Γ e₁ e₂ s ihBound ihVal ihMono =>
      intro ops hops hb
      cases h₁ : generate sig X Γ e₁ s with
      | none => simp [h₁] at hrun
      | some r₁ =>
          have hfirstOps : e₁.ops ⊆ ops := by
            intro op hop
            exact hops (by simp [Expr.ops, hop])
          have hbodyOps : e₂.ops ⊆ ops := by
            intro op hop
            exact hops (by simp [Expr.ops, hop])
          have hs₁ := ihBound h₁ ops hfirstOps hb
          have hbase := hb.mono (generate_next_mono h₁)
          cases hv : e₁.isValue with
          | true =>
              cases h₂ : generate sig X
                  (Scheme.generalize Γ r₁.constraints r₁.ty :: Γ)
                  e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at hrun
              | some r₂ =>
                  simp [h₁, hv, h₂] at hrun
                  cases hrun
                  have hctx := hbase.consGeneralize
                    r₁.constraints r₁.ty
                    (by simpa [Output.supportTypes] using hs₁.1)
                    (by
                      intro i hi
                      exact hs₁.2 i (by
                        simp [Output.supportEffects] at hi ⊢
                        aesop))
                  have hs₂ := ihVal r₁ h₂ ops hbodyOps hctx
                  exact Output.letVal_support_below Γ r₁ r₂
                    hs₁.1 hs₁.2 hs₂.1 hs₂.2
                    (generate_next_mono h₂)
          | false =>
              cases h₂ : generate sig X
                  (Scheme.mono r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at hrun
              | some r₂ =>
                  simp [h₁, hv, h₂] at hrun
                  cases hrun
                  have hctx := hbase.consMono r₁.ty
                    (fun i hi => hs₁.1 i
                      (Finset.mem_union_left _ hi))
                    (fun i hi => hs₁.2 i
                      (by simp [Output.supportEffects, hi]))
                  have hs₂ := ihMono r₁ h₂ ops hbodyOps hctx
                  exact Output.letMono_support_below r₁ r₂
                    hs₁.1 hs₁.2 hs₂.1 hs₂.2
                    (generate_next_mono h₂)
  | case7 Γ op e s ih =>
      intro ops hops hb
      cases hd : sig op with
      | none => simp [hd] at hrun
      | some decl =>
          cases he : generate sig X Γ e
              (s.advance decl.typeVars decl.effectVars) with
          | none => simp [hd, he] at hrun
          | some re =>
              simp [hd, he] at hrun
              cases hrun
              have hop : op ∈ ops := hops (by simp [Expr.ops])
              have hchildOps : e.ops ⊆ ops := by
                intro op' hop'
                exact hops (by simp [Expr.ops, hop'])
              have hdecl := hb.signature op hop decl hd
              have hchild := hb.mono ⟨
                Nat.le_of_lt (s.advance_mono
                  decl.typeVars decl.effectVars).1,
                Nat.le_of_lt (s.advance_mono
                  decl.typeVars decl.effectVars).2⟩
              have hsup := ih decl he ops hchildOps hchild
              exact Output.perform_support_below s decl op re
                hdecl.1 hdecl.2 hsup.1 hsup.2
                (generate_next_mono he)
  | case8 Γ body op ret clause s ihBody ihRet ihClause =>
      intro ops hops hb
      cases hd : sig op with
      | none => simp [hd] at hrun
      | some raw =>
          cases hbody : generate sig X Γ body s with
          | none => simp [hd, hbody] at hrun
          | some rb =>
              let ρ := renameBound raw.typeVars rb.next.types
              let η := renameBound raw.effectVars rb.next.effects
              let decl := raw.alphaRename ρ η
              let sb := rb.next.advance raw.typeVars raw.effectVars
              let a := Ty.var sb.types
              let δ := Poly.Effect.var sb.effects
              let χ := Poly.Effect.var (sb.effects + 1)
              let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
              cases hret : generate sig X
                  (Scheme.mono rb.ty :: Γ) ret sr with
              | none => simp [hd, hbody, hret, sb, sr] at hrun
              | some rr =>
                  cases hclause : generate sig X
                      (Scheme.mono (.arr decl.output χ a) ::
                        Scheme.mono decl.input :: Γ) clause rr.next with
                  | none =>
                      simp [hd, hbody, hret, hclause,
                        ρ, η, decl, sb, a, χ, sr] at hrun
                  | some rc =>
                      let localTypes := Finset.range rc.next.types \
                        Finset.range rr.next.types
                      let localEffects := Finset.range rc.next.effects \
                        Finset.range rr.next.effects
                      let C := Constraint.handler op decl
                        rb.constraints rr.constraints rc.constraints
                        rr.ty rc.ty a rb.effect rr.effect rc.effect δ χ
                        localTypes localEffects
                      have hop : op ∈ ops := hops (by simp [Expr.ops])
                      have hbodyOps : body.ops ⊆ ops := by
                        intro op' h
                        exact hops (by simp [Expr.ops, h])
                      have hretOps : ret.ops ⊆ ops := by
                        intro op' h
                        exact hops (by simp [Expr.ops, h])
                      have hclauseOps : clause.ops ⊆ ops := by
                        intro op' h
                        exact hops (by simp [Expr.ops, h])
                      have hsb := ihBody hbody ops hbodyOps hb
                      have hmBody := generate_next_mono hbody
                      have hbase := hb.mono hmBody
                      have hraw := hbase.signature op hop raw hd
                      have hdecl := OpDecl.alphaRename_used_below_advance
                        raw rb.next hraw.1 hraw.2
                      have hadvance := rb.next.advance_mono
                        raw.typeVars raw.effectVars
                      have hrbSr :
                          rb.next.types ≤ sr.types ∧
                          rb.next.effects ≤ sr.effects := by
                        dsimp [sr, sb]
                        omega
                      have hretBase := hbase.mono hrbSr
                      have hretCtx := hretBase.consMono rb.ty
                        (fun i hi => lt_of_lt_of_le
                          (hsb.1 i (Finset.mem_union_left _ hi))
                          hrbSr.1)
                        (fun i hi => lt_of_lt_of_le
                          (hsb.2 i (by simp [Output.supportEffects, hi]))
                          hrbSr.2)
                      have hsret := ihRet raw rb hret ops hretOps hretCtx
                      have hmRet := generate_next_mono hret
                      have hsbRr :
                          sb.types ≤ rr.next.types ∧
                          sb.effects ≤ rr.next.effects := by
                        dsimp [sr] at hmRet
                        omega
                      have haRr : sb.types < rr.next.types := by
                        have h := hmRet.1
                        dsimp [sr] at h
                        omega
                      have hχRr : sb.effects + 1 < rr.next.effects := by
                        have h := hmRet.2
                        dsimp [sr] at h
                        omega
                      have hclauseBase : BoundedInputs sig X Γ ops rr.next :=
                        hbase.mono ⟨hrbSr.1.trans hmRet.1,
                          hrbSr.2.trans hmRet.2⟩
                      have hdeclT : ∀ i ∈ decl.usedTypes,
                          i < rr.next.types := by
                        intro i hi
                        exact lt_of_lt_of_le (hdecl.1 i hi) hsbRr.1
                      have hdeclE : ∀ i ∈ decl.usedEffects,
                          i < rr.next.effects := by
                        intro i hi
                        exact lt_of_lt_of_le (hdecl.2 i hi) hsbRr.2
                      have hinputT : ∀ i ∈ decl.input.fvTypes,
                          i < rr.next.types := by
                        intro i hi
                        exact hdeclT i (by simp [OpDecl.usedTypes, hi])
                      have hinputE : ∀ i ∈ decl.input.fvEffects,
                          i < rr.next.effects := by
                        intro i hi
                        exact hdeclE i (by simp [OpDecl.usedEffects, hi])
                      have houtputT : ∀ i ∈ decl.output.fvTypes,
                          i < rr.next.types := by
                        intro i hi
                        exact hdeclT i (by simp [OpDecl.usedTypes, hi])
                      have houtputE : ∀ i ∈ decl.output.fvEffects,
                          i < rr.next.effects := by
                        intro i hi
                        exact hdeclE i (by simp [OpDecl.usedEffects, hi])
                      have hclauseCtx₁ := hclauseBase.consMono decl.input
                        hinputT hinputE
                      have hclauseCtx := hclauseCtx₁.consMono
                        (.arr decl.output χ a)
                        (by
                          intro i hi
                          simp [Ty.fvTypes] at hi
                          rcases hi with hout | ha
                          · exact houtputT i hout
                          · simp [a, Ty.fvTypes] at ha
                            omega)
                        (by
                          intro i hi
                          simp [Ty.fvEffects, χ, a,
                            Poly.Effect.var] at hi
                          rcases hi with hχ | hout
                          · omega
                          · exact houtputE i hout)
                      have hsclause := ihClause raw rb rr hclause
                        ops hclauseOps hclauseCtx
                      have hmClause := generate_next_mono hclause
                      have hnextB :
                          rb.next.types ≤ rc.next.types ∧
                          rb.next.effects ≤ rc.next.effects :=
                        ⟨(hrbSr.1.trans hmRet.1).trans hmClause.1,
                          (hrbSr.2.trans hmRet.2).trans hmClause.2⟩
                      have hnextR := hmClause
                      have hdeclFinalT : ∀ i ∈ decl.typeVars,
                          i < rc.next.types := by
                        intro i hi
                        have hmember : i ∈ decl.usedTypes := by
                          simp [OpDecl.usedTypes, hi]
                        exact lt_of_lt_of_le
                          (hdeclT i hmember) hmClause.1
                      have hdeclFinalE : ∀ i ∈ decl.effectVars,
                          i < rc.next.effects := by
                        intro i hi
                        have hmember : i ∈ decl.usedEffects := by
                          simp [OpDecl.usedEffects, hi]
                        exact lt_of_lt_of_le
                          (hdeclE i hmember) hmClause.2
                      have hlocal := Supply.local_interval_below
                        rr.next rc.next
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hscope : decl.HandlerScope Γ
                          rb.ty a rb.effect rr.effect δ χ
                        · by_cases hclauseScope : decl.ClauseScope Γ C
                            rb.ty a rb.effect rr.effect δ χ
                            localTypes localEffects
                          · simp [hd, hbody, hret, hclause,
                              hsafe, hscope, hclauseScope,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at hrun
                            cases hrun
                            apply Output.handler_support_below
                              op decl sb rb rr rc
                              localTypes localEffects
                              hsb.1 hsb.2 hsret.1 hsret.2
                              hsclause.1 hsclause.2
                              hnextB hnextR
                              hdeclFinalT hdeclFinalE
                            · dsimp [sr] at hmRet
                              omega
                            · dsimp [sr] at hmRet
                              omega
                            · dsimp [sr] at hmRet
                              omega
                            · exact hlocal.1
                            · exact hlocal.2
                          · simp [hd, hbody, hret, hclause,
                              hsafe, hscope, hclauseScope,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at hrun
                        · simp [hd, hbody, hret, hclause,
                            hsafe, hscope,
                            ρ, η, decl, sb, a, δ, χ, sr] at hrun
                      · simp [hd, hbody, hret,
                          hsafe, ρ, η, sb, sr] at hrun

/-- The public generator satisfies the support invariant for every
expression, including value lets and handlers. -/
theorem generateFresh_support_below {sig : Signature} {X : Domain}
    (hX : LawfulFVRename X) (Γ : Context X) (e : Expr)
    (s : Supply) (r : Output X)
    (h : generateFresh sig X Γ e s = some r) :
    (∀ i ∈ r.supportTypes, i < r.next.types) ∧
      (∀ i ∈ r.supportEffects, i < r.next.effects) := by
  change generate sig X Γ e (s.seed sig Γ e []) = some r at h
  exact generate_support_below hX h e.ops (Finset.Subset.rfl)
    (BoundedInputs.seed Γ e s)

/-- A solution of a generated result remains a solution after later fresh
assignments, provided earlier supply names are preserved. -/
theorem generateFresh_solution_frame {sig : Signature} {X : Domain}
    (hRename : LawfulFVRename X) (hSupport : LawfulSupport X)
    (Γ : Context X) (e : Expr) (s : Supply) (r : Output X)
    (h : generateFresh sig X Γ e s = some r)
    (v w : Valuation)
    (ht : ∀ i, i < r.next.types → v.types i = w.types i)
    (he : ∀ i, i < r.next.effects → v.effects i = w.effects i) :
    (r.constraints.holds v ↔ r.constraints.holds w) ∧
      r.ty.eval v = r.ty.eval w ∧
      r.effect.eval v.effects = r.effect.eval w.effects := by
  have hs := generateFresh_support_below hRename Γ e s r h
  exact r.semantic_frame_of_below hSupport v w hs.1 hs.2 ht he

private noncomputable def assignImage {α : Type}
    (bound : Finset Nat) (rename : Nat → Nat)
    (values original : Nat → α) (j : Nat) : α :=
  if h : ∃ i, i ∈ bound ∧ rename i = j then
    values (Classical.choose h)
  else original j

private theorem assignImage_mem {α : Type}
    (bound : Finset Nat) (rename : Nat → Nat)
    (hinj : Set.InjOn rename bound)
    (values original : Nat → α) (i : Nat) (hi : i ∈ bound) :
    assignImage bound rename values original (rename i) = values i := by
  let h : ∃ k, k ∈ bound ∧ rename k = rename i := ⟨i, hi, rfl⟩
  have hc := Classical.choose_spec h
  have hki : Classical.choose h = i := hinj hc.1 hi hc.2
  simp [assignImage, h, hki]

private theorem assignImage_not_mem {α : Type}
    (bound : Finset Nat) (rename : Nat → Nat)
    (values original : Nat → α) (j : Nat)
    (hj : j ∉ bound.image rename) :
    assignImage bound rename values original j = original j := by
  have hnone : ¬ ∃ i, i ∈ bound ∧ rename i = j := by
    rintro ⟨i, hi, rfl⟩
    exact hj (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  simp [assignImage, hnone]

/-- A ground use of a qualified scheme chooses its quantified type and effect
variables while keeping the other variables fixed. -/
def Scheme.GroundInstance {X : Domain} (σ : Scheme X)
    (ρ : Valuation) (t : GroundTy) : Prop :=
  ∃ ft : Nat → GroundTy, ∃ fe : Nat → Finset Op,
    (∀ i, i ∉ σ.typeVars → ft i = ρ.types i) ∧
    (∀ i, i ∉ σ.effectVars → fe i = ρ.effects i) ∧
    σ.predicates.holds ⟨ft, fe⟩ ∧ σ.result.eval ⟨ft, fe⟩ = t

/-- Pointwise inclusion of admissible ground uses; this is the semantic
counterpart of HM(X)'s constrained scheme instance preorder. -/
def Scheme.MoreGeneralAt {X : Domain} (σg σd : Scheme X)
    (ρg ρd : Valuation) : Prop :=
  ∀ t, σd.GroundInstance ρd t → σg.GroundInstance ρg t

def Context.MoreGeneralAt {X : Domain} (Γg Γd : Context X)
    (ρg ρd : Valuation) : Prop :=
  List.Forall₂ (fun σg σd => σg.MoreGeneralAt σd ρg ρd) Γg Γd

theorem Context.lookup_of_length_eq {X : Domain}
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


theorem Context.moreGeneralAt_refl {X : Domain} (Γ : Context X)
    (ρ : Valuation) : Γ.MoreGeneralAt Γ ρ ρ := by
  induction Γ with
  | nil => exact List.Forall₂.nil
  | cons σ rest ih =>
      exact List.Forall₂.cons (by intro t h; exact h) ih

theorem Context.moreGeneralAt_lookup {X : Domain}
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

theorem Scheme.moreGeneralAt_refl {X : Domain} (σ : Scheme X)
    (ρ : Valuation) : σ.MoreGeneralAt σ ρ ρ := by
  intro t h
  exact h

theorem Scheme.moreGeneralAt_trans {X : Domain}
    {σ₁ σ₂ σ₃ : Scheme X} {ρ₁ ρ₂ ρ₃ : Valuation}
    (h₁₂ : σ₁.MoreGeneralAt σ₂ ρ₁ ρ₂)
    (h₂₃ : σ₂.MoreGeneralAt σ₃ ρ₂ ρ₃) :
    σ₁.MoreGeneralAt σ₃ ρ₁ ρ₃ := by
  intro t h
  exact h₁₂ t (h₂₃ t h)

/-- A scheme use depends on the surrounding valuation only through its free
names. The witnesses for quantified names can be carried across unchanged. -/
theorem Scheme.groundInstance_support {X : Domain}
    (hX : LawfulSupport X) (σ : Scheme X) (v w : Valuation)
    (ht : ∀ i ∈ σ.fvTypes, v.types i = w.types i)
    (he : ∀ i ∈ σ.fvEffects, v.effects i = w.effects i)
    (t : GroundTy) :
    σ.GroundInstance v t ↔ σ.GroundInstance w t := by
  have forward (v w : Valuation)
      (ht : ∀ i ∈ σ.fvTypes, v.types i = w.types i)
      (he : ∀ i ∈ σ.fvEffects, v.effects i = w.effects i)
      (h : σ.GroundInstance v t) : σ.GroundInstance w t := by
    rcases h with ⟨ft, fe, hft, hfe, hp, hr⟩
    let wt : Nat → GroundTy := fun i =>
      if i ∈ σ.typeVars then ft i else w.types i
    let we : Nat → Finset Op := fun i =>
      if i ∈ σ.effectVars then fe i else w.effects i
    have hty : ∀ i ∈ σ.result.fvTypes ∪ σ.predicates.fvTypes,
        ft i = wt i := by
      intro i hi
      by_cases hb : i ∈ σ.typeVars
      · simp [wt, hb]
      · have hf : i ∈ σ.fvTypes := Finset.mem_sdiff.mpr ⟨hi, hb⟩
        simp [wt, hb, hft i hb, ht i hf]
    have heff : ∀ i ∈ σ.result.fvEffects ∪ σ.predicates.fvEffects,
        fe i = we i := by
      intro i hi
      by_cases hb : i ∈ σ.effectVars
      · simp [we, hb]
      · have hf : i ∈ σ.fvEffects := Finset.mem_sdiff.mpr ⟨hi, hb⟩
        simp [we, hb, hfe i hb, he i hf]
    refine ⟨wt, we, ?_, ?_, ?_, ?_⟩
    · intro i hi; simp [wt, hi]
    · intro i hi; simp [we, hi]
    · exact (Constraint.holds_support hX σ.predicates ⟨ft, fe⟩ ⟨wt, we⟩
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

theorem Scheme.moreGeneralAt_support {X : Domain}
    (hX : LawfulSupport X) (σg σd : Scheme X)
    (vg wg vd wd : Valuation)
    (h : σg.MoreGeneralAt σd vg vd)
    (hgt : ∀ i ∈ σg.fvTypes, vg.types i = wg.types i)
    (hge : ∀ i ∈ σg.fvEffects, vg.effects i = wg.effects i)
    (hdt : ∀ i ∈ σd.fvTypes, vd.types i = wd.types i)
    (hde : ∀ i ∈ σd.fvEffects, vd.effects i = wd.effects i) :
    σg.MoreGeneralAt σd wg wd := by
  intro t hd
  have hd' := (σd.groundInstance_support hX vd wd hdt hde t).mpr hd
  have hg' := h t hd'
  exact (σg.groundInstance_support hX vg wg hgt hge t).mp hg'

/-- Existing context instances remain related when evaluation changes only
names outside every scheme's free support. -/
theorem Context.moreGeneralAt_support {X : Domain}
    (hX : LawfulSupport X)
    (Γg Γd : Context X) (vg wg vd wd : Valuation)
    (h : Γg.MoreGeneralAt Γd vg vd)
    (hgt : ∀ σ ∈ Γg, ∀ i ∈ σ.fvTypes, vg.types i = wg.types i)
    (hge : ∀ σ ∈ Γg, ∀ i ∈ σ.fvEffects, vg.effects i = wg.effects i)
    (hdt : ∀ σ ∈ Γd, ∀ i ∈ σ.fvTypes, vd.types i = wd.types i)
    (hde : ∀ σ ∈ Γd, ∀ i ∈ σ.fvEffects, vd.effects i = wd.effects i) :
    Γg.MoreGeneralAt Γd wg wd := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons σg σd Γg Γd hhead htail ih =>
      apply List.Forall₂.cons
      · exact σg.moreGeneralAt_support hX σd vg wg vd wd hhead
          (hgt σg (by simp)) (hge σg (by simp))
          (hdt σd (by simp)) (hde σd (by simp))
      · apply ih
        · intro σ hs i hi; exact hgt σ (by simp [hs]) i hi
        · intro σ hs i hi; exact hge σ (by simp [hs]) i hi
        · intro σ hs i hi; exact hdt σ (by simp [hs]) i hi
        · intro σ hs i hi; exact hde σ (by simp [hs]) i hi

/-- Assignments above the current supply leave every scheme relation in
the generated context unchanged. -/
theorem Context.moreGeneralAt_below {sig : Signature} {X : Domain}
    (hX : LawfulSupport X)
    (Γg Γd : Context X) (ops : Finset Op) (s : Supply)
    (hb : BoundedInputs sig X Γg ops s)
    (vg wg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd)
    (ht : ∀ i, i < s.types → vg.types i = wg.types i)
    (he : ∀ i, i < s.effects → vg.effects i = wg.effects i) :
    Γg.MoreGeneralAt Γd wg vd := by
  apply Context.moreGeneralAt_support hX Γg Γd vg wg vd vd hctx
  · intro σ hσ i hi
    exact ht i (hb.contextTypes σ hσ i
      (Scheme.fvTypes_subset_usedTypes σ hi))
  · intro σ hσ i hi
    exact he i (hb.contextEffects σ hσ i
      (Scheme.fvEffects_subset_usedEffects σ hi))
  · intro σ hσ i hi
    rfl
  · intro σ hσ i hi
    rfl

theorem Scheme.mono_groundInstance_iff {X : Domain} (τ : Ty)
    (ρ : Valuation) (t : GroundTy) :
    (Scheme.mono (X := X) τ).GroundInstance ρ t ↔ τ.eval ρ = t := by
  constructor
  · rintro ⟨ft, fe, hft, hfe, _, ht⟩
    have hft' : ft = ρ.types := funext (fun i => hft i (by simp [Scheme.mono]))
    have hfe' : fe = ρ.effects := funext (fun i => hfe i (by simp [Scheme.mono]))
    simpa [hft', hfe', Scheme.mono] using ht
  · intro ht
    exact ⟨ρ.types, ρ.effects, by simp [Scheme.mono],
      by simp [Scheme.mono], trivial, ht⟩

theorem Scheme.mono_moreGeneralAt_iff {X : Domain}
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

theorem Scheme.instantiate_groundInstance_of_injective {X : Domain}
    (hX : LawfulRename X) (σ : Scheme X)
    (ρ η : Nat → Nat) (hρ : Function.Injective ρ)
    (hη : Function.Injective η) (hadm : σ.AdmissibleRename ρ η)
    (v : Valuation)
    (hpred : (σ.instantiate ρ η).2.holds v) :
    σ.GroundInstance v ((σ.instantiate ρ η).1.eval v) := by
  refine ⟨v.types ∘ ρ, v.effects ∘ η, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [hadm.1 i hi]
  · intro i hi
    simp [hadm.2 i hi]
  · exact (Constraint.holds_rename_injective hX σ.predicates
      ρ η hρ hη v).mp hpred
  · simp [Scheme.instantiate, Ty.eval_rename, Valuation.pullback]

/-- `SafeRename` supplies exactly the finite non-capture condition required
by quantified predicates inside a scheme. -/
theorem Scheme.renameSafe_predicates {X : Domain} (σ : Scheme X)
    (ρ η : Nat → Nat) (hadm : σ.AdmissibleRename ρ η)
    (hsafe : σ.SafeRename ρ η) :
    σ.predicates.RenameSafe ρ η := by
  constructor
  · intro i hi j hj hij
    let A := σ.typeVars
    have hinj : Set.InjOn ρ A := Finset.injOn_of_card_image_eq hsafe.1
    have hno : ∀ z, z ∈ A.image ρ →
        z ∈ σ.fvTypes ∪ σ.predicates.boundTypes → False := by
      intro z hz hu
      have hm : z ∈ A.image ρ ∩
          (σ.fvTypes ∪ σ.predicates.boundTypes) :=
        Finset.mem_inter.mpr ⟨hz, hu⟩
      rw [hsafe.2.2.1] at hm
      simp at hm
    have hused (k : Nat) (hk : k ∈ σ.predicates.usedTypes)
        (hkA : k ∉ A) :
        k ∈ σ.fvTypes ∪ σ.predicates.boundTypes := by
      rcases Finset.mem_union.mp hk with hf | hb
      · change k ∉ σ.typeVars at hkA
        exact Finset.mem_union_left _ (by
          simp [Scheme.fvTypes, hf, hkA])
      · exact Finset.mem_union_right _ hb
    by_cases hiA : i ∈ A
    · by_cases hjA : j ∈ A
      · exact fun heq => hij (hinj hiA hjA heq)
      · intro heq
        have hz : ρ i ∈ A.image ρ := Finset.mem_image.mpr ⟨i, hiA, rfl⟩
        have hjfix := hadm.1 j hjA
        apply hno (ρ i) hz
        rw [heq, hjfix]
        exact hused j hj hjA
    · by_cases hjA : j ∈ A
      · intro heq
        have hz : ρ j ∈ A.image ρ := Finset.mem_image.mpr ⟨j, hjA, rfl⟩
        apply hno (ρ j) hz
        rw [← heq, hadm.1 i hiA]
        exact Finset.mem_union_right _ hi
      · simpa [hadm.1 i hiA, hadm.1 j hjA] using hij
  · intro i hi j hj hij
    let A := σ.effectVars
    have hinj : Set.InjOn η A := Finset.injOn_of_card_image_eq hsafe.2.1
    have hno : ∀ z, z ∈ A.image η →
        z ∈ σ.fvEffects ∪ σ.predicates.boundEffects → False := by
      intro z hz hu
      have hm : z ∈ A.image η ∩
          (σ.fvEffects ∪ σ.predicates.boundEffects) :=
        Finset.mem_inter.mpr ⟨hz, hu⟩
      rw [hsafe.2.2.2] at hm
      simp at hm
    have hused (k : Nat) (hk : k ∈ σ.predicates.usedEffects)
        (hkA : k ∉ A) :
        k ∈ σ.fvEffects ∪ σ.predicates.boundEffects := by
      rcases Finset.mem_union.mp hk with hf | hb
      · change k ∉ σ.effectVars at hkA
        exact Finset.mem_union_left _ (by
          simp [Scheme.fvEffects, hf, hkA])
      · exact Finset.mem_union_right _ hb
    by_cases hiA : i ∈ A
    · by_cases hjA : j ∈ A
      · exact fun heq => hij (hinj hiA hjA heq)
      · intro heq
        have hz : η i ∈ A.image η := Finset.mem_image.mpr ⟨i, hiA, rfl⟩
        have hjfix := hadm.2 j hjA
        apply hno (η i) hz
        rw [heq, hjfix]
        exact hused j hj hjA
    · by_cases hjA : j ∈ A
      · intro heq
        have hz : η j ∈ A.image η := Finset.mem_image.mpr ⟨j, hjA, rfl⟩
        apply hno (η j) hz
        rw [← heq, hadm.2 i hiA]
        exact Finset.mem_union_right _ hi
      · simpa [hadm.2 i hiA, hadm.2 j hjA] using hij

theorem Scheme.instantiate_groundInstance {X : Domain}
    (hRename : LawfulRename X) (hSupport : LawfulSupport X)
    (σ : Scheme X) (ρ η : Nat → Nat)
    (hadm : σ.AdmissibleRename ρ η)
    (hsafe : σ.SafeRename ρ η) (v : Valuation)
    (hpred : (σ.instantiate ρ η).2.holds v) :
    σ.GroundInstance v ((σ.instantiate ρ η).1.eval v) := by
  let ft : Nat → GroundTy := fun i =>
    if i ∈ σ.typeVars then v.types (ρ i) else v.types i
  let fe : Nat → Finset Op := fun i =>
    if i ∈ σ.effectVars then v.effects (η i) else v.effects i
  have hft : ft = v.types ∘ ρ := by
    funext i
    by_cases hi : i ∈ σ.typeVars
    · simp [ft, hi]
    · simp [ft, hi, hadm.1 i hi]
  have hfe : fe = v.effects ∘ η := by
    funext i
    by_cases hi : i ∈ σ.effectVars
    · simp [fe, hi]
    · simp [fe, hi, hadm.2 i hi]
  refine ⟨ft, fe, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [ft, hi]
  · intro i hi
    simp [fe, hi]
  · have hp := (Constraint.holds_rename_safe hRename hSupport
      σ.predicates ρ η v (σ.renameSafe_predicates ρ η hadm hsafe)).mp hpred
    simpa [hft, hfe, Valuation.pullback] using hp
  · simp [hft, hfe, Scheme.instantiate, Ty.eval_rename,
      Valuation.pullback]

/-- Every ground scheme instance can be represented by a safe fresh
instantiation after assigning its bound witnesses to the renamed variables. -/
theorem Scheme.groundInstance_realizable_fixed {X : Domain}
    (hRename : LawfulRename X) (hSupport : LawfulSupport X)
    (σ : Scheme X) (ρ η : Nat → Nat)
    (hadm : σ.AdmissibleRename ρ η)
    (hsafe : σ.SafeRename ρ η)
    (fixedTypes fixedEffects : Finset Nat)
    (hdisjT : (σ.typeVars.image ρ) ∩ fixedTypes = ∅)
    (hdisjE : (σ.effectVars.image η) ∩ fixedEffects = ∅)
    (v : Valuation) (t : GroundTy)
    (hinst : σ.GroundInstance v t) :
    ∃ w : Valuation,
      (∀ i ∈ σ.fvTypes, w.types i = v.types i) ∧
      (∀ i ∈ σ.fvEffects, w.effects i = v.effects i) ∧
      (∀ i ∈ fixedTypes, w.types i = v.types i) ∧
      (∀ i ∈ fixedEffects, w.effects i = v.effects i) ∧
      (σ.instantiate ρ η).2.holds w ∧
      (σ.instantiate ρ η).1.eval w = t := by
  classical
  rcases hinst with ⟨ft, fe, hft, hfe, hc, ht⟩
  let w : Valuation :=
    ⟨assignImage σ.typeVars ρ ft v.types,
      assignImage σ.effectVars η fe v.effects⟩
  have hinjT : Set.InjOn ρ σ.typeVars :=
    Finset.injOn_of_card_image_eq hsafe.1
  have hinjE : Set.InjOn η σ.effectVars :=
    Finset.injOn_of_card_image_eq hsafe.2.1
  have hfixedT : ∀ i ∈ σ.fvTypes, w.types i = v.types i := by
    intro i hi
    apply assignImage_not_mem
    intro himg
    have hm : i ∈ σ.typeVars.image ρ ∩
        (σ.fvTypes ∪ σ.predicates.boundTypes) :=
      Finset.mem_inter.mpr ⟨himg, Finset.mem_union_left _ hi⟩
    rw [hsafe.2.2.1] at hm
    simp at hm
  have hfixedE : ∀ i ∈ σ.fvEffects, w.effects i = v.effects i := by
    intro i hi
    apply assignImage_not_mem
    intro himg
    have hm : i ∈ σ.effectVars.image η ∩
        (σ.fvEffects ∪ σ.predicates.boundEffects) :=
      Finset.mem_inter.mpr ⟨himg, Finset.mem_union_left _ hi⟩
    rw [hsafe.2.2.2] at hm
    simp at hm
  have hagreeT : ∀ i ∈ σ.result.fvTypes ∪ σ.predicates.fvTypes,
      ft i = (w.pullback ρ η).types i := by
    intro i hi
    by_cases hiA : i ∈ σ.typeVars
    · simp [Valuation.pullback, w,
        assignImage_mem σ.typeVars ρ hinjT ft v.types i hiA]
    · have hfree : i ∈ σ.fvTypes :=
        Finset.mem_sdiff.mpr ⟨hi, hiA⟩
      have hfix := hfixedT i hfree
      have hbase := hft i hiA
      simp [Valuation.pullback, hadm.1 i hiA, hfix, hbase]
  have hagreeE : ∀ i ∈ σ.result.fvEffects ∪ σ.predicates.fvEffects,
      fe i = (w.pullback ρ η).effects i := by
    intro i hi
    by_cases hiA : i ∈ σ.effectVars
    · simp [Valuation.pullback, w,
        assignImage_mem σ.effectVars η hinjE fe v.effects i hiA]
    · have hfree : i ∈ σ.fvEffects :=
        Finset.mem_sdiff.mpr ⟨hi, hiA⟩
      have hfix := hfixedE i hfree
      have hbase := hfe i hiA
      simp [Valuation.pullback, hadm.2 i hiA, hfix, hbase]
  have hpredPullback : σ.predicates.holds (w.pullback ρ η) :=
    (Constraint.holds_support hSupport σ.predicates ⟨ft, fe⟩
      (w.pullback ρ η)
      (fun i hi => hagreeT i (Finset.mem_union_right _ hi))
      (fun i hi => hagreeE i (Finset.mem_union_right _ hi))).mp hc
  have hresultPullback : σ.result.eval (w.pullback ρ η) = t := by
    have heq := Ty.eval_support σ.result ⟨ft, fe⟩
      (w.pullback ρ η)
      (fun i hi => hagreeT i (Finset.mem_union_left _ hi))
      (fun i hi => hagreeE i (Finset.mem_union_left _ hi))
    exact heq.symm.trans ht
  have hpreserveT : ∀ i ∈ fixedTypes, w.types i = v.types i := by
    intro i hi
    apply assignImage_not_mem
    intro himg
    have hm : i ∈ (σ.typeVars.image ρ) ∩ fixedTypes :=
      Finset.mem_inter.mpr ⟨himg, hi⟩
    rw [hdisjT] at hm
    simp at hm
  have hpreserveE : ∀ i ∈ fixedEffects, w.effects i = v.effects i := by
    intro i hi
    apply assignImage_not_mem
    intro himg
    have hm : i ∈ (σ.effectVars.image η) ∩ fixedEffects :=
      Finset.mem_inter.mpr ⟨himg, hi⟩
    rw [hdisjE] at hm
    simp at hm
  refine ⟨w, hfixedT, hfixedE, hpreserveT, hpreserveE, ?_, ?_⟩
  · exact (Constraint.holds_rename_safe hRename hSupport
      σ.predicates ρ η w
      (σ.renameSafe_predicates ρ η hadm hsafe)).mpr hpredPullback
  · simpa [Scheme.instantiate, Ty.eval_rename] using hresultPullback

theorem Scheme.groundInstance_realizable {X : Domain}
    (hRename : LawfulRename X) (hSupport : LawfulSupport X)
    (σ : Scheme X) (ρ η : Nat → Nat)
    (hadm : σ.AdmissibleRename ρ η)
    (hsafe : σ.SafeRename ρ η)
    (v : Valuation) (t : GroundTy)
    (hinst : σ.GroundInstance v t) :
    ∃ w : Valuation,
      (∀ i ∈ σ.fvTypes, w.types i = v.types i) ∧
      (∀ i ∈ σ.fvEffects, w.effects i = v.effects i) ∧
      (σ.instantiate ρ η).2.holds w ∧
      (σ.instantiate ρ η).1.eval w = t := by
  rcases σ.groundInstance_realizable_fixed hRename hSupport ρ η
      hadm hsafe ∅ ∅ (by simp) (by simp) v t hinst with
    ⟨w, ht, he, _, _, hp, hr⟩
  exact ⟨w, ht, he, hp, hr⟩

/-- Variable case of semantic completeness under HM(X)'s pointwise context
instance order. `fixedTypes` and `fixedEffects` are names allocated before
this occurrence; the fresh instantiation leaves their values intact. -/
theorem Context.variable_complete_at {X : Domain}
    (hRename : LawfulRename X) (hSupport : LawfulSupport X)
    {Γg Γd : Context X} {σg σd : Scheme X} {i : Nat}
    (hg : Γg[i]? = some σg) (hd : Γd[i]? = some σd)
    (ρd ηd ρg ηg : Nat → Nat)
    (hadmD : σd.AdmissibleRename ρd ηd)
    (hsafeD : σd.SafeRename ρd ηd)
    (hadmG : σg.AdmissibleRename ρg ηg)
    (hsafeG : σg.SafeRename ρg ηg)
    (fixedTypes fixedEffects : Finset Nat)
    (hdisjT : (σg.typeVars.image ρg) ∩ fixedTypes = ∅)
    (hdisjE : (σg.effectVars.image ηg) ∩ fixedEffects = ∅)
    (vg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd)
    (hp : (σd.instantiate ρd ηd).2.holds vd) :
    ∃ w : Valuation,
      (∀ j ∈ fixedTypes, w.types j = vg.types j) ∧
      (∀ j ∈ fixedEffects, w.effects j = vg.effects j) ∧
      (σg.instantiate ρg ηg).2.holds w ∧
      (σg.instantiate ρg ηg).1.eval w =
        (σd.instantiate ρd ηd).1.eval vd := by
  have hdinst : σd.GroundInstance vd
      ((σd.instantiate ρd ηd).1.eval vd) :=
    σd.instantiate_groundInstance hRename hSupport ρd ηd
      hadmD hsafeD vd hp
  have hginst := (Context.moreGeneralAt_lookup hctx hg hd)
    _ hdinst
  rcases σg.groundInstance_realizable_fixed hRename hSupport ρg ηg
      hadmG hsafeG fixedTypes fixedEffects hdisjT hdisjE vg _ hginst with
    ⟨w, _, _, hfixedT, hfixedE, hpred, hresult⟩
  exact ⟨w, hfixedT, hfixedE, hpred, hresult⟩

private theorem foldl_union_mono {α : Type} (l : List α)
    (f : α → Finset Nat) {a b : Finset Nat} (hab : a ⊆ b) :
    l.foldl (fun names x => names ∪ f x) a ⊆
    l.foldl (fun names x => names ∪ f x) b := by
  intro i hi
  rcases (foldl_union_mem f l a i).mp hi with ha | ⟨x, hx, hf⟩
  · exact (foldl_union_mem f l b i).mpr (Or.inl (hab ha))
  · exact (foldl_union_mem f l b i).mpr
      (Or.inr ⟨x, hx, hf⟩)

private theorem mem_foldl_union_of_mem {α : Type} (l : List α)
    (f : α → Finset Nat) (a : Finset Nat) (x : α) (i : Nat)
    (hx : x ∈ l) (hi : i ∈ f x) :
    i ∈ l.foldl (fun names y => names ∪ f y) a := by
  exact (foldl_union_mem f l a i).mpr (Or.inr ⟨x, hx, hi⟩)

theorem Context.fvTypes_of_mem {X : Domain} (Γ : Context X)
    (σ : Scheme X) (hσ : σ ∈ Γ) (i : Nat)
    (hi : i ∈ σ.fvTypes) : i ∈ Γ.fvTypes :=
  mem_foldl_union_of_mem Γ Scheme.fvTypes ∅ σ i hσ hi

theorem Context.fvEffects_of_mem {X : Domain} (Γ : Context X)
    (σ : Scheme X) (hσ : σ ∈ Γ) (i : Nat)
    (hi : i ∈ σ.fvEffects) : i ∈ Γ.fvEffects :=
  mem_foldl_union_of_mem Γ Scheme.fvEffects ∅ σ i hσ hi

theorem Context.fvTypes_subset_cons {X : Domain}
    (σ : Scheme X) (Γ : Context X) :
    Γ.fvTypes ⊆ Context.fvTypes (σ :: Γ) := by
  simpa [Context.fvTypes] using
    (foldl_union_mono Γ Scheme.fvTypes (Finset.empty_subset _))

theorem Context.fvEffects_subset_cons {X : Domain}
    (σ : Scheme X) (Γ : Context X) :
    Γ.fvEffects ⊆ Context.fvEffects (σ :: Γ) := by
  simpa [Context.fvEffects] using
    (foldl_union_mono Γ Scheme.fvEffects (Finset.empty_subset _))

theorem BoundedInputs.context_fvTypes_below
    {sig : Signature} {X : Domain}
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (hb : BoundedInputs sig X Γ ops s) :
    ∀ i ∈ Γ.fvTypes, i < s.types := by
  intro i hi
  rcases (foldl_union_mem Scheme.fvTypes Γ ∅ i).mp hi with
    hnil | ⟨σ, hσ, hfv⟩
  · simp at hnil
  · exact hb.contextTypes σ hσ i
      (σ.fvTypes_subset_usedTypes hfv)

theorem BoundedInputs.context_fvEffects_below
    {sig : Signature} {X : Domain}
    {Γ : Context X} {ops : Finset Op} {s : Supply}
    (hb : BoundedInputs sig X Γ ops s) :
    ∀ i ∈ Γ.fvEffects, i < s.effects := by
  intro i hi
  rcases (foldl_union_mem Scheme.fvEffects Γ ∅ i).mp hi with
    hnil | ⟨σ, hσ, hfv⟩
  · simp at hnil
  · exact hb.contextEffects σ hσ i
      (σ.fvEffects_subset_usedEffects hfv)

/-- The public seed is above every name appearing in a looked-up scheme. -/
theorem Supply.seed_above_lookup {X : Domain}
    (s : Supply) (sig : Signature) (Γ : Context X) (e : Expr)
    (A : List X.Pred) (i : Nat) (σ : Scheme X)
    (hlookup : Γ[i]? = some σ) :
    (∀ j ∈ σ.usedTypes, j < (s.seed sig Γ e A).types) ∧
    (∀ j ∈ σ.usedEffects, j < (s.seed sig Γ e A).effects) := by
  have hmem : σ ∈ Γ := List.mem_of_getElem? hlookup
  have hs := s.seed_above_inputs sig Γ e A
  constructor
  · intro j hj
    apply hs.1 j
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (mem_foldl_union_of_mem Γ Scheme.usedTypes ∅ σ j hmem hj))
  · intro j hj
    apply hs.2 j
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (mem_foldl_union_of_mem Γ Scheme.usedEffects ∅ σ j hmem hj))

theorem Supply.seed_lookup_safe {X : Domain}
    (s : Supply) (sig : Signature) (Γ : Context X) (e : Expr)
    (A : List X.Pred) (i : Nat) (σ : Scheme X)
    (hlookup : Γ[i]? = some σ) :
    σ.SafeRename
      (renameBound σ.typeVars (s.seed sig Γ e A).types)
      (renameBound σ.effectVars (s.seed sig Γ e A).effects) := by
  have hb := s.seed_above_lookup sig Γ e A i σ hlookup
  apply σ.renameBound_safe
  · intro j hj
    have hused : j ∈ σ.usedTypes := by
      simp [Scheme.usedTypes, Scheme.fvTypes] at hj ⊢
      aesop
    exact Nat.le_of_lt (hb.1 j hused)
  · intro j hj
    have hused : j ∈ σ.usedEffects := by
      simp [Scheme.usedEffects, Scheme.fvEffects] at hj ⊢
      aesop
    exact Nat.le_of_lt (hb.2 j hused)

/-- A variable lookup cannot fail the freshness check after the public seed. -/
theorem generateFresh_var_success {X : Domain}
    (sig : Signature) (Γ : Context X) (s : Supply)
    (i : Nat) (σ : Scheme X) (hlookup : Γ[i]? = some σ) :
    ∃ r : Output X,
      generateFresh sig X Γ (.var i) s = some r := by
  let seed := s.seed sig Γ (.var i) []
  let ρ := renameBound σ.typeVars seed.types
  let η := renameBound σ.effectVars seed.effects
  have hsafe : σ.SafeRename ρ η :=
    s.seed_lookup_safe sig Γ (.var i) [] i σ hlookup
  refine ⟨⟨(σ.instantiate ρ η).1, ∅,
    (σ.instantiate ρ η).2, seed.advance σ.typeVars σ.effectVars⟩, ?_⟩
  simp [generateFresh, generate, seed, hlookup, ρ, η, hsafe]

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

theorem OpDecl.closed_usedTypes (raw : OpDecl)
    (hc : raw.Closed) : raw.usedTypes ⊆ raw.typeVars := by
  intro i hi
  simp only [OpDecl.usedTypes, Finset.mem_union] at hi
  rcases hi with (hi | hi) | hi
  · exact hi
  · exact hc.1 (Finset.mem_union_left _ hi)
  · exact hc.1 (Finset.mem_union_right _ hi)

theorem OpDecl.closed_alphaRename (raw : OpDecl)
    (hc : raw.Closed) (ρ η : Nat → Nat) :
    (raw.alphaRename ρ η).Closed := by
  rcases hc with ⟨ht, he⟩
  constructor
  · simpa [OpDecl.Closed, OpDecl.alphaRename,
      Ty.fvTypes_rename, Finset.image_union] using
      (Finset.image_subset_image ht)
  · simpa [OpDecl.Closed, OpDecl.alphaRename,
      Ty.fvEffects_rename, Finset.image_union] using
      (Finset.image_subset_image he)

theorem OpDecl.closed_usedEffects (raw : OpDecl)
    (hc : raw.Closed) : raw.usedEffects ⊆ raw.effectVars := by
  intro i hi
  simp only [OpDecl.usedEffects, Finset.mem_union] at hi
  rcases hi with (hi | hi) | hi
  · exact hi
  · exact hc.2 (Finset.mem_union_left _ hi)
  · exact hc.2 (Finset.mem_union_right _ hi)

theorem OpDecl.closed_alphaRename_used_ge
    (raw : OpDecl) (hc : raw.Closed) (s : Supply) :
    let ρ := renameBound raw.typeVars s.types
    let η := renameBound raw.effectVars s.effects
    let decl := raw.alphaRename ρ η
    (∀ i ∈ decl.usedTypes, s.types < i) ∧
      (∀ i ∈ decl.usedEffects, s.effects < i) := by
  dsimp
  constructor
  · intro i hi
    have hsub : i ∈ raw.usedTypes.image
        (renameBound raw.typeVars s.types) := by
      simp [OpDecl.usedTypes, OpDecl.alphaRename,
        Ty.fvTypes_rename, Finset.image_union] at hi ⊢
      aesop
    rcases Finset.mem_image.mp hsub with ⟨j, hj, rfl⟩
    have hbound := raw.closed_usedTypes hc hj
    simp [renameBound, hbound]
    omega
  · intro i hi
    have hsub : i ∈ raw.usedEffects.image
        (renameBound raw.effectVars s.effects) := by
      simp [OpDecl.usedEffects, OpDecl.alphaRename,
        Ty.fvEffects_rename, Finset.image_union] at hi ⊢
      aesop
    rcases Finset.mem_image.mp hsub with ⟨j, hj, rfl⟩
    have hbound := raw.closed_usedEffects hc hj
    simp [renameBound, hbound]
    omega

/-- Two admissible instantiations of the same operation agree after fresh
binder assignment, provided valuations agree on the declaration's free names. -/
theorem OpDecl.rename_realizable
    (raw : OpDecl) (s : Supply)
    (ρd ηd : Nat → Nat)
    (hadmD : raw.AdmissibleRename ρd ηd)
    (vg vd : Valuation)
    (hbelowT : ∀ i ∈ raw.usedTypes, i < s.types)
    (hbelowE : ∀ i ∈ raw.usedEffects, i < s.effects)
    (hfreeT : ∀ i ∈ raw.usedTypes, i ∉ raw.typeVars →
      vg.types i = vd.types i)
    (hfreeE : ∀ i ∈ raw.usedEffects, i ∉ raw.effectVars →
      vg.effects i = vd.effects i) :
    let ρg := renameBound raw.typeVars s.types
    let ηg := renameBound raw.effectVars s.effects
    ∃ w : Valuation,
      (∀ i, i < s.types → vg.types i = w.types i) ∧
      (∀ i, i < s.effects → vg.effects i = w.effects i) ∧
      (raw.input.rename ρg ηg).eval w =
        (raw.input.rename ρd ηd).eval vd ∧
      (raw.output.rename ρg ηg).eval w =
        (raw.output.rename ρd ηd).eval vd := by
  dsimp
  let ρg := renameBound raw.typeVars s.types
  let ηg := renameBound raw.effectVars s.effects
  let w : Valuation :=
    ⟨assignImage raw.typeVars ρg (vd.types ∘ ρd) vg.types,
      assignImage raw.effectVars ηg (vd.effects ∘ ηd) vg.effects⟩
  have hdisjT := renameBound_image_disjoint_below
    raw.typeVars (Finset.range s.types) s.types
    (by intro j hj; exact Finset.mem_range.mp hj)
  have hdisjE := renameBound_image_disjoint_below
    raw.effectVars (Finset.range s.effects) s.effects
    (by intro j hj; exact Finset.mem_range.mp hj)
  have hfixedT : ∀ i, i < s.types →
      vg.types i = w.types i := by
    intro i hi
    have hnot : i ∉ raw.typeVars.image ρg := by
      intro hm
      have : i ∈ raw.typeVars.image ρg ∩ Finset.range s.types :=
        Finset.mem_inter.mpr ⟨hm, Finset.mem_range.mpr hi⟩
      simp [ρg, hdisjT] at this
    exact (assignImage_not_mem raw.typeVars ρg
      (vd.types ∘ ρd) vg.types i hnot).symm
  have hfixedE : ∀ i, i < s.effects →
      vg.effects i = w.effects i := by
    intro i hi
    have hnot : i ∉ raw.effectVars.image ηg := by
      intro hm
      have : i ∈ raw.effectVars.image ηg ∩ Finset.range s.effects :=
        Finset.mem_inter.mpr ⟨hm, Finset.mem_range.mpr hi⟩
      simp [ηg, hdisjE] at this
    exact (assignImage_not_mem raw.effectVars ηg
      (vd.effects ∘ ηd) vg.effects i hnot).symm
  have hagreeT : ∀ i ∈ raw.usedTypes,
      w.types (ρg i) = vd.types (ρd i) := by
    intro i hi
    by_cases hb : i ∈ raw.typeVars
    · exact assignImage_mem raw.typeVars ρg
        (renameBound_injOn raw.typeVars s.types)
        (vd.types ∘ ρd) vg.types i hb
    · have hfixG : ρg i = i :=
        renameBound_fixed raw.typeVars s.types i hb
      have hfixD : ρd i = i := hadmD.1 i hb
      change (assignImage raw.typeVars ρg
        (vd.types ∘ ρd) vg.types) (ρg i) = vd.types (ρd i)
      rw [hfixG, hfixD]
      exact (hfixedT i (hbelowT i hi)).symm.trans
        (hfreeT i hi hb)
  have hagreeE : ∀ i ∈ raw.usedEffects,
      w.effects (ηg i) = vd.effects (ηd i) := by
    intro i hi
    by_cases hb : i ∈ raw.effectVars
    · exact assignImage_mem raw.effectVars ηg
        (renameBound_injOn raw.effectVars s.effects)
        (vd.effects ∘ ηd) vg.effects i hb
    · have hfixG : ηg i = i :=
        renameBound_fixed raw.effectVars s.effects i hb
      have hfixD : ηd i = i := hadmD.2 i hb
      change (assignImage raw.effectVars ηg
        (vd.effects ∘ ηd) vg.effects) (ηg i) = vd.effects (ηd i)
      rw [hfixG, hfixD]
      exact (hfixedE i (hbelowE i hi)).symm.trans
        (hfreeE i hi hb)
  refine ⟨w, hfixedT, hfixedE, ?_, ?_⟩
  · rw [Ty.eval_rename, Ty.eval_rename]
    exact Ty.eval_support raw.input
      (w.pullback ρg ηg) (vd.pullback ρd ηd)
      (fun i hi => hagreeT i (by simp [OpDecl.usedTypes, hi]))
      (fun i hi => hagreeE i (by simp [OpDecl.usedEffects, hi]))
  · rw [Ty.eval_rename, Ty.eval_rename]
    exact Ty.eval_support raw.output
      (w.pullback ρg ηg) (vd.pullback ρd ηd)
      (fun i hi => hagreeT i (by simp [OpDecl.usedTypes, hi]))
      (fun i hi => hagreeE i (by simp [OpDecl.usedEffects, hi]))


theorem OpDecl.renamed_eval_frame
    (raw : OpDecl) (s : Supply) (v w : Valuation)
    (hbelowT : ∀ i ∈ raw.usedTypes, i < s.types)
    (hbelowE : ∀ i ∈ raw.usedEffects, i < s.effects)
    (ht : ∀ i, i < (s.advance raw.typeVars raw.effectVars).types →
      v.types i = w.types i)
    (he : ∀ i, i < (s.advance raw.typeVars raw.effectVars).effects →
      v.effects i = w.effects i) :
    let ρ := renameBound raw.typeVars s.types
    let η := renameBound raw.effectVars s.effects
    (raw.input.rename ρ η).eval v =
      (raw.input.rename ρ η).eval w ∧
    (raw.output.rename ρ η).eval v =
      (raw.output.rename ρ η).eval w := by
  dsimp
  have hty (τ : Ty)
      (hτ : τ.fvTypes ⊆ raw.usedTypes) :
      ∀ i ∈ (τ.rename
        (renameBound raw.typeVars s.types)
        (renameBound raw.effectVars s.effects)).fvTypes,
        v.types i = w.types i := by
    intro i hi
    rw [Ty.fvTypes_rename] at hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact ht _ (s.renameBound_types_below_advance
      raw.typeVars raw.effectVars raw.usedTypes hbelowT j (hτ hj))
  have heff (τ : Ty)
      (hτ : τ.fvEffects ⊆ raw.usedEffects) :
      ∀ i ∈ (τ.rename
        (renameBound raw.typeVars s.types)
        (renameBound raw.effectVars s.effects)).fvEffects,
        v.effects i = w.effects i := by
    intro i hi
    rw [Ty.fvEffects_rename] at hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact he _ (s.renameBound_effects_below_advance
      raw.typeVars raw.effectVars raw.usedEffects hbelowE j (hτ hj))
  constructor
  · exact Ty.eval_support _ v w
      (hty raw.input (by
        intro i hi
        simp [OpDecl.usedTypes, hi]))
      (heff raw.input (by
        intro i hi
        simp [OpDecl.usedEffects, hi]))
  · exact Ty.eval_support _ v w
      (hty raw.output (by
        intro i hi
        simp [OpDecl.usedTypes, hi]))
      (heff raw.output (by
        intro i hi
        simp [OpDecl.usedEffects, hi]))


/-- Executable variable-case completeness: a declarative ground use can be
reproduced by `generateFresh` while preserving every name already used by
the input context. -/
theorem generateFresh_var_ground_complete {X : Domain}
    (hRename : LawfulRename X) (hSupport : LawfulSupport X)
    (sig : Signature) (Γ : Context X) (s : Supply)
    (i : Nat) (σ : Scheme X) (hlookup : Γ[i]? = some σ)
    (C : Constraint X) (ρd ηd : Nat → Nat)
    (hadmD : σ.AdmissibleRename ρd ηd)
    (hsafeD : σ.SafeRename ρd ηd)
    (hent : C.Entails (σ.instantiate ρd ηd).2)
    (v : Valuation) (hC : C.holds v) :
    ∃ r : Output X, ∃ w : Valuation,
      generateFresh sig X Γ (.var i) s = some r ∧
      (∀ j ∈ Γ.foldl (fun names σ => names ∪ σ.usedTypes) ∅,
        w.types j = v.types j) ∧
      (∀ j ∈ Γ.foldl (fun names σ => names ∪ σ.usedEffects) ∅,
        w.effects j = v.effects j) ∧
      r.constraints.holds w ∧
      r.ty.eval w = (σ.instantiate ρd ηd).1.eval v := by
  let seed := s.seed sig Γ (.var i) []
  let ρg := renameBound σ.typeVars seed.types
  let ηg := renameBound σ.effectVars seed.effects
  let Tctx := Γ.foldl (fun names σ => names ∪ σ.usedTypes) ∅
  let Ectx := Γ.foldl (fun names σ => names ∪ σ.usedEffects) ∅
  have hsafeG : σ.SafeRename ρg ηg :=
    s.seed_lookup_safe sig Γ (.var i) [] i σ hlookup
  have hseed := s.seed_above_inputs sig Γ (.var i) []
  have hbelowT : ∀ j ∈ Tctx, j < seed.types := by
    intro j hj
    exact hseed.1 j (Finset.mem_union_left _ (Finset.mem_union_left _ hj))
  have hbelowE : ∀ j ∈ Ectx, j < seed.effects := by
    intro j hj
    exact hseed.2 j (Finset.mem_union_left _ (Finset.mem_union_left _ hj))
  have hdisjT := renameBound_image_disjoint_below σ.typeVars
    Tctx seed.types hbelowT
  have hdisjE := renameBound_image_disjoint_below σ.effectVars
    Ectx seed.effects hbelowE
  rcases Context.variable_complete_at hRename hSupport hlookup hlookup
      ρd ηd ρg ηg hadmD hsafeD
      ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩ hsafeG
      Tctx Ectx hdisjT hdisjE v v
      (Context.moreGeneralAt_refl Γ v) (hent v hC) with
    ⟨w, ht, he, hp, hr⟩
  let r : Output X :=
    ⟨(σ.instantiate ρg ηg).1, ∅,
      (σ.instantiate ρg ηg).2,
      seed.advance σ.typeVars σ.effectVars⟩
  have hrun : generateFresh sig X Γ (.var i) s = some r := by
    simp [generateFresh, generate, r, seed, hlookup, ρg, ηg, hsafeG]
  exact ⟨r, w, hrun, ht, he, hp, hr⟩

/-- The executable variable result uses only names below its returned supply.
This is the variable branch of the frame invariant needed by applications,
monomorphic lets, and handlers. -/
theorem generateFresh_var_support_below {X : Domain}
    (hX : LawfulFVRename X)
    (sig : Signature) (Γ : Context X) (s : Supply)
    (i : Nat) (σ : Scheme X) (hlookup : Γ[i]? = some σ) :
    ∃ r : Output X,
      generateFresh sig X Γ (.var i) s = some r ∧
      (∀ j ∈ r.supportTypes, j < r.next.types) ∧
      (∀ j ∈ r.supportEffects, j < r.next.effects) := by
  let seed := s.seed sig Γ (.var i) []
  let ρ := renameBound σ.typeVars seed.types
  let η := renameBound σ.effectVars seed.effects
  let r : Output X := ⟨(σ.instantiate ρ η).1, ∅,
    (σ.instantiate ρ η).2,
    seed.advance σ.typeVars σ.effectVars⟩
  have hsafe : σ.SafeRename ρ η :=
    s.seed_lookup_safe sig Γ (.var i) [] i σ hlookup
  have hrun : generateFresh sig X Γ (.var i) s = some r := by
    simp [generateFresh, generate, r, seed, hlookup, ρ, η, hsafe]
  have hb := s.seed_above_lookup sig Γ (.var i) [] i σ hlookup
  refine ⟨r, hrun, ?_, ?_⟩
  · intro j hj
    have hsub : r.supportTypes ⊆ σ.usedTypes.image ρ := by
      simpa [r, Output.supportTypes] using
        σ.instantiate_supportTypes_subset hX ρ η
    rcases Finset.mem_image.mp (hsub hj) with ⟨k, hk, rfl⟩
    exact seed.renameBound_types_below_advance
      σ.typeVars σ.effectVars σ.usedTypes hb.1 k hk
  · intro j hj
    have hsub : r.supportEffects ⊆ σ.usedEffects.image η := by
      simpa [r, Output.supportEffects] using
        σ.instantiate_supportEffects_subset hX ρ η
    rcases Finset.mem_image.mp (hsub hj) with ⟨k, hk, rfl⟩
    exact seed.renameBound_effects_below_advance
      σ.typeVars σ.effectVars σ.usedEffects hb.2 k hk

/-- HM(X) generalization leaves exactly the obligation that the bound value
has at least one admissible ground instance. -/
theorem Scheme.generalize_instance_iff_residual {X : Domain}
    (Γ : Context X) (c : Constraint X) (τ : Ty) (ρ : Valuation) :
    (∃ t, (Scheme.generalize Γ c τ).GroundInstance ρ t) ↔
      (Scheme.residual Γ c τ).holds ρ := by
  rw [Scheme.residual_holds_iff]
  constructor
  · rintro ⟨t, ft, fe, hft, hfe, hc, _⟩
    exact ⟨ft, fe, hft, hfe, hc⟩
  · rintro ⟨ft, fe, hft, hfe, hc⟩
    exact ⟨τ.eval ⟨ft, fe⟩, ft, fe, hft, hfe, hc, rfl⟩

/-- The fragment whose declarative rules do not change a binding scheme. -/
def Expr.Core : Expr → Prop
  | .var _ | .int _ | .bool _ => True
  | .lam e => e.Core
  | .app f x => f.Core ∧ x.Core
  | .perform _ e => e.Core
  | .letE _ _ | .handle _ _ _ _ => False

/-- A generated result covers one declarative judgement while preserving all
names that were already allocated when generation began. -/
def Output.CoversAt {X : Domain} (Γg Γd : Context X)
    (C : Constraint X) (s : Supply) (r : Output X)
    (τ : Ty) (ε : Effect) : Prop :=
  ∀ vg vd, Γg.MoreGeneralAt Γd vg vd → C.holds vd →
    ∃ wg : Valuation,
      (∀ i, i < s.types → vg.types i = wg.types i) ∧
      (∀ i, i < s.effects → vg.effects i = wg.effects i) ∧
      r.constraints.holds wg ∧
      r.ty.eval wg = τ.eval vd ∧
      r.effect.eval wg.effects = ε.eval vd.effects

/-- One declarative clause instance yields the projected generated clause
constraint, with all clause-local assignments confined to its allocated range. -/
theorem Output.CoversAt.project_clause {X : Domain}
    (hX : LawfulSupport X)
    (Γg Γd : Context X) (D : Constraint X)
    (s : Supply) (r : Output X) (τ a : Ty) (ε χ : Effect)
    (hboundT : ∀ i ∈ r.supportTypes, i < r.next.types)
    (hboundE : ∀ i ∈ r.supportEffects, i < r.next.effects)
    (haT : ∀ i ∈ a.fvTypes, i < s.types)
    (haE : ∀ i ∈ a.fvEffects, i < s.effects)
    (hχ : ∀ i ∈ χ.vars, i < s.effects)
    (hcov : Output.CoversAt Γg Γd D s r τ ε)
    (vg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd)
    (hD : D.holds vd)
    (htarget : τ.eval vd = a.eval vg)
    (heffect : ε.eval vd.effects ⊆ χ.eval vg.effects) :
    (Constraint.project
      (Finset.range r.next.types \ Finset.range s.types)
      (Finset.range r.next.effects \ Finset.range s.effects)
      (.and r.constraints
        (.and (.typeEq r.ty a) (.effectLe r.effect χ)))).holds vg := by
  rcases hcov vg vd hctx hD with
    ⟨w, hbelowT, hbelowE, hC, hTy, hEff⟩
  rcases r.localize_solution hX s vg w
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
  apply (Constraint.project_holds_iff _ _ _ vg).mpr
  refine ⟨v.types, v.effects, hlocalT, hlocalE, ?_⟩
  exact ⟨hCv,
    hTyV.trans (hTy.trans (htarget.trans ha.symm)),
    by
      change r.effect.eval v.effects ⊆ χ.eval v.effects
      rw [hEffV, hEff, hχV]
      exact heffect⟩

/-- The application step combines two sequential witnesses and assigns the
fresh result type and latent effect. -/
theorem Output.CoversAt.app {sig : Signature} {X : Domain}
    (hSupport : LawfulSupport X)
    (Γg Γd : Context X) (C : Constraint X)
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
    (hf : Output.CoversAt Γg Γd C s rf (.arr a η b) εf)
    (hx : Output.CoversAt Γg Γd C rf.next rx a εx) :
    Output.CoversAt Γg Γd C s
      ⟨.var rx.next.types,
        rf.effect ∪ rx.effect ∪ Poly.Effect.var rx.next.effects,
        .and (.and rf.constraints rx.constraints)
          (.typeEq rf.ty
            (.arr rx.ty (Poly.Effect.var rx.next.effects)
              (.var rx.next.types))),
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩
      b (εf ∪ εx ∪ η) := by
  intro vg vd hctx hC
  rcases hf vg vd hctx hC with
    ⟨w₁, h₁T, h₁E, hCf, hTf, hEf⟩
  have hctx₁ := Context.moreGeneralAt_below hSupport
    Γg Γd ops s hb vg w₁ vd hctx h₁T h₁E
  rcases hx w₁ vd hctx₁ hC with
    ⟨w₂, h₂T, h₂E, hCx, hTx, hEx⟩
  have hsolution := Output.app_solution_extend hSupport rf rx
    hfBound hxBound hnext w₁ w₂ h₂T h₂E hCf hCx
    (a.eval vd) (b.eval vd) (η.eval vd.effects)
    (by simpa [Ty.eval] using hTf) hTx
  let w₃ := w₂.assignAt rx.next (b.eval vd) (η.eval vd.effects)
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

/-- Lambda allocates one parameter name; the body may assign later
names while the parameter keeps its declared ground type. -/
theorem Output.CoversAt.lam {sig : Signature} {X : Domain}
    (hSupport : LawfulSupport X)
    (Γg Γd : Context X) (C : Constraint X)
    (ops : Finset Op) (s : Supply)
    (rb : Output X) (a b : Ty) (ε : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (hbody : Output.CoversAt
      (Scheme.mono (.var s.types) :: Γg)
      (Scheme.mono a :: Γd) C
      {s with types := s.types + 1} rb b ε) :
    Output.CoversAt Γg Γd C s
      ⟨.arr (.var s.types) rb.effect rb.ty, ∅,
        rb.constraints, rb.next⟩
      (.arr a ε b) ∅ := by
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
  have hctx' := Context.moreGeneralAt_below hSupport
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

/-- A monomorphic let retains the first solution while checking its body. -/
theorem Output.CoversAt.letMono {sig : Signature} {X : Domain}
    (hSupport : LawfulSupport X)
    (Γg Γd : Context X) (C : Constraint X)
    (ops : Finset Op) (s : Supply)
    (r₁ r₂ : Output X) (τ₁ τ₂ : Ty) (ε₁ ε₂ : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (h₁Bound : (∀ i ∈ r₁.supportTypes, i < r₁.next.types) ∧
      (∀ i ∈ r₁.supportEffects, i < r₁.next.effects))
    (hstart : s.types ≤ r₁.next.types ∧
      s.effects ≤ r₁.next.effects)
    (hfirst : Output.CoversAt Γg Γd C s r₁ τ₁ ε₁)
    (hbody : Output.CoversAt
      (Scheme.mono r₁.ty :: Γg)
      (Scheme.mono τ₁ :: Γd) C r₁.next r₂ τ₂ ε₂) :
    Output.CoversAt Γg Γd C s
      ⟨r₂.ty, r₁.effect ∪ r₂.effect,
        .and r₁.constraints r₂.constraints, r₂.next⟩
      τ₂ (ε₁ ∪ ε₂) := by
  intro vg vd hctx hC
  rcases hfirst vg vd hctx hC with
    ⟨w₁, h₁T, h₁E, hC₁, hTy₁, hEff₁⟩
  have hctx₁ := Context.moreGeneralAt_below hSupport
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
  have hframe := r₁.semantic_frame_of_below hSupport w₁ w₂
    h₁Bound.1 h₁Bound.2 h₂T h₂E
  refine ⟨w₂, ?_, ?_, ⟨hframe.1.mp hC₁, hC₂⟩, hTy₂, ?_⟩
  · intro i hi
    exact (h₁T i hi).trans (h₂T i (lt_of_lt_of_le hi hstart.1))
  · intro i hi
    exact (h₁E i hi).trans (h₂E i (lt_of_lt_of_le hi hstart.2))
  · simp [Effect.eval_union, ← hframe.2.2, hEff₁, hEff₂]


/-- Completeness step for a performed operation at valuations that agree
on the operation signature's unquantified names. -/
theorem Output.perform_solution_at {sig : Signature} {X : Domain}
    (hSupport : LawfulSupport X)
    (Γg Γd : Context X) (C : Constraint X)
    (ops : Finset Op) (s : Supply)
    (op : Op) (raw : OpDecl) (ρd ηd : Nat → Nat)
    (re : Output X) (ε : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (hop : op ∈ ops) (hd : sig op = some raw)
    (hadmD : raw.AdmissibleRename ρd ηd)
    (hbody : Output.CoversAt Γg Γd C
      (s.advance raw.typeVars raw.effectVars)
      re (raw.input.rename ρd ηd) ε)
    (vg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd)
    (hC : C.holds vd)
    (hfreeT : ∀ i ∈ raw.usedTypes, i ∉ raw.typeVars →
      vg.types i = vd.types i)
    (hfreeE : ∀ i ∈ raw.usedEffects, i ∉ raw.effectVars →
      vg.effects i = vd.effects i) :
    let ρg := renameBound raw.typeVars s.types
    let ηg := renameBound raw.effectVars s.effects
    let out : Output X :=
      ⟨raw.output.rename ρg ηg,
        Poly.Effect.singleton op ∪ re.effect,
        .and re.constraints
          (.typeEq re.ty (raw.input.rename ρg ηg)),
        re.next⟩
    ∃ w : Valuation,
      (∀ i, i < s.types → vg.types i = w.types i) ∧
      (∀ i, i < s.effects → vg.effects i = w.effects i) ∧
      out.constraints.holds w ∧
      out.ty.eval w = (raw.output.rename ρd ηd).eval vd ∧
      out.effect.eval w.effects =
        (Poly.Effect.singleton op ∪ ε).eval vd.effects := by
  dsimp
  have hraw := hb.signature op hop raw hd
  rcases raw.rename_realizable s ρd ηd hadmD vg vd
      hraw.1 hraw.2 hfreeT hfreeE with
    ⟨v', hfixedT, hfixedE, hInput, hOutput⟩
  have hctx' := Context.moreGeneralAt_below hSupport
    Γg Γd ops s hb vg v' vd hctx hfixedT hfixedE
  rcases hbody v' vd hctx' hC with
    ⟨w, hwt, hwe, hCg, hTy, hEff⟩
  have hframe := raw.renamed_eval_frame s v' w
    hraw.1 hraw.2 hwt hwe
  refine ⟨w, ?_, ?_, ⟨hCg, ?_⟩, ?_, ?_⟩
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
  · change re.ty.eval w =
      (raw.input.rename
        (renameBound raw.typeVars s.types)
        (renameBound raw.effectVars s.effects)).eval w
    exact hTy.trans (hInput.symm.trans hframe.1)
  · exact hframe.2.symm.trans hOutput
  · rw [Effect.eval_union, Effect.eval_union]
    have hopW : (Poly.Effect.singleton op).eval w.effects = {op} := by
      simp [Poly.Effect.eval, Poly.Effect.singleton]
    have hopD : (Poly.Effect.singleton op).eval vd.effects = {op} := by
      simp [Poly.Effect.eval, Poly.Effect.singleton]
    rw [hopW, hopD, hEff]


/-- Closed operation schemes make the perform step independent of
unquantified signature names. -/
theorem Output.CoversAt.perform {sig : Signature} {X : Domain}
    (hSupport : LawfulSupport X)
    (Γg Γd : Context X) (C : Constraint X)
    (ops : Finset Op) (s : Supply)
    (op : Op) (raw : OpDecl) (ρd ηd : Nat → Nat)
    (re : Output X) (ε : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (hop : op ∈ ops) (hd : sig op = some raw)
    (hc : raw.Closed)
    (hadmD : raw.AdmissibleRename ρd ηd)
    (hbody : Output.CoversAt Γg Γd C
      (s.advance raw.typeVars raw.effectVars)
      re (raw.input.rename ρd ηd) ε) :
    let ρg := renameBound raw.typeVars s.types
    let ηg := renameBound raw.effectVars s.effects
    Output.CoversAt Γg Γd C s
      ⟨raw.output.rename ρg ηg,
        Poly.Effect.singleton op ∪ re.effect,
        .and re.constraints
          (.typeEq re.ty (raw.input.rename ρg ηg)),
        re.next⟩
      (raw.output.rename ρd ηd)
      (Poly.Effect.singleton op ∪ ε) := by
  dsimp
  intro vg vd hctx hC
  exact Output.perform_solution_at hSupport
    Γg Γd C ops s op raw ρd ηd re ε
    hb hop hd hadmD hbody vg vd hctx hC
    (by
      intro i hi hnot
      exact False.elim (hnot (raw.closed_usedTypes hc hi)))
    (by
      intro i hi hnot
      exact False.elim (hnot (raw.closed_usedEffects hc hi)))

theorem Output.CoversAt.conv {X : Domain}
    (Γg Γd : Context X) (C : Constraint X)
    (s : Supply) (r : Output X) (τ τ' : Ty) (ε : Effect)
    (h : Output.CoversAt Γg Γd C s r τ ε)
    (hEq : C.Entails (.typeEq τ τ')) :
    Output.CoversAt Γg Γd C s r τ' ε := by
  intro vg vd hctx hC
  rcases h vg vd hctx hC with
    ⟨w, ht, he, hCg, hTy, hEff⟩
  exact ⟨w, ht, he, hCg,
    hTy.trans (hEq vd hC), hEff⟩

theorem Output.CoversAt.weaken {X : Domain}
    (Γg Γd : Context X) (C D : Constraint X)
    (s : Supply) (r : Output X) (τ : Ty) (ε : Effect)
    (h : Output.CoversAt Γg Γd C s r τ ε)
    (hEnt : D.Entails C) :
    Output.CoversAt Γg Γd D s r τ ε := by
  intro vg vd hctx hD
  exact h vg vd hctx (hEnt vd hD)


/-- At a fixed valuation, the generated constraint and result include a
declarative result. This is the semantic instance relation for monotypes. -/
def GeneratedCovers {X : Domain} (C Cg : Constraint X)
    (τg τ : Ty) (εg ε : Effect) : Prop :=
  ∀ ρ, C.holds ρ → Cg.holds ρ ∧
    τg.eval ρ = τ.eval ρ ∧ εg.eval ρ.effects = ε.eval ρ.effects

/-- The semantic completeness relation when the generated and declared
contexts differ under a let. The generated valuation may assign fresh names,
but it preserves the generated context's free names. -/
def GeneratedCoversAcross {X : Domain}
    (Γg Γd : Context X) (C Cg : Constraint X)
    (τg τ : Ty) (εg ε : Effect) : Prop :=
  ∀ vg vd, Γg.MoreGeneralAt Γd vg vd → C.holds vd →
    ∃ wg : Valuation,
      (∀ i ∈ Γg.fvTypes, wg.types i = vg.types i) ∧
      (∀ i ∈ Γg.fvEffects, wg.effects i = vg.effects i) ∧
      Cg.holds wg ∧ τg.eval wg = τ.eval vd ∧
      εg.eval wg.effects = ε.eval vd.effects

theorem Output.CoversAt.toAcross {sig : Signature} {X : Domain}
    (Γg Γd : Context X) (C : Constraint X)
    (ops : Finset Op) (s : Supply) (r : Output X)
    (τ : Ty) (ε : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (h : Output.CoversAt Γg Γd C s r τ ε) :
    GeneratedCoversAcross Γg Γd C r.constraints
      r.ty τ r.effect ε := by
  intro vg vd hctx hC
  rcases h vg vd hctx hC with
    ⟨wg, ht, he, hCg, hTy, hEff⟩
  have hctxBelow := hb.contextFVBelow
  exact ⟨wg,
    (fun i hi => (ht i (hctxBelow.1 i hi)).symm),
    (fun i hi => (he i (hctxBelow.2 i hi)).symm),
    hCg, hTy, hEff⟩


/-- The executable variable branch is complete at any supply above the
generated context, including when the declarative context has a less general
scheme at the same index. -/
theorem generate_var_coversAt {sig : Signature} {X : Domain}
    (hRename : LawfulRename X) (hSupport : LawfulSupport X)
    (Γg Γd : Context X) (C : Constraint X)
    (ops : Finset Op) (s : Supply) (i : Nat)
    (σg σd : Scheme X) (ρd ηd : Nat → Nat)
    (hb : BoundedInputs sig X Γg ops s)
    (hg : Γg[i]? = some σg) (hd : Γd[i]? = some σd)
    (hadmD : σd.AdmissibleRename ρd ηd)
    (hsafeD : σd.SafeRename ρd ηd)
    (hent : C.Entails (σd.instantiate ρd ηd).2) :
    ∃ r : Output X,
      generate sig X Γg (.var i) s = some r ∧
      Output.CoversAt Γg Γd C s r
        (σd.instantiate ρd ηd).1 ∅ := by
  let ρg := renameBound σg.typeVars s.types
  let ηg := renameBound σg.effectVars s.effects
  let r : Output X :=
    ⟨(σg.instantiate ρg ηg).1, ∅,
      (σg.instantiate ρg ηg).2,
      s.advance σg.typeVars σg.effectVars⟩
  have hmem : σg ∈ Γg := List.mem_of_getElem? hg
  have hbelowT := hb.contextTypes σg hmem
  have hbelowE := hb.contextEffects σg hmem
  have hsafeG : σg.SafeRename ρg ηg := by
    apply σg.renameBound_safe s.types s.effects
    · intro j hj
      have hu : j ∈ σg.usedTypes := by
        simp [Scheme.usedTypes, Scheme.fvTypes] at hj ⊢
        aesop
      exact Nat.le_of_lt (hbelowT j hu)
    · intro j hj
      have hu : j ∈ σg.usedEffects := by
        simp [Scheme.usedEffects, Scheme.fvEffects] at hj ⊢
        aesop
      exact Nat.le_of_lt (hbelowE j hu)
  have hrun : generate sig X Γg (.var i) s = some r := by
    simp [generate, r, hg, ρg, ηg, hsafeG]
  refine ⟨r, hrun, ?_⟩
  intro vg vd hctx hC
  have hdisjT := renameBound_image_disjoint_below
    σg.typeVars (Finset.range s.types) s.types
    (by intro j hj; exact Finset.mem_range.mp hj)
  have hdisjE := renameBound_image_disjoint_below
    σg.effectVars (Finset.range s.effects) s.effects
    (by intro j hj; exact Finset.mem_range.mp hj)
  rcases Context.variable_complete_at hRename hSupport hg hd
      ρd ηd ρg ηg hadmD hsafeD
      ⟨renameBound_fixed _ _, renameBound_fixed _ _⟩ hsafeG
      (Finset.range s.types) (Finset.range s.effects)
      hdisjT hdisjE vg vd hctx (hent vd hC) with
    ⟨w, ht, he, hp, hty⟩
  refine ⟨w, ?_, ?_, hp, hty, rfl⟩
  · intro j hj
    exact (ht j (Finset.mem_range.mpr hj)).symm
  · intro j hj
    exact (he j (Finset.mem_range.mpr hj)).symm


/-- A solution which preserves the context's free names gives a ground
instance of the generalized value scheme. -/
theorem Scheme.generalize_groundInstance_of_solution {X : Domain}
    (hX : LawfulSupport X) (Γ : Context X)
    (C : Constraint X) (τ : Ty)
    (v w : Valuation) (t : GroundTy)
    (hct : ∀ i ∈ Γ.fvTypes, w.types i = v.types i)
    (hce : ∀ i ∈ Γ.fvEffects, w.effects i = v.effects i)
    (hC : C.holds w) (ht : τ.eval w = t) :
    (Scheme.generalize Γ C τ).GroundInstance v t := by
  let σ := Scheme.generalize Γ C τ
  let wt : Nat → GroundTy := fun i =>
    if i ∈ σ.typeVars then w.types i else v.types i
  let we : Nat → Finset Op := fun i =>
    if i ∈ σ.effectVars then w.effects i else v.effects i
  have hty : ∀ i ∈ τ.fvTypes ∪ C.fvTypes, w.types i = wt i := by
    intro i hi
    by_cases hb : i ∈ σ.typeVars
    · simp [wt, hb]
    · have hΓ : i ∈ Γ.fvTypes := by
        by_contra hn
        exact hb (by simp [σ, Scheme.generalize, hi, hn])
      simp [wt, hb, hct i hΓ]
  have heff : ∀ i ∈ τ.fvEffects ∪ C.fvEffects,
      w.effects i = we i := by
    intro i hi
    by_cases hb : i ∈ σ.effectVars
    · simp [we, hb]
    · have hΓ : i ∈ Γ.fvEffects := by
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
  · exact (Constraint.holds_support hX C w ⟨wt, we⟩
      (fun i hi => hty i (Finset.mem_union_right _ hi))
      (fun i hi => heff i (Finset.mem_union_right _ hi))).mp hC
  · exact (Ty.eval_support τ w ⟨wt, we⟩
      (fun i hi => hty i (Finset.mem_union_left _ hi))
      (fun i hi => heff i (Finset.mem_union_left _ hi))).symm ▸ ht

/-- A clause's generated body preserves its result equality and effect
inclusion under the rigid-then-local quantifier order. -/
theorem Constraint.closed_clause_mono {X : Domain}
    (boundTypes boundEffects localTypes localEffects : Finset Nat)
    (D Co : Constraint X) (τo τog a : Ty) (εo εog χ : Effect)
    (hcov : GeneratedCovers D Co τog τo εog εo) :
    (Constraint.close boundTypes boundEffects
      (Constraint.project localTypes localEffects
        (.and D (.and (.typeEq τo a) (.effectLe εo χ))))).Entails
    (Constraint.close boundTypes boundEffects
      (Constraint.project localTypes localEffects
        (.and Co (.and (.typeEq τog a) (.effectLe εog χ))))) := by
  apply Constraint.close_mono boundTypes boundEffects
  apply Constraint.project_mono localTypes localEffects
  intro ρ h
  rcases h with ⟨hD, hτ, hε⟩
  rcases hcov ρ hD with ⟨hCo, hτg, hεg⟩
  exact ⟨hCo, hτg.trans hτ, by simpa [Constraint.holds, hεg] using hε⟩

/-- Generalization preserves the pointwise instance order when the generated
constraint covers the declared value. This is the `let` step used by HM(X). -/
theorem Scheme.generalize_moreGeneralAt {X : Domain}
    (hX : LawfulSupport X) (Γ : Context X)
    (C₁ Cg : Constraint X) (τ₁ τg : Ty) (ε₁ εg : Effect)
    (hcov : GeneratedCovers C₁ Cg τg τ₁ εg ε₁)
    (ρ : Valuation) :
    (Scheme.generalize Γ Cg τg).MoreGeneralAt
      (Scheme.generalize Γ C₁ τ₁) ρ ρ := by
  intro t hinst
  rcases hinst with ⟨ft, fe, hft, hfe, hC₁, ht⟩
  let σg := Scheme.generalize Γ Cg τg
  let σ₁ := Scheme.generalize Γ C₁ τ₁
  let vg : Valuation := ⟨ft, fe⟩
  let wg : Valuation :=
    ⟨fun i => if i ∈ σg.typeVars then ft i else ρ.types i,
      fun i => if i ∈ σg.effectVars then fe i else ρ.effects i⟩
  have htyAgree : ∀ i ∈ τg.fvTypes ∪ Cg.fvTypes,
      vg.types i = wg.types i := by
    intro i hi
    by_cases hgen : i ∈ σg.typeVars
    · simp [vg, wg, hgen]
    · have hΓ : i ∈ Γ.fvTypes := by
        by_contra hn
        have : i ∈ σg.typeVars := by
          simp [σg, Scheme.generalize, hi, hn]
        exact hgen this
      have hdecl : i ∉ σ₁.typeVars := by
        simp [σ₁, Scheme.generalize, hΓ]
      simpa [vg, wg, hgen] using hft i hdecl
  have heffAgree : ∀ i ∈ τg.fvEffects ∪ Cg.fvEffects,
      vg.effects i = wg.effects i := by
    intro i hi
    by_cases hgen : i ∈ σg.effectVars
    · simp [vg, wg, hgen]
    · have hΓ : i ∈ Γ.fvEffects := by
        by_contra hn
        have : i ∈ σg.effectVars := by
          simp [σg, Scheme.generalize, hi, hn]
        exact hgen this
      have hdecl : i ∉ σ₁.effectVars := by
        simp [σ₁, Scheme.generalize, hΓ]
      simpa [vg, wg, hgen] using hfe i hdecl
  rcases hcov vg hC₁ with ⟨hCg, htype, _⟩
  have hCg' : Cg.holds wg :=
    (Constraint.holds_support hX Cg vg wg
      (fun i hi => htyAgree i (Finset.mem_union_right _ hi))
      (fun i hi => heffAgree i (Finset.mem_union_right _ hi))).mp hCg
  have htype' : τg.eval wg = τ₁.eval vg := by
    rw [← Ty.eval_support τg vg wg
      (fun i hi => htyAgree i (Finset.mem_union_left _ hi))
      (fun i hi => heffAgree i (Finset.mem_union_left _ hi))]
    exact htype
  refine ⟨wg.types, wg.effects, ?_, ?_, hCg', ?_⟩
  · intro i hi
    change i ∉ σg.typeVars at hi
    simp [wg, hi]
  · intro i hi
    change i ∉ σg.effectVars at hi
    simp [wg, hi]
  · exact htype'.trans ht

/-- The HM(X) let step when the generated and declarative contexts already
have different schemes. The only assumption about X is finite support. -/
theorem Scheme.generalize_moreGeneralAt_across {X : Domain}
    (hX : LawfulSupport X)
    (Γg Γd : Context X) (C₁ Cg : Constraint X)
    (τ₁ τg : Ty) (ε₁ εg : Effect)
    (hcov : GeneratedCoversAcross Γg Γd C₁ Cg τg τ₁ εg ε₁)
    (vg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd) :
    (Scheme.generalize Γg Cg τg).MoreGeneralAt
      (Scheme.generalize Γd C₁ τ₁) vg vd := by
  intro t hinst
  rcases hinst with ⟨ft, fe, hft, hfe, hC₁, ht⟩
  let vd' : Valuation := ⟨ft, fe⟩
  have hctx' : Γg.MoreGeneralAt Γd vg vd' := by
    apply Context.moreGeneralAt_support hX Γg Γd vg vg vd vd' hctx
    · intro σ _ i _; rfl
    · intro σ _ i _; rfl
    · intro σ hσ i hi
      have hΓ := Context.fvTypes_of_mem Γd σ hσ i hi
      have hnot : i ∉ (Scheme.generalize Γd C₁ τ₁).typeVars := by
        simp [Scheme.generalize, hΓ]
      exact (hft i hnot).symm
    · intro σ hσ i hi
      have hΓ := Context.fvEffects_of_mem Γd σ hσ i hi
      have hnot : i ∉ (Scheme.generalize Γd C₁ τ₁).effectVars := by
        simp [Scheme.generalize, hΓ]
      exact (hfe i hnot).symm
  rcases hcov vg vd' hctx' hC₁ with
    ⟨wg, hgt, hge, hCg, hty, _⟩
  exact Scheme.generalize_groundInstance_of_solution hX Γg Cg τg
    vg wg t hgt hge hCg (hty.trans ht)

/-- The residual obligation for a value let is preserved across related
contexts, using the same solution as the generalized scheme order. -/
theorem Scheme.residual_across {X : Domain}
    (hX : LawfulSupport X)
    (Γg Γd : Context X) (C₁ Cg : Constraint X)
    (τ₁ τg : Ty) (ε₁ εg : Effect)
    (hcov : GeneratedCoversAcross Γg Γd C₁ Cg τg τ₁ εg ε₁)
    (vg vd : Valuation)
    (hctx : Γg.MoreGeneralAt Γd vg vd)
    (hres : (Scheme.residual Γd C₁ τ₁).holds vd) :
    (Scheme.residual Γg Cg τg).holds vg := by
  rcases (Scheme.generalize_instance_iff_residual Γd C₁ τ₁ vd).mpr
    hres with ⟨t, hinst⟩
  apply (Scheme.generalize_instance_iff_residual Γg Cg τg vg).mp
  exact ⟨t, (Scheme.generalize_moreGeneralAt_across hX Γg Γd C₁ Cg
    τ₁ τg ε₁ εg hcov vg vd hctx) t hinst⟩

/-- Value let composes under two different generalized schemes. The first
premise supplies the scheme inclusion; the body preserves its residual. -/
theorem Output.CoversAt.letVal {sig : Signature} {X : Domain}
    (hSupport : LawfulSupport X)
    (Γg Γd : Context X) (C₁ C₂ : Constraint X)
    (ops : Finset Op) (s : Supply)
    (r₁ r₂ : Output X) (τ₁ τ₂ : Ty) (ε₂ : Effect)
    (hb : BoundedInputs sig X Γg ops s)
    (h₁Bound : (∀ i ∈ r₁.supportTypes, i < r₁.next.types) ∧
      (∀ i ∈ r₁.supportEffects, i < r₁.next.effects))
    (hstart : s.types ≤ r₁.next.types ∧
      s.effects ≤ r₁.next.effects)
    (hfirst : Output.CoversAt Γg Γd C₁ s r₁ τ₁ ∅)
    (hbody : Output.CoversAt
      (Scheme.generalize Γg r₁.constraints r₁.ty :: Γg)
      (Scheme.generalize Γd C₁ τ₁ :: Γd)
      C₂ r₁.next r₂ τ₂ ε₂) :
    Output.CoversAt Γg Γd
      (.and (Scheme.residual Γd C₁ τ₁) C₂) s
      ⟨r₂.ty, r₂.effect,
        .and (Scheme.residual Γg r₁.constraints r₁.ty)
          r₂.constraints, r₂.next⟩
      τ₂ ε₂ := by
  intro vg vd hctx hC
  rcases hC with ⟨hresD, hC₂⟩
  have hfirstAcross := hfirst.toAcross Γg Γd C₁ ops s r₁
    τ₁ ∅ hb
  have hgen := Scheme.generalize_moreGeneralAt_across hSupport
    Γg Γd C₁ r₁.constraints τ₁ r₁.ty ∅ r₁.effect
    hfirstAcross vg vd hctx
  have hresG := Scheme.residual_across hSupport
    Γg Γd C₁ r₁.constraints τ₁ r₁.ty ∅ r₁.effect
    hfirstAcross vg vd hctx hresD
  have hctxBody : Context.MoreGeneralAt
      (Scheme.generalize Γg r₁.constraints r₁.ty :: Γg)
      (Scheme.generalize Γd C₁ τ₁ :: Γd) vg vd :=
    List.Forall₂.cons hgen hctx
  rcases hbody vg vd hctxBody hC₂ with
    ⟨w₂, h₂T, h₂E, hC₂g, hTy₂, hEff₂⟩
  have hresW := r₁.letVal_residual_frame hSupport Γg
    h₁Bound.1 h₁Bound.2 vg w₂ hresG h₂T h₂E
  exact ⟨w₂,
    (fun i hi => h₂T i (lt_of_lt_of_le hi hstart.1)),
    (fun i hi => h₂E i (lt_of_lt_of_le hi hstart.2)),
    ⟨hresW, hC₂g⟩, hTy₂, hEff₂⟩


/-- Semantic composition of the generated value-let rule. The first premise
establishes both the generalized scheme order and its residual obligation;
the body premise then runs under the extended related contexts. -/
theorem GeneratedCoversAcross.letVal {X : Domain}
    (hX : LawfulSupport X)
    (Γg Γd : Context X)
    (C₁ Cg C₂ C₂g : Constraint X)
    (τ₁ τg τ₂ τ₂g : Ty)
    (ε₁ εg ε₂ ε₂g : Effect)
    (hfirst : GeneratedCoversAcross Γg Γd C₁ Cg τg τ₁ εg ε₁)
    (hbody : GeneratedCoversAcross
      (Scheme.generalize Γg Cg τg :: Γg)
      (Scheme.generalize Γd C₁ τ₁ :: Γd)
      C₂ C₂g τ₂g τ₂ ε₂g ε₂) :
    GeneratedCoversAcross Γg Γd
      (.and (Scheme.residual Γd C₁ τ₁) C₂)
      (.and (Scheme.residual Γg Cg τg) C₂g)
      τ₂g τ₂ ε₂g ε₂ := by
  intro vg vd hctx hC
  rcases hC with ⟨hresD, hC₂⟩
  have hgen := Scheme.generalize_moreGeneralAt_across hX Γg Γd
    C₁ Cg τ₁ τg ε₁ εg hfirst vg vd hctx
  have hresG := Scheme.residual_across hX Γg Γd
    C₁ Cg τ₁ τg ε₁ εg hfirst vg vd hctx hresD
  have hctxBody : Context.MoreGeneralAt
      (Scheme.generalize Γg Cg τg :: Γg)
      (Scheme.generalize Γd C₁ τ₁ :: Γd) vg vd :=
    List.Forall₂.cons hgen hctx
  rcases hbody vg vd hctxBody hC₂ with
    ⟨wg, hbt, hbe, hCg₂, hty, heff⟩
  have hct : ∀ i ∈ Γg.fvTypes, wg.types i = vg.types i := by
    intro i hi
    exact hbt i (Context.fvTypes_subset_cons _ Γg hi)
  have hce : ∀ i ∈ Γg.fvEffects, wg.effects i = vg.effects i := by
    intro i hi
    exact hbe i (Context.fvEffects_subset_cons _ Γg hi)
  have hresW : (Scheme.residual Γg Cg τg).holds wg := by
    have hs := Scheme.residual_fv_context Γg Cg τg
    exact (Constraint.holds_support hX
      (Scheme.residual Γg Cg τg) vg wg
      (fun i hi => (hct i (hs.1 hi)).symm)
      (fun i hi => (hce i (hs.2 hi)).symm)).mp hresG
  exact ⟨wg, hct, hce, ⟨hresW, hCg₂⟩, hty, heff⟩

/-- Reverse direction for the core rules. It does not cover `let` or handler;
those need an instance relation on schemes and quantified clause constraints. -/
theorem Typing.core_generate_complete {sig : Signature} {X : Domain}
    {C : Constraint X} {Γ : Context X} {e : Expr} {τ : Ty} {ε : Effect}
    (h : Typing sig X C Γ e τ ε) (hcore : e.Core) :
    ∃ τg εg Cg, Generate sig X Γ e τg εg Cg ∧
      GeneratedCovers C Cg τg τ εg ε := by
  induction h with
  | var hlookup hadm hsafe hent =>
      refine ⟨_, _, _, Generate.var hlookup hadm hsafe, ?_⟩
      intro ρ hC
      exact ⟨hent ρ hC, rfl, rfl⟩
  | int n =>
      refine ⟨_, _, _, Generate.int n, ?_⟩
      intro ρ _
      exact ⟨trivial, rfl, rfl⟩
  | bool b =>
      refine ⟨_, _, _, Generate.bool b, ?_⟩
      intro ρ _
      exact ⟨trivial, rfl, rfl⟩
  | lam _ ih =>
      rcases ih hcore with ⟨bg, ηg, Cg, hg, hcov⟩
      refine ⟨.arr _ ηg bg, ∅, Cg, Generate.lam hg, ?_⟩
      intro ρ hC
      rcases hcov ρ hC with ⟨hCg, hty, heff⟩
      exact ⟨hCg, by simp [Ty.eval, hty, heff], rfl⟩
  | app _ _ ihf ihx =>
      rename_i fExpr xExpr aTy bTy effF effX eta hproofF hproofX
      rcases hcore with ⟨hcf, hcx⟩
      rcases ihf hcf with ⟨τfg, εfg, Cfg, hgf, hcovf⟩
      rcases ihx hcx with ⟨τxg, εxg, Cxg, hgx, hcovx⟩
      refine ⟨bTy, εfg ∪ εxg ∪ eta,
        .and (.and Cfg Cxg) (.typeEq τfg (.arr τxg eta bTy)),
        Generate.app hgf hgx, ?_⟩
      intro ρ hC
      rcases hcovf ρ hC with ⟨hCf, htf, hef⟩
      rcases hcovx ρ hC with ⟨hCx, htx, hex⟩
      refine ⟨⟨⟨hCf, hCx⟩, ?_⟩, rfl, ?_⟩
      · simp [Constraint.holds, Ty.eval, htf, htx]
      · simp [Effect.eval_union, hef, hex]
  | perform hsig hadm _ ih =>
      rcases ih hcore with ⟨τg, εg, Cg, hg, hcov⟩
      refine ⟨_, _, _, Generate.perform hsig hadm hg, ?_⟩
      intro ρ hC
      rcases hcov ρ hC with ⟨hCg, hty, heff⟩
      refine ⟨⟨hCg, ?_⟩, rfl, ?_⟩
      · simpa [Constraint.holds] using hty
      · simp [Effect.eval_union, heff]
  | letVal => simp [Expr.Core] at hcore
  | letMono => simp [Expr.Core] at hcore
  | handle => simp [Expr.Core] at hcore
  | conv _ hconv ih =>
      rcases ih hcore with ⟨τg, εg, Cg, hg, hcov⟩
      refine ⟨τg, εg, Cg, hg, ?_⟩
      intro ρ hC
      rcases hcov ρ hC with ⟨hCg, hty, heff⟩
      exact ⟨hCg, hty.trans (hconv ρ hC), heff⟩
  | weaken _ hent ih =>
      rcases ih hcore with ⟨τg, εg, Cg, hg, hcov⟩
      refine ⟨τg, εg, Cg, hg, ?_⟩
      intro ρ hD
      exact hcov ρ (hent ρ hD)

/-- The immediate effect inferred for an expression uses only effect
variables allocated at or after the input supply. -/
theorem generate_effect_fresh {sig : Signature} {X : Domain}
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (h : generate sig X Γ e s = some r) :
    ∀ i ∈ r.effect.vars, s.effects ≤ i := by
  fun_induction generate sig X Γ e s generalizing r with
  | case1 Γ i s =>
      cases hσ : Γ[i]? with
      | none => simp [hσ] at h
      | some σ =>
          by_cases hs : σ.SafeRename
              (renameBound σ.typeVars s.types)
              (renameBound σ.effectVars s.effects)
          · simp [hσ, hs] at h
            cases h
            simp
          · simp [hσ, hs] at h
  | case2 Γ n s => cases h; simp
  | case3 Γ b s => cases h; simp
  | case4 Γ body s a ih =>
      cases hr : generate sig X (Scheme.mono a :: Γ) body
          {s with types := s.types + 1} with
      | none => simp [hr] at h
      | some rb =>
          simp [hr] at h
          cases h
          simp
  | case5 Γ f x s ihf ihx =>
      cases hf : generate sig X Γ f s with
      | none => simp [hf] at h
      | some rf =>
          cases hx : generate sig X Γ x rf.next with
          | none => simp [hf, hx] at h
          | some rx =>
              simp [hf, hx] at h
              cases h
              intro i hi
              simp only [Poly.Effect.vars_union, Poly.Effect.var,
                Finset.mem_union, Finset.mem_singleton] at hi
              rcases hi with (hfi | hxi) | hη
              · exact ihf hf i hfi
              · exact (generate_next_mono hf).2.trans
                  (ihx rf hx i hxi)
              · subst i
                exact (generate_next_mono hf).2.trans
                  (generate_next_mono hx).2
  | case6 Γ e₁ e₂ s ihBound ihVal ihMono =>
      cases h₁ : generate sig X Γ e₁ s with
      | none => simp [h₁] at h
      | some r₁ =>
          cases hv : e₁.isValue with
          | true =>
              cases h₂ : generate sig X
                  (Scheme.generalize Γ r₁.constraints r₁.ty :: Γ)
                  e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  intro i hi
                  exact (generate_next_mono h₁).2.trans
                    (ihVal r₁ h₂ i hi)
          | false =>
              cases h₂ : generate sig X
                  (Scheme.mono r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at h
              | some r₂ =>
                  simp [h₁, hv, h₂] at h
                  cases h
                  intro i hi
                  simp [Poly.Effect.vars_union] at hi
                  rcases hi with hfirst | hsecond
                  · exact ihBound h₁ i hfirst
                  · exact (generate_next_mono h₁).2.trans
                      (ihMono r₁ h₂ i hsecond)
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
              intro i hi
              simp [Poly.Effect.vars_union] at hi
              exact (Nat.le_of_lt
                (s.advance_mono decl.typeVars decl.effectVars).2).trans
                (ih decl he i hi)
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
                        Scheme.mono decl.input :: Γ) clause rr.next with
                  | none =>
                      simp [hd, hb, hr, hc, ρ, η, decl, sb, a, χ, sr] at h
                  | some rc =>
                      let localTypes :=
                        Finset.range rc.next.types \ Finset.range rr.next.types
                      let localEffects :=
                        Finset.range rc.next.effects \ Finset.range rr.next.effects
                      let C := Constraint.handler op decl
                        rb.constraints rr.constraints rc.constraints
                        rr.ty rc.ty a rb.effect rr.effect rc.effect
                        δ χ localTypes localEffects
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hs : decl.HandlerScope Γ rb.ty a
                            rb.effect rr.effect δ χ
                        · by_cases hcs : decl.ClauseScope Γ C rb.ty a
                              rb.effect rr.effect δ χ
                              localTypes localEffects
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at h
                            cases h
                            intro i hi
                            simp [Poly.Effect.var] at hi
                            subst i
                            have hm := generate_next_mono hb
                            have ha := rb.next.advance_mono
                              raw.typeVars raw.effectVars
                            omega
                          · simp [hd, hb, hr, hc, hsafe, hs,
                              ρ, η, decl, sb, a, δ, χ, sr] at h
                            exact False.elim (hcs h.1)
                        · simp [hd, hb, hr, hc, hsafe, hs,
                            ρ, η, decl, sb, a, δ, χ, sr] at h
                      · simp [hd, hb, hr, hsafe, ρ, η, sb, sr] at h

/-- Fresh operation binders satisfy the handler's outer scope check.
The return effect cannot mention them because immediate effects use only
names allocated after the return call's input supply. -/
theorem generated_handlerScope
    {sig : Signature} {X : Domain}
    (Γ : Context X) (ops : Finset Op) (s : Supply)
    (raw : OpDecl) (rb rr : Output X)
    (hb : BoundedInputs sig X Γ ops s)
    (hmono : s.types ≤ rb.next.types ∧
      s.effects ≤ rb.next.effects)
    (hboundT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hboundE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hretFresh : ∀ i ∈ rr.effect.vars,
      (rb.next.advance raw.typeVars raw.effectVars).effects + 2 ≤ i) :
    let ρ := renameBound raw.typeVars rb.next.types
    let η := renameBound raw.effectVars rb.next.effects
    let decl := raw.alphaRename ρ η
    let sb := rb.next.advance raw.typeVars raw.effectVars
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    decl.HandlerScope Γ rb.ty a rb.effect rr.effect δ χ := by
  dsimp
  constructor
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro i hi hother
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    have hlow : rb.next.types <
        renameBound raw.typeVars rb.next.types j := by
      simp [renameBound, hj]
      omega
    have hup : renameBound raw.typeVars rb.next.types j <
        (rb.next.advance raw.typeVars raw.effectVars).types :=
      (rb.next.advance_above_renamed raw.typeVars raw.effectVars).1 j hj
    simp only [Finset.mem_union, Ty.fvTypes] at hother
    rcases hother with (hΓ | hτ) | ha
    · exact (not_lt_of_ge (hmono.1.trans
        (Nat.le_of_lt hlow)))
        (hb.context_fvTypes_below _ hΓ)
    · have ht := hboundT _ (Finset.mem_union_left _ hτ)
      omega
    · simp at ha
      omega
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro i hi hother
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    have hlow : rb.next.effects <
        renameBound raw.effectVars rb.next.effects j := by
      simp [renameBound, hj]
      omega
    have hup : renameBound raw.effectVars rb.next.effects j <
        (rb.next.advance raw.typeVars raw.effectVars).effects :=
      (rb.next.advance_above_renamed raw.typeVars raw.effectVars).2 j hj
    simp only [Finset.mem_union, Ty.fvEffects] at hother
    rcases hother with ((((((hΓ | hτ) | ha) | hεin) | hεr) | hδ) | hχ)
    · have ht := hb.context_fvEffects_below _ hΓ
      omega
    · have ht := hboundE _ (by
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ hτ))
      omega
    · simp at ha
    · have ht := hboundE _ (by
        exact Finset.mem_union_left _
          (Finset.mem_union_right _ hεin))
      omega
    · have ht := hretFresh _ hεr
      omega
    · simp [Poly.Effect.var] at hδ
      omega
    · simp [Poly.Effect.var] at hχ
      omega

theorem generated_handlerScope_of_runs
    {sig : Signature} {X : Domain}
    (Γ : Context X) (ops : Finset Op) (s : Supply)
    (raw : OpDecl) (body ret : Expr) (rb rr : Output X)
    (hb : BoundedInputs sig X Γ ops s)
    (hbody : generate sig X Γ body s = some rb)
    (hboundT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hboundE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hret : generate sig X (Scheme.mono rb.ty :: Γ) ret
      ⟨(rb.next.advance raw.typeVars raw.effectVars).types + 1,
        (rb.next.advance raw.typeVars raw.effectVars).effects + 2⟩ =
      some rr) :
    let ρ := renameBound raw.typeVars rb.next.types
    let η := renameBound raw.effectVars rb.next.effects
    let decl := raw.alphaRename ρ η
    let sb := rb.next.advance raw.typeVars raw.effectVars
    decl.HandlerScope Γ rb.ty (.var sb.types) rb.effect rr.effect
      (Poly.Effect.var sb.effects)
      (Poly.Effect.var (sb.effects + 1)) := by
  exact generated_handlerScope Γ ops s raw rb rr hb
    (generate_next_mono hbody) hboundT hboundE
    (generate_effect_fresh hret)


end SystemFXi.EHMX

set_option maxHeartbeats 1000000

namespace SystemFXi.EHMX

def Context.UsesType {X : Domain} (Γ : Context X) (i : Nat) : Prop :=
  ∃ σ ∈ Γ, i ∈ σ.usedTypes

def Context.UsesEffect {X : Domain} (Γ : Context X) (i : Nat) : Prop :=
  ∃ σ ∈ Γ, i ∈ σ.usedEffects

theorem generate_support_origin {sig : Signature} {X : Domain}
    (hX : LawfulFVRename X) (hClosed : sig.Closed)
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (hrun : generate sig X Γ e s = some r) :
    (∀ i ∈ r.supportTypes, i < s.types → Γ.UsesType i) ∧
      (∀ i ∈ r.supportEffects, i < s.effects → Γ.UsesEffect i) := by
  fun_induction generate sig X Γ e s generalizing r with
  | case1 Γ i s =>
      cases hσ : Γ[i]? with
      | none => simp [hσ] at hrun
      | some σ =>
          by_cases hs : σ.SafeRename
              (renameBound σ.typeVars s.types)
              (renameBound σ.effectVars s.effects)
          · simp [hσ, hs] at hrun
            cases hrun
            have hmem : σ ∈ Γ := List.mem_of_getElem? hσ
            constructor
            · intro j hj hsmall
              have hsub := Scheme.instantiate_supportTypes_subset hX σ
                (renameBound σ.typeVars s.types)
                (renameBound σ.effectVars s.effects)
              have hj' : j ∈ σ.usedTypes.image
                  (renameBound σ.typeVars s.types) :=
                hsub (by simpa [Output.supportTypes] using hj)
              rcases Finset.mem_image.mp hj' with ⟨k, hk, rfl⟩
              by_cases hkbound : k ∈ σ.typeVars
              · simp [renameBound, hkbound] at hsmall
                omega
              · rw [renameBound_fixed σ.typeVars s.types k hkbound]
                exact ⟨σ, hmem, hk⟩
            · intro j hj hsmall
              have hsub := Scheme.instantiate_supportEffects_subset hX σ
                (renameBound σ.typeVars s.types)
                (renameBound σ.effectVars s.effects)
              have hj' : j ∈ σ.usedEffects.image
                  (renameBound σ.effectVars s.effects) :=
                hsub (by simpa [Output.supportEffects] using hj)
              rcases Finset.mem_image.mp hj' with ⟨k, hk, rfl⟩
              by_cases hkbound : k ∈ σ.effectVars
              · simp [renameBound, hkbound] at hsmall
                omega
              · rw [renameBound_fixed σ.effectVars s.effects k hkbound]
                exact ⟨σ, hmem, hk⟩
          · simp [hσ, hs] at hrun
  | case2 Γ n s =>
      cases hrun
      constructor <;> intro i hi <;>
        simp [Output.supportTypes, Output.supportEffects,
          Constraint.usedTypes, Constraint.usedEffects,
          Constraint.fvTypes, Constraint.fvEffects,
          Constraint.boundTypes, Constraint.boundEffects,
          Ty.fvTypes, Ty.fvEffects] at hi
  | case3 Γ b s =>
      cases hrun
      constructor <;> intro i hi <;>
        simp [Output.supportTypes, Output.supportEffects,
          Constraint.usedTypes, Constraint.usedEffects,
          Constraint.fvTypes, Constraint.fvEffects,
          Constraint.boundTypes, Constraint.boundEffects,
          Ty.fvTypes, Ty.fvEffects] at hi
  | case4 Γ body s a ih =>
      cases hr : generate sig X (Scheme.mono a :: Γ) body
          {s with types := s.types + 1} with
      | none => simp [hr] at hrun
      | some rb =>
          simp [hr] at hrun
          cases hrun
          have hchild := ih hr
          constructor
          · intro i hi hlt
            have hsub : i = s.types ∨ i ∈ rb.supportTypes := by
              simp [a, Output.supportTypes, Constraint.usedTypes,
                Ty.fvTypes] at hi ⊢
              aesop
            rcases hsub with rfl | hmem
            · omega
            · have hc := hchild.1 i hmem (by dsimp; omega)
              rcases hc with ⟨σ, hσ, hu⟩
              rcases List.mem_cons.mp hσ with rfl | hrest
              · simp [a, Scheme.usedTypes, Scheme.mono,
                  Ty.fvTypes, Constraint.fvTypes,
                  Constraint.boundTypes] at hu
                omega
              · exact ⟨σ, hrest, hu⟩
          · intro i hi hlt
            have hsub : i ∈ rb.supportEffects := by
              simp [a, Output.supportEffects, Constraint.usedEffects,
                Ty.fvEffects] at hi ⊢
              aesop
            have hc := hchild.2 i hsub (by dsimp; omega)
            rcases hc with ⟨σ, hσ, hu⟩
            rcases List.mem_cons.mp hσ with rfl | hrest
            · simp [a, Scheme.usedEffects, Scheme.mono,
                Ty.fvEffects, Constraint.fvEffects,
                Constraint.boundEffects] at hu
            · exact ⟨σ, hrest, hu⟩
  | case5 Γ f x s ihf ihx =>
      cases hf : generate sig X Γ f s with
      | none => simp [hf] at hrun
      | some rf =>
          cases hx : generate sig X Γ x rf.next with
          | none => simp [hf, hx] at hrun
          | some rx =>
              simp [hf, hx] at hrun
              cases hrun
              have hmonoF := generate_next_mono hf
              have hmonoX := generate_next_mono hx
              have h₁ := ihf hf
              have h₂ := ihx rf hx
              constructor
              · intro i hi hlt
                have hsub : i = rx.next.types ∨
                    i ∈ rf.supportTypes ∨ i ∈ rx.supportTypes := by
                  simp [Output.supportTypes, Constraint.usedTypes,
                    Constraint.fvTypes, Constraint.boundTypes,
                    Ty.fvTypes] at hi ⊢
                  aesop
                rcases hsub with hnew | hfirst | hsecond
                · omega
                · exact h₁.1 i hfirst hlt
                · exact h₂.1 i hsecond (by omega)
              · intro i hi hlt
                have hsub : i = rx.next.effects ∨
                    i ∈ rf.supportEffects ∨ i ∈ rx.supportEffects := by
                  simp [Output.supportEffects, Constraint.usedEffects,
                    Constraint.fvEffects, Constraint.boundEffects,
                    Ty.fvEffects, Poly.Effect.var] at hi ⊢
                  aesop
                rcases hsub with hnew | hfirst | hsecond
                · omega
                · exact h₁.2 i hfirst hlt
                · exact h₂.2 i hsecond (by omega)
  | case6 Γ e₁ e₂ s ihBound ihVal ihMono =>
      cases h₁ : generate sig X Γ e₁ s with
      | none => simp [h₁] at hrun
      | some r₁ =>
          have hm := generate_next_mono h₁
          have hfirst := ihBound h₁
          cases hv : e₁.isValue with
          | true =>
              cases h₂ : generate sig X
                  (Scheme.generalize Γ r₁.constraints r₁.ty :: Γ)
                  e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at hrun
              | some r₂ =>
                  simp [h₁, hv, h₂] at hrun
                  cases hrun
                  have hsecond := ihVal r₁ h₂
                  constructor
                  · intro i hi hlt
                    have hsub : i ∈ r₁.supportTypes ∨
                        i ∈ r₂.supportTypes := by
                      have hres := Scheme.residual_supportTypes_subset
                        Γ r₁.constraints r₁.ty
                      simp only [Output.supportTypes,
                        Constraint.usedTypes_and, Finset.mem_union] at hi ⊢
                      rcases hi with hty | hrmem | hc
                      · exact Or.inr (Or.inl hty)
                      · exact Or.inl (Finset.mem_union.mp (hres hrmem))
                      · exact Or.inr (Or.inr hc)
                    rcases hsub with hleft | hright
                    · exact hfirst.1 i hleft hlt
                    · rcases hsecond.1 i hright (by omega) with
                        ⟨σ, hσ, hu⟩
                      rcases List.mem_cons.mp hσ with rfl | hrest
                      · have hg := Scheme.generalize_usedTypes_subset
                          Γ r₁.constraints r₁.ty hu
                        exact hfirst.1 i (by
                          simpa [Output.supportTypes] using hg) hlt
                      · exact ⟨σ, hrest, hu⟩
                  · intro i hi hlt
                    have hsub : i ∈ r₁.supportEffects ∨
                        i ∈ r₂.supportEffects := by
                      have hres := Scheme.residual_supportEffects_subset
                        Γ r₁.constraints r₁.ty
                      simp only [Output.supportEffects,
                        Constraint.usedEffects_and, Finset.mem_union] at hi ⊢
                      rcases hi with ((hty | heff) | (hrmem | hc))
                      · exact Or.inr (Or.inl (Or.inl hty))
                      · exact Or.inr (Or.inl (Or.inr heff))
                      · exact Or.inl (by
                          rcases Finset.mem_union.mp (hres hrmem) with
                            ht | hc
                          · exact Or.inl (Or.inl ht)
                          · exact Or.inr hc)
                      · exact Or.inr (Or.inr hc)
                    rcases hsub with hleft | hright
                    · exact hfirst.2 i hleft hlt
                    · rcases hsecond.2 i hright (by omega) with
                        ⟨σ, hσ, hu⟩
                      rcases List.mem_cons.mp hσ with rfl | hrest
                      · have hg := Scheme.generalize_usedEffects_subset
                          Γ r₁.constraints r₁.ty hu
                        exact hfirst.2 i (by
                          simp only [Output.supportEffects, Finset.mem_union]
                          rcases Finset.mem_union.mp hg with ht | hc
                          · exact Or.inl (Or.inl ht)
                          · exact Or.inr hc) hlt
                      · exact ⟨σ, hrest, hu⟩
          | false =>
              cases h₂ : generate sig X
                  (Scheme.mono r₁.ty :: Γ) e₂ r₁.next with
              | none => simp [h₁, hv, h₂] at hrun
              | some r₂ =>
                  simp [h₁, hv, h₂] at hrun
                  cases hrun
                  have hsecond := ihMono r₁ h₂
                  constructor
                  · intro i hi hlt
                    have hsub : i ∈ r₁.supportTypes ∨
                        i ∈ r₂.supportTypes := by
                      simp only [Output.supportTypes,
                        Constraint.usedTypes_and, Finset.mem_union] at hi ⊢
                      aesop
                    rcases hsub with hleft | hright
                    · exact hfirst.1 i hleft hlt
                    · rcases hsecond.1 i hright (by omega) with
                        ⟨σ, hσ, hu⟩
                      rcases List.mem_cons.mp hσ with rfl | hrest
                      · simp [Scheme.mono, Scheme.usedTypes,
                          Constraint.fvTypes, Constraint.boundTypes] at hu
                        exact hfirst.1 i (Finset.mem_union_left _ hu) hlt
                      · exact ⟨σ, hrest, hu⟩
                  · intro i hi hlt
                    have hsub : i ∈ r₁.supportEffects ∨
                        i ∈ r₂.supportEffects := by
                      simp only [Output.supportEffects,
                        Constraint.usedEffects_and,
                        Poly.Effect.vars_union, Finset.mem_union] at hi ⊢
                      aesop
                    rcases hsub with hleft | hright
                    · exact hfirst.2 i hleft hlt
                    · rcases hsecond.2 i hright (by omega) with
                        ⟨σ, hσ, hu⟩
                      rcases List.mem_cons.mp hσ with rfl | hrest
                      · simp [Scheme.mono, Scheme.usedEffects,
                          Constraint.fvEffects, Constraint.boundEffects] at hu
                        exact hfirst.2 i (by
                          simp [Output.supportEffects, hu]) hlt
                      · exact ⟨σ, hrest, hu⟩
  | case7 Γ op e s ih =>
      cases hd : sig op with
      | none => simp [hd] at hrun
      | some raw =>
          let sa := s.advance raw.typeVars raw.effectVars
          cases he : generate sig X Γ e sa with
          | none => simp [hd, he, sa] at hrun
          | some re =>
              simp [hd, he, sa] at hrun
              cases hrun
              have hchild := ih raw he
              have hcl := hClosed op raw hd
              have hmono := s.advance_mono raw.typeVars raw.effectVars
              have hsigT : ∀ i ∈ (raw.input.rename
                  (renameBound raw.typeVars s.types)
                  (renameBound raw.effectVars s.effects)).fvTypes ∪
                  (raw.output.rename
                  (renameBound raw.typeVars s.types)
                  (renameBound raw.effectVars s.effects)).fvTypes,
                  s.types < i := by
                intro i hi
                simp only [Ty.fvTypes_rename,
                  Finset.mem_union] at hi
                rcases hi with hin | hout
                · rcases Finset.mem_image.mp hin with ⟨j, hj, rfl⟩
                  have hbound := hcl.1
                    (Finset.mem_union_left _ hj)
                  simp [renameBound, hbound]
                  omega
                · rcases Finset.mem_image.mp hout with ⟨j, hj, rfl⟩
                  have hbound := hcl.1
                    (Finset.mem_union_right _ hj)
                  simp [renameBound, hbound]
                  omega
              have hsigE : ∀ i ∈ (raw.input.rename
                  (renameBound raw.typeVars s.types)
                  (renameBound raw.effectVars s.effects)).fvEffects ∪
                  (raw.output.rename
                  (renameBound raw.typeVars s.types)
                  (renameBound raw.effectVars s.effects)).fvEffects,
                  s.effects < i := by
                intro i hi
                simp only [Ty.fvEffects_rename,
                  Finset.mem_union] at hi
                rcases hi with hin | hout
                · rcases Finset.mem_image.mp hin with ⟨j, hj, rfl⟩
                  have hbound := hcl.2
                    (Finset.mem_union_left _ hj)
                  simp [renameBound, hbound]
                  omega
                · rcases Finset.mem_image.mp hout with ⟨j, hj, rfl⟩
                  have hbound := hcl.2
                    (Finset.mem_union_right _ hj)
                  simp [renameBound, hbound]
                  omega
              constructor
              · intro i hi hlt
                have hsub : i ∈ re.supportTypes ∨
                    i ∈ (raw.input.rename
                      (renameBound raw.typeVars s.types)
                      (renameBound raw.effectVars s.effects)).fvTypes ∪
                      (raw.output.rename
                      (renameBound raw.typeVars s.types)
                      (renameBound raw.effectVars s.effects)).fvTypes := by
                  simp [Output.supportTypes,
                    Constraint.usedTypes, Constraint.fvTypes,
                    Constraint.boundTypes] at hi ⊢
                  aesop
                rcases hsub with harg | hsig
                · exact hchild.1 i harg (by omega)
                · exact False.elim (by have := hsigT i hsig; omega)
              · intro i hi hlt
                have hsub : i ∈ re.supportEffects ∨
                    i ∈ (raw.input.rename
                      (renameBound raw.typeVars s.types)
                      (renameBound raw.effectVars s.effects)).fvEffects ∪
                      (raw.output.rename
                      (renameBound raw.typeVars s.types)
                      (renameBound raw.effectVars s.effects)).fvEffects := by
                  simp [Output.supportEffects,
                    Constraint.usedEffects, Constraint.fvEffects,
                    Constraint.boundEffects,
                    Poly.Effect.vars_union] at hi ⊢
                  aesop
                rcases hsub with harg | hsig
                · exact hchild.2 i harg (by omega)
                · exact False.elim (by have := hsigE i hsig; omega)
  | case8 Γ body op ret clause s ihBody ihRet ihClause =>
      cases hd : sig op with
      | none => simp [hd] at hrun
      | some raw =>
          cases hb : generate sig X Γ body s with
          | none => simp [hd, hb] at hrun
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
              | none => simp [hd, hb, hr, sb, sr] at hrun
              | some rr =>
                  cases hc : generate sig X
                      (Scheme.mono (.arr decl.output χ a) ::
                        Scheme.mono decl.input :: Γ) clause rr.next with
                  | none =>
                      simp [hd, hb, hr, hc, ρ, η, decl, sb, a, χ, sr] at hrun
                  | some rc =>
                      let localTypes :=
                        Finset.range rc.next.types \
                          Finset.range rr.next.types
                      let localEffects :=
                        Finset.range rc.next.effects \
                          Finset.range rr.next.effects
                      let C := Constraint.handler op decl
                        rb.constraints rr.constraints rc.constraints
                        rr.ty rc.ty a rb.effect rr.effect rc.effect
                        δ χ localTypes localEffects
                      have hmonoB := generate_next_mono hb
                      have hmonoR := generate_next_mono hr
                      have hmonoC := generate_next_mono hc
                      have hbody := ihBody hb
                      have hret := ihRet raw rb hr
                      have hclause := ihClause raw rb rr hc
                      have hsig := raw.closed_alphaRename_used_ge
                        (hClosed op raw hd) rb.next
                      have hgeT : s.types ≤ rb.next.types := hmonoB.1
                      have hgeE : s.effects ≤ rb.next.effects := hmonoB.2
                      have hnewT : s.types < sb.types := by
                        have h := rb.next.advance_mono
                          raw.typeVars raw.effectVars
                        dsimp [sb]
                        omega
                      have hnewE : s.effects < sb.effects := by
                        have h := rb.next.advance_mono
                          raw.typeVars raw.effectVars
                        dsimp [sb]
                        omega
                      change s.types <
                        (rb.next.advance raw.typeVars raw.effectVars).types
                          at hnewT
                      change s.effects <
                        (rb.next.advance raw.typeVars raw.effectVars).effects
                          at hnewE
                      change
                        (rb.next.advance raw.typeVars raw.effectVars).types + 1 ≤
                          rr.next.types ∧
                        (rb.next.advance raw.typeVars raw.effectVars).effects + 2 ≤
                          rr.next.effects at hmonoR
                      have hretT : ∀ i ∈ rr.supportTypes,
                          i < s.types → Γ.UsesType i := by
                        intro i hi hlt
                        rcases hret.1 i hi (by dsimp [sr]; omega) with
                          ⟨σ, hσ, hu⟩
                        rcases List.mem_cons.mp hσ with rfl | hrest
                        · simp [Scheme.usedTypes, Scheme.mono,
                            Constraint.fvTypes,
                            Constraint.boundTypes] at hu
                          exact hbody.1 i
                            (Finset.mem_union_left _ hu) hlt
                        · exact ⟨σ, hrest, hu⟩
                      have hretE : ∀ i ∈ rr.supportEffects,
                          i < s.effects → Γ.UsesEffect i := by
                        intro i hi hlt
                        rcases hret.2 i hi (by dsimp [sr]; omega) with
                          ⟨σ, hσ, hu⟩
                        rcases List.mem_cons.mp hσ with rfl | hrest
                        · simp [Scheme.usedEffects, Scheme.mono,
                            Constraint.fvEffects,
                            Constraint.boundEffects] at hu
                          exact hbody.2 i (by
                            simp [Output.supportEffects, hu]) hlt
                        · exact ⟨σ, hrest, hu⟩
                      have hclauseT : ∀ i ∈ rc.supportTypes,
                          i < s.types → Γ.UsesType i := by
                        intro i hi hlt
                        rcases hclause.1 i hi (by omega) with
                          ⟨σ, hσ, hu⟩
                        rcases List.mem_cons.mp hσ with hhead | hrest
                        · subst σ
                          simp [Scheme.usedTypes, Scheme.mono,
                            Ty.fvTypes, Constraint.fvTypes,
                            Constraint.boundTypes] at hu
                          rcases hu with ha | hout
                          · omega
                          · have hh : i ∈ decl.usedTypes := by
                              exact Finset.mem_union_right _ hout
                            have := hsig.1 i hh
                            omega
                        · rcases List.mem_cons.mp hrest with hhead | hΓ
                          · subst σ
                            simp [Scheme.usedTypes, Scheme.mono,
                              Constraint.fvTypes,
                              Constraint.boundTypes] at hu
                            have hh : i ∈ decl.usedTypes := by
                              exact Finset.mem_union_left _
                                (Finset.mem_union_right _ hu)
                            have := hsig.1 i hh
                            omega
                          · exact ⟨σ, hΓ, hu⟩
                      have hclauseE : ∀ i ∈ rc.supportEffects,
                          i < s.effects → Γ.UsesEffect i := by
                        intro i hi hlt
                        rcases hclause.2 i hi (by omega) with
                          ⟨σ, hσ, hu⟩
                        rcases List.mem_cons.mp hσ with hhead | hrest
                        · subst σ
                          simp [Scheme.usedEffects, Scheme.mono,
                            Ty.fvEffects, Constraint.fvEffects,
                            Constraint.boundEffects,
                            Poly.Effect.var] at hu
                          rcases hu with hχ | hout
                          · omega
                          · have hh : i ∈ decl.usedEffects := by
                              exact Finset.mem_union_right _ hout
                            have := hsig.2 i hh
                            omega
                        · rcases List.mem_cons.mp hrest with hhead | hΓ
                          · subst σ
                            simp [Scheme.usedEffects, Scheme.mono,
                              Constraint.fvEffects,
                              Constraint.boundEffects] at hu
                            have hh : i ∈ decl.usedEffects := by
                              exact Finset.mem_union_left _
                                (Finset.mem_union_right _ hu)
                            have := hsig.2 i hh
                            omega
                          · exact ⟨σ, hΓ, hu⟩
                      by_cases hsafe : raw.AlphaSafe ρ η
                      · by_cases hs : decl.HandlerScope Γ rb.ty a
                            rb.effect rr.effect δ χ
                        · by_cases hcs : decl.ClauseScope Γ C rb.ty a
                              rb.effect rr.effect δ χ
                              localTypes localEffects
                          · simp [hd, hb, hr, hc, hsafe, hs, hcs,
                              ρ, η, decl, sb, a, δ, χ, sr,
                              localTypes, localEffects, C] at hrun
                            cases hrun
                            constructor
                            · intro i hi hlt
                              have hCsup := Constraint.handler_usedTypes_subset
                                op decl rb.constraints rr.constraints
                                rc.constraints rr.ty rc.ty a rb.effect
                                rr.effect rc.effect δ χ
                                localTypes localEffects
                              have hrbC : i ∈ rb.constraints.usedTypes →
                                  Γ.UsesType i := by
                                intro h
                                exact hbody.1 i
                                  (Finset.mem_union_right _ h) hlt
                              have hrrC : i ∈ rr.constraints.usedTypes →
                                  Γ.UsesType i := by
                                intro h
                                exact hretT i
                                  (Finset.mem_union_right _ h) hlt
                              have hrcC : i ∈ rc.constraints.usedTypes →
                                  Γ.UsesType i := by
                                intro h
                                exact hclauseT i
                                  (Finset.mem_union_right _ h) hlt
                              have hrrTy : i ∈ rr.ty.fvTypes →
                                  Γ.UsesType i := by
                                intro h
                                exact hretT i
                                  (Finset.mem_union_left _ h) hlt
                              have hrcTy : i ∈ rc.ty.fvTypes →
                                  Γ.UsesType i := by
                                intro h
                                exact hclauseT i
                                  (Finset.mem_union_left _ h) hlt
                              have hdecl : i ∈ decl.typeVars →
                                  False := by
                                intro h
                                have hu : i ∈ decl.usedTypes := by
                                  exact Finset.mem_union_left _
                                    (Finset.mem_union_left _ h)
                                have := hsig.1 i hu
                                omega
                              have hlocal : i ∈ localTypes →
                                  False := by
                                intro h
                                have hn : rr.next.types ≤ i := by
                                  have hn := (Finset.mem_sdiff.mp h).2
                                  simpa using hn
                                omega
                              have ha : i ∈ a.fvTypes → False := by
                                simp [a, Ty.fvTypes, sb]
                                omega
                              simp only [Output.supportTypes,
                                Finset.mem_union] at hi
                              rcases hi with ha' | hC
                              · exact False.elim (ha ha')
                              · have hh := hCsup hC
                                simp only [Finset.mem_union] at hh
                                rcases hh with ((((((hCin | hCr) | hCo) |
                                  hτr) | hτo) | ha') | hdecl') | hlocal'
                                · exact hrbC hCin
                                · exact hrrC hCr
                                · exact hrcC hCo
                                · exact hrrTy hτr
                                · exact hrcTy hτo
                                · exact False.elim (ha ha')
                                · exact False.elim (hdecl hdecl')
                                · exact False.elim (hlocal hlocal')
                            · intro i hi hlt
                              have hCsup := Constraint.handler_usedEffects_subset
                                op decl rb.constraints rr.constraints
                                rc.constraints rr.ty rc.ty a rb.effect
                                rr.effect rc.effect δ χ
                                localTypes localEffects
                              have hrbC : i ∈ rb.constraints.usedEffects →
                                  Γ.UsesEffect i := by
                                intro h
                                exact hbody.2 i (by
                                  simp [Output.supportEffects, h]) hlt
                              have hrrC : i ∈ rr.constraints.usedEffects →
                                  Γ.UsesEffect i := by
                                intro h
                                exact hretE i (by
                                  simp [Output.supportEffects, h]) hlt
                              have hrcC : i ∈ rc.constraints.usedEffects →
                                  Γ.UsesEffect i := by
                                intro h
                                exact hclauseE i (by
                                  simp [Output.supportEffects, h]) hlt
                              have hrrTy : i ∈ rr.ty.fvEffects →
                                  Γ.UsesEffect i := by
                                intro h
                                exact hretE i (by
                                  simp [Output.supportEffects, h]) hlt
                              have hrcTy : i ∈ rc.ty.fvEffects →
                                  Γ.UsesEffect i := by
                                intro h
                                exact hclauseE i (by
                                  simp [Output.supportEffects, h]) hlt
                              have hrbEff : i ∈ rb.effect.vars →
                                  Γ.UsesEffect i := by
                                intro h
                                exact hbody.2 i (by
                                  simp [Output.supportEffects, h]) hlt
                              have hrrEff : i ∈ rr.effect.vars →
                                  Γ.UsesEffect i := by
                                intro h
                                exact hretE i (by
                                  simp [Output.supportEffects, h]) hlt
                              have hrcEff : i ∈ rc.effect.vars →
                                  Γ.UsesEffect i := by
                                intro h
                                exact hclauseE i (by
                                  simp [Output.supportEffects, h]) hlt
                              have hdecl : i ∈ decl.effectVars →
                                  False := by
                                intro h
                                have hu : i ∈ decl.usedEffects := by
                                  exact Finset.mem_union_left _
                                    (Finset.mem_union_left _ h)
                                have := hsig.2 i hu
                                omega
                              have hlocal : i ∈ localEffects →
                                  False := by
                                intro h
                                have hn : rr.next.effects ≤ i := by
                                  have hn := (Finset.mem_sdiff.mp h).2
                                  simpa using hn
                                omega
                              have ha : i ∈ a.fvEffects → False := by
                                simp [a, Ty.fvEffects]
                              have hδ : i ∈ δ.vars → False := by
                                simp [δ, Poly.Effect.var, sb]
                                omega
                              have hχ : i ∈ χ.vars → False := by
                                simp [χ, Poly.Effect.var, sb]
                                omega
                              simp only [Output.supportEffects,
                                Finset.mem_union] at hi
                              rcases hi with (ha' | hχ') | hC
                              · exact False.elim (ha ha')
                              · exact False.elim (hχ hχ')
                              · have hh := hCsup hC
                                simp only [Finset.mem_union] at hh
                                rcases hh with (((((((((((hCin | hCr) | hCo) |
                                  hτr) | hτo) | ha') | hεin) | hεr) |
                                  hεo) | hδ') | hχ') | hdecl') | hlocal'
                                · exact hrbC hCin
                                · exact hrrC hCr
                                · exact hrcC hCo
                                · exact hrrTy hτr
                                · exact hrcTy hτo
                                · exact False.elim (ha ha')
                                · exact hrbEff hεin
                                · exact hrrEff hεr
                                · exact hrcEff hεo
                                · exact False.elim (hδ hδ')
                                · exact False.elim (hχ hχ')
                                · exact False.elim (hdecl hdecl')
                                · exact False.elim (hlocal hlocal')
                          · simp [hd, hb, hr, hc, hsafe, hs,
                              ρ, η, decl, sb, a, δ, χ, sr] at hrun
                            exact False.elim (hcs hrun.1)
                        · simp [hd, hb, hr, hc, hsafe, hs,
                            ρ, η, decl, sb, a, δ, χ, sr] at hrun
                      · simp [hd, hb, hr, hsafe, ρ, η, sb, sr] at hrun

end SystemFXi.EHMX

namespace SystemFXi.EHMX

/-- Below its input supply, a generated return clause can only refer to
names from its context, which predates the operation binders. -/
theorem generated_return_old_support
    {sig : Signature} {X : Domain}
    (hX : LawfulFVRename X) (hClosed : sig.Closed)
    (Γ : Context X) (raw : OpDecl) (rb rr : Output X)
    (ret : Expr)
    (hΓT : ∀ σ ∈ Γ, ∀ i ∈ σ.usedTypes, i < rb.next.types)
    (hΓE : ∀ σ ∈ Γ, ∀ i ∈ σ.usedEffects, i < rb.next.effects)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hr : generate sig X (Scheme.mono rb.ty :: Γ) ret
      ⟨(rb.next.advance raw.typeVars raw.effectVars).types + 1,
        (rb.next.advance raw.typeVars raw.effectVars).effects + 2⟩ =
      some rr) :
    (∀ i ∈ rr.supportTypes,
      i < (rb.next.advance raw.typeVars raw.effectVars).types + 1 →
      i < rb.next.types) ∧
    (∀ i ∈ rr.supportEffects,
      i < (rb.next.advance raw.typeVars raw.effectVars).effects + 2 →
      i < rb.next.effects) := by
  have h := generate_support_origin hX hClosed hr
  constructor
  · intro i hi hlt
    rcases h.1 i hi hlt with ⟨σ, hσ, hu⟩
    rcases List.mem_cons.mp hσ with rfl | hrest
    · simp [Scheme.usedTypes, Scheme.mono,
        Constraint.fvTypes, Constraint.boundTypes] at hu
      exact hbT i (Finset.mem_union_left _ hu)
    · exact hΓT σ hrest i hu
  · intro i hi hlt
    rcases h.2 i hi hlt with ⟨σ, hσ, hu⟩
    rcases List.mem_cons.mp hσ with rfl | hrest
    · simp [Scheme.usedEffects, Scheme.mono,
        Constraint.fvEffects, Constraint.boundEffects] at hu
      exact hbE i (by simp [Output.supportEffects, hu])
    · exact hΓE σ hrest i hu

end SystemFXi.EHMX

namespace SystemFXi.EHMX

theorem Constraint.closeTypes_fvTypes {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.closeTypes vars c).fvTypes =
      c.fvTypes \ vars.toFinset := by
  induction vars with
  | nil => simp [Constraint.closeTypes]
  | cons i rest ih =>
      change (Constraint.closeTypes rest c).fvTypes.erase i =
        c.fvTypes \ (i :: rest).toFinset
      rw [ih]
      ext j
      simp [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_erase,
        Finset.mem_insert]
      tauto

theorem Constraint.closeEffects_fvEffects {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.closeEffects vars c).fvEffects =
      c.fvEffects \ vars.toFinset := by
  induction vars with
  | nil => simp [Constraint.closeEffects]
  | cons i rest ih =>
      change (Constraint.closeEffects rest c).fvEffects.erase i =
        c.fvEffects \ (i :: rest).toFinset
      rw [ih]
      ext j
      simp [List.toFinset_cons, Finset.mem_sdiff, Finset.mem_erase,
        Finset.mem_insert]
      tauto

theorem Constraint.closeTypes_fvEffects {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.closeTypes vars c).fvEffects = c.fvEffects := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      simpa [Constraint.closeTypes, Constraint.fvEffects] using ih

theorem Constraint.closeEffects_fvTypes {X : Domain}
    (vars : List Nat) (c : Constraint X) :
    (Constraint.closeEffects vars c).fvTypes = c.fvTypes := by
  induction vars with
  | nil => rfl
  | cons i rest ih =>
      simpa [Constraint.closeEffects, Constraint.fvTypes] using ih

theorem Constraint.close_fvTypes {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) :
    (Constraint.close types effects c).fvTypes =
      c.fvTypes \ types := by
  simp [Constraint.close, Constraint.closeTypes_fvTypes,
    Constraint.closeEffects_fvTypes]

theorem Constraint.close_fvEffects {X : Domain}
    (types effects : Finset Nat) (c : Constraint X) :
    (Constraint.close types effects c).fvEffects =
      c.fvEffects \ effects := by
  simp [Constraint.close, Constraint.closeTypes_fvEffects,
    Constraint.closeEffects_fvEffects]

end SystemFXi.EHMX

namespace SystemFXi.EHMX

theorem Constraint.handler_fvTypes {X : Domain}
    (op : Op) (decl : OpDecl)
    (Cin Cr Co : Constraint X) (τr τo a : Ty)
    (εin εr εo δ χ : Effect)
    (localTypes localEffects : Finset Nat) :
    (Constraint.handler op decl Cin Cr Co τr τo a
      εin εr εo δ χ localTypes localEffects).fvTypes =
      Cin.fvTypes ∪ Cr.fvTypes ∪ τr.fvTypes ∪ a.fvTypes ∪
        (((Co.fvTypes ∪ τo.fvTypes ∪ a.fvTypes) \ localTypes) \
          decl.typeVars) := by
  ext i
  simp [Constraint.handler, Constraint.fvTypes,
    Constraint.close_fvTypes, Constraint.project_fvTypes,
    Constraint.split, Finset.mem_sdiff]

theorem Constraint.handler_fvEffects {X : Domain}
    (op : Op) (decl : OpDecl)
    (Cin Cr Co : Constraint X) (τr τo a : Ty)
    (εin εr εo δ χ : Effect)
    (localTypes localEffects : Finset Nat) :
    (Constraint.handler op decl Cin Cr Co τr τo a
      εin εr εo δ χ localTypes localEffects).fvEffects =
      Cin.fvEffects ∪ Cr.fvEffects ∪ τr.fvEffects ∪
      a.fvEffects ∪ εin.vars ∪ εr.vars ∪ δ.vars ∪ χ.vars ∪
        (((Co.fvEffects ∪ τo.fvEffects ∪ a.fvEffects ∪
          εo.vars ∪ χ.vars) \ localEffects) \ decl.effectVars) := by
  ext i
  simp [Constraint.handler, Constraint.fvEffects,
    Constraint.close_fvEffects, Constraint.project_fvEffects,
    Constraint.split, Finset.mem_sdiff]
  tauto

end SystemFXi.EHMX

namespace SystemFXi.EHMX

theorem OpDecl.closed_alphaRename_used_interval
    (raw : OpDecl) (hc : raw.Closed) (s : Supply) :
    let ρ := renameBound raw.typeVars s.types
    let η := renameBound raw.effectVars s.effects
    let decl := raw.alphaRename ρ η
    (∀ i ∈ decl.usedTypes,
      s.types < i ∧ i < (s.advance raw.typeVars raw.effectVars).types) ∧
    (∀ i ∈ decl.usedEffects,
      s.effects < i ∧ i < (s.advance raw.typeVars raw.effectVars).effects) := by
  dsimp
  have hlow := raw.closed_alphaRename_used_ge hc s
  constructor
  · intro i hi
    have him : i ∈ raw.usedTypes.image
        (renameBound raw.typeVars s.types) := by
      simp [OpDecl.usedTypes, OpDecl.alphaRename,
        Ty.fvTypes_rename, Finset.image_union] at hi ⊢
      aesop
    rcases Finset.mem_image.mp him with ⟨j, hj, rfl⟩
    exact ⟨hlow.1 _ hi,
      (s.advance_above_renamed raw.typeVars raw.effectVars).1
        j (raw.closed_usedTypes hc hj)⟩
  · intro i hi
    have him : i ∈ raw.usedEffects.image
        (renameBound raw.effectVars s.effects) := by
      simp [OpDecl.usedEffects, OpDecl.alphaRename,
        Ty.fvEffects_rename, Finset.image_union] at hi ⊢
      aesop
    rcases Finset.mem_image.mp him with ⟨j, hj, rfl⟩
    exact ⟨hlow.2 _ hi,
      (s.advance_above_renamed raw.typeVars raw.effectVars).2
        j (raw.closed_usedEffects hc hj)⟩

end SystemFXi.EHMX

namespace SystemFXi.EHMX

/-- Projection removes every clause name allocated after the return clause. -/
theorem generated_handler_outer_fv_below {X : Domain}
    (op : Op) (decl : OpDecl) (sb : Supply)
    (rb rr rc : Output X)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hrT : ∀ i ∈ rr.supportTypes, i < rr.next.types)
    (hrE : ∀ i ∈ rr.supportEffects, i < rr.next.effects)
    (hcT : ∀ i ∈ rc.supportTypes, i < rc.next.types)
    (hcE : ∀ i ∈ rc.supportEffects, i < rc.next.effects)
    (hnextB : rb.next.types ≤ rr.next.types ∧
      rb.next.effects ≤ rr.next.effects)
    (hnextR : rr.next.types ≤ rc.next.types ∧
      rr.next.effects ≤ rc.next.effects)
    (ha : sb.types < rr.next.types)
    (_hδ : sb.effects < rr.next.effects)
    (hχ : sb.effects + 1 < rr.next.effects) :
    let localTypes :=
      Finset.range rc.next.types \ Finset.range rr.next.types
    let localEffects :=
      Finset.range rc.next.effects \ Finset.range rr.next.effects
    let C := Constraint.handler op decl
      rb.constraints rr.constraints rc.constraints
      rr.ty rc.ty (Ty.var sb.types)
      rb.effect rr.effect rc.effect
      (Poly.Effect.var sb.effects)
      (Poly.Effect.var (sb.effects + 1))
      localTypes localEffects
    (∀ i ∈ C.fvTypes, i < rr.next.types) ∧
      (∀ i ∈ C.fvEffects, i < rr.next.effects) := by
  dsimp
  constructor
  · intro i hi
    rw [Constraint.handler_fvTypes] at hi
    simp only [Finset.mem_union, Finset.mem_sdiff,
      Ty.fvTypes, Finset.mem_singleton] at hi
    rcases hi with (((hCin | hCr) | hτr) | ha') | hproj
    · exact lt_of_lt_of_le
        (hbT i (Finset.mem_union_right _
          (by simp [Constraint.usedTypes, hCin]))) hnextB.1
    · exact hrT i (Finset.mem_union_right _
        (by simp [Constraint.usedTypes, hCr]))
    · exact hrT i (Finset.mem_union_left _ hτr)
    · omega
    · rcases hproj with ⟨⟨hsource, hnotLocal⟩, _⟩
      have hrc : i < rc.next.types := by
        rcases hsource with (hCo | hτo) | ha'
        · exact hcT i (Finset.mem_union_right _
            (by
              have hh : i ∈ rc.constraints.usedTypes := by
                simp [Constraint.usedTypes, hCo]
              exact hh))
        · exact hcT i (Finset.mem_union_left _ hτo)
        · omega
      by_contra hbad
      have hloc : i ∈ Finset.range rc.next.types \
          Finset.range rr.next.types := by
        simp only [Finset.mem_sdiff, Finset.mem_range]
        omega
      exact hnotLocal (Finset.mem_sdiff.mp hloc)
  · intro i hi
    rw [Constraint.handler_fvEffects] at hi
    simp only [Finset.mem_union, Finset.mem_sdiff,
      Ty.fvEffects, Poly.Effect.var,
      Finset.mem_singleton] at hi
    simp at hi
    rcases hi with ((((((hCin | hCr) | hτr) | hεin) |
      hεr) | hδ') | hχ') | hproj
    · exact lt_of_lt_of_le
        (hbE i (by simp [Output.supportEffects,
          Constraint.usedEffects, hCin])) hnextB.2
    · exact hrE i (by simp [Output.supportEffects,
        Constraint.usedEffects, hCr])
    · exact hrE i (by simp [Output.supportEffects, hτr])
    · exact lt_of_lt_of_le
        (hbE i (by simp [Output.supportEffects, hεin])) hnextB.2
    · exact hrE i (by simp [Output.supportEffects, hεr])
    · omega
    · omega
    · rcases hproj with ⟨⟨hsource, hnotLocal⟩, _⟩
      apply hnotLocal
      rcases hsource with ((hCo | hτo) | hεo) | hχ'
      · exact hcE i (by simp [Output.supportEffects,
          Constraint.usedEffects, hCo])
      · exact hcE i (by simp [Output.supportEffects, hτo])
      · exact hcE i (by simp [Output.supportEffects, hεo])
      · omega

end SystemFXi.EHMX

namespace SystemFXi.EHMX

theorem generated_handler_binders_avoid_outer {X : Domain}
    (op : Op) (raw : OpDecl) (hc : raw.Closed)
    (rb rr rc : Output X)
    (localTypes localEffects : Finset Nat)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hrOldT : ∀ i ∈ rr.supportTypes,
      i < (rb.next.advance raw.typeVars raw.effectVars).types + 1 →
      i < rb.next.types)
    (hrOldE : ∀ i ∈ rr.supportEffects,
      i < (rb.next.advance raw.typeVars raw.effectVars).effects + 2 →
      i < rb.next.effects) :
    let ρ := renameBound raw.typeVars rb.next.types
    let η := renameBound raw.effectVars rb.next.effects
    let decl := raw.alphaRename ρ η
    let sb := rb.next.advance raw.typeVars raw.effectVars
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    let C := Constraint.handler op decl
      rb.constraints rr.constraints rc.constraints rr.ty rc.ty a
      rb.effect rr.effect rc.effect δ χ localTypes localEffects
    decl.typeVars ∩ C.fvTypes = ∅ ∧
      decl.effectVars ∩ C.fvEffects = ∅ := by
  dsimp
  let ρ := renameBound raw.typeVars rb.next.types
  let η := renameBound raw.effectVars rb.next.effects
  let decl := raw.alphaRename ρ η
  let sb := rb.next.advance raw.typeVars raw.effectVars
  have hi := raw.closed_alphaRename_used_interval hc rb.next
  constructor
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro i hbind hfv
    have hdecl : i ∈ decl.usedTypes := by
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hbind)
    have hlo := (hi.1 i hdecl).1
    have hhi := (hi.1 i hdecl).2
    rw [Constraint.handler_fvTypes] at hfv
    simp only [Finset.mem_union, Finset.mem_sdiff,
      Ty.fvTypes, Finset.mem_singleton] at hfv
    rcases hfv with (((hCin | hCr) | hτr) | ha) | hproj
    · have h := hbT i (by simp [Output.supportTypes,
          Constraint.usedTypes, hCin])
      omega
    · have h := hrOldT i (by simp [Output.supportTypes,
          Constraint.usedTypes, hCr]) (by omega)
      omega
    · have h := hrOldT i (Finset.mem_union_left _ hτr)
        (by omega)
      omega
    · omega
    · exact hproj.2 hbind
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro i hbind hfv
    have hdecl : i ∈ decl.usedEffects := by
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hbind)
    have hlo := (hi.2 i hdecl).1
    have hhi := (hi.2 i hdecl).2
    rw [Constraint.handler_fvEffects] at hfv
    simp only [Finset.mem_union, Finset.mem_sdiff,
      Ty.fvEffects, Poly.Effect.var,
      Finset.mem_singleton] at hfv
    simp at hfv
    rcases hfv with ((((((hCin | hCr) | hτr) | hεin) |
      hεr) | hδ) | hχ) | hproj
    · have h := hbE i (by simp [Output.supportEffects,
        Constraint.usedEffects, hCin])
      omega
    · have h := hrOldE i (by simp [Output.supportEffects,
        Constraint.usedEffects, hCr]) (by omega)
      omega
    · have h := hrOldE i (by simp [Output.supportEffects, hτr])
        (by omega)
      omega
    · have h := hbE i (by simp [Output.supportEffects, hεin])
      omega
    · have h := hrOldE i (by simp [Output.supportEffects, hεr])
        (by omega)
      omega
    · omega
    · omega
    · exact hproj.2 hbind

end SystemFXi.EHMX

set_option maxHeartbeats 1000000

namespace SystemFXi.EHMX

theorem generated_clauseScope_of_bounds {X : Domain}
    (Γ : Context X) (op : Op) (raw : OpDecl) (hc : raw.Closed)
    (rb rr rc : Output X)
    (hΓT : ∀ i ∈ Γ.fvTypes, i < rr.next.types)
    (hΓE : ∀ i ∈ Γ.fvEffects, i < rr.next.effects)
    (hbT : ∀ i ∈ rb.supportTypes, i < rb.next.types)
    (hbE : ∀ i ∈ rb.supportEffects, i < rb.next.effects)
    (hrT : ∀ i ∈ rr.supportTypes, i < rr.next.types)
    (hrE : ∀ i ∈ rr.supportEffects, i < rr.next.effects)
    (hcT : ∀ i ∈ rc.supportTypes, i < rc.next.types)
    (hcE : ∀ i ∈ rc.supportEffects, i < rc.next.effects)
    (hrOldT : ∀ i ∈ rr.supportTypes,
      i < (rb.next.advance raw.typeVars raw.effectVars).types + 1 →
      i < rb.next.types)
    (hrOldE : ∀ i ∈ rr.supportEffects,
      i < (rb.next.advance raw.typeVars raw.effectVars).effects + 2 →
      i < rb.next.effects)
    (hnextB : rb.next.types ≤ rr.next.types ∧
      rb.next.effects ≤ rr.next.effects)
    (hnextR : rr.next.types ≤ rc.next.types ∧
      rr.next.effects ≤ rc.next.effects)
    (ha : (rb.next.advance raw.typeVars raw.effectVars).types <
      rr.next.types)
    (hχ : (rb.next.advance raw.typeVars raw.effectVars).effects + 1 <
      rr.next.effects) :
    let ρ := renameBound raw.typeVars rb.next.types
    let η := renameBound raw.effectVars rb.next.effects
    let decl := raw.alphaRename ρ η
    let sb := rb.next.advance raw.typeVars raw.effectVars
    let a := Ty.var sb.types
    let δ := Poly.Effect.var sb.effects
    let χ := Poly.Effect.var (sb.effects + 1)
    let localTypes :=
      Finset.range rc.next.types \ Finset.range rr.next.types
    let localEffects :=
      Finset.range rc.next.effects \ Finset.range rr.next.effects
    let C := Constraint.handler op decl
      rb.constraints rr.constraints rc.constraints rr.ty rc.ty a
      rb.effect rr.effect rc.effect δ χ localTypes localEffects
    decl.ClauseScope Γ C rb.ty a rb.effect rr.effect δ χ
      localTypes localEffects := by
  dsimp
  let ρ := renameBound raw.typeVars rb.next.types
  let η := renameBound raw.effectVars rb.next.effects
  let decl := raw.alphaRename ρ η
  let sb := rb.next.advance raw.typeVars raw.effectVars
  let a := Ty.var sb.types
  let δ := Poly.Effect.var sb.effects
  let χ := Poly.Effect.var (sb.effects + 1)
  let localTypes := Finset.range rc.next.types \
    Finset.range rr.next.types
  let localEffects := Finset.range rc.next.effects \
    Finset.range rr.next.effects
  let C := Constraint.handler op decl
    rb.constraints rr.constraints rc.constraints rr.ty rc.ty a
    rb.effect rr.effect rc.effect δ χ localTypes localEffects
  have hbind := generated_handler_binders_avoid_outer op raw hc
    rb rr rc localTypes localEffects hbT hbE hrOldT hrOldE
  have houter := generated_handler_outer_fv_below op decl sb
    rb rr rc hbT hbE hrT hrE hcT hcE hnextB hnextR ha
    (by
      change (rb.next.advance raw.typeVars raw.effectVars).effects <
        rr.next.effects
      omega) hχ
  have hdecl := raw.closed_alphaRename_used_interval hc rb.next
  constructor
  · exact hbind.1
  constructor
  · exact hbind.2
  constructor
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro i hlocal hfixed
    have hlow : rr.next.types ≤ i := by
      have hn := (Finset.mem_sdiff.mp hlocal).2
      simpa [localTypes] using hn
    simp only [Finset.mem_union] at hfixed
    rcases hfixed with ((((((hΓ | hC) | hτin) | ha') |
      hdeclVar) | hinput) | houtput)
    · have := hΓT i hΓ; omega
    · have := houter.1 i hC; omega
    · have := hbT i (Finset.mem_union_left _ hτin)
      omega
    · simp [Ty.fvTypes] at ha'
      omega
    · have hu : i ∈ decl.usedTypes := by
        exact Finset.mem_union_left _
          (Finset.mem_union_left _ hdeclVar)
      have := (hdecl.1 i hu).2
      omega
    · have hu : i ∈ decl.usedTypes := by
        exact Finset.mem_union_left _
          (Finset.mem_union_right _ hinput)
      have := (hdecl.1 i hu).2
      omega
    · have hu : i ∈ decl.usedTypes := by
        exact Finset.mem_union_right _ houtput
      have := (hdecl.1 i hu).2
      omega
  · rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
    intro i hlocal hfixed
    have hlow : rr.next.effects ≤ i := by
      have hn := (Finset.mem_sdiff.mp hlocal).2
      simpa [localEffects] using hn
    simp only [Finset.mem_union] at hfixed
    have hΓ : i ∈ Γ.fvEffects → False := by
      intro h; have := hΓE i h; omega
    have hC : i ∈ C.fvEffects → False := by
      intro h; have := houter.2 i h; omega
    have hty : i ∈ rb.ty.fvEffects → False := by
      intro h
      have := hbE i (by simp [Output.supportEffects, h])
      omega
    have hεin : i ∈ rb.effect.vars → False := by
      intro h
      have := hbE i (by simp [Output.supportEffects, h])
      omega
    have hεr : i ∈ rr.effect.vars → False := by
      intro h
      have := hrE i (by simp [Output.supportEffects, h])
      omega
    have hdeclBelow : ∀ j ∈ decl.usedEffects,
        j < rr.next.effects := by
      intro j hj
      have := (hdecl.2 j hj).2
      omega
    have hdeclVar : i ∈ decl.effectVars → False := by
      intro h
      have := hdeclBelow i (Finset.mem_union_left _
        (Finset.mem_union_left _ h))
      omega
    have hinput : i ∈ decl.input.fvEffects → False := by
      intro h
      have := hdeclBelow i (Finset.mem_union_left _
        (Finset.mem_union_right _ h))
      omega
    have houtput : i ∈ decl.output.fvEffects → False := by
      intro h
      have := hdeclBelow i (Finset.mem_union_right _ h)
      omega
    simp only [Ty.fvEffects, Poly.Effect.var,
      Finset.mem_singleton] at hfixed
    rcases hfixed with (((((((((hΓ' | hC') | hty') | ha') |
      hεin') | hεr') | hδ') | hχ') | hdecl') | hin') | hout'
    · exact hΓ hΓ'
    · exact hC hC'
    · exact hty hty'
    · simp at ha'
    · exact hεin hεin'
    · exact hεr hεr'
    · omega
    · omega
    · exact hdeclVar hdecl'
    · exact hinput hin'
    · exact houtput hout'

end SystemFXi.EHMX

namespace SystemFXi.EHMX

private noncomputable def assignImageReverse {α : Type}
    (bound : Finset Nat) (rename : Nat → Nat)
    (values original : Nat → α) (j : Nat) : α :=
  if h : ∃ i, i ∈ bound ∧ rename i = j then
    values (Classical.choose h)
  else original j

private theorem assignImageReverse_mem {α : Type}
    (bound : Finset Nat) (rename : Nat → Nat)
    (hinj : Set.InjOn rename bound)
    (values original : Nat → α) (i : Nat) (hi : i ∈ bound) :
    assignImageReverse bound rename values original (rename i) =
      values i := by
  let h : ∃ k, k ∈ bound ∧ rename k = rename i := ⟨i, hi, rfl⟩
  have hc := Classical.choose_spec h
  have hki : Classical.choose h = i := hinj hc.1 hi hc.2
  simp [assignImageReverse, h, hki]

private theorem assignImageReverse_not_mem {α : Type}
    (bound : Finset Nat) (rename : Nat → Nat)
    (values original : Nat → α) (j : Nat)
    (hj : j ∉ bound.image rename) :
    assignImageReverse bound rename values original j = original j := by
  have hnone : ¬ ∃ i, i ∈ bound ∧ rename i = j := by
    rintro ⟨i, hi, rfl⟩
    exact hj (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  simp [assignImageReverse, hnone]

/-- Every assignment of the generated rigid operation variables has a
matching assignment of the declarative operation variables. -/
theorem OpDecl.closed_rename_reverse
    (raw : OpDecl) (hc : raw.Closed)
    (ρg ηg ρd ηd : Nat → Nat)
    (hsafeD : raw.AlphaSafe ρd ηd)
    (vg vd : Valuation) :
    let decld := raw.alphaRename ρd ηd
    ∃ wd : Valuation,
      (∀ i, i ∉ decld.typeVars → wd.types i = vd.types i) ∧
      (∀ i, i ∉ decld.effectVars → wd.effects i = vd.effects i) ∧
      (raw.input.rename ρg ηg).eval vg = decld.input.eval wd ∧
      (raw.output.rename ρg ηg).eval vg = decld.output.eval wd := by
  dsimp
  let wd : Valuation :=
    ⟨assignImageReverse raw.typeVars ρd
        (vg.types ∘ ρg) vd.types,
      assignImageReverse raw.effectVars ηd
        (vg.effects ∘ ηg) vd.effects⟩
  have hinjT : Set.InjOn ρd raw.typeVars :=
    Finset.injOn_of_card_image_eq hsafeD.1
  have hinjE : Set.InjOn ηd raw.effectVars :=
    Finset.injOn_of_card_image_eq hsafeD.2.1
  have hfixedT : ∀ i,
      i ∉ (raw.alphaRename ρd ηd).typeVars →
      wd.types i = vd.types i := by
    intro i hi
    exact assignImageReverse_not_mem raw.typeVars ρd
      (vg.types ∘ ρg) vd.types i
      (by simpa [OpDecl.alphaRename] using hi)
  have hfixedE : ∀ i,
      i ∉ (raw.alphaRename ρd ηd).effectVars →
      wd.effects i = vd.effects i := by
    intro i hi
    exact assignImageReverse_not_mem raw.effectVars ηd
      (vg.effects ∘ ηg) vd.effects i
      (by simpa [OpDecl.alphaRename] using hi)
  have hagreeT : ∀ i ∈ raw.usedTypes,
      vg.types (ρg i) = wd.types (ρd i) := by
    intro i hi
    have hb := raw.closed_usedTypes hc hi
    exact (assignImageReverse_mem raw.typeVars ρd hinjT
      (vg.types ∘ ρg) vd.types i hb).symm
  have hagreeE : ∀ i ∈ raw.usedEffects,
      vg.effects (ηg i) = wd.effects (ηd i) := by
    intro i hi
    have hb := raw.closed_usedEffects hc hi
    exact (assignImageReverse_mem raw.effectVars ηd hinjE
      (vg.effects ∘ ηg) vd.effects i hb).symm
  refine ⟨wd, hfixedT, hfixedE, ?_, ?_⟩
  · change (raw.input.rename ρg ηg).eval vg =
      (raw.input.rename ρd ηd).eval wd
    rw [Ty.eval_rename, Ty.eval_rename]
    exact Ty.eval_support raw.input
      (vg.pullback ρg ηg) (wd.pullback ρd ηd)
      (fun i hi => hagreeT i (by simp [OpDecl.usedTypes, hi]))
      (fun i hi => hagreeE i (by simp [OpDecl.usedEffects, hi]))
  · change (raw.output.rename ρg ηg).eval vg =
      (raw.output.rename ρd ηd).eval wd
    rw [Ty.eval_rename, Ty.eval_rename]
    exact Ty.eval_support raw.output
      (vg.pullback ρg ηg) (wd.pullback ρd ηd)
      (fun i hi => hagreeT i (by simp [OpDecl.usedTypes, hi]))
      (fun i hi => hagreeE i (by simp [OpDecl.usedEffects, hi]))

end SystemFXi.EHMX

namespace SystemFXi.EHMX

theorem generate_handle_of_runs
    {sig : Signature} {X : Domain}
    (hX : LawfulFVRename X) (hClosed : sig.Closed)
    (Γ : Context X) (body ret clause : Expr) (op : Op)
    (raw : OpDecl) (s : Supply)
    (rb rr rc : Output X)
    (ops : Finset Op)
    (hb : BoundedInputs sig X Γ ops s)
    (hd : sig op = some raw)
    (hbody : generate sig X Γ body s = some rb)
    (hret : generate sig X (Scheme.mono rb.ty :: Γ) ret
      ⟨(rb.next.advance raw.typeVars raw.effectVars).types + 1,
        (rb.next.advance raw.typeVars raw.effectVars).effects + 2⟩ =
      some rr)
    (hclause : generate sig X
      (Scheme.mono
          (.arr (raw.alphaRename
            (renameBound raw.typeVars rb.next.types)
            (renameBound raw.effectVars rb.next.effects)).output
            (Poly.Effect.var
              ((rb.next.advance raw.typeVars raw.effectVars).effects + 1))
            (.var (rb.next.advance raw.typeVars raw.effectVars).types)) ::
        Scheme.mono (raw.alphaRename
          (renameBound raw.typeVars rb.next.types)
          (renameBound raw.effectVars rb.next.effects)).input :: Γ)
      clause rr.next = some rc)
    (hbBound : (∀ i ∈ rb.supportTypes, i < rb.next.types) ∧
      (∀ i ∈ rb.supportEffects, i < rb.next.effects))
    (hrBound : (∀ i ∈ rr.supportTypes, i < rr.next.types) ∧
      (∀ i ∈ rr.supportEffects, i < rr.next.effects))
    (hcBound : (∀ i ∈ rc.supportTypes, i < rc.next.types) ∧
      (∀ i ∈ rc.supportEffects, i < rc.next.effects)) :
    ∃ r : Output X,
      generate sig X Γ (.handle body op ret clause) s = some r := by
  let ρ := renameBound raw.typeVars rb.next.types
  let η := renameBound raw.effectVars rb.next.effects
  let decl := raw.alphaRename ρ η
  let sb := rb.next.advance raw.typeVars raw.effectVars
  let a := Ty.var sb.types
  let δ := Poly.Effect.var sb.effects
  let χ := Poly.Effect.var (sb.effects + 1)
  let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
  let localTypes :=
    Finset.range rc.next.types \ Finset.range rr.next.types
  let localEffects :=
    Finset.range rc.next.effects \ Finset.range rr.next.effects
  let C := Constraint.handler op decl
    rb.constraints rr.constraints rc.constraints rr.ty rc.ty a
    rb.effect rr.effect rc.effect δ χ localTypes localEffects
  have hmB := generate_next_mono hbody
  have hmR := generate_next_mono hret
  have hmC := generate_next_mono hclause
  have hraw := hClosed op raw hd
  have hsafe : raw.AlphaSafe ρ η := by
    apply raw.renameBound_alphaSafe
    · intro i hi
      exact False.elim
        ((Finset.mem_sdiff.mp hi).2
          (hraw.1 (Finset.mem_sdiff.mp hi).1))
    · intro i hi
      exact False.elim
        ((Finset.mem_sdiff.mp hi).2
          (hraw.2 (Finset.mem_sdiff.mp hi).1))
  have hscope : decl.HandlerScope Γ rb.ty a
      rb.effect rr.effect δ χ := by
    exact generated_handlerScope_of_runs Γ ops s raw body ret rb rr
      hb hbody hbBound.1 hbBound.2 hret
  have hΓT : ∀ i ∈ Γ.fvTypes, i < rr.next.types := by
    intro i hi
    have h := (hb.contextFVBelow).1 i hi
    have ha := rb.next.advance_mono raw.typeVars raw.effectVars
    dsimp [sr, sb] at hmR
    omega
  have hΓE : ∀ i ∈ Γ.fvEffects, i < rr.next.effects := by
    intro i hi
    have h := (hb.contextFVBelow).2 i hi
    have ha := rb.next.advance_mono raw.typeVars raw.effectVars
    dsimp [sr, sb] at hmR
    omega
  have hretOld := generated_return_old_support hX hClosed
    Γ raw rb rr ret
    (by
      intro σ hσ i hi
      have h := hb.contextTypes σ hσ i hi
      omega)
    (by
      intro σ hσ i hi
      have h := hb.contextEffects σ hσ i hi
      omega)
    hbBound.1 hbBound.2 hret
  have hnextB : rb.next.types ≤ rr.next.types ∧
      rb.next.effects ≤ rr.next.effects := by
    have ha := rb.next.advance_mono raw.typeVars raw.effectVars
    dsimp [sr, sb] at hmR
    omega
  have ha : sb.types < rr.next.types := by
    change (rb.next.advance raw.typeVars raw.effectVars).types <
      rr.next.types
    exact lt_of_lt_of_le (Nat.lt_succ_self _)
      (by simpa [sr, sb] using hmR.1)
  have hχ : sb.effects + 1 < rr.next.effects := by
    change (rb.next.advance raw.typeVars raw.effectVars).effects + 1 <
      rr.next.effects
    have hm := hmR.2
    dsimp [sr, sb] at hm
    omega
  have hclscope : decl.ClauseScope Γ C rb.ty a
      rb.effect rr.effect δ χ localTypes localEffects := by
    exact generated_clauseScope_of_bounds Γ op raw hraw rb rr rc
      hΓT hΓE hbBound.1 hbBound.2 hrBound.1 hrBound.2
      hcBound.1 hcBound.2 hretOld.1 hretOld.2
      hnextB hmC ha hχ
  refine ⟨⟨a, χ, C, rc.next⟩, ?_⟩
  simp [generate, hd, hbody, hret, hclause,
    hsafe, hscope, hclscope,
    ρ, η, decl, sb, a, δ, χ,
    localTypes, localEffects, C]

end SystemFXi.EHMX

namespace SystemFXi.EHMX

theorem Constraint.holds_disjoint_frame {X : Domain}
    (hX : LawfulSupport X) (c : Constraint X)
    (bt be : Finset Nat) (v w : Valuation)
    (hbt : bt ∩ c.fvTypes = ∅)
    (hbe : be ∩ c.fvEffects = ∅)
    (ht : ∀ i, i ∉ bt → v.types i = w.types i)
    (he : ∀ i, i ∉ be → v.effects i = w.effects i) :
    c.holds v ↔ c.holds w := by
  apply Constraint.holds_support hX c v w
  · intro i hi
    apply ht i
    intro hb
    have hm : i ∈ bt ∩ c.fvTypes :=
      Finset.mem_inter.mpr ⟨hb, hi⟩
    simp [hbt] at hm
  · intro i hi
    apply he i
    intro hb
    have hm : i ∈ be ∩ c.fvEffects :=
      Finset.mem_inter.mpr ⟨hb, hi⟩
    simp [hbe] at hm

theorem Ty.eval_disjoint_frame
    (τ : Ty) (bt be : Finset Nat) (v w : Valuation)
    (hbt : bt ∩ τ.fvTypes = ∅)
    (hbe : be ∩ τ.fvEffects = ∅)
    (ht : ∀ i, i ∉ bt → v.types i = w.types i)
    (he : ∀ i, i ∉ be → v.effects i = w.effects i) :
    τ.eval v = τ.eval w := by
  apply Ty.eval_support τ v w
  · intro i hi
    apply ht i
    intro hb
    have hm : i ∈ bt ∩ τ.fvTypes :=
      Finset.mem_inter.mpr ⟨hb, hi⟩
    simp [hbt] at hm
  · intro i hi
    apply he i
    intro hb
    have hm : i ∈ be ∩ τ.fvEffects :=
      Finset.mem_inter.mpr ⟨hb, hi⟩
    simp [hbe] at hm

theorem Effect.eval_disjoint_frame
    (ε : Effect) (be : Finset Nat)
    (v w : Valuation)
    (hbe : be ∩ ε.vars = ∅)
    (he : ∀ i, i ∉ be → v.effects i = w.effects i) :
    ε.eval v.effects = ε.eval w.effects := by
  apply Effect.eval_support ε v w
  intro i hi
  apply he i
  intro hb
  have hm : i ∈ be ∩ ε.vars :=
    Finset.mem_inter.mpr ⟨hb, hi⟩
  simp [hbe] at hm

end SystemFXi.EHMX

namespace SystemFXi.EHMX

theorem Typing.generate_complete {sig : Signature} {X : Domain}
    (hRename : LawfulRename X)
    (hSupport : LawfulSupport X)
    (hFVRename : LawfulFVRename X)
    (hClosed : sig.Closed)
    {C : Constraint X} {Γd : Context X}
    {e : Expr} {τ : Ty} {ε : Effect}
    (h : Typing sig X C Γd e τ ε) :
    ∀ (Γg : Context X) (ops : Finset Op) (s : Supply),
      Γg.length = Γd.length →
      e.ops ⊆ ops →
      BoundedInputs sig X Γg ops s →
      ∃ r : Output X,
        generate sig X Γg e s = some r ∧
        Output.CoversAt Γg Γd C s r τ ε := by
  induction h with
  | var hlookup hadm hsafe hent =>
      intro Γg ops s hlen hops hb
      obtain ⟨σg, hlookupG⟩ :=
        Context.lookup_of_length_eq Γg _ _ hlen _ hlookup
      exact generate_var_coversAt hRename hSupport
        Γg _ _ ops s _ σg _ _ _
        hb hlookupG hlookup hadm hsafe hent
  | int n =>
      intro Γg ops s hlen hops hb
      refine ⟨⟨.base .int, ∅, .top, s⟩, by simp [generate], ?_⟩
      intro vg vd hctx hC
      exact ⟨vg, (fun _ _ => rfl), (fun _ _ => rfl),
        trivial, rfl, rfl⟩
  | bool b =>
      intro Γg ops s hlen hops hb
      refine ⟨⟨.base .bool, ∅, .top, s⟩, by simp [generate], ?_⟩
      intro vg vd hctx hC
      exact ⟨vg, (fun _ _ => rfl), (fun _ _ => rfl),
        trivial, rfl, rfl⟩
  | lam _ ih =>
      intro Γg ops s hlen hops hb
      let aG := Ty.var s.types
      let sb : Supply := {s with types := s.types + 1}
      have hbodyOps : _ := hops
      have hbase : BoundedInputs sig X Γg ops sb :=
        hb.mono (by dsimp [sb]; omega)
      have hchild : BoundedInputs sig X (Scheme.mono aG :: Γg)
          ops sb := by
        apply hbase.consMono aG
        · intro i hi
          simp [aG, Ty.fvTypes] at hi
          dsimp [sb]
          omega
        · intro i hi
          simp [aG, Ty.fvEffects] at hi
      rcases ih (Scheme.mono aG :: Γg) ops sb
          (by simp [hlen]) hbodyOps hchild with ⟨rb, hr, hcov⟩
      refine ⟨⟨.arr aG rb.effect rb.ty, ∅,
        rb.constraints, rb.next⟩, ?_, ?_⟩
      · simp [generate, aG, sb, hr]
      · exact Output.CoversAt.lam hSupport Γg _ _ ops s rb
          _ _ _ hb hcov
  | app _ _ ihf ihx =>
      intro Γg ops s hlen hops hb
      rcases ihf Γg ops s hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb with
        ⟨rf, hrf, hcovF⟩
      have hstart := generate_next_mono hrf
      have hbX := hb.mono hstart
      rcases ihx Γg ops rf.next hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hbX with
        ⟨rx, hrx, hcovX⟩
      have hfBound := generate_support_below hFVRename
        hrf ops (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb
      have hxBound := generate_support_below hFVRename
        hrx ops (by intro op hop; exact hops (by simp [Expr.ops, hop])) hbX
      have hnext := generate_next_mono hrx
      refine ⟨⟨.var rx.next.types,
        rf.effect ∪ rx.effect ∪ Poly.Effect.var rx.next.effects,
        .and (.and rf.constraints rx.constraints)
          (.typeEq rf.ty
            (.arr rx.ty (Poly.Effect.var rx.next.effects)
              (.var rx.next.types))),
        ⟨rx.next.types + 1, rx.next.effects + 1⟩⟩, ?_, ?_⟩
      · simp [generate, hrf, hrx]
      · exact Output.CoversAt.app hSupport Γg _ _ ops s rf rx
          _ _ _ _ _ hb hfBound hxBound hstart hnext
          hcovF hcovX
  | perform =>
      rename_i cPerf ctxPerf op raw ρd ηd ePerf effPerf hsig hadm hbody ih
      intro Γg ops s hlen hops hb
      have hop : op ∈ ops := hops (by simp [Expr.ops])
      let sa := s.advance raw.typeVars raw.effectVars
      have hchild : BoundedInputs sig X Γg ops sa :=
        hb.mono ⟨Nat.le_of_lt (s.advance_mono
          raw.typeVars raw.effectVars).1,
          Nat.le_of_lt (s.advance_mono
          raw.typeVars raw.effectVars).2⟩
      rcases ih Γg ops sa hlen
          (by intro op' hop'; exact hops (by simp [Expr.ops, hop']))
          hchild with ⟨re, hr, hcov⟩
      refine ⟨⟨raw.output.rename
          (renameBound raw.typeVars s.types)
          (renameBound raw.effectVars s.effects),
          Poly.Effect.singleton op ∪ re.effect,
          .and re.constraints
            (.typeEq re.ty (raw.input.rename
              (renameBound raw.typeVars s.types)
              (renameBound raw.effectVars s.effects))),
          re.next⟩, ?_, ?_⟩
      · simp [generate, hsig, hr, sa]
      · exact Output.CoversAt.perform hSupport Γg _ _ ops s
          op raw _ _ re _ hb hop hsig (hClosed op raw hsig)
          hadm hcov
  | letVal hv _ _ ih₁ ih₂ =>
      intro Γg ops s hlen hops hb
      rcases ih₁ Γg ops s hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb with
        ⟨r₁, hr₁, hcov₁⟩
      have hstart := generate_next_mono hr₁
      have h₁Bound := generate_support_below hFVRename
        hr₁ ops (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb
      have hctx := (hb.mono hstart).consGeneralize
        r₁.constraints r₁.ty
        (by simpa [Output.supportTypes] using h₁Bound.1)
        (by
          intro i hi
          exact h₁Bound.2 i (by
            simp [Output.supportEffects] at hi ⊢
            aesop))
      rcases ih₂
          (Scheme.generalize Γg r₁.constraints r₁.ty :: Γg)
          ops r₁.next (by simp [hlen])
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hctx with
        ⟨r₂, hr₂, hcov₂⟩
      refine ⟨⟨r₂.ty, r₂.effect,
        .and (Scheme.residual Γg r₁.constraints r₁.ty)
          r₂.constraints, r₂.next⟩, ?_, ?_⟩
      · simp [generate, hr₁, Expr.isValue_iff.mpr hv, hr₂]
      · exact Output.CoversAt.letVal hSupport Γg _ _ _
          ops s r₁ r₂ _ _ _ hb h₁Bound hstart hcov₁ hcov₂
  | letMono hnv _ _ ih₁ ih₂ =>
      intro Γg ops s hlen hops hb
      rcases ih₁ Γg ops s hlen
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb with
        ⟨r₁, hr₁, hcov₁⟩
      have hstart := generate_next_mono hr₁
      have h₁Bound := generate_support_below hFVRename
        hr₁ ops (by intro op hop; exact hops (by simp [Expr.ops, hop])) hb
      have hctx := (hb.mono hstart).consMono r₁.ty
        (fun i hi => h₁Bound.1 i (Finset.mem_union_left _ hi))
        (fun i hi => h₁Bound.2 i
          (by simp [Output.supportEffects, hi]))
      rcases ih₂ (Scheme.mono r₁.ty :: Γg)
          ops r₁.next (by simp [hlen])
          (by intro op hop; exact hops (by simp [Expr.ops, hop])) hctx with
        ⟨r₂, hr₂, hcov₂⟩
      refine ⟨⟨r₂.ty, r₁.effect ∪ r₂.effect,
        .and r₁.constraints r₂.constraints, r₂.next⟩,
        ?_, ?_⟩
      · simp [generate, hr₁, Expr.isValue_iff, hnv, hr₂]
      · exact Output.CoversAt.letMono hSupport Γg _ _ ops s
          r₁ r₂ _ _ _ _ hb h₁Bound hstart hcov₁ hcov₂
  | @handle C D Γ body op ret clause raw decl ρd ηd τin aD τo
      εin εr εo δd χd localTd localEd hsig hadm hsafe hren
      hscope hclscope hbody hret hclause hproj hsplit
      hδ hε ihb ihr ihc =>
      subst decl
      intro Γg ops s hlen hops hb
      have hbodyOps : body.ops ⊆ ops := by
        intro op' hop'
        exact hops (by simp [Expr.ops, hop'])
      have hretOps : ret.ops ⊆ ops := by
        intro op' hop'
        exact hops (by simp [Expr.ops, hop'])
      have hclauseOps : clause.ops ⊆ ops := by
        intro op' hop'
        exact hops (by simp [Expr.ops, hop'])
      rcases ihb Γg ops s hlen hbodyOps hb with
        ⟨rb, hrunB, hcovB⟩
      have hbBound := generate_support_below hFVRename hrunB
        ops hbodyOps hb
      have hmB := generate_next_mono hrunB
      let ρg := renameBound raw.typeVars rb.next.types
      let ηg := renameBound raw.effectVars rb.next.effects
      let declg := raw.alphaRename ρg ηg
      let sb := rb.next.advance raw.typeVars raw.effectVars
      let aG := Ty.var sb.types
      let δg := Poly.Effect.var sb.effects
      let χg := Poly.Effect.var (sb.effects + 1)
      let sr : Supply := ⟨sb.types + 1, sb.effects + 2⟩
      have hraw := hClosed op raw hsig
      have hbaseR : BoundedInputs sig X Γg ops sr := by
        apply hb.mono
        have h := rb.next.advance_mono raw.typeVars raw.effectVars
        dsimp [sr, sb]
        omega
      have hretCtx : BoundedInputs sig X
          (Scheme.mono rb.ty :: Γg) ops sr := by
        apply hbaseR.consMono rb.ty
        · intro i hi
          have h := hbBound.1 i (Finset.mem_union_left _ hi)
          have ha := rb.next.advance_mono
            raw.typeVars raw.effectVars
          dsimp [sr, sb]
          omega
        · intro i hi
          have h := hbBound.2 i (by
            simp [Output.supportEffects, hi])
          have ha := rb.next.advance_mono
            raw.typeVars raw.effectVars
          dsimp [sr, sb]
          omega
      rcases ihr (Scheme.mono rb.ty :: Γg) ops sr
          (by simp [hlen]) hretOps hretCtx with
        ⟨rr, hrunR, hcovR⟩
      have hrBound := generate_support_below hFVRename hrunR
        ops hretOps hretCtx
      have hmR := generate_next_mono hrunR
      have hinterval := raw.closed_alphaRename_used_interval
        hraw rb.next
      have hbaseC : BoundedInputs sig X Γg ops rr.next := by
        apply hb.mono
        have ha := rb.next.advance_mono
          raw.typeVars raw.effectVars
        dsimp [sr, sb] at hmR
        omega
      have hinputT : ∀ i ∈ declg.input.fvTypes,
          i < rr.next.types := by
        intro i hi
        have h := (hinterval.1 i (by
          exact Finset.mem_union_left _
            (Finset.mem_union_right _ hi))).2
        dsimp [sr, sb] at hmR
        omega
      have hinputE : ∀ i ∈ declg.input.fvEffects,
          i < rr.next.effects := by
        intro i hi
        have h := (hinterval.2 i (by
          exact Finset.mem_union_left _
            (Finset.mem_union_right _ hi))).2
        dsimp [sr, sb] at hmR
        omega
      have houtputT : ∀ i ∈ declg.output.fvTypes,
          i < rr.next.types := by
        intro i hi
        have h := (hinterval.1 i (by
          exact Finset.mem_union_right _ hi)).2
        dsimp [sr, sb] at hmR
        omega
      have houtputE : ∀ i ∈ declg.output.fvEffects,
          i < rr.next.effects := by
        intro i hi
        have h := (hinterval.2 i (by
          exact Finset.mem_union_right _ hi)).2
        dsimp [sr, sb] at hmR
        omega
      have hclauseCtx : BoundedInputs sig X
          (Scheme.mono (.arr declg.output χg aG) ::
            Scheme.mono declg.input :: Γg) ops rr.next := by
        apply (hbaseC.consMono declg.input hinputT hinputE).consMono
          (.arr declg.output χg aG)
        · intro i hi
          simp [Ty.fvTypes] at hi
          rcases hi with hout | ha
          · exact houtputT i hout
          · simp [aG, Ty.fvTypes, sb] at ha
            dsimp [sr, sb] at hmR
            omega
        · intro i hi
          simp [Ty.fvEffects, χg, aG,
            Poly.Effect.var] at hi
          rcases hi with hχ | hout
          · dsimp [sr, sb] at hmR
            simp [sb] at hχ
            omega
          · exact houtputE i hout
      rcases ihc
          (Scheme.mono (.arr declg.output χg aG) ::
            Scheme.mono declg.input :: Γg)
          ops rr.next (by simp [hlen])
          hclauseOps hclauseCtx with
        ⟨rc, hrunC, hcovC⟩
      have hcBound := generate_support_below hFVRename hrunC
        ops hclauseOps hclauseCtx
      obtain ⟨r, hrun⟩ := generate_handle_of_runs
        hFVRename hClosed Γg body ret clause op raw s rb rr rc ops
        hb hsig hrunB hrunR hrunC hbBound hrBound hcBound
      refine ⟨r, hrun, ?_⟩
      simp [generate, hsig, hrunB, hrunR, hrunC,
        ρg, ηg, declg, sb, aG, χg, sr] at hrun
      rcases hrun with ⟨_, _, _, heq⟩
      cases heq
      intro vg vd hctx hC
      rcases hcovB vg vd hctx hC with
        ⟨wb, hbFixT, hbFixE, hbC, hbTy, hbEff⟩
      let v0 := wb.assignAt sb (aD.eval vd)
        (δd.eval vd.effects)
      let v1 : Valuation :=
        ⟨v0.types, Function.update v0.effects
          (sb.effects + 1) (χd.eval vd.effects)⟩
      have hadvance := rb.next.advance_mono
        raw.typeVars raw.effectVars
      have h0fixed := Valuation.assignAt_preserves_below
        wb sb (aD.eval vd) (δd.eval vd.effects)
      have hbelowBTypes : ∀ i, i < rb.next.types →
          wb.types i = v1.types i := by
        intro i hi
        exact h0fixed.1 i (by dsimp [sb] at *; omega)
      have hbelowBEffects : ∀ i, i < rb.next.effects →
          wb.effects i = v1.effects i := by
        intro i hi
        have hne : i ≠ sb.effects + 1 := by
          dsimp [sb] at *
          omega
        have h0 := h0fixed.2 i (by dsimp [sb] at *; omega)
        simpa [v1, Function.update, hne] using h0
      have hframeB := rb.semantic_frame_of_below hSupport wb v1
        hbBound.1 hbBound.2 hbelowBTypes hbelowBEffects
      have hctxV1 : Γg.MoreGeneralAt Γ v1 vd := by
        apply Context.moreGeneralAt_below hSupport
          Γg Γ ops s hb vg v1 vd hctx
        · intro i hi
          exact (hbFixT i hi).trans
            (hbelowBTypes i (by omega))
        · intro i hi
          exact (hbFixE i hi).trans
            (hbelowBEffects i (by omega))
      have hmonoTop :
          (Scheme.mono (X := X) rb.ty).MoreGeneralAt
            (Scheme.mono τin) v1 vd := by
        apply (Scheme.mono_moreGeneralAt_iff rb.ty τin v1 vd).mpr
        exact hframeB.2.1.symm.trans hbTy
      have hctxRet : Context.MoreGeneralAt
          (Scheme.mono rb.ty :: Γg)
            (Scheme.mono τin :: Γ) v1 vd := by
        apply List.Forall₂.cons
        · exact hmonoTop
        · exact hctxV1
      rcases hcovR v1 vd hctxRet hC with
        ⟨wr, hrFixT, hrFixE, hrC, hrTy, hrEff⟩
      have hbelowBWTypes : ∀ i, i < rb.next.types →
          wb.types i = wr.types i := by
        intro i hi
        exact (hbelowBTypes i hi).trans
          (hrFixT i (by
            have h := hadvance.1
            dsimp [sr, sb]
            omega))
      have hbelowBWEffects : ∀ i, i < rb.next.effects →
          wb.effects i = wr.effects i := by
        intro i hi
        exact (hbelowBEffects i hi).trans
          (hrFixE i (by
            have h := hadvance.2
            dsimp [sr, sb]
            omega))
      have hframeBW := rb.semantic_frame_of_below hSupport wb wr
        hbBound.1 hbBound.2 hbelowBWTypes hbelowBWEffects
      have haWr : aG.eval wr = aD.eval vd := by
        have hkeep := hrFixT sb.types (by dsimp [sr]; omega)
        have hset : v1.types sb.types = aD.eval vd := by
          simp [v1, v0, Valuation.assignAt]
        simp [aG, Ty.eval]
        exact hkeep.symm.trans hset
      have hδWr : δg.eval wr.effects = δd.eval vd.effects := by
        have hkeep := hrFixE sb.effects (by dsimp [sr]; omega)
        have hset : v1.effects sb.effects =
            δd.eval vd.effects := by
          simp [v1, v0, Valuation.assignAt,
            Function.update]
        simp [δg, Poly.Effect.eval, Poly.Effect.var]
        exact hkeep.symm.trans hset
      have hχWr : χg.eval wr.effects = χd.eval vd.effects := by
        have hkeep := hrFixE (sb.effects + 1)
          (by dsimp [sr]; omega)
        have hset : v1.effects (sb.effects + 1) =
            χd.eval vd.effects := by
          simp [v1, Function.update]
        simp [χg, Poly.Effect.eval, Poly.Effect.var]
        exact hkeep.symm.trans hset
      have hsplitG :
          (Constraint.split (X := X) op rb.effect δg).holds wr := by
        apply (Constraint.split_iff wr op rb.effect δg).mpr
        rw [hδWr, hframeBW.2.2.symm, hbEff]
        exact (Constraint.split_iff vd op εin δd).mp
          (hsplit vd hC)
      have hδG :
          (Constraint.effectLe (X := X) δg χg).holds wr := by
        change δg.eval wr.effects ⊆ χg.eval wr.effects
        rw [hδWr, hχWr]
        exact hδ vd hC
      have hεG :
          (Constraint.effectLe (X := X) rr.effect χg).holds wr := by
        change rr.effect.eval wr.effects ⊆ χg.eval wr.effects
        rw [hrEff, hχWr]
        exact hε vd hC
      have hτG :
          (Constraint.typeEq (X := X) rr.ty aG).holds wr := by
        change rr.ty.eval wr = aG.eval wr
        exact hrTy.trans haWr.symm
      let localT :=
        Finset.range rc.next.types \ Finset.range rr.next.types
      let localE :=
        Finset.range rc.next.effects \ Finset.range rr.next.effects
      have hprojG :
          (Constraint.close declg.typeVars declg.effectVars
            (Constraint.project localT localE
              (.and rc.constraints
                (.and (.typeEq rc.ty aG)
                  (.effectLe rc.effect χg))))).holds wr := by
        apply (Constraint.close_project_holds_iff
          declg.typeVars declg.effectVars localT localE
          (.and rc.constraints
            (.and (.typeEq rc.ty aG)
              (.effectLe rc.effect χg))) wr).mpr
        intro bt be hbt hbe
        let bg : Valuation := ⟨bt, be⟩
        have hbgT : ∀ i, i ∉ declg.typeVars →
            bg.types i = wr.types i := hbt
        have hbgE : ∀ i, i ∉ declg.effectVars →
            bg.effects i = wr.effects i := hbe
        rcases raw.closed_rename_reverse hraw ρg ηg ρd ηd
            hsafe bg vd with
          ⟨vdB, hdBT, hdBE, hinputAlign, houtputAlign⟩
        have hprojD := hproj vd hC
        rcases (Constraint.close_project_holds_iff
          (raw.alphaRename ρd ηd).typeVars
          (raw.alphaRename ρd ηd).effectVars
          localTd localEd
          (.and D (.and (.typeEq τo aD)
            (.effectLe εo χd))) vd).mp hprojD
          vdB.types vdB.effects hdBT hdBE with
          ⟨lt, le, hlocalDT, hlocalDE, hDall⟩
        let vdL : Valuation := ⟨lt, le⟩
        have hD : D.holds vdL := hDall.1
        have hτclause : τo.eval vdL = aD.eval vdL := hDall.2.1
        have hεclause : εo.eval vdL.effects ⊆
            χd.eval vdL.effects := hDall.2.2
        have hbgBelowT : ∀ i, i < s.types →
            vg.types i = bg.types i := by
          intro i hi
          have hnot : i ∉ declg.typeVars := by
            intro hm
            have hu : i ∈ declg.usedTypes :=
              Finset.mem_union_left _
                (Finset.mem_union_left _ hm)
            have hgt := (hinterval.1 i hu).1
            omega
          exact (hbFixT i hi).trans
            ((hbelowBWTypes i (by omega)).trans
              (hbgT i hnot).symm)
        have hbgBelowE : ∀ i, i < s.effects →
            vg.effects i = bg.effects i := by
          intro i hi
          have hnot : i ∉ declg.effectVars := by
            intro hm
            have hu : i ∈ declg.usedEffects :=
              Finset.mem_union_left _
                (Finset.mem_union_left _ hm)
            have hgt := (hinterval.2 i hu).1
            omega
          exact (hbFixE i hi).trans
            ((hbelowBWEffects i (by omega)).trans
              (hbgE i hnot).symm)
        have hctxBG : Γg.MoreGeneralAt Γ bg vd :=
          Context.moreGeneralAt_below hSupport Γg Γ
            ops s hb vg bg vd hctx hbgBelowT hbgBelowE
        have hstableDT : ∀ i ∈ Γ.fvTypes ∪ aD.fvTypes,
            vd.types i = vdL.types i := by
          intro i hi
          have hnB : i ∉ (raw.alphaRename ρd ηd).typeVars := by
            intro hmem
            have hm : i ∈ (raw.alphaRename ρd ηd).typeVars ∩
                (Γ.fvTypes ∪ τin.fvTypes ∪ aD.fvTypes) := by
              apply Finset.mem_inter.mpr
              constructor
              · exact hmem
              · rcases Finset.mem_union.mp hi with hΓ | ha
                · simp [hΓ]
                · simp [ha]
            rw [hscope.1] at hm
            simp at hm
          have hnL : i ∉ localTd := by
            intro hmem
            have hm : i ∈ localTd ∩
                (Γ.fvTypes ∪ C.fvTypes ∪ τin.fvTypes ∪
                  aD.fvTypes ∪
                  (raw.alphaRename ρd ηd).typeVars ∪
                  (raw.alphaRename ρd ηd).input.fvTypes ∪
                  (raw.alphaRename ρd ηd).output.fvTypes) := by
              apply Finset.mem_inter.mpr
              constructor
              · exact hmem
              · rcases Finset.mem_union.mp hi with hΓ | ha
                · simp [hΓ]
                · simp [ha]
            rw [hclscope.2.2.1] at hm
            simp at hm
          exact (hdBT i hnB).symm.trans
            (hlocalDT i hnL).symm
        have hstableDE :
            ∀ i ∈ Γ.fvEffects ∪ aD.fvEffects ∪ χd.vars,
              vd.effects i = vdL.effects i := by
          intro i hi
          have hnB : i ∉ (raw.alphaRename ρd ηd).effectVars := by
            intro hmem
            have hm : i ∈ (raw.alphaRename ρd ηd).effectVars ∩
                (Γ.fvEffects ∪ τin.fvEffects ∪ aD.fvEffects ∪
                  εin.vars ∪ εr.vars ∪ δd.vars ∪ χd.vars) := by
              apply Finset.mem_inter.mpr
              constructor
              · exact hmem
              · rcases Finset.mem_union.mp hi with hΓa | hχ
                · rcases Finset.mem_union.mp hΓa with hΓ | ha
                  · simp [hΓ]
                  · simp [ha]
                · simp [hχ]
            rw [hscope.2] at hm
            simp at hm
          have hnL : i ∉ localEd := by
            intro hmem
            have hm : i ∈ localEd ∩
                (Γ.fvEffects ∪ C.fvEffects ∪ τin.fvEffects ∪
                  aD.fvEffects ∪ εin.vars ∪ εr.vars ∪
                  δd.vars ∪ χd.vars ∪
                  (raw.alphaRename ρd ηd).effectVars ∪
                  (raw.alphaRename ρd ηd).input.fvEffects ∪
                  (raw.alphaRename ρd ηd).output.fvEffects) := by
              apply Finset.mem_inter.mpr
              constructor
              · exact hmem
              · rcases Finset.mem_union.mp hi with hΓa | hχ
                · rcases Finset.mem_union.mp hΓa with hΓ | ha
                  · simp [hΓ]
                  · simp [ha]
                · simp [hχ]
            rw [hclscope.2.2.2] at hm
            simp at hm
          exact (hdBE i hnB).symm.trans
            (hlocalDE i hnL).symm
        have hctxD : Γg.MoreGeneralAt Γ bg vdL := by
          apply Context.moreGeneralAt_support hSupport
            Γg Γ bg bg vd vdL hctxBG
          · intro σ hσ i hi; rfl
          · intro σ hσ i hi; rfl
          · intro σ hσ i hi
            exact hstableDT i (Finset.mem_union_left _
              (Context.fvTypes_of_mem Γ σ hσ i hi))
          · intro σ hσ i hi
            exact hstableDE i (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Context.fvEffects_of_mem Γ σ hσ i hi)))
        have hlocalOpT : ∀ i ∈
            (raw.alphaRename ρd ηd).input.fvTypes ∪
              (raw.alphaRename ρd ηd).output.fvTypes,
            vdB.types i = vdL.types i := by
          intro i hi
          apply (hlocalDT i ?_).symm
          intro hmem
          have hm : i ∈ localTd ∩
              (Γ.fvTypes ∪ C.fvTypes ∪ τin.fvTypes ∪
                aD.fvTypes ∪
                (raw.alphaRename ρd ηd).typeVars ∪
                (raw.alphaRename ρd ηd).input.fvTypes ∪
                (raw.alphaRename ρd ηd).output.fvTypes) := by
            apply Finset.mem_inter.mpr
            constructor
            · exact hmem
            · rcases Finset.mem_union.mp hi with hin | hout
              · simp [hin]
              · simp [hout]
          rw [hclscope.2.2.1] at hm
          simp at hm
        have hlocalOpE : ∀ i ∈
            (raw.alphaRename ρd ηd).input.fvEffects ∪
              (raw.alphaRename ρd ηd).output.fvEffects,
            vdB.effects i = vdL.effects i := by
          intro i hi
          apply (hlocalDE i ?_).symm
          intro hmem
          have hm : i ∈ localEd ∩
              (Γ.fvEffects ∪ C.fvEffects ∪ τin.fvEffects ∪
                aD.fvEffects ∪ εin.vars ∪ εr.vars ∪
                δd.vars ∪ χd.vars ∪
                (raw.alphaRename ρd ηd).effectVars ∪
                (raw.alphaRename ρd ηd).input.fvEffects ∪
                (raw.alphaRename ρd ηd).output.fvEffects) := by
            apply Finset.mem_inter.mpr
            constructor
            · exact hmem
            · rcases Finset.mem_union.mp hi with hin | hout
              · simp [hin]
              · simp [hout]
          rw [hclscope.2.2.2] at hm
          simp at hm
        have hinputLocal :
            (raw.alphaRename ρd ηd).input.eval vdB =
              (raw.alphaRename ρd ηd).input.eval vdL := by
          apply Ty.eval_support
          · intro i hi
            exact hlocalOpT i (Finset.mem_union_left _ hi)
          · intro i hi
            exact hlocalOpE i (Finset.mem_union_left _ hi)
        have houtputLocal :
            (raw.alphaRename ρd ηd).output.eval vdB =
              (raw.alphaRename ρd ηd).output.eval vdL := by
          apply Ty.eval_support
          · intro i hi
            exact hlocalOpT i (Finset.mem_union_right _ hi)
          · intro i hi
            exact hlocalOpE i (Finset.mem_union_right _ hi)
        have haDStable : aD.eval vd = aD.eval vdL := by
          apply Ty.eval_support
          · intro i hi
            exact hstableDT i (Finset.mem_union_right _ hi)
          · intro i hi
            exact hstableDE i (Finset.mem_union_left _
              (Finset.mem_union_right _ hi))
        have hχDStable : χd.eval vd.effects =
            χd.eval vdL.effects := by
          apply Effect.eval_support
          intro i hi
          exact hstableDE i (Finset.mem_union_right _ hi)
        have haBG : aG.eval bg = aD.eval vdL := by
          have hnot : sb.types ∉ declg.typeVars := by
            intro hm
            have hu : sb.types ∈ declg.usedTypes :=
              Finset.mem_union_left _
                (Finset.mem_union_left _ hm)
            have hh := (hinterval.1 _ hu).2
            dsimp [sb] at hh
            omega
          have hfix := hbgT sb.types hnot
          simp [aG, Ty.eval]
          exact hfix.trans (haWr.trans haDStable)
        have hχBG : χg.eval bg.effects =
            χd.eval vdL.effects := by
          have hnot : sb.effects + 1 ∉ declg.effectVars := by
            intro hm
            have hu : sb.effects + 1 ∈ declg.usedEffects :=
              Finset.mem_union_left _
                (Finset.mem_union_left _ hm)
            have hh := (hinterval.2 _ hu).2
            dsimp [sb] at hh
            omega
          have hfix := hbgE (sb.effects + 1) hnot
          have hvar : χg.eval bg.effects = χg.eval wr.effects := by
            simpa [χg, Poly.Effect.eval, Poly.Effect.var] using hfix
          exact hvar.trans (hχWr.trans hχDStable)
        have hinputEq : declg.input.eval bg =
            (raw.alphaRename ρd ηd).input.eval vdL :=
          hinputAlign.trans hinputLocal
        have houtputEq : declg.output.eval bg =
            (raw.alphaRename ρd ηd).output.eval vdL :=
          houtputAlign.trans houtputLocal
        have hkEq : (Ty.arr declg.output χg aG).eval bg =
            (Ty.arr (raw.alphaRename ρd ηd).output χd aD).eval vdL := by
          simp [Ty.eval, houtputEq, hχBG, haBG]
        have hctxClause : Context.MoreGeneralAt
            (Scheme.mono (.arr declg.output χg aG) ::
              Scheme.mono declg.input :: Γg)
            (Scheme.mono (.arr (raw.alphaRename ρd ηd).output χd aD) ::
              Scheme.mono (raw.alphaRename ρd ηd).input :: Γ)
            bg vdL := by
          apply List.Forall₂.cons
          · exact (Scheme.mono_moreGeneralAt_iff _ _ bg vdL).mpr hkEq
          · apply List.Forall₂.cons
            · exact (Scheme.mono_moreGeneralAt_iff _ _ bg vdL).mpr
                hinputEq
            · exact hctxD
        have haBelowT : ∀ i ∈ aG.fvTypes,
            i < rr.next.types := by
          intro i hi
          simp [aG, Ty.fvTypes] at hi
          subst i
          change (rb.next.advance raw.typeVars raw.effectVars).types <
            rr.next.types
          dsimp [sr, sb] at hmR
          omega
        have haBelowE : ∀ i ∈ aG.fvEffects,
            i < rr.next.effects := by
          intro i hi
          simp [aG, Ty.fvEffects] at hi
        have hχBelow : ∀ i ∈ χg.vars,
            i < rr.next.effects := by
          intro i hi
          simp [χg, Poly.Effect.var, sb] at hi
          dsimp [sr, sb] at hmR
          omega
        have htarget : τo.eval vdL = aG.eval bg :=
          hτclause.trans haBG.symm
        have heffect : εo.eval vdL.effects ⊆
            χg.eval bg.effects := by
          rw [hχBG]
          exact hεclause
        have hprojectG := Output.CoversAt.project_clause
          hSupport
          (Scheme.mono (.arr declg.output χg aG) ::
            Scheme.mono declg.input :: Γg)
          (Scheme.mono (.arr (raw.alphaRename ρd ηd).output χd aD) ::
            Scheme.mono (raw.alphaRename ρd ηd).input :: Γ)
          D rr.next rc τo aG εo χg
          hcBound.1 hcBound.2 haBelowT haBelowE hχBelow
          hcovC bg vdL hctxClause hD htarget heffect
        exact (Constraint.project_holds_iff localT localE
          (.and rc.constraints
            (.and (.typeEq rc.ty aG)
              (.effectLe rc.effect χg))) bg).mp hprojectG
      refine ⟨wr, ?_, ?_, ?_, haWr, hχWr⟩
      · intro i hi
        exact (hbFixT i hi).trans
          (hbelowBWTypes i (by omega))
      · intro i hi
        exact (hbFixE i hi).trans
          (hbelowBWEffects i (by omega))
      · change (rb.constraints.holds wr ∧ rr.constraints.holds wr) ∧
          (Constraint.typeEq (X := X) rr.ty aG).holds wr ∧
          (Constraint.close declg.typeVars declg.effectVars
            (Constraint.project localT localE
              (.and rc.constraints
                (.and (.typeEq rc.ty aG)
                  (.effectLe rc.effect χg))))).holds wr ∧
          (Constraint.split (X := X) op rb.effect δg).holds wr ∧
          (Constraint.effectLe (X := X) δg χg).holds wr ∧
          (Constraint.effectLe (X := X) rr.effect χg).holds wr
        exact ⟨⟨hframeBW.1.mp hbC, hrC⟩,
          hτG, hprojG, hsplitG, hδG, hεG⟩
  | conv _ hEq ih =>
      intro Γg ops s hlen hops hb
      rcases ih Γg ops s hlen hops hb with
        ⟨r, hr, hcov⟩
      exact ⟨r, hr, Output.CoversAt.conv Γg _ _ s r _ _ _
        hcov hEq⟩
  | weaken _ hEnt ih =>
      intro Γg ops s hlen hops hb
      rcases ih Γg ops s hlen hops hb with
        ⟨r, hr, hcov⟩
      exact ⟨r, hr, Output.CoversAt.weaken Γg _ _ _ s r _ _
        hcov hEnt⟩


end SystemFXi.EHMX

namespace SystemFXi.EHMX

/-- For every declaratively typable expression, including handlers, the
generated qualified type is sound and every other declarative typing is its
semantic instance. -/
theorem Typing.generateFresh_principal
    {sig : Signature} {X : Domain}
    (hRename : LawfulRename X)
    (hSupport : LawfulSupport X)
    (hFVRename : LawfulFVRename X)
    (hClosed : sig.Closed)
    (Γ : Context X) (e : Expr) (s : Supply)
    {C₀ : Constraint X} {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀) :
    ∃ r : Output X,
      generateFresh sig X Γ e s = some r ∧
      Typing sig X r.constraints Γ e r.ty r.effect ∧
      ∀ (C : Constraint X) (τ : Ty) (ε : Effect),
        Typing sig X C Γ e τ ε →
        ∀ vd : Valuation, C.holds vd →
          ∃ wg : Valuation,
            r.constraints.holds wg ∧
            r.ty.eval wg = τ.eval vd ∧
            r.effect.eval wg.effects = ε.eval vd.effects := by
  let seed := s.seed sig Γ e []
  obtain ⟨r, hr, _⟩ :=
    h₀.generate_complete hRename hSupport
      hFVRename hClosed Γ e.ops seed
      rfl (Finset.Subset.rfl) (BoundedInputs.seed Γ e s)
  refine ⟨r, ?_, ?_, ?_⟩
  · exact hr
  · exact (generate_sound hr).sound
  · intro C' τ' ε' h' vd hC'
    obtain ⟨r', hr', hcov⟩ :=
      h'.generate_complete hRename hSupport
        hFVRename hClosed Γ e.ops seed
        rfl (Finset.Subset.rfl) (BoundedInputs.seed Γ e s)
    rw [hr] at hr'
    cases hr'
    rcases hcov vd vd (Context.moreGeneralAt_refl Γ vd) hC' with
      ⟨wg, _, _, hCg, hTy, hEff⟩
    exact ⟨wg, hCg, hTy, hEff⟩

end SystemFXi.EHMX
