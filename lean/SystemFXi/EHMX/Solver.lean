import SystemFXi.EHMX.Algorithm

namespace SystemFXi.EHMX

def GroundTy.height : GroundTy → Nat
  | .atom _ => 0
  | .arr a _ b => max a.height b.height + 1

theorem Ty.eval_height_le_of_mem (τ : Ty) (i : Nat) (ρ : Valuation)
    (h : i ∈ τ.fvTypes) :
    (ρ.types i).height ≤ (τ.eval ρ).height := by
  induction τ with
  | var j =>
      simp [Ty.fvTypes] at h
      subst j
      simp [Ty.eval]
  | base b => simp [Ty.fvTypes] at h
  | arr a ε b iha ihb =>
      simp only [Ty.fvTypes, Finset.mem_union] at h
      rcases h with ha | hb
      · calc
          (ρ.types i).height ≤ (a.eval ρ).height := iha ha
          _ ≤ max (a.eval ρ).height (b.eval ρ).height := Nat.le_max_left _ _
          _ ≤ ((Ty.arr a ε b).eval ρ).height := by
            change max (a.eval ρ).height (b.eval ρ).height ≤
              max (a.eval ρ).height (b.eval ρ).height + 1
            omega
      · calc
          (ρ.types i).height ≤ (b.eval ρ).height := ihb hb
          _ ≤ max (a.eval ρ).height (b.eval ρ).height := Nat.le_max_right _ _
          _ ≤ ((Ty.arr a ε b).eval ρ).height := by
            change max (a.eval ρ).height (b.eval ρ).height ≤
              max (a.eval ρ).height (b.eval ρ).height + 1
            omega

theorem Ty.eval_height_lt_of_mem_arr (a b : Ty) (ε : Effect)
    (i : Nat) (ρ : Valuation) (h : i ∈ (Ty.arr a ε b).fvTypes) :
    (ρ.types i).height < ((Ty.arr a ε b).eval ρ).height := by
  simp only [Ty.fvTypes, Finset.mem_union] at h
  rcases h with ha | hb
  · exact lt_of_le_of_lt (Ty.eval_height_le_of_mem a i ρ ha)
      (by simp [Ty.eval, GroundTy.height, Nat.lt_succ_of_le (Nat.le_max_left _ _)])
  · exact lt_of_le_of_lt (Ty.eval_height_le_of_mem b i ρ hb)
      (by simp [Ty.eval, GroundTy.height, Nat.lt_succ_of_le (Nat.le_max_right _ _)])

private theorem eval_closed (ρ : Nat → Finset Op) (ε : Effect)
    (h : ε.vars = ∅) : ε.eval ρ = ε.labels := by
  simp [Poly.Effect.eval, h]

def Ty.occursBad : Ty → Ty → Bool
  | .var i, t => decide (i ∈ t.fvTypes)
  | t, .var i => decide (i ∈ t.fvTypes)
  | _, _ => false

theorem Ty.occursBad_eq_unsat (a b : Ty) (ρ : Valuation)
    (hne : a ≠ b) (hbad : a.occursBad b = true) :
    a.eval ρ ≠ b.eval ρ := by
  cases a with
  | var i =>
      cases b with
      | var j =>
          simp [Ty.occursBad, Ty.fvTypes] at hbad
          subst j
          exact False.elim (hne rfl)
      | base _ => simp [Ty.occursBad, Ty.fvTypes] at hbad
      | arr x ε y =>
          have hmem : i ∈ (Ty.arr x ε y).fvTypes := by
            simpa [Ty.occursBad] using hbad
          intro heq
          have hh := congrArg GroundTy.height heq
          have hlt := Ty.eval_height_lt_of_mem_arr x y ε i ρ hmem
          exact Nat.lt_irrefl _ (hh ▸ hlt)
  | base _ =>
      cases b with
      | var _ => simp [Ty.occursBad, Ty.fvTypes] at hbad
      | base _ => simp [Ty.occursBad] at hbad
      | arr _ _ _ => simp [Ty.occursBad] at hbad
  | arr x ε y =>
      cases b with
      | var i =>
          have hmem : i ∈ (Ty.arr x ε y).fvTypes := by
            simpa [Ty.occursBad] using hbad
          intro heq
          have hh := congrArg GroundTy.height heq
          have hlt := Ty.eval_height_lt_of_mem_arr x y ε i ρ hmem
          exact Nat.lt_irrefl _ (hh.symm ▸ hlt)
      | base _ => simp [Ty.occursBad] at hbad
      | arr _ _ _ => simp [Ty.occursBad] at hbad

/-- One sound pass of type-shape decomposition and closed-effect checking.
Symbolic equalities and effects remain as qualified constraints. -/
def simplifyAtom {X : Domain} : Constraint X → Option (Constraint X)
  | .typeEq (.arr a ε b) (.arr a' ε' b') =>
      some (.and (.typeEq a a')
        (.and (.typeEq b b')
          (.and (.effectLe ε ε') (.effectLe ε' ε))))
  | .typeEq (.base a) (.base b) =>
      if a = b then some .top else none
  | .typeEq (.base _) (.arr _ _ _) => none
  | .typeEq (.arr _ _ _) (.base _) => none
  | .typeEq a b =>
      if a = b then some .top
      else if a.occursBad b then none
      else some (.typeEq a b)
  | .effectLe ε η =>
      if _hε : ε.vars = ∅ then
        if _hη : η.vars = ∅ then
          if ε.labels ⊆ η.labels then some .top else none
        else some (.effectLe ε η)
      else some (.effectLe ε η)
  | .lacks op ε =>
      if _hε : ε.vars = ∅ then
        if op ∉ ε.labels then some .top else none
      else some (.lacks op ε)
  | c => some c

def simplify {X : Domain} : Constraint X → Option (Constraint X)
  | .and c d => do
      let c' ← simplify c
      let d' ← simplify d
      some (.and c' d')
  | c => simplifyAtom c

/-- The undecided type equality is retained; equal types become `top`. -/
private theorem simplify_typeEq_undecided_sound {X : Domain} (a b : Ty)
    {r : Constraint X}
    (h : (if a = b then some Constraint.top
      else if a.occursBad b then none else some (.typeEq a b)) = some r) :
    r.Entails (.typeEq a b) := by
  by_cases heq : a = b
  · simp [heq] at h
    cases h
    intro ρ _
    simp [Constraint.holds, heq]
  · by_cases hbad : a.occursBad b = true
    · simp [heq, hbad] at h
    · simp [heq, hbad] at h
      cases h
      exact Constraint.entails_refl _

private theorem simplify_typeEq_undecided_complete {X : Domain} (a b : Ty)
    {r : Constraint X}
    (h : (if a = b then some Constraint.top
      else if a.occursBad b then none else some (.typeEq a b)) = some r) :
    (Constraint.typeEq a b).Entails r := by
  by_cases heq : a = b
  · simp [heq] at h
    cases h
    intro ρ _
    trivial
  · by_cases hbad : a.occursBad b = true
    · simp [heq, hbad] at h
    · simp [heq, hbad] at h
      cases h
      exact Constraint.entails_refl _

private theorem simplify_typeEq_undecided_none_unsat {X : Domain} (a b : Ty)
    (h : (if a = b then some Constraint.top
      else if a.occursBad b then none else some (.typeEq a b : Constraint X)) = none)
    (ρ : Valuation) : a.eval ρ ≠ b.eval ρ := by
  by_cases heq : a = b
  · simp [heq] at h
  · by_cases hbad : a.occursBad b = true
    · exact Ty.occursBad_eq_unsat a b ρ heq hbad
    · simp [heq, hbad] at h

/-- Every atom rejected by the simplifier has no valuation. -/
theorem simplifyAtom_none_unsat {X : Domain} {c : Constraint X}
    (h : simplifyAtom c = none) (ρ : Valuation) : ¬ c.holds ρ := by
  cases c with
  | top => simp [simplifyAtom] at h
  | and _ _ => simp [simplifyAtom] at h
  | typeEq a b =>
      cases a with
      | var i =>
          cases b <;> exact simplify_typeEq_undecided_none_unsat (X := X) _ _
            (by simpa [simplifyAtom] using h) ρ
      | base u =>
          cases b with
          | var i =>
              exact simplify_typeEq_undecided_none_unsat (X := X) _ _
                (by simpa [simplifyAtom] using h) ρ
          | base v =>
              cases u <;> cases v <;>
                simp [simplifyAtom, Constraint.holds, Ty.eval] at h ⊢
          | arr _ _ _ =>
              intro hh
              cases u <;> cases hh
      | arr a ε out =>
          cases b with
          | var i =>
              exact simplify_typeEq_undecided_none_unsat (X := X) _ _
                (by simpa [simplifyAtom] using h) ρ
          | base u =>
              intro hh
              cases u <;> cases hh
          | arr _ _ _ => simp [simplifyAtom] at h
  | effectLe ε η =>
      by_cases hε : ε.vars = ∅
      · by_cases hη : η.vars = ∅
        · by_cases hsub : ε.labels ⊆ η.labels
          · simp [simplifyAtom, hε, hη, hsub] at h
          · intro hh
            apply hsub
            simpa [Constraint.holds, eval_closed ρ.effects ε hε,
              eval_closed ρ.effects η hη] using hh
        · simp [simplifyAtom, hε, hη] at h
      · simp [simplifyAtom, hε] at h
  | lacks op ε =>
      by_cases hε : ε.vars = ∅
      · by_cases hnot : op ∉ ε.labels
        · simp [simplifyAtom, hε, hnot] at h
        · intro hh
          apply hnot
          simpa [Constraint.holds, eval_closed ρ.effects ε hε] using hh
      · simp [simplifyAtom, hε] at h
  | predicate _ => simp [simplifyAtom] at h
  | allTy _ _ => simp [simplifyAtom] at h
  | allEff _ _ => simp [simplifyAtom] at h
  | exTy _ _ => simp [simplifyAtom] at h
  | exEff _ _ => simp [simplifyAtom] at h

theorem simplifyAtom_sound {X : Domain} {c r : Constraint X}
    (h : simplifyAtom c = some r) : r.Entails c := by
  cases c with
  | top => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | and c d => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | typeEq a b =>
      cases a with
      | var i =>
          cases b <;> exact simplify_typeEq_undecided_sound _ _ (by simpa [simplifyAtom] using h)
      | base u =>
          cases b with
          | var i =>
              exact simplify_typeEq_undecided_sound _ _ (by simpa [simplifyAtom] using h)
          | base v =>
              by_cases huv : u = v
              · simp [simplifyAtom, huv] at h
                cases h
                intro ρ _
                simp [Constraint.holds, huv]
              · simp [simplifyAtom, huv] at h
          | arr a ε b => simp [simplifyAtom] at h
      | arr a ε out =>
          cases b with
          | var i =>
              exact simplify_typeEq_undecided_sound _ _ (by simpa [simplifyAtom] using h)
          | base u => simp [simplifyAtom] at h
          | arr a' ε' b' =>
              simp [simplifyAtom] at h
              cases h
              intro ρ hh
              rcases hh with ⟨ha, hb, hεε', hε'ε⟩
              simp only [Constraint.holds] at *
              have heff := Finset.Subset.antisymm hεε' hε'ε
              simp only [Ty.eval]
              congr 1
  | effectLe ε η =>
      by_cases hε : ε.vars = ∅
      · by_cases hη : η.vars = ∅
        · by_cases hsub : ε.labels ⊆ η.labels
          · simp [simplifyAtom, hε, hη, hsub] at h
            cases h
            intro ρ _
            simpa [Constraint.holds, eval_closed ρ.effects ε hε,
              eval_closed ρ.effects η hη] using hsub
          · simp [simplifyAtom, hε, hη, hsub] at h
        · simp [simplifyAtom, hε, hη] at h
          cases h
          exact Constraint.entails_refl _
      · simp [simplifyAtom, hε] at h
        cases h
        exact Constraint.entails_refl _
  | lacks op ε =>
      by_cases hε : ε.vars = ∅
      · by_cases hnot : op ∉ ε.labels
        · simp [simplifyAtom, hε, hnot] at h
          cases h
          intro ρ _
          simpa [Constraint.holds, eval_closed ρ.effects ε hε] using hnot
        · simp [simplifyAtom, hε, hnot] at h
      · simp [simplifyAtom, hε] at h
        cases h
        exact Constraint.entails_refl _
  | predicate p => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | allTy i c => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | allEff i c => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | exTy i c => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | exEff i c => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _

theorem simplify_sound {X : Domain} {c r : Constraint X}
    (h : simplify c = some r) : r.Entails c := by
  induction c generalizing r with
  | and c d ihc ihd =>
      cases hc : simplify c with
      | none => simp [simplify, hc] at h
      | some c' =>
          cases hd : simplify d with
          | none => simp [simplify, hc, hd] at h
          | some d' =>
              simp [simplify, hc, hd] at h
              cases h
              intro ρ hh
              exact ⟨ihc hc ρ hh.1, ihd hd ρ hh.2⟩
  | _ => exact simplifyAtom_sound h

/-- Every successful simplification preserves the full set of valuations. -/
theorem simplifyAtom_complete {X : Domain} {c r : Constraint X}
    (h : simplifyAtom c = some r) : c.Entails r := by
  cases c with
  | top => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | and c d => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | typeEq a b =>
      cases a with
      | var i =>
          cases b <;> exact simplify_typeEq_undecided_complete _ _
            (by simpa only [simplifyAtom] using h)
      | base u =>
          cases b with
          | var i =>
              exact simplify_typeEq_undecided_complete _ _
                (by simpa only [simplifyAtom] using h)
          | base v =>
              by_cases huv : u = v
              · simp [simplifyAtom, huv] at h
                cases h
                intro ρ _
                trivial
              · simp [simplifyAtom, huv] at h
          | arr a ε b => simp [simplifyAtom] at h
      | arr a ε out =>
          cases b with
          | var i =>
              exact simplify_typeEq_undecided_complete _ _
                (by simpa only [simplifyAtom] using h)
          | base u => simp [simplifyAtom] at h
          | arr a' ε' b' =>
              simp [simplifyAtom] at h
              cases h
              intro ρ hh
              simp only [Constraint.holds] at *
              have ha : a.eval ρ = a'.eval ρ := (GroundTy.arr.inj hh).1
              have he : ε.eval ρ.effects = ε'.eval ρ.effects :=
                (GroundTy.arr.inj hh).2.1
              have hb : out.eval ρ = b'.eval ρ := (GroundTy.arr.inj hh).2.2
              exact ⟨ha, hb, he.subset, he.symm.subset⟩
  | effectLe ε η =>
      by_cases hε : ε.vars = ∅
      · by_cases hη : η.vars = ∅
        · by_cases hsub : ε.labels ⊆ η.labels
          · simp [simplifyAtom, hε, hη, hsub] at h
            cases h
            intro ρ _
            trivial
          · simp [simplifyAtom, hε, hη, hsub] at h
        · simp [simplifyAtom, hε, hη] at h
          cases h
          exact Constraint.entails_refl _
      · simp [simplifyAtom, hε] at h
        cases h
        exact Constraint.entails_refl _
  | lacks op ε =>
      by_cases hε : ε.vars = ∅
      · by_cases hnot : op ∉ ε.labels
        · simp [simplifyAtom, hε, hnot] at h
          cases h
          intro ρ _
          trivial
        · simp [simplifyAtom, hε, hnot] at h
      · simp [simplifyAtom, hε] at h
        cases h
        exact Constraint.entails_refl _
  | predicate p => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | allTy i c => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | allEff i c => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | exTy i c => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _
  | exEff i c => simp [simplifyAtom] at h; cases h; exact Constraint.entails_refl _

theorem simplify_complete {X : Domain} {c r : Constraint X}
    (h : simplify c = some r) : c.Entails r := by
  induction c generalizing r with
  | and c d ihc ihd =>
      cases hc : simplify c with
      | none => simp [simplify, hc] at h
      | some c' =>
          cases hd : simplify d with
          | none => simp [simplify, hc, hd] at h
          | some d' =>
              simp [simplify, hc, hd] at h
              cases h
              intro ρ hh
              exact ⟨ihc hc ρ hh.1, ihd hd ρ hh.2⟩
  | _ => exact simplifyAtom_complete h

/-- A failed pass cannot discard a satisfiable constraint. -/
theorem simplify_none_unsat {X : Domain} {c : Constraint X}
    (h : simplify c = none) (ρ : Valuation) : ¬ c.holds ρ := by
  induction c with
  | and c d ihc ihd =>
      cases hc : simplify c with
      | none =>
          intro hh
          exact ihc hc hh.1
      | some c' =>
          cases hd : simplify d with
          | none =>
              intro hh
              exact ihd hd hh.2
          | some d' => simp [simplify, hc, hd] at h
  | _ => exact simplifyAtom_none_unsat (by simpa [simplify] using h) ρ

theorem simplify_equiv {X : Domain} {c r : Constraint X}
    (h : simplify c = some r) (ρ : Valuation) :
    c.holds ρ ↔ r.holds ρ :=
  ⟨simplify_complete h ρ, simplify_sound h ρ⟩

/-- An explicit contradictory constraint, used when simplification detects one. -/
def Constraint.unsat {X : Domain} : Constraint X :=
  .typeEq (.base .int) (.base .bool)

theorem Constraint.unsat_false {X : Domain} (ρ : Valuation) :
    ¬ (Constraint.unsat (X := X)).holds ρ := by
  simp [Constraint.unsat, Constraint.holds, Ty.eval]

/-- Normalization stays total even when a constraint has no solutions. -/
def simplifyTotal {X : Domain} (c : Constraint X) : Constraint X :=
  (simplify c).getD .unsat

theorem simplifyTotal_equiv {X : Domain} (c : Constraint X)
    (ρ : Valuation) : c.holds ρ ↔ (simplifyTotal c).holds ρ := by
  cases h : simplify c with
  | some r => simpa [simplifyTotal, h] using simplify_equiv h ρ
  | none =>
      simp only [simplifyTotal, h, Option.getD_none]
      exact ⟨fun hc => False.elim (simplify_none_unsat h ρ hc),
        fun hu => False.elim (Constraint.unsat_false ρ hu)⟩

/-- The concrete simplifier can be composed with executable generation. -/
def infer (sig : Signature) (X : Domain) (Γ : Context X)
    (e : Expr) (s : Supply) : Option (Output X) := do
  let r ← generate sig X Γ e s
  let C ← simplify r.constraints
  some {r with constraints := C}

theorem infer_sound {sig : Signature} {X : Domain} {Γ : Context X}
    {e : Expr} {s : Supply} {r : Output X}
    (h : infer sig X Γ e s = some r) :
    Typing sig X r.constraints Γ e r.ty r.effect := by
  unfold infer at h
  cases hg : generate sig X Γ e s with
  | none => simp [hg] at h
  | some g =>
      cases hs : simplify g.constraints with
      | none => simp [hg, hs] at h
      | some C =>
          simp [hg, hs] at h
          have htyped : Typing sig X C Γ e g.ty g.effect :=
            generate_residual_sound (r := g) hg (simplify_sound hs)
          cases h
          exact htyped

/-- A successful simplification changes neither the inferred type/effect nor
the solutions of its generated constraint. -/
theorem infer_preserves_solutions {sig : Signature} {X : Domain}
    {Γ : Context X} {e : Expr} {s : Supply} {r : Output X}
    (h : infer sig X Γ e s = some r) :
    ∃ g, generate sig X Γ e s = some g ∧
      r.ty = g.ty ∧ r.effect = g.effect ∧
      ∀ ρ, r.constraints.holds ρ ↔ g.constraints.holds ρ := by
  unfold infer at h
  cases hg : generate sig X Γ e s with
  | none => simp [hg] at h
  | some g =>
      cases hs : simplify g.constraints with
      | none => simp [hg, hs] at h
      | some R =>
          simp [hg, hs] at h
          cases h
          exact ⟨g, rfl, rfl, rfl,
            fun ρ => (simplify_equiv hs ρ).symm⟩

/-- An X solver may discharge only predicates explicitly supplied as assumptions.
The remaining predicates stay in the qualified constraint. -/
def assumptions {X : Domain} : List X.Pred → Constraint X
  | [] => .top
  | p :: ps => .and (.predicate p) (assumptions ps)

def resolveX {X : Domain} [DecidableEq X.Pred]
    (A : List X.Pred) : Constraint X → Constraint X
  | .and c d => .and (resolveX A c) (resolveX A d)
  | .predicate p => if p ∈ A then .top else .predicate p
  | c => c

theorem assumptions_mem {X : Domain} (A : List X.Pred)
    (ρ : Valuation) {p : X.Pred} (hA : (assumptions A).holds ρ)
    (hp : p ∈ A) : X.holds ρ p := by
  induction A with
  | nil => cases hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hA.1
      · exact ih hA.2 hp

theorem resolveX_sound {X : Domain} [DecidableEq X.Pred]
    (A : List X.Pred) (c : Constraint X) :
    (Constraint.and (assumptions A) (resolveX A c)).Entails c := by
  induction c with
  | and c d ihc ihd =>
      intro ρ h
      exact ⟨ihc ρ ⟨h.1, h.2.1⟩, ihd ρ ⟨h.1, h.2.2⟩⟩
  | predicate p =>
      intro ρ h
      by_cases hp : p ∈ A
      · exact assumptions_mem A ρ h.1 hp
      · simpa [resolveX, hp, Constraint.holds] using h.2
  | _ =>
      intro ρ h
      exact h.2

theorem resolveX_complete {X : Domain} [DecidableEq X.Pred]
    (A : List X.Pred) (c : Constraint X) :
    (Constraint.and (assumptions A) c).Entails
      (.and (assumptions A) (resolveX A c)) := by
  induction c with
  | and c d ihc ihd =>
      intro ρ h
      exact ⟨h.1, ⟨(ihc ρ ⟨h.1, h.2.1⟩).2,
        (ihd ρ ⟨h.1, h.2.2⟩).2⟩⟩
  | predicate p =>
      intro ρ h
      by_cases hp : p ∈ A
      · simpa [resolveX, hp, Constraint.holds] using h.1
      · simpa [resolveX, hp, Constraint.holds] using h
  | _ =>
      intro ρ h
      exact h

theorem resolveX_equiv {X : Domain} [DecidableEq X.Pred]
    (A : List X.Pred) (c : Constraint X) :
    ∀ ρ, (Constraint.and (assumptions A) c).holds ρ ↔
      (Constraint.and (assumptions A) (resolveX A c)).holds ρ := by
  intro ρ
  exact ⟨resolveX_complete A c ρ,
    fun h => ⟨h.1, resolveX_sound A c ρ h⟩⟩

def inferQualified (sig : Signature) (X : Domain) [DecidableEq X.Pred]
    (A : List X.Pred) (Γ : Context X) (e : Expr) (s : Supply) :
    Option (Output X) := do
  let r ← infer sig X Γ e s
  some {r with constraints := .and (assumptions A) (resolveX A r.constraints)}

theorem inferQualified_sound {sig : Signature} {X : Domain}
    [DecidableEq X.Pred] {A : List X.Pred} {Γ : Context X}
    {e : Expr} {s : Supply} {r : Output X}
    (h : inferQualified sig X A Γ e s = some r) :
    Typing sig X r.constraints Γ e r.ty r.effect := by
  unfold inferQualified at h
  cases hi : infer sig X Γ e s with
  | none => simp [hi] at h
  | some q =>
      simp [hi] at h
      have htyped : Typing sig X
          (.and (assumptions A) (resolveX A q.constraints))
          Γ e q.ty q.effect :=
        Typing.weaken (infer_sound hi) (resolveX_sound A q.constraints)
      cases h
      exact htyped

/-- Under the explicit assumptions, predicate discharge preserves exactly
the generated solution set, including all symbolic effect choices. -/
theorem inferQualified_preserves_solutions {sig : Signature} {X : Domain}
    [DecidableEq X.Pred] {A : List X.Pred} {Γ : Context X}
    {e : Expr} {s : Supply} {r : Output X}
    (h : inferQualified sig X A Γ e s = some r) :
    ∃ g, generate sig X Γ e s = some g ∧
      r.ty = g.ty ∧ r.effect = g.effect ∧
      ∀ ρ, r.constraints.holds ρ ↔
        (Constraint.and (assumptions A) g.constraints).holds ρ := by
  unfold inferQualified at h
  cases hi : infer sig X Γ e s with
  | none => simp [hi] at h
  | some q =>
      simp [hi] at h
      cases h
      obtain ⟨g, hg, ht, he, hsol⟩ := infer_preserves_solutions hi
      refine ⟨g, hg, ht, he, ?_⟩
      intro ρ
      exact (resolveX_equiv A q.constraints ρ).symm.trans
        (and_congr_right (fun _ => hsol ρ))

/-- The proof-facing inference entry point keeps inconsistent residuals instead
of failing, and seeds fresh names above the input's existing names. -/
def inferQualifiedTotal (sig : Signature) (X : Domain)
    [DecidableEq X.Pred] (A : List X.Pred) (Γ : Context X)
    (e : Expr) (s : Supply) : Option (Output X) := do
  let g ← generate sig X Γ e (s.seed sig Γ e A)
  let C := simplifyTotal g.constraints
  some {g with constraints := .and (assumptions A) (resolveX A C)}

theorem inferQualifiedTotal_sound {sig : Signature} {X : Domain}
    [DecidableEq X.Pred] {A : List X.Pred} {Γ : Context X}
    {e : Expr} {s : Supply} {r : Output X}
    (h : inferQualifiedTotal sig X A Γ e s = some r) :
    Typing sig X r.constraints Γ e r.ty r.effect := by
  unfold inferQualifiedTotal at h
  cases hg : generate sig X Γ e (s.seed sig Γ e A) with
  | none => simp [hg] at h
  | some g =>
      simp [hg] at h
      cases h
      apply Typing.weaken (Generate.sound (generate_sound hg))
      intro ρ hr
      have hc : (simplifyTotal g.constraints).holds ρ :=
        resolveX_sound A (simplifyTotal g.constraints) ρ hr
      exact (simplifyTotal_equiv g.constraints ρ).mpr hc

theorem inferQualifiedTotal_preserves_solutions {sig : Signature}
    {X : Domain} [DecidableEq X.Pred]
    {A : List X.Pred} {Γ : Context X} {e : Expr}
    {s : Supply} {r : Output X}
    (h : inferQualifiedTotal sig X A Γ e s = some r) :
    ∃ g, generate sig X Γ e (s.seed sig Γ e A) = some g ∧
      r.ty = g.ty ∧ r.effect = g.effect ∧
      ∀ ρ, r.constraints.holds ρ ↔
        (Constraint.and (assumptions A) g.constraints).holds ρ := by
  unfold inferQualifiedTotal at h
  cases hg : generate sig X Γ e (s.seed sig Γ e A) with
  | none => simp [hg] at h
  | some g =>
      simp [hg] at h
      cases h
      refine ⟨g, rfl, rfl, rfl, ?_⟩
      intro ρ
      exact (resolveX_equiv A (simplifyTotal g.constraints) ρ).symm.trans
        (and_congr_right (fun _ => (simplifyTotal_equiv g.constraints ρ).symm))

end SystemFXi.EHMX
