import SystemFXi.EHMX.Algorithm

namespace SystemFXi.EHMX

private theorem eval_closed (ρ : Nat → Finset Op) (ε : Effect)
    (h : ε.vars = ∅) : ε.eval ρ = ε.labels := by
  simp [Poly.Effect.eval, h]

def Ty.occursBad : Ty → Ty → Bool
  | .var i, t => decide (i ∈ t.fvTypes)
  | t, .var i => decide (i ∈ t.fvTypes)
  | _, _ => false

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

end SystemFXi.EHMX
