import SystemFXi.EHMX.NormalForm

namespace SystemFXi.EHMX

/-- The concrete executable instance uses equations `α = t` with a closed,
effect-free right-hand side. -/
inductive ClosedPureTy where
  | int | bool
  | arr : ClosedPureTy → ClosedPureTy → ClosedPureTy
  deriving DecidableEq, Repr

def ClosedPureTy.toTy : ClosedPureTy → Ty
  | .int => .base .int
  | .bool => .base .bool
  | .arr a b => .arr a.toTy ∅ b.toTy

theorem ClosedPureTy.subst_fixed (t : ClosedPureTy)
    (θ : Substitution) : t.toTy.subst θ = t.toTy := by
  induction t with
  | int => rfl
  | bool => rfl
  | arr a b iha ihb =>
      have he : (∅ : Effect).subst θ.effects = ∅ := by
        simp [Effect.subst]
        rfl
      simp [ClosedPureTy.toTy, Ty.subst, iha, ihb, he]

theorem ClosedPureTy.toTy_injective :
    Function.Injective ClosedPureTy.toTy := by
  intro t u h
  induction t generalizing u with
  | int => cases u <;> simp [ClosedPureTy.toTy] at h ⊢
  | bool => cases u <;> simp [ClosedPureTy.toTy] at h ⊢
  | arr a b iha ihb =>
      cases u with
      | int => simp [ClosedPureTy.toTy] at h
      | bool => simp [ClosedPureTy.toTy] at h
      | arr c d =>
          simp [ClosedPureTy.toTy] at h
          exact congrArg₂ ClosedPureTy.arr (iha h.1) (ihb h.2)

structure PureEquation where
  name : Nat
  value : ClosedPureTy
  deriving DecidableEq, Repr

def PureEquation.Compatible (eqs : List PureEquation) : Prop :=
  ∀ b ∈ eqs, ∀ c ∈ eqs,
    b.name = c.name → b.value = c.value

def PureEquation.compatibleB (eqs : List PureEquation) : Bool :=
  eqs.all (fun b => eqs.all (fun c =>
    decide (b.name = c.name → b.value = c.value)))

theorem PureEquation.compatibleB_iff (eqs : List PureEquation) :
    PureEquation.compatibleB eqs = true ↔
      PureEquation.Compatible eqs := by
  simp [PureEquation.compatibleB, PureEquation.Compatible,
    List.all_eq_true]
  constructor
  · intro h b hb c hc hn
    exact (h b hb c hc).resolve_left (fun hne => hne hn)
  · intro h b hb c hc
    by_cases hn : b.name = c.name
    · exact Or.inr (h b hb c hc hn)
    · exact Or.inl hn

instance (eqs : List PureEquation) : Decidable (PureEquation.Compatible eqs) :=
  decidable_of_iff (PureEquation.compatibleB eqs = true)
    (PureEquation.compatibleB_iff eqs)

def PureEquation.lookup : List PureEquation → Nat → Option ClosedPureTy
  | [], _ => none
  | b :: bs, i =>
      if b.name = i then some b.value else lookup bs i

def PureEquation.subst (eqs : List PureEquation) : Substitution :=
  { types := fun i => match PureEquation.lookup eqs i with
      | some t => t.toTy
      | none => .var i
    effects := Poly.Effect.var }

def PureEquation.solves (eqs : List PureEquation)
    (θ : Substitution) : Prop :=
  ∀ b ∈ eqs, (Ty.var b.name).subst θ = b.value.toTy.subst θ

/-- The total executable normalizer for this finite equality fragment. -/
def PureEquation.unify (eqs : List PureEquation) : Option Substitution :=
  if PureEquation.Compatible eqs then some (PureEquation.subst eqs) else none

theorem PureEquation.solves_iff (eqs : List PureEquation)
    (θ : Substitution) :
    PureEquation.solves eqs θ ↔ ∀ b ∈ eqs, θ.types b.name = b.value.toTy := by
  simp [PureEquation.solves, Ty.subst, ClosedPureTy.subst_fixed]

theorem PureEquation.lookup_of_mem (eqs : List PureEquation)
    (h : PureEquation.Compatible eqs) (b : PureEquation) (hb : b ∈ eqs) :
    PureEquation.lookup eqs b.name = some b.value := by
  induction eqs with
  | nil => cases hb
  | cons a rest ih =>
      simp only [List.mem_cons] at hb
      by_cases hn : a.name = b.name
      · have hval : a.value = b.value := h a (by simp) b (by simp [hb]) hn
        simp [PureEquation.lookup, hn, hval]
      · rcases hb with rfl | hb
        · exact False.elim (hn rfl)
        · have hrest : PureEquation.Compatible rest := by
            intro c hc d hd hcd
            exact h c (by simp [hc]) d (by simp [hd]) hcd
          simpa [PureEquation.lookup, hn] using ih hrest hb

theorem PureEquation.lookup_some_mem (eqs : List PureEquation)
    (i : Nat) (t : ClosedPureTy)
    (h : PureEquation.lookup eqs i = some t) :
    ∃ b ∈ eqs, b.name = i ∧ b.value = t := by
  induction eqs with
  | nil => simp [PureEquation.lookup] at h
  | cons b bs ih =>
      by_cases hb : b.name = i
      · simp [PureEquation.lookup, hb] at h
        exact ⟨b, by simp, hb, h⟩
      · simp [PureEquation.lookup, hb] at h
        rcases ih h with ⟨c, hc, hci, hct⟩
        exact ⟨c, by simp [hc], hci, hct⟩

theorem PureEquation.unify_sound (eqs : List PureEquation)
    (θ : Substitution) (h : PureEquation.unify eqs = some θ) :
    PureEquation.solves eqs θ := by
  unfold PureEquation.unify at h
  split at h
  · cases h
    apply (PureEquation.solves_iff eqs (PureEquation.subst eqs)).mpr
    intro b hb
    simp [PureEquation.subst,
      PureEquation.lookup_of_mem eqs (by assumption) b hb]
  · simp at h

/-- Every other syntactic solution factors through the computed substitution.
This is the most-general-unifier property, not just equality of ground sets. -/
theorem PureEquation.unify_most_general (eqs : List PureEquation)
    (θ : Substitution) (h : PureEquation.unify eqs = some θ)
    (σ : Substitution) (hσ : PureEquation.solves eqs σ) :
    (∀ i, (θ.types i).subst σ = σ.types i) ∧
    (∀ i, (θ.effects i).subst σ.effects = σ.effects i) := by
  unfold PureEquation.unify at h
  split at h
  · cases h
    have hs := (PureEquation.solves_iff eqs σ).mp hσ
    constructor
    · intro i
      by_cases hl : ∃ t, PureEquation.lookup eqs i = some t
      · rcases hl with ⟨t, ht⟩
        rcases PureEquation.lookup_some_mem eqs i t ht with
          ⟨b, hb, hbi, hbt⟩
        change (match PureEquation.lookup eqs i with
          | some t => t.toTy
          | none => .var i).subst σ = σ.types i
        rw [ht]
        simp only [ClosedPureTy.subst_fixed]
        rw [← hbt, ← hbi]
        exact (hs b hb).symm
      · have hn : PureEquation.lookup eqs i = none := by
          cases hh : PureEquation.lookup eqs i with
          | none => rfl
          | some t => exact False.elim (hl ⟨t, hh⟩)
        simp [PureEquation.subst, hn, Ty.subst]
    · intro i
      simp [PureEquation.subst, Effect.subst,
        Poly.Effect.var]
  · simp at h

theorem PureEquation.unify_complete (eqs : List PureEquation)
    (σ : Substitution) (hσ : PureEquation.solves eqs σ) :
    PureEquation.unify eqs = some (PureEquation.subst eqs) := by
  have hc : PureEquation.Compatible eqs := by
    intro b hb c hc hname
    have hs := (PureEquation.solves_iff eqs σ).mp hσ
    have hbc : b.value.toTy = c.value.toTy := by
      calc
        b.value.toTy = σ.types b.name := (hs b hb).symm
        _ = σ.types c.name := by rw [hname]
        _ = c.value.toTy := hs c hc
    exact ClosedPureTy.toTy_injective hbc
  simp [PureEquation.unify, hc]

theorem PureEquation.unify_none_iff (eqs : List PureEquation) :
    PureEquation.unify eqs = none ↔
      ¬ ∃ σ, PureEquation.solves eqs σ := by
  constructor
  · intro h ⟨σ, hσ⟩
    rw [PureEquation.unify_complete eqs σ hσ] at h
    cases h
  · intro h
    by_cases hc : PureEquation.Compatible eqs
    · exact False.elim (h ⟨PureEquation.subst eqs,
        PureEquation.unify_sound eqs (PureEquation.subst eqs)
          (by simp [PureEquation.unify, hc])⟩)
    · simp [PureEquation.unify, hc]

def PureEquation.constraints (X : Domain) :
    List PureEquation → Constraint X
  | [] => .top
  | b :: bs => .and (.typeEq (.var b.name) b.value.toTy)
      (PureEquation.constraints X bs)

theorem PureEquation.constraints_holds_iff {X : Domain}
    (eqs : List PureEquation) (v : Valuation) :
    (PureEquation.constraints X eqs).holds v ↔
      ∀ b ∈ eqs, v.types b.name = b.value.toTy.eval v := by
  induction eqs with
  | nil => simp [PureEquation.constraints, Constraint.holds]
  | cons b bs ih =>
      simp [PureEquation.constraints, Constraint.holds, ih,
        Ty.eval, List.mem_cons]

theorem ClosedPureTy.eval_const (t : ClosedPureTy)
    (v w : Valuation) : t.toTy.eval v = t.toTy.eval w := by
  induction t with
  | int => rfl
  | bool => rfl
  | arr a b iha ihb =>
      simp [ClosedPureTy.toTy, Ty.eval, iha, ihb,
        Poly.Effect.eval]

def PureEquation.normalForm {X : Domain}
    (eqs : List PureEquation) : NormalForm X :=
  ⟨.top, PureEquation.subst eqs⟩

theorem PureEquation.normalForm_sound {X : Domain}
    (eqs : List PureEquation) (hc : PureEquation.Compatible eqs) :
    (PureEquation.normalForm (X := X) eqs).SoundFor
      (PureEquation.constraints X eqs) := by
  intro v hv
  rcases hv with ⟨w, _, rfl⟩
  apply (PureEquation.constraints_holds_iff eqs
    (w.pullbackSubst (PureEquation.subst eqs))).mpr
  intro b hb
  have hl := PureEquation.lookup_of_mem eqs hc b hb
  simp [Valuation.pullbackSubst, PureEquation.subst, hl,
    ClosedPureTy.eval_const b.value w
      (w.pullbackSubst (PureEquation.subst eqs))]

theorem PureEquation.normalForm_covers {X : Domain}
    (eqs : List PureEquation) (v : Valuation)
    (hv : (PureEquation.constraints X eqs).holds v) :
    (PureEquation.normalForm (X := X) eqs).Represents v := by
  refine ⟨v, trivial, ?_⟩
  have hsol := (PureEquation.constraints_holds_iff eqs v).mp hv
  cases v with
  | mk ft fe =>
      congr 1
      · funext i
        by_cases hl : ∃ t, PureEquation.lookup eqs i = some t
        · rcases hl with ⟨t, ht⟩
          rcases PureEquation.lookup_some_mem eqs i t ht with
            ⟨b, hb, hbi, hbt⟩
          have h := hsol b hb
          change ft i =
            (match PureEquation.lookup eqs i with
            | some t => t.toTy
            | none => .var i).eval ⟨ft, fe⟩
          rw [ht]
          rw [hbi, hbt] at h
          exact h
        · have hn : PureEquation.lookup eqs i = none := by
            cases hh : PureEquation.lookup eqs i with
            | none => rfl
            | some t => exact False.elim (hl ⟨t, hh⟩)
          change ft i =
            (match PureEquation.lookup eqs i with
            | some t => t.toTy
            | none => .var i).eval ⟨ft, fe⟩
          rw [hn]
          rfl
      · funext i
        change fe i = (Poly.Effect.var i).eval fe
        simp [Poly.Effect.eval, Poly.Effect.var]

theorem PureEquation.normalForm_principal {X : Domain}
    (eqs : List PureEquation) (hc : PureEquation.Compatible eqs) :
    (PureEquation.normalForm (X := X) eqs).IsPrincipal
      (fun c => c = .top) (PureEquation.constraints X eqs) := by
  apply NormalForm.principal_of_covers
  · exact ⟨rfl, PureEquation.normalForm_sound eqs hc⟩
  · intro v hv
    exact PureEquation.normalForm_covers eqs v hv

/-- Executable normalization of the finite closed-pure equality fragment. -/
def PureEquation.normalize {X : Domain}
    (eqs : List PureEquation) : Option (NormalForm X) :=
  match PureEquation.unify eqs with
  | some θ => some ⟨.top, θ⟩
  | none => none

theorem PureEquation.normalize_principal {X : Domain}
    (eqs : List PureEquation) (n : NormalForm X)
    (h : PureEquation.normalize eqs = some n) :
    n.IsPrincipal (fun c => c = .top)
      (PureEquation.constraints X eqs) := by
  by_cases hc : PureEquation.Compatible eqs
  · simp [PureEquation.normalize, PureEquation.unify, hc] at h
    cases h
    exact PureEquation.normalForm_principal eqs hc
  · simp [PureEquation.normalize, PureEquation.unify, hc] at h

theorem PureEquation.normalize_none_iff {X : Domain}
    (eqs : List PureEquation) :
    (PureEquation.normalize (X := X) eqs = none) ↔
      ¬ ∃ σ, PureEquation.solves eqs σ := by
  simp only [PureEquation.normalize]
  cases h : PureEquation.unify eqs with
  | none =>
      simpa [h] using (PureEquation.unify_none_iff eqs)
  | some θ =>
      simp
      exact ⟨θ, PureEquation.unify_sound eqs θ h⟩

/-- A single variable binding handles an arbitrary type term, including
arrows. The occurs check rejects cyclic equations. -/
def variableBinding (i : Nat) (t : Ty) : Substitution :=
  { types := fun j => if j = i then t else .var j
    effects := Poly.Effect.var }

theorem Effect.subst_vars_id (ε : Effect) :
    ε.subst Poly.Effect.var = ε := by
  cases ε with
  | mk labels vars =>
      simp [Effect.subst, Poly.Effect.var]

theorem Ty.subst_variableBinding_fixed (i : Nat) (t u : Ty)
    (hi : i ∉ u.fvTypes) :
    u.subst (variableBinding i t) = u := by
  induction u with
  | var j =>
      have hne : j ≠ i := by
        intro h
        subst j
        exact hi (by simp [Ty.fvTypes])
      simp [Ty.subst, variableBinding, hne]
  | base b => cases b <;> rfl
  | arr a ε b iha ihb =>
      have ha : i ∉ a.fvTypes := by
        intro h; exact hi (by simp [Ty.fvTypes, h])
      have hb : i ∉ b.fvTypes := by
        intro h; exact hi (by simp [Ty.fvTypes, h])
      change Ty.arr (a.subst (variableBinding i t))
        (ε.subst Poly.Effect.var)
        (b.subst (variableBinding i t)) = Ty.arr a ε b
      rw [iha ha, ihb hb, Effect.subst_vars_id]

def unifyVariable (i : Nat) (t : Ty) : Option Substitution :=
  if t = .var i then some (variableBinding i t)
  else if i ∈ t.fvTypes then none
  else some (variableBinding i t)

theorem unifyVariable_sound (i : Nat) (t : Ty) (θ : Substitution)
    (h : unifyVariable i t = some θ) :
    (.var i : Ty).subst θ = t.subst θ := by
  unfold unifyVariable at h
  by_cases heq : t = .var i
  · simp [heq] at h
    cases h
    rw [heq]
  · simp [heq] at h
    by_cases hi : i ∈ t.fvTypes
    · simp [hi] at h
    · simp [hi] at h
      cases h
      have hleft : (.var i : Ty).subst (variableBinding i t) = t := by
        simp [Ty.subst, variableBinding]
      rw [hleft]
      exact (Ty.subst_variableBinding_fixed i t t hi).symm

theorem unifyVariable_most_general (i : Nat) (t : Ty)
    (θ σ : Substitution) (h : unifyVariable i t = some θ)
    (hσ : (.var i : Ty).subst σ = t.subst σ) :
    (∀ j, (θ.types j).subst σ = σ.types j) ∧
    (∀ j, (θ.effects j).subst σ.effects = σ.effects j) := by
  unfold unifyVariable at h
  by_cases heq : t = .var i
  · simp [heq] at h
    cases h
    constructor
    · intro j
      by_cases hj : j = i
      · subst j; simp [variableBinding, Ty.subst]
      · simp [variableBinding, hj, Ty.subst]
    · intro j
      simp [variableBinding, Poly.Effect.var,
        Effect.subst]
  · simp [heq] at h
    by_cases hi : i ∈ t.fvTypes
    · simp [hi] at h
    · simp [hi] at h
      cases h
      constructor
      · intro j
        by_cases hj : j = i
        · subst j
          simpa [variableBinding, Ty.subst] using hσ.symm
        · simp [variableBinding, hj, Ty.subst]
      · intro j
        simp [variableBinding, Poly.Effect.var,
          Effect.subst]

theorem unifyVariable_none_iff (i : Nat) (t : Ty) :
    unifyVariable i t = none ↔
      ¬ ∃ σ : Substitution,
        (.var i : Ty).subst σ = t.subst σ := by
  constructor
  · intro h ⟨σ, hσ⟩
    unfold unifyVariable at h
    by_cases heq : t = .var i
    · simp [heq] at h
    · simp [heq] at h
      have hi : i ∈ t.fvTypes := by
        by_contra hn
        simp [hn] at h
      let v : Valuation :=
        ⟨fun _ => .atom 2, fun _ => ∅⟩
      have hv : (.var i : Ty).eval (v.pullbackSubst σ) =
          t.eval (v.pullbackSubst σ) := by
        simpa [Ty.eval_subst] using
          congrArg (fun u : Ty => u.eval v) hσ
      have hbad : (Ty.var i).occursBad t = true := by
        simpa [Ty.occursBad] using hi
      exact (Ty.occursBad_eq_unsat (.var i) t
        (v.pullbackSubst σ) (by
          intro h'; exact heq h'.symm) hbad) hv
  · intro h
    by_cases heq : t = .var i
    · exact False.elim (h ⟨variableBinding i t,
        by simp [heq, Ty.subst]⟩)
    · by_cases hi : i ∈ t.fvTypes
      · simp [unifyVariable, heq, hi]
      · exact False.elim (h ⟨variableBinding i t,
          unifyVariable_sound i t (variableBinding i t)
            (by simp [unifyVariable, heq, hi])⟩)

def alphaIntEquation : List PureEquation :=
  [{ name := 0, value := .int }]

theorem alphaInt_unify :
    PureEquation.unify alphaIntEquation =
      some (PureEquation.subst alphaIntEquation) := by
  rfl

theorem alphaInt_normalize {X : Domain} :
    PureEquation.normalize (X := X) alphaIntEquation =
      some (PureEquation.normalForm alphaIntEquation) := by
  rfl

theorem alphaInt_substitution :
    (PureEquation.subst alphaIntEquation).types 0 = .base .int := by
  decide

theorem alphaInt_principal {X : Domain} :
    (PureEquation.normalForm (X := X) alphaIntEquation).IsPrincipal
      (fun c => c = .top)
      (PureEquation.constraints X alphaIntEquation) := by
  apply PureEquation.normalForm_principal
  decide

theorem empty_equations_identity (i : Nat) :
    (PureEquation.subst []).types i = .var i := rfl

theorem alphaInt_reconstruct {X : Domain} (r : Output X)
    (ht : r.ty = .var 0) :
    ((PureEquation.normalForm alphaIntEquation).reconstruct r).ty =
      .base .int := by
  change r.ty.subst (PureEquation.subst alphaIntEquation) = .base .int
  rw [ht]
  exact alphaInt_substitution

theorem conflicting_base_equations :
    PureEquation.unify
      [{ name := 0, value := .int },
       { name := 0, value := .bool }] = none := by
  decide

theorem cyclic_type_equation :
    unifyVariable 0 (Ty.arr (.var 0) ∅ (.var 0)) = none := by
  decide

theorem cyclic_type_equation_no_solution :
    ¬ ∃ σ : Substitution,
      (.var 0 : Ty).subst σ =
        (Ty.arr (.var 0) ∅ (.var 0)).subst σ := by
  exact (unifyVariable_none_iff 0
    (Ty.arr (.var 0) ∅ (.var 0))).mp cyclic_type_equation

end SystemFXi.EHMX
