import SystemFXi.EHMX.Classes

namespace SystemFXi.EHMX

example (sig : Signature) (X : Domain) (Γ : Context X) (s : Supply)
    (n : Int) :
    infer sig X Γ (.int n) s =
      some ⟨.base .int, ∅, .top, s⟩ := by
  rfl

example (sig : Signature) (X : Domain) (Γ : Context X) (s : Supply)
    (b : Bool) :
    infer sig X Γ (.bool b) s =
      some ⟨.base .bool, ∅, .top, s⟩ := by
  rfl

example (X : Domain) :
    simplifyAtom (X := X) (.typeEq (.base .int) (.base .bool)) = none := by
  rfl

example (I : ClassEnv) :
    (infer (fun _ => none) (classDomain I) []
      (.app (.lam (.var 0)) (.int 1)) ⟨1, 1⟩).map
        (fun r => (r.ty, r.effect.vars)) =
      some (.var 4, {3}) := by
  rfl

/-- The bare `Domain` interface admits renamings that do not preserve truth.
This is a concrete obstruction to a completeness theorem for arbitrary X. -/
private def nonLawfulDomain : Domain where
  Pred := Bool
  rename := fun ρ _ p => if ρ 0 = 0 then p else true
  holds := fun _ p => p = false
  fvTypes := fun _ => {0}
  fvEffects := fun _ => ∅

private def nonLawfulScheme : Scheme nonLawfulDomain where
  typeVars := {0}
  effectVars := ∅
  predicates := .predicate false
  result := .var 0

theorem nonLawfulDomain_not_lawfulRename :
    ¬ LawfulRename nonLawfulDomain := by
  intro h
  let v : Valuation := ⟨fun _ => .atom 0, fun _ => ∅⟩
  have heq := h.holds_rename (fun _ => 1) id false v
  simp [nonLawfulDomain, Valuation.pullback] at heq

theorem nonLawfulDomain_declarative_var :
    Typing (fun _ => none) nonLawfulDomain .top [nonLawfulScheme]
      (.var 0) (.var 0) ∅ := by
  have h : Typing (fun _ => none) nonLawfulDomain .top [nonLawfulScheme]
      (.var 0) (nonLawfulScheme.instantiate id id).1 ∅ := by
    apply Typing.var rfl
    · exact ⟨by simp, by simp⟩
    · simp [Scheme.SafeRename, Scheme.fvTypes, Scheme.fvEffects,
        nonLawfulScheme, Constraint.boundTypes, Constraint.boundEffects,
        Constraint.fvTypes, Constraint.fvEffects, nonLawfulDomain]
    · intro ρ _
      simp [Scheme.instantiate, Constraint.rename, nonLawfulScheme,
        nonLawfulDomain, Constraint.holds]
  simpa [Scheme.instantiate, Ty.rename, nonLawfulScheme] using h

theorem nonLawfulDomain_generated_unsat :
    ∃ r, generate (fun _ => none) nonLawfulDomain [nonLawfulScheme]
        (.var 0) ⟨1, 0⟩ = some r ∧
      ∀ ρ, ¬ r.constraints.holds ρ := by
  refine ⟨⟨.var 2, ∅, .predicate true, ⟨3, 2⟩⟩, rfl, ?_⟩
  intro ρ
  simp [Constraint.holds, nonLawfulDomain]

/-- Even for the lawful class domain, the executable supply must start above
the free names in the context. Here it reuses the context's `α0`. -/
theorem stale_supply_collides (I : ClassEnv) :
    (generate (fun _ => none) (classDomain I)
      [Scheme.mono (.var 0)] (.lam (.var 1)) ⟨0, 0⟩).map
        (fun r => r.ty) =
      some (.arr (.var 0) ∅ (.var 0)) ∧
    Typing (fun _ => none) (classDomain I) .top
      [Scheme.mono (.var 0)] (.lam (.var 1))
      (.arr (.var 1) ∅ (.var 0)) ∅ := by
  constructor
  · rfl
  · apply Typing.lam
    have h : Typing (fun _ => none) (classDomain I) .top
        (Scheme.mono (.var 1) :: [Scheme.mono (.var 0)])
        (.var 1) ((Scheme.mono (X := classDomain I) (.var 0)).instantiate id id).1 ∅ := by
      apply Typing.var rfl
      · exact ⟨by simp, by simp⟩
      · simp [Scheme.SafeRename, Scheme.mono, Scheme.fvTypes,
          Scheme.fvEffects, Constraint.boundTypes, Constraint.boundEffects]
      · intro ρ _
        trivial
    simpa [Scheme.mono, Scheme.instantiate, Ty.rename] using h

theorem stale_supply_changes_meaning :
    let v : Valuation :=
      ⟨fun i => if i = 0 then .atom 0 else .atom 1, fun _ => ∅⟩
    (Ty.arr (.var 0) ∅ (.var 0)).eval v ≠
      (Ty.arr (.var 1) ∅ (.var 0)).eval v := by
  simp [Ty.eval]

theorem seeded_supply_avoids_collision (I : ClassEnv) :
    (generateFresh (fun _ => none) (classDomain I)
      [Scheme.mono (.var 0)] (.lam (.var 1)) ⟨0, 0⟩).map
        (fun r => r.ty) =
      some (.arr (.var 1) ∅ (.var 0)) := by
  rfl

/-- A clause-local instantiation can depend on each rigid operation type. -/
theorem local_instance_after_rigid (X : Domain) (i j : Nat) (hij : i ≠ j)
    (ρ : Valuation) :
    (Constraint.allTy i
      (Constraint.exTy j (.typeEq (.var j) (.var i)) : Constraint X)).holds ρ := by
  intro t
  refine ⟨t, ?_⟩
  simp [Constraint.holds, Ty.eval, hij]

/-- Projecting an unrelated local name does not make a rigid argument a
fixed handler result. -/
theorem projected_argument_cannot_escape (X : Domain) (i j k : Nat)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (ρ : Valuation) :
    ¬ (Constraint.allTy i
      (Constraint.exTy k (.typeEq (.var i) (.var j)) : Constraint X)).holds ρ := by
  intro h
  have h0 := h (.atom 0)
  have h1 := h (.atom 1)
  rcases h0 with ⟨_, h0⟩
  rcases h1 with ⟨_, h1⟩
  simp [Constraint.holds, Ty.eval, hik, hjk, Ne.symm hij] at h0 h1
  have h01 := h0.trans h1.symm
  cases h01

/-- The handler result name cannot be hidden as a clause-local witness. -/
theorem result_type_not_clause_local (X : Domain) (decl : OpDecl)
    (Γ : Context X) (C : Constraint X) (εin εr δ χ : Effect) :
    ¬ decl.ClauseScope Γ C (.base .int) (.var 0) εin εr δ χ {0} ∅ := by
  intro h
  have hlocal := h.2.2.1
  have hmem : 0 ∈ ({0} : Finset Nat) ∩
      (Γ.fvTypes ∪ C.fvTypes ∪ (Ty.base .int).fvTypes ∪
        (Ty.var 0).fvTypes ∪ decl.typeVars ∪
        decl.input.fvTypes ∪ decl.output.fvTypes) := by
    simp [Ty.fvTypes]
  rw [hlocal] at hmem
  simp at hmem

private def collisionSig : Signature := fun op =>
  if op = 0 then
    some ⟨{0}, ∅, .var 0, .var 0⟩
  else none

/-- The operation binder α0 is renamed before entering a handler whose
environment already has a free α0. -/
theorem alpha_collision_handler_generates :
    (generate collisionSig
      (classDomain ⟨fun _ => True, fun _ => True⟩)
      [Scheme.mono (.var 0)]
      (.handle (.perform 0 (.var 0)) 0 (.var 0)
        (.app (.var 0) (.var 1))) ⟨2, 1⟩).isSome = true := by
  native_decide

private def captureScheme : Scheme (classDomain ⟨fun _ => True, fun _ => True⟩) :=
  { typeVars := {0}
    effectVars := ∅
    predicates := .allTy 1 (.typeEq (.var 0) (.var 1))
    result := .var 0 }

theorem scheme_inner_binder_capture_rejected :
    ¬ captureScheme.SafeRename (renameBound {0} 0) id := by
  simp [Scheme.SafeRename, captureScheme, Scheme.fvTypes,
    Scheme.fvEffects, Constraint.boundTypes, Constraint.boundEffects,
    Constraint.fvTypes, Constraint.fvEffects, renameBound]

end SystemFXi.EHMX
