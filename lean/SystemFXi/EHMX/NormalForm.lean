import SystemFXi.EHMX.Completeness

namespace SystemFXi.EHMX

/-- A solved residual constraint and a reconstruction substitution. -/
structure NormalForm (X : Domain) where
  residual : Constraint X
  subst : Substitution

/-- The valuations of the original constraint represented by a normal form. -/
def NormalForm.Represents {X : Domain} (n : NormalForm X)
    (v : Valuation) : Prop :=
  ∃ w : Valuation, n.residual.holds w ∧ v = w.pullbackSubst n.subst

def NormalForm.SoundFor {X : Domain} (n : NormalForm X)
    (D : Constraint X) : Prop :=
  ∀ v, n.Represents v → D.holds v

def NormalForm.Covers {X : Domain} (n : NormalForm X)
    (D : Constraint X) : Prop :=
  ∀ v, D.holds v → n.Represents v

/-- A normal form must preserve the type and effect names free in Γ. -/
def NormalForm.IsNormalForm {X : Domain}
    (Solved : Constraint X → Prop) (D : Constraint X)
    (n : NormalForm X) : Prop :=
  Solved n.residual ∧ n.SoundFor D

/-- HM(X)'s existential projection onto the free names of D. -/
def NormalForm.MoreGeneralThanOn {X : Domain}
    (D : Constraint X) (n m : NormalForm X) : Prop :=
  ∀ v, m.Represents v → ∃ w, n.Represents w ∧
    (∀ i ∈ D.fvTypes, w.types i = v.types i) ∧
    (∀ i ∈ D.fvEffects, w.effects i = v.effects i)

def NormalForm.IsPrincipal {X : Domain}
    (Solved : Constraint X → Prop) (D : Constraint X)
    (n : NormalForm X) : Prop :=
  n.IsNormalForm Solved D ∧
  ∀ m, m.IsNormalForm Solved D → n.MoreGeneralThanOn D m

/-- A complete representation of D is principal among sound solved forms. -/
theorem NormalForm.principal_of_covers {X : Domain}
    (Solved : Constraint X → Prop) (D : Constraint X)
    (n : NormalForm X)
    (hn : n.IsNormalForm Solved D) (hcover : n.Covers D) :
    n.IsPrincipal Solved D := by
  refine ⟨hn, ?_⟩
  intro m hm v hv
  exact ⟨v, hcover v (hm.2 v hv),
    fun _ _ => rfl, fun _ _ => rfl⟩

/-- Projection can make a normal form principal even when it omits solutions
on names absent from the constraint. Such a name may still occur in the
inferred result type. -/
def NormalForm.projectionExample {X : Domain} : NormalForm X :=
  { residual := .typeEq (.var 0) (.base .int)
    subst := { types := Ty.var, effects := Poly.Effect.var } }

theorem NormalForm.projectionExample_principal {X : Domain} :
    (NormalForm.projectionExample (X := X)).IsPrincipal
      (fun R => R = .typeEq (.var 0) (.base .int)) .top := by
  let v : Valuation := ⟨fun _ => .atom 0, fun _ => ∅⟩
  have hv : (NormalForm.projectionExample (X := X)).Represents v := by
    refine ⟨v, ?_, ?_⟩
    · rfl
    · cases v with
      | mk ft fe =>
          congr 1
          · funext i
            simp [projectionExample,
              Poly.Effect.eval, Poly.Effect.var]
  refine ⟨⟨rfl, fun _ _ => trivial⟩, ?_⟩
  intro m _ u _
  exact ⟨v, hv, by simp [Constraint.fvTypes],
    by simp [Constraint.fvEffects]⟩

theorem NormalForm.projectionExample_not_covers {X : Domain} :
    ¬ (NormalForm.projectionExample (X := X)).Covers .top := by
  let v : Valuation := ⟨fun _ => .atom 1, fun _ => ∅⟩
  intro hc
  obtain ⟨w, hw, heq⟩ := hc v trivial
  have h0 : w.types 0 = .atom 0 := hw
  have h1 := congrArg (fun u : Valuation => u.types 0) heq
  simp [NormalForm.projectionExample, Valuation.pullbackSubst,
    Ty.eval, v] at h1
  rw [h0] at h1
  cases h1

/-- The computational obligation for a constraint domain. It is imposed on
the combined type, effect, and X predicates, including handler quantifiers. -/
structure PrincipalNormalizer (X : Domain) where
  solved : Constraint X → Prop
  solved_satisfiable : ∀ R, solved R → ∃ v, R.holds v
  normalize : Constraint X → Option (NormalForm X)
  principal_result : ∀ D n, normalize D = some n →
    n.IsPrincipal solved D
  fail_iff_no_normal_form : ∀ D, normalize D = none ↔
    ¬ ∃ n : NormalForm X, n.IsNormalForm solved D

theorem PrincipalNormalizer.principal {X : Domain}
    (N : PrincipalNormalizer X)
    (D : Constraint X) (n : NormalForm X)
    (h : N.normalize D = some n) :
    n.IsPrincipal N.solved D :=
  N.principal_result D n h

theorem PrincipalNormalizer.success_has_solution {X : Domain}
    (N : PrincipalNormalizer X) (D : Constraint X)
    (n : NormalForm X) (h : N.normalize D = some n) :
    ∃ v, D.holds v := by
  have hp := N.principal D n h
  obtain ⟨w, hw⟩ := N.solved_satisfiable n.residual hp.1.1
  exact ⟨w.pullbackSubst n.subst,
    hp.1.2 _ ⟨w, hw, rfl⟩⟩

def NormalForm.reconstruct {X : Domain} (n : NormalForm X)
    (r : Output X) : Output X :=
  { ty := r.ty.subst n.subst
    effect := r.effect.subst n.subst.effects
    constraints := n.residual
    next := r.next }

theorem NormalForm.reconstruct_sound {X : Domain}
    (n : NormalForm X) (r : Output X)
    (h : n.SoundFor r.constraints) (w : Valuation)
    (hw : n.residual.holds w) :
    r.constraints.holds (w.pullbackSubst n.subst) ∧
    (n.reconstruct r).ty.eval w =
      r.ty.eval (w.pullbackSubst n.subst) ∧
    (n.reconstruct r).effect.eval w.effects =
      r.effect.eval (w.pullbackSubst n.subst).effects := by
  constructor
  · exact h _ ⟨w, hw, rfl⟩
  constructor
  · exact Ty.eval_subst r.ty n.subst w
  · exact Effect.eval_subst r.effect n.subst.effects w.effects

/-- HM(X)-style normalization yields a principal normal form. The generated
qualified type separately retains its semantic principality. -/
theorem Typing.inferQualifiedTotal_with_principal_normalForm
    {sig : Signature} {X : Domain} [DecidableEq X.Pred]
    (hRename : LawfulRename X)
    (hSupport : LawfulSupport X)
    (hFVRename : LawfulFVRename X)
    (hClosed : sig.Closed)
    (N : PrincipalNormalizer X)
    (A : List X.Pred) (Γ : Context X) (e : Expr) (s : Supply)
    {C₀ : Constraint X} {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀)
    (r : Output X) (n : NormalForm X)
    (hr : inferQualifiedTotal sig X A Γ e s = some r)
    (hn : N.normalize r.constraints = some n) :
    n.IsPrincipal N.solved r.constraints ∧
    n.SoundFor r.constraints ∧
    ∀ (C : Constraint X) (τ : Ty) (ε : Effect),
      Typing sig X C Γ e τ ε →
      r.MoreGeneralThan Γ
        (.and (assumptions A) C) τ ε := by
  obtain ⟨r', hr', _, hprincipal⟩ :=
    h₀.inferQualifiedTotal_principal hRename hSupport
      hFVRename hClosed A Γ e s
  rw [hr] at hr'
  cases hr'
  refine ⟨N.principal r.constraints n hn,
    (N.principal_result r.constraints n hn).1.2, ?_⟩
  intro C τ ε h
  exact hprincipal C τ ε h

end SystemFXi.EHMX
