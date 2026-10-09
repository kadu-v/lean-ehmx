import SystemFXi.EHMX.Completeness

namespace SystemFXi.EHMX

/-- HM(X)'s semantic free variables: changing this name can change truth. -/
def Constraint.semFreeType {X : Domain} (D : Constraint X)
    (i : Nat) : Prop :=
  ∃ v : Valuation, ∃ t : GroundTy,
    ¬ D.holds v ∧
      D.holds {v with types := Function.update v.types i t}

def Constraint.semFreeEffect {X : Domain} (D : Constraint X)
    (i : Nat) : Prop :=
  ∃ v : Valuation, ∃ ε : Finset Op,
    ¬ D.holds v ∧
      D.holds {v with effects := Function.update v.effects i ε}

/-- Fresh result names, kept outside the support of the generated result. -/
def Output.resultTypeName {X : Domain} (r : Output X) : Nat :=
  max r.next.types (r.supportTypes.sup id + 1)

def Output.resultEffectName {X : Domain} (r : Output X) : Nat :=
  max r.next.effects (r.supportEffects.sup id + 1)

theorem Output.resultTypeName_fresh {X : Domain}
    (r : Output X) (i : Nat) (hi : i ∈ r.supportTypes) :
    i < r.resultTypeName := by
  have hs : i ≤ r.supportTypes.sup id := Finset.le_sup (f := id) hi
  simp only [Output.resultTypeName]
  omega

theorem Output.resultEffectName_fresh {X : Domain}
    (r : Output X) (i : Nat) (hi : i ∈ r.supportEffects) :
    i < r.resultEffectName := by
  have hs : i ≤ r.supportEffects.sup id := Finset.le_sup (f := id) hi
  simp only [Output.resultEffectName]
  omega

def Output.extendResult {X : Domain} (r : Output X)
    (v : Valuation) : Valuation :=
  { types := Function.update v.types r.resultTypeName (r.ty.eval v)
    effects := Function.update v.effects r.resultEffectName
      (r.effect.eval v.effects) }

/-- HM(X)-style canonical inference problem: the output type and effect are
represented by distinguished variables inside the constraint. -/
def Output.canonicalConstraint {X : Domain} (r : Output X) :
    Constraint X :=
  .and r.constraints
    (.and (.typeEq (.var r.resultTypeName) r.ty)
      (.and (.effectLe (Poly.Effect.var r.resultEffectName) r.effect)
        (.effectLe r.effect (Poly.Effect.var r.resultEffectName))))

theorem Output.canonicalConstraint_holds_iff {X : Domain}
    (r : Output X) (v : Valuation) :
    r.canonicalConstraint.holds v ↔
      r.constraints.holds v ∧
      v.types r.resultTypeName = r.ty.eval v ∧
      v.effects r.resultEffectName = r.effect.eval v.effects := by
  simp only [Output.canonicalConstraint, Constraint.holds,
    Ty.eval]
  have hvar :
      (Poly.Effect.var r.resultEffectName).eval v.effects =
        v.effects r.resultEffectName := by
    simp [Poly.Effect.eval, Poly.Effect.var]
  rw [hvar]
  constructor
  · rintro ⟨hc, ht, he₁, he₂⟩
    exact ⟨hc, ht, Finset.Subset.antisymm he₁ he₂⟩
  · rintro ⟨hc, ht, he⟩
    exact ⟨hc, ht, he.le, he.symm.le⟩

theorem Output.extendResult_agrees {X : Domain}
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

theorem Output.extendResult_solution {X : Domain}
    (hSupport : LawfulSupport X)
    (r : Output X) (v : Valuation)
    (hv : r.constraints.holds v) :
    r.canonicalConstraint.holds (r.extendResult v) := by
  have ha := r.extendResult_agrees v
  have hC : r.constraints.holds (r.extendResult v) :=
    (Constraint.holds_support hSupport r.constraints v
      (r.extendResult v)
      (by intro i hi; exact (ha.1 i (by
        simp [Output.supportTypes, Constraint.usedTypes, hi])).symm)
      (by intro i hi; exact (ha.2 i (by
        simp [Output.supportEffects, Constraint.usedEffects, hi])).symm)).mp hv
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
  apply (r.canonicalConstraint_holds_iff (r.extendResult v)).mpr
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

theorem Output.resultTypeName_semFree {X : Domain}
    (r : Output X) (v : Valuation)
    (hv : r.canonicalConstraint.holds v) :
    r.canonicalConstraint.semFreeType r.resultTypeName := by
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
  have hfail : ¬ r.canonicalConstraint.holds bad := by
    intro hb
    have hbt := (r.canonicalConstraint_holds_iff bad).mp hb |>.2.1
    have hvt := (r.canonicalConstraint_holds_iff v).mp hv |>.2.1
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

theorem Output.resultEffectName_semFree {X : Domain}
    (r : Output X) (v : Valuation)
    (hv : r.canonicalConstraint.holds v) :
    r.canonicalConstraint.semFreeEffect r.resultEffectName := by
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
  have hfail : ¬ r.canonicalConstraint.holds bad := by
    intro hb
    have hbe := (r.canonicalConstraint_holds_iff bad).mp hb |>.2.2
    have hve := (r.canonicalConstraint_holds_iff v).mp hv |>.2.2
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

def Output.canonical {X : Domain} (r : Output X) : Output X :=
  { ty := .var r.resultTypeName
    effect := Poly.Effect.var r.resultEffectName
    constraints := r.canonicalConstraint
    next := ⟨r.resultTypeName + 1, r.resultEffectName + 1⟩ }

def Context.Closed {X : Domain} (Γ : Context X) : Prop :=
  Γ.fvTypes = ∅ ∧ Γ.fvEffects = ∅

theorem Output.canonical_principal {X : Domain}
    (hSupport : LawfulSupport X)
    (Γ : Context X) (hClosed : Γ.Closed)
    (r : Output X) (C : Constraint X) (τ : Ty) (ε : Effect)
    (h : r.MoreGeneralThan Γ C τ ε) :
    r.canonical.MoreGeneralThan Γ C τ ε := by
  intro vd hC
  obtain ⟨wg, _, _, hwg, hty, heff⟩ := h vd hC
  let w := r.extendResult wg
  have hw : r.canonicalConstraint.holds w :=
    r.extendResult_solution hSupport wg hwg
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
  · change (Poly.Effect.var r.resultEffectName).eval w.effects =
      ε.eval vd.effects
    calc
      (Poly.Effect.var r.resultEffectName).eval w.effects =
          w.effects r.resultEffectName := by
        simp [Poly.Effect.eval, Poly.Effect.var]
      _ = r.effect.eval wg.effects := by
        simp [w, Output.extendResult, Function.update]
      _ = ε.eval vd.effects := heff

theorem Typing.inferQualifiedTotal_canonical_principal
    {sig : Signature} {X : Domain} [DecidableEq X.Pred]
    (hRename : LawfulRename X)
    (hSupport : LawfulSupport X)
    (hFVRename : LawfulFVRename X)
    (hSigClosed : sig.Closed)
    (A : List X.Pred) (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (s : Supply)
    {C₀ : Constraint X} {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀) :
    ∃ r : Output X,
      inferQualifiedTotal sig X A Γ e s = some r ∧
      ∀ (C : Constraint X) (τ : Ty) (ε : Effect),
        Typing sig X C Γ e τ ε →
        r.canonical.MoreGeneralThan Γ
          (.and (assumptions A) C) τ ε := by
  obtain ⟨r, hr, _, hp⟩ := h₀.inferQualifiedTotal_principal
    hRename hSupport hFVRename hSigClosed A Γ e s
  refine ⟨r, hr, ?_⟩
  intro C τ ε h
  exact r.canonical_principal hSupport Γ hΓClosed
    (.and (assumptions A) C) τ ε (hp C τ ε h)

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

theorem Constraint.semFreeType_mem_fvTypes {X : Domain}
    (hSupport : LawfulSupport X) (D : Constraint X) (i : Nat)
    (h : D.semFreeType i) : i ∈ D.fvTypes := by
  by_contra hnot
  obtain ⟨v, t, hn, hy⟩ := h
  have heq := Constraint.holds_support hSupport D v
    {v with types := Function.update v.types i t}
    (by
      intro j hj
      have hji : j ≠ i := by
        intro he; subst j; exact hnot hj
      simp [Function.update, hji])
    (by intro j _; rfl)
  exact hn (heq.mpr hy)

theorem Constraint.semFreeEffect_mem_fvEffects {X : Domain}
    (hSupport : LawfulSupport X) (D : Constraint X) (i : Nat)
    (h : D.semFreeEffect i) : i ∈ D.fvEffects := by
  by_contra hnot
  obtain ⟨v, ε, hn, hy⟩ := h
  have heq := Constraint.holds_support hSupport D v
    {v with effects := Function.update v.effects i ε}
    (by intro j _; rfl)
    (by
      intro j hj
      have hji : j ≠ i := by
        intro he; subst j; exact hnot hj
      simp [Function.update, hji])
  exact hn (heq.mpr hy)

/-- Every semantic ground type has a closed term in the HM(X) type algebra. -/
def GroundTy.toTy : GroundTy → Ty
  | .atom 0 => .base .int
  | .atom 1 => .base .bool
  | .atom (n + 2) => .base (.other n)
  | .arr a ε b => .arr a.toTy ⟨ε, ∅⟩ b.toTy

theorem GroundTy.toTy_eval (t : GroundTy) (v : Valuation) :
    t.toTy.eval v = t := by
  induction t with
  | atom n =>
      cases n with
      | zero => rfl
      | succ n =>
          cases n with
          | zero => rfl
          | succ n => rfl
  | arr a ε b iha ihb =>
      simp [GroundTy.toTy, Ty.eval, iha, ihb,
        Poly.Effect.eval]

def Valuation.groundSubst (v : Valuation) : Substitution :=
  { types := fun i => (v.types i).toTy
    effects := fun i => ⟨v.effects i, ∅⟩ }

theorem Valuation.groundSubst_pullback (v w : Valuation) :
    w.pullbackSubst v.groundSubst = v := by
  cases v with
  | mk ft fe =>
      cases w with
      | mk wt we =>
          simp only [Valuation.pullbackSubst,
            Valuation.groundSubst]
          congr 1
          · funext i
            exact GroundTy.toTy_eval (ft i) ⟨wt, we⟩
          · funext i
            simp [Poly.Effect.eval]

def NormalForm.groundWith {X : Domain}
    (R : Constraint X) (v : Valuation) : NormalForm X :=
  ⟨R, v.groundSubst⟩

theorem NormalForm.groundWith_represents {X : Domain}
    (R : Constraint X) (hR : ∀ w, R.holds w)
    (v : Valuation) :
    (NormalForm.groundWith R v).Represents v := by
  exact ⟨v, hR v, (v.groundSubst_pullback v).symm⟩

theorem NormalForm.groundWith_soundFor {X : Domain}
    (R D : Constraint X) (v : Valuation) (hv : D.holds v) :
    (NormalForm.groundWith R v).SoundFor D := by
  intro u hu
  obtain ⟨w, _, he⟩ := hu
  change u = w.pullbackSubst v.groundSubst at he
  rw [v.groundSubst_pullback w] at he
  subst u
  exact hv

/-- A normal form must preserve the type and effect names free in Γ. -/
def NormalForm.IsNormalForm {X : Domain}
    (Solved : Constraint X → Prop) (D : Constraint X)
    (n : NormalForm X) : Prop :=
  Solved n.residual ∧ n.SoundFor D

/-- HM(X)'s existential projection onto the free names of D. -/
def NormalForm.MoreGeneralThanOn {X : Domain}
    (D : Constraint X) (n m : NormalForm X) : Prop :=
  ∀ v, m.Represents v → ∃ w, n.Represents w ∧
    (∀ i, D.semFreeType i → w.types i = v.types i) ∧
    (∀ i, D.semFreeEffect i → w.effects i = v.effects i)

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
  exact ⟨v, hv,
    by simp [Constraint.semFreeType, Constraint.holds],
    by simp [Constraint.semFreeEffect, Constraint.holds]⟩

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

/-- HM(X) principality implies projection completeness for every ground
solution when `true` is an admissible solved form. -/
theorem NormalForm.principal_projects_solution {X : Domain}
    (Solved : Constraint X → Prop)
    (hTrue : ∃ R, Solved R ∧ ∀ v, R.holds v)
    (D : Constraint X) (n : NormalForm X)
    (hp : n.IsPrincipal Solved D)
    (v : Valuation) (hv : D.holds v) :
    ∃ u, n.Represents u ∧
      (∀ i, D.semFreeType i → u.types i = v.types i) ∧
      (∀ i, D.semFreeEffect i → u.effects i = v.effects i) := by
  obtain ⟨R, hR, hvalid⟩ := hTrue
  have hm : (NormalForm.groundWith R v).IsNormalForm Solved D :=
    ⟨hR, NormalForm.groundWith_soundFor R D v hv⟩
  exact hp.2 (NormalForm.groundWith R v) hm v
    (NormalForm.groundWith_represents R hvalid v)

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

theorem NormalForm.reconstruct_canonical_principal {X : Domain}
    (Solved : Constraint X → Prop)
    (hTrue : ∃ R, Solved R ∧ ∀ v, R.holds v)
    (Γ : Context X) (hΓClosed : Γ.Closed)
    (r : Output X) (n : NormalForm X)
    (hp : n.IsPrincipal Solved r.canonicalConstraint)
    (C : Constraint X) (τ : Ty) (ε : Effect)
    (hr : r.canonical.MoreGeneralThan Γ C τ ε) :
    (n.reconstruct r.canonical).MoreGeneralThan Γ C τ ε := by
  intro vd hC
  obtain ⟨vg, _, _, hg, ht, he⟩ := hr vd hC
  obtain ⟨u, hu, hut, hue⟩ :=
    n.principal_projects_solution Solved hTrue
      r.canonicalConstraint hp vg hg
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

/-- HM(X)-style normalization yields a principal reconstructed qualified
type and effect when a solved form denotes `true`. -/
theorem Typing.inferQualifiedTotal_with_principal_normalForm
    {sig : Signature} {X : Domain} [DecidableEq X.Pred]
    (hRename : LawfulRename X)
    (hSupport : LawfulSupport X)
    (hFVRename : LawfulFVRename X)
    (hClosed : sig.Closed)
    (N : PrincipalNormalizer X)
    (hTrue : ∃ R, N.solved R ∧ ∀ v, R.holds v)
    (A : List X.Pred) (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (s : Supply)
    {C₀ : Constraint X} {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀)
    (r : Output X) (n : NormalForm X)
    (hr : inferQualifiedTotal sig X A Γ e s = some r)
    (hn : N.normalize r.canonicalConstraint = some n) :
    n.IsPrincipal N.solved r.canonicalConstraint ∧
    n.SoundFor r.canonicalConstraint ∧
    ∀ (C : Constraint X) (τ : Ty) (ε : Effect),
      Typing sig X C Γ e τ ε →
      (n.reconstruct r.canonical).MoreGeneralThan Γ
        (.and (assumptions A) C) τ ε := by
  obtain ⟨r', hr', _, hprincipal⟩ :=
    h₀.inferQualifiedTotal_principal hRename hSupport
      hFVRename hClosed A Γ e s
  rw [hr] at hr'
  cases hr'
  refine ⟨N.principal r.canonicalConstraint n hn,
    (N.principal_result r.canonicalConstraint n hn).1.2, ?_⟩
  intro C τ ε h
  exact n.reconstruct_canonical_principal N.solved hTrue Γ hΓClosed r
    (N.principal r.canonicalConstraint n hn)
    (.and (assumptions A) C) τ ε
    (r.canonical_principal hSupport Γ hΓClosed
      (.and (assumptions A) C) τ ε (hprincipal C τ ε h))

/-- Closed, realizable HM(X)-style existence theorem: inference and
normalization return a sound principal constrained type and effect. -/
theorem Typing.inferQualifiedTotal_normalized_exists
    {sig : Signature} {X : Domain} [DecidableEq X.Pred]
    (hRename : LawfulRename X)
    (hSupport : LawfulSupport X)
    (hFVRename : LawfulFVRename X)
    (hSigClosed : sig.Closed)
    (N : PrincipalNormalizer X)
    (hTrue : ∃ R, N.solved R ∧ ∀ v, R.holds v)
    (A : List X.Pred) (Γ : Context X) (hΓClosed : Γ.Closed)
    (e : Expr) (s : Supply)
    {C₀ : Constraint X} {τ₀ : Ty} {ε₀ : Effect}
    (h₀ : Typing sig X C₀ Γ e τ₀ ε₀)
    (v : Valuation)
    (hv : (Constraint.and (assumptions A) C₀).holds v) :
    ∃ (r : Output X) (n : NormalForm X),
      inferQualifiedTotal sig X A Γ e s = some r ∧
      N.normalize r.canonicalConstraint = some n ∧
      n.IsPrincipal N.solved r.canonicalConstraint ∧
      n.SoundFor r.canonicalConstraint ∧
      ∀ (C : Constraint X) (τ : Ty) (ε : Effect),
        Typing sig X C Γ e τ ε →
        (n.reconstruct r.canonical).MoreGeneralThan Γ
          (.and (assumptions A) C) τ ε := by
  obtain ⟨r, hr, w, hw⟩ := h₀.inferQualifiedTotal_realizable
    hRename hSupport hFVRename hSigClosed A Γ e s v hv
  have hcanon := r.extendResult_solution hSupport w hw
  obtain ⟨R, hR, hvalid⟩ := hTrue
  have hform : ∃ n : NormalForm X,
      n.IsNormalForm N.solved r.canonicalConstraint :=
    ⟨NormalForm.groundWith R (r.extendResult w),
      hR, NormalForm.groundWith_soundFor _ _ _ hcanon⟩
  have hnotnone : N.normalize r.canonicalConstraint ≠ none := by
    intro hn
    exact (N.fail_iff_no_normal_form _).mp hn hform
  cases hn : N.normalize r.canonicalConstraint with
  | none => exact False.elim (hnotnone hn)
  | some n =>
      obtain ⟨hp, hs, hq⟩ := h₀.inferQualifiedTotal_with_principal_normalForm
        hRename hSupport hFVRename hSigClosed N
        ⟨R, hR, hvalid⟩
        A Γ hΓClosed e s r n hr hn
      exact ⟨r, n, hr, hn, hp, hs, hq⟩

end SystemFXi.EHMX
