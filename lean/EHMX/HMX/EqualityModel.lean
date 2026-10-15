import EHMX.HMX.Instantiation
import EHMX.HMX.ComputationSchemes
import EHMX.HMX.PartialSolving

namespace EHMX

inductive Ty where
  | var : Nat → Ty
  | base : BaseTy → Ty
  | arr : Ty → Effect → Ty → Ty
  deriving DecidableEq

def Ty.rename (ρ : Nat → Nat) (η : Nat → Nat) : Ty → Ty
  | .var i => .var (ρ i)
  | .base b => .base b
  | .arr a ε b => .arr (a.rename ρ η) (ε.rename η) (b.rename ρ η)

structure Substitution where
  types : Nat → Ty
  effects : Nat → Effect

def Ty.subst (θ : Substitution) : Ty → Ty
  | .var i => θ.types i
  | .base b => .base b
  | .arr a ε b => .arr (a.subst θ) (ε.subst θ.effects) (b.subst θ)

inductive GroundTy where
  | atom : Nat → GroundTy
  | arr : GroundTy → Finset Op → GroundTy → GroundTy
  deriving DecidableEq

structure Valuation where
  types : Nat → GroundTy
  effects : Nat → Finset Op

def Ty.eval (ρ : Valuation) : Ty → GroundTy
  | .var i => ρ.types i
  | .base .int => .atom 0
  | .base .bool => .atom 1
  | .base (.other n) => .atom (n + 2)
  | .arr a ε b => .arr (a.eval ρ) (ε.eval ρ.effects) (b.eval ρ)

def Valuation.pullbackSubst (v : Valuation) (θ : Substitution) : Valuation :=
  ⟨fun i => (θ.types i).eval v, fun i => (θ.effects i).eval v.effects⟩

theorem Ty.eval_subst (τ : Ty) (θ : Substitution) (v : Valuation) :
    (τ.subst θ).eval v = τ.eval (v.pullbackSubst θ) := by
  induction τ with
  | var i => rfl
  | base b => cases b <;> rfl
  | arr a ε b iha ihb =>
      simp [Ty.subst, Ty.eval, iha, ihb, Effect.eval_subst,
        Valuation.pullbackSubst]

def Valuation.pullback (v : Valuation) (ρ η : Nat → Nat) : Valuation :=
  ⟨v.types ∘ ρ, v.effects ∘ η⟩

theorem Effect.eval_rename (ε : Effect) (η : Nat → Nat)
    (v : Valuation) :
    (ε.rename η).eval v.effects = ε.eval (v.effects ∘ η) := by
  ext op
  simp [Effect.eval, Effect.rename, Finset.mem_biUnion,
    Finset.mem_image]

theorem Ty.eval_rename (τ : Ty) (ρ η : Nat → Nat)
    (v : Valuation) :
    (τ.rename ρ η).eval v = τ.eval (v.pullback ρ η) := by
  induction τ with
  | var i => rfl
  | base b => cases b <;> rfl
  | arr a ε b iha ihb =>
      simp [Ty.rename, Ty.eval, iha, ihb, Effect.eval_rename,
        Valuation.pullback]

def Ty.fvTypes : Ty → Finset Nat
  | .var i => {i}
  | .base _ => ∅
  | .arr a _ b => a.fvTypes ∪ b.fvTypes

def Ty.fvEffects : Ty → Finset Nat
  | .var _ => ∅
  | .base _ => ∅
  | .arr a ε b => a.fvEffects ∪ ε.vars ∪ b.fvEffects

theorem Ty.eval_support (τ : Ty) (v w : Valuation)
    (ht : ∀ i ∈ τ.fvTypes, v.types i = w.types i)
    (he : ∀ i ∈ τ.fvEffects, v.effects i = w.effects i) :
    τ.eval v = τ.eval w := by
  induction τ with
  | var i => exact ht i (by simp [Ty.fvTypes])
  | base b => cases b <;> rfl
  | arr a ε b iha ihb =>
      simp only [Ty.eval]
      congr 1
      · exact iha (by
          intro i hi
          exact ht i (by simp [Ty.fvTypes, hi]))
          (by intro i hi; exact he i (by simp [Ty.fvEffects, hi]))
      · exact Effect.eval_support ε v.effects w.effects (by
          intro i hi
          exact he i (by simp [Ty.fvEffects, hi]))
      · exact ihb (by
          intro i hi
          exact ht i (by simp [Ty.fvTypes, hi]))
          (by intro i hi; exact he i (by simp [Ty.fvEffects, hi]))

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
        Effect.eval]

end EHMX

namespace EHMX.HMX

/-- A concrete equality model for the counterexamples and ground representation. -/
abbrev equalityTypes : TypeDomain where
  Term := Ty
  Value := GroundTy
  value_nonempty := ⟨.atom 0⟩
  var := Ty.var
  literal := Ty.base
  arrow := Ty.arr
  groundLiteral := fun b => (Ty.base b).eval ⟨fun _ => .atom 0, fun _ => ∅⟩
  groundArrow := GroundTy.arr
  rename := Ty.rename
  subst := fun f g t => t.subst ⟨f, g⟩
  subst_var := by intros; rfl
  support := fun t => ⟨t.fvTypes, t.fvEffects⟩
  support_var := by intro i; rfl
  subst_eq_self := by
    intro f g t ht he
    induction t with
    | var i => exact ht i (by simp [Ty.fvTypes])
    | base b => rfl
    | arr a e b ha hb =>
        have left := ha (fun i hi => ht i (by simp [Ty.fvTypes, hi]))
          (fun i hi => he i (by simp [Ty.fvEffects, hi]))
        have right := hb (fun i hi => ht i (by simp [Ty.fvTypes, hi]))
          (fun i hi => he i (by simp [Ty.fvEffects, hi]))
        simp only [Ty.subst, left, right,
          e.subst_eq_self g (fun i hi => he i (by simp [Ty.fvEffects, hi]))]
  support_subst_avoids := by
    intro f g t a ht he
    induction t with
    | var i => exact ht i (by simp [Ty.fvTypes])
    | base b => simp [Ty.subst, Ty.fvTypes, Ty.fvEffects, Names.Disjoint]
    | arr u e v hu hv =>
        have left := hu (fun i hi => ht i (by simp [Ty.fvTypes, hi]))
          (fun i hi => he i (by simp [Ty.fvEffects, hi]))
        have right := hv (fun i hi => ht i (by simp [Ty.fvTypes, hi]))
          (fun i hi => he i (by simp [Ty.fvEffects, hi]))
        have eff : Disjoint a.effects (e.subst g).vars := by
          apply Finset.disjoint_left.mpr
          intro i hi hj
          obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hj
          exact Finset.disjoint_left.mp (he j (by simp [Ty.fvEffects, hj])) hi hij
        exact ⟨Finset.disjoint_union_right.mpr ⟨left.1, right.1⟩,
          Finset.disjoint_union_right.mpr
            ⟨Finset.disjoint_union_right.mpr ⟨left.2, eff⟩, right.2⟩⟩
  eval := fun v t => t.eval ⟨v.types, v.effects⟩
  eval_var := by intros; rfl
  eval_literal := by intro v b; cases b <;> rfl
  eval_arrow := by intros; rfl
  eval_rename := by intro v f g t; exact t.eval_rename f g ⟨v.types, v.effects⟩
  eval_subst := by intro v f g t; exact t.eval_subst ⟨f, g⟩ ⟨v.types, v.effects⟩
  eval_support := by
    intro v w t h
    exact t.eval_support ⟨v.types, v.effects⟩ ⟨w.types, w.effects⟩ h.1 h.2

end EHMX.HMX

namespace EHMX.HMX
namespace ApproximationExample

private abbrev X := Constraints.semantic equalityTypes (TypeOrder.equality equalityTypes)
private def c : X.Formula := X.eq (.var 0) (.base .int)
private def bound : Names := ⟨{1}, ∅⟩
private def result : Ty := .arr (.var 1) ∅ (.var 1)
private def scheme : Scheme X := .qualified bound c result
private def context : Context X := []
private def signature : Signature equalityTypes := fun _ => none

private theorem condition_sat : X.Satisfiable c :=
  ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, (X.holds_eq _ _ _).mpr rfl⟩

private theorem source_typed : Typing signature X X.Satisfiable c context (.lam (.var 0)) scheme ∅ := by
  have hc := (X.admissible_satisfiable_iff _).mpr condition_sat
  have base : Typing signature X X.Satisfiable c context (.lam (.var 0)) (.mono result) ∅ :=
    ⟨.lam (.var rfl), Derivation.valid_of_satisfiable _ condition_sat (by simp [context, Context.Admissible])⟩
  exact (base.generalize (.lam (.var 0)) bound (by simp [context, Context.Avoids])
    ((X.admissible_satisfiable_iff _).mpr
      ((X.satisfiable_exists_iff bound c).mpr condition_sat))).weaken hc (X.exists_intro bound c)

private theorem source_realizable : scheme.Realizable c := by
  refine ⟨(Substitution.identity equalityTypes).apply result, .forallLeft (Substitution.identity equalityTypes)
    (by simp [Substitution.identity, Names.empty])
    (by simp [Substitution.identity, Names.empty]) ?_ (.sub ?_)⟩
  · intro v hv
    simpa only [X.holds_subst, Substitution.identity_pullback] using hv
  · intro v _
    exact (X.holds_le _ _ _).mpr rfl

private theorem no_global_instance (target : Scheme X) : ¬ Instance X X.top scheme target := by
  intro h
  let v : Valuation equalityTypes.Value := ⟨fun _ => .atom 1, fun _ => ∅⟩
  have hv := (X.holds_top v).mpr trivial
  obtain ⟨u, hu⟩ := h.target_nonempty hv
  obtain ⟨w, hw, hc, _⟩ := h.groundInstance hv hu
  have hzero := hw.1 0 (by simp [bound])
  have he := (X.holds_eq _ _ _).mp hc
  change w.types 0 = GroundTy.atom 0 at he
  change w.types 0 = GroundTy.atom 1 at hzero
  have := GroundTy.atom.inj (he.symm.trans hzero)
  contradiction

/-- The repaired approximation covers the identity example; the unconditional
comparison still fails. No projection or effect rule is used. -/
theorem relative_approximation :
    ∃ (Y : Constraints equalityTypes (TypeOrder.equality equalityTypes))
      (d : Y.Formula) (g : Context Y) (s : Scheme Y),
      (∀ a q, Y.Admissible Y.Satisfiable q → Y.Admissible Y.Satisfiable (Y.existsNames a q)) ∧
      Y.Admissible Y.Satisfiable d ∧ g.Admissible Y.Satisfiable ∧
      List.Forall₂ (Scheme.Approximates Y.Satisfiable d) g g ∧
      Typing (fun _ => none) Y Y.Satisfiable d g (.lam (.var 0)) s ∅ ∧
      s.Realizable d ∧ s.Approximates Y.Satisfiable d s ∧
      ¬ ∃ target, Instance Y Y.top s target := by
  refine ⟨X, c, context, scheme, ?_,
    (X.admissible_satisfiable_iff _).mpr condition_sat, ?_, ?_, source_typed, source_realizable,
    Scheme.Approximates.refl ((X.admissible_satisfiable_iff _).mpr condition_sat) source_realizable, ?_⟩
  · intro a q hq
    exact (X.admissible_satisfiable_iff _).mpr ((X.satisfiable_exists_iff a q).mpr
      ((X.admissible_satisfiable_iff _).mp hq))
  · simp [context, Context.Admissible, Scheme.Admissible]
  · exact .nil
  · rintro ⟨target, hi⟩
    exact no_global_instance target hi

end ApproximationExample
end EHMX.HMX

namespace EHMX.HMX.RealizabilityExample

private abbrev X := Constraints.semantic equalityTypes (TypeOrder.equality equalityTypes)
private def bound : Names := ⟨{1}, ∅⟩
private def result : Ty := .arr (.var 1) ∅ (.var 1)
private def qualifier : X.Formula := X.eq (.var 0) result
private def outer : X.Formula := X.existsNames bound qualifier
private def scheme : Scheme X := .qualified bound qualifier result

private theorem qualifier_sat : X.Satisfiable qualifier := by
  let v : Valuation GroundTy := ⟨fun i => if i = 0 then .arr (.atom 0) ∅ (.atom 0) else .atom 0,
    fun _ => ∅⟩
  refine ⟨v, (X.holds_eq _ _ _).mpr ?_⟩
  simp [result, equalityTypes, Ty.eval, Effect.eval, v]

private theorem typed :
    Typing (fun _ => none) X X.Satisfiable outer [] (.lam (.var 0)) scheme ∅ := by
  have h : Typing (fun _ => none) X X.Satisfiable qualifier [] (.lam (.var 0)) (.mono result) ∅ :=
    ⟨.lam (.var rfl), Derivation.valid_of_satisfiable _ qualifier_sat (by simp [Context.Admissible])⟩
  exact h.generalize (.lam (.var 0)) bound (by simp [Context.Avoids])
    ((X.admissible_satisfiable_iff _).mpr
      ((X.satisfiable_exists_iff bound qualifier).mpr qualifier_sat))

private theorem not_realizable : ¬ scheme.Realizable outer := by
  rintro ⟨u, hu⟩
  obtain ⟨θ, hθ, hd, _⟩ := Instance.qualified_mono_iff.mp hu
  have extract (u : GroundTy) :
      (θ.types 1).eval ⟨fun _ => .arr u ∅ u, fun _ => ∅⟩ = u := by
    let v : Valuation GroundTy := ⟨fun _ => .arr u ∅ u, fun _ => ∅⟩
    let w : Valuation GroundTy := ⟨Function.update v.types 1 u, v.effects⟩
    have hv : X.holds outer v := by
      apply (X.holds_exists bound qualifier v).mpr
      refine ⟨w, ?_, (X.holds_eq _ _ _).mpr ?_⟩
      · constructor
        · intro i hi
          have hi' : i ≠ 1 := by simpa [bound] using hi
          simp [w, hi']
        · intro i _; rfl
      · simp [w, v, result, equalityTypes, Ty.eval, Effect.eval]
    have h := (X.holds_eq _ _ _).mp ((X.holds_subst _ _ _).mp (hd v hv))
    have hzero : θ.types 0 = Ty.var 0 := θ.types_outside 0 (by
      intro h; have := hθ.1 h; simp [bound] at this)
    have h' : GroundTy.arr u ∅ u = GroundTy.arr
        ((θ.types 1).eval ⟨v.types, v.effects⟩) ∅ ((θ.types 1).eval ⟨v.types, v.effects⟩) := by
      simpa [qualifier, result, equalityTypes, Substitution.pullback, Ty.eval, hzero, v,
        Effect.eval] using h
    exact (GroundTy.arr.inj h').1.symm
  cases image : θ.types 1 with
  | var i => have bad := extract (.atom 0); simp [image, Ty.eval] at bad
  | base b =>
      have bad := extract (.arr (.atom 0) ∅ (.atom 0))
      cases b <;> simp [image, Ty.eval] at bad
  | arr x e y => have bad := extract (.atom 0); simp [image, Ty.eval] at bad

/-- Validity does not make every
let-bound scheme uniformly realizable. The example uses only value
generalization and an unused value let, not handlers or `existsIntro`.
It refutes that intermediate implication, not the transformation theorem. -/
theorem valid_let_without_realizable_scheme :
    ∃ (Y : Constraints equalityTypes (TypeOrder.equality equalityTypes))
      (c : Y.Formula) (s : Scheme Y),
      Typing (fun _ => none) Y Y.Satisfiable c [] (.lam (.var 0)) s ∅ ∧
      ¬ s.Realizable c ∧
      Typing (fun _ => none) Y Y.Satisfiable c []
        (.letE (.lam (.var 0)) (.int 0)) (.mono (.base .int)) ∅ := by
  refine ⟨X, outer, scheme,
    typed, not_realizable, ?_⟩
  have root := typed.root
  obtain ⟨tree, valid⟩ := typed
  exact ⟨.letVal (.lam (.var 0)) tree (.int 0), root.1, root.2.1, trivial,
    valid, root.1, Context.admissible_cons root.2.1 root.2.2, trivial, trivial⟩

private def assign (i : Nat) (t : Ty) : Substitution equalityTypes where
  domain := ⟨{i}, ∅⟩
  types := fun k => if k = i then t else .var k
  effects := Effect.var
  types_outside := by intro k hk; simp only [Finset.mem_singleton] at hk; simp [hk]
  effects_outside := fun _ _ => rfl

private theorem assign_solved (i : Nat) (t : Ty) (hi : i ∉ t.fvTypes) :
    (assign i t).Solved := by
  constructor
  · intro k hk
    have hki : k = i := by simpa [assign] using hk
    subst k
    simp [assign, Names.Disjoint, equalityTypes, hi]
  · intro k hk; simp [assign] at hk

private theorem projected_typed :
    Typing (fun _ => none) X X.Satisfiable outer []
      (.lam (.var 0)) (.mono (.var 0)) ∅ := by
  have comparison : X.Entails qualifier (X.le result (.var 0)) := by
    intro v hv
    exact (X.holds_le _ _ _).mpr ((X.holds_eq _ _ _).mp hv).symm
  let source : Derivation (fun _ => none) X qualifier []
      (.lam (.var 0)) (.mono (.var 0)) ∅ := .sub (.lam (.var rfl)) comparison
  let tree := source.existsIntro (a := bound) (by simp [Context.Avoids])
    (by simp [Scheme.Avoids, Scheme.FreeType, Scheme.FreeEffect, bound,
      Ty.fvTypes, Ty.fvEffects]) (by simp)
  exact ⟨tree, tree.valid_of_satisfiable
    ((X.satisfiable_exists_iff bound qualifier).mpr qualifier_sat)
    (by simp [Context.Admissible])⟩

/-- The extra projection rule can hide a type witness that no finite
substitution supplies uniformly. This does not refute projection closure of
admissibility: it separates semantic witnesses from term witnesses. -/
theorem projection_without_uniform_witness :
    ∃ (Y : Constraints equalityTypes (TypeOrder.equality equalityTypes))
      (a : Names) (d : Y.Formula) (t : Ty),
      (Scheme.mono (X := Y) t).Avoids a ∧
      Typing (fun _ => none) Y Y.Satisfiable (Y.existsNames a d) []
        (.lam (.var 0)) (.mono t) ∅ ∧
      ¬ ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        Y.Entails (Y.existsNames a d) (Y.subst θ d) := by
  have fresh : (Scheme.mono (X := X) (.var 0)).Avoids bound := by
    simp [Scheme.Avoids, Scheme.FreeType, Scheme.FreeEffect, bound, Ty.fvTypes,
      Ty.fvEffects]
  refine ⟨X, bound, qualifier, .var 0, fresh, ?_, ?_⟩
  · exact projected_typed
  · rintro ⟨θ, scope, entails⟩
    apply not_realizable
    exact ⟨θ.apply result, .forallLeft θ scope.1 scope.2 entails
      (.sub (fun v _ => (X.holds_le _ _ _).mpr rfl))⟩


private def tautologies (c : X.Formula) : Prop := ∀ v, X.holds c v

private def projectedNormal : X.NormalForm := ⟨X.top, assign 0 result⟩

private theorem projectedNormal_normal : projectedNormal.IsNormal tautologies outer := by
  refine ⟨fun v => (X.holds_top v).mpr trivial,
    assign_solved _ _ (by simp [result, Ty.fvTypes]), ⟨?_, ?_⟩, ?_⟩
  · intro v _; exact (X.holds_top v).mpr trivial
  · intro v _; exact (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial)
  · intro v hv
    have ht := ((X.holds_substitutionConstraint _ v).mp
      ((X.holds_and _ _ v).mp hv).2).1 0 (by simp [projectedNormal, assign])
    apply X.exists_intro bound qualifier v
    apply (X.holds_eq _ _ _).mpr
    simpa [projectedNormal, assign, qualifier, equalityTypes, Ty.eval] using ht

/-- The projected diagonal-arrow constraint has a scoped principal normal form
when solved constraints are tautologies. This is a local principal form, not a
global normalizer for the entire semantic constraint language. -/
private theorem projectedNormal_principal :
    projectedNormal.IsPrincipalOn ⟨{0}, ∅⟩ tautologies outer := by
  refine ⟨projectedNormal_normal, ?_⟩
  intro m hm
  have shape (v : Valuation GroundTy) :
      ∃ z, equalityTypes.eval v (m.substitution.types 0) = GroundTy.arr z ∅ z := by
    have h := (X.holds_subst _ _ _).mp
      (Constraints.NormalForm.reconstruct_entails X hm v (hm.1 v))
    obtain ⟨w, hw, hq⟩ := (X.holds_exists bound qualifier _).mp h
    have zero := hw.1 0 (by simp [bound])
    have equation := (X.holds_eq _ _ _).mp hq
    refine ⟨w.types 1, ?_⟩
    simpa [result, equalityTypes, Ty.eval, Effect.eval, zero, Substitution.pullback]
      using equation
  cases img : m.substitution.types 0 with
  | var i =>
      obtain ⟨z, hz⟩ := shape ⟨fun _ => .atom 0, fun _ => ∅⟩
      simp [img, equalityTypes, Ty.eval] at hz
  | base b =>
      obtain ⟨z, hz⟩ := shape ⟨fun _ => .atom 0, fun _ => ∅⟩
      cases b <;> simp [img, equalityTypes, Ty.eval] at hz
  | arr a eff b =>
      refine ⟨assign 1 a, ?_⟩
      intro v hv
      constructor
      ·
        constructor
        · intro i hi
          have hi0 : i = 0 := by simpa using hi
          subst i
          obtain ⟨z, hz⟩ := shape v
          change (m.substitution.types 0).eval ⟨v.types, v.effects⟩ = _ at hz
          rw [img] at hz
          obtain ⟨ha, he, hb⟩ := GroundTy.arr.inj hz
          simp [projectedNormal, assign, result, Substitution.pullback, img,
            equalityTypes, Ty.eval, Effect.eval, ha, hb]
          exact he.symm
        · intro i hi; simp at hi
      · exact (X.holds_top _).mpr trivial

/-- Scoped principality does not imply coverage of all satisfiability-based
monotypes by uniform finite instances. Ground coverage still holds. The target
constraint is not admissible in the chosen solved set, so this does not refute
same-solved-set principality or assume a global normalizer. -/
theorem scoped_principal_does_not_cover_all_satisfiable_typings :
    ∃ (Y : Constraints equalityTypes (TypeOrder.equality equalityTypes))
      (solved : Y.Formula → Prop) (c : Y.Formula) (n : Y.NormalForm)
      (s : ComputationScheme Y),
      (∀ d, solved d → Y.Satisfiable d) ∧
      (Y.freeNames c).Subset ⟨{0}, ∅⟩ ∧
      n.IsPrincipalOn ⟨{0}, ∅⟩ solved c ∧
      s = ComputationScheme.generalize [] n.residual (n.substitution.types 0) ∅ ∧
      ¬ Y.Admissible solved c ∧
      Typing (fun _ => none) Y Y.Satisfiable c [] (.lam (.var 0)) (.mono (.var 0)) ∅ ∧
      (∀ v, Y.holds c v → s.GroundInstance v (v.types 0) ∅) ∧
      (∀ b : BaseTy, s.FiniteInstance Y.top (.arr (.base b) ∅ (.base b)) ∅) ∧
      ¬ s.FiniteInstance c (.var 0) ∅ := by
  let s : ComputationScheme X := ⟨bound, X.top, result, ∅⟩
  have topSupport : X.support X.top = Names.empty := rfl
  have inputScope : (X.freeNames outer).Subset ⟨{0}, ∅⟩ := by
    have implementationSupport : X.support outer = ⟨{0, 1}, ∅⟩ := by
      decide
    constructor
    · intro i hi
      have member := X.freeType_mem_support ((X.mem_freeNames_types outer i).mp hi)
      have hidden := X.freeNames_exists_disjoint bound qualifier
      rw [implementationSupport] at member
      have notHidden : i ≠ 1 := by
        intro eq
        subst i
        exact Finset.disjoint_left.mp hidden.1 (by simp [bound]) hi
      simpa [notHidden] using member
    · intro i hi
      have member := X.freeEffect_mem_support ((X.mem_freeNames_effects outer i).mp hi)
      simp [implementationSupport] at member
  refine ⟨X, tautologies, outer, projectedNormal, s,
    (fun d hd => ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, hd _⟩),
    inputScope, projectedNormal_principal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s, projectedNormal, ComputationScheme.generalize, Context.support,
      assign, result, bound, topSupport, Names.union, Names.diff, Names.empty,
      equalityTypes, Ty.fvTypes, Ty.fvEffects, Effect.vars_empty]
  · rintro ⟨d, hd, _, back⟩
    let v : Valuation GroundTy := ⟨fun _ => .atom 0, fun _ => ∅⟩
    obtain ⟨w, hw, hq⟩ := (X.holds_exists bound qualifier v).mp (back v (hd v))
    have zero := hw.1 0 (by simp [bound])
    have equation := (X.holds_eq _ _ _).mp hq
    simp [result, equalityTypes, Ty.eval, Effect.eval, zero, v] at equation
  · exact projected_typed
  · intro v hv
    obtain ⟨w, hw, hq⟩ := (X.holds_exists bound qualifier v).mp hv
    refine ⟨w, hw, (X.holds_top w).mpr trivial, ?_, ?_⟩
    · have zero := hw.1 0 (by simp [bound])
      have equation := (X.holds_eq _ _ _).mp hq
      change result.eval ⟨w.types, w.effects⟩ = v.types 0
      exact equation.symm.trans zero
    · simp [s, Effect.eval]
  · intro b
    let σ := assign 0 (.arr (.base b) ∅ (.base b))
    have solves : X.Entails X.top (X.subst σ outer) := by
      intro v _
      apply (X.holds_subst _ _ _).mpr
      let w : Valuation GroundTy :=
        ⟨Function.update (σ.pullback v).types 1 (equalityTypes.groundLiteral b), v.effects⟩
      apply (X.holds_exists bound qualifier _).mpr
      refine ⟨w, ?_, (X.holds_eq _ _ _).mpr ?_⟩
      · constructor
        · intro i hi
          have hi' : i ≠ 1 := by simpa [bound] using hi
          simp [w, hi']
        · intro i _; simp [w, σ, assign, Substitution.pullback, Effect.eval, Effect.var]
      · cases b <;> simp [w, σ, assign, Substitution.pullback, result,
          equalityTypes, Ty.eval, Effect.eval]
    have invariant : X.Equivalent (X.subst σ X.top) X.top :=
      ⟨fun v _ => (X.holds_top v).mpr trivial,
        fun v _ => (X.holds_subst _ _ _).mpr ((X.holds_top _).mpr trivial)⟩
    have h := ComputationScheme.generalize_finite_of_admissible_substitution
      (X := X) [] rfl projectedNormal_principal
      ⟨X.top, (fun v => (X.holds_top v).mpr trivial), X.entails_refl _, X.entails_refl _⟩
      σ (assign_solved _ _ (by simp [Ty.fvTypes])) invariant solves (.var 0) ∅
      (by simp [Ty.fvTypes, Ty.fvEffects, Names.Subset]) (by simp)
    have emptySubst (θ : Nat → Effect) : (∅ : Effect).subst θ = ∅ :=
      Effect.subst_eq_self _ _ (by simp)
    rw [emptySubst, emptySubst] at h
    change (ComputationScheme.generalize [] X.top result ∅).FiniteInstance
      X.top (.arr (.base b) ∅ (.base b)) ∅ at h
    have presentation : ComputationScheme.generalize [] X.top result ∅ = s := by
      simp [s, ComputationScheme.generalize, Context.support, result, bound,
        topSupport, Names.union, Names.diff, Names.empty, equalityTypes,
        Ty.fvTypes, Ty.fvEffects]
    rwa [presentation] at h
  · rintro ⟨θ, ht, he, covered⟩
    apply not_realizable
    have entails : X.Entails outer (X.subst θ qualifier) := by
      intro v hv
      apply (X.holds_subst _ _ _).mpr
      apply (X.holds_eq _ _ _).mpr
      have zero : θ.types 0 = Ty.var 0 := θ.types_outside 0 (by
        intro hi; have := ht hi; simp [s, bound] at this)
      have eq := (covered v hv).2.1
      change result.eval ⟨(θ.pullback v).types, (θ.pullback v).effects⟩ = v.types 0 at eq
      simpa [qualifier, equalityTypes, Ty.eval, Substitution.pullback, zero] using eq.symm
    exact ⟨θ.apply result, .forallLeft θ ht he entails
      (.sub (fun v _ => (X.holds_le _ _ _).mpr rfl))⟩

end EHMX.HMX.RealizabilityExample

namespace EHMX.HMX.PartialSolverExamples

/-- This quantified obligation is valid with the witness ν = ∅. A solver
leaving it unresolved is incomplete for discharging valid constraints, not an
unsound solver and not a counterexample to constraint-generation completeness. -/
theorem quantified_effect_slack_valid {T : TypeDomain} {O : TypeOrder T}
    (X : Constraints T O) :
    ∀ v, X.holds (X.clause ⟨∅, {0}⟩ ⟨∅, {1}⟩
      (X.effectLe (Effect.var 0 ∪ Effect.var 1) (Effect.var 0))) v := by
  intro v
  apply (X.holds_clause _ _ _ v).mpr
  intro w _
  let u : Valuation T.Value := ⟨w.types, Function.update w.effects 1 ∅⟩
  refine ⟨u, ⟨fun _ _ => rfl, ?_⟩, ?_⟩
  · intro i hi
    have hi' : i ≠ 1 := by simpa using hi
    simp [u, hi']
  · apply (X.holds_effectLe _ _ u).mpr
    simp [u, Effect.eval, Effect.var]

private abbrev X := Constraints.semantic equalityTypes (TypeOrder.equality equalityTypes)

/-- The built-in Eq instance interpretation used by the Rust example. -/
private def eqPredicate : X.Formula :=
  Constraints.semanticAtom equalityTypes (TypeOrder.equality equalityTypes) ⟨{0}, ∅⟩
    (fun v => v.types 0 = .atom 0 ∨ v.types 0 = .atom 1)
    (by intro v w h; rw [h.1 0 (by simp)])

private def eqScheme : Scheme X := .qualified ⟨{0}, ∅⟩ eqPredicate
  (.arr (.var 0) ∅ (.arr (.var 0) ∅ (.base .bool)))

/-- ∃α. Eq α is valid, even though Eq α is not valid for arbitrary α. -/
theorem exists_eq_valid : ∀ v, X.holds (X.existsNames ⟨{0}, ∅⟩ eqPredicate) v := by
  intro v
  let w : Valuation GroundTy := ⟨Function.update v.types 0 (.atom 0), v.effects⟩
  apply (X.holds_exists _ _ _).mpr
  refine ⟨w, ⟨?_, fun _ _ => rfl⟩, ?_⟩
  · intro i hi
    have hi' : i ≠ 0 := by simpa using hi
    simp [w, hi']
  · change w.types 0 = .atom 0 ∨ w.types 0 = .atom 1
    simp [w]

/-- The hidden Int witness discharges the formula with the identity exported
substitution. This satisfies no-guess; it does not assign a visible alpha. -/
theorem exists_eq_guessFree (given : X.Formula) :
    (Constraints.NormalForm.mk X.top (Substitution.identity equalityTypes)).GuessFreeSolution
      given (X.existsNames ⟨{0}, ∅⟩ eqPredicate) :=
  Constraints.NormalForm.guessFree_identity
    ⟨fun v _ => exists_eq_valid v, fun v _ => (X.holds_top v).mpr trivial⟩

theorem exists_eq_independent (q : X.Formula) (fresh : X.Avoids q ⟨{0}, ∅⟩) :
    X.Equivalent (X.existsNames ⟨{0}, ∅⟩ (X.and q eqPredicate)) q :=
  Constraints.exists_independent_valid fresh exists_eq_valid

/-- In contrast, exporting alpha := Int from a visible Eq alpha is not
guess-free: the Bool instance is a countermodel to the exported equation. -/
theorem visible_eq_not_guessFree :
    ¬ (Constraints.NormalForm.mk X.top
      (Substitution.outputs (T := equalityTypes) 0 0 (.base .int) ∅)).GuessFreeSolution
        X.top eqPredicate := by
  intro h
  let v : Valuation GroundTy := ⟨fun _ => .atom 1, fun _ => ∅⟩
  have pred : X.holds eqPredicate v := Or.inr rfl
  have graph := ((X.holds_and _ _ v).mp
    (h.no_guess v ((X.holds_and _ _ v).mpr ⟨(X.holds_top v).mpr trivial, pred⟩))).2
  have eq := ((X.holds_substitutionConstraint _ v).mp graph).1 0 (by simp [Substitution.outputs])
  simp [v, Substitution.outputs, equalityTypes, Ty.eval] at eq

/-- A well-typed program corresponding to `let unused = eq in 0`.
An unresolved existential qualifier is not evidence that this term is ill typed. -/
theorem unused_eq_typable : Typing (fun _ => none) X X.Satisfiable X.top [eqScheme]
    (.letE (.var 0) (.int 0)) (.mono (.base .int)) ∅ := by
  have sat : X.Satisfiable X.top :=
    ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, (X.holds_top _).mpr trivial⟩
  have qualifier : X.Satisfiable eqPredicate :=
    ⟨⟨fun _ => .atom 0, fun _ => ∅⟩, Or.inl rfl⟩
  let tree : Derivation (fun _ => none) X X.top [eqScheme]
      (.letE (.var 0) (.int 0)) (.mono (.base .int)) ∅ :=
    .letVal (.var 0) (.var rfl) (.int 0)
  refine ⟨tree, tree.valid_of_satisfiable sat ?_⟩
  intro s hs
  have : s = eqScheme := by simpa using hs
  subst s
  exact (X.admissible_satisfiable_iff _).mpr qualifier

end EHMX.HMX.PartialSolverExamples
