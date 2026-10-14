import EHMX.HMX.Constraints
import Mathlib.Data.Finset.Sort

namespace EHMX.HMX

namespace Constraints
variable {T : TypeDomain} {O : TypeOrder T} (X : Constraints T O)

def effectEq (a b : Effect) : X.Formula := X.and (X.effectLe a b) (X.effectLe b a)

theorem holds_effectEq (a b : Effect) (v : Valuation T.Value) :
    X.holds (X.effectEq a b) v ↔ a.eval v.effects = b.eval v.effects := by
  simp [effectEq, X.holds_and, X.holds_effectLe, Finset.Subset.antisymm_iff]

def conjunction (cs : List X.Formula) : X.Formula := cs.foldr X.and X.top

theorem holds_conjunction (cs : List X.Formula) (v : Valuation T.Value) :
    X.holds (X.conjunction cs) v ↔ ∀ c ∈ cs, X.holds c v := by
  induction cs with
  | nil => simp [conjunction, X.holds_top]
  | cons c cs ih =>
      change X.holds (X.and c (X.conjunction cs)) v ↔ _
      simp [X.holds_and, ih]

/-- A finite substitution represented as a conjunction of equalities, as in
Corollary 4 of Sulzmann's dissertation (§3.6.2). -/
def substitutionConstraint (s : Substitution T) : X.Formula :=
  X.and
    (X.conjunction ((s.domain.types.sort (· ≤ ·)).map
      (fun i => X.eq (T.var i) (s.types i))))
    (X.conjunction ((s.domain.effects.sort (· ≤ ·)).map
      (fun i => X.effectEq (Effect.var i) (s.effects i))))

theorem holds_substitutionConstraint (s : Substitution T) (v : Valuation T.Value) :
    X.holds (X.substitutionConstraint s) v ↔
      (∀ i ∈ s.domain.types, v.types i = T.eval v (s.types i)) ∧
      (∀ i ∈ s.domain.effects, v.effects i = (s.effects i).eval v.effects) := by
  simp [substitutionConstraint, X.holds_and, X.holds_conjunction,
    X.holds_eq, X.holds_effectEq, T.eval_var, Effect.eval, Effect.var]

/-- A residual constraint and a finite substitution. -/
structure NormalForm where
  residual : X.Formula
  substitution : Substitution T

/-- Dissertation Definition 22: a constraint invariant under its substitution. -/
structure ConstraintProblem extends X.NormalForm where
  substitution_solved : substitution.Solved
  invariant : X.Equivalent (X.subst substitution residual) residual

def ConstraintProblem.initial (d : X.Formula) : X.ConstraintProblem where
  residual := d
  substitution := Substitution.identity T
  substitution_solved := Substitution.identity_solved T
  invariant := by
    constructor <;> intro v h <;>
      simpa only [X.holds_subst, Substitution.identity_pullback] using h

variable {X} in

def NormalForm.formula (n : X.NormalForm) : X.Formula :=
  X.and n.residual (X.substitutionConstraint n.substitution)

variable {X} in
def NormalForm.IsNormal (solved : X.Formula → Prop) (d : X.Formula)
    (n : X.NormalForm) : Prop :=
  solved n.residual ∧ n.substitution.Solved ∧
    X.Equivalent (X.subst n.substitution n.residual) n.residual ∧
    X.Entails n.formula d

variable {X} in
def NormalForm.MoreGeneral (n m : X.NormalForm) : Prop :=
  ∃ φ : Substitution T, φ.Solved ∧
    (∀ v, n.substitution.pullback (φ.pullback v) = m.substitution.pullback v) ∧
    X.Entails m.residual (X.subst φ n.residual)

variable {X} in
/-- Finite-observation comparison. A single finite factor must work for every
valuation, independently of the residual. Only the observed input names are
compared; output parameters may be instantiated. Unlike `MoreGeneral`, factors
here are not required to be solved. This is a candidate for the scoped interface,
not yet the comparison used by `PrincipalNormalizer`. -/
def NormalForm.MoreGeneralOn (u : Names) (n m : X.NormalForm) : Prop :=
  ∃ φ : Substitution T,
    (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn
      (m.substitution.pullback v) u) ∧
    X.Entails m.residual (X.subst φ n.residual)

theorem NormalForm.MoreGeneralOn.refl (u : Names) (n : X.NormalForm) :
    n.MoreGeneralOn u n := by
  refine ⟨Substitution.identity T, ?_, ?_⟩
  · intro v
    rw [Substitution.identity_pullback]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  · intro v hv
    exact (X.holds_subst _ _ _).mpr (by rwa [Substitution.identity_pullback])

theorem NormalForm.MoreGeneralOn.trans {u : Names} {n m k : X.NormalForm}
    (h : n.MoreGeneralOn u m) (j : m.MoreGeneralOn u k) :
    n.MoreGeneralOn u k := by
  obtain ⟨φ, factor, residual⟩ := h
  obtain ⟨ψ, factor', residual'⟩ := j
  refine ⟨ψ.compose φ, ?_, ?_⟩
  · intro v
    rw [Substitution.compose_pullback]
    exact (factor (ψ.pullback v)).trans (factor' v)
  · intro v hv
    apply (X.holds_subst _ _ _).mpr
    rw [Substitution.compose_pullback]
    exact (X.holds_subst _ _ _).mp
      (residual _ ((X.holds_subst _ _ _).mp (residual' v hv)))

theorem NormalForm.MoreGeneralOn.mono {u w : Names} {n m : X.NormalForm}
    (h : n.MoreGeneralOn u m) (hw : w.Subset u) : n.MoreGeneralOn w m := by
  obtain ⟨φ, factor, residual⟩ := h
  exact ⟨φ, fun v => (factor v).mono hw, residual⟩

theorem NormalForm.MoreGeneral.on {n m : X.NormalForm} (h : n.MoreGeneral m)
    (u : Names) : n.MoreGeneralOn u m := by
  obtain ⟨φ, _, factor, residual⟩ := h
  refine ⟨φ, ?_, residual⟩
  intro v
  rw [factor v]
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- A reversible change of output parameters gives mutual comparison. The
premises describe the observed images and residual, so no unproved syntactic
renaming law of the abstract type algebra is assumed. -/
theorem NormalForm.MoreGeneralOn.parameters {u : Names} {n m : X.NormalForm}
    (p : Renaming)
    (images : ∀ v, (n.substitution.pullback ((p.asSubstitution T).pullback v)).AgreeOn
      (m.substitution.pullback v) u)
    (residual : X.Equivalent m.residual (X.subst (p.asSubstitution T) n.residual)) :
    n.MoreGeneralOn u m ∧ m.MoreGeneralOn u n := by
  let q := p.inverse.asSubstitution T
  have inverse (v : Valuation T.Value) : (p.asSubstitution T).pullback (q.pullback v) = v := by
    cases v
    simp [q, Substitution.pullback, Renaming.asSubstitution, Renaming.inverse,
      T.eval_var, Effect.eval, Effect.var]
  refine ⟨⟨p.asSubstitution T, images, residual.1⟩, q, ?_, ?_⟩
  · intro v
    have h := images (q.pullback v)
    rw [inverse v] at h
    exact ⟨fun i hi => (h.1 i hi).symm, fun i hi => (h.2 i hi).symm⟩
  · intro v hv
    apply (X.holds_subst _ _ _).mpr
    apply residual.2
    apply (X.holds_subst _ _ _).mpr
    rwa [inverse v]

theorem NormalForm.MoreGeneral.refl (n : X.NormalForm) : n.MoreGeneral n := by
  refine ⟨Substitution.identity T, Substitution.identity_solved T, ?_, ?_⟩
  · intro v; rw [Substitution.identity_pullback]
  · intro v hv
    exact (X.holds_subst _ _ _).mpr (by rwa [Substitution.identity_pullback])

variable {X} in
def NormalForm.IsPrincipal (solved : X.Formula → Prop) (d : X.Formula)
    (n : X.NormalForm) : Prop :=
  n.IsNormal solved d ∧ ∀ m, m.IsNormal solved d → n.MoreGeneral m

variable {X} in
def NormalForm.IsPrincipalOn (u : Names) (solved : X.Formula → Prop) (d : X.Formula)
    (n : X.NormalForm) : Prop :=
  n.IsNormal solved d ∧ ∀ m, m.IsNormal solved d → n.MoreGeneralOn u m

/-- An admissible strengthening supplies an identity-substitution competitor.
Scoped principality therefore supplies one uniform finite factor fixing all
observed input values. Admissibility of the target constraint is essential;
satisfiability alone does not suffice. No closure of the solved set is used. -/
theorem NormalForm.IsPrincipalOn.factor_admissible {u : Names}
    {solved : X.Formula → Prop} {c d : X.Formula} {n : X.NormalForm}
    (hn : n.IsPrincipalOn u solved d) (hc : X.Admissible solved c)
    (entails : X.Entails c d) :
    ∃ φ : Substitution T,
      (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn v u) ∧
      X.Entails c (X.subst φ n.residual) := by
  obtain ⟨r, hr, forward, backward⟩ := hc
  let m : X.NormalForm := ⟨r, Substitution.identity T⟩
  have hm : m.IsNormal solved d := by
    refine ⟨hr, Substitution.identity_solved T, ⟨?_, ?_⟩, ?_⟩
    · intro v hv
      simpa only [m, X.holds_subst, Substitution.identity_pullback] using hv
    · intro v hv
      simpa only [m, X.holds_subst, Substitution.identity_pullback] using hv
    · intro v hv
      exact entails v (backward v ((X.holds_and _ _ v).mp hv).1)
  obtain ⟨φ, factor, residual⟩ := hn.2 m hm
  exact ⟨φ, fun v => by simpa only [m, Substitution.identity_pullback] using factor v,
    X.entails_trans forward residual⟩

variable {X} in
def NormalForm.IsNormalOf (solved : X.Formula → Prop) (p : X.ConstraintProblem)
    (n : X.NormalForm) : Prop :=
  solved n.residual ∧ n.substitution.Solved ∧
    X.Equivalent (X.subst n.substitution n.residual) n.residual ∧
    p.toNormalForm.MoreGeneral n

variable {X} in
def NormalForm.IsPrincipalOf (solved : X.Formula → Prop) (p : X.ConstraintProblem)
    (n : X.NormalForm) : Prop :=
  n.IsNormalOf solved p ∧ ∀ m, m.IsNormalOf solved p → n.MoreGeneral m

structure PrincipalNormalizer where
  solved : X.Formula → Prop
  solved_satisfiable : ∀ d, solved d → X.Satisfiable d
  normalize : X.ConstraintProblem → Option X.NormalForm
  principal : ∀ p n, normalize p = some n → n.IsPrincipalOf solved p
  failure : ∀ p, normalize p = none ↔ ¬ ∃ n : X.NormalForm, n.IsNormalOf solved p

/-- The constraint-based instance is inhabited for every constraint system.
This is an existence construction, not a satisfiability decision procedure. -/
noncomputable def PrincipalNormalizer.satisfiable : X.PrincipalNormalizer := by
  classical
  have principal (p : X.ConstraintProblem) (hp : X.Satisfiable p.residual) :
      p.toNormalForm.IsPrincipalOf X.Satisfiable p :=
    ⟨⟨hp, p.substitution_solved, p.invariant, NormalForm.MoreGeneral.refl X _⟩,
      fun _ hm => hm.2.2.2⟩
  exact {
    solved := X.Satisfiable
    solved_satisfiable := fun _ h => h
    normalize := fun p => if X.Satisfiable p.residual then some p.toNormalForm else none
    principal := by
      intro p n hn
      split at hn
      · obtain rfl := Option.some.inj hn
        exact principal p ‹X.Satisfiable p.residual›
      · contradiction
    failure := by
      intro p
      by_cases hp : X.Satisfiable p.residual
      · simp only [hp, ↓reduceIte, Option.some_ne_none, false_iff, not_not]
        exact ⟨p.toNormalForm, (principal p hp).1⟩
      · simp only [hp, ↓reduceIte, true_iff]
        rintro ⟨n, hn⟩
        obtain ⟨v, hv⟩ := hn.1
        obtain ⟨φ, _, _, he⟩ := hn.2.2.2
        exact hp ⟨φ.pullback v, (X.holds_subst _ _ _).mp (he v hv)⟩ }

/-- Applying a solved substitution makes its equality graph true. -/
theorem substitutionConstraint_pullback (s : Substitution T)
    (hs : s.Idempotent) (v : Valuation T.Value) :
    X.holds (X.substitutionConstraint s) (s.pullback v) := by
  apply (X.holds_substitutionConstraint s (s.pullback v)).mpr
  constructor
  · intro i _
    exact (congrArg (fun w => w.types i) (Substitution.idempotent_pullback hs v)).symm
  · intro i _
    exact (congrArg (fun w => w.effects i) (Substitution.idempotent_pullback hs v)).symm

theorem substitutionConstraint_fixed (s : Substitution T) (v : Valuation T.Value)
    (hv : X.holds (X.substitutionConstraint s) v) : s.pullback v = v := by
  obtain ⟨ht, he⟩ := (X.holds_substitutionConstraint s v).mp hv
  apply congrArg₂ Valuation.mk
  · funext i
    by_cases hi : i ∈ s.domain.types
    · exact (ht i hi).symm
    · simp [s.types_outside i hi, T.eval_var]
  · funext i
    by_cases hi : i ∈ s.domain.effects
    · exact (he i hi).symm
    · simp [s.effects_outside i hi, Effect.eval, Effect.var]

/-- Reorienting a variable equation preserves the entire substitution graph,
including equations whose right-hand sides mention the old representative. -/
theorem substitutionConstraint_pivot (s : Substitution T) (hs : s.Solved)
    {i j : Nat} (hi : i ∈ s.domain.types) (heq : s.types i = T.var j) :
    X.Equivalent (X.substitutionConstraint s)
      (X.substitutionConstraint (s.pivot i j heq)) := by
  have hj : j ∉ s.domain.types := by
    simpa [heq, T.support_var] using (hs.type_range i hi).1
  have fixed_iff (θ : Substitution T) (v : Valuation T.Value) :
      X.holds (X.substitutionConstraint θ) v ↔ θ.pullback v = v := by
    refine ⟨X.substitutionConstraint_fixed θ v, fun h => ?_⟩
    exact (X.holds_substitutionConstraint θ v).mpr
      ⟨fun k _ => (congrArg (fun w => w.types k) h).symm,
        fun k _ => (congrArg (fun w => w.effects k) h).symm⟩
  have same (v : Valuation T.Value) (h : v.types j = v.types i) :
      (⟨Function.update v.types j (v.types i), v.effects⟩ : Valuation T.Value) = v := by
    rw [← h, Function.update_eq_self]
  constructor
  · intro v hv
    have fixed := (fixed_iff s v).mp hv
    have equal : v.types j = v.types i := by
      simpa [Substitution.pullback, heq, T.eval_var] using
        congrArg (fun w => w.types i) fixed
    apply (fixed_iff _ v).mpr
    rw [Substitution.pivot_pullback, same v equal]
    exact fixed
  · intro v hv
    have fixed := (fixed_iff _ v).mp hv
    rw [Substitution.pivot_pullback] at fixed
    have equal : v.types j = v.types i := by
      have h := congrArg (fun w => w.types j) fixed
      simpa [Substitution.pullback, s.types_outside j hj, T.eval_var] using h.symm
    exact (fixed_iff s v).mpr (by simpa only [same v equal] using fixed)

/-- Reversing an effect alias preserves its equations, including occurrences
of that effect variable inside type images. -/
theorem substitutionConstraint_pivotEffect (s : Substitution T) (hs : s.Solved)
    {i j : Nat} (hi : i ∈ s.domain.effects) (heq : s.effects i = Effect.var j) :
    X.Equivalent (X.substitutionConstraint s)
      (X.substitutionConstraint (s.pivotEffect i j heq)) := by
  have hj : j ∉ s.domain.effects := by
    simpa [heq, Effect.var] using hs.effect_range i hi
  have fixed_iff (θ : Substitution T) (v : Valuation T.Value) :
      X.holds (X.substitutionConstraint θ) v ↔ θ.pullback v = v := by
    refine ⟨X.substitutionConstraint_fixed θ v, fun h => ?_⟩
    exact (X.holds_substitutionConstraint θ v).mpr
      ⟨fun k _ => (congrArg (fun w => w.types k) h).symm,
        fun k _ => (congrArg (fun w => w.effects k) h).symm⟩
  have same (v : Valuation T.Value) (h : v.effects j = v.effects i) :
      (⟨v.types, Function.update v.effects j (v.effects i)⟩ : Valuation T.Value) = v := by
    rw [← h, Function.update_eq_self]
  constructor
  · intro v hv
    have fixed := (fixed_iff s v).mp hv
    have equal : v.effects j = v.effects i := by
      simpa [Substitution.pullback, heq, Effect.eval, Effect.var] using
        congrArg (fun w => w.effects i) fixed
    apply (fixed_iff _ v).mpr
    rw [Substitution.pivotEffect_pullback, same v equal]
    exact fixed
  · intro v hv
    have fixed := (fixed_iff _ v).mp hv
    rw [Substitution.pivotEffect_pullback] at fixed
    have equal : v.effects j = v.effects i := by
      have h := congrArg (fun w => w.effects j) fixed
      simpa [Substitution.pullback, s.effects_outside j hj, Effect.eval, Effect.var] using h.symm
    exact (fixed_iff s v).mpr (by simpa only [same v equal] using fixed)

/-- Dissertation Lemma 4. Domain/range separation is essential: idempotence
of set-normalized effect expressions alone does not justify this equivalence. -/
theorem subst_eq_exists_graph (s : Substitution T) (hs : s.Solved) (c : X.Formula) :
    X.Equivalent (X.subst s c)
      (X.existsNames s.domain (X.and (X.substitutionConstraint s) c)) := by
  constructor
  · intro v hv
    exact (X.holds_exists _ _ v).mpr ⟨s.pullback v, s.pullback_outside v,
      (X.holds_and _ _ _).mpr ⟨X.substitutionConstraint_pullback s hs.idempotent v,
        (X.holds_subst _ _ v).mp hv⟩⟩
  · intro v hv
    obtain ⟨w, hw, h⟩ := (X.holds_exists _ _ v).mp hv
    obtain ⟨hg, hc⟩ := (X.holds_and _ _ w).mp h
    apply (X.holds_subst _ _ v).mpr
    have fixed := X.substitutionConstraint_fixed s w hg
    rwa [(hs.pullback_agreeOutside hw).symm.trans fixed]

/-- Constraint-level reconstruction soundness, before any typing theorem.
The residual-invariance condition is Definition 23 of Sulzmann's dissertation;
idempotence is Definition 6. Neither premise assumes inference correctness. -/
theorem NormalForm.reconstruct_entails
    {solved : X.Formula → Prop} {d : X.Formula} {n : X.NormalForm}
    (hn : n.IsNormal solved d) :
    X.Entails n.residual (X.subst n.substitution d) := by
  intro v hv
  apply (X.holds_subst n.substitution d v).mpr
  apply hn.2.2.2
  apply (X.holds_and _ _ _).mpr
  exact ⟨(X.holds_subst _ _ v).mp (hn.2.2.1.2 v hv),
    X.substitutionConstraint_pullback n.substitution hn.2.1.idempotent v⟩

/-- A uniformly solving, solved substitution whose target constraint is
invariant constructs a genuine competing normal form. Its residual is selected
from admissibility, not assumed to be syntactically equal to the target. -/
theorem NormalForm.IsPrincipalOn.factor_admissible_substitution {u : Names}
    {solved : X.Formula → Prop} {c d : X.Formula} {n : X.NormalForm}
    (hn : n.IsPrincipalOn u solved d) (hc : X.Admissible solved c)
    (σ : Substitution T) (hσ : σ.Solved)
    (invariant : X.Equivalent (X.subst σ c) c)
    (entails : X.Entails c (X.subst σ d)) :
    ∃ φ : Substitution T,
      (∀ v, (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) u) ∧
      X.Entails c (X.subst φ n.residual) := by
  obtain ⟨r, hr, forward, backward⟩ := hc
  let m : X.NormalForm := ⟨r, σ⟩
  have hm : m.IsNormal solved d := by
    refine ⟨hr, hσ, ⟨?_, ?_⟩, ?_⟩
    · intro v hv
      exact forward v (invariant.1 v ((X.holds_subst _ _ _).mpr
        (backward _ ((X.holds_subst _ _ _).mp hv))))
    · intro v hv
      exact (X.holds_subst _ _ _).mpr
        (forward _ ((X.holds_subst _ _ _).mp (invariant.2 v (backward v hv))))
    · intro v hv
      obtain ⟨hR, graph⟩ := (X.holds_and _ _ _).mp hv
      have hd := (X.holds_subst _ _ _).mp (entails v (backward v hR))
      rwa [X.substitutionConstraint_fixed σ v graph] at hd
  obtain ⟨φ, factor, residual⟩ := hn.2 m hm
  exact ⟨φ, factor, X.entails_trans forward residual⟩

/-- Scoped comparison covers the target solution on the observed names.
It does not equate the two presentations on their private parameters. -/
theorem NormalForm.MoreGeneralOn.covers {solved : X.Formula → Prop}
    {u : Names} {d : X.Formula} {n m : X.NormalForm}
    (h : n.MoreGeneralOn u m) (hn : n.IsNormal solved d)
    (v : Valuation T.Value) (hv : X.holds m.formula v) :
    ∃ w, X.holds n.formula w ∧ w.AgreeOn v u := by
  obtain ⟨φ, factor, residual⟩ := h
  obtain ⟨hr, hg⟩ := (X.holds_and _ _ _).mp hv
  let w := n.substitution.pullback (φ.pullback v)
  refine ⟨w, (X.holds_and _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · exact (X.holds_subst _ _ _).mp
      (hn.2.2.1.2 _ ((X.holds_subst _ _ _).mp (residual v hr)))
  · exact X.substitutionConstraint_pullback _ hn.2.1.idempotent _
  · simpa only [X.substitutionConstraint_fixed _ v hg] using factor v

/-- For a normal source the target substitution itself is a comparison factor.
Idempotence absorbs the original factor, and residual invariance transports
the residual entailment. No composition of solved substitutions is needed. -/
theorem NormalForm.MoreGeneral.canonical {solved : X.Formula → Prop}
    {d : X.Formula} {n m : X.NormalForm} (h : n.MoreGeneral m)
    (hn : n.IsNormal solved d) :
    (∀ v, n.substitution.pullback (m.substitution.pullback v) = m.substitution.pullback v) ∧
    X.Entails m.residual (X.subst m.substitution n.residual) := by
  obtain ⟨φ, _, factor, entails⟩ := h
  constructor
  · intro v
    rw [← factor v]
    exact Substitution.idempotent_pullback hn.2.1.idempotent _
  · intro v hv
    have hR := (X.holds_subst _ _ v).mp (entails v hv)
    have h := (X.holds_subst _ _ _).mp (hn.2.2.1.2 _ hR)
    exact (X.holds_subst _ _ v).mpr (by rwa [factor v] at h)

/-- Normal-form comparison is exactly unconditional implication of substitution
graphs together with implication of the full constraint presentations. The
unconditional graph implication must not be dropped. -/
theorem NormalForm.moreGeneral_iff_entails {solved : X.Formula → Prop}
    {d : X.Formula} {n m : X.NormalForm}
    (hn : n.IsNormal solved d) (hm : m.IsNormal solved d) :
    n.MoreGeneral m ↔
      X.Entails (X.substitutionConstraint m.substitution)
        (X.substitutionConstraint n.substitution) ∧ X.Entails m.formula n.formula := by
  have graph {s : Substitution T} {v : Valuation T.Value} (hs : s.pullback v = v) :
      X.holds (X.substitutionConstraint s) v := by
    apply (X.holds_substitutionConstraint _ _).mpr
    exact ⟨fun i _ => (congrArg (fun w => w.types i) hs).symm,
      fun i _ => (congrArg (fun w => w.effects i) hs).symm⟩
  constructor
  · intro h
    obtain ⟨factor, entails⟩ := h.canonical X hn
    have hg : X.Entails (X.substitutionConstraint m.substitution)
        (X.substitutionConstraint n.substitution) := by
      intro v hv
      apply graph
      simpa only [X.substitutionConstraint_fixed m.substitution v hv] using factor v
    refine ⟨hg, ?_⟩
    intro v hv
    obtain ⟨hr, hgraph⟩ := (X.holds_and _ _ _).mp hv
    have h := (X.holds_subst _ _ _).mp (entails v hr)
    rw [X.substitutionConstraint_fixed m.substitution v hgraph] at h
    exact (X.holds_and _ _ _).mpr ⟨h, hg v hgraph⟩
  · rintro ⟨hg, hf⟩
    refine ⟨m.substitution, hm.2.1, ?_, ?_⟩
    · intro v
      exact X.substitutionConstraint_fixed _ _
        (hg _ (X.substitutionConstraint_pullback _ hm.2.1.idempotent v))
    · intro v hv
      apply (X.holds_subst _ _ _).mpr
      exact ((X.holds_and _ _ _).mp (hf _ ((X.holds_and _ _ _).mpr
        ⟨(X.holds_subst _ _ _).mp (hm.2.2.1.2 v hv),
          X.substitutionConstraint_pullback _ hm.2.1.idempotent v⟩))).1

/-- Reorienting a normal form preserves principality when both its graph and
its full constraint presentation are equivalent. This reduces representative
selection to logical equivalences, without assuming a new normalizer law. -/
theorem NormalForm.IsPrincipal.replace {solved : X.Formula → Prop}
    {d : X.Formula} {n m : X.NormalForm} (hn : n.IsPrincipal solved d)
    (hm : m.IsNormal solved d)
    (graph : X.Equivalent (X.substitutionConstraint n.substitution)
      (X.substitutionConstraint m.substitution))
    (formula : X.Equivalent n.formula m.formula) : m.IsPrincipal solved d := by
  refine ⟨hm, ?_⟩
  intro k hk
  obtain ⟨hgraph, hformula⟩ := (NormalForm.moreGeneral_iff_entails X hn.1 hk).mp (hn.2 k hk)
  exact (NormalForm.moreGeneral_iff_entails X hm hk).mpr
    ⟨X.entails_trans hgraph graph.1, X.entails_trans hformula formula.1⟩

/-- Choose a new solved orientation of the same equations. The residual is
transported with that orientation, subject to the usual consistency condition
on the chosen solved set. It is not enough merely to change the substitution. -/
theorem NormalForm.IsPrincipal.reorient {solved : X.Formula → Prop}
    {d : X.Formula} {n : X.NormalForm} (hn : n.IsPrincipal solved d)
    (σ : Substitution T) (hs : σ.Solved)
    (graph : X.Equivalent (X.substitutionConstraint n.substitution)
      (X.substitutionConstraint σ))
    (consistent : X.Admissible solved (X.subst σ n.residual)) :
    ∃ m : X.NormalForm, m.IsPrincipal solved d ∧ m.substitution = σ ∧
      X.Equivalent m.residual (X.subst σ n.residual) := by
  obtain ⟨r, hr, he⟩ := consistent
  let m : X.NormalForm := ⟨r, σ⟩
  have residual (v : Valuation T.Value) : X.holds r v ↔ X.holds n.residual (σ.pullback v) :=
    ⟨fun hv => (X.holds_subst _ _ _).mp (he.2 v hv),
      fun hv => he.1 v ((X.holds_subst _ _ _).mpr hv)⟩
  have invariant : X.Equivalent (X.subst σ r) r := by
    constructor <;> intro v hv <;>
      simpa only [X.holds_subst, residual, Substitution.idempotent_pullback hs.idempotent] using hv
  have formula : X.Equivalent n.formula m.formula := by
    constructor
    · intro v hv
      obtain ⟨hR, hgraph⟩ := (X.holds_and _ _ _).mp hv
      have hg := graph.1 v hgraph
      exact (X.holds_and _ _ _).mpr ⟨(residual v).mpr
        (by rwa [X.substitutionConstraint_fixed σ v hg]), hg⟩
    · intro v hv
      obtain ⟨hR, hgraph⟩ := (X.holds_and _ _ _).mp hv
      have h := (residual v).mp hR
      rw [X.substitutionConstraint_fixed σ v hgraph] at h
      exact (X.holds_and _ _ _).mpr ⟨h, graph.2 v hgraph⟩
  have normal : m.IsNormal solved d :=
    ⟨hr, hs, invariant, X.entails_trans formula.2 hn.1.2.2.2⟩
  exact ⟨m, hn.replace X normal graph formula, rfl, he.2, he.1⟩

/-- The formula presentation is exactly the identity-input case of Definition 23. -/
theorem NormalForm.isNormalOf_initial_iff {solved : X.Formula → Prop}
    {d : X.Formula} {n : X.NormalForm} :
    n.IsNormalOf solved (ConstraintProblem.initial X d) ↔ n.IsNormal solved d := by
  constructor
  · rintro ⟨hs, hi, hinv, φ, _, hf, he⟩
    refine ⟨hs, hi, hinv, ?_⟩
    intro v hv
    obtain ⟨hr, hg⟩ := (X.holds_and _ _ _).mp hv
    have h := (X.holds_subst _ _ _).mp (he v hr)
    have hh : φ.pullback v = n.substitution.pullback v := by
      simpa only [ConstraintProblem.initial, Substitution.identity_pullback] using hf v
    rwa [hh, X.substitutionConstraint_fixed n.substitution v hg] at h
  · intro hn
    refine ⟨hn.1, hn.2.1, hn.2.2.1, n.substitution, hn.2.1, ?_, ?_⟩
    · intro v; exact Substitution.identity_pullback _
    · exact NormalForm.reconstruct_entails X hn

theorem PrincipalNormalizer.principal_initial (P : X.PrincipalNormalizer)
    {d : X.Formula} {n : X.NormalForm}
    (h : P.normalize (ConstraintProblem.initial X d) = some n) :
    n.IsPrincipal P.solved d := by
  obtain ⟨hn, hp⟩ := P.principal _ _ h
  exact ⟨(NormalForm.isNormalOf_initial_iff X).mp hn,
    fun m hm => hp m ((NormalForm.isNormalOf_initial_iff X).mpr hm)⟩

theorem PrincipalNormalizer.success_has_solution
    (N : X.PrincipalNormalizer) {d : X.Formula} {n : X.NormalForm}
    (hn : N.normalize (ConstraintProblem.initial X d) = some n) : X.Satisfiable d := by
  have hp := (N.principal_initial X hn).1
  obtain ⟨v, hv⟩ := N.solved_satisfiable n.residual hp.1
  exact ⟨n.substitution.pullback v,
    (X.holds_subst _ _ v).mp (NormalForm.reconstruct_entails X hp v hv)⟩

/-- Meaning-preserving simplification is separate from term reconstruction.
No soundness or completeness of inference is hidden in this interface. -/
structure Simplifier where
  run : X.Formula → X.Formula
  equivalent : ∀ c, X.Equivalent (run c) c

def Simplifier.identity : X.Simplifier :=
  ⟨id, fun c => ⟨X.entails_refl c, X.entails_refl c⟩⟩

end Constraints
end EHMX.HMX
