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

variable {X} in
def NormalForm.formula (n : X.NormalForm) : X.Formula :=
  X.and n.residual (X.substitutionConstraint n.substitution)

variable {X} in
def NormalForm.IsNormal (solved : X.Formula → Prop) (d : X.Formula)
    (n : X.NormalForm) : Prop :=
  solved n.residual ∧ n.substitution.Solved ∧
    X.Equivalent (X.subst n.substitution n.residual) n.residual ∧
    X.Entails n.formula d

variable {X}
namespace NormalForm
/-- One finite factor compares the observed input names under the target
residual. The same factor witnesses residual entailment for every valuation. -/
def MoreGeneralOn (u : Names) (n m : X.NormalForm) : Prop :=
  ∃ φ : Substitution T, ∀ v, X.holds m.residual v →
    (n.substitution.pullback (φ.pullback v)).AgreeOn (m.substitution.pullback v) u ∧
    X.holds n.residual (φ.pullback v)
namespace MoreGeneralOn
theorem refl (u : Names) (n : X.NormalForm) : MoreGeneralOn u n n := by
  refine ⟨Substitution.identity T, ?_⟩
  intro v hv
  rw [Substitution.identity_pullback]
  exact ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩, hv⟩
theorem trans {u : Names} {n m k : X.NormalForm}
    (h : MoreGeneralOn u n m) (j : MoreGeneralOn u m k) : MoreGeneralOn u n k := by
  obtain ⟨φ, hf⟩ := h
  obtain ⟨ψ, hg⟩ := j
  refine ⟨ψ.compose φ, ?_⟩
  intro v hv
  obtain ⟨agreeM, holdsM⟩ := hg v hv
  obtain ⟨agreeN, holdsN⟩ := hf (ψ.pullback v) holdsM
  rw [Substitution.compose_pullback]
  exact ⟨agreeN.trans agreeM, holdsN⟩
theorem mono {u w : Names} {n m : X.NormalForm}
    (h : MoreGeneralOn u n m) (hw : w.Subset u) : MoreGeneralOn w n m := by
  obtain ⟨φ, hf⟩ := h
  exact ⟨φ, fun v hv => ⟨(hf v hv).1.mono hw, (hf v hv).2⟩⟩
theorem parameters {u : Names} {n m : X.NormalForm} (p : Renaming)
    (images : ∀ v, X.holds m.residual v →
      (n.substitution.pullback ((p.asSubstitution T).pullback v)).AgreeOn
        (m.substitution.pullback v) u)
    (residual : X.Equivalent m.residual (X.subst (p.asSubstitution T) n.residual)) :
    MoreGeneralOn u n m ∧ MoreGeneralOn u m n := by
  let q := p.inverse.asSubstitution T
  have inverse (v : Valuation T.Value) :
      (p.asSubstitution T).pullback (q.pullback v) = v := by
    cases v
    simp [q, Substitution.pullback, Renaming.asSubstitution, Renaming.inverse,
      T.eval_var, EHMX.Effect.eval, EHMX.Effect.var]
  refine ⟨⟨p.asSubstitution T, fun v hv =>
    ⟨images v hv, (X.holds_subst _ _ _).mp (residual.1 v hv)⟩⟩, q, ?_⟩
  intro v hv
  have hm : X.holds m.residual (q.pullback v) := by
    apply residual.2
    apply (X.holds_subst _ _ _).mpr
    rwa [inverse]
  have h := images (q.pullback v) hm
  rw [inverse] at h
  exact ⟨⟨fun i hi => (h.1 i hi).symm, fun i hi => (h.2 i hi).symm⟩, hm⟩
theorem replace_parameters {u : Names} {n n' m m' : X.NormalForm}
    (hn : MoreGeneralOn u n n' ∧ MoreGeneralOn u n' n)
    (hm : MoreGeneralOn u m m' ∧ MoreGeneralOn u m' m) :
    MoreGeneralOn u n m ↔ MoreGeneralOn u n' m' :=
  ⟨fun h => trans (trans hn.2 h) hm.1, fun h => trans (trans hn.1 h) hm.2⟩
end MoreGeneralOn
end NormalForm
variable (X)
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
      (∀ v, X.holds c v → (n.substitution.pullback (φ.pullback v)).AgreeOn v u) ∧
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
  obtain ⟨φ, factor⟩ := hn.2 m hm
  refine ⟨φ, ?_, ?_⟩
  · intro v hv
    simpa only [m, Substitution.identity_pullback] using (factor v (forward v hv)).1
  · intro v hv
    exact (X.holds_subst _ _ _).mpr (factor v (forward v hv)).2

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
      (∀ v, X.holds c v → (n.substitution.pullback (φ.pullback v)).AgreeOn (σ.pullback v) u) ∧
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
  obtain ⟨φ, factor⟩ := hn.2 m hm
  exact ⟨φ, fun v hv => (factor v (forward v hv)).1,
    fun v hv => (X.holds_subst _ _ _).mpr (factor v (forward v hv)).2⟩

/-- Scoped comparison covers the target solution on the observed names.
It does not equate the two presentations on their private parameters. -/
theorem NormalForm.MoreGeneralOn.covers {solved : X.Formula → Prop}
    {u : Names} {d : X.Formula} {n m : X.NormalForm}
    (h : n.MoreGeneralOn u m) (hn : n.IsNormal solved d)
    (v : Valuation T.Value) (hv : X.holds m.formula v) :
    ∃ w, X.holds n.formula w ∧ w.AgreeOn v u := by
  obtain ⟨φ, factor⟩ := h
  obtain ⟨hr, hg⟩ := (X.holds_and _ _ _).mp hv
  let w := n.substitution.pullback (φ.pullback v)
  refine ⟨w, (X.holds_and _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
  · exact (X.holds_subst _ _ _).mp
      (hn.2.2.1.2 _ (factor v hr).2)
  · exact X.substitutionConstraint_pullback _ hn.2.1.idempotent _
  · simpa only [X.substitutionConstraint_fixed _ v hg] using (factor v hr).1

structure Simplifier where
  run : X.Formula → X.Formula
  equivalent : ∀ c, X.Equivalent (run c) c

def Simplifier.identity : X.Simplifier :=
  ⟨id, fun c => ⟨X.entails_refl c, X.entails_refl c⟩⟩

end Constraints
end EHMX.HMX
