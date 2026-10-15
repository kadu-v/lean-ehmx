import EHMX.HMX.ReconstructionPrincipality

/-! Direct constraint-preserving reconstruction for `S = Sat_X`.
This model does not satisfy variable-equality reflection in general; these
results use generation completeness directly, not the conditional Theorem 7.
-/
namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

theorem Substitution.imageSupport_identity (u : Names) :
    (Substitution.identity T).imageSupport u = u := by
  cases u
  simp [Substitution.imageSupport, Substitution.identity, T.support_var, Effect.var]

theorem reconstructedScheme_identity (g : Context X) (d : X.Formula) :
    reconstructedScheme g ⟨d, Substitution.identity T⟩ =
      ComputationScheme.generalize g d (T.var (g.support.shiftTypes 0))
        (Effect.var (g.support.shiftEffects 0)) := by
  unfold reconstructedScheme
  rw [Substitution.imageSupport_identity]
  rfl

theorem inferTerm_satisfiable_open {sig : Signature T}
    (N : X.Simplifier) {g : Context X} {e : Expr}
    {c : X.Formula} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e s eff) (real : g.Realizable c) :
    ∃ n, inferTerm sig X N (Constraints.ScopedPrincipalNormalizer.satisfiable X) g e =
      some (.reconstructed n) ∧
      let result := reconstructedScheme g n
      ComputationTyping sig X X.Satisfiable result.outer g e result ∧
      (∀ c' s' eff', Typing sig X X.Satisfiable c' g e s' eff' → g.Realizable c' →
        X.Entails c' result.outer ∧ Instance X c' result.valueScheme s') ∧
      (∀ c' t' eff', Typing sig X X.Satisfiable c' g e (.mono t') eff' →
        g.Realizable c' → result.FiniteInstance c' t' eff') := by
  classical
  obtain ⟨d, generated, _, sat, _, comp, cover, finite⟩ :=
    typed.principal_computation_open_at N _ _ g.output_names_fresh.1 g.output_names_fresh.2 real
  refine ⟨⟨d, Substitution.identity T⟩, ?_, ?_⟩
  · simp [inferTerm, inferTermAt, generated, Constraints.ScopedPrincipalNormalizer.satisfiable, sat]
  · rw [reconstructedScheme_identity]
    exact ⟨comp, cover, finite⟩

theorem inferTerm_satisfiable_closed {sig : Signature T}
    (N : X.Simplifier) {g : Context X} {e : Expr}
    {c : X.Formula} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e s eff)
    (closed : g.support = Names.empty) (real : g.Realizable X.top) :
    ∃ n, inferTerm sig X N (Constraints.ScopedPrincipalNormalizer.satisfiable X) g e =
      some (.reconstructed n) ∧
      let result := reconstructedScheme g n
      X.Equivalent result.outer X.top ∧
      PrincipalComputationScheme sig X X.Satisfiable g e result ∧
      (∀ c' t' eff', Typing sig X X.Satisfiable c' g e (.mono t') eff' →
        result.FiniteInstance c' t' eff') ∧
      (∀ c' s' eff', Typing sig X X.Satisfiable c' g e s' eff' →
        Instance X c' result.valueScheme s') ∧
      (Value e → PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
        g e X.top result.valueScheme) := by
  classical
  have weakenReal c' : g.Realizable c' := real.weaken (fun v _ => (X.holds_top v).mpr trivial)
  obtain ⟨d, generated, _, sat, valid, _, _, finite⟩ :=
    typed.principal_computation_open_at N _ _ g.output_names_fresh.1 g.output_names_fresh.2 (weakenReal c)
  let n : X.NormalForm := ⟨d, Substitution.identity T⟩
  have topSat : X.Satisfiable X.top := by
    obtain ⟨v, _⟩ := sat
    exact ⟨v, (X.holds_top v).mpr trivial⟩
  have comp := valid.computation_generalize_closed closed sat ((X.admissible_satisfiable_iff _).mpr topSat)
  have allFinite c' t' eff' ht := finite c' t' eff' ht (weakenReal c')
  refine ⟨n, ?_, reconstructedScheme_outer_closed closed sat, ?_⟩
  · simp [inferTerm, inferTermAt, generated, Constraints.ScopedPrincipalNormalizer.satisfiable, sat, n]
  · change PrincipalComputationScheme sig X X.Satisfiable g e (reconstructedScheme g n) ∧ _
    dsimp [n]
    rw [reconstructedScheme_identity]
    exact ⟨⟨comp, fun c' t' eff' ht v hv => (allFinite c' t' eff' ht).ground v hv⟩,
      allFinite, fun _ _ _ ht => ht.instance_of_finite_realizable finite (weakenReal _),
      fun hv => comp.principal_value (fun _ h => h) real hv allFinite⟩

end EHMX.HMX
