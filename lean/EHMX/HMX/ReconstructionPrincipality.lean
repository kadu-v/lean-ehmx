import EHMX.HMX.ReconstructionCompleteness

/-! Corollary 7 for actual reconstruction outputs. Computation schemes cover
arbitrary expressions; ordinary polymorphic typing retains the value restriction.
All soundness and comparison judgments use the same solved set. -/
namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

/-- A closed context may be renamed by capture-avoiding substitution, but it
still approximates the original context. No syntactic equality is required. -/
theorem Context.subst_approximates_closed
    {S : X.Formula → Prop} {c : X.Formula} {g : Context X}
    (closed : g.support = Names.empty) (adm : g.Admissible S)
    (real : g.Realizable c) (σ : Substitution T) :
    (g.subst σ).Approximates S c g := by
  have avoids : g.Avoids σ.domain := g.avoids_of_support_disjoint σ.domain (by
    rw [closed]
    exact ⟨Finset.disjoint_empty_right _, Finset.disjoint_empty_right _⟩)
  apply Context.Approximates.subst_congr (Substitution.identity T) σ _ _
    (Context.Approximates.subst_identity (Context.Approximates.refl adm real))
  · intro s hs v i hi
    rw [Substitution.identity_pullback]
    exact ((σ.pullback_outside v).1 i (fun h => (avoids s hs).1 i h hi)).symm
  · intro s hs v i hi
    rw [Substitution.identity_pullback]
    exact ((σ.pullback_outside v).2 i (fun h => (avoids s hs).2 i h hi)).symm

theorem reconstructedScheme_eq_generalize_closed
    (g : Context X) (n : X.NormalForm) (closed : g.support = Names.empty) :
    reconstructedScheme g n = ComputationScheme.generalize g n.residual
      (reconstructedScheme g n).result (reconstructedScheme g n).effect := by
  simp [reconstructedScheme, ComputationScheme.generalizeWithSupport,
    ComputationScheme.generalize, Substitution.imageSupport, closed, Names.empty]

theorem reconstructedScheme_outer_closed {g : Context X} {n : X.NormalForm}
    (closed : g.support = Names.empty) (sat : X.Satisfiable n.residual) :
    X.Equivalent (reconstructedScheme g n).outer X.top := by
  refine ⟨fun v _ => (X.holds_top v).mpr trivial, ?_⟩
  intro v _
  obtain ⟨w, hw⟩ := sat
  obtain ⟨u, hu, hr, _, _⟩ := ComputationScheme.generalize_closed_instance g n.residual
    (reconstructedScheme g n).result (reconstructedScheme g n).effect closed w hw v
  have eq := reconstructedScheme_eq_generalize_closed g n closed
  rw [eq]
  exact (X.holds_exists _ _ _).mpr ⟨u, hu, hr⟩

end EHMX.HMX
namespace EHMX.HMX
open EHMX EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}
theorem inferTerm_finite_closed {sig : Signature T}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (closure : X.SolvedClosure P.solved) {g : Context X} {e : Expr} {n : X.NormalForm}
    (run : inferTerm sig X N P g e = some (.reconstructed n))
    (closed : g.support = Names.empty) (real : g.Realizable X.top)
    {c : X.Formula} {t : T.Term} {eff : Effect}
    (typed : Typing sig X P.solved c g e (.mono t) eff) :
    (reconstructedScheme g n).FiniteInstance c t eff := by
  have ground (v : Valuation T.Value) (hv : X.holds c v) :
      GroundTyping sig O (g.ground ((Substitution.identity T).pullback v)) e
        (T.eval v t) (eff.eval v.effects) := by
    obtain ⟨tree, _⟩ := typed
    simpa only [Substitution.identity_pullback] using
      tree.ground v hv (real.ground ((X.holds_top v).mpr trivial)) _ (O.refl _)
  obtain ⟨m, hm, φ, _, residual, images⟩ :=
    inferTerm_complete_mono_of_ground N P closure (Substitution.identity T) typed.root.1 ground
  have eq : m = n := by rw [run] at hm; exact (Option.some.inj hm).symm |> ReconstructionResult.reconstructed.inj
  subst m
  rw [reconstructedScheme_eq_generalize_closed g n closed]
  apply ComputationScheme.generalize_finite g _ _ _ closed φ
  intro v hv
  exact ⟨(X.holds_subst _ _ _).mp (residual v hv),
    (images v hv).1.symm ▸ O.refl _, (images v hv).2⟩

/-- Completeness alone yields acceptance of any qualified typing in the original
context. This avoids assuming that identity substitution is syntactic identity. -/
theorem inferTerm_acceptance_context {sig : Signature T}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (closure : X.SolvedClosure P.solved) {g : Context X} {e : Expr}
    {c : X.Formula} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X P.solved c g e s eff) (real : g.Realizable c) :
    ∃ n, inferTerm sig X N P g e = some (.reconstructed n) := by
  obtain ⟨d, t, _, mono, real'⟩ := typed.mono_strengthening P.solved_satisfiable closure real
  obtain ⟨n, run, _⟩ := inferTerm_complete_mono_of_ground N P closure
    (Substitution.identity T) mono.root.1 (fun v hv => by
      obtain ⟨tree, _⟩ := mono
      simpa only [Substitution.identity_pullback] using
        tree.ground v hv (real'.ground hv) _ (O.refl _))
  exact ⟨n, run⟩

end EHMX.HMX

namespace EHMX.HMX
open EHMX EHMX.HMX
variable {O : TypeOrder equalityTypes} {X : Constraints equalityTypes O}

/-- Corollary 7 for a fixed successful run. All conclusions use the original
closed context and the same solved set; the comparison includes all derivations. -/
theorem inferTerm_principal_closed {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (cl : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hsig : sig.Closed)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (run : inferTerm sig X N P g e = some (.reconstructed n))
    (closed : g.support = Names.empty) (adm : g.Admissible P.solved)
    (real : g.Realizable X.top) :
    let result := reconstructedScheme g n
    X.Equivalent result.outer X.top ∧
    PrincipalComputationScheme sig X P.solved g e result ∧
    (∀ c t eff, Typing sig X P.solved c g e (.mono t) eff →
      result.FiniteInstance c t eff) ∧
    (∀ c s eff, Typing sig X P.solved c g e s eff →
      Instance X c result.valueScheme s) ∧
    (Value e → PrincipalPair (fun c g e s => Typing sig X P.solved c g e s ∅)
      g e X.top result.valueScheme) := by
  dsimp only
  have env := g.subst_approximates_closed (c := n.residual) closed adm
    (real.weaken (fun v _ => (X.holds_top v).mpr trivial)) n.substitution
  have typed : Typing sig X P.solved n.residual g e
      (.mono (reconstructedScheme g n).result) (reconstructedScheme g n).effect := by
    simpa [reconstructedScheme, ComputationScheme.generalizeWithSupport,
      Substitution.apply, Ty.subst, Effect.subst, Effect.var] using
      inferTermAt_sound_of_approximation N P cl reflect allow lift hr truth hsig run env
  obtain ⟨d, _, normalized, _⟩ := inferTermAt_normal run
  have sat := (P.sound (reconstructionScope_covers X g _ _ d) normalized).2.1
  have outer := reconstructedScheme_outer_closed closed sat
  have topAdm : X.Admissible P.solved X.top :=
    ⟨r, hr, fun v _ => truth v, fun v _ => (X.holds_top v).mpr trivial⟩
  have comp : ComputationTyping sig X P.solved X.top g e (reconstructedScheme g n) := by
    have h := typed.computation_generalize_closed closed sat topAdm
    rw [← reconstructedScheme_eq_generalize_closed g n closed] at h
    exact h
  have finite := fun c t eff (ht : Typing sig X P.solved c g e (.mono t) eff) =>
    inferTerm_finite_closed N P cl run closed real ht
  exact ⟨outer, ⟨comp, fun c t eff ht v hv => (finite c t eff ht).ground v hv⟩,
    finite, fun _ _ _ ht => ht.instance_of_finite_sameSolved
      P.solved_satisfiable cl.rename cl.conjoin real finite,
    fun hv => comp.principal_value_sameSolved P.solved_satisfiable
      cl.rename cl.conjoin real hv finite⟩

/-- A typable closed judgment has an actual reconstruction output with all the
principal-computation and qualified-comparison guarantees of Corollary 7.
Ordinary polymorphic typing of that output is asserted only for values. -/
theorem Typing.corollary7 {sig : Signature equalityTypes}
    (N : X.Simplifier) (P : X.ScopedPrincipalNormalizer)
    (cl : X.SolvedClosure P.solved)
    (reflect : EHMX.HMX.EffectResidualNormalization.VariableEqualityReflection (X := X) P.solved)
    (allow : ∀ (r : X.Formula) (s : Substitution equalityTypes), s.domain.types = ∅ →
      X.Admissible P.solved r → X.Satisfiable (X.and r (X.substitutionConstraint s)) →
      X.Admissible P.solved (X.and r (X.substitutionConstraint s)))
    (lift : ∀ (a : Names) (d : X.Formula),
      X.Admissible P.solved (X.existsNames a d) →
      ∃ θ : Substitution equalityTypes, θ.domain.Subset a ∧
        X.Admissible P.solved (X.subst θ d))
    {r : X.Formula} (hr : P.solved r) (truth : ∀ v, X.holds r v)
    (hsig : sig.Closed)
    {g : Context X} {e : Expr} {s : Scheme X} {eff : Effect}
    (typed : Typing sig X P.solved X.top g e s eff)
    (closed : g.support = Names.empty) (real : g.Realizable X.top) :
    ∃ n, inferTerm sig X N P g e = some (.reconstructed n) ∧
    let result := reconstructedScheme g n
    X.Equivalent result.outer X.top ∧
    PrincipalComputationScheme sig X P.solved g e result ∧
    (∀ c t eff, Typing sig X P.solved c g e (.mono t) eff →
      result.FiniteInstance c t eff) ∧
    (∀ c s eff, Typing sig X P.solved c g e s eff →
      Instance X c result.valueScheme s) ∧
    (Value e → PrincipalPair (fun c g e s => Typing sig X P.solved c g e s ∅)
      g e X.top result.valueScheme) := by
  obtain ⟨n, run⟩ := inferTerm_acceptance_context N P cl typed real
  exact ⟨n, run, inferTerm_principal_closed N P cl reflect allow lift hr truth hsig
    run closed typed.root.2.1 real⟩

end EHMX.HMX
