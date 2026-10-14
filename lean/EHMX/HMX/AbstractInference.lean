import EHMX.HMX.AlgorithmCorrectness

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T} {X : Constraints T O}

namespace SatDecider

/-- HM(X) in constraint form: decidable satisfiability implies completeness
of the actual composed algorithm. Open environments and handlers are included;
the decider must cover the full X language, not just its handler-free fragment. -/
theorem infer_complete (D : SatDecider X) (N : X.Simplifier)
    {sig : Signature T} {g : Context X} {e : Expr}
    {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e scheme eff) (real : g.Realizable c) :
    ∃ n, infer sig X N D.solver g e = some (.solved n) :=
  EHMX.HMX.infer_complete N D.solver D.solver_complete typed real

/-- Accepted constraints type the expression in the original environment:
this solver returns the identity substitution even for open inputs. -/
theorem inferAt_sound (D : SatDecider X) (N : X.Simplifier)
    {sig : Signature T} (hsig : sig.Closed)
    {g : Context X} {e : Expr} {t : T.Term} {eff : Effect} {n : X.NormalForm}
    (run : inferAt sig X N D.solver g e t eff = some (.solved n))
    (real : g.Realizable X.top) (admissible : g.Admissible X.Satisfiable) :
    Typing sig X X.Satisfiable n.residual g e (.mono t) eff := by
  obtain ⟨d, generated, solved⟩ := Option.map_eq_some_iff.mp run
  obtain ⟨sat, rfl⟩ := (D.solver_solved_iff X.top d n).mp solved
  apply Typing.of_ground N admissible
    (by obtain ⟨v, hv⟩ := sat; exact ⟨v, ((X.holds_and _ _ _).mp hv).2⟩)
  intro v hv
  exact (generateProjected_ground_iff N hsig generated v
    (real.ground ((X.holds_top v).mpr trivial))).mp hv

/-- The actual entry point is sound without transporting the environment. -/
theorem infer_sound (D : SatDecider X) (N : X.Simplifier)
    {sig : Signature T} (hsig : sig.Closed)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (run : infer sig X N D.solver g e = some (.solved n))
    (real : g.Realizable X.top) (admissible : g.Admissible X.Satisfiable) :
    Typing sig X X.Satisfiable n.residual g e
      (.mono (T.var (g.support.shiftTypes 0))) (Effect.var (g.support.shiftEffects 0)) :=
  D.inferAt_sound N hsig run real admissible

/-- Typability guarantees an actual principal output, not merely principality
conditional on success. No `PartialSolver.Complete` hypothesis is supplied.
Computations use qualified computation schemes; values additionally have the
existing principal-pair guarantee. Generalization retains the value restriction. -/
theorem infer_principal (D : SatDecider X) (N : X.Simplifier)
    {sig : Signature T} (hsig : sig.Closed)
    {g : Context X} {e : Expr} {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (closed : g.support = Names.empty) (real : g.Realizable X.top)
    (typed : Typing sig X X.Satisfiable c g e scheme eff) :
    ∃ n, infer sig X N D.solver g e = some (.solved n) ∧
      PrincipalComputationScheme sig X X.Satisfiable g e (inferredScheme g n) ∧
      (∀ c' t' eff', Typing sig X X.Satisfiable c' g e (.mono t') eff' →
        (inferredScheme g n).FiniteInstance c' t' eff') ∧
      (Value e → PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
        g e X.top (.qualified (inferredScheme g n).bound
          (inferredScheme g n).condition (inferredScheme g n).result)) := by
  have realC : g.Realizable c := real.weaken (fun v _ => (X.holds_top v).mpr trivial)
  obtain ⟨n, run⟩ := D.infer_complete N typed realC
  exact ⟨n, run, EHMX.HMX.infer_principal_closed N D.solver hsig
    closed real typed.root.2.1 run⟩

/-- Structural failure is separate from constraint inconsistency; neither is
reported as an unresolved constraint by this composed algorithm. -/
theorem infer_ne_unresolved (D : SatDecider X) (N : X.Simplifier)
    (sig : Signature T) (g : Context X) (e : Expr) (r : X.Formula) :
    infer sig X N D.solver g e ≠ some (.unresolved r) := by
  intro run
  obtain ⟨d, _, solved⟩ := Option.map_eq_some_iff.mp run
  exact D.solver_ne_unresolved X.top d r solved

end SatDecider
end EHMX.HMX
