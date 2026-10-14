import EHMX.HMX.OpenCompleteness
import EHMX.HMX.SolverContract

namespace EHMX.HMX
variable {T : TypeDomain} {O : TypeOrder T}

/-- Actual generation followed by the supplied solver. -/
def inferAt (sig : Signature T) (X : Constraints T O) (N : X.Simplifier)
    (S : PartialSolver X) (g : Context X) (e : Expr) (t : T.Term) (eff : Effect) :
    Option (SolveResult X) :=
  (generateProjected sig X N g e t eff).map (S.run X.top)

theorem generateProjected_sound {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (hsig : sig.Closed) {g : Context X} {e : Expr}
    {t : T.Term} {eff : Effect} {output : X.Formula}
    (run : generateProjected sig X N g e t eff = some output) :
    Inference sig X N X.top g e t eff output := by
  let fixed := (Inference.Protected X g t eff).union (X.support X.top)
  have hf : (Inference.Protected X g t eff).Subset fixed := Names.subset_union_left _ _
  change (generate sig X N e g t eff fixed).map _ = some output at run
  obtain ⟨d, generated, eq⟩ := Option.map_eq_some_iff.mp run
  rw [← eq]
  have hd := generate_sound sig X N hsig e g t eff fixed hf d generated

  let hidden := (X.support d).diff fixed
  have hdis : hidden.Disjoint fixed :=
    ⟨Finset.disjoint_left.mpr (fun _ hi => (Finset.mem_sdiff.mp hi).2),
      Finset.disjoint_left.mpr (fun _ hi => (Finset.mem_sdiff.mp hi).2)⟩
  have hgt := hdis.mono_right ((Inference.Protected.context g t eff).trans hf)
  have htt := hdis.mono_right ((Inference.Protected.type g t eff).trans hf)
  have projected : Inference sig X N X.top g e t eff (X.existsNames hidden d) :=
    hd.project (g.avoids_of_support_disjoint hidden hgt)
      ⟨fun _ hi hj => Finset.disjoint_left.mp htt.1 hi hj,
        fun _ hi hj => Finset.disjoint_left.mp htt.2 hi hj⟩
      (Finset.disjoint_left.mpr (fun _ hi hj => Finset.disjoint_left.mp hdis.2 hi
        (hf.2 (Inference.Protected.effect g t eff hj))))
      (hdis.mono_right (Names.subset_union_right _ _))
  exact projected

theorem generateProjected_ground_iff {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (hsig : sig.Closed) {g : Context X} {e : Expr}
    {t : T.Term} {eff : Effect} {d : X.Formula}
    (run : generateProjected sig X N g e t eff = some d)
    (v : Valuation T.Value) (real : g.GroundRealizable v) :
    X.holds d v ↔ GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects) := by
  constructor
  · intro hv
    obtain ⟨⟨tree⟩, _⟩ := (generateProjected_sound N hsig run).sound
    exact tree.ground v hv real _ (O.refl _)
  · intro typed
    obtain ⟨d', run', _, cover⟩ := Inference.groundComplete_projected_run N g e t eff ⟨v, typed⟩
    have eq := Option.some.inj (run.symm.trans run')
    subst d'
    exact cover v typed

/-- Completeness of the composed procedure, including open environments and
handlers. The solver law concerns constraints only. -/
theorem inferAt_complete {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X) (complete : S.Complete)
    {g : Context X} {e : Expr} {c : X.Formula} {t : T.Term} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e (.mono t) eff) (real : g.Realizable c) :
    ∃ n, inferAt sig X N S g e t eff = some (.solved n) := by
  obtain ⟨v, hv⟩ := (X.admissible_satisfiable_iff c).mp typed.root.1
  obtain ⟨tree, _⟩ := typed
  have ground := tree.ground v hv (real.ground hv) _ (O.refl _)
  obtain ⟨d, run, _, cover⟩ := Inference.groundComplete_projected_run N g e t eff ⟨v, ground⟩
  obtain ⟨n, hn⟩ := complete X.top d ⟨v, (X.holds_and _ _ _).mpr
    ⟨(X.holds_top v).mpr trivial, cover v ground⟩⟩
  exact ⟨n, by simp [inferAt, run, hn]⟩

/-- Open environments are interpreted at the same substituted valuation as the
result. No assumption that normalization fixes the environment is made here. -/
theorem inferAt_ground_sound {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X) (hsig : sig.Closed)
    {g : Context X} {e : Expr} {t : T.Term} {eff : Effect} {n : X.NormalForm}
    (run : inferAt sig X N S g e t eff = some (.solved n))
    (v : Valuation T.Value) (residual : X.holds n.residual v)
    (real : g.GroundRealizable (n.substitution.pullback v)) :
    GroundTyping sig O (g.ground (n.substitution.pullback v)) e
      (T.eval v (n.substitution.apply t)) ((eff.subst n.substitution.effects).eval v.effects) := by
  obtain ⟨d, generated, solved⟩ := Option.map_eq_some_iff.mp run
  have laws := (S.success X.top d n solved).1
  have hd := (X.holds_subst _ _ _).mp (laws.sound v
    ((X.holds_and _ _ _).mpr ⟨(X.holds_top v).mpr trivial, residual⟩))
  simpa only [Substitution.eval_apply, Effect.eval_subst, Substitution.pullback] using
    (generateProjected_ground_iff N hsig generated _ real).mp hd

/-- Soundness in a syntactically represented substituted environment. The
transport premise specifies capture-avoiding environment substitution. -/
theorem inferAt_sound {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X) (hsig : sig.Closed)
    {g targetContext : Context X} {e : Expr} {t : T.Term} {eff : Effect} {n : X.NormalForm}
    (run : inferAt sig X N S g e t eff = some (.solved n))
    (real : g.Realizable X.top)
    (transport : ∀ v, targetContext.ground v = g.ground (n.substitution.pullback v))
    (admissible : targetContext.Admissible X.Satisfiable) :
    Typing sig X X.Satisfiable n.residual targetContext e
      (.mono (n.substitution.apply t)) (eff.subst n.substitution.effects) := by
  obtain ⟨d, generated, solved⟩ := Option.map_eq_some_iff.mp run
  have sat := (S.success X.top d n solved).2
  apply Typing.of_ground N admissible
    (by obtain ⟨v, hv⟩ := sat; exact ⟨v, (X.holds_and _ _ _).mp hv |>.2⟩)
  intro v hv
  rw [transport]
  exact inferAt_ground_sound N S hsig run v hv (real.ground ((X.holds_top _).mpr trivial))

/-- The actual accepted output is principal; solver completeness is not used. -/
theorem inferAt_principal_closed_at {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X) (hsig : sig.Closed)
    (resultName effectName : Nat)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (closed : g.support = Names.empty) (real : g.Realizable X.top)
    (admissible : g.Admissible X.Satisfiable)
    (run : inferAt sig X N S g e (T.var resultName) (Effect.var effectName) = some (.solved n)) :
    let s := ComputationScheme.generalize g n.residual
      (n.substitution.types resultName) (n.substitution.effects effectName)
    PrincipalComputationScheme sig X X.Satisfiable g e s ∧
    (∀ c t eff, Typing sig X X.Satisfiable c g e (.mono t) eff → s.FiniteInstance c t eff) ∧
    (Value e → PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
      g e X.top (.qualified s.bound s.condition s.result)) := by
  obtain ⟨d, generated, solved⟩ := Option.map_eq_some_iff.mp run
  obtain ⟨laws, sat⟩ := S.success X.top d n solved
  obtain ⟨v, hv⟩ := sat
  have hr : X.holds n.residual v := ((X.holds_and _ _ _).mp hv).2
  have hd : X.holds d (n.substitution.pullback v) :=
    (X.holds_subst _ _ _).mp (laws.sound v hv)
  have inferred := generateProjected_sound N hsig generated
  have typed := (inferred.sound_valid admissible ⟨_, hd⟩).1
  obtain ⟨d', generated', _, _, _, finite⟩ := typed.principal_computation_at N resultName effectName closed real
  have eq := Option.some.inj (generated.symm.trans generated')
  subst d'
  have equiv := laws.formula_equivalent_top
  let result := n.substitution.types resultName
  let effect := n.substitution.effects effectName
  have transport (w : Valuation T.Value) : g.ground w = g.ground (n.substitution.pullback w) := by
    apply Context.ground_support
    rw [closed]
    constructor <;> intro i hi <;> simp [Names.empty] at hi
  have reconstructed : Typing sig X X.Satisfiable n.residual g e (.mono result) effect := by
    simpa [Substitution.apply, T.subst_var, Effect.subst, Effect.var, result, effect] using
      inferAt_sound N S hsig run real transport admissible
  have finite' c' t' eff' (ht : Typing sig X X.Satisfiable c' g e (.mono t') eff') :
      (ComputationScheme.generalize g n.residual result effect).FiniteInstance c' t' eff' := by
    obtain ⟨σ, _, _, hσ⟩ := finite c' t' eff' ht
    apply ComputationScheme.generalize_finite g _ _ _ closed σ
    intro w hw
    obtain ⟨hD, htype, heffect⟩ := hσ w hw
    obtain ⟨hR, hgraph⟩ := (X.holds_and _ _ _).mp (equiv.2 _ hD)
    have fixed := X.substitutionConstraint_fixed n.substitution (σ.pullback w) hgraph
    refine ⟨hR, ?_, ?_⟩
    · change O.le ((n.substitution.pullback (σ.pullback w)).types resultName) _
      rw [fixed]
      simpa only [T.eval_var] using htype
    · change (n.substitution.pullback (σ.pullback w)).effects effectName = _
      rw [fixed]
      simpa [Effect.eval, Effect.var] using heffect
  have comp := reconstructed.computation_generalize_closed closed ⟨v, hr⟩
    ((X.admissible_satisfiable_iff _).mpr ⟨v, (X.holds_top v).mpr trivial⟩)
  exact ⟨⟨comp, fun c t eff ht w hw => (finite' c t eff ht).ground w hw⟩,
    finite', fun he => comp.principal_value (fun _ h => h) real he finite'⟩

theorem inferAt_principal_closed {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X) (hsig : sig.Closed)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (closed : g.support = Names.empty) (real : g.Realizable X.top)
    (admissible : g.Admissible X.Satisfiable)
    (run : inferAt sig X N S g e (T.var 0) (Effect.var 0) = some (.solved n)) :
    let s := ComputationScheme.generalize g n.residual
      (n.substitution.types 0) (n.substitution.effects 0)
    PrincipalComputationScheme sig X X.Satisfiable g e s ∧
    (∀ c t eff, Typing sig X X.Satisfiable c g e (.mono t) eff → s.FiniteInstance c t eff) ∧
    (Value e → PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
      g e X.top (.qualified s.bound s.condition s.result)) := by
  exact inferAt_principal_closed_at N S hsig 0 0 closed real admissible run

/-- A complete solver makes inference at fresh result variables succeed for
any valid closed-environment typing, not just for a supplied expected type. -/
theorem inferAt_complete_closed {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X) (complete : S.Complete)
    {g : Context X} {e : Expr} {c : X.Formula} {s : Scheme X} {eff : Effect}
    (closed : g.support = Names.empty) (real : g.Realizable X.top)
    (typed : Typing sig X X.Satisfiable c g e s eff) :
    ∃ n, inferAt sig X N S g e (T.var 0) (Effect.var 0) = some (.solved n) := by
  obtain ⟨d, generated, _, sat, _, _⟩ := typed.principal_computation_run N closed real
  obtain ⟨v, hv⟩ := sat
  obtain ⟨n, hn⟩ := complete X.top d
    ⟨v, (X.holds_and _ _ _).mpr ⟨(X.holds_top v).mpr trivial, hv⟩⟩
  exact ⟨n, by simp [inferAt, generated, hn]⟩

/-- Principality for open inputs: a single finite factor works for every
solution of a target constraint, transporting the environment as well as the
result. It compares substitutions of the input configuration, not unrelated
contexts. No closure of the input context is required. -/
theorem inferAt_principal_open {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X)
    {g targetContext : Context X} {e : Expr} {t : T.Term} {eff : Effect} {n : X.NormalForm}
    (run : inferAt sig X N S g e t eff = some (.solved n))
    (σ : Substitution T) (c : X.Formula)
    (transport : ∀ v, targetContext.ground v = g.ground (σ.pullback v))
    (real : targetContext.Realizable c)
    (typed : Typing sig X X.Satisfiable c targetContext e
      (.mono (σ.apply t)) (eff.subst σ.effects)) :
    ∃ φ : Substitution T, ∀ v, X.holds c v →
      X.holds n.residual (φ.pullback v) ∧
      n.substitution.pullback (φ.pullback v) = σ.pullback v := by
  obtain ⟨d, generated, solved⟩ := Option.map_eq_some_iff.mp run
  have laws := (S.success X.top d n solved).1
  refine ⟨σ, ?_⟩
  intro v hv
  obtain ⟨tree, _⟩ := typed
  have ground := tree.ground v hv (real.ground hv) _ (O.refl _)
  have ground' : GroundTyping sig O (g.ground (σ.pullback v)) e
      (T.eval (σ.pullback v) t) (eff.eval (σ.pullback v).effects) := by
    simpa only [transport, Substitution.eval_apply, Effect.eval_subst, Substitution.pullback] using ground
  obtain ⟨d', generated', _, cover⟩ := Inference.groundComplete_projected_run N g e t eff ⟨_, ground'⟩
  have eq := Option.some.inj (generated.symm.trans generated')
  subst d'
  have hd := cover _ ground'
  obtain ⟨hr, graph⟩ := (X.holds_and _ _ _).mp (laws.no_guess _
    ((X.holds_and _ _ _).mpr ⟨(X.holds_top _).mpr trivial, hd⟩))
  exact ⟨hr, X.substitutionConstraint_fixed n.substitution _ graph⟩

/-- Rejection is justified by constraint unsatisfiability; it cannot mean that
an incomplete solver simply failed to find a solution. -/
theorem inferAt_inconsistent {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X)
    {g : Context X} {e : Expr} {t : T.Term} {eff : Effect}
    (run : inferAt sig X N S g e t eff = some .inconsistent) :
    ¬ ∃ v, GroundTyping sig O (g.ground v) e (T.eval v t) (eff.eval v.effects) := by
  obtain ⟨d, generated, rejected⟩ := Option.map_eq_some_iff.mp run
  rintro ⟨v, ht⟩
  obtain ⟨d', generated', _, cover⟩ := Inference.groundComplete_projected_run N g e t eff ⟨v, ht⟩
  have eq := Option.some.inj (generated.symm.trans generated')
  subst d'
  exact S.inconsistent X.top d rejected
    ⟨v, (X.holds_and _ _ _).mpr ⟨(X.holds_top v).mpr trivial, cover v ht⟩⟩

/-- Unknown retains the entire generated condition, up to equivalence. -/
theorem inferAt_unresolved {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X)
    {g : Context X} {e : Expr} {t : T.Term} {eff : Effect} {r : X.Formula}
    (run : inferAt sig X N S g e t eff = some (.unresolved r)) :
    ∃ d, generateProjected sig X N g e t eff = some d ∧ X.Equivalent r d := by
  obtain ⟨d, generated, unknown⟩ := Option.map_eq_some_iff.mp run
  have eq := S.unresolved X.top d r unknown
  refine ⟨d, generated, ?_, ?_⟩
  · intro v hv
    exact ((X.holds_and _ _ _).mp (eq.1 v
      ((X.holds_and _ _ _).mpr ⟨(X.holds_top v).mpr trivial, hv⟩))).2
  · intro v hv
    exact ((X.holds_and _ _ _).mp (eq.2 v
      ((X.holds_and _ _ _).mpr ⟨(X.holds_top v).mpr trivial, hv⟩))).2

/-- Inference without an expected type: result names are fresh for the input
context. The normal form applies to this entire open input configuration. -/
def infer (sig : Signature T) (X : Constraints T O) (N : X.Simplifier)
    (S : PartialSolver X) (g : Context X) (e : Expr) : Option (SolveResult X) :=
  inferAt sig X N S g e (T.var (g.support.shiftTypes 0)) (Effect.var (g.support.shiftEffects 0))

/-- Qualified output interpretation. Its closed-context principal-type theorem
is `infer_principal_closed`; open inputs additionally carry the environment
substitution and use finite-factor comparison. -/
def inferredScheme {X : Constraints T O} (g : Context X) (n : X.NormalForm) : ComputationScheme X :=
  ComputationScheme.generalize g n.residual
    (n.substitution.types (g.support.shiftTypes 0))
    (n.substitution.effects (g.support.shiftEffects 0))

theorem infer_complete {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X) (complete : S.Complete)
    {g : Context X} {e : Expr} {c : X.Formula} {scheme : Scheme X} {eff : Effect}
    (typed : Typing sig X X.Satisfiable c g e scheme eff) (real : g.Realizable c) :
    ∃ n, infer sig X N S g e = some (.solved n) := by
  obtain ⟨v, hv⟩ := (X.admissible_satisfiable_iff c).mp typed.root.1
  obtain ⟨tree, _⟩ := typed
  have hreal := real.ground hv
  obtain ⟨u, hu⟩ := tree.groundInstance_exists v hv hreal
  let w := v.fresh g.support (fun _ => u) (fun _ => eff.eval v.effects)
  let t := T.var (g.support.shiftTypes 0)
  let out := Effect.var (g.support.shiftEffects 0)
  have ground : GroundTyping sig O (g.ground w) e (T.eval w t) (out.eval w.effects) := by
    rw [Context.ground_support (v.fresh_agree g.support _ _)]
    simpa [t, out, w, T.eval_var, Effect.eval, Effect.var,
      Valuation.fresh_types, Valuation.fresh_effects] using tree.ground v hv hreal u hu
  obtain ⟨d, generated, _, cover⟩ := Inference.groundComplete_projected_run N g e t out ⟨w, ground⟩
  obtain ⟨n, hn⟩ := complete X.top d
    ⟨w, (X.holds_and _ _ _).mpr ⟨(X.holds_top w).mpr trivial, cover w ground⟩⟩
  exact ⟨n, by simpa [infer, inferAt, t, out, generated] using congrArg some hn⟩

theorem infer_principal_closed {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X) (hsig : sig.Closed)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (closed : g.support = Names.empty) (real : g.Realizable X.top)
    (admissible : g.Admissible X.Satisfiable)
    (run : infer sig X N S g e = some (.solved n)) :
    let s := ComputationScheme.generalize g n.residual
      (n.substitution.types (g.support.shiftTypes 0))
      (n.substitution.effects (g.support.shiftEffects 0))
    PrincipalComputationScheme sig X X.Satisfiable g e s ∧
    (∀ c t eff, Typing sig X X.Satisfiable c g e (.mono t) eff → s.FiniteInstance c t eff) ∧
    (Value e → PrincipalPair (fun c g e s => Typing sig X X.Satisfiable c g e s ∅)
      g e X.top (.qualified s.bound s.condition s.result)) :=
  inferAt_principal_closed_at N S hsig _ _ closed real admissible run

/-- Success soundness for the inference entry point without an expected type. -/
theorem infer_ground_sound {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X) (hsig : sig.Closed)
    {g : Context X} {e : Expr} {n : X.NormalForm}
    (run : infer sig X N S g e = some (.solved n))
    (v : Valuation T.Value) (residual : X.holds n.residual v)
    (real : g.GroundRealizable (n.substitution.pullback v)) :
    GroundTyping sig O (g.ground (n.substitution.pullback v)) e
      (T.eval v (n.substitution.types (g.support.shiftTypes 0)))
      ((n.substitution.effects (g.support.shiftEffects 0)).eval v.effects) := by
  simpa [Substitution.apply, T.subst_var, Effect.subst, Effect.var] using
    inferAt_ground_sound N S hsig run v residual real

/-- Principal finite-factor property of the actual open inference output. -/
theorem infer_principal_open {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X)
    {g targetContext : Context X} {e : Expr} {n : X.NormalForm}
    (run : infer sig X N S g e = some (.solved n))
    (σ : Substitution T) (c : X.Formula)
    (transport : ∀ v, targetContext.ground v = g.ground (σ.pullback v))
    (real : targetContext.Realizable c)
    (typed : Typing sig X X.Satisfiable c targetContext e
      (.mono (σ.types (g.support.shiftTypes 0))) (σ.effects (g.support.shiftEffects 0))) :
    ∃ φ : Substitution T, ∀ v, X.holds c v →
      X.holds n.residual (φ.pullback v) ∧
      n.substitution.pullback (φ.pullback v) = σ.pullback v := by
  apply inferAt_principal_open N S run σ c transport real
  simpa [Substitution.apply, T.subst_var, Effect.subst, Effect.var] using typed

/-- Structural failure cannot hide a valid input, independently of whether
the supplied solver is complete. -/
theorem infer_missing {sig : Signature T} {X : Constraints T O}
    (N : X.Simplifier) (S : PartialSolver X)
    {g : Context X} {e : Expr}
    (run : infer sig X N S g e = none)
    {c : X.Formula} {scheme : Scheme X} {eff : Effect} (real : g.Realizable c) :
    ¬ Typing sig X X.Satisfiable c g e scheme eff := by
  intro typed
  obtain ⟨n, hn⟩ := infer_complete N (PartialSolver.semantic X)
    (PartialSolver.semantic_complete X) typed real
  unfold infer inferAt at run hn
  have missing := Option.map_eq_none_iff.mp run
  rw [missing] at hn
  contradiction

end EHMX.HMX
