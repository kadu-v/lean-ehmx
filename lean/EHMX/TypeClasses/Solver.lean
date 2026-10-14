import EHMX.TypeClasses.Normalizer
import EHMX.HMX.AlgorithmCorrectness

namespace EHMX.TypeClasses
open HMX

def Certificate {K} (E : ClassEnv K) (g w : Formula K E.count) : SolveResult (constraints E) → Prop
  | .solved n => n.GuessFreeSolution g w ∧ (constraints E).Satisfiable (.and g n.residual)
  | .unresolved r => (constraints E).Equivalent (.and g r) (.and g w)
  | .inconsistent => ¬ (constraints E).Satisfiable (.and g w)

def solveBinding {K} (E : ClassEnv K) (g w : Formula K E.count) (b : Binding E w)
    (fresh : b.name ∉ ((constraints E).support g).types) :
    Option {r : SolveResult (constraints E) // Certificate E g w r} := by
  let n : (constraints E).NormalForm :=
    ⟨simplify E (push E (binding b.name b.value) w), binding b.name b.value⟩
  have laws : n.GuessFreeSolution g w := binding_guessFree E g w b fresh
  match decideConstraint E (.and g n.residual) with
  | .sat h => exact some ⟨.solved n, laws, h⟩
  | .unsat h =>
    exact some ⟨.inconsistent, fun ⟨v, hv⟩ => h ⟨v,
      (holds_and E _ _ _).mpr ⟨hv.1, ((constraints E).holds_and _ _ _).mp (laws.no_guess v hv) |>.1⟩⟩⟩
  | .unknown => exact none

def solve {K} (E : ClassEnv K) (g w : Formula K E.count) :
    {r : SolveResult (constraints E) // Certificate E g w r} := by
  let r := normalize E w
  have equiv : (constraints E).Equivalent r w := (normalizer E).equivalent w
  have both : (constraints E).Equivalent (.and g r) (.and g w) :=
    ⟨fun v hv => (holds_and E _ _ _).mpr ⟨hv.1, equiv.1 v hv.2⟩,
     fun v hv => (holds_and E _ _ _).mpr ⟨hv.1, equiv.2 v hv.2⟩⟩
  let attempt := match hb : findBinding E ((constraints E).support g).types r with
    | none => none
    | some b =>
      let bw : Binding E w := ⟨b.name, b.value, b.occurs, fun v hv => b.forced v (equiv.2 v hv)⟩
      solveBinding E g w bw (findBinding_protected E _ r b hb)
  match attempt with
  | some result => exact result
  | none =>
    match decideConstraint E (.and g r) with
    | .sat h =>
      exact ⟨.solved ⟨r, Substitution.identity (types K)⟩,
        Constraints.NormalForm.guessFree_identity equiv, h⟩
    | .unsat h => exact ⟨.inconsistent, fun ⟨v, hv⟩ => h ⟨v, both.2 v hv⟩⟩
    | .unknown => exact ⟨.unresolved r, both⟩

def solver {K} (E : ClassEnv K) : PartialSolver (constraints E) where
  run := fun g w => (solve E g w).val
  success := by
    intro g w n h
    have cert := (solve E g w).property
    rw [h] at cert
    exact cert
  unresolved := by
    intro g w r h
    have cert := (solve E g w).property
    rw [h] at cert
    exact cert
  inconsistent := by
    intro g w h
    have cert := (solve E g w).property
    rw [h] at cert
    exact cert

/-- The executable solver's contracts specialize the generic soundness and
principality results without a semantic satisfiability oracle. -/
def inferClasses {K} (E : ClassEnv K) (sig : Signature (types K))
    (g : Context (constraints E)) (e : Expr) :=
  HMX.infer sig (constraints E) (normalizer E) (solver E) g e

theorem inferClasses_sound {K} (E : ClassEnv K) {sig : Signature (types K)}
    (hsig : sig.Closed) {g e n}
    (run : inferClasses E sig g e = some (.solved n))
    (v) (residual : Formula.Holds E n.residual v)
    (real : g.GroundRealizable (n.substitution.pullback v)) :
    GroundTyping sig (TypeOrder.equality (types K)) (g.ground (n.substitution.pullback v)) e
      ((n.substitution.types (g.support.shiftTypes 0)).eval v)
      ((n.substitution.effects (g.support.shiftEffects 0)).eval v.effects) :=
  HMX.infer_ground_sound (normalizer E) (solver E) hsig run v residual real

theorem inferClasses_principal {K} (E : ClassEnv K) {sig : Signature (types K)}
    (hsig : sig.Closed) {g : Context (constraints E)} {e n}
    (closed : g.support = Names.empty) (real : g.Realizable (constraints E).top)
    (admissible : g.Admissible (constraints E).Satisfiable)
    (run : inferClasses E sig g e = some (.solved n)) :
    PrincipalComputationScheme sig (constraints E) (constraints E).Satisfiable g e (inferredScheme g n) :=
  (HMX.infer_principal_closed (normalizer E) (solver E) hsig closed real admissible run).1

end EHMX.TypeClasses
