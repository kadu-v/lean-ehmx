import EHMX.TypeClasses.FlatSolver
import EHMX.TypeClasses.Unification

namespace EHMX.TypeClasses
open HMX

inductive Decision {K} (E : ClassEnv K) (c : Formula K E.count) where
  | sat : (constraints E).Satisfiable c → Decision E c
  | unsat : (¬ (constraints E).Satisfiable c) → Decision E c
  | unknown : Decision E c

/-- Complete for collected class/effect conjunctions, and preserves outer
existential quantifiers. Unsupported forms are explicitly unknown. -/
def decideSimple {K} (E : ClassEnv K) (c : Formula K E.count) : Decision E c :=
  match c with
  | .bot => .unsat (by rintro ⟨v, hv⟩; exact holds_bot E v hv)
  | .ex a body =>
    match decideSimple E body with
    | .sat h => .sat (((constraints E).satisfiable_exists_iff a body).mpr h)
    | .unsat h => .unsat (fun he => h (((constraints E).satisfiable_exists_iff a body).mp he))
    | .unknown => .unknown
  | c =>
    match h : collect c with
    | none => .unknown
    | some f => if hs : flatSat E f = true then
        .sat ((flatSat_iff E c f h).mp hs)
      else .unsat (fun hc => hs ((flatSat_iff E c f h).mpr hc))

/-- Every elimination preserves satisfiability in both directions. Exhausting
the explicit bound returns unknown; it is never interpreted as a refutation. -/
def decideWith {K} (E : ClassEnv K) (fuel : Nat) (c : Formula K E.count) : Decision E c :=
  match c with
  | .ex a body => match decideWith E fuel body with
    | .sat h => .sat (((constraints E).satisfiable_exists_iff a body).mpr h)
    | .unsat h => .unsat (fun he => h (((constraints E).satisfiable_exists_iff a body).mp he))
    | .unknown => .unknown
  | c => match decideSimple E c with
    | .sat h => .sat h
    | .unsat h => .unsat h
    | .unknown => match fuel with
      | 0 => .unknown
      | fuel + 1 => match findBinding E ∅ c with
        | none => .unknown
        | some b => match decideWith E fuel (simplify E (push E (binding b.name b.value) c)) with
          | .sat h => .sat (b.sat_iff.mp h)
          | .unsat h => .unsat (fun hc => h (b.sat_iff.mpr hc))
          | .unknown => .unknown
termination_by (fuel, sizeOf c)

def decideConstraint {K} (E : ClassEnv K) (c : Formula K E.count) : Decision E c :=
  match decideWith E (((constraints E).support c).types.card + 1) (simplify E c) with
  | .sat h => .sat (by obtain ⟨v, hv⟩ := h; exact ⟨v, (simplify_correct E c v).mp hv⟩)
  | .unsat h => .unsat (by rintro ⟨v, hv⟩; exact h ⟨v, (simplify_correct E c v).mpr hv⟩)
  | .unknown => .unknown

end EHMX.TypeClasses
