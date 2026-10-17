import EHMX
import Lean.Util.CollectAxioms

/-! Check every EHMX theorem, including regressions. Standard Lean axioms only;
in particular, neither sorryAx nor a user-declared safety/inference axiom is allowed. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if `EHMX |>.isPrefixOf name then
      match info with
      | .axiomInfo _ => throwError "EHMX declares an axiom: {name}"
      | .thmInfo _ =>
          for ax in ← collectAxioms name do
            unless allowed.contains ax do
              throwError "{name} depends on unapproved axiom {ax}"
          checked := checked + 1
      | _ => pure ()
  if checked == 0 then throwError "No EHMX theorems were checked"
  logInfo m!"Checked axioms of {checked} EHMX theorem declarations."
