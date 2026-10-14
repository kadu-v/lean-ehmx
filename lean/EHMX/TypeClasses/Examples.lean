import EHMX.TypeClasses.Completeness
import EHMX.TypeClasses.Declarations

namespace EHMX.TypeClasses.Examples
open HMX

abbrev constructors : Constructors := ⟨2, fun k => if k.val = 0 then 1 else 2⟩
def eqClass : Fin 2 := 0
def ordClass : Fin 2 := 1

abbrev classes : ClassEnv constructors where
  count := 2
  supers := fun c => if c = ordClass then {eqClass} else ∅
  bases := {(eqClass, .int), (eqClass, .bool), (ordClass, .int)}
  rules := fun c _ => some (fun _ => {c})

theorem classes_valid : classes.WellFormed := by decide +kernel

def list (t : Ty constructors) : Ty constructors := .con 0 (fun _ => t)
def pair (a b : Ty constructors) : Ty constructors := .con 1 (fun i => if i.val = 0 then a else b)

def status {X : Constraints T O} : SolveResult X → Nat
  | .solved _ => 0
  | .unresolved _ => 1
  | .inconsistent => 2

def inferStatus (e : Expr) : Option Nat :=
  (inferClasses classes (fun _ => none) [] e).map status

example : inhabited classes {eqClass, ordClass} = true := by decide +kernel
example : (Ground.con (K := constructors) 0 (fun _ => .base .int)).classes classes =
    {eqClass, ordClass} := by decide +kernel

def declarations : Declarations constructors where
  count := 2
  supers := classes.supers
  instances := [.base eqClass .int, .base eqClass .bool, .base ordClass .int,
    .con eqClass 0 (fun _ => {eqClass}), .con ordClass 0 (fun _ => {ordClass}),
    .con eqClass 1 (fun _ => {eqClass}), .con ordClass 1 (fun _ => {ordClass})]

abbrev separateClasses : ClassEnv constructors where
  count := 2
  supers := fun _ => ∅
  bases := {(eqClass, .int), (ordClass, .bool)}
  rules := fun _ _ => none

def identityOp : Operation (types constructors) := ⟨⟨{0}, ∅⟩, .var 0, .var 0⟩
def signature : Signature (types constructors) := fun _ => some identityOp

def resumeIdentity : Expr :=
  .handle (.perform 0 (.int 0)) 0 (.var 0) (.app (.var 0) (.var 1))

theorem identityOp_closed : identityOp.Closed := by
  simp [identityOp, Operation.Closed, types, Ty.types, Ty.effects]

theorem signature_closed : signature.Closed := by
  intro op d h
  cases h
  exact identityOp_closed

theorem resumeIdentity_ground : GroundTyping signature (TypeOrder.equality (types constructors))
    [] resumeIdentity (.base .int) ∅ := by
  let T := types constructors
  let O := TypeOrder.equality T
  let v : HMX.Valuation (Ground constructors) := ⟨fun _ => .base .int, fun _ => ∅⟩
  have body : GroundTyping signature O [] (.perform 0 (.int 0)) (.base .int) {0} := by
    simpa [identityOp, T, types, Ty.eval, v] using
      (GroundTyping.perform (O := O) (raw := identityOp) (g := []) (op := 0)
        v rfl identityOp_closed (.int 0))
  apply GroundTyping.handle (raw := identityOp) (decl := identityOp)
    (input := Ground.base .int) (ein := {0}) (er := ∅) (rest := ∅) (fun _ => ∅)
  · rfl
  · exact identityOp_closed
  · exact ⟨id, id, Function.injective_id.injOn, Function.injective_id.injOn, rfl⟩
  · exact body
  · exact .var rfl rfl
  · intro w
    have hk : GroundTyping signature O
        [upper O (T.groundArrow (T.eval w identityOp.output) ∅ (.base .int)),
         upper O (T.eval w identityOp.input)] (.var 0)
        (T.groundArrow (T.eval w identityOp.output) ∅ (.base .int)) ∅ := .var rfl rfl
    have hx : GroundTyping signature O
        [upper O (T.groundArrow (T.eval w identityOp.output) ∅ (.base .int)),
         upper O (T.eval w identityOp.input)] (.var 1) (T.eval w identityOp.output) ∅ := .var rfl rfl
    simpa using GroundTyping.app hk hx
  all_goals simp

def polymorphicLet : Expr :=
  .letE (.lam (.var 0)) (.letE (.app (.var 0) (.int 0)) (.app (.var 1) (.bool true)))

def eqScheme : Scheme (constraints classes) :=
  .qualified ⟨{0}, ∅⟩ (.pred eqClass (.var 0))
    (.arr (.var 0) ∅ (.arr (.var 0) ∅ (.base .bool)))

/-- Run compiled code as a regression test; no native-decide axiom is introduced. -/
def regressions : IO Unit := do
  let checks : List Bool := [
    status ((solver classes).run .top (.pred eqClass (list (.base .bool)))) == 0,
    status ((solver classes).run .top (.pred ordClass (list (.base .bool)))) == 2,
    status ((solver classes).run .top (.pred eqClass (.var 0))) == 0,
    status ((solver classes).run .top (.ex ⟨{0}, ∅⟩ (.pred eqClass (.var 0)))) == 0,
    status ((solver classes).run .top (.eq (.base .int) (.base .bool))) == 2,
    !effectSat [.le (Effect.singleton 0) (Effect.var 0), .lacks 0 (Effect.var 0)],
    effectSat [.le (Effect.var 0) (Effect.var 1), .lacks 0 (Effect.var 1)],
    status ((solver classes).run .top (.pred eqClass (pair (.base .int) (.base .bool)))) == 0,
    status ((solver separateClasses).run .top (.and (.pred eqClass (.var 0)) (.pred ordClass (.var 0)))) == 2,
    declarations.check.isSome,
    !({ declarations with instances := .base eqClass .int :: declarations.instances }.check.isSome),
    !({ declarations with supers := fun c => {c} }.check.isSome),
    !(({ declarations with instances := [.base ordClass .int] } : Declarations constructors).check.isSome),
    inferStatus polymorphicLet == some 0,
    ((inferClasses classes (fun _ => none) [eqScheme] (.letE (.var 0) (.int 0))).map status) == some 0,
    ((inferClasses classes signature [] (.perform 0 (.int 0))).map status) == some 0,
    ((inferClasses classes signature [] resumeIdentity).map status) == some 0,
    status ((solver classes).run .top (.clause ⟨{0}, ∅⟩ ⟨{1}, ∅⟩ (.eq (.var 0) (.var 1)))) == 0,
    status ((solver classes).run .top (.ex ⟨{1}, ∅⟩ (.clause ⟨{0}, ∅⟩ Names.empty (.eq (.var 0) (.var 1))))) == 1,
    status ((solver classes).run .top (.eq (.var 0) (list (.var 0)))) == 2,
    inferStatus (.int 1) == some 0,
    inferStatus (.lam (.var 0)) == some 0,
    inferStatus (.app (.lam (.var 0)) (.bool true)) == some 0]
  if !checks.all id then throw (IO.userError "type-class solver regression")
  match (solver classes).run .top (.pred eqClass (.var 0)) with
  | .solved n =>
    if !(decide (n.substitution.types 0 = Ty.var 0)) then throw (IO.userError "defaulted a public variable")
  | _ => throw (IO.userError "Eq alpha should be a satisfiable qualified residual")
  match (solver classes).run .top (.eq (.var 0) (.base .int)) with
  | .solved n =>
    if !(decide (n.substitution.types 0 = Ty.base .int)) then throw (IO.userError "missing forced substitution")
  | _ => throw (IO.userError "type equality not solved")
  match (solver classes).run (.pred eqClass (.var 0)) (.eq (.var 0) (.base .int)) with
  | .solved n =>
    if !(decide (n.substitution.types 0 = Ty.var 0)) then throw (IO.userError "modified a given variable")
  | _ => throw (IO.userError "consistent given/wanted pair not solved")

#guard_msgs in
#eval regressions

end EHMX.TypeClasses.Examples
