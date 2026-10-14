import EHMX.HMX.AlgorithmCorrectness

namespace EHMX.HMX.AlgorithmExamples

private abbrev T := equalityTypes
private abbrev O := TypeOrder.equality T
private abbrev X := Constraints.semantic T O
private abbrev N := Constraints.Simplifier.identity X

private def identityOp : Operation T := ⟨⟨{0}, ∅⟩, T.var 0, T.var 0⟩
private def signature : Signature T := fun _ => some identityOp

private theorem op_closed : identityOp.Closed := by
  simp [identityOp, Operation.Closed, T, equalityTypes, Ty.fvTypes, Ty.fvEffects]

private theorem signature_closed : signature.Closed := by
  intro op d h
  cases h
  exact op_closed

/-- handle (perform op 0) with return x => x | op(x,k) => k x. -/
def resumeIdentity : Expr :=
  .handle (.perform 0 (.int 0)) 0 (.var 0) (.app (.var 0) (.var 1))

theorem resumeIdentity_ground : GroundTyping signature O [] resumeIdentity (T.groundLiteral .int) ∅ := by
  let v : Valuation T.Value := ⟨fun _ => T.groundLiteral .int, fun _ => ∅⟩
  have body : GroundTyping signature O [] (.perform 0 (.int 0)) (T.groundLiteral .int) {0} := by
    simpa [identityOp, T, equalityTypes, Ty.eval, v] using
      (GroundTyping.perform (O := O) (raw := identityOp) (g := []) (op := 0) v rfl op_closed (.int 0))
  apply GroundTyping.handle (raw := identityOp) (decl := identityOp)
    (input := T.groundLiteral .int) (ein := {0}) (er := ∅) (rest := ∅) (fun _ => ∅)
  · rfl
  · exact op_closed
  · exact ⟨id, id, Function.injective_id.injOn, Function.injective_id.injOn, rfl⟩
  · exact body
  · exact .var rfl rfl
  · intro w
    have hk : GroundTyping signature O
        [upper O (T.groundArrow (T.eval w identityOp.output) ∅ (T.groundLiteral .int)),
         upper O (T.eval w identityOp.input)] (.var 0)
        (T.groundArrow (T.eval w identityOp.output) ∅ (T.groundLiteral .int)) ∅ := .var rfl rfl
    have hx : GroundTyping signature O
        [upper O (T.groundArrow (T.eval w identityOp.output) ∅ (T.groundLiteral .int)),
         upper O (T.eval w identityOp.input)] (.var 1) (T.eval w identityOp.output) ∅ := .var rfl rfl
    simpa using GroundTyping.app hk hx
  all_goals simp

/-- The actual handler constraint, including its quantifiers, is satisfiable. -/
theorem resumeIdentity_generated :
    ∃ d, generateProjected signature X N [] resumeIdentity (T.literal .int) ∅ = some d ∧
      X.Satisfiable d := by
  let v : Valuation T.Value := ⟨fun _ => T.groundLiteral .int, fun _ => ∅⟩
  have hg : GroundTyping signature O (Context.ground (X := X) [] v) resumeIdentity
      (T.eval v (T.literal .int)) ((∅ : Effect).eval v.effects) := by
    simpa [Context.ground, T, equalityTypes, Ty.eval, Effect.eval] using resumeIdentity_ground
  obtain ⟨d, run, _, cover⟩ := Inference.groundComplete_projected_run N [] resumeIdentity
    (T.literal .int) ∅ ⟨v, hg⟩
  exact ⟨d, run, v, cover v hg⟩

theorem resumeIdentity_complete (S : PartialSolver X) (complete : S.Complete) :
    ∃ n, inferAt signature X N S [] resumeIdentity (T.literal .int) ∅ = some (.solved n) := by
  obtain ⟨d, run, v, hv⟩ := resumeIdentity_generated
  obtain ⟨n, solved⟩ := complete X.top d
    ⟨v, (X.holds_and _ _ _).mpr ⟨(X.holds_top v).mpr trivial, hv⟩⟩
  exact ⟨n, by simp [inferAt, run, solved]⟩

theorem resumeIdentity_deferred :
    ∃ d, inferAt signature X N (PartialSolver.defer X) [] resumeIdentity
      (T.literal .int) ∅ = some (.unresolved d) ∧ X.Satisfiable d := by
  obtain ⟨d, run, sat⟩ := resumeIdentity_generated
  exact ⟨d, by simp [inferAt, run, PartialSolver.defer], sat⟩

/-- Finite syntax generation runs without a solver or classical choice. -/
example : (generateProjected signature X N [] resumeIdentity (T.var 0) (Effect.var 0)).isSome = true := by
  decide

example : generateProjected signature X N [] (.var 0) (T.var 0) (Effect.var 0) = none := rfl

example : (generateProjected signature X N []
    (.letE (.lam (.var 0)) (.letE (.app (.var 0) (.int 0)) (.app (.var 1) (.bool true))))
    (T.var 0) (Effect.var 0)).isSome = true := by
  decide

def polymorphicLet : Expr :=
  .letE (.lam (.var 0)) (.letE (.app (.var 0) (.int 0)) (.app (.var 1) (.bool true)))

theorem polymorphicLet_ground : GroundTyping signature O [] polymorphicLet (T.groundLiteral .bool) ∅ := by
  let instances : Set T.Value := {t | ∃ a, t = T.groundArrow a ∅ a}
  have body : GroundTyping signature O [instances]
      (.letE (.app (.var 0) (.int 0)) (.app (.var 1) (.bool true))) (T.groundLiteral .bool) ∅ := by
    have hi : GroundTyping signature O [instances] (.app (.var 0) (.int 0))
        (T.groundLiteral .int) ∅ := by
      have idInt : GroundTyping signature O [instances] (.var 0)
          (T.groundArrow (T.groundLiteral .int) ∅ (T.groundLiteral .int)) ∅ :=
        .var rfl ⟨_, rfl⟩
      simpa using GroundTyping.app idInt (.int 0)
    have hb : GroundTyping signature O [upper O (T.groundLiteral .int), instances]
        (.app (.var 1) (.bool true)) (T.groundLiteral .bool) ∅ := by
      have idBool : GroundTyping signature O [upper O (T.groundLiteral .int), instances] (.var 1)
          (T.groundArrow (T.groundLiteral .bool) ∅ (T.groundLiteral .bool)) ∅ :=
        .var rfl ⟨_, rfl⟩
      simpa using GroundTyping.app idBool (.bool true)
    simpa using GroundTyping.letMono (by intro h; cases h) hi hb
  apply GroundTyping.letVal (.lam (.var 0)) (s := instances)
  · exact ⟨_, T.groundLiteral .int, rfl⟩
  · intro a ha
    obtain ⟨b, rfl⟩ := ha
    exact .lam (.var rfl rfl)
  · exact body

/-- Nested handlers preserve both quantifier scopes in the generated formula. -/
theorem nestedHandler_ground : GroundTyping signature O []
    (.handle resumeIdentity 0 (.var 0) (.app (.var 0) (.var 1))) (T.groundLiteral .int) ∅ := by
  apply GroundTyping.handle (raw := identityOp) (decl := identityOp)
    (input := T.groundLiteral .int) (ein := ∅) (er := ∅) (rest := ∅) (fun _ => ∅)
  · rfl
  · exact op_closed
  · exact ⟨id, id, Function.injective_id.injOn, Function.injective_id.injOn, rfl⟩
  · exact resumeIdentity_ground
  · exact .var rfl rfl
  · intro w
    have hk : GroundTyping signature O
        [upper O (T.groundArrow (T.eval w identityOp.output) ∅ (T.groundLiteral .int)),
         upper O (T.eval w identityOp.input)] (.var 0)
        (T.groundArrow (T.eval w identityOp.output) ∅ (T.groundLiteral .int)) ∅ := .var rfl rfl
    have hx : GroundTyping signature O
        [upper O (T.groundArrow (T.eval w identityOp.output) ∅ (T.groundLiteral .int)),
         upper O (T.eval w identityOp.input)] (.var 1) (T.eval w identityOp.output) ∅ := .var rfl rfl
    simpa using GroundTyping.app hk hx
  all_goals simp

end EHMX.HMX.AlgorithmExamples
