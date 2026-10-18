import EHMX.Syntax

/-! 構文に沿う制約生成。全称量化は操作節だけに導入する。
全ての内部変数を添字で導入するので新鮮な自由名の選択は不要。
この定義の健全性・完全性・主要制約性は Proofs/Inference*.lean で証明する。 -/
namespace EHMX

/-- Pair a type subtyping obligation with an evaluation-effect upper bound. -/
def resultConstraint (A T : Ty) (η ε : Effect) : Constraint :=
  .conj (.le 0 A T) (.le 1 η ε)

def generate (sig : OpSignature) : Expr → Ty → Effect → Constraint
  | .ident x, T, ε => .conj (.inst x T) (.le 1 .empty ε)
  | .lam body, T, ε =>
      .exists_ [0,1,0] (.conj
        (.def_ (.mono (.bound 0)) (generate sig body (.bound 2) (.bound 1)))
        (resultConstraint (.arrow (.bound 0) (.bound 1) (.bound 2))
          (T.shift 3 0) .empty (ε.shift 3 0)))
  | .app f x, T, ε =>
      .exists_ [0,1,1,1] (.conj
        (generate sig f (.arrow (.bound 0) (.bound 1) (T.shift 4 0)) (.bound 2))
        (.conj (generate sig x (.bound 0) (.bound 3))
          (.le 1 (.union (.union (.bound 1) (.bound 2)) (.bound 3)) (ε.shift 4 0))))
  | .letE rhs body, T, ε =>
      if rhs.isValue then
        .letBound (.all [0] (generate sig rhs (.bound 0) .empty) (.bound 0))
          (generate sig body T ε)
      else
        .exists_ [0,1,1] (.conj (generate sig rhs (.bound 0) (.bound 1))
          (.conj (.def_ (.mono (.bound 0)) (generate sig body (T.shift 3 0) (.bound 2)))
            (.le 1 (.union (.bound 1) (.bound 2)) (ε.shift 3 0))))
  | .perform op arg, T, ε =>
      match sig op with
      | none => .falsity
      | some decl =>
        .exists_ (decl.kinds ++ [1]) (.conj decl.condition (.conj
          (generate sig arg decl.input (.bound decl.kinds.length))
          (resultConstraint decl.output (T.shift (decl.kinds.length + 1) 0)
            (.union (.singleton op) (.bound decl.kinds.length))
            (ε.shift (decl.kinds.length + 1) 0))))
  | .handle body op ret clause, T, ε =>
      match sig op with
      | none => .falsity
      | some decl =>
        let B := Ty.bound 2
        let η := Ty.bound 3
        let n := decl.kinds.length
        .exists_ [0,1,0,1] (.conj (generate sig body (.bound 0) (.bound 1))
          (.conj (.le 1 (.bound 1) (.union (.singleton op) η))
          (.conj (.def_ (.mono (.bound 0)) (generate sig ret B η))
          (.conj (.forall_ decl.kinds
            (.implies decl.condition (.def_ (.mono decl.input)
              (.def_ (.mono (.arrow decl.output (η.shift n 0) (B.shift n 0)))
                (generate sig clause (B.shift n 0) (η.shift n 0))))))
            (resultConstraint B (T.shift 4 0) η (ε.shift 4 0))))))

def infer (sig : OpSignature) (Γ : Env) (e : Expr) (T : Ty) (ε : Effect) : Constraint :=
  Γ.letIn (generate sig e T ε)

end EHMX
