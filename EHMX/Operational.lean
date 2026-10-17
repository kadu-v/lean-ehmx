import EHMX.Syntax

/-! 左から右の値呼び評価。型・効果引数は項に存在せず実行時にも渡さない。
handler は deep で、操作節の外側には自動的に handler を置かない。 -/
namespace EHMX

inductive EvalCtx where
  | hole
  | appFun : EvalCtx → Expr → EvalCtx
  | appArg : (v : Expr) → Value v → EvalCtx → EvalCtx
  | letRhs : EvalCtx → Expr → EvalCtx
  | perform : Op → EvalCtx → EvalCtx
  | handle : EvalCtx → Op → Expr → Expr → EvalCtx

def EvalCtx.plug : EvalCtx → Expr → Expr
  | .hole, e => e
  | .appFun E x, e => .app (E.plug e) x
  | .appArg v _ E, e => .app v (E.plug e)
  | .letRhs E body, e => .letE (E.plug e) body
  | .perform op E, e => .perform op (E.plug e)
  | .handle E op ret clause, e => .handle (E.plug e) op ret clause

def EvalCtx.handled : EvalCtx → Finset Op
  | .hole => ∅
  | .appFun E _ | .appArg _ _ E | .letRhs E _ | .perform _ E => E.handled
  | .handle E op _ _ => insert op E.handled

theorem valueShift {v : Expr} (hv : Value v) (n d : Nat) : Value (v.shift n d) := by
  cases v with
  | ident x => cases x <;> simp [Value, Expr.isValue, Expr.shift]
  | lam => rfl
  | app | letE | perform | handle => simp [Value, Expr.isValue] at hv

def EvalCtx.shift (n d : Nat) : EvalCtx → EvalCtx
  | .hole => .hole
  | .appFun E x => .appFun (E.shift n d) (x.shift n d)
  | .appArg v hv E => .appArg (v.shift n d) (valueShift hv n d) (E.shift n d)
  | .letRhs E body => .letRhs (E.shift n d) (body.shift n (d + 1))
  | .perform op E => .perform op (E.shift n d)
  | .handle E op ret clause =>
      .handle (E.shift n d) op (ret.shift n (d + 1)) (clause.shift n (d + 2))

theorem evalCtxShiftPlug (E : EvalCtx) (e : Expr) (n d : Nat) :
    (E.plug e).shift n d = (E.shift n d).plug (e.shift n d) := by
  induction E <;> simp_all [EvalCtx.plug, EvalCtx.shift, Expr.shift]

/-- Shift the captured free context under the continuation's new lambda. -/
def Expr.resume (E : EvalCtx) (op : Op) (ret clause : Expr) : Expr :=
  .lam (.handle ((E.shift 1 0).plug (.ident (.bound 0))) op
    (ret.shift 1 1) (clause.shift 1 2))

inductive Step : Expr → Expr → Prop where
  | beta : Value v → Step (.app (.lam body) v) (body.openAt 0 [v])
  | letValue : Value v → Step (.letE v body) (body.openAt 0 [v])
  | returnValue : Value v → Step (.handle v op ret clause) (ret.openAt 0 [v])
  | operation {E : EvalCtx} : Value v → op ∉ E.handled →
      Step (.handle (E.plug (.perform op v)) op ret clause)
        (clause.openAt 0 [Expr.resume E op ret clause, v])
  | context {E : EvalCtx} : Step e e' → Step (E.plug e) (E.plug e')

inductive Steps : Expr → Expr → Prop where
  | refl (e) : Steps e e
  | tail : Steps e e' → Step e' e'' → Steps e e''

def Unhandled (e : Expr) (op : Op) : Prop :=
  ∃ (E : EvalCtx) (v : Expr), e = E.plug (.perform op v) ∧ Value v ∧ op ∉ E.handled

theorem resumeValue (E : EvalCtx) (op : Op) (ret clause : Expr) :
    Value (Expr.resume E op ret clause) := rfl

end EHMX
