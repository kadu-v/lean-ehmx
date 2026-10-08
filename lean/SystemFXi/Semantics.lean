import SystemFXi.Typing

/-!
# 値呼び評価と deep handler

評価文脈は左から右の値呼び順序を表す。`EvalCtx.handled` は穴から
外側へ向かう経路に現れる handler の操作名を集める。
-/

namespace SystemFXi

/-- `v` は項変数、項抽象、型抽象のいずれかである。 -/
inductive Value : Expr → Prop where
  | var (i : Nat) : Value (.var i)
  | lam (a : Ty) (body : Expr) : Value (.lam a body)
  | tlam (body : Expr) : Value (.tlam body)

/-- 値の自由項変数を改名しても値である。 -/
theorem Value.renameTerm {v : Expr} (hv : Value v) (ρ : Nat → Nat) :
    Value (v.renameTerm ρ) := by
  cases hv with
  | var => exact .var _
  | lam => exact .lam _ _
  | tlam => exact .tlam _

/-- `E` は穴を一つ持つ左から右への値呼び評価文脈。 -/
inductive EvalCtx where
  | hole : EvalCtx
  | appFun : EvalCtx → Expr → EvalCtx
  | appArg : (v : Expr) → Value v → EvalCtx → EvalCtx
  | tapp : EvalCtx → Ty → EvalCtx
  | perform : Op → List Ty → EvalCtx → EvalCtx
  | handle : EvalCtx → Op → Nat → Expr → Expr → EvalCtx

/-- `E[e]` は評価文脈 `E` の穴に `e` を置いた式。 -/
def EvalCtx.plug : EvalCtx → Expr → Expr
  | .hole, e => e
  | .appFun E x, e => .app (E.plug e) x
  | .appArg v _ E, e => .app v (E.plug e)
  | .tapp E a, e => .tapp (E.plug e) a
  | .perform op args E, e => .perform op args (E.plug e)
  | .handle E op n ret clause, e =>
      .handle (E.plug e) op n ret clause

/-- `handled(E)` は `E` に現れる handler 枠の操作名の集合。 -/
def EvalCtx.handled : EvalCtx → Effect
  | .hole => ∅
  | .appFun E _ => E.handled
  | .appArg _ _ E => E.handled
  | .tapp E _ => E.handled
  | .perform _ _ E => E.handled
  | .handle E op _ _ _ => insert op E.handled

/-- 文脈の自由項変数だけを改名する。穴は改名しない。 -/
def EvalCtx.renameTerm (ρ : Nat → Nat) : EvalCtx → EvalCtx
  | .hole => .hole
  | .appFun E x => .appFun (E.renameTerm ρ) (x.renameTerm ρ)
  | .appArg v hv E =>
      .appArg (v.renameTerm ρ) (hv.renameTerm ρ) (E.renameTerm ρ)
  | .tapp E a => .tapp (E.renameTerm ρ) a
  | .perform op args E => .perform op args (E.renameTerm ρ)
  | .handle E op n ret clause =>
      .handle (E.renameTerm ρ) op n
        (ret.renameTerm (liftTermRen ρ))
        (clause.renameTerm (liftTermRenN 2 ρ))

/-- 捕捉された文脈 `E` を同じ handler で包み直す deep な継続。 -/
def Expr.resume (E : EvalCtx) (op : Op) (n : Nat)
    (ret clause : Expr) (resultTy : Ty) : Expr :=
  .lam resultTy
    (.handle ((E.renameTerm Nat.succ).plug (.var 0)) op n
      (ret.renameTerm (liftTermRen Nat.succ))
      (clause.renameTerm (liftTermRenN 2 Nat.succ)))

/-- 操作節の `k` と `x` を、それぞれ deep な継続と引数値で置換する。 -/
def Expr.instantiateOp (body continuation argument : Expr) : Expr :=
  body.substTerm (fun
    | 0 => continuation
    | 1 => argument
    | i + 2 => .var i)

/-- `e → e′` は TeX の簡約規則と評価文脈閉包。 -/
inductive Step (sig : Signature) : Expr → Expr → Prop where
  | beta {a body v} : Value v →
      Step sig (.app (.lam a body) v) (body.instantiate v)
  | typeBeta {body arg} :
      Step sig (.tapp (.tlam body) arg)
        (body.substTy (fun | 0 => arg | i + 1 => .var i))
  | ret {v op n ret clause} : Value v →
      Step sig (.handle v op n ret clause) (ret.instantiate v)
  | operation {E : EvalCtx} {op n ret clause args v decl} :
      sig op = some decl → n = decl.arity →
      args.length = n → Value v → op ∉ E.handled →
      Step sig
        (.handle (E.plug (.perform op args v)) op n ret clause)
        ((clause.instantiateManyTy args).instantiateOp
          (Expr.resume E op n ret clause
            (decl.output.instantiateMany args)) v)
  | context {E : EvalCtx} {e e'} : Step sig e e' →
      Step sig (E.plug e) (E.plug e')

/-- `E[perform op[τ̄] v]` で `op ∉ handled(E)` なら操作は未処理で露出する。 -/
def Unhandled (e : Expr) (op : Op) : Prop :=
  ∃ (E : EvalCtx) (args : List Ty) (v : Expr),
    e = E.plug (.perform op args v) ∧
    Value v ∧ op ∉ E.handled

end SystemFXi
