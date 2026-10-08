import SystemFXi.EffectPolyTyping

/-!
# 効果多相な値呼び評価

評価文脈は左から右へ進む。操作節で捕捉した文脈は同じ handler で
包み直すので、継続は deep である。
-/

namespace SystemFXi.Poly

/-- v は項変数、項抽象、kind 付き抽象のいずれか。 -/
inductive Value : Expr → Prop where
  | var (i : Nat) : Value (.var i)
  | lam (a : Ty) (body : Expr) : Value (.lam a body)
  | tlam (κ : Kind) (body : Expr) : Value (.tlam κ body)

/-- 値の項変数改名は値を保つ。 -/
theorem Value.renameTerm {v : Expr} (hv : Value v) (ρ : Nat → Nat) :
    Value (v.renameTerm ρ) := by
  cases hv with
  | var => exact .var _
  | lam => exact .lam _ _
  | tlam => exact .tlam _ _

/-- E は穴を一つ持つ値呼び評価文脈。 -/
inductive EvalCtx where
  | hole : EvalCtx
  | appFun : EvalCtx → Expr → EvalCtx
  | appArg : (v : Expr) → Value v → EvalCtx → EvalCtx
  | tapp : EvalCtx → Arg → EvalCtx
  | perform : Op → List Arg → EvalCtx → EvalCtx
  | handle : EvalCtx → Op → Nat → Expr → Expr → EvalCtx

/-- E[e] は評価文脈への式の代入。 -/
def EvalCtx.plug : EvalCtx → Expr → Expr
  | .hole, e => e
  | .appFun E x, e => .app (E.plug e) x
  | .appArg v _ E, e => .app v (E.plug e)
  | .tapp E arg, e => .tapp (E.plug e) arg
  | .perform op args E, e => .perform op args (E.plug e)
  | .handle E op n ret clause, e =>
      .handle (E.plug e) op n ret clause

/-- handled(E) は穴の外側の handler が処理する操作の集合。 -/
def EvalCtx.handled : EvalCtx → Finset Op
  | .hole => ∅
  | .appFun E _ => E.handled
  | .appArg _ _ E => E.handled
  | .tapp E _ => E.handled
  | .perform _ _ E => E.handled
  | .handle E op _ _ _ => insert op E.handled

/-- 文脈の自由項変数だけを改名する。 -/
def EvalCtx.renameTerm (ρ : Nat → Nat) : EvalCtx → EvalCtx
  | .hole => .hole
  | .appFun E x => .appFun (E.renameTerm ρ) (x.renameTerm ρ)
  | .appArg v hv E =>
      .appArg (v.renameTerm ρ) (hv.renameTerm ρ) (E.renameTerm ρ)
  | .tapp E arg => .tapp (E.renameTerm ρ) arg
  | .perform op args E => .perform op args (E.renameTerm ρ)
  | .handle E op n ret clause =>
      .handle (E.renameTerm ρ) op n
        (ret.renameTerm (liftTermRen ρ))
        (clause.renameTerm (liftTermRenN 2 ρ))

/-- E を h で包み直す deep 継続。 -/
def Expr.resume (E : EvalCtx) (op : Op) (n : Nat)
    (ret clause : Expr) (resultTy : Ty) : Expr :=
  .lam resultTy
    (.handle ((E.renameTerm Nat.succ).plug (.var 0)) op n
      (ret.renameTerm (liftTermRen Nat.succ))
      (clause.renameTerm (liftTermRenN 2 Nat.succ)))

/-- 操作節の k と x を継続と引数値で置換する。 -/
def Expr.instantiateOp (body continuation argument : Expr) : Expr :=
  body.substTerm (fun
    | 0 => continuation
    | 1 => argument
    | i + 2 => .var i)

/-- e → e′ は値呼びの一歩簡約。 -/
inductive Step (sig : Signature) : Expr → Expr → Prop where
  | beta {a body v} : Value v →
      Step sig (.app (.lam a body) v) (body.instantiate v)
  | kindBeta {κ body arg} :
      Step sig (.tapp (.tlam κ body) arg)
        (body.substKind (KindSubst.single arg))
  | ret {v op n ret clause} : Value v →
      Step sig (.handle v op n ret clause) (ret.instantiate v)
  | operation {E : EvalCtx} {op n ret clause args v decl} :
      sig op = some decl → n = decl.kinds.length →
      args.length = n → Value v → op ∉ E.handled →
      Step sig
        (.handle (E.plug (.perform op args v)) op n ret clause)
        ((clause.instantiateMany args).instantiateOp
          (Expr.resume E op n ret clause
            (decl.output.instantiateMany args)) v)
  | context {E : EvalCtx} {e e'} : Step sig e e' →
      Step sig (E.plug e) (E.plug e')

/-- 未処理操作は最も内側の該当 handler の外で露出する。 -/
def Unhandled (e : Expr) (op : Op) : Prop :=
  ∃ (E : EvalCtx) (args : List Arg) (v : Expr),
    e = E.plug (.perform op args v) ∧
    Value v ∧ op ∉ E.handled

end SystemFXi.Poly
