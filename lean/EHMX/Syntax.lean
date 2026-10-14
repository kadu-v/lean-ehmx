import EHMX.Effect

namespace EHMX

inductive BaseTy where
  | int | bool | other : Nat → BaseTy
  deriving DecidableEq

inductive Expr where
  | var : Nat → Expr
  | int : Int → Expr
  | bool : Bool → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  | letE : Expr → Expr → Expr
  | perform : Op → Expr → Expr
  | handle : Expr → Op → Expr → Expr → Expr
  deriving DecidableEq

inductive Value : Expr → Prop where
  | var (i : Nat) : Value (.var i)
  | int (n : Int) : Value (.int n)
  | bool (b : Bool) : Value (.bool b)
  | lam (body : Expr) : Value (.lam body)

def Value.isValue : Expr → Bool
  | .var _ | .int _ | .bool _ | .lam _ => true
  | _ => false

@[simp] theorem Value.isValue_iff (e : Expr) : Value.isValue e = true ↔ Value e := by
  cases e <;> simp [Value.isValue]
  all_goals first | constructor | (intro h; cases h)

end EHMX
