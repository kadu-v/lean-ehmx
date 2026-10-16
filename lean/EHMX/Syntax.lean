import EHMX.Effect

namespace EHMX

/-- Constants are typed by the finite initial environment, not by a mandatory
collection of closed types in the abstract type algebra. -/
inductive Constant where
  | int : Int → Constant
  | bool : Bool → Constant
  | named : Nat → Constant
  deriving DecidableEq

inductive Expr where
  | var : Nat → Expr
  | const : Constant → Expr
  | lam : Expr → Expr
  | app : Expr → Expr → Expr
  | letE : Expr → Expr → Expr
  | perform : Op → Expr → Expr
  | handle : Expr → Op → Expr → Expr → Expr
  deriving DecidableEq

inductive Value : Expr → Prop where
  | var (i : Nat) : Value (.var i)
  | const (k : Constant) : Value (.const k)
  | lam (body : Expr) : Value (.lam body)

def Value.isValue : Expr → Bool
  | .var _ | .const _ | .lam _ => true
  | _ => false

@[simp] theorem Value.isValue_iff (e : Expr) : Value.isValue e = true ↔ Value e := by
  cases e <;> simp [Value.isValue]
  all_goals first | constructor | (intro h; cases h)

end EHMX
