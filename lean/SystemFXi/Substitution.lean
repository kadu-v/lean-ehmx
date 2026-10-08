import SystemFXi.Syntax

/-!
# 型変数と項変数の置換

型束縛子と項束縛子は別々に持ち上げる。操作節の型束縛子の個数は
handler に記録された操作宣言の `arity` と一致する。
-/

namespace SystemFXi

/-- 束縛子の下へ型変数の改名 `ρ` を移す。 -/
def liftTyRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

/-- 型変数の改名 `ρ` を `n` 個の型束縛子の下へ移す。 -/
def liftTyRenN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | n + 1, ρ => liftTyRen (liftTyRenN n ρ)

/-- `ρ` に沿った型変数の改名。 -/
def Ty.rename (ρ : Nat → Nat) : Ty → Ty
  | .var i => .var (ρ i)
  | .arr a ε b => .arr (a.rename ρ) ε (b.rename ρ)
  | .all body => .all (body.rename (liftTyRen ρ))

/-- 束縛子の下へ型置換 `τ` を移す。 -/
def liftTySubst (τ : Nat → Ty) : Nat → Ty
  | 0 => .var 0
  | i + 1 => (τ i).rename Nat.succ

/-- 型置換 `τ` を `n` 個の型束縛子の下へ移す。 -/
def liftTySubstN : Nat → (Nat → Ty) → Nat → Ty
  | 0, τ => τ
  | n + 1, τ => liftTySubst (liftTySubstN n τ)

/-- `τ` に沿った型変数の同時置換。 -/
def Ty.subst (τ : Nat → Ty) : Ty → Ty
  | .var i => τ i
  | .arr a ε b => .arr (a.subst τ) ε (b.subst τ)
  | .all body => .all (body.subst (liftTySubst τ))

/-- `σ[α ↦ τ]` は最も内側の型変数を `τ` で置換する。 -/
def Ty.instantiate (body arg : Ty) : Ty :=
  body.subst (fun | 0 => arg | i + 1 => .var i)

/-- 束縛子の下へ項変数の改名 `ρ` を移す。 -/
def liftTermRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

/-- 項変数の改名 `ρ` を `n` 個の項束縛子の下へ移す。 -/
def liftTermRenN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | n + 1, ρ => liftTermRen (liftTermRenN n ρ)

@[simp] theorem liftTermRenN_two (ρ : Nat → Nat) :
    liftTermRenN 2 ρ = liftTermRen (liftTermRen ρ) := rfl

/-- 式中の自由項変数を `ρ` で改名する。 -/
def Expr.renameTerm (ρ : Nat → Nat) : Expr → Expr
  | .var i => .var (ρ i)
  | .lam a body => .lam a (body.renameTerm (liftTermRen ρ))
  | .app f x => .app (f.renameTerm ρ) (x.renameTerm ρ)
  | .tlam body => .tlam (body.renameTerm ρ)
  | .tapp e a => .tapp (e.renameTerm ρ) a
  | .perform op args e => .perform op args (e.renameTerm ρ)
  | .handle e op n ret clause =>
      .handle (e.renameTerm ρ) op n
        (ret.renameTerm (liftTermRen ρ))
        (clause.renameTerm (liftTermRenN 2 ρ))

/-- 式中の自由型変数を `ρ` で改名する。 -/
def Expr.renameTy (ρ : Nat → Nat) : Expr → Expr
  | .var i => .var i
  | .lam a body => .lam (a.rename ρ) (body.renameTy ρ)
  | .app f x => .app (f.renameTy ρ) (x.renameTy ρ)
  | .tlam body => .tlam (body.renameTy (liftTyRen ρ))
  | .tapp e a => .tapp (e.renameTy ρ) (a.rename ρ)
  | .perform op args e =>
      .perform op (args.map (Ty.rename ρ)) (e.renameTy ρ)
  | .handle e op n ret clause =>
      .handle (e.renameTy ρ) op n (ret.renameTy ρ)
        (clause.renameTy (liftTyRenN n ρ))

/-- 式中の自由型変数を `τ` で同時置換する。 -/
def Expr.substTy (τ : Nat → Ty) : Expr → Expr
  | .var i => .var i
  | .lam a body => .lam (a.subst τ) (body.substTy τ)
  | .app f x => .app (f.substTy τ) (x.substTy τ)
  | .tlam body => .tlam (body.substTy (liftTySubst τ))
  | .tapp e a => .tapp (e.substTy τ) (a.subst τ)
  | .perform op args e =>
      .perform op (args.map (Ty.subst τ)) (e.substTy τ)
  | .handle e op n ret clause =>
      .handle (e.substTy τ) op n (ret.substTy τ)
        (clause.substTy (liftTySubstN n τ))

/-- 束縛子の下へ項置換 `s` を移す。 -/
def liftTermSubst (s : Nat → Expr) : Nat → Expr
  | 0 => .var 0
  | i + 1 => (s i).renameTerm Nat.succ

/-- 項置換 `s` を `n` 個の項束縛子の下へ移す。 -/
def liftTermSubstN : Nat → (Nat → Expr) → Nat → Expr
  | 0, s => s
  | n + 1, s => liftTermSubst (liftTermSubstN n s)

@[simp] theorem liftTermSubstN_two (s : Nat → Expr) :
    liftTermSubstN 2 s = liftTermSubst (liftTermSubst s) := rfl

/-- `s` の像を `n` 個の型束縛子の下へ移す。 -/
def liftTermSubstTyN (n : Nat) (s : Nat → Expr) : Nat → Expr :=
  fun i => (s i).renameTy (fun j => j + n)

/-- 式中の自由項変数を `s` で同時置換する。 -/
def Expr.substTerm (s : Nat → Expr) : Expr → Expr
  | .var i => s i
  | .lam a body => .lam a (body.substTerm (liftTermSubst s))
  | .app f x => .app (f.substTerm s) (x.substTerm s)
  | .tlam body => .tlam (body.substTerm (liftTermSubstTyN 1 s))
  | .tapp e a => .tapp (e.substTerm s) a
  | .perform op args e => .perform op args (e.substTerm s)
  | .handle e op n ret clause =>
      .handle (e.substTerm s) op n
        (ret.substTerm (liftTermSubst s))
        (clause.substTerm (liftTermSubstN 2 (liftTermSubstTyN n s)))

/-- `e[x ↦ v]` は最も内側の項変数を `v` で置換する。 -/
def Expr.instantiate (body value : Expr) : Expr :=
  body.substTerm (fun | 0 => value | i + 1 => .var i)

end SystemFXi
