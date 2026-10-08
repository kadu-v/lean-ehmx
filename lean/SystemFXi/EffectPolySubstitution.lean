import SystemFXi.EffectPoly

/-!
# 型・効果変数の同時置換

型と効果の変数は共通の kind 環境を参照する。束縛子の下では両方の
de Bruijn 添字を一つ持ち上げる。操作節の量化列も同様に扱う。
-/

namespace SystemFXi.Poly

/-- 一つの型・効果束縛子の内側への改名。 -/
def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

/-- 複数の型・効果束縛子の内側への改名。 -/
def liftRenN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | n + 1, ρ => liftRen (liftRenN n ρ)

/-- ε の自由効果変数を改名する。 -/
def Effect.renameVars (ε : Effect) (ρ : Nat → Nat) : Effect :=
  ε.rename ρ

/-- σ の自由な型・効果変数を同時に改名する。 -/
def Ty.rename (ρ : Nat → Nat) : Ty → Ty
  | .var i => .var (ρ i)
  | .arr a ε b => .arr (a.rename ρ) (ε.rename ρ) (b.rename ρ)
  | .all κ body => .all κ (body.rename (liftRen ρ))

/-- θ の自由な型・効果変数を改名する。 -/
def Arg.rename (ρ : Nat → Nat) : Arg → Arg
  | .type σ => .type (σ.rename ρ)
  | .effect ε => .effect (ε.rename ρ)

/-- 型と効果の両方を同時に置換する写像。 -/
structure KindSubst where
  types : Nat → Ty
  effects : Nat → Effect

/-- 置換写像を型・効果束縛子の下へ持ち上げる。 -/
def KindSubst.lift (τ : KindSubst) : KindSubst where
  types
    | 0 => .var 0
    | i + 1 => (τ.types i).rename Nat.succ
  effects
    | 0 => Effect.var 0
    | i + 1 => (τ.effects i).rename Nat.succ

/-- 置換写像を量化列の下へ持ち上げる。 -/
def KindSubst.liftN : Nat → KindSubst → KindSubst
  | 0, τ => τ
  | n + 1, τ => (τ.liftN n).lift

/-- ε[τ] は効果変数への捕獲回避置換。 -/
def Effect.substKind (ε : Effect) (τ : KindSubst) : Effect :=
  ε.subst τ.effects

/-- 恒等改名は効果を変えない: id(ε) = ε。 -/
theorem Effect.rename_id (ε : Effect) : ε.rename id = ε := by
  cases ε
  simp [Effect.rename]

/-- 効果変数の改名の合成。 -/
theorem Effect.rename_comp (ε : Effect) (ρ υ : Nat → Nat) :
    (ε.rename ρ).rename υ = ε.rename (fun i => υ (ρ i)) := by
  cases ε
  simp [Effect.rename, Finset.image_image, Function.comp_def]

/-- 恒等置換は効果を変えない: ε[μ ↦ μ] = ε。 -/
theorem Effect.subst_id (ε : Effect) :
    ε.subst Effect.var = ε := by
  cases ε with
  | mk labels vars =>
      simp [Effect.subst, Effect.var]

/-- 効果式の置換は和集合へ分配する。 -/
theorem Effect.subst_union (ε η : Effect) (τ : Nat → Effect) :
    (ε ∪ η).subst τ = ε.subst τ ∪ η.subst τ := by
  cases ε with
  | mk labels vars =>
      cases η with
      | mk labels' vars' =>
          apply congrArg₂ Effect.mk
          · simp [Effect.subst, Finset.union_biUnion,
              Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
          · simp [Effect.subst, Finset.union_biUnion]

/-- 効果変数の単元への置換はその像である。 -/
theorem Effect.subst_var (μ : Nat) (τ : Nat → Effect) :
    (Effect.var μ).subst τ = τ μ := by
  cases h : τ μ with
  | mk labels vars =>
      simp [Effect.subst, Effect.var, h]

/-- 効果置換後の改名は、各置換像を改名することに等しい。 -/
theorem Effect.subst_rename (ε : Effect) (τ : Nat → Effect)
    (ρ : Nat → Nat) :
    (ε.subst τ).rename ρ =
      ε.subst (fun μ => (τ μ).rename ρ) := by
  cases ε with
  | mk labels vars =>
      apply congrArg₂ Effect.mk
      · simp [Effect.subst, Effect.rename]
      · simp [Effect.subst, Effect.rename, Finset.biUnion_image]

/-- 改名後の効果置換は、置換写像の添字を先に改名することに等しい。 -/
theorem Effect.rename_subst (ε : Effect) (ρ : Nat → Nat)
    (τ : Nat → Effect) :
    (ε.rename ρ).subst τ =
      ε.subst (fun μ => τ (ρ μ)) := by
  cases ε with
  | mk labels vars =>
      apply congrArg₂ Effect.mk
      · simp [Effect.rename, Finset.image_biUnion]
      · simp [Effect.rename, Finset.image_biUnion]

/-- 二つの効果置換は像に対する置換の合成に等しい。 -/
theorem Effect.subst_subst (ε : Effect) (τ υ : Nat → Effect) :
    (ε.subst τ).subst υ =
      ε.subst (fun μ => (τ μ).subst υ) := by
  cases ε with
  | mk labels vars =>
      apply congrArg₂ Effect.mk
      · simp [Effect.subst, Finset.biUnion_union,
          Finset.biUnion_biUnion, Finset.union_assoc]
      · simp [Effect.subst, Finset.biUnion_biUnion]

/-- σ[τ] は型・効果変数への捕獲回避同時置換。 -/
def Ty.subst (τ : KindSubst) : Ty → Ty
  | .var i => τ.types i
  | .arr a ε b => .arr (a.subst τ) (ε.substKind τ) (b.subst τ)
  | .all κ body => .all κ (body.subst τ.lift)

/-- θ[τ] は kind に応じた置換。 -/
def Arg.subst (τ : KindSubst) : Arg → Arg
  | .type σ => .type (σ.subst τ)
  | .effect ε => .effect (ε.substKind τ)

/-- θ を最も内側の型・効果変数に代入する。 -/
def KindSubst.single : Arg → KindSubst
  | .type σ =>
      { types := fun | 0 => σ | i + 1 => .var i
        effects := fun | 0 => Effect.var 0 | i + 1 => Effect.var i }
  | .effect ε =>
      { types := fun | 0 => .var 0 | i + 1 => .var i
        effects := fun | 0 => ε | i + 1 => Effect.var i }

/-- [β ↦ θ]σ は最も内側の kind 束縛子を具体化する。 -/
def Ty.instantiate (body : Ty) (arg : Arg) : Ty :=
  body.subst (KindSubst.single arg)

/-- 型・効果変数の改名は、項の型注釈にも作用する。 -/
def Expr.renameKind (ρ : Nat → Nat) : Expr → Expr
  | .var i => .var i
  | .lam a body => .lam (a.rename ρ) (body.renameKind ρ)
  | .app f x => .app (f.renameKind ρ) (x.renameKind ρ)
  | .tlam κ body => .tlam κ (body.renameKind (liftRen ρ))
  | .tapp e arg => .tapp (e.renameKind ρ) (arg.rename ρ)
  | .perform op args e =>
      .perform op (args.map (Arg.rename ρ)) (e.renameKind ρ)
  | .handle e op n ret clause =>
      .handle (e.renameKind ρ) op n (ret.renameKind ρ)
        (clause.renameKind (liftRenN n ρ))

/-- 型・効果変数の同時置換は、項の型注釈にも作用する。 -/
def Expr.substKind (τ : KindSubst) : Expr → Expr
  | .var i => .var i
  | .lam a body => .lam (a.subst τ) (body.substKind τ)
  | .app f x => .app (f.substKind τ) (x.substKind τ)
  | .tlam κ body => .tlam κ (body.substKind τ.lift)
  | .tapp e arg => .tapp (e.substKind τ) (arg.subst τ)
  | .perform op args e =>
      .perform op (args.map (Arg.subst τ)) (e.substKind τ)
  | .handle e op n ret clause =>
      .handle (e.substKind τ) op n (ret.substKind τ)
        (clause.substKind (τ.liftN n))

/-- 型・効果変数の混合引数列による同時置換。 -/
def KindSubst.many (args : List Arg) : KindSubst where
  types i :=
    match args[i]? with
    | some (.type σ) => σ
    | _ => .var (i - args.length)
  effects i :=
    match args[i]? with
    | some (.effect ε) => ε
    | _ => Effect.var (i - args.length)

/-- 操作宣言型を混合引数列で具体化する。 -/
def Ty.instantiateMany (body : Ty) (args : List Arg) : Ty :=
  body.subst (KindSubst.many args)

/-- 操作節を混合引数列で具体化する。 -/
def Expr.instantiateMany (body : Expr) (args : List Arg) : Expr :=
  body.substKind (KindSubst.many args)

/-- 項変数の改名を一つの λ・return 束縛子の下へ移す。 -/
def liftTermRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ρ i + 1

/-- 項変数の改名を複数の束縛子の下へ移す。 -/
def liftTermRenN : Nat → (Nat → Nat) → Nat → Nat
  | 0, ρ => ρ
  | n + 1, ρ => liftTermRen (liftTermRenN n ρ)

@[simp] theorem liftTermRenN_two (ρ : Nat → Nat) :
    liftTermRenN 2 ρ = liftTermRen (liftTermRen ρ) := rfl

/-- 項変数を改名する。 -/
def Expr.renameTerm (ρ : Nat → Nat) : Expr → Expr
  | .var i => .var (ρ i)
  | .lam a body => .lam a (body.renameTerm (liftTermRen ρ))
  | .app f x => .app (f.renameTerm ρ) (x.renameTerm ρ)
  | .tlam κ body => .tlam κ (body.renameTerm ρ)
  | .tapp e arg => .tapp (e.renameTerm ρ) arg
  | .perform op args e => .perform op args (e.renameTerm ρ)
  | .handle e op n ret clause =>
      .handle (e.renameTerm ρ) op n
        (ret.renameTerm (liftTermRen ρ))
        (clause.renameTerm (liftTermRenN 2 ρ))

/-- 項置換を一つの項束縛子の下へ移す。 -/
def liftTermSubst (s : Nat → Expr) : Nat → Expr
  | 0 => .var 0
  | i + 1 => (s i).renameTerm Nat.succ

/-- 項置換を複数の項束縛子の下へ移す。 -/
def liftTermSubstN : Nat → (Nat → Expr) → Nat → Expr
  | 0, s => s
  | n + 1, s => liftTermSubst (liftTermSubstN n s)

@[simp] theorem liftTermSubstN_two (s : Nat → Expr) :
    liftTermSubstN 2 s = liftTermSubst (liftTermSubst s) := rfl

/-- 項置換像を型・効果束縛子の下へ移す。 -/
def liftTermSubstKindN (n : Nat) (s : Nat → Expr) : Nat → Expr :=
  fun i => (s i).renameKind (fun j => j + n)

/-- 項変数への捕獲回避同時置換。 -/
def Expr.substTerm (s : Nat → Expr) : Expr → Expr
  | .var i => s i
  | .lam a body => .lam a (body.substTerm (liftTermSubst s))
  | .app f x => .app (f.substTerm s) (x.substTerm s)
  | .tlam κ body => .tlam κ (body.substTerm (liftTermSubstKindN 1 s))
  | .tapp e arg => .tapp (e.substTerm s) arg
  | .perform op args e => .perform op args (e.substTerm s)
  | .handle e op n ret clause =>
      .handle (e.substTerm s) op n
        (ret.substTerm (liftTermSubst s))
        (clause.substTerm (liftTermSubstN 2 (liftTermSubstKindN n s)))

/-- [x ↦ v]e は最も内側の項変数を値で置換する。 -/
def Expr.instantiate (body value : Expr) : Expr :=
  body.substTerm (fun | 0 => value | i + 1 => .var i)

end SystemFXi.Poly
