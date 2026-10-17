import HMX.LocallyNameless.Proofs.CorrespondenceSupport
import HMX.LocallyNameless.Proofs.TermRenaming

namespace HMX.LN.Proofs

/-- Rename free identifiers only; binders remain de Bruijn indices. -/
def exprMapIds (f : Id → Id) : Expr → Expr
  | .ident (.free x) => .ident (.free (f x))
  | .ident (.bound i) => .ident (.bound i)
  | .lam t => .lam (exprMapIds f t)
  | .app t u => .app (exprMapIds f t) (exprMapIds f u)
  | .letE t u => .letE (exprMapIds f t) (exprMapIds f u)

theorem exprMapIdsLC (f : Id → Id) (t : Expr) (n : Nat) (h : t.LCAt n) :
    (exprMapIds f t).LCAt n := by
  induction t generalizing n with
  | ident x => cases x <;> exact h
  | lam t ih => exact ih _ h
  | app t u iht ihu => exact ⟨iht _ h.1, ihu _ h.2⟩
  | letE t u iht ihu => exact ⟨iht _ h.1, ihu _ h.2⟩

theorem exprMapIdsIdentity (t : Expr) : exprMapIds id t = t := by
  induction t with
  | ident x => cases x <;> rfl
  | lam t ih => exact congrArg Expr.lam ih
  | app t u iht ihu => exact congrArg₂ Expr.app iht ihu
  | letE t u iht ihu => exact congrArg₂ Expr.letE iht ihu

theorem encodingExprOpenMap (t : HMX.Expr) (pre : List Id) (z : Nat)
    (w : Id) (f : Id → Id) :
    exprMapIds (Function.update f (.var z) w) (ofExpr pre t) =
      Expr.openAt pre.length (.ident (.free w)) (exprMapIds f (ofExpr (pre ++ [.var z]) t)) := by
  induction t generalizing pre with
  | ident x =>
    by_cases hp : x ∈ pre
    · have hi := List.idxOf_lt_length_iff.mpr hp
      simp [ofExpr, ofId, hp, List.idxOf_append_of_mem hp, exprMapIds, Expr.openAt,
        show pre.idxOf x ≠ pre.length by omega, show ¬ pre.length ≤ pre.idxOf x by omega]
    · by_cases hx : x = .var z
      · subst x
        simp [ofExpr, ofId, hp, List.idxOf_append_of_notMem hp, exprMapIds, Expr.openAt,
          Expr.shift]
      · simp [ofExpr, ofId, hp, hx, exprMapIds, Expr.openAt]
  | lam y t ih =>
    simpa only [ofExpr, exprMapIds, Expr.openAt, List.cons_append, List.length_cons] using
      congrArg Expr.lam (ih (.var y :: pre))
  | app t u iht ihu =>
    exact congrArg₂ Expr.app (iht pre) (ihu pre)
  | letE y t u iht ihu =>
    exact congrArg₂ Expr.letE (iht pre) (ihu (.var y :: pre))

theorem tyBoundRenameFv (T : Ty) (n : Nat) (p : Nat → Nat) :
    (T.renameAt n p).fv = T.fv := by
  induction T using tyInduction with
  | hf X => simp [Ty.renameAt, Ty.fv]
  | hb i => simp [Ty.renameAt, Ty.fv]
  | hc f ts ih =>
    simp only [Ty.renameAt, Ty.fv, List.map_map, Function.comp_def]
    rw [List.map_congr_left (fun U hu => ih U hu)]

theorem constraintBoundRenameFv (C : Constraint) (n : Nat) (p : Nat → Nat) :
    (C.mapTypes (fun d T => T.renameAt d p) n).fv = C.fv := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ n, (C.mapTypes (fun d T => T.renameAt d p) n).fv = C.fv)
    (motive_2 := fun s => ∀ n, (s.mapTypes (fun d T => T.renameAt d p) n).fv = s.fv)
    (by intro; rfl) (by intro; rfl)
    (by intro q ts n; simp [Constraint.mapTypes, Constraint.fv, List.map_map,
      Function.comp_def, tyBoundRenameFv])
    (by intro C D hc hd n; exact congrArg₂ (· ∪ ·) (hc n) (hd n))
    (by intro ks C hc n; exact hc _)
    (by intro b s C hs hc n; exact congrArg₂ (· ∪ ·) (hs n) (hc n))
    (by intro x T n; exact tyBoundRenameFv T n p)
    (by intro ks C T hc n; exact congrArg₂ (· ∪ ·) (hc _) (tyBoundRenameFv T _ p)) C n

theorem constraintBinderEqFv (h : Constraint.BinderEq C D) : C.fv = D.fv := by
  apply Constraint.BinderEq.rec
    (motive_1 := fun C D _ => C.fv = D.fv)
    (motive_2 := fun s r _ => s.fv = r.fv)
    rfl (fun _ ih => ih.symm) (fun _ _ ih ij => ih.trans ij)
    (fun _ _ ih ij => congrArg₂ (· ∪ ·) ih ij)
    (by intro ks ls p D C hp h ih; exact (constraintBoundRenameFv C 0 p).symm.trans ih)
    (fun _ _ ih ij => congrArg₂ (· ∪ ·) ih ij)
    rfl (fun _ ih => ih.symm) (fun _ _ ih ij => ih.trans ij)
    (fun _ _ ht ih => congrArg₂ (· ∪ ·)
      ((constraintBoundRenameFv _ _ _).symm.trans ih)
      ((tyBoundRenameFv _ _ _).symm.trans (congrArg Ty.fv ht))) h

theorem schemeBinderEqFv (h : Scheme.BinderEq s r) : s.fv = r.fv := by
  apply Scheme.BinderEq.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun s r _ => s.fv = r.fv)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    rfl (fun _ ih => ih.symm) (fun _ _ ih ij => ih.trans ij)
    (fun _ hc ht _ => congrArg₂ (· ∪ ·)
      ((constraintBoundRenameFv _ _ _).symm.trans (constraintBinderEqFv hc))
      ((tyBoundRenameFv _ _ _).symm.trans (congrArg Ty.fv ht))) h

theorem encodingEnvAlpha (h : HMX.Env.Alpha Γ Δ) : (ofEnv Γ).BinderEq (ofEnv Δ) := by
  induction h with
  | nil => exact .nil
  | cons hp ht ih => exact .cons ⟨hp.1, encodingAlpha.2.2 _ _ hp.2⟩ ih

theorem envBinderEqFv (h : Env.BinderEq Γ Δ) : Γ.fv = Δ.fv := by
  induction h with
  | nil => rfl
  | cons hp ht ih => exact congrArg₂ (· ∪ ·) (schemeBinderEqFv hp.2) ih

theorem lookupAppendOne {α : Type} (Γ : List (Id × α)) (x y : Id) (s : α) :
    lookup (Γ ++ [(y,s)]) x = if y = x then some s else lookup Γ x := by
  by_cases h : y = x <;> simp [lookup, List.reverse_append, h]

theorem envBinderEqLookupRel (h : Env.BinderEq Γ Δ) (x : Id) :
    Option.Rel Scheme.BinderEq (lookup Γ x) (lookup Δ x) := by
  induction h with
  | nil => exact .none
  | @cons p q Γ Δ hp ht ih =>
    rw [lookupCons, lookupCons]
    generalize lookup Γ x = a at ih ⊢
    generalize lookup Δ x = b at ih ⊢
    cases ih with
    | some h => exact .some h
    | none =>
      rw [← hp.1]
      by_cases hx : x = p.1
      · simp only [hx, ↓reduceIte]; exact .some hp.2
      · simp only [hx, ↓reduceIte]; exact .none

theorem envBinderEqLookup (h : Env.BinderEq Γ Δ) (hl : lookup Γ x = some s) :
    ∃ r, lookup Δ x = some r ∧ s.BinderEq r := by
  have hr := envBinderEqLookupRel h x
  rw [hl] at hr
  generalize lookup Δ x = b at hr ⊢
  cases hr with
  | some h => exact ⟨_, rfl, h⟩

end HMX.LN.Proofs
