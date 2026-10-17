import HMX.LocallyNameless.ProofSupport
import Mathlib.Data.List.Basic

namespace HMX.LN.Proofs

/-- Generalize the insertion depth before structural induction. -/
theorem exprOpenClose (t : Expr) (d z : Nat) :
    Expr.openAt d (.ident (.free (.var z))) (t.closeAt d z) = t := by
  induction t generalizing d with
  | ident x =>
      cases x with
      | free x => by_cases h : x = .var z <;> simp [Expr.closeAt, Expr.openAt, Expr.shift, h]
      | bound i =>
          by_cases h : i < d
          · simp [Expr.closeAt, Expr.openAt, h, Nat.ne_of_lt h]
          · have hne : i + 1 ≠ d := by omega
            have hnlt : ¬ i + 1 < d := by omega
            simp [Expr.closeAt, Expr.openAt, h, hne, hnlt]
  | lam t ih => simp [Expr.closeAt, Expr.openAt, ih]
  | app t u iht ihu => simp [Expr.closeAt, Expr.openAt, iht, ihu]
  | letE t u iht ihu => simp [Expr.closeAt, Expr.openAt, iht, ihu]

theorem exprCloseOpen (t : Expr) (d z : Nat) (hz : Id.var z ∉ t.fpi) :
    (Expr.openAt d (.ident (.free (.var z))) t).closeAt d z = t := by
  induction t generalizing d with
  | ident x =>
      cases x with
      | free x =>
          have hx : x ≠ .var z := by simpa [Expr.fpi, eq_comm] using hz
          simp [Expr.openAt, Expr.closeAt, hx]
      | bound i =>
          by_cases he : i = d
          · subst i; simp [Expr.openAt, Expr.shift, Expr.closeAt]
          · by_cases hl : i < d
            · simp [Expr.openAt, Expr.closeAt, he, hl]
            · have hn : ¬ i - 1 < d := by omega
              have hi : i - 1 + 1 = i := by omega
              simp [Expr.openAt, Expr.closeAt, he, hl, hn, hi]
  | lam t ih => simpa [Expr.openAt, Expr.closeAt] using congrArg Expr.lam (ih d.succ hz)
  | app t u iht ihu =>
      simp only [Expr.fpi, Finset.mem_union, not_or] at hz
      simp [Expr.openAt, Expr.closeAt, iht _ hz.1, ihu _ hz.2]
  | letE t u iht ihu =>
      simp only [Expr.fpi, Finset.mem_union, not_or] at hz
      simp [Expr.openAt, Expr.closeAt, iht _ hz.1, ihu _ hz.2]

theorem termOpeningClosing : HMX.LN.termOpeningClosing := by
  exact ⟨fun t z _ => exprOpenClose t 0 z, fun t z _ hz => exprCloseOpen t 0 z hz⟩

/-- Structural induction with an elementwise hypothesis for constructor arguments. -/
theorem tyInduction {P : Ty → Prop}
    (hf : ∀ X, P (.free X)) (hb : ∀ i, P (.bound i))
    (hc : ∀ f ts, (∀ T ∈ ts, P T) → P (.con f ts)) (T : Ty) : P T := by
  exact Ty.rec (motive_1 := P) (motive_2 := fun ts => ∀ T ∈ ts, P T)
    hf hb hc (by simp) (by intro h ts hh ht T hm; rcases List.mem_cons.mp hm with rfl | hm; exact hh; exact ht T hm) T

theorem tyOpenClose (T : Ty) (d : Nat) (xs : List TVar) :
    (T.closeAt d xs).openAt d (xs.map Ty.free) = T := by
  induction T using tyInduction generalizing d with
  | hf X =>
      by_cases hx : X ∈ xs
      · simp [Ty.closeAt, Ty.openAt, hx, List.getElem?_map, List.getElem?_idxOf hx, Ty.shift]
      · simp [Ty.closeAt, Ty.openAt, hx]
  | hb i =>
      by_cases h : i < d
      · simp [Ty.closeAt, Ty.openAt, h]
      · have hlt : ¬ i + xs.length < d := by omega
        have hn : (xs.map Ty.free)[i + xs.length - d]? = none := by
          apply List.getElem?_eq_none
          simp only [List.length_map]
          omega
        simp [Ty.closeAt, Ty.openAt, h, hlt, hn]
  | hc f ts ih =>
      simp only [Ty.closeAt, Ty.openAt, List.map_map]
      congr 1
      exact (show ts.map (Ty.openAt d (xs.map Ty.free) ∘ Ty.closeAt d xs) = ts.map id from
        List.map_congr_left (fun T hT => ih T hT d)).trans (List.map_id ts)

theorem tyCloseOpen (T : Ty) (d : Nat) (xs : List TVar) (hn : xs.Nodup)
    (hf : Disjoint xs.toFinset T.fv) :
    (T.openAt d (xs.map Ty.free)).closeAt d xs = T := by
  induction T using tyInduction generalizing d with
  | hf X =>
      have hx : X ∉ xs := by simpa [Ty.fv, Finset.disjoint_singleton_right] using hf
      simp [Ty.openAt, Ty.closeAt, hx]
  | hb i =>
      by_cases hid : i < d
      · simp [Ty.openAt, Ty.closeAt, hid]
      · by_cases hin : i - d < xs.length
        · have hget := List.getElem?_eq_getElem hin
          have hx : xs[i-d] ∈ xs := List.getElem_mem hin
          have heq : d + (i - d) = i := by omega
          simp [Ty.openAt, Ty.closeAt, hid, List.getElem?_map, hget, Ty.shift, hx,
            hn.idxOf_getElem (i-d) hin, heq]
        · have hget : (xs.map Ty.free)[i-d]? = none := by
            apply List.getElem?_eq_none
            simp only [List.length_map]
            omega
          have hnot : ¬ i - xs.length < d := by omega
          have hi : i - xs.length + xs.length = i := by omega
          simp [Ty.openAt, Ty.closeAt, hid, hget, hnot, hi]
  | hc f ts ih =>
      simp only [Ty.openAt, Ty.closeAt, List.map_map]
      congr 1
      apply Eq.trans ?_ (List.map_id _)
      apply List.map_congr_left
      intro U hU
      apply ih U hU d
      apply Finset.disjoint_left.mpr
      intro X hx hu
      apply Finset.disjoint_left.mp hf hx
      simp only [Ty.fv]
      have : U.fv ⊆ (ts.map Ty.fv).foldr (· ∪ ·) ∅ := by
        clear ih hf
        induction ts with
        | nil => simp at hU
        | cons V vs hvs =>
            simp only [List.mem_cons] at hU
            rcases hU with rfl | hU
            · exact Finset.subset_union_left
            · exact Finset.Subset.trans (hvs hU) Finset.subset_union_right
      exact this hu

theorem typeOpeningClosing : HMX.LN.typeOpeningClosing := by
  exact ⟨fun xs T _ _ => tyOpenClose T 0 xs, fun xs T hn _ hf => tyCloseOpen T 0 xs hn hf⟩

/-- A pointwise inverse lifts through both mutually recursive type traversals. -/
theorem constraintMapTypesInverse (f g : Nat → Ty → Ty)
    (h : ∀ d T, g d (f d T) = T) (C : Constraint) (d : Nat) :
    (C.mapTypes f d).mapTypes g d = C := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, (C.mapTypes f d).mapTypes g d = C)
    (motive_2 := fun s => ∀ d, (s.mapTypes f d).mapTypes g d = s)
    (by intro d; rfl) (by intro d; rfl)
    (by
      intro p ts d
      simp only [Constraint.mapTypes, List.map_map]
      congr 1
      exact (show ts.map (g d ∘ f d) = ts.map id from
        List.map_congr_left (fun T _ => h d T)).trans (List.map_id ts))
    (by intros; simp_all [Constraint.mapTypes])
    (by intros; simp_all [Constraint.mapTypes])
    (by intros; simp_all [Constraint.mapTypes])
    (by intros; simp_all [Constraint.mapTypes])
    (by intros; simp_all [Scheme.mapTypes]) C d

theorem constraintOpeningClosing (S : Signature) : HMX.LN.constraintOpeningClosing S := by
  intro xs C _ _
  exact constraintMapTypesInverse _ _ (fun d T => tyOpenClose T d xs) C 0

end HMX.LN.Proofs
