import HMX.LocallyNameless.Proofs.WellFormed

namespace HMX.LN.Proofs

theorem exprOpenBelow (t v : Expr) (n d : Nat) (h : t.LCAt n) (hd : n ≤ d) :
    Expr.openAt d v t = t := by
  induction t generalizing n d with
  | ident x =>
      cases x with
      | free x => rfl
      | bound i =>
          have hi : i < d := Nat.lt_of_lt_of_le h hd
          simp [Expr.openAt, Nat.ne_of_lt hi, hi]
  | lam t ih => simp only [Expr.openAt]; rw [ih (n+1) (d+1) h (by omega)]
  | app t u iht ihu => simp only [Expr.openAt]; rw [iht n d h.1 hd, ihu n d h.2 hd]
  | letE t u iht ihu => simp only [Expr.openAt]; rw [iht n d h.1 hd, ihu (n+1) (d+1) h.2 (by omega)]

theorem exprOpenSubst (t v : Expr) (d z x : Nat) (hv : v.LCAt 0) (hx : x ≠ z) :
    Expr.subst z v (Expr.openAt d (.ident (.free (.var x))) t) =
      Expr.openAt d (.ident (.free (.var x))) (Expr.subst z v t) := by
  induction t generalizing d with
  | ident y =>
      cases y with
      | free y =>
          by_cases hy : y = .var z
          · simp [Expr.openAt, Expr.subst, hy, exprOpenBelow v _ 0 d hv (Nat.zero_le d)]
          · simp [Expr.openAt, Expr.subst, hy]
      | bound i =>
          by_cases hi : i = d
          · simp [Expr.openAt, Expr.shift, Expr.subst, hi, hx]
          · by_cases hid : i < d <;> simp [Expr.openAt, Expr.subst, hi, hid]
  | lam t ih => simp [Expr.openAt, Expr.subst, ih]
  | app t u iht ihu => simp [Expr.openAt, Expr.subst, iht, ihu]
  | letE t u iht ihu => simp [Expr.openAt, Expr.subst, iht, ihu]

theorem termOpeningSubstitution : HMX.LN.termOpeningSubstitution := by
  intro t v z x _ hv hx
  exact exprOpenSubst t v 0 z x hv hx

theorem tyLCMono (T : Ty) (n d : Nat) (h : T.LCAt n) (hd : n ≤ d) : T.LCAt d := by
  induction T using tyInduction with
  | hf X => simp [Ty.LCAt]
  | hb i => simpa only [Ty.LCAt] using Nat.lt_of_lt_of_le (by simpa only [Ty.LCAt] using h) hd
  | hc f ts ih =>
      simp only [Ty.LCAt] at h ⊢
      exact fun U hu => ih U hu (h U hu)

theorem tyOpenBelow (T : Ty) (us : List Ty) (n d : Nat) (h : T.LCAt n) (hd : n ≤ d) :
    T.openAt d us = T := by
  induction T using tyInduction with
  | hf X => simp [Ty.openAt]
  | hb i =>
      have hi : i < d := Nat.lt_of_lt_of_le (by simpa only [Ty.LCAt] using h) hd
      simp [Ty.openAt, hi]
  | hc f ts ih =>
      simp only [Ty.LCAt] at h
      simp only [Ty.openAt]
      congr 1
      exact (show ts.map (Ty.openAt d us) = ts.map id from
        List.map_congr_left (fun U hu => ih U hu (h U hu))).trans (List.map_id ts)

theorem substImagesClosed (S : Signature) (θ : Subst) (hθ : θ.Valid S) (X : TVar) :
    (θ X).LCAt 0 := by
  by_cases h : θ X = .free X
  · simp [h, Ty.LCAt]
  · exact tyKindLC (θ X) S [] X.1 (hθ.2.2 X (hθ.2.1 X h))

theorem tySubstShift (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0) (T : Ty) (n d : Nat) :
    (T.shift n d).subst θ = (T.subst θ).shift n d := by
  induction T using tyInduction with
  | hf X =>
      simp only [Ty.shift, Ty.subst]
      exact (tyShiftClosed (θ X) d n (tyLCMono (θ X) 0 d (hθ X) (Nat.zero_le d))).symm
  | hb i => simp [Ty.shift, Ty.subst]
  | hc f ts ih =>
      simp only [Ty.shift, Ty.subst, List.map_map]
      congr 1
      exact List.map_congr_left (fun U hu => ih U hu)

theorem tyOpenSubst (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0) (T : Ty) (d : Nat) (us : List Ty) :
    (T.openAt d us).subst θ = (T.subst θ).openAt d (us.map (Ty.subst θ)) := by
  induction T using tyInduction with
  | hf X =>
      simp only [Ty.openAt, Ty.subst]
      exact (tyOpenBelow (θ X) _ 0 d (hθ X) (Nat.zero_le d)).symm
  | hb i =>
      by_cases hi : i < d
      · simp [Ty.openAt, Ty.subst, hi]
      · cases hu : us[i-d]? with
        | none => simp [Ty.openAt, Ty.subst, hi, hu, List.getElem?_map]
        | some U => simp [Ty.openAt, Ty.subst, hi, hu, List.getElem?_map, tySubstShift θ hθ]
  | hc f ts ih =>
      simp only [Ty.openAt, Ty.subst, List.map_map]
      congr 1
      exact List.map_congr_left (fun U hu => ih U hu)

/-- Lift a commuting square to constraint and scheme traversals. -/
theorem constraintMapTypesCommute (f g f' g' : Nat → Ty → Ty)
    (h : ∀ d T, g d (f d T) = f' d (g' d T)) (C : Constraint) (d : Nat) :
    (C.mapTypes f d).mapTypes g d = (C.mapTypes g' d).mapTypes f' d := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, (C.mapTypes f d).mapTypes g d = (C.mapTypes g' d).mapTypes f' d)
    (motive_2 := fun s => ∀ d, (s.mapTypes f d).mapTypes g d = (s.mapTypes g' d).mapTypes f' d)
    (by intro d; rfl) (by intro d; rfl)
    (by
      intro p ts d
      simp only [Constraint.mapTypes, List.map_map]
      congr 1
      exact List.map_congr_left (fun T _ => h d T))
    (by intros; simp_all [Constraint.mapTypes])
    (by intros; simp_all [Constraint.mapTypes])
    (by intros; simp_all [Constraint.mapTypes])
    (by intros; simp_all [Constraint.mapTypes])
    (by intros; simp_all [Scheme.mapTypes]) C d

theorem typeOpeningSubstitution (S : Signature) : HMX.LN.typeOpeningSubstitution S := by
  intro θ ks us C hθ _ _
  exact constraintMapTypesCommute _ _ _ _
    (fun d T => tyOpenSubst θ (substImagesClosed S θ hθ) T d us) C 0

end HMX.LN.Proofs
