import EHMX.Semantics

namespace EHMX

@[elab_as_elim] theorem tyInduction {P : Ty → Prop}
    (hf : ∀ X, P (.free X)) (hb : ∀ i, P (.bound i))
    (hc : ∀ f ts, (∀ T ∈ ts, P T) → P (.con f ts)) (T : Ty) : P T := by
  exact Ty.rec (motive_1 := P) (motive_2 := fun ts => ∀ T ∈ ts, P T)
    hf hb hc (by simp)
    (by intro h ts hh ht T hm; rcases List.mem_cons.mp hm with rfl | hm
        exact hh
        exact ht T hm) T

@[simp] theorem tyShiftZero (T : Ty) (d : Nat) : T.shift 0 d = T := by
  induction T using tyInduction with
  | hf X => simp [Ty.shift]
  | hb i => simp [Ty.shift]
  | hc f ts ih =>
      simp only [Ty.shift]
      congr 1
      exact (show ts.map (Ty.shift 0 d) = ts.map id from
        List.map_congr_left (fun U hu => ih U hu)).trans (List.map_id ts)

theorem forall₂ImplMem {R Q : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (hf : ∀ x ∈ xs, ∀ y, R x y → Q x y) :
    List.Forall₂ Q xs ys := by
  induction h with
  | nil => exact .nil
  | cons hr hs ih => exact .cons (hf _ (by simp) _ hr) (ih (fun x hx => hf x (by simp [hx])))

theorem forall₂Lookup {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {i : Nat} {y : β} (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hy
  | cons hr hs ih =>
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
                subst y; exact ⟨_, rfl, hr⟩
      | succ i => exact ih hy

theorem emptyKind (_hS : S.WF) : Ty.HasKind S Δ .empty 1 :=
  .con trivial .nil

theorem singletonKind (op : Op) : Ty.HasKind S Δ (.singleton op) 1 :=
  .con trivial .nil

theorem unionKind (hε : Ty.HasKind S Δ ε 1) (hη : Ty.HasKind S Δ η 1) :
    Ty.HasKind S Δ (.union ε η) 1 :=
  .con trivial (.cons hε (.cons hη .nil))

theorem arrowKind (hA : Ty.HasKind S Δ A 0) (hε : Ty.HasKind S Δ ε 1)
    (hB : Ty.HasKind S Δ B 0) : Ty.HasKind S Δ (.arrow A ε B) 0 :=
  .con trivial (.cons hA (.cons hε (.cons hB .nil)))

/-- The kind substitution obligation for adding a block at the front. -/
theorem kindShift (h : Ty.HasKind S Δ T k) (ks : List Kind) :
    Ty.HasKind S (ks ++ Δ) (T.shift ks.length 0) k := by
  induction T using tyInduction generalizing k with
  | hf X =>
      simp only [Ty.shift]
      cases h; exact .free (by assumption)
  | hb i =>
      cases h with
      | bound hi hk =>
          simp only [Ty.shift, Nat.not_lt_zero, ↓reduceIte]
          apply Ty.HasKind.bound _ hk
          simpa [List.getElem?_append, Nat.not_lt, Nat.add_sub_cancel_right,
            Nat.add_comm] using hi
  | hc f ts ih =>
      cases h with
      | con hf hs =>
          simp only [Ty.shift]
          apply Ty.HasKind.con hf
          apply List.forall₂_map_left_iff.mpr
          exact forall₂ImplMem hs (fun T hT k hk => ih T hT hk)

/-- Replace all local declaration variables with arguments in the surrounding Δ. -/
theorem operationInstantiation (h : Ty.HasKind S ks T k)
    (hargs : List.Forall₂ (Ty.HasKind S Δ) args ks) :
    Ty.HasKind S Δ (T.openAt 0 args) k := by
  induction T using tyInduction generalizing k with
  | hf X =>
      simp only [Ty.openAt]
      cases h; exact .free (by assumption)
  | hb i =>
      cases h with
      | bound hi hk =>
          obtain ⟨U, hU, hkind⟩ := forall₂Lookup hargs hi
          simpa only [Ty.openAt, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, hU, tyShiftZero] using hkind
  | hc f ts ih =>
      cases h with
      | con hf hs =>
          simp only [Ty.openAt]
          apply Ty.HasKind.con hf
          apply List.forall₂_map_left_iff.mpr
          exact forall₂ImplMem hs (fun T hT k hk => ih T hT hk)

theorem evalKind (hF : EffectFramework S M) (hρ : Assignment.Valid S M ρ)
    (hbs : KindValues M Δ bs) (hT : Ty.HasKind S Δ T k) :
    M.kind (T.eval M ρ bs) = k := by
  induction T using tyInduction generalizing k with
  | hf X => cases hT with | free hk => simpa only [Ty.eval] using hρ X hk
  | hb i =>
      cases hT with
      | bound hi _ =>
          obtain ⟨v, hv, hk⟩ := forall₂Lookup hbs hi
          simpa [Ty.eval, hv] using hk
  | hc f ts ih =>
      cases hT with
      | con hf hs =>
          simp only [Ty.eval]
          apply hF.constructorKind f hf
          apply List.forall₂_map_left_iff.mpr
          exact forall₂ImplMem hs (fun T hT k hk => ih T hT hk)

/-- Add outer type binders without changing the indices of a closed declaration. -/
theorem kindAppend (h : Ty.HasKind S Δ T k) (ks : List Kind) :
    Ty.HasKind S (Δ ++ ks) T k := by
  induction T using tyInduction generalizing k with
  | hf X => cases h; exact .free (by assumption)
  | hb i =>
      cases h with
      | bound hi hk =>
          have hlt := (List.getElem?_eq_some_iff.mp hi).1
          exact .bound (by simpa [List.getElem?_append, hlt] using hi) hk
  | hc f ts ih =>
      cases h with
      | con hf hs => exact .con hf (forall₂ImplMem hs (fun T hT k hk => ih T hT hk))

theorem evalShift (T : Ty) (ρ : Assignment M) (bs vs : List M.Carrier) :
    (T.shift vs.length 0).eval M ρ (vs ++ bs) = T.eval M ρ bs := by
  induction T using tyInduction with
  | hf X => simp [Ty.shift, Ty.eval]
  | hb i =>
      have hn : ¬ i + vs.length < vs.length := by omega
      simp [Ty.shift, Ty.eval, List.getElem?_append, hn]
  | hc f ts ih =>
      simp only [Ty.shift, Ty.eval, List.map_map]
      congr 1
      exact List.map_congr_left (fun T hT => ih T hT)

end EHMX
