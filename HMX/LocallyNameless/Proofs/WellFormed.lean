import HMX.LocallyNameless.Proofs.Binding
import Mathlib.Data.List.Forall2

namespace HMX.LN.Proofs

theorem forall₂ImplMem {α β : Type} {R Q : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (hf : ∀ x ∈ xs, ∀ y, R x y → Q x y) : List.Forall₂ Q xs ys := by
  induction h with
  | nil => exact .nil
  | cons hr hs ih => exact .cons (hf _ (by simp) _ hr) (ih (fun x hx => hf x (by simp [hx])))

theorem forall₂Left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (x : α) (hx : x ∈ xs) : ∃ y, R x y := by
  induction h with
  | nil => simp at hx
  | cons hr hs ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, hr⟩
      · exact ih hx

theorem tyKindLC (T : Ty) (S : Signature) (ks : List Nat) (k : Nat)
    (h : T.HasKind S ks k) : T.LCAt ks.length := by
  induction T using tyInduction generalizing k with
  | hf X => simp [Ty.LCAt]
  | hb i =>
      cases h with
      | bound hi _ => simpa [Ty.LCAt] using (List.getElem?_eq_some_iff.mp hi).1
  | hc f ts ih =>
      cases h with
      | con _ hs =>
          simp only [Ty.LCAt]
          intro U hu
          obtain ⟨p, hp⟩ := forall₂Left hs U hu
          exact ih U hu _ hp

theorem tyShiftClosed (T : Ty) (d n : Nat) (h : T.LCAt d) : T.shift n d = T := by
  induction T using tyInduction with
  | hf X => simp [Ty.shift]
  | hb i =>
      simp only [Ty.LCAt] at h
      simp [Ty.shift, h]
  | hc f ts ih =>
      simp only [Ty.LCAt] at h
      simp only [Ty.shift]
      congr 1
      exact (show ts.map (Ty.shift n d) = ts.map id from
        List.map_congr_left (fun U hu => ih U hu (h U hu))).trans (List.map_id ts)

theorem tyKindClosed (T : Ty) (S : Signature) (ks : List Nat) (k : Nat)
    (h : T.HasKind S [] k) : T.HasKind S ks k := by
  induction T using tyInduction generalizing k with
  | hf X => cases h; exact .free (by assumption)
  | hb i => cases h with | bound hi _ => simp at hi
  | hc f ts ih =>
      cases h with
      | con hf hs =>
          apply Ty.HasKind.con hf
          exact forall₂ImplMem hs (fun U hU p hp => ih U hU _ hp)

/-- Relate a successful index lookup to its matching entry in a Forall₂ list. -/
theorem forall₂Lookup {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) (i : Nat) (y : β) (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ R x y := by
  induction h generalizing i with
  | nil => simp at hy
  | @cons x y' xs ys hr hs ih =>
      cases i with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hy; subst y; exact ⟨x, rfl, hr⟩
      | succ i => exact ih i hy

theorem tyOpenKind (S : Signature) (T : Ty) (ks bs : List Nat) (us : List Ty)
    (hu : List.Forall₂ (Ty.HasKind S []) us ks) (k : Nat)
    (h : T.HasKind S (bs ++ ks) k) :
    (T.openAt bs.length us).HasKind S bs k := by
  induction T using tyInduction generalizing k with
  | hf X => simp only [Ty.openAt]; cases h; exact .free (by assumption)
  | hb i =>
      cases h with
      | bound hi hk =>
          by_cases hib : i < bs.length
          · simp only [Ty.openAt, hib, ↓reduceIte]
            exact .bound (by simpa [List.getElem?_append, hib] using hi) hk
          · have hi' : ks[i-bs.length]? = some k := by
              simpa [List.getElem?_append, hib] using hi
            obtain ⟨U, hU, hkU⟩ := forall₂Lookup hu (i-bs.length) k hi'
            simp only [Ty.openAt, hib, ↓reduceIte, hU]
            rw [tyShiftClosed U 0 bs.length (tyKindLC U S [] k hkU)]
            exact tyKindClosed U S bs k hkU
  | hc f ts ih =>
      cases h with
      | con hf hs =>
          simp only [Ty.openAt]
          apply Ty.HasKind.con hf
          apply List.forall₂_map_left_iff.mpr
          exact forall₂ImplMem hs (fun U hU p hp => ih U hU _ hp)

/-- Lift a kind-preserving traversal under arbitrary type and term binders. -/
theorem constraintMapTypesWF (S : Signature) (f : Nat → Ty → Ty) (ks : List Nat)
    (h : ∀ bs T k, T.HasKind S (bs ++ ks) k → (f bs.length T).HasKind S bs k)
    (C : Constraint) (bs : List Nat) (d : Nat) (hc : C.WF S (bs ++ ks) d) :
    (C.mapTypes f bs.length).WF S bs d := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ bs d, C.WF S (bs ++ ks) d → (C.mapTypes f bs.length).WF S bs d)
    (motive_2 := fun s => ∀ bs d, s.WF S (bs ++ ks) d → (s.mapTypes f bs.length).WF S bs d)
    (by intros; trivial) (by intros; trivial)
    (by
      intro p ts bs d hp
      refine ⟨hp.1, List.forall₂_map_left_iff.mpr (List.Forall₂.imp (fun T k hk => h bs T k hk) hp.2)⟩)
    (by intro C D ihC ihD bs d hc; exact ⟨ihC bs d hc.1, ihD bs d hc.2⟩)
    (by
      intro ns C ih bs d hc
      refine ⟨hc.1, ?_⟩
      simpa [List.length_append, Nat.add_comm] using ih (ns ++ bs) d (by simpa [List.append_assoc] using hc.2))
    (by intro b s C ihs ihC bs d hc; exact ⟨ihs bs d hc.1, ihC bs (d+1) hc.2⟩)
    (by intro x T bs d hc; exact ⟨h bs T 0 hc.1, hc.2⟩)
    (by
      intro ns C T ih bs d hs
      refine ⟨hs.1, ?_, ?_⟩
      · simpa [List.length_append, Nat.add_comm] using ih (ns ++ bs) d (by simpa [List.append_assoc] using hs.2.1)
      · simpa [List.length_append, Nat.add_comm] using h (ns ++ bs) T 0 (by simpa [List.append_assoc] using hs.2.2)) C bs d hc

theorem typeOpeningWF (S : Signature) : HMX.LN.typeOpeningWF S := by
  intro ks us C hC hu
  exact constraintMapTypesWF S (fun d T => T.openAt d us) ks
    (fun bs T k h => tyOpenKind S T ks bs us hu k h) C [] 0 hC

theorem tySubstKind (S : Signature) (θ : Subst) (hθ : θ.Valid S)
    (T : Ty) (ks : List Nat) (k : Nat) (h : T.HasKind S ks k) : (T.subst θ).HasKind S ks k := by
  induction T using tyInduction generalizing k with
  | hf X =>
      simp only [Ty.subst]
      cases h with | free hx => exact tyKindClosed (θ X) S ks X.1 (hθ.2.2 X hx)
  | hb i => simpa only [Ty.subst] using h
  | hc f ts ih =>
      cases h with
      | con hf hs =>
          simp only [Ty.subst]
          exact .con hf (List.forall₂_map_left_iff.mpr (forall₂ImplMem hs (fun U hU p hp => ih U hU _ hp)))

theorem constraintMapTypesPreservesWF (S : Signature) (f : Nat → Ty → Ty)
    (h : ∀ ks d T k, T.HasKind S ks k → (f d T).HasKind S ks k)
    (C : Constraint) (ks : List Nat) (d n : Nat) (hc : C.WF S ks d) :
    (C.mapTypes f n).WF S ks d := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ ks d n, C.WF S ks d → (C.mapTypes f n).WF S ks d)
    (motive_2 := fun s => ∀ ks d n, s.WF S ks d → (s.mapTypes f n).WF S ks d)
    (by intros; trivial) (by intros; trivial)
    (by intro p ts ks d n hp; exact ⟨hp.1, List.forall₂_map_left_iff.mpr (List.Forall₂.imp (fun T k hk => h ks n T k hk) hp.2)⟩)
    (by intro C D ihC ihD ks d n hc; exact ⟨ihC ks d n hc.1, ihD ks d n hc.2⟩)
    (by intro bs C ih ks d n hc; exact ⟨hc.1, ih (bs ++ ks) d (n + bs.length) hc.2⟩)
    (by intro b s C ihs ihC ks d n hc; exact ⟨ihs ks d n hc.1, ihC ks (d+1) n hc.2⟩)
    (by intro x T ks d n hc; exact ⟨h ks n T 0 hc.1, hc.2⟩)
    (by intro bs C T ih ks d n hs; exact ⟨hs.1, ih (bs ++ ks) d (n + bs.length) hs.2.1, h (bs ++ ks) (n + bs.length) T 0 hs.2.2⟩) C ks d n hc

theorem freeSubstitutionWF (S : Signature) : HMX.LN.freeSubstitutionWF S := by
  intro θ hθ
  refine ⟨fun ks T k h => tySubstKind S θ hθ T ks k h, ?_, ?_⟩
  · intro ks d C hC
    exact constraintMapTypesPreservesWF S (fun _ T => T.subst θ)
      (fun ks _ T k h => tySubstKind S θ hθ T ks k h) C ks d 0 hC
  · intro ks d s hs
    cases s with
    | all bs C T =>
        exact ⟨hs.1, constraintMapTypesPreservesWF S (fun _ T => T.subst θ)
          (fun ks _ T k h => tySubstKind S θ hθ T ks k h) C (bs ++ ks) d (0 + bs.length) hs.2.1,
          tySubstKind S θ hθ T (bs ++ ks) 0 hs.2.2⟩

end HMX.LN.Proofs
