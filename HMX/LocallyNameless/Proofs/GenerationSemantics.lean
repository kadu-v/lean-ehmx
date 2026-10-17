import HMX.LocallyNameless.Proofs.Generation
import HMX.LocallyNameless.Proofs.TypingEquivalence

namespace HMX.LN.Proofs

theorem tyEvalAtClosed (M : Model) (ρ : Assignment M) (β : Nat → M.Carrier)
    (T : Ty) (h : T.LCAt 0) : T.evalAt M ρ β = T.eval M ρ :=
  tyEvalStacks M ρ β _ T 0 h (by simp)

theorem existsNamesHoldsAt (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) (xs : List TVar) (C : Constraint) :
    (C.existsNames xs).holdsAt S M ρ ι β γ ↔ ∃ vs,
      List.Forall₂ (fun v X => M.kind v = X.1) vs xs ∧
      C.holdsAt S M (assignBlock xs vs ρ) ι β γ := by
  simp only [Constraint.existsNames,Constraint.holdsAt]
  apply exists_congr
  intro vs
  rw [List.forall₂_map_right_iff]
  apply and_congr_right
  intro hv
  have he := constraintEvalClose S M ρ ι xs vs hv.length_eq C [] β γ
  simpa only [List.length_nil,pushNil,Constraint.closeTypes] using he

theorem leHoldsAt (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) (k : Nat) (T U : Ty)
    (hT : T.LCAt 0) (hU : U.LCAt 0) :
    (Constraint.le k T U).holdsAt S M ρ ι β γ ↔
      M.kind (T.eval M ρ) = k ∧ M.kind (U.eval M ρ) = k ∧ M.below k (T.eval M ρ) (U.eval M ρ) := by
  simp only [Constraint.le,Constraint.holdsAt,List.map_cons,List.map_nil,Predicate.eval,
    tyEvalAtClosed M ρ β T hT,tyEvalAtClosed M ρ β U hU]

theorem schemeAtValid (hM : M.Requirements S) (ρ : Assignment M) (ι : GroundEnv M)
    (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier) (s : Scheme) (d : Nat)
    (hρ : ρ.Valid S M) (hs : s.WF S [] d) :
    (∀ a ∈ s.denoteAt S M ρ ι β γ, M.kind a = 0) ∧
    (∀ a b, a ∈ s.denoteAt S M ρ ι β γ → M.kind b = 0 → M.below 0 a b → b ∈ s.denoteAt S M ρ ι β γ) := by
  cases s with
  | all ks C T =>
      constructor
      · exact fun _ h => h.1
      · intro a b ha hb hab
        obtain ⟨ha,vs,hvs,hC,hTa⟩ := ha
        refine ⟨hb,vs,hvs,hC,?_⟩
        exact hM.2.2.2.2.1 0 hM.1.1 _ _ _
          (evaluationKind S M hM ρ _ ks T 0 hρ (pushKinds M vs ks hvs β) (by simpa using hs.2.2)) ha hb hTa hab

theorem pushGroundValid {M : Model} (A : Set M.Carrier) (γ : Nat → Set M.Carrier)
    (hA : (∀ a ∈ A, M.kind a = 0) ∧ (∀ a b, a ∈ A → M.kind b = 0 → M.below 0 a b → b ∈ A))
    (hγ : ∀ i, (∀ a ∈ γ i, M.kind a = 0) ∧
      (∀ a b, a ∈ γ i → M.kind b = 0 → M.below 0 a b → b ∈ γ i)) :
    ∀ i, (∀ a ∈ push [A] γ i, M.kind a = 0) ∧
      (∀ a b, a ∈ push [A] γ i → M.kind b = 0 → M.below 0 a b → b ∈ push [A] γ i) := by
  intro i
  cases i with
  | zero => simpa [push] using hA
  | succ i => simpa [push] using hγ i

theorem generateExpectedRename (t : Expr) (T : Ty) (X : TVar) (hT : T.LCAt 0)
    (ρ : Assignment M) (ι : GroundEnv M) (β : Nat → M.Carrier) (γ : Nat → Set M.Carrier)
    (he : T.eval M ρ = ρ X) :
    (generate t T).holdsAt S M ρ ι β γ ↔ (generate t (.free X)).holdsAt S M ρ ι β γ := by
  let θ : Subst := fun Y => if Y = X then T else .free Y
  have hθ : ∀ Y, (θ Y).LCAt 0 := by intro Y; by_cases h : Y = X <;> simp [θ,h,Ty.LCAt,hT]
  have hg := generateSubstEq t (.free X) θ hθ (by simp [Ty.LCAt])
  have hσ : (fun Y => (θ Y).eval M ρ) = ρ := by
    funext Y
    by_cases h : Y = X
    · subst Y; simpa [θ] using he
    · simp [θ,h,Ty.eval,Ty.evalAt]
  have hh := constraintEvalSubst S M θ hθ ρ ι (generate t (.free X)) 0 β γ
  change ((generate t (.free X)).subst θ).holdsAt S M ρ ι β γ ↔ _ at hh
  rw [hg,hσ] at hh
  simpa only [Ty.subst,θ,ite_true] using hh

theorem exprOpenNameLC (t : Expr) (z d : Nat) (h : t.LCAt (d+1)) :
    (Expr.openAt d (.ident (.free (.var z))) t).LCAt d := by
  induction t generalizing d with
  | ident v =>
      cases v with
      | free x => trivial
      | bound i =>
          simp only [Expr.LCAt] at h
          by_cases he : i = d
          · simp [Expr.openAt,he,Expr.shift,Expr.LCAt]
          · have hi : i < d := by omega
            simp [Expr.openAt,he,hi,Expr.LCAt]
  | lam t ih => exact ih (d+1) h
  | app t u iht ihu => exact ⟨iht d h.1,ihu d h.2⟩
  | letE t u iht ihu => exact ⟨iht d h.1,ihu (d+1) h.2⟩

theorem pvarCloseOpen (v : PVar) (x : Id) (d : Nat) (h : v ≠ .free x) :
    (v.openAt d x).closeAt d x = v := by
  cases v with
  | free y =>
      have hy : y ≠ x := fun he => h (congrArg PVar.free he)
      simp [PVar.openAt,PVar.closeAt,hy]
  | bound i =>
      by_cases he : i = d
      · subst i; simp [PVar.openAt,PVar.closeAt]
      · by_cases hi : i < d
        · simp [PVar.openAt,PVar.closeAt,he,hi]
        · have hi' : ¬ i-1 < d := by omega
          have hi'' : i-1+1 = i := by omega
          simp [PVar.openAt,PVar.closeAt,he,hi,hi',hi'']

theorem constraintCloseOpenId (C : Constraint) (x : Id) (d : Nat) (hf : x ∉ C.fpi) :
    (C.mapIds (fun n v => v.openAt n x) d).mapIds (fun n v => v.closeAt n x) d = C := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ d, x ∉ C.fpi →
      (C.mapIds (fun n v => v.openAt n x) d).mapIds (fun n v => v.closeAt n x) d = C)
    (motive_2 := fun s => ∀ d, x ∉ s.fpi →
      (s.mapIds (fun n v => v.openAt n x) d).mapIds (fun n v => v.closeAt n x) d = s)
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
    (by
      intro C D ihC ihD n hh
      exact congrArg₂ Constraint.conj (ihC n (fun hx => hh (Finset.mem_union_left _ hx)))
        (ihD n (fun hx => hh (Finset.mem_union_right _ hx))))
    (by intro ks C ih n hh; exact congrArg (Constraint.exists_ ks) (ih n hh))
    (by
      intro b s C ihs ihC n hh
      exact congrArg₂ (Constraint.def_ b) (ihs n (fun hx => hh (Finset.mem_union_left _ hx)))
        (ihC (n+1) (fun hx => hh (Finset.mem_union_right _ hx))))
    (by
      intro v T n hh
      apply congrArg (fun w => Constraint.inst w T)
      apply pvarCloseOpen
      intro he
      subst v
      exact hh (by simp [Constraint.fpi]))
    (by intro ks C T ih n hh; exact congrArg (fun D => Scheme.all ks D T) (ih n hh)) C d hf

theorem generateLetName (t : Expr) (z : Nat) (T A : Ty) (hz : Id.var z ∉ t.fpi) :
    (generate t T).letBound .term (.mono A) =
      (generate (Expr.openAt 0 (.ident (.free (.var z))) t) T).letName (.var z) (.mono A) := by
  have hf : Id.var z ∉ (generate t T).fpi := by rw [(generationFreeVariables t T).2]; exact hz
  have he := constraintCloseOpenId (generate t T) (.var z) 0 hf
  change ((generate t T).openId (.var z)).closeId (.var z) = generate t T at he
  have ho : (generate t T).openId (.var z) = generate (Expr.openAt 0 (.ident (.free (.var z))) t) T :=
    generateOpenAt t T (.var z) 0
  rw [ho] at he
  simp only [Constraint.letBound,Constraint.letName,Constraint.define,Binder.ofId,he]

theorem letNameWF (S : Signature) (x : Id) (s : Scheme) (C : Constraint)
    (hs : s.WF S [] 0) (hc : C.WF S [] 0) : (C.letName x s).WF S [] 0 :=
  ⟨schemeExistsWF S s hs,hs,constraintCloseIdWF S x C [] 0 0 le_rfl hc⟩

theorem letNameFv (x : Id) (s : Scheme) (C : Constraint) : (C.letName x s).fv = s.fv ∪ C.fv := by
  simp only [Constraint.letName,Constraint.define,Constraint.fv,Constraint.closeId,constraintMapIdsFv]
  rw [← Finset.union_assoc,Finset.union_eq_right.mpr (schemeExistsFv s)]

theorem arrowEval (M : Model) (ρ : Assignment M) (T U : Ty) :
    (Ty.arrow T U).eval M ρ = M.constructor 0 [T.eval M ρ,U.eval M ρ] := by
  simp [Ty.arrow,Ty.eval,Ty.evalAt]

end HMX.LN.Proofs
