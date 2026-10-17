import HMX.LocallyNameless.Proofs.Weakening

namespace HMX.LN.Proofs

def termIdEquiv (p : Nat ≃ Nat) : Id ≃ Id where
  toFun := fun x => match x with | .var z => .var (p z) | .loc z => .loc z | .const z => .const z
  invFun := fun x => match x with | .var z => .var (p.symm z) | .loc z => .loc z | .const z => .const z
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro x; cases x <;> simp

def exprNames (p : Nat ≃ Nat) : Expr → Expr
  | .ident (.free x) => .ident (.free (termIdEquiv p x))
  | .ident (.bound i) => .ident (.bound i)
  | .lam t => .lam (exprNames p t)
  | .app t u => .app (exprNames p t) (exprNames p u)
  | .letE t u => .letE (exprNames p t) (exprNames p u)

def envNames (p : Nat ≃ Nat) (Γ : Env) : Env := Γ.map (fun q => (termIdEquiv p q.1,q.2))

theorem envNamesWF (p : Nat ≃ Nat) (Γ : Env) (h : Γ.WF S) : (envNames p Γ).WF S := by
  intro q hq
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
  exact h r hr

theorem envNamesFv (p : Nat ≃ Nat) (Γ : Env) : (envNames p Γ).fv = Γ.fv := by
  simp [envNames,Env.fv,List.map_map,Function.comp_def]

theorem envNamesFpi (p : Nat ≃ Nat) (Γ : Env) : (envNames p Γ).fpi = Γ.fpi := by
  simp [envNames,Env.fpi,List.map_map,Function.comp_def]

theorem exprNamesLC (p : Nat ≃ Nat) (t : Expr) (d : Nat) (h : t.LCAt d) : (exprNames p t).LCAt d := by
  induction t generalizing d with
  | ident x => cases x <;> exact h
  | lam t ih => exact ih (d+1) h
  | app t u iht ihu => exact ⟨iht d h.1,ihu d h.2⟩
  | letE t u iht ihu => exact ⟨iht d h.1,ihu (d+1) h.2⟩

theorem judgmentNamesWF (p : Nat ≃ Nat) (h : JudgmentWF S C Γ t s) :
    JudgmentWF S C (envNames p Γ) (exprNames p t) s :=
  ⟨h.1,envNamesWF p Γ h.2.1,exprNamesLC p t 0 h.2.2.1,h.2.2.2.1,
    h.2.2.2.2.1,(envNamesFpi p Γ).trans h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

theorem lookupNames (p : Nat ≃ Nat) (Γ : Env) (x : Id) :
    lookup (envNames p Γ) (termIdEquiv p x) = lookup Γ x := by
  induction Γ with
  | nil => rfl
  | cons q Γ ih =>
      change lookup ((termIdEquiv p q.1,q.2)::envNames p Γ) (termIdEquiv p x) = _
      rw [lookupCons,lookupCons,ih]
      simp only [(termIdEquiv p).injective.eq_iff]

theorem exprNamesOpen (p : Nat ≃ Nat) (t : Expr) (z d : Nat) :
    exprNames p (Expr.openAt d (.ident (.free (.var z))) t) =
      Expr.openAt d (.ident (.free (.var (p z)))) (exprNames p t) := by
  induction t generalizing d with
  | ident x =>
      cases x with
      | free x => rfl
      | bound i => by_cases h : i = d <;> simp [Expr.openAt,exprNames,Expr.shift,h,termIdEquiv]
  | lam t ih => simp [Expr.openAt,exprNames,ih]
  | app t u iht ihu => simp [Expr.openAt,exprNames,iht,ihu]
  | letE t u iht ihu => simp [Expr.openAt,exprNames,iht,ihu]

theorem envNamesAppend (p : Nat ≃ Nat) (Γ Δ : Env) : envNames p (Γ ++ Δ) = envNames p Γ ++ envNames p Δ :=
  List.map_append

theorem envNamesBinderEq (p : Nat ≃ Nat) (Γ Δ : Env) (h : Γ.BinderEq Δ) :
    (envNames p Γ).BinderEq (envNames p Δ) := by
  induction h with
  | nil => exact .nil
  | cons hp ht ih => exact .cons ⟨congrArg (termIdEquiv p) hp.1,hp.2⟩ ih

theorem derivationNames (p : Nat ≃ Nat) (h : Derivation S M C Γ t s d) :
    Derivation S M C (envNames p Γ) (exprNames p t) s d := by
  induction h with
  | var hw hl hr => exact .var (judgmentNamesWF p hw) (by rw [lookupNames]; exact hl) hr
  | abs L hw hd ih =>
      apply Derivation.abs (L.image p) (judgmentNamesWF p hw)
      intro z hz
      have hz' : p.symm z ∉ L := fun hh => hz (Finset.mem_image.mpr ⟨p.symm z,hh,p.apply_symm_apply z⟩)
      have hp := ih (p.symm z) hz'
      simpa only [exprNamesOpen,p.apply_symm_apply,envNamesAppend,envNames,List.map_append,List.map_cons,List.map_nil,termIdEquiv,Equiv.coe_fn_mk] using hp
  | app hw ht hu iht ihu => exact .app (judgmentNamesWF p hw) iht ihu
  | letE L hw ht hu iht ihu =>
      apply Derivation.letE (L.image p) (judgmentNamesWF p hw) iht
      intro z hz
      have hz' : p.symm z ∉ L := fun hh => hz (Finset.mem_image.mpr ⟨p.symm z,hh,p.apply_symm_apply z⟩)
      have hp := ihu (p.symm z) hz'
      simpa only [exprNamesOpen,p.apply_symm_apply,envNamesAppend,envNames,List.map_append,List.map_cons,List.map_nil,termIdEquiv,Equiv.coe_fn_mk] using hp
  | gen hw hn hf hd ih => exact .gen (judgmentNamesWF p hw) hn (by simpa only [envNamesFv] using hf) ih
  | inst hw hn hd ih => exact .inst (judgmentNamesWF p hw) hn ih
  | sub hw hd hr ih => exact .sub (judgmentNamesWF p hw) ih hr
  | exists_ hw hn hk hf hd ih => exact .exists_ (judgmentNamesWF p hw) hn hk (by simpa only [envNamesFv] using hf) ih
  | convert hw hd hc hΓ hs ih => exact .convert (judgmentNamesWF p hw) ih hc (envNamesBinderEq p _ _ hΓ) hs

theorem exprNamesFixed (p : Nat ≃ Nat) (t : Expr) (h : ∀ x ∈ t.fpi, termIdEquiv p x = x) : exprNames p t = t := by
  induction t with
  | ident x =>
      cases x with
      | free x => exact congrArg (fun y => Expr.ident (.free y)) (h x (by simp [Expr.fpi]))
      | bound i => rfl
  | lam t ih => exact congrArg Expr.lam (ih h)
  | app t u iht ihu =>
      exact congrArg₂ Expr.app (iht (fun x hx => h x (Finset.mem_union_left _ hx)))
        (ihu (fun x hx => h x (Finset.mem_union_right _ hx)))
  | letE t u iht ihu =>
      exact congrArg₂ Expr.letE (iht (fun x hx => h x (Finset.mem_union_left _ hx)))
        (ihu (fun x hx => h x (Finset.mem_union_right _ hx)))

theorem envNamesFixed (p : Nat ≃ Nat) (Γ : Env) (h : ∀ x ∈ Γ.dpi, termIdEquiv p x = x) : envNames p Γ = Γ := by
  apply (List.map_congr_left (g := id) ?_).trans (List.map_id Γ)
  intro q hq
  exact Prod.ext (h q.1 (List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,hq,rfl⟩))) rfl

def idNumber : Id → Nat | .var z | .loc z | .const z => z

theorem swapNamesFixed (F : Finset Id) (z w : Nat)
    (hz : z ∉ F.image idNumber) (hw : w ∉ F.image idNumber) :
    ∀ x ∈ F, termIdEquiv (Equiv.swap z w) x = x := by
  intro x hx
  cases x with
  | var v =>
      have hv : v ∈ F.image idNumber := Finset.mem_image.mpr ⟨.var v,hx,rfl⟩
      change Id.var (Equiv.swap z w v) = Id.var v
      have hvz : v ≠ z := fun he => hz (he ▸ hv)
      have hvw : v ≠ w := fun he => hw (he ▸ hv)
      rw [Equiv.swap_apply_of_ne_of_ne hvz hvw]
  | loc v => rfl
  | const v => rfl

/-- Reopen one fresh derivation at every other fresh name without changing its
shape. This supplies the uniform shape required by Figure 10-7's cofinite rules. -/
theorem uniformOpening (C : Constraint) (Γ : Env) (t : Expr) (s r : Scheme) (L : Finset Nat)
    (h : ∀ z ∉ L, Typing S M C (Γ ++ [(.var z,s)]) (Expr.openAt 0 (.ident (.free (.var z))) t) r) :
    ∃ (d : Shape) (L' : Finset Nat), ∀ z ∉ L', Derivation S M C (Γ ++ [(.var z,s)]) (Expr.openAt 0 (.ident (.free (.var z))) t) r d := by
  let F := Γ.dpi ∪ t.fpi
  obtain ⟨z,hz⟩ := Finset.exists_notMem (L ∪ F.image idNumber)
  have hzL : z ∉ L := fun hh => hz (Finset.mem_union_left _ hh)
  have hzF : z ∉ F.image idNumber := fun hh => hz (Finset.mem_union_right _ hh)
  obtain ⟨d,hd⟩ := h z hzL
  refine ⟨d,F.image idNumber,?_⟩
  intro w hw
  have hfix := swapNamesFixed F z w hzF hw
  have hΓ : envNames (Equiv.swap z w) Γ = Γ := envNamesFixed _ Γ
    (fun x hx => hfix x (Finset.mem_union_left _ hx))
  have ht : exprNames (Equiv.swap z w) t = t := exprNamesFixed _ t
    (fun x hx => hfix x (Finset.mem_union_right _ hx))
  have hp := derivationNames (Equiv.swap z w) hd
  rw [envNamesAppend,hΓ,exprNamesOpen,ht] at hp
  simpa only [Equiv.swap_apply_left,envNames,List.map_cons,List.map_nil,termIdEquiv,Equiv.coe_fn_mk] using hp

end HMX.LN.Proofs
