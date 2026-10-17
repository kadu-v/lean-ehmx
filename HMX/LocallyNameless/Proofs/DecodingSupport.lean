import HMX.LocallyNameless.Proofs.SchemeRepresentationConversion

namespace HMX.LN.Proofs

def EnvRepresentation (S : Signature) (M : Model) (Γ : Env) (Δ : HMX.Env) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ SchemeRepresentation S M p.2 q.2) Γ Δ

theorem constraintRepresentationConj (h : ConstraintRepresentation S M C C')
    (g : ConstraintRepresentation S M D D') : ConstraintRepresentation S M (.conj C D) (.conj C' D') :=
  ⟨⟨h.1,g.1⟩,congrArg₂ (· ∪ ·) h.2.1 g.2.1,congrArg₂ (· ∪ ·) h.2.2.1 g.2.2.1,
    fun ρ ι hρ => and_congr (h.2.2.2 ρ ι hρ) (g.2.2.2 ρ ι hρ)⟩

theorem constraintRepresentationExists (h : ConstraintRepresentation S M C C')
    (hw : C.WF S [] 0) (xs : List TVar) (hk : ∀ X ∈ xs, X.1 ∈ S.kinds) :
    ConstraintRepresentation S M (C.existsNames xs) (.exists_ xs.toFinset C') := by
  refine ⟨⟨fun X hx => hk X (List.mem_toFinset.mp hx),h.1⟩,?_,?_,?_⟩
  · exact (congrArg (fun F => F \ xs.toFinset) h.2.1).trans (existsNamesFv xs C).symm
  · exact h.2.2.1.trans (existsNamesFpi xs C).symm
  · intro ρ ι hρ
    apply (namedExistsList xs hk C' ρ ι hρ).trans
    apply Iff.trans ?_ (existsNamesHolds S M ρ ι xs C hw).symm
    exact exists_congr (fun vs => and_congr_right (fun hv => h.2.2.2 _ ι (assignBlockValid S M ρ xs vs hρ hv)))

theorem schemeRepresentationExistsHolds (h : SchemeRepresentation S M s r)
    (ρ : Assignment M) (ι : GroundEnv M) (hρ : ρ.Valid S M) :
    r.exists_.Holds S M ρ ι ↔ s.exists_.Holds S M ρ ι := by
  obtain ⟨xs,D,T,E,U,hn,hk,hD,hT,hE,hU,rfl,rfl⟩ := h
  exact (constraintRepresentationExists hE hD xs hk).2.2.2 ρ ι hρ

theorem schemeRepresentationMono (T : Ty) (hT : T.HasKind S [] 0) :
    SchemeRepresentation S M (.mono T) (.mono (namedTy T)) := by
  have hw : (HMX.Scheme.mono (namedTy T)).WF S := ⟨by simp,trivial,namedTyKind hT⟩
  have h := encodingSchemeRepresentation (HMX.Scheme.mono (namedTy T)) hw (M := M)
  rw [encodingMono,namedTyEncoding T (tyKindLC T S [] 0 hT)] at h
  exact h

theorem envRepresentationProperties (h : EnvRepresentation S M Γ Δ) :
    Δ.WF S ∧ Δ.fv = Γ.fv ∧ Δ.fpi = Γ.fpi := by
  induction h with
  | nil => exact ⟨by simp [HMX.Env.WF],rfl,rfl⟩
  | @cons p q Γ Δ hp ht ih =>
    have hs := schemeRepresentationProperties hp.2
    refine ⟨?_,congrArg₂ (· ∪ ·) hs.2.2.1 ih.2.1,congrArg₂ (· ∪ ·) hs.2.2.2 ih.2.2⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hs.2.1
    · exact ih.1 r hr

theorem envRepresentationLookup (h : EnvRepresentation S M Γ Δ) (hl : lookup Γ x = some s) :
    ∃ r, lookup Δ x = some r ∧ SchemeRepresentation S M s r := by
  have hrel : Option.Rel (SchemeRepresentation S M) (lookup Γ x) (lookup Δ x) := by
    clear hl
    induction h with
    | nil => exact .none
    | @cons p q Γ Δ hp ht ih =>
      rw [lookupCons,lookupCons]
      generalize lookup Γ x = a at ih ⊢
      generalize lookup Δ x = b at ih ⊢
      cases ih with
      | some h => exact .some h
      | none =>
        rw [← hp.1]
        by_cases hx : x = p.1
        · simp only [hx,↓reduceIte]; exact .some hp.2
        · simp only [hx,↓reduceIte]; exact .none
  rw [hl] at hrel
  generalize lookup Δ x = b at hrel ⊢
  cases hrel with
  | some h => exact ⟨_,rfl,h⟩

theorem envRepresentationAppend (h : EnvRepresentation S M Γ Δ)
    (hs : SchemeRepresentation S M s r) (x : Id) :
    EnvRepresentation S M (Γ ++ [(x,s)]) (Δ ++ [(x,r)]) :=
  List.rel_append h (.cons ⟨rfl,hs⟩ .nil)

theorem encodingEnvRepresentation (Γ : HMX.Env) (hw : Γ.WF S) :
    EnvRepresentation S M (ofEnv Γ) Γ := by
  induction Γ with
  | nil => exact .nil
  | cons p Γ ih =>
    exact .cons ⟨rfl,encodingSchemeRepresentation p.2 (hw p (by simp))⟩
      (ih (fun q hq => hw q (List.mem_cons_of_mem p hq)))

theorem envRepresentationBinderEq (hM : M.Requirements S) (h : Env.BinderEq Γ Δ)
    (hr : EnvRepresentation S M Δ Ξ) (hf : Γ.fpi = ∅) :
    ∃ Θ, EnvRepresentation S M Γ Θ ∧ HMX.Proofs.EnvConversion S M Θ Ξ := by
  induction h generalizing Ξ with
  | nil => cases hr; exact ⟨[],.nil,.nil⟩
  | @cons p q Γ Δ hp ht ih =>
    cases hr with
    | cons hq hu =>
      have hpf := (Finset.union_eq_empty.mp hf).1
      have hpw := (schemeBinderEqWF hp.2 [] 0).mpr (schemeRepresentationProperties hq.2).1
      obtain ⟨r,hr⟩ := schemeRepresentationExists p.2 hpw (M := M)
      obtain ⟨Θ,hΘ,hc⟩ := ih hu (Finset.union_eq_empty.mp hf).2
      exact ⟨(p.1,r)::Θ,.cons ⟨rfl,hr⟩ hΘ,
        .cons ⟨hp.1.trans hq.1,binderEqSchemeRepresentations hM hp.2 r _ hr hq.2 hpf⟩ hc⟩

theorem decodingJudgment (hw : JudgmentWF S C Γ t s)
    (hc : ConstraintRepresentation S M C D) (hΓ : EnvRepresentation S M Γ Δ)
    (hs : SchemeRepresentation S M s r) : HMX.JudgmentWF S D Δ r := by
  have he := envRepresentationProperties hΓ
  have hr := schemeRepresentationProperties hs
  exact ⟨hc.1,he.1,hr.2.1,hc.2.2.1.trans hw.2.2.2.2.1,
    he.2.2.trans hw.2.2.2.2.2.1,hr.2.2.2.trans hw.2.2.2.2.2.2⟩

theorem decodingFinish (hM : M.Requirements S) (hc : ConstraintRepresentation S M C D)
    (he : ConstraintRepresentation S M C E) (hs : SchemeRepresentation S M s r)
    (ht : SchemeRepresentation S M s u) (hCf : C.fpi = ∅) (hsf : s.fpi = ∅)
    (hd : HMX.Typing S M D Γ t r) : HMX.Typing S M E Γ t u := by
  have hp := HMX.Proofs.typingConstraintEquivalent hd he.1 (he.2.2.1.trans hCf)
    ⟨fun ρ ι hρ _ hh => (he.2.2.2 ρ ι hρ).mpr ((hc.2.2.2 ρ ι hρ).mp hh),
      fun ρ ι hρ _ hh => (hc.2.2.2 ρ ι hρ).mpr ((he.2.2.2 ρ ι hρ).mp hh)⟩
  exact (HMX.Proofs.schemeConversionTyping hM (equalSchemeRepresentations hM hs ht rfl hsf)).mp hp

theorem encodingExprClose (t : HMX.Expr) (pre : List Id) (z : Nat) :
    (ofExpr pre t).closeAt pre.length z = ofExpr (pre ++ [.var z]) t := by
  induction t generalizing pre with
  | ident x =>
    by_cases hx : x ∈ pre
    · have hi := List.idxOf_lt_length_iff.mpr hx
      simp [ofExpr,ofId,hx,Expr.closeAt,List.idxOf_append_of_mem hx,hi]
    · by_cases hz : x = .var z
      · subst x
        simp [ofExpr,ofId,hx,Expr.closeAt,List.idxOf_append_of_notMem hx]
      · simp [ofExpr,ofId,hx,hz,Expr.closeAt]
  | lam y t ih => simpa only [ofExpr,Expr.closeAt,List.cons_append,List.length_cons] using congrArg Expr.lam (ih (.var y :: pre))
  | app t u iht ihu => exact congrArg₂ Expr.app (iht pre) (ihu pre)
  | letE y t u iht ihu => exact congrArg₂ Expr.letE (iht pre) (ihu (.var y :: pre))

theorem decodingLam (t : Expr) (u : HMX.Expr) (z : Nat) (hz : Id.var z ∉ t.fpi)
    (hu : ofExpr [] u = Expr.openAt 0 (.ident (.free (.var z))) t) :
    ofExpr [] (.lam z u) = .lam t := by
  change Expr.lam (ofExpr [.var z] u) = _
  have he := encodingExprClose u [] z
  simp only [List.length_nil,List.nil_append] at he
  rw [← he,hu,exprCloseOpen t 0 z hz]

theorem namedTyArrow (T U : Ty) : namedTy (.arrow T U) = .arrow (namedTy T) (namedTy U) := by
  simp [Ty.arrow,namedTy,HMX.Ty.arrow]

end HMX.LN.Proofs
