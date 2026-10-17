import HMX.LocallyNameless.Proofs.EncodingTyping

namespace HMX.Proofs

open LN.Proofs

theorem bindsReflexive (A : Vars) : Binds Eq Eq A A := by
  refine ⟨?_,?_,?_⟩
  · intro X hx; exact ⟨X,⟨hx,rfl,rfl⟩,fun Y h => h.2.2.symm⟩
  · intro Y hy; exact ⟨Y,⟨hy,rfl,rfl⟩,fun X h => h.2.2⟩
  · intro X Y
    constructor
    · intro h; subst Y
      by_cases hx : X ∈ A
      · exact Or.inl ⟨hx,hx,rfl,rfl⟩
      · exact Or.inr ⟨hx,hx,rfl⟩
    · rintro (⟨_,_,_,h⟩ | ⟨_,_,h⟩) <;> exact h

theorem bindIdReflexive (x : Id) : bindId Eq x x = Eq := by
  funext y z
  apply propext
  constructor
  · rintro (⟨h,h'⟩ | ⟨_,_,h⟩)
    · exact h.trans h'.symm
    · exact h
  · intro h; subst z
    by_cases hx : y = x
    · exact Or.inl ⟨hx,hx⟩
    · exact Or.inr ⟨hx,hx,rfl⟩

theorem tyAlphaReflexive (T : Ty) : Ty.Related Eq T T := by
  cases T with
  | var X => exact .var rfl
  | con f ts =>
    exact .con (List.forall₂_same.mpr (fun U _ => tyAlphaReflexive U))
termination_by sizeOf T

mutual
theorem constraintAlphaReflexive (C : Constraint) : C.Alpha C := by
  cases C with
  | truth => exact .truth
  | falsity => exact .falsity
  | atom p ts => exact .atom (List.forall₂_same.mpr (fun T _ => tyAlphaReflexive T))
  | conj C D => exact .conj (constraintAlphaReflexive C) (constraintAlphaReflexive D)
  | exists_ A C => exact .exists_ (bindsReflexive A) (constraintAlphaReflexive C)
  | def_ x s C =>
    apply Constraint.Related.def_ (Or.inl rfl) (schemeAlphaReflexive s)
    rw [bindIdReflexive]
    exact constraintAlphaReflexive C
  | inst x T => exact .inst rfl (tyAlphaReflexive T)
theorem schemeAlphaReflexive (s : Scheme) : s.Alpha s := by
  cases s with
  | all A C T => exact .all (bindsReflexive A) (constraintAlphaReflexive C) (tyAlphaReflexive T)
end

theorem exprAlphaReflexive (t : Expr) : t.Alpha t := (encodingAlpha.1 t t).mpr rfl

theorem envAlphaReflexive (Γ : Env) : Γ.Alpha Γ :=
  List.forall₂_same.mpr (fun p _ => ⟨rfl,schemeAlphaReflexive p.2⟩)

theorem derivationRealizable (hM : M.Requirements S) (hd : Derivation S M C Γ t s d) :
    Entails S M C s.exists_ := by
  have hw := derivationWF hd
  have hs : s.exists_.WF S := by cases s; exact ⟨hw.2.2.1.1,hw.2.2.1.2.1⟩
  apply (encodingEntails hM hw.1 hs).mp
  rw [encodingSchemeExists]
  exact LN.Proofs.derivationRealizable hM (encodingDerivation hM hd)

theorem derivationScope (hM : M.Requirements S) (hd : Derivation S M C Γ t s d) :
    t.fpi ⊆ Γ.dpi := by
  have h := LN.Proofs.derivationScope (encodingDerivation hM hd)
  simpa only [(encodingFreeVariables.1 t),encodingEnvDpi] using h

theorem typingConstraintEquivalent (h : Typing S M C Γ t s) (hD : D.WF S)
    (hDf : D.fpi = ∅) (he : Equivalent S M C D) : Typing S M D Γ t s := by
  obtain ⟨d,hd⟩ := h
  have hw := derivationWF hd
  exact ⟨d,.convert ⟨hD,hw.2.1,hw.2.2.1,hDf,hw.2.2.2.2.1,hw.2.2.2.2.2⟩ hd he
    (envAlphaReflexive Γ) (exprAlphaReflexive t) (schemeAlphaReflexive s)⟩

/-- Replace equivalent qualifications after choosing the common quantifiers
fresh for the ambient constraint and context. The extra existential is discharged
by realizability of the result, not by realizability of the whole context. -/
theorem typingQualificationEquivalent (hM : M.Requirements S)
    (h : Typing S M C Γ t (.all A D T)) (hE : E.WF S) (hEf : E.fpi = ∅)
    (he : Equivalent S M D E) (hf : Disjoint A (C.fv ∪ Γ.fv)) :
    Typing S M C Γ t (.all A E T) := by
  obtain ⟨d,hd⟩ := h
  have hw := derivationWF hd
  have hDw := hw.2.2.1.2.1
  have hTw := hw.2.2.1.2.2
  have hDf : D.fpi = ∅ := hw.2.2.2.2.2
  have hiw : JudgmentWF S (.conj C D) Γ (.mono T) :=
    ⟨⟨hw.1,hDw⟩,hw.2.1,⟨by simp,trivial,hTw⟩,
      by simp [Constraint.fpi,hw.2.2.2.1,hDf],hw.2.2.2.2.1,rfl⟩
  have hi : Typing S M (.conj C D) Γ t (.mono T) := ⟨_,.inst hiw hd⟩
  have hj := typingConstraintEquivalent hi (show (Constraint.conj C E).WF S from ⟨hw.1,hE⟩)
    (by simp [Constraint.fpi,hw.2.2.2.1,hEf])
    ⟨fun ρ ι hρ hι hh => ⟨hh.1,he.1 ρ ι hρ hι hh.2⟩,
      fun ρ ι hρ hι hh => ⟨hh.1,he.2 ρ ι hρ hι hh.2⟩⟩
  have hgw : JudgmentWF S (.conj C (.exists_ A E)) Γ (.all A E T) :=
    ⟨⟨hw.1,hw.2.2.1.1,hE⟩,hw.2.1,⟨hw.2.2.1.1,hE,hTw⟩,
      by simp [Constraint.fpi,hw.2.2.2.1,hEf],hw.2.2.2.2.1,hEf⟩
  have hg : Typing S M (.conj C (.exists_ A E)) Γ t (.all A E T) :=
    ⟨_,.gen hgw hj.choose_spec hf⟩
  apply typingConstraintEquivalent hg hw.1 hw.2.2.2.1
  refine ⟨fun _ _ _ _ hh => hh.1,?_⟩
  intro ρ ι hρ hι hh
  obtain ⟨ρ',hρ',ha,hD⟩ := derivationRealizable hM hd ρ ι hρ hι hh
  exact ⟨hh,ρ',hρ',ha,he.1 ρ' ι hρ' hι hD⟩

end HMX.Proofs
