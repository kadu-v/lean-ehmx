import HMX.LocallyNameless.Proofs.NamedRenaming

namespace HMX.Proofs

open LN.Proofs

theorem renamedAssignmentValid (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (hρ : Assignment.Valid S M ρ) : Assignment.Valid S M (ρ ∘ p) := by
  intro X hx
  simpa only [Function.comp_apply,hk] using hρ (p X) (by simpa only [hk] using hx)

theorem inverseKindPermutation (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1) :
    ∀ X, (p.symm X).1 = X.1 := fun X => (hk (p.symm X)).symm.trans (by simp)

theorem namedTyRenameEval (p : TVar ≃ TVar) (T : Ty) (ρ : Assignment M) :
    (namedTyRename p T).eval M ρ = T.eval M (ρ ∘ p) := by
  cases T with
  | var X => simp [namedTyRename,Ty.eval]
  | con f ts =>
    simp only [namedTyRename,Ty.eval,List.map_map,Function.comp_def]
    congr 1
    exact List.map_congr_left (fun U _ => namedTyRenameEval p U ρ)
termination_by sizeOf T

mutual
theorem namedConstraintRenameSem (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (C : Constraint) (ρ : Assignment M) (ι : GroundEnv M) :
    (namedConstraintRename p C).Holds S M ρ ι ↔ C.Holds S M (ρ ∘ p) ι := by
  cases C with
  | truth | falsity => rfl
  | atom q ts => simp only [namedConstraintRename,Constraint.Holds,List.map_map,
      Function.comp_def,namedTyRenameEval]
  | conj C D => exact and_congr (namedConstraintRenameSem p hk C ρ ι) (namedConstraintRenameSem p hk D ρ ι)
  | exists_ A C =>
    constructor
    · rintro ⟨σ,hσ,ha,hc⟩
      refine ⟨σ ∘ p,renamedAssignmentValid p hk hσ,?_,(namedConstraintRenameSem p hk C σ ι).mp hc⟩
      intro X hx
      exact ha (p X) (by simpa using hx)
    · rintro ⟨σ,hσ,ha,hc⟩
      refine ⟨σ ∘ p.symm,renamedAssignmentValid p.symm (inverseKindPermutation p hk) hσ,?_,?_⟩
      · intro X hx
        have hh := ha (p.symm X) (fun hh => hx (Finset.mem_image.mpr ⟨p.symm X,hh,p.apply_symm_apply X⟩))
        simpa [Function.comp_def] using hh
      · apply (namedConstraintRenameSem p hk C _ ι).mpr
        simpa [Function.comp_def] using hc
  | def_ x s C =>
    simp only [namedConstraintRename,Constraint.Holds,namedSchemeRenameSem p hk s ρ ι]
    exact namedConstraintRenameSem p hk C ρ _
  | inst x T => simp only [namedConstraintRename,Constraint.Holds,namedTyRenameEval]
theorem namedSchemeRenameSem (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (s : Scheme) (ρ : Assignment M) (ι : GroundEnv M) :
    (namedSchemeRename p s).denote S M ρ ι = s.denote S M (ρ ∘ p) ι := by
  cases s with
  | all A C T =>
    ext v
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨σ,hσ,ha,hc,ht⟩
      refine ⟨σ ∘ p,renamedAssignmentValid p hk hσ,?_,(namedConstraintRenameSem p hk C σ ι).mp hc,?_⟩
      · intro X hx; exact ha (p X) (by simpa using hx)
      · simpa only [namedTyRenameEval] using ht
    · rintro ⟨σ,hσ,ha,hc,ht⟩
      refine ⟨σ ∘ p.symm,renamedAssignmentValid p.symm (inverseKindPermutation p hk) hσ,?_,?_,?_⟩
      · intro X hx
        have hh := ha (p.symm X) (fun hh => hx (Finset.mem_image.mpr ⟨p.symm X,hh,p.apply_symm_apply X⟩))
        simpa [Function.comp_def] using hh
      · apply (namedConstraintRenameSem p hk C _ ι).mpr
        simpa [Function.comp_def] using hc
      · simpa [namedTyRenameEval,Function.comp_def] using ht
end

theorem namedEquivalentRename (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (he : Equivalent S M C D) : Equivalent S M (namedConstraintRename p C) (namedConstraintRename p D) := by
  constructor
  · intro ρ ι hρ hι hh
    exact (namedConstraintRenameSem p hk D ρ ι).mpr
      (he.1 _ ι (renamedAssignmentValid p hk hρ) hι ((namedConstraintRenameSem p hk C ρ ι).mp hh))
  · intro ρ ι hρ hι hh
    exact (namedConstraintRenameSem p hk C ρ ι).mpr
      (he.2 _ ι (renamedAssignmentValid p hk hρ) hι ((namedConstraintRenameSem p hk D ρ ι).mp hh))

theorem bindsSymmetric (h : Binds r r' A B) :
    Binds (fun X Y => r Y X) (fun X Y => r' Y X) B A := by
  refine ⟨?_,?_,?_⟩
  · intro Y hy
    obtain ⟨X,hx,hu⟩ := h.2.1 Y hy
    exact ⟨X,⟨hx.1,hx.2.1.symm,hx.2.2⟩,fun Z hz => hu Z ⟨hz.1,hz.2.1.symm,hz.2.2⟩⟩
  · intro X hx
    obtain ⟨Y,hy,hu⟩ := h.1 X hx
    exact ⟨Y,⟨hy.1,hy.2.1.symm,hy.2.2⟩,fun Z hz => hu Z ⟨hz.1,hz.2.1.symm,hz.2.2⟩⟩
  · intro X Y
    apply (h.2.2 Y X).trans
    constructor <;> rintro (⟨ha,hb,hk,hr⟩ | ⟨ha,hb,hr⟩)
    · exact Or.inl ⟨hb,ha,hk.symm,hr⟩
    · exact Or.inr ⟨hb,ha,hr⟩
    · exact Or.inl ⟨hb,ha,hk.symm,hr⟩
    · exact Or.inr ⟨hb,ha,hr⟩

theorem tyRelatedSymmetric (h : Ty.Related r T U) : Ty.Related (fun X Y => r Y X) U T := by
  cases h with
  | var h => exact .var h
  | con h =>
    exact .con (LN.Proofs.forall₂ImplMem h (fun U _ V h => tyRelatedSymmetric h)).flip
termination_by sizeOf T

/-- Symmetry is structural, including the masking of both sides at binders. -/
theorem constraintRelatedSymmetric (h : Constraint.Related r q C D) :
    Constraint.Related (fun X Y => r Y X) (fun x y => q y x) D C := by
  apply Constraint.Related.rec
    (motive_1 := fun r q C D _ => Constraint.Related (fun X Y => r Y X) (fun x y => q y x) D C)
    (motive_2 := fun r q s u _ => Scheme.Related (fun X Y => r Y X) (fun x y => q y x) u s)
    (by intros; exact .truth) (by intros; exact .falsity)
    (by intro r q ts us p h; exact .atom (h.flip.imp (fun _ _ h => tyRelatedSymmetric h)))
    (by intro r q C C' D D' h g ih ij; exact .conj ih ij)
    (by intro r r' A B q C D hb h ih; exact .exists_ (bindsSymmetric hb) ih)
    (by
      intro x y r q s s' C D hb hs hc ihs ihc
      have hb' : y = x ∨ (∃ a b, y = .var a ∧ x = .var b) ∨ (∃ a b, y = .loc a ∧ x = .loc b) := by
        rcases hb with h | ⟨a,b,ha,hb⟩ | ⟨a,b,ha,hb⟩
        · exact Or.inl h.symm
        · exact Or.inr (Or.inl ⟨b,a,hb,ha⟩)
        · exact Or.inr (Or.inr ⟨b,a,hb,ha⟩)
      apply Constraint.Related.def_ hb' ihs
      have he : (fun a b => bindId q x y b a) = bindId (fun a b => q b a) y x := by
        funext a b; apply propext; simp only [bindId]; tauto
      rw [← he]; exact ihc)
    (by intro q x y r T U h ht; exact .inst h (tyRelatedSymmetric ht))
    (by intro r r' A B q C D T U hb hc ht ih; exact .all (bindsSymmetric hb) ih (tyRelatedSymmetric ht)) h

theorem schemeRelatedSymmetric (h : Scheme.Related r q s u) :
    Scheme.Related (fun X Y => r Y X) (fun x y => q y x) u s := by
  cases h with
  | all hb hc ht => exact .all (bindsSymmetric hb) (constraintRelatedSymmetric hc) (tyRelatedSymmetric ht)

theorem schemeAlphaSymmetric (h : Scheme.Alpha s r) : r.Alpha s := by
  have hh := schemeRelatedSymmetric h
  have he : (fun X Y : TVar => Y = X) = Eq := by funext X Y; exact propext eq_comm
  have hi : (fun x y : Id => y = x) = Eq := by funext x y; exact propext eq_comm
  change Scheme.Related Eq Eq r s
  simpa only [he,hi] using hh

theorem typingSchemeAlpha (h : Typing S M C Γ t s) (hr : r.WF S) (hrf : r.fpi = ∅)
    (ha : s.Alpha r) : Typing S M C Γ t r := by
  obtain ⟨d,hd⟩ := h
  have hw := derivationWF hd
  exact ⟨d,.convert ⟨hw.1,hw.2.1,hr,hw.2.2.2.1,hw.2.2.2.2.1,hrf⟩ hd
    ⟨fun _ _ _ _ h => h,fun _ _ _ _ h => h⟩ (envAlphaReflexive Γ) (exprAlphaReflexive t) ha⟩

theorem typingQualificationConversion (hM : M.Requirements S)
    (h : Typing S M C Γ t (.all A D T)) (hE : E.WF S) (hEf : E.fpi = ∅)
    (he : Equivalent S M D E) : Typing S M C Γ t (.all A E T) := by
  have hw := derivationWF h.choose_spec
  let s : Scheme := .all A D T
  let r : Scheme := .all A E T
  have hr : r.WF S := ⟨hw.2.2.1.1,hE,hw.2.2.1.2.2⟩
  obtain ⟨p,hpk,hpf,hfresh⟩ := freshTypePermutation A (C.fv ∪ Γ.fv) (s.fv ∪ r.fv) (by
    apply Finset.disjoint_left.mpr
    intro X hx hX
    rcases Finset.mem_union.mp hX with hX | hX
    · exact (Finset.mem_sdiff.mp hX).2 hx
    · exact (Finset.mem_sdiff.mp hX).2 hx)
  have hsα := namedSchemeRenameAlpha p hpk s (fun X hx => hpf X (Finset.mem_union_left _ hx))
  have hrα := namedSchemeRenameAlpha p hpk r (fun X hx => hpf X (Finset.mem_union_right _ hx))
  have hp := typingSchemeAlpha h (namedSchemeRenameWF p hpk s hw.2.2.1)
    ((namedSchemeRenameFpi p s).trans hw.2.2.2.2.2) hsα
  have hq := typingQualificationEquivalent hM hp (namedConstraintRenameWF p hpk E hE)
    ((namedConstraintRenameFpi p E).trans hEf) (namedEquivalentRename p hpk he)
    (Finset.disjoint_left.mpr (by
      intro X hx hf
      obtain ⟨Y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact hfresh Y hy hf))
  exact typingSchemeAlpha hq hr hEf (schemeAlphaSymmetric hrα)

end HMX.Proofs
