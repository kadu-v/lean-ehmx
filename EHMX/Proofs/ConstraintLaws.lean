import EHMX.Proofs.Kind

namespace EHMX

theorem entailsRefl : Entails S M Δ C C := fun _ _ _ _ _ _ h => h
theorem entailsTrans (hCD : Entails S M Δ C D) (hDE : Entails S M Δ D E) :
    Entails S M Δ C E :=
  fun ρ bs ι hρ hbs hι h => hDE ρ bs ι hρ hbs hι (hCD ρ bs ι hρ hbs hι h)

theorem leRefl (hF : EffectFramework S M) (hk : k ∈ S.kinds)
    (hT : Ty.HasKind S Δ T k) : Entails S M Δ C (.le k T T) := by
  intro ρ bs ι hρ hbs _ _
  have h := evalKind hF hρ hbs hT
  exact ⟨h, h, hF.belowRefl k hk _ h⟩

theorem effectEmptyBelow (hF : EffectFramework S M) (hε : Ty.HasKind S Δ ε 1) :
    Entails S M Δ C (.le 1 .empty ε) := by
  intro ρ bs ι hρ hbs _ _
  have he := evalKind hF hρ hbs (emptyKind (Δ := Δ) hF.signature)
  have hε' := evalKind hF hρ hbs hε
  refine ⟨he, hε', (hF.effectOrder _ _ he hε').mpr ?_⟩
  simp only [Ty.empty, Ty.eval, List.map_nil]
  rw [hF.emptyEffect]
  exact Set.empty_subset _

theorem forallHoldsElim (h : (Constraint.forall_ ks C).Holds M ρ bs ι)
    (hvs : KindValues M ks vs) : C.Holds M ρ (vs ++ bs) ι := h vs hvs

theorem forallHoldsIntro
    (h : ∀ vs, KindValues M ks vs → C.Holds M ρ (vs ++ bs) ι) :
    (Constraint.forall_ ks C).Holds M ρ bs ι := h

/-- Universal constraints are not existential witnesses chosen by the handler. -/
theorem forallConjunction :
    (Constraint.forall_ ks (.conj C D)).Holds M ρ bs ι ↔
      (Constraint.forall_ ks C).Holds M ρ bs ι ∧
      (Constraint.forall_ ks D).Holds M ρ bs ι := by
  constructor
  · intro h; exact ⟨fun vs hv => (h vs hv).1, fun vs hv => (h vs hv).2⟩
  · rintro ⟨hC,hD⟩; exact fun vs hv => ⟨hC vs hv, hD vs hv⟩

theorem schemeUpperSet (hF : EffectFramework S M) (s : Scheme)
    (hs : s.WF S Δ n) (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs) :
    UpperSet M (s.denote M ρ bs ι) := by
  cases s with
  | all ks C T =>
      constructor
      · exact fun a ha => ha.1
      · rintro a ⟨ha, vs, hv, hC, hTa⟩ b hb hab
        refine ⟨hb, vs, hv, hC, ?_⟩
        have hT := evalKind hF hρ (List.rel_append hv hbs) hs.2.2
        exact hF.belowTrans 0 hF.signature.1 _ _ _ hT ha hb hTa hab

theorem monoInstance (hF : EffectFramework S M) (hT : Ty.HasKind S Δ T 0) :
    Entails S M Δ C ((Scheme.mono T).instanceConstraint T) := by
  intro ρ bs ι hρ hbs _ _
  simp only [Scheme.mono, Scheme.instanceConstraint, Constraint.Holds]
  refine ⟨[], List.Forall₂.nil, trivial, ?_⟩
  have h := evalKind hF hρ hbs hT
  simpa only [Constraint.le, List.length_nil, tyShiftZero, Constraint.Holds,
    List.nil_append, List.map_cons, List.map_nil, Predicate.eval] using
    And.intro h (And.intro h (hF.belowRefl 0 hF.signature.1 _ h))

end EHMX
