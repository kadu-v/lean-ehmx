import SystemFXi.EHMX.GenericOrigin

namespace SystemFXi.EHMX.Generic

open SystemFXi.EHMX

/-- Once the declarative clause can be aligned with every assignment of the
rigid operation parameters, completeness of the clause generator supplies
the existential witnesses required by the handler constraint. -/
theorem Output.CoversAt.handlerClause_of_aligned
    {X : ConstraintSystem}
    (Γg Γd : Context X) (D : X.Formula)
    (s : Supply) (r : Output X) (τ a : Ty) (ε χ : Effect)
    (bt be : Finset Nat)
    (hboundT : ∀ i ∈ r.supportTypes, i < r.next.types)
    (hboundE : ∀ i ∈ r.supportEffects, i < r.next.effects)
    (haT : ∀ i ∈ a.fvTypes, i < s.types)
    (haE : ∀ i ∈ a.fvEffects, i < s.effects)
    (hχ : ∀ i ∈ χ.vars, i < s.effects)
    (hcov : r.CoversAt Γg Γd D s τ ε)
    (v : Valuation)
    (halign : ∀ ft : Nat → GroundTy, ∀ fe : Nat → Finset Op,
      (∀ i, i ∉ bt → ft i = v.types i) →
      (∀ i, i ∉ be → fe i = v.effects i) →
      ∃ vd : Valuation,
        Γg.MoreGeneralAt Γd ⟨ft, fe⟩ vd ∧
        X.holds D vd ∧
        τ.eval vd = a.eval ⟨ft, fe⟩ ∧
        ε.eval vd.effects ⊆ χ.eval fe) :
    X.holds
      (X.handlerClause bt be
        (Finset.range r.next.types \ Finset.range s.types)
        (Finset.range r.next.effects \ Finset.range s.effects)
        (X.combine r.condition
          (X.combine (X.equalType r.ty a)
            (X.includedEffect r.effect χ)))) v := by
  apply (X.handlerClause_iff bt be _ _ _ v).2
  intro ft fe hft hfe
  obtain ⟨vd, hctx, hD, htarget, heffect⟩ :=
    halign ft fe hft hfe
  have hproj := Output.CoversAt.project_clause Γg Γd D s r τ a ε χ
    hboundT hboundE haT haE hχ hcov
    ⟨ft, fe⟩ vd hctx hD htarget heffect
  obtain ⟨wt, we, hwt, hwe, hbody⟩ :=
    (X.projection_iff _ _ _ ⟨ft, fe⟩).1 hproj
  exact ⟨wt, we, hwt, hwe, hbody⟩

end SystemFXi.EHMX.Generic
