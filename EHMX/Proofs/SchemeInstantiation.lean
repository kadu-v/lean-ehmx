import EHMX.Proofs.TypingTypeSubstitution

/-!
多相値代入の変数分岐で必要な具体化。
`Scheme.instanceConstraint` の証人はモデルの値であり、型構文で表現可能と
仮定しない。証人を `Typing.exists_` の内側に残して型付けを構成する。
項全体へのスキーム値代入とは別の補題である。
-/
namespace EHMX

theorem constraintShiftHolds (hC : Constraint.WF S Δ n C)
    (ρ : Assignment M) (bs vs : List M.Carrier) (ι : GroundEnv M) :
    (C.shift vs.length 0).Holds M ρ (vs ++ bs) ι ↔ C.Holds M ρ bs ι := by
  rw [shiftSubstBound.1]
  apply (substBoundSemantics M).1 C _ _ hC
  intro i k hi
  have hn : ¬ i + vs.length < vs.length := by omega
  simp [Ty.eval, List.getElem?_append, hn]

theorem entailsShift (hF : EffectFramework S M) (ks : List Kind)
    (hC : Constraint.WF S Δ 0 C) (hD : Constraint.WF S Δ 0 D)
    (h : Entails S M Δ C D) :
    Entails S M (ks ++ Δ) (C.shift ks.length 0) (D.shift ks.length 0) := by
  simpa only [shiftSubstBound.1, Nat.not_lt_zero, ↓reduceIte] using
    entailsSubstBound hF (BoundSubst.validShift ks) hC hD h

theorem constraintShiftWF (hC : Constraint.WF S Δ n C) (ks : List Kind) :
    (C.shift ks.length 0).WF S (ks ++ Δ) n := by
  rw [shiftSubstBound.1]
  simpa only [Nat.not_lt_zero, ↓reduceIte] using
    (substBoundWF S).1 C _ _ hC _ _ (BoundSubst.validShift ks)

theorem constraintShiftFpi (C : Constraint) (n d : Nat) : (C.shift n d).fpi = C.fpi := by
  rw [shiftSubstBound.1]
  exact substBoundFpi.1 _ _

/-- At a variable use, instantiate the generalized derivation under any stronger
well-formed constraint. The model's witness remains under an existential binder.
Used by the pending SchemeValueSubstitutionGoal, not a proof of that goal itself. -/
theorem schemeValueInstantiation (hF : EffectFramework S M)
    (ht : Typing S M sig (ks ++ Δ) (.conj (C.shift ks.length 0) D)
      (Γ.shift ks.length) v A .empty)
    (hks : ∀ k ∈ ks, k ∈ S.kinds)
    (hw : JudgmentWF S Δ E Γ v T .empty)
    (hC : Constraint.WF S Δ 0 C)
    (hEC : Entails S M Δ E C)
    (hinst : Entails S M Δ E ((Scheme.all ks D A).instanceConstraint T)) :
    Typing S M sig Δ E Γ v T .empty := by
  let K : Constraint := .conj (E.shift ks.length 0)
    (.conj D (.le 0 A (T.shift ks.length 0)))
  have htw := typingWF ht
  have hEshift := constraintShiftWF hw.1 ks
  have hTshift := kindShift hw.2.2.2.2.1 ks
  have hK : K.WF S (ks ++ Δ) 0 :=
    ⟨hEshift, htw.1.2, leConstraintWF hF.signature.1 htw.2.2.2.2.1 hTshift⟩
  have hDf : D.fpi = ∅ := Finset.union_eq_empty.mp htw.2.1 |>.2
  have hKf : K.fpi = ∅ := by
    simp [K, Constraint.fpi, Constraint.le, constraintShiftFpi, hw.2.1, hDf]
  have hKC : Entails S M (ks ++ Δ) K (.conj (C.shift ks.length 0) D) := by
    intro ρ bs ι hρ hbs hι hK'
    exact ⟨entailsShift hF ks hw.1 hC hEC ρ bs ι hρ hbs hι hK'.1, hK'.2.1⟩
  have hvA : Typing S M sig (ks ++ Δ) K (Γ.shift ks.length) v A .empty :=
    .strengthen ⟨hK, hKf, htw.2.2⟩ ht hKC
  have hvT : Typing S M sig (ks ++ Δ) K (Γ.shift ks.length) v
      (T.shift ks.length 0) .empty := by
    refine .sub ⟨hK, hKf, htw.2.2.1, htw.2.2.2.1, hTshift,
      emptyKind hF.signature⟩ hvA ?_ ?_
    · exact fun _ _ _ _ _ _ h => h.2.2
    · exact leRefl hF hF.signature.2.1 (emptyKind hF.signature)
  have hExists : Typing S M sig Δ (.exists_ ks K) Γ v T .empty := by
    apply Typing.exists_ ⟨⟨hks, hK⟩, hKf, hw.2.2⟩
    simpa only [Ty.empty, Ty.shift, List.map_nil] using hvT
  apply Typing.strengthen hw hExists
  intro ρ bs ι hρ hbs hι hE
  obtain ⟨vs, hvs, hD, hle⟩ := hinst ρ bs ι hρ hbs hι hE
  refine ⟨vs, hvs, ?_, hD, hle⟩
  have hlen := hvs.length_eq
  exact (by simpa only [← hlen] using
    (constraintShiftHolds hw.1 ρ bs vs ι).mpr hE)

end EHMX
