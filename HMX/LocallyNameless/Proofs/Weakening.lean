import HMX.LocallyNameless.Proofs.TypingSupport

namespace HMX.LN.Proofs

theorem envBinderEqRefl (Γ : Env) : Γ.BinderEq Γ := by
  induction Γ with
  | nil => exact .nil
  | cons a Γ ih => exact .cons ⟨rfl, .refl⟩ ih

theorem judgmentChangeConstraint (h : JudgmentWF S C Γ t s)
    (he : E.WF S [] 0) (hf : E.fpi = ∅) : JudgmentWF S E Γ t s :=
  ⟨he, h.2.1, h.2.2.1, h.2.2.2.1, hf, h.2.2.2.2.2⟩

theorem existsNamesFv (xs : List TVar) (C : Constraint) :
    (C.existsNames xs).fv = C.fv \ xs.toFinset := constraintCloseFv xs C 0

theorem generalizeFv (xs : List TVar) (C : Constraint) (T : Ty) :
    (Scheme.generalize xs C T).fv = (C.fv ∪ T.fv) \ xs.toFinset := by
  simp only [Scheme.generalize, Scheme.fv, Constraint.closeTypes, constraintCloseFv, tyCloseFv, Finset.union_sdiff_distrib]

theorem existsNamesFpi (xs : List TVar) (C : Constraint) :
    (C.existsNames xs).fpi = C.fpi := constraintMapTypesFpi _ C 0

theorem existsNamesIntro (xs : List TVar) (C : Constraint)
    (hk : ∀ X ∈ xs, X.1 ∈ S.kinds) (hw : C.WF S [] 0) : Entails S M C (C.existsNames xs) := by
  intro ρ ι hρ _ he
  apply (existsNamesHolds S M ρ ι xs C hw).mpr
  exact ⟨xs.map ρ, assignmentBlockKinds S M ρ xs hρ hk, by simpa [assignBlockSelf] using he⟩

theorem freshenGeneralization (hS : S.Valid) (F : Vars) (xs : List TVar)
    (hn : xs.Nodup) (hf : Disjoint xs.toFinset (C.fv ∪ Γ.fv))
    (hd : Derivation S M (.conj C D) Γ t (.mono T) d) :
    ∃ ys E U, ys.Nodup ∧ Disjoint ys.toFinset F ∧ Disjoint ys.toFinset (C.fv ∪ Γ.fv) ∧
      E.existsNames ys = D.existsNames xs ∧ Scheme.generalize ys E U = Scheme.generalize xs D T ∧
      Derivation S M (.conj C E) Γ t (.mono U) d := by
  let G := C.fv ∪ Γ.fv ∪ ((D.fv ∪ T.fv) \ xs.toFinset)
  have hG : Disjoint xs.toFinset G := by
    apply Finset.disjoint_left.mpr
    intro X hx hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact Finset.disjoint_left.mp hf hx hg
    · exact (Finset.mem_sdiff.mp hg).2 hx
  obtain ⟨p,hpk,hpg,hpf⟩ := freshTypePermutation xs.toFinset (F ∪ G) G hG
  have hC : C.subst (typeRename p) = C := constraintRenameFixed p C 0
    (fun X hx => hpg X (by simp [G, hx]))
  have hΓ : Γ.subst (typeRename p) = Γ := envRenameFixed p Γ
    (fun X hx => hpg X (by simp [G, hx]))
  have hD : (D.existsNames xs).subst (typeRename p) = D.existsNames xs := by
    apply constraintRenameFixed
    intro X hx
    rw [existsNamesFv] at hx
    exact hpg X (Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩))
  have hs : (Scheme.generalize xs D T).subst (typeRename p) = Scheme.generalize xs D T := by
    apply schemeRenameFixed
    intro X hx
    rw [generalizeFv] at hx
    exact hpg X (Finset.mem_union_right _ hx)
  have hnew : Disjoint (xs.map p).toFinset (F ∪ G) := by
    apply Finset.disjoint_left.mpr
    intro Y hy hY
    obtain ⟨X,hX,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact hpf X (List.mem_toFinset.mpr hX) hY
  refine ⟨xs.map p, D.subst (typeRename p), T.subst (typeRename p), hn.map p.injective,
    hnew.mono_right (Finset.subset_union_left), ?_, ?_, ?_, ?_⟩
  · exact hnew.mono_right (fun X hx => Finset.mem_union_right _ (Finset.mem_union_left _ hx))
  · exact (renameExistsNames p hpk xs D).symm.trans hD
  · exact (renameGeneralize p hpk xs D T).symm.trans hs
  · simpa only [substConj, substMono, hC, hΓ] using derivationRename hS p hpk hd

theorem freshenExistential (hS : S.Valid) (F : Vars) (xs : List TVar)
    (hn : xs.Nodup) (hf : Disjoint xs.toFinset (Γ.fv ∪ s.fv))
    (hd : Derivation S M C Γ t s d) :
    ∃ ys D, ys.Nodup ∧ Disjoint ys.toFinset F ∧ Disjoint ys.toFinset (Γ.fv ∪ s.fv) ∧
      D.existsNames ys = C.existsNames xs ∧ Derivation S M D Γ t s d := by
  let G := Γ.fv ∪ s.fv ∪ (C.fv \ xs.toFinset)
  have hG : Disjoint xs.toFinset G := by
    apply Finset.disjoint_left.mpr
    intro X hx hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact Finset.disjoint_left.mp hf hx hg
    · exact (Finset.mem_sdiff.mp hg).2 hx
  obtain ⟨p,hpk,hpg,hpf⟩ := freshTypePermutation xs.toFinset (F ∪ G) G hG
  have hΓ : Γ.subst (typeRename p) = Γ := envRenameFixed p Γ
    (fun X hx => hpg X (by simp [G, hx]))
  have hs : s.subst (typeRename p) = s := schemeRenameFixed p s
    (fun X hx => hpg X (by simp [G, hx]))
  have hC : (C.existsNames xs).subst (typeRename p) = C.existsNames xs := by
    apply constraintRenameFixed
    intro X hx
    rw [existsNamesFv] at hx
    exact hpg X (Finset.mem_union_right _ hx)
  have hnew : Disjoint (xs.map p).toFinset (F ∪ G) := by
    apply Finset.disjoint_left.mpr
    intro Y hy hY
    obtain ⟨X,hX,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
    exact hpf X (List.mem_toFinset.mpr hX) hY
  refine ⟨xs.map p, C.subst (typeRename p), hn.map p.injective,
    hnew.mono_right Finset.subset_union_left, ?_, ?_, ?_⟩
  · exact hnew.mono_right (fun X hx => Finset.mem_union_right _ (Finset.mem_union_left _ hx))
  · exact (renameExistsNames p hpk xs C).symm.trans hC
  · simpa only [hΓ, hs] using derivationRename hS p hpk hd

theorem derivationWeakeningBound (hM : M.Requirements S) (n : Nat) :
    ∀ C Γ t s d, Derivation S M C Γ t s d → sizeOf d ≤ n →
      ∀ E, JudgmentWF S E Γ t s → Entails S M E C → Derivation S M E Γ t s d := by
  induction n using Nat.strong_induction_on with
  | h n outer =>
    intro C Γ t s d hd
    induction hd with
    | var hw hl hr =>
        intro hb E he hEC
        exact .var he hl (fun ρ ι hρ hι h => hr ρ ι hρ hι (hEC ρ ι hρ hι h))
    | abs L hw hd ih =>
        intro hb E he hEC
        apply Derivation.abs L he
        intro z hz
        apply ih z hz (by simp only [Shape.node.sizeOf_spec, List.cons.sizeOf_spec] at hb; omega) E
          (judgmentChangeConstraint (derivationWF (hd z hz)) he.1 he.2.2.2.2.1) hEC
    | app hw ht hu iht ihu =>
        intro hb E he hEC
        exact .app he
          (iht (by simp only [Shape.node.sizeOf_spec, List.cons.sizeOf_spec] at hb; omega) E
            (judgmentChangeConstraint (derivationWF ht) he.1 he.2.2.2.2.1) hEC)
          (ihu (by simp only [Shape.node.sizeOf_spec, List.cons.sizeOf_spec] at hb; omega) E
            (judgmentChangeConstraint (derivationWF hu) he.1 he.2.2.2.2.1) hEC)
    | letE L hw ht hu iht ihu =>
        intro hb E he hEC
        apply Derivation.letE L he
          (iht (by simp only [Shape.node.sizeOf_spec, List.cons.sizeOf_spec] at hb; omega) E
            (judgmentChangeConstraint (derivationWF ht) he.1 he.2.2.2.2.1) hEC)
        intro z hz
        exact ihu z hz (by simp only [Shape.node.sizeOf_spec, List.cons.sizeOf_spec] at hb; omega) E
          (judgmentChangeConstraint (derivationWF (hu z hz)) he.1 he.2.2.2.2.1) hEC
    | @gen C Γ t xs D T d hw hn hf hd ih =>
        intro hb E he hEC
        obtain ⟨ys,D',T',hyn,hyE,hyCG,hD,hs,hd'⟩ := freshenGeneralization hM.1 E.fv xs hn hf hd
        have hw' := derivationWF hd'
        have hDf : D'.fpi = ∅ := (Finset.union_eq_empty.mp hw'.2.2.2.2.1).2
        have hDwf : (D'.existsNames ys).WF S [] 0 := hD ▸ hw.1.2
        have hDhk := (existsNamesWFReflect S ys D' hDwf).1
        have hE' : JudgmentWF S (.conj E D') Γ t (.mono T') :=
          judgmentChangeConstraint hw' ⟨he.1,hw'.1.2⟩ (by simp [Constraint.fpi, he.2.2.2.2.1, hDf])
        have hp : Derivation S M (.conj E D') Γ t (.mono T') d :=
          outer (sizeOf d) (by simp only [Shape.node.sizeOf_spec, List.cons.sizeOf_spec] at hb; omega)
            _ _ _ _ _ hd' le_rfl _ hE'
            (fun ρ ι hρ hι hh => ⟨(hEC ρ ι hρ hι hh.1).1,hh.2⟩)
        have hout : JudgmentWF S (.conj E (D'.existsNames ys)) Γ t (Scheme.generalize ys D' T') := by
          rw [hs]
          exact judgmentChangeConstraint he ⟨he.1,hDwf⟩
            (by simp [Constraint.fpi, existsNamesFpi, he.2.2.2.2.1, hDf])
        have hg := Derivation.gen hout hyn (Finset.disjoint_union_right.mpr
          ⟨hyE,hyCG.mono_right Finset.subset_union_right⟩) hp
        rw [hs] at hg
        apply Derivation.convert he hg ?_ (envBinderEqRefl _) .refl
        exact ⟨fun _ _ _ _ hh => hh.1,
          fun ρ ι hρ hι hh => ⟨hh, by rw [hD]; exact (hEC ρ ι hρ hι hh).2⟩⟩
    | @inst C D Γ t T xs d hw hn hd ih =>
        intro hb E he hEC
        have hp := ih (by simp only [Shape.node.sizeOf_spec, List.cons.sizeOf_spec] at hb; omega) E
          (judgmentChangeConstraint (derivationWF hd) he.1 he.2.2.2.2.1)
          (fun ρ ι hρ hι hh => (hEC ρ ι hρ hι hh).1)
        have hDf : D.fpi = ∅ := (Finset.union_eq_empty.mp hw.2.2.2.2.1).2
        have hw' : JudgmentWF S (.conj E D) Γ t (.mono T) :=
          judgmentChangeConstraint he ⟨he.1,hw.1.2⟩ (by simp [Constraint.fpi, he.2.2.2.2.1, hDf])
        apply Derivation.convert he (Derivation.inst hw' hn hp) ?_
          (envBinderEqRefl _) .refl
        exact ⟨fun _ _ _ _ hh => hh.1,fun ρ ι hρ hι hh => ⟨hh,(hEC ρ ι hρ hι hh).2⟩⟩
    | sub hw hd ht ih =>
        intro hb E he hEC
        exact .sub he
          (ih (by simp only [Shape.node.sizeOf_spec, List.cons.sizeOf_spec] at hb; omega) E
            (judgmentChangeConstraint (derivationWF hd) he.1 he.2.2.2.2.1) hEC)
          (fun ρ ι hρ hι hh => ht ρ ι hρ hι (hEC ρ ι hρ hι hh))
    | @exists_ Γ t s xs C d hw hn hk hf hd ih =>
        intro hb E he hEC
        obtain ⟨ys,D,hyn,hyE,hyΓs,hD,hd'⟩ := freshenExistential hM.1 E.fv xs hn hf hd
        have hw' := derivationWF hd'
        have hDwf : (D.existsNames ys).WF S [] 0 := hD ▸ hw.1
        have hDhk := (existsNamesWFReflect S ys D hDwf).1
        have hpw : JudgmentWF S (.conj E D) Γ t s :=
          judgmentChangeConstraint he ⟨he.1,hw'.1⟩
            (by simp [Constraint.fpi, he.2.2.2.2.1, hw'.2.2.2.2.1])
        have hp : Derivation S M (.conj E D) Γ t s d :=
          outer (sizeOf d) (by simp only [Shape.node.sizeOf_spec, List.cons.sizeOf_spec] at hb; omega)
            _ _ _ _ _ hd' le_rfl _ hpw (fun _ _ _ _ hh => hh.2)
        have hqwf := existsNamesWF S ys (.conj E D) 0 hDhk hpw.1
        have hqw : JudgmentWF S ((Constraint.conj E D).existsNames ys) Γ t s :=
          judgmentChangeConstraint he hqwf (by rw [existsNamesFpi]; exact hpw.2.2.2.2.1)
        have hq := Derivation.exists_ hqw hyn hDhk hyΓs hp
        apply Derivation.convert he hq ?_ (envBinderEqRefl _) .refl
        constructor
        · intro ρ ι hρ hι hh
          obtain ⟨vs,hvs,hh⟩ := (existsNamesHolds S M ρ ι ys (.conj E D) hpw.1).mp hh
          exact (holdsAssignBlock S M hM ρ ι ys vs E hρ hι hvs he.1 hyE).mp hh.1
        · intro ρ ι hρ hι hh
          have hde : (D.existsNames ys).Holds S M ρ ι := by rw [hD]; exact hEC ρ ι hρ hι hh
          obtain ⟨vs,hvs,hhD⟩ := (existsNamesHolds S M ρ ι ys D hw'.1).mp hde
          exact (existsNamesHolds S M ρ ι ys (.conj E D) hpw.1).mpr
            ⟨vs,hvs,(holdsAssignBlock S M hM ρ ι ys vs E hρ hι hvs he.1 hyE).mpr hh,hhD⟩
    | convert hw hd hc hΓ hs ih =>
        intro hb E he hEC
        exact .convert he
          (ih hb E (judgmentChangeConstraint (derivationWF hd) he.1 he.2.2.2.2.1)
            (fun ρ ι hρ hι hh => hc.2 ρ ι hρ hι (hEC ρ ι hρ hι hh)))
          ⟨fun _ _ _ _ hh => hh,fun _ _ _ _ hh => hh⟩ hΓ hs

theorem lemma10_3_1_weakening (S : Signature) (M : Model) (I : Set Nat) :
    HMX.LN.lemma10_3_1_weakening S M I := by
  intro hF C E Γ t s d he hEC hd
  exact derivationWeakeningBound hF.1 (sizeOf d) C Γ t s d hd le_rfl E he hEC

end HMX.LN.Proofs
