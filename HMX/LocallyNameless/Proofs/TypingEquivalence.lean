import HMX.LocallyNameless.Proofs.TypingSubstitution
import HMX.LocallyNameless.Proofs.TermRenaming

namespace HMX.LN.Proofs

theorem freshKinds (ks : List Nat) (F : Vars) :
    ∃ xs : List TVar, xs.map Prod.fst = ks ∧ xs.Nodup ∧ Disjoint xs.toFinset F := by
  induction ks with
  | nil => exact ⟨[],rfl,by simp,by simp⟩
  | cons k ks ih =>
      obtain ⟨xs,hks,hn,hf⟩ := ih
      obtain ⟨X,hX,hXF⟩ := freshSameKind k (F ∪ xs.toFinset)
      refine ⟨X::xs,by simp [hX,hks],?_,?_⟩
      · exact List.nodup_cons.mpr ⟨fun hx => hXF (Finset.mem_union_right _ (List.mem_toFinset.mpr hx)),hn⟩
      · simpa only [List.toFinset_cons,Finset.disjoint_insert_left] using
          And.intro (fun hx => hXF (Finset.mem_union_left _ hx)) hf

theorem constraintCloseOpen (xs : List TVar) (C : Constraint) (n : Nat) (hn : xs.Nodup)
    (hf : Disjoint xs.toFinset C.fv) :
    (C.mapTypes (fun d T => T.openAt d (xs.map Ty.free)) n).mapTypes (fun d T => T.closeAt d xs) n = C := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ n, Disjoint xs.toFinset C.fv →
      (C.mapTypes (fun d T => T.openAt d (xs.map Ty.free)) n).mapTypes (fun d T => T.closeAt d xs) n = C)
    (motive_2 := fun s => ∀ n, Disjoint xs.toFinset s.fv →
      (s.mapTypes (fun d T => T.openAt d (xs.map Ty.free)) n).mapTypes (fun d T => T.closeAt d xs) n = s)
    (by intros; rfl) (by intros; rfl)
    (by
      intro q ts n hh
      simp only [Constraint.mapTypes,List.map_map]
      congr 1
      exact (List.map_congr_left (g := id) (fun T ht => tyCloseOpen T n xs hn
        (hh.mono_right (fun X hx => (memUnionFold Ty.fv ts X).mpr ⟨T,ht,hx⟩)))).trans (List.map_id ts))
    (by
      intro C D ihC ihD n hh
      exact congrArg₂ Constraint.conj (ihC n (hh.mono_right Finset.subset_union_left))
        (ihD n (hh.mono_right Finset.subset_union_right)))
    (by intro ks C ih n hh; exact congrArg (Constraint.exists_ ks) (ih _ hh))
    (by
      intro b s C ihs ihC n hh
      exact congrArg₂ (Constraint.def_ b) (ihs n (hh.mono_right Finset.subset_union_left))
        (ihC n (hh.mono_right Finset.subset_union_right)))
    (by intro x T n hh; exact congrArg (Constraint.inst x) (tyCloseOpen T n xs hn hh))
    (by
      intro ks C T ih n hh
      exact congrArg₂ (Scheme.all ks) (ih _ (hh.mono_right Finset.subset_union_left))
        (tyCloseOpen T _ xs hn (hh.mono_right Finset.subset_union_right))) C n hf

theorem schemeFreshOpening (s : Scheme) (hs : s.WF S [] 0) (F : Vars) :
    ∃ xs D T, xs.Nodup ∧ Disjoint xs.toFinset F ∧
      (∀ X ∈ xs, X.1 ∈ S.kinds) ∧ D.WF S [] 0 ∧ T.HasKind S [] 0 ∧
      Scheme.generalize xs D T = s := by
  cases s with
  | all ks C T =>
      obtain ⟨xs,hks,hn,hf⟩ := freshKinds ks (F ∪ (C.fv ∪ T.fv))
      have hkxs : ∀ X ∈ xs, X.1 ∈ S.kinds := by
        intro X hx
        exact hs.1 X.1 (hks ▸ List.mem_map.mpr ⟨X,hx,rfl⟩)
      have hu : List.Forall₂ (Ty.HasKind S []) (xs.map Ty.free) ks := by
        rw [← hks]
        apply List.forall₂_map_left_iff.mpr
        apply List.forall₂_map_right_iff.mpr
        exact List.forall₂_same.mpr (fun X hx => .free (hkxs X hx))
      refine ⟨xs,C.openTypes (xs.map Ty.free),T.openAt 0 (xs.map Ty.free),hn,
        hf.mono_right Finset.subset_union_left,hkxs,?_,?_,?_⟩
      · exact typeOpeningWF S ks _ C (by simpa using hs.2.1) hu
      · exact tyOpenKind S T ks [] _ hu 0 (by simpa using hs.2.2)
      · unfold Scheme.generalize
        rw [hks]
        congr 1
        · exact constraintCloseOpen xs C 0 hn (hf.mono_right
            (fun X hx => Finset.mem_union_right _ (Finset.mem_union_left _ hx)))
        · exact tyCloseOpen T 0 xs hn (hf.mono_right
            (fun X hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)))

theorem monoSelfMember (hM : M.Requirements S) (T : Ty) (hT : T.HasKind S [] 0)
    (ρ : Assignment M) (ι : GroundEnv M) (hρ : ρ.Valid S M) :
    T.eval M ρ ∈ (Scheme.mono T).denote S M ρ ι := by
  have hk := evalKind S M hM ρ hρ T 0 hT
  exact (monoDenote S M ρ ι T _).mpr ⟨hk,hM.2.2.2.1 0 (tyKindDeclared S hM.1 T [] 0 hT) _ hk⟩

theorem alternateMonoInstance (hF : Framework S M I) (hd : AlternateTyping S M C Γ t T)
    (he : JudgmentWF S E Γ t (.mono U)) (hEC : Entails S M E C)
    (hi : ∀ ρ ι, ρ.Valid S M → ι.Valid M → E.Holds S M ρ ι → U.eval M ρ ∈ (Scheme.mono T).denote S M ρ ι) :
    AlternateTyping S M E Γ t U := by
  have hp := alternateWeakening S M I hF C E Γ t T
    (judgmentChangeConstraint (alternateWF hd) he.1 he.2.2.2.2.1) hEC hd
  apply AlternateTyping.sub he hp
  intro ρ ι hρ hι hh
  have hm := (monoDenote S M ρ ι T _).mp (hi ρ ι hρ hι hh)
  exact (leHolds S M ρ ι 0 T U).mpr
    ⟨evalKind S M hF.1 ρ hρ T 0 (alternateWF hd).2.2.2.1.2.2,hm⟩

theorem alternateGeneralizedInstance (hF : Framework S M I) (xs : List TVar) (hn : xs.Nodup)
    (hk : ∀ X ∈ xs, X.1 ∈ S.kinds) (hd : AlternateTyping S M (.conj C D) Γ t T)
    (he : JudgmentWF S E Γ t (.mono U)) (hEC : Entails S M E C)
    (hf : Disjoint xs.toFinset (E.fv ∪ Γ.fv ∪ U.fv))
    (hi : ∀ ρ ι, ρ.Valid S M → ι.Valid M → E.Holds S M ρ ι →
      U.eval M ρ ∈ (Scheme.generalize xs D T).denote S M ρ ι) :
    AlternateTyping S M E Γ t U := by
  let K := Constraint.conj (.conj E D) (.le 0 T U)
  have hw := alternateWF hd
  have hT := hw.2.2.2.1.2.2
  have hU := he.2.2.2.1.2.2
  have hL : (Constraint.le 0 T U).WF S [] 0 := ⟨hF.1.1.1,.cons hT (.cons hU .nil)⟩
  have hDf : D.fpi = ∅ := (Finset.union_eq_empty.mp hw.2.2.2.2.1).2
  have hKw : K.WF S [] 0 := ⟨⟨he.1,hw.1.2⟩,hL⟩
  have hKf : K.fpi = ∅ := by simp [K,Constraint.fpi,Constraint.le,he.2.2.2.2.1,hDf]
  have hp := alternateWeakening S M I hF (.conj C D) K Γ t T
    (judgmentChangeConstraint hw hKw hKf) (fun ρ ι hρ hι hh => ⟨hEC ρ ι hρ hι hh.1.1,hh.1.2⟩) hd
  have hq := AlternateTyping.sub (judgmentChangeConstraint he hKw hKf) hp (fun _ _ _ _ hh => hh.2)
  have hyE : Disjoint xs.toFinset E.fv := hf.mono_right
    (fun X hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have hyU : Disjoint xs.toFinset U.fv := hf.mono_right Finset.subset_union_right
  have hyΓU : Disjoint xs.toFinset (Γ.fv ∪ U.fv) := by
    apply hf.mono_right
    intro X hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    · exact Finset.mem_union_right _ hx
  have hxw : JudgmentWF S (K.existsNames xs) Γ t (.mono U) :=
    judgmentChangeConstraint he (existsNamesWF S xs K 0 hk hKw) (by rw [existsNamesFpi,hKf])
  apply AlternateTyping.convert he (AlternateTyping.exists_ hxw hn hk hyΓU hq) ?_ (envBinderEqRefl _)
  constructor
  · intro ρ ι hρ hι hh
    obtain ⟨vs,hvs,hh⟩ := (existsNamesHolds S M ρ ι xs K hKw).mp hh
    exact (holdsAssignBlock S M hF.1 ρ ι xs vs E hρ hι hvs he.1 hyE).mp hh.1.1
  · intro ρ ι hρ hι hh
    obtain ⟨_,vs,hvs,hD,hTU⟩ := (generalizeDenote S M ρ ι xs D T hw.1.2 hT _).mp (hi ρ ι hρ hι hh)
    have hρ' := assignBlockValid S M ρ xs vs hρ hvs
    apply (existsNamesHolds S M ρ ι xs K hKw).mpr
    refine ⟨vs,hvs,⟨(holdsAssignBlock S M hF.1 ρ ι xs vs E hρ hι hvs he.1 hyE).mpr hh,hD⟩,?_⟩
    apply (leHolds S M _ ι 0 T U).mpr
    rw [tyEvalAssignBlock M ρ xs vs U (tyKindLC U S [] 0 hU) hyU]
    exact ⟨evalKind S M hF.1 _ hρ' T 0 hT,evalKind S M hF.1 ρ hρ U 0 hU,hTU⟩

theorem generalizeSelfMember (xs : List TVar)
    (hx : ∀ X ∈ xs, X.1 ∈ S.kinds) (D : Constraint) (T : Ty)
    (hD : D.WF S [] 0) (hT : T.HasKind S [] 0) (ρ : Assignment M) (ι : GroundEnv M)
    (hρ : ρ.Valid S M) (hd : D.Holds S M ρ ι) (v : M.Carrier)
    (hv : M.kind v = 0 ∧ M.below 0 (T.eval M ρ) v) :
    v ∈ (Scheme.generalize xs D T).denote S M ρ ι := by
  apply (generalizeDenote S M ρ ι xs D T hD hT v).mpr
  exact ⟨hv.1,xs.map ρ,assignmentBlockKinds S M ρ xs hρ hx,
    by simpa [assignBlockSelf] using hd,by simpa [assignBlockSelf] using hv.2⟩

theorem generalizeFpi (xs : List TVar) (D : Constraint) (T : Ty) :
    (Scheme.generalize xs D T).fpi = D.fpi := constraintMapTypesFpi _ D 0

/-- The generalized induction conclusion covers every semantic instance of the
result scheme. This makes conversion by binder permutations representation-independent. -/
theorem derivationInstanceBound (hF : Framework S M I) (n : Nat) :
    ∀ C Γ t s d, Derivation S M C Γ t s d → sizeOf d ≤ n →
      ∀ E U, JudgmentWF S E Γ t (.mono U) → Entails S M E C →
        (∀ ρ ι, ρ.Valid S M → ι.Valid M → E.Holds S M ρ ι → U.eval M ρ ∈ s.denote S M ρ ι) →
        AlternateTyping S M E Γ t U := by
  induction n using Nat.strong_induction_on with
  | h n outer =>
    intro C Γ t s d hd
    induction hd with
    | @var C Γ x s hw hl hr =>
        intro hb E U he hEC hi
        obtain ⟨xs,D,T,hn,hf,hk,hD,hT,hs⟩ := schemeFreshOpening s hw.2.2.2.1 (E.fv ∪ Γ.fv ∪ U.fv)
        have hDf : D.fpi = ∅ := by rw [← generalizeFpi xs D T,hs]; exact hw.2.2.2.2.2.2
        have hvt : JudgmentWF S (.conj E D) Γ (.ident (.free x)) (.mono T) :=
          ⟨⟨he.1,hD⟩,he.2.1,he.2.2.1,monoWF S T hT,
            by simp [Constraint.fpi,he.2.2.2.2.1,hDf],he.2.2.2.2.2.1,rfl⟩
        have hp := AlternateTyping.varInst (M := M) hvt hn (by rw [hs]; exact hl)
        exact alternateGeneralizedInstance hF xs hn hk hp he (fun _ _ _ _ hh => hh) hf
          (by simpa only [hs] using hi)
    | @abs C Γ t T U d L hw hd ih =>
        intro hb E V he hEC hi
        have hp : AlternateTyping S M C Γ (.lam t) (.arrow T U) := by
          apply AlternateTyping.abs L hw
          intro z hz
          exact ih z hz (by simp only [Shape.node.sizeOf_spec,List.cons.sizeOf_spec] at hb; omega)
            C U (derivationWF (hd z hz)) (fun _ _ _ _ hh => hh)
            (fun ρ ι hρ _ _ => monoSelfMember hF.1 U (derivationWF (hd z hz)).2.2.2.1.2.2 ρ ι hρ)
        exact alternateMonoInstance hF hp he hEC hi
    | @app C Γ t u U T d e hw ht hu iht ihu =>
        intro hb E V he hEC hi
        have hpt := iht (by simp only [Shape.node.sizeOf_spec,List.cons.sizeOf_spec] at hb; omega)
          C (.arrow T U) (derivationWF ht) (fun _ _ _ _ hh => hh)
          (fun ρ ι hρ _ _ => monoSelfMember hF.1 _ (derivationWF ht).2.2.2.1.2.2 ρ ι hρ)
        have hpu := ihu (by simp only [Shape.node.sizeOf_spec,List.cons.sizeOf_spec] at hb; omega)
          C T (derivationWF hu) (fun _ _ _ _ hh => hh)
          (fun ρ ι hρ _ _ => monoSelfMember hF.1 _ (derivationWF hu).2.2.2.1.2.2 ρ ι hρ)
        exact alternateMonoInstance hF (.app hw hpt hpu) he hEC hi
    | @letE C Γ t u T s d e L hw ht hu iht ihu =>
        intro hb E V he hEC hi
        have htw := derivationWF ht
        obtain ⟨xs,D,U,hn,hf,hk,hD,hU,hs⟩ := schemeFreshOpening s htw.2.2.2.1 (C.fv ∪ Γ.fv)
        have hDf : D.fpi = ∅ := by rw [← generalizeFpi xs D U,hs]; exact htw.2.2.2.2.2.2
        have hptw : JudgmentWF S (.conj C D) Γ t (.mono U) :=
          ⟨⟨htw.1,hD⟩,htw.2.1,htw.2.2.1,monoWF S U hU,
            by simp [Constraint.fpi,htw.2.2.2.2.1,hDf],htw.2.2.2.2.2.1,rfl⟩
        have hpt := iht (by simp only [Shape.node.sizeOf_spec,List.cons.sizeOf_spec] at hb; omega)
          (.conj C D) U hptw (fun _ _ _ _ hh => hh.1) (by
            intro ρ ι hρ hι hh
            rw [← hs]
            exact generalizeSelfMember xs hk D U hD hU ρ ι hρ hh.2 _
              ((monoDenote S M ρ ι U _).mp (monoSelfMember hF.1 U hU ρ ι hρ)))
        have hRwf : (Constraint.conj C (D.existsNames xs)).WF S [] 0 := ⟨htw.1,existsNamesWF S xs D 0 hk hD⟩
        have hRf : (Constraint.conj C (D.existsNames xs)).fpi = ∅ := by
          simp [Constraint.fpi,existsNamesFpi,htw.2.2.2.2.1,hDf]
        have hpu : ∀ z ∉ L, AlternateTyping S M (.conj C (D.existsNames xs))
            (Γ ++ [(.var z,Scheme.generalize xs D U)]) (Expr.openAt 0 (.ident (.free (.var z))) u) T := by
          intro z hz
          rw [hs]
          exact ihu z hz (by simp only [Shape.node.sizeOf_spec,List.cons.sizeOf_spec] at hb; omega)
            _ T (judgmentChangeConstraint (derivationWF (hu z hz)) hRwf hRf)
            (fun _ _ _ _ hh => hh.1)
            (fun ρ ι hρ _ _ => monoSelfMember hF.1 T (derivationWF (hu z hz)).2.2.2.1.2.2 ρ ι hρ)
        have hgen := AlternateTyping.letGen L (judgmentChangeConstraint hw hRwf hRf) hn hf hpt hpu
        have hr := derivationRealizable hF.1 ht
        rw [← hs] at hr
        have hbase : AlternateTyping S M C Γ (.letE t u) T :=
          .convert hw hgen ⟨fun _ _ _ _ hh => hh.1,fun ρ ι hρ hι hh => ⟨hh,hr ρ ι hρ hι hh⟩⟩ (envBinderEqRefl _)
        exact alternateMonoInstance hF hbase he hEC hi
    | @gen C Γ t xs D T d hw hn hf hd ih =>
        intro hb E U he hEC hi
        obtain ⟨ys,D',T',hyn,hyEU,hyCΓ,hD,hs,hd'⟩ := freshenGeneralization hF.1.1 (E.fv ∪ U.fv) xs hn hf hd
        have hw' := derivationWF hd'
        have hpt := outer (sizeOf d) (by simp only [Shape.node.sizeOf_spec,List.cons.sizeOf_spec] at hb; omega)
          _ _ _ _ _ hd' le_rfl _ T' hw' (fun _ _ _ _ hh => hh)
          (fun ρ ι hρ _ _ => monoSelfMember hF.1 T' hw'.2.2.2.1.2.2 ρ ι hρ)
        have hys := (generalizeWFReflect S ys D' T' (hs ▸ hw.2.2.2.1)).1
        apply alternateGeneralizedInstance hF ys hyn hys hpt he
          (fun ρ ι hρ hι hh => (hEC ρ ι hρ hι hh).1) ?_ (by simpa only [hs] using hi)
        apply Finset.disjoint_left.mpr
        intro X hx hX
        rcases Finset.mem_union.mp hX with hX | hX
        · rcases Finset.mem_union.mp hX with hX | hX
          · exact Finset.disjoint_left.mp hyEU hx (Finset.mem_union_left _ hX)
          · exact Finset.disjoint_left.mp hyCΓ hx (Finset.mem_union_right _ hX)
        · exact Finset.disjoint_left.mp hyEU hx (Finset.mem_union_right _ hX)
    | @inst C D Γ t T xs d hw hn hd ih =>
        intro hb E U he hEC hi
        have hs := generalizeWFReflect S xs D T (derivationWF hd).2.2.2.1
        apply ih (by simp only [Shape.node.sizeOf_spec,List.cons.sizeOf_spec] at hb; omega) E U he
          (fun ρ ι hρ hι hh => (hEC ρ ι hρ hι hh).1)
        intro ρ ι hρ hι hh
        exact generalizeSelfMember xs hs.1 D T hs.2.1 hs.2.2 ρ ι hρ
          (hEC ρ ι hρ hι hh).2 _ ((monoDenote S M ρ ι T _).mp (hi ρ ι hρ hι hh))
    | @sub C Γ t U T d hw hd hr ih =>
        intro hb E V he hEC hi
        have hpt := ih (by simp only [Shape.node.sizeOf_spec,List.cons.sizeOf_spec] at hb; omega)
          C T (derivationWF hd) (fun _ _ _ _ hh => hh)
          (fun ρ ι hρ _ _ => monoSelfMember hF.1 T (derivationWF hd).2.2.2.1.2.2 ρ ι hρ)
        exact alternateMonoInstance hF (.sub hw hpt hr) he hEC hi
    | @exists_ Γ t s xs C d hw hn hk hf hd ih =>
        intro hb E U he hEC hi
        obtain ⟨ys,D,hyn,hyEU,hyΓs,hD,hd'⟩ := freshenExistential hF.1.1 (E.fv ∪ U.fv) xs hn hf hd
        have hw' := derivationWF hd'
        have hDw : (D.existsNames ys).WF S [] 0 := hD ▸ hw.1
        have hyk := (existsNamesWFReflect S ys D hDw).1
        have hpw : JudgmentWF S (.conj E D) Γ t (.mono U) :=
          judgmentChangeConstraint he ⟨he.1,hw'.1⟩
            (by simp [Constraint.fpi,he.2.2.2.2.1,hw'.2.2.2.2.1])
        have hp := outer (sizeOf d) (by simp only [Shape.node.sizeOf_spec,List.cons.sizeOf_spec] at hb; omega)
          _ _ _ _ _ hd' le_rfl _ U hpw (fun _ _ _ _ hh => hh.2)
          (fun ρ ι hρ hι hh => hi ρ ι hρ hι hh.1)
        have hyE := hyEU.mono_right Finset.subset_union_left
        have hyΓU : Disjoint ys.toFinset (Γ.fv ∪ U.fv) := Finset.disjoint_union_right.mpr
          ⟨hyΓs.mono_right Finset.subset_union_left,hyEU.mono_right Finset.subset_union_right⟩
        have hqw := judgmentChangeConstraint he (existsNamesWF S ys (.conj E D) 0 hyk hpw.1)
          (by rw [existsNamesFpi]; exact hpw.2.2.2.2.1)
        apply AlternateTyping.convert he (AlternateTyping.exists_ hqw hyn hyk hyΓU hp) ?_ (envBinderEqRefl _)
        constructor
        · intro ρ ι hρ hι hh
          obtain ⟨vs,hvs,hh⟩ := (existsNamesHolds S M ρ ι ys (.conj E D) hpw.1).mp hh
          exact (holdsAssignBlock S M hF.1 ρ ι ys vs E hρ hι hvs he.1 hyE).mp hh.1
        · intro ρ ι hρ hι hh
          have hde : (D.existsNames ys).Holds S M ρ ι := by rw [hD]; exact hEC ρ ι hρ hι hh
          obtain ⟨vs,hvs,hhD⟩ := (existsNamesHolds S M ρ ι ys D hw'.1).mp hde
          exact (existsNamesHolds S M ρ ι ys (.conj E D) hpw.1).mpr
            ⟨vs,hvs,(holdsAssignBlock S M hF.1 ρ ι ys vs E hρ hι hvs he.1 hyE).mpr hh,hhD⟩
    | @convert D Δ t r C Γ s d hw hd hc hΓ hs ih =>
        intro hb E U he hEC hi
        have hw' := derivationWF hd
        have hew : JudgmentWF S E Γ t (.mono U) :=
          ⟨he.1,hw'.2.1,he.2.2.1,he.2.2.2.1,he.2.2.2.2.1,hw'.2.2.2.2.2.1,rfl⟩
        have hp := ih hb E U hew (fun ρ ι hρ hι hh => hc.2 ρ ι hρ hι (hEC ρ ι hρ hι hh)) (by
          intro ρ ι hρ hι hh
          have heq := schemeBinderEq S M ρ ι s r hs (fun _ => ρ (0,0)) (fun _ => ∅)
          change s.denote S M ρ ι = r.denote S M ρ ι at heq
          rw [heq]
          exact hi ρ ι hρ hι hh)
        exact .convert he hp ⟨fun _ _ _ _ hh => hh,fun _ _ _ _ hh => hh⟩ hΓ

theorem schemeElimination (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.schemeElimination S M I := by
  intro hF C Γ t xs D T hn hD hT ⟨d,hd⟩
  have hw := derivationWF hd
  have hDf : D.fpi = ∅ := (generalizeFpi xs D T).symm.trans hw.2.2.2.2.2.2
  have he : JudgmentWF S (.conj C D) Γ t (.mono T) :=
    ⟨⟨hw.1,hD⟩,hw.2.1,hw.2.2.1,monoWF S T hT,
      by simp [Constraint.fpi,hw.2.2.2.2.1,hDf],hw.2.2.2.2.2.1,rfl⟩
  apply derivationInstanceBound hF (sizeOf d) C Γ t _ d hd le_rfl _ T he (fun _ _ _ _ hh => hh.1)
  intro ρ ι hρ hι hh
  exact generalizeSelfMember xs (generalizeWFReflect S xs D T hw.2.2.2.1).1 D T hD hT ρ ι hρ hh.2 _
    ((monoDenote S M ρ ι T _).mp (monoSelfMember hF.1 T hT ρ ι hρ))

theorem alternateToTyping (hd : AlternateTyping S M C Γ t T) :
    Typing S M C Γ t (.mono T) := by
  induction hd with
  | @varInst C D Γ x T xs hw hn hl =>
      have hs := hw.2.1 _ (lookupMember Γ x _ hl)
      have hk := (generalizeWFReflect S xs D T hs).1
      have hDf := (Finset.union_eq_empty.mp hw.2.2.2.2.1).2
      have hvw : JudgmentWF S (.conj C D) Γ (.ident (.free x)) (Scheme.generalize xs D T) :=
        ⟨hw.1,hw.2.1,hw.2.2.1,hs,hw.2.2.2.2.1,hw.2.2.2.2.2.1,(generalizeFpi xs D T).trans hDf⟩
      have hv : Derivation S M (.conj C D) Γ (.ident (.free x)) (Scheme.generalize xs D T) (.node 0 []) :=
        .var hvw hl (fun ρ ι hρ hι hh => existsNamesIntro xs D hk hw.1.2 ρ ι hρ hι hh.2)
      have hiw : JudgmentWF S (.conj (.conj C D) D) Γ (.ident (.free x)) (.mono T) :=
        judgmentChangeConstraint hw ⟨hw.1,hw.1.2⟩ (by
          change (Constraint.conj C D).fpi ∪ D.fpi = ∅
          rw [hw.2.2.2.2.1,hDf,Finset.union_self])
      exact ⟨_,.convert hw (.inst hiw hn hv)
        ⟨fun _ _ _ _ hh => hh.1,fun _ _ _ _ hh => ⟨hh,hh.2⟩⟩ (envBinderEqRefl _) .refl⟩
  | @abs C Γ t T U L hw hd ih =>
      obtain ⟨d,L',hp⟩ := uniformOpening C Γ t (.mono T) (.mono U) L ih
      exact ⟨_,.abs L' hw hp⟩
  | app hw ht hu iht ihu =>
      obtain ⟨d,hpt⟩ := iht
      obtain ⟨e,hpu⟩ := ihu
      exact ⟨_,.app hw hpt hpu⟩
  | @letGen C Γ t u U D T xs L hw hn hf ht hu iht ihu =>
      obtain ⟨d,hpt⟩ := iht
      have htw := derivationWF hpt
      have hk := (existsNamesWFReflect S xs D hw.1.2).1
      have hDf := (Finset.union_eq_empty.mp htw.2.2.2.2.1).2
      have hgw : JudgmentWF S (.conj C (D.existsNames xs)) Γ t (Scheme.generalize xs D T) :=
        ⟨hw.1,htw.2.1,htw.2.2.1,generalizeWF S xs D T 0 hk htw.1.2 htw.2.2.2.1.2.2,
          hw.2.2.2.2.1,htw.2.2.2.2.2.1,(generalizeFpi xs D T).trans hDf⟩
      have hpg := Derivation.gen hgw hn hf hpt
      obtain ⟨e,L',hpu⟩ := uniformOpening (.conj C (D.existsNames xs)) Γ u (Scheme.generalize xs D T) (.mono U) L ihu
      exact ⟨_,.letE L' hw hpg hpu⟩
  | sub hw hd hr ih => obtain ⟨d,hp⟩ := ih; exact ⟨_,.sub hw hp hr⟩
  | exists_ hw hn hk hf hd ih =>
      obtain ⟨d,hp⟩ := ih
      exact ⟨_,.exists_ hw hn hk (by simpa [Scheme.mono,Scheme.fv,Constraint.fv] using hf) hp⟩
  | convert hw hd hc hΓ ih =>
      obtain ⟨d,hp⟩ := ih
      exact ⟨_,.convert hw hp hc hΓ .refl⟩

theorem theorem10_3_4 (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.theorem10_3_4 S M I := by
  intro hF C Γ t T
  constructor
  · exact alternateToTyping
  · intro ht
    have hw := derivationWF ht.choose_spec
    have hT := hw.2.2.2.1.2.2
    have heq : Scheme.generalize [] .truth T = Scheme.mono T := by
      simp only [Scheme.generalize,Scheme.mono,Constraint.closeTypes,Constraint.mapTypes,List.map_nil,
        tyCloseUnused T [] 0 (tyKindLC T S [] 0 hT) (by simp)]
    have hp := schemeElimination S M I hF C Γ t [] .truth T (by simp) trivial hT (by rw [heq]; exact ht)
    exact .convert hw hp (andTrueLaw S M C ⟨hw.1,trivial⟩ hw.1) (envBinderEqRefl _)

end HMX.LN.Proofs
