import EHMX.Proofs.Generation
import EHMX.Proofs.SchemeInstantiation

/-! 環境を付加した推論制約の整形式性と意味解釈。 -/
namespace EHMX

variable {S : Signature} {Δ : List Kind} {Γ : Env} {C : Constraint}

/-- Increasing the available term-variable depth preserves well-formedness. -/
theorem termDepthWF :
    (∀ C : Constraint, ∀ Δ n m, C.WF S Δ n → n ≤ m → C.WF S Δ m) ∧
    (∀ s : Scheme, ∀ Δ n m, s.WF S Δ n → n ≤ m → s.WF S Δ m) := by
  have hc : ∀ C : Constraint, ∀ Δ n m, C.WF S Δ n → n ≤ m → C.WF S Δ m := by
    apply Constraint.rec
      (motive_1 := fun C => ∀ Δ n m, C.WF S Δ n → n ≤ m → C.WF S Δ m)
      (motive_2 := fun s => ∀ Δ n m, s.WF S Δ n → n ≤ m → s.WF S Δ m)
    · intros; trivial
    · intros; trivial
    · intros; assumption
    · intro C D ihC ihD Δ n m h hnm
      exact ⟨ihC _ _ _ h.1 hnm, ihD _ _ _ h.2 hnm⟩
    · intro ks C ih Δ n m h hnm
      exact ⟨h.1, ih _ _ _ h.2 hnm⟩
    · intro ks C ih Δ n m h hnm
      exact ⟨h.1, ih _ _ _ h.2 hnm⟩
    · intro s C ihs ihC Δ n m h hnm
      exact ⟨ihs _ _ _ h.1 hnm, ihC _ _ _ h.2 (by omega)⟩
    · intro x s C ihs ihC Δ n m h hnm
      exact ⟨ihs _ _ _ h.1 hnm, ihC _ _ _ h.2 hnm⟩
    · intro x T Δ n m h hnm
      refine ⟨h.1, ?_⟩
      cases x with
      | free _ => trivial
      | bound i => exact Nat.lt_of_lt_of_le h.2 hnm
    · intro ks C T ih Δ n m h hnm
      exact ⟨h.1, ih _ _ _ h.2.1 hnm, h.2.2⟩
  refine ⟨hc, ?_⟩
  rintro ⟨ks, C, T⟩ Δ n m h hnm
  exact ⟨h.1, hc _ _ _ _ h.2.1 hnm, h.2.2⟩

theorem envLetInWF (hΓ : Γ.WF S Δ) (hC : C.WF S Δ Γ.bound.length) :
    (Γ.letIn C).WF S Δ 0 := by
  have hb : ∀ (ss : List Scheme) (D : Constraint) n,
      (∀ s ∈ ss, s.WF S Δ 0) → D.WF S Δ (ss.length + n) →
      (ss.foldl (fun E s => E.letBound s) D).WF S Δ n := by
    intro ss
    induction ss with
    | nil => intro D n _ h; simpa using h
    | cons s ss ih =>
        intro D n hs hD
        apply ih _ _ (fun t ht => hs t (by simp [ht]))
        have hsw := termDepthWF.2 s Δ 0 (ss.length + n) (hs s (by simp)) (Nat.zero_le _)
        cases s with
        | all ks E T =>
            exact ⟨⟨hsw.1, hsw.2.1⟩, hsw, by simpa [List.length_cons, Nat.add_assoc,
              Nat.add_comm, Nat.add_left_comm] using hD⟩
  have hf : ∀ (ps : List (Nat × Scheme)) (D : Constraint),
      (∀ p ∈ ps, p.2.WF S Δ 0) → D.WF S Δ 0 →
      (ps.foldr (fun p E => E.letFree p.1 p.2) D).WF S Δ 0 := by
    intro ps
    induction ps with
    | nil => intro D _ h; exact h
    | cons p ps ih =>
        intro D hs hD
        have hp := hs p (by simp)
        cases hpS : p.2 with
        | all ks E T =>
            rw [hpS] at hp
            change (Constraint.letFree p.1 p.2 _).WF S Δ 0
            rw [hpS]
            exact ⟨⟨hp.1, hp.2.1⟩, hp, ih D (fun q hq => hs q (by simp [hq])) hD⟩
  exact hf Γ.free _ (fun p hp => (hΓ.1 p hp).1)
    (hb Γ.bound C 0 (fun s hs => (hΓ.2 s hs).1) (by simpa using hC))

theorem envLetInFpi (hΓ : Γ.WF S Δ) : (Γ.letIn C).fpi = C.fpi \ Γ.dpi := by
  have hb : ∀ (ss : List Scheme) (D : Constraint),
      (∀ s ∈ ss, s.fpi = ∅) →
      (ss.foldl (fun E s => E.letBound s) D).fpi = D.fpi := by
    intro ss
    induction ss with
    | nil => intros; rfl
    | cons s ss ih =>
        intro D hs
        rw [List.foldl_cons, ih _ (fun t ht => hs t (by simp [ht]))]
        cases s with
        | all ks E T =>
            have h := hs (.all ks E T) (by simp)
            simp only [Scheme.fpi] at h
            simp [Constraint.letBound, Constraint.fpi, Scheme.exists_, Scheme.fpi, h]
  have hf : ∀ (ps : List (Nat × Scheme)) (D : Constraint),
      (∀ p ∈ ps, p.2.fpi = ∅) →
      (ps.foldr (fun p E => E.letFree p.1 p.2) D).fpi =
        D.fpi \ (ps.map Prod.fst).toFinset := by
    intro ps
    induction ps with
    | nil => intros; simp
    | cons p ps ih =>
        intro D hs
        have hp := hs p (by simp)
        cases hpS : p.2 with
        | all ks E T =>
            rw [hpS] at hp
            simp only [Scheme.fpi] at hp
            rw [List.foldr_cons]
            conv_lhs => rw [hpS]
            change E.fpi ∪ (E.fpi ∪ (ps.foldr (fun p E => E.letFree p.1 p.2) D).fpi.erase p.1) = _
            rw [hp, Finset.empty_union, Finset.empty_union,
              ih _ (fun q hq => hs q (by simp [hq]))]
            ext x
            simp only [List.map_cons, List.toFinset_cons, Finset.mem_erase,
              Finset.mem_sdiff, Finset.mem_insert]
            aesop
  exact (hf Γ.free _ (fun p hp => (hΓ.1 p hp).2)).trans
    (by rw [hb Γ.bound C (fun s hs => (hΓ.2 s hs).2)]; rfl)

theorem inferWF (hS : S.WF) (hsig : OpSignature.WF S sig)
    (hΓ : Γ.WF S Δ) (he : e.Scoped Γ)
    (hT : T.HasKind S Δ 0) (hε : ε.HasKind S Δ 1) :
    (infer sig Γ e T ε).WF S Δ 0 :=
  envLetInWF hΓ (generationWF hS hsig he.1 hT hε)

theorem inferScope (hΓ : Γ.WF S Δ) (he : e.Scoped Γ) (hd : e.Declared sig) :
    (infer sig Γ e T ε).fpi = ∅ := by
  rw [infer, envLetInFpi hΓ, generationScope hd]
  exact Finset.sdiff_eq_empty_iff_subset.mpr he.2

theorem inferJudgmentWF (hS : S.WF) (hsig : OpSignature.WF S sig)
    (hΓ : Γ.WF S Δ) (he : e.Scoped Γ) (hd : e.Declared sig)
    (hT : T.HasKind S Δ 0) (hε : ε.HasKind S Δ 1) :
    JudgmentWF S Δ (infer sig Γ e T ε) Γ e T ε :=
  ⟨inferWF hS hsig hΓ he hT hε, inferScope hΓ he hd, hΓ, he, hT, hε⟩

/-- Interpret free bindings from left to right and bound bindings from the outside
inwards. This is the same order as `Env.letIn`. -/
def Env.interpret (Γ : Env) (M : Model) (ρ : Assignment M)
    (bs : List M.Carrier) (ι : GroundEnv M) : GroundEnv M :=
  Γ.bound.foldr (fun s κ => κ.push (s.denote M ρ bs κ))
    (Γ.free.foldl (fun κ p => κ.bind p.1 (p.2.denote M ρ bs κ)) ι)

/-- Environment wrapping asserts feasibility as well as interpreting its body. -/
theorem envLetInHolds (Γ : Env) (D : Constraint) (ρ : Assignment M)
    (bs : List M.Carrier) (ι : GroundEnv M) :
    (Γ.letIn D).Holds M ρ bs ι ↔
      Γ.exists_.Holds M ρ bs ι ∧ D.Holds M ρ bs (Γ.interpret M ρ bs ι) := by
  have hb : ∀ (ss : List Scheme) (D : Constraint) (ι : GroundEnv M),
      (ss.foldl (fun E s => E.letBound s) D).Holds M ρ bs ι ↔
      (ss.foldl (fun E s => E.letBound s) Constraint.truth).Holds M ρ bs ι ∧
      D.Holds M ρ bs (ss.foldr (fun s κ => κ.push (s.denote M ρ bs κ)) ι) := by
    intro ss
    induction ss using List.reverseRecOn with
    | nil => intros; simp [Constraint.Holds]
    | append_singleton ss s ih =>
        intro D ι
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldr_append, List.foldr_cons, List.foldr_nil]
        change (s.exists_.Holds M ρ bs ι ∧ _) ↔
          (s.exists_.Holds M ρ bs ι ∧ _) ∧ _
        simp only [Constraint.Holds]
        rw [ih D]
        exact and_assoc.symm
  have hf : ∀ (ps : List (Nat × Scheme)) (A E : Constraint) (ι : GroundEnv M),
      (∀ κ, A.Holds M ρ bs κ ↔ E.Holds M ρ bs κ ∧
        D.Holds M ρ bs (Γ.bound.foldr (fun s κ => κ.push (s.denote M ρ bs κ)) κ)) →
      ((ps.foldr (fun p F => F.letFree p.1 p.2) A).Holds M ρ bs ι ↔
      (ps.foldr (fun p F => F.letFree p.1 p.2) E).Holds M ρ bs ι ∧
      D.Holds M ρ bs (Γ.bound.foldr (fun s κ => κ.push (s.denote M ρ bs κ))
        (ps.foldl (fun κ p => κ.bind p.1 (p.2.denote M ρ bs κ)) ι))) := by
    intro ps
    induction ps with
    | nil => intro D E ι h; exact h ι
    | cons p ps ih =>
        intro D E ι h
        change (p.2.exists_.Holds M ρ bs ι ∧ _) ↔
          (p.2.exists_.Holds M ρ bs ι ∧ _) ∧ _
        simp only [Constraint.Holds]
        rw [ih D E _ h]
        exact and_assoc.symm
  exact hf Γ.free _ _ ι (hb Γ.bound D)

/-- Agreement only on variables that a well-formed constraint can inspect. -/
def GroundEnv.Agrees (n : Nat) (xs : Finset Nat) (ι κ : GroundEnv M) : Prop :=
  (∀ x ∈ xs, ι.free x = κ.free x) ∧
  ∀ i, i < n → ι.lookup (.bound i) = κ.lookup (.bound i)

theorem groundAgreement :
    (∀ (D : Constraint) Δ n, D.WF S Δ n → ∀ (ρ : Assignment M) bs ι κ,
      GroundEnv.Agrees n D.fpi ι κ → (D.Holds M ρ bs ι ↔ D.Holds M ρ bs κ)) ∧
    (∀ (s : Scheme) Δ n, s.WF S Δ n → ∀ (ρ : Assignment M) bs ι κ,
      GroundEnv.Agrees n s.fpi ι κ → s.denote M ρ bs ι = s.denote M ρ bs κ) := by
  have hc : ∀ (D : Constraint) Δ n, D.WF S Δ n → ∀ (ρ : Assignment M) bs ι κ,
      GroundEnv.Agrees n D.fpi ι κ → (D.Holds M ρ bs ι ↔ D.Holds M ρ bs κ) := by
    apply Constraint.rec
      (motive_1 := fun D => ∀ Δ n, D.WF S Δ n → ∀ (ρ : Assignment M) bs ι κ,
        GroundEnv.Agrees n D.fpi ι κ → (D.Holds M ρ bs ι ↔ D.Holds M ρ bs κ))
      (motive_2 := fun s => ∀ Δ n, s.WF S Δ n → ∀ (ρ : Assignment M) bs ι κ,
        GroundEnv.Agrees n s.fpi ι κ → s.denote M ρ bs ι = s.denote M ρ bs κ)
    · intros; rfl
    · intros; rfl
    · intros; rfl
    · intro D E ihD ihE Δ n hw ρ bs ι κ ha
      exact and_congr
        (ihD _ _ hw.1 _ _ _ _ ⟨fun x hx => ha.1 x (Finset.mem_union_left _ hx), ha.2⟩)
        (ihE _ _ hw.2 _ _ _ _ ⟨fun x hx => ha.1 x (Finset.mem_union_right _ hx), ha.2⟩)
    · intro ks D ih Δ n hw ρ bs ι κ ha
      exact exists_congr (fun vs => and_congr_right (fun _ => ih _ _ hw.2 _ _ _ _ ha))
    · intro ks D ih Δ n hw ρ bs ι κ ha
      exact forall_congr' (fun vs => imp_congr_right (fun _ => ih _ _ hw.2 _ _ _ _ ha))
    · intro s D ihs ihD Δ n hw ρ bs ι κ ha
      have hs := ihs _ _ hw.1 ρ bs ι κ
        ⟨fun x hx => ha.1 x (Finset.mem_union_left _ hx), ha.2⟩
      change D.Holds M ρ bs (ι.push _) ↔ D.Holds M ρ bs (κ.push _)
      rw [hs]
      apply ihD _ _ hw.2
      refine ⟨fun x hx => ha.1 x (Finset.mem_union_right _ hx), ?_⟩
      intro i hi
      cases i with
      | zero => rfl
      | succ i => exact ha.2 i (by omega)
    · intro x s D ihs ihD Δ n hw ρ bs ι κ ha
      have hs := ihs _ _ hw.1 ρ bs ι κ
        ⟨fun y hy => ha.1 y (Finset.mem_union_left _ hy), ha.2⟩
      change D.Holds M ρ bs (ι.bind x _) ↔ D.Holds M ρ bs (κ.bind x _)
      rw [hs]
      apply ihD _ _ hw.2
      refine ⟨?_, ha.2⟩
      intro y hy
      by_cases h : y = x
      · simp [GroundEnv.bind, h]
      · simp only [GroundEnv.bind, h, ↓reduceIte]
        exact ha.1 y (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨h, hy⟩))
    · intro x T Δ n hw ρ bs ι κ ha
      change T.eval M ρ bs ∈ ι.lookup x ↔ T.eval M ρ bs ∈ κ.lookup x
      cases x with
      | free x => rw [show ι.lookup (.free x) = κ.lookup (.free x) from ha.1 x (by simp [Constraint.fpi])]
      | bound i => rw [ha.2 i hw.2]
    · intro ks D T ih Δ n hw ρ bs ι κ ha
      ext v
      change (_ ∧ ∃ vs, KindValues M ks vs ∧ _ ∧ _) ↔
        (_ ∧ ∃ vs, KindValues M ks vs ∧ _ ∧ _)
      apply and_congr_right; intro _
      apply exists_congr; intro vs
      exact and_congr_right (fun _ => and_congr (ih _ _ hw.2.1 _ _ _ _ ha) Iff.rfl)
  refine ⟨hc, ?_⟩
  rintro ⟨ks, D, T⟩ Δ n hw ρ bs ι κ ha
  ext v
  change (_ ∧ ∃ vs, KindValues M ks vs ∧ _ ∧ _) ↔
    (_ ∧ ∃ vs, KindValues M ks vs ∧ _ ∧ _)
  apply and_congr_right; intro _
  apply exists_congr; intro vs
  exact and_congr_right (fun _ => and_congr (hc _ _ _ hw.2.1 _ _ _ _ ha) Iff.rfl)

theorem constraintGroundIndependent (hD : Constraint.WF S Δ 0 D) (hf : D.fpi = ∅)
    (ρ : Assignment M) (bs : List M.Carrier) (ι κ : GroundEnv M) :
    D.Holds M ρ bs ι ↔ D.Holds M ρ bs κ :=
  groundAgreement.1 D _ _ hD ρ bs ι κ ⟨by simp [hf], by simp⟩

theorem schemeGroundIndependent (hs : Scheme.WF S Δ 0 s) (hf : s.fpi = ∅)
    (ρ : Assignment M) (bs : List M.Carrier) (ι κ : GroundEnv M) :
    s.denote M ρ bs ι = s.denote M ρ bs κ :=
  groundAgreement.2 s _ _ hs ρ bs ι κ ⟨by simp [hf], by simp⟩


theorem GroundEnv.validPush {ι : GroundEnv M} (hι : GroundEnv.Valid ι) (hs : UpperSet M s) :
    GroundEnv.Valid (ι.push s) :=
  ⟨hι.1, fun t ht => (List.mem_cons.mp ht).elim (fun h => h ▸ hs) (hι.2 t)⟩

theorem GroundEnv.validBind {ι : GroundEnv M} (hι : GroundEnv.Valid ι) (hs : UpperSet M s) :
    GroundEnv.Valid (ι.bind x s) := by
  refine ⟨?_, hι.2⟩
  intro y
  by_cases h : y = x <;> simp only [GroundEnv.bind, h, ↓reduceIte]
  · exact hs
  · exact hι.1 y

theorem envInterpretValid (hF : EffectFramework S M) (hΓ : Env.WF S Δ Γ)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs) (hι : GroundEnv.Valid ι) :
    GroundEnv.Valid (Γ.interpret M ρ bs ι) := by
  have hf : ∀ (ps : List (Nat × Scheme)) (κ : GroundEnv M),
      (∀ p ∈ ps, p.2.WF S Δ 0) → κ.Valid →
      (ps.foldl (fun κ p => κ.bind p.1 (p.2.denote M ρ bs κ)) κ).Valid := by
    intro ps
    induction ps with
    | nil => intros; assumption
    | cons p ps ih =>
        intro κ hw hκ
        exact ih _ (fun q hq => hw q (by simp [hq]))
          (GroundEnv.validBind hκ (schemeUpperSet hF p.2 (hw p (by simp)) hρ hbs))
  have hb : ∀ (ss : List Scheme) (κ : GroundEnv M),
      (∀ s ∈ ss, s.WF S Δ 0) → κ.Valid →
      (ss.foldr (fun s κ => κ.push (s.denote M ρ bs κ)) κ).Valid := by
    intro ss
    induction ss with
    | nil => intros; assumption
    | cons s ss ih =>
        intro κ hw hκ
        exact GroundEnv.validPush (ih κ (fun t ht => hw t (by simp [ht])) hκ)
          (schemeUpperSet hF s (hw s (by simp)) hρ hbs)
  exact hb _ _ (fun s hs => (hΓ.2 s hs).1)
    (hf _ _ (fun p hp => (hΓ.1 p hp).1) hι)

theorem envLetInConjunction (Γ : Env) (D E : Constraint) :
    Equivalent S M Δ (Γ.letIn (.conj D E)) (.conj (Γ.letIn D) (Γ.letIn E)) := by
  constructor <;> intro ρ bs ι _ _ _ h
  · rcases (envLetInHolds Γ _ ρ bs ι).mp h with ⟨hr, hD, hE⟩
    exact ⟨(envLetInHolds Γ D ρ bs ι).mpr ⟨hr, hD⟩,
      (envLetInHolds Γ E ρ bs ι).mpr ⟨hr, hE⟩⟩
  · rcases (envLetInHolds Γ D ρ bs ι).mp h.1 with ⟨hr, hD⟩
    exact (envLetInHolds Γ _ ρ bs ι).mpr
      ⟨hr, hD, ((envLetInHolds Γ E ρ bs ι).mp h.2).2⟩

theorem envLetInIndependent (hD : Constraint.WF S Δ 0 D) (hf : D.fpi = ∅) :
    Equivalent S M Δ (Γ.letIn D) (.conj Γ.exists_ D) := by
  constructor <;> intro ρ bs ι _ _ _ h
  · rcases (envLetInHolds Γ D ρ bs ι).mp h with ⟨hr, hD'⟩
    exact ⟨hr, (constraintGroundIndependent hD hf ρ bs _ ι).mp hD'⟩
  · exact (envLetInHolds Γ D ρ bs ι).mpr
      ⟨h.1, (constraintGroundIndependent hD hf ρ bs ι _).mp h.2⟩

theorem envInterpretPush (hs : Scheme.WF S Δ 0 s)
    (hf : s.fpi = ∅) (ρ : Assignment M) (bs : List M.Carrier) (ι : GroundEnv M) :
    (Γ.push s).interpret M ρ bs ι =
      (Γ.interpret M ρ bs ι).push (s.denote M ρ bs ι) := by
  change (Γ.interpret M ρ bs ι).push (s.denote M ρ bs (Γ.interpret M ρ bs ι)) = _
  rw [schemeGroundIndependent hs hf ρ bs _ ι]

/-- Feasibility of the new scheme is checked in the original valuation. -/
theorem envPushExists (hs : Scheme.WF S Δ 0 s) (hf : s.fpi = ∅)
    (ρ : Assignment M) (bs : List M.Carrier) (ι : GroundEnv M) :
    (Γ.push s).exists_.Holds M ρ bs ι ↔
      Γ.exists_.Holds M ρ bs ι ∧ s.exists_.Holds M ρ bs ι := by
  have he : (Γ.push s).exists_ = Γ.letIn (s.exists_.conj (.def_ s .truth)) := rfl
  rw [he, envLetInHolds]
  simp only [Constraint.Holds, and_true]
  cases s with
  | all ks D T =>
      exact and_congr_right (fun _ => constraintGroundIndependent
        (show (Constraint.exists_ ks D).WF S Δ 0 from ⟨hs.1, hs.2.1⟩)
        hf ρ bs _ ι)


/-- Reading an interpreted environment agrees with its syntactic lookup,
including rightmost free-variable shadowing and nearest-first bound indices. -/
theorem envInterpretLookup (hΓ : Env.WF S Δ Γ) (hl : Γ.lookup x = some s)
    (ρ : Assignment M) (bs : List M.Carrier) (ι : GroundEnv M) :
    (Γ.interpret M ρ bs ι).lookup x = s.denote M ρ bs ι := by
  have hb : ∀ (ss : List Scheme) (κ : GroundEnv M),
      (∀ s ∈ ss, s.WF S Δ 0 ∧ s.fpi = ∅) →
      (ss.foldr (fun s κ => κ.push (s.denote M ρ bs κ)) κ).free = κ.free ∧
      (ss.foldr (fun s κ => κ.push (s.denote M ρ bs κ)) κ).bound =
        ss.map (fun s => s.denote M ρ bs ι) ++ κ.bound := by
    intro ss
    induction ss with
    | nil => intro κ _; exact ⟨rfl, rfl⟩
    | cons s ss ih =>
        intro κ hw
        have hh := ih κ (fun t ht => hw t (by simp [ht]))
        refine ⟨hh.1, ?_⟩
        change s.denote M ρ bs _ ::
          (ss.foldr (fun s κ => κ.push (s.denote M ρ bs κ)) κ).bound =
          s.denote M ρ bs ι :: _
        rw [hh.2, schemeGroundIndependent (hw s (by simp)).1 (hw s (by simp)).2 ρ bs _ ι]
        rfl
  have hf : ∀ (ps : List (Nat × Scheme)) (κ : GroundEnv M) x,
      (∀ p ∈ ps, p.2.WF S Δ 0 ∧ p.2.fpi = ∅) →
      (ps.foldl (fun κ p => κ.bind p.1 (p.2.denote M ρ bs κ)) κ).free x =
        ((ps.reverse.find? (fun p => p.1 == x)).map
          (fun p => p.2.denote M ρ bs ι)).getD (κ.free x) := by
    intro ps
    induction ps using List.reverseRecOn with
    | nil => intros; rfl
    | append_singleton ps p ih =>
        intro κ x hw
        have hp := hw p (by simp)
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil,
          GroundEnv.bind, List.reverse_append, List.reverse_cons, List.reverse_nil,
          List.nil_append, List.cons_append, List.find?_cons]
        rw [schemeGroundIndependent hp.1 hp.2 ρ bs _ ι]
        by_cases h : x = p.1
        · simp [h]
        · have h' : p.1 ≠ x := Ne.symm h
          simpa only [h, beq_eq_false_iff_ne.mpr h', ↓reduceIte, GroundEnv.bind] using
            ih κ x (fun q hq => hw q (by simp [hq]))
  cases x with
  | free x =>
      change (Γ.interpret M ρ bs ι).free x = _
      unfold Env.interpret
      rw [(hb Γ.bound _ hΓ.2).1, hf Γ.free _ x hΓ.1]
      obtain ⟨p, hp, hps⟩ := Option.map_eq_some_iff.mp hl
      simp only [hp, Option.map_some, Option.getD_some, hps]
  | bound i =>
      change Γ.bound[i]? = some s at hl
      change ((Γ.interpret M ρ bs ι).bound[i]?).getD ∅ = _
      unfold Env.interpret
      rw [(hb Γ.bound _ hΓ.2).2]
      have hi : i < Γ.bound.length := (List.getElem?_eq_some_iff.mp hl).1
      simp only [List.getElem?_append, List.length_map, hi, ↓reduceIte,
        List.getElem?_map, hl, Option.map_some, Option.getD_some]

/-- Membership in a scheme equals satisfaction of its instance constraint. -/
theorem instanceConstraintHolds (hF : EffectFramework S M)
    (hs : Scheme.WF S Δ n s) (hT : Ty.HasKind S Δ T 0)
    (hρ : Assignment.Valid S M ρ) (hbs : KindValues M Δ bs) (ι : GroundEnv M) :
    (s.instanceConstraint T).Holds M ρ bs ι ↔ T.eval M ρ bs ∈ s.denote M ρ bs ι := by
  cases s with
  | all ks D A =>
      change (∃ vs, KindValues M ks vs ∧ D.Holds M ρ (vs ++ bs) ι ∧
        (Constraint.le 0 A (T.shift ks.length 0)).Holds M ρ (vs ++ bs) ι) ↔ _
      constructor
      · rintro ⟨vs, hv, hD, hle⟩
        have hn := hv.length_eq
        refine ⟨evalKind hF hρ hbs hT, vs, hv, hD, ?_⟩
        simpa only [← hn, evalShift] using hle.2.2
      · rintro ⟨_, vs, hv, hD, hle⟩
        refine ⟨vs, hv, hD, evalKind hF hρ (List.rel_append hv hbs) hs.2.2, ?_, ?_⟩
        · exact evalKind hF hρ (List.rel_append hv hbs) (kindShift hT ks)
        · simpa only [← hv.length_eq, evalShift] using hle


/-- Environment wrapping commutes with type/effect substitution. -/
theorem envLetInSubstitution (Γ : Env) (D : Constraint) (σ : BoundSubst) :
    (Γ.letIn D).substBound σ = (Γ.substBound σ).letIn (D.substBound σ) := by
  have hb : ∀ (ss : List Scheme) (D : Constraint),
      (ss.foldl (fun E s => E.letBound s) D).substBound σ =
      (ss.map (Scheme.substBound σ)).foldl (fun E s => E.letBound s) (D.substBound σ) := by
    intro ss
    induction ss with
    | nil => intros; rfl
    | cons s ss ih =>
        intro D
        simp only [List.foldl_cons, List.map_cons]
        rw [ih]
        cases s
        rfl
  have hf : ∀ (ps : List (Nat × Scheme)) (D : Constraint),
      (ps.foldr (fun p E => E.letFree p.1 p.2) D).substBound σ =
      (ps.map (fun p => (p.1, p.2.substBound σ))).foldr
        (fun p E => E.letFree p.1 p.2) (D.substBound σ) := by
    intro ps
    induction ps with
    | nil => intros; rfl
    | cons p ps ih =>
        intro D
        cases p with
        | mk x s =>
          cases s
          simp only [List.foldr_cons, List.map_cons, Constraint.letFree,
            Scheme.exists_, Constraint.substBound, Scheme.substBound]
          congr 2
          exact ih D
  unfold Env.letIn Env.substBound
  rw [hf, hb]

/-- Shifting the context shifts every scheme but leaves term-variable order intact. -/
theorem envLetInShift (Γ : Env) (D : Constraint) (n : Nat) :
    (Γ.letIn D).shift n 0 = (Γ.shift n).letIn (D.shift n 0) := by
  simp only [shiftSubstBound.1, shiftSubstBound.2, Env.shift,
    envLetInSubstitution, Env.substBound]
  have hs : Scheme.shift n 0 = fun s => s.substBound
      (fun i => .bound (if i < 0 then i else i + n)) := by
    funext s
    exact shiftSubstBound.2 s n 0
  rw [hs]

theorem envShiftWF (hΓ : Env.WF S Δ Γ) (ks : List Kind) :
    Env.WF S (ks ++ Δ) (Γ.shift ks.length) := by
  constructor
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨schemeShiftWF (hΓ.1 q hq).1 ks,
      (schemeShiftFpi _ _ _).trans (hΓ.1 q hq).2⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact ⟨schemeShiftWF (hΓ.2 t ht).1 ks,
      (schemeShiftFpi _ _ _).trans (hΓ.2 t ht).2⟩

theorem schemeShiftDenote (hs : Scheme.WF S Δ n s)
    (ρ : Assignment M) (bs vs : List M.Carrier) (ι : GroundEnv M) :
    (s.shift vs.length 0).denote M ρ (vs ++ bs) ι = s.denote M ρ bs ι := by
  rw [shiftSubstBound.2]
  apply (substBoundSemantics M).2 s _ _ hs
  intro i k hi
  have hn : ¬ i + vs.length < vs.length := by omega
  simp [Ty.eval, List.getElem?_append, hn]

theorem envInterpretShift (hΓ : Env.WF S Δ Γ)
    (ρ : Assignment M) (bs vs : List M.Carrier) (ι : GroundEnv M) :
    (Γ.shift vs.length).interpret M ρ (vs ++ bs) ι = Γ.interpret M ρ bs ι := by
  have hf : ∀ (ps : List (Nat × Scheme)) (κ : GroundEnv M),
      (∀ p ∈ ps, p.2.WF S Δ 0) →
      ((ps.map (fun p => (p.1, p.2.shift vs.length 0))).foldl
        (fun κ p => κ.bind p.1 (p.2.denote M ρ (vs ++ bs) κ)) κ) =
      ps.foldl (fun κ p => κ.bind p.1 (p.2.denote M ρ bs κ)) κ := by
    intro ps
    induction ps with
    | nil => intros; rfl
    | cons p ps ih =>
        intro κ hw
        simp only [List.map_cons, List.foldl_cons]
        rw [schemeShiftDenote (hw p (by simp))]
        exact ih _ (fun q hq => hw q (by simp [hq]))
  have hb : ∀ (ss : List Scheme) (κ : GroundEnv M),
      (∀ s ∈ ss, s.WF S Δ 0) →
      ((ss.map (Scheme.shift vs.length 0)).foldr
        (fun s κ => κ.push (s.denote M ρ (vs ++ bs) κ)) κ) =
      ss.foldr (fun s κ => κ.push (s.denote M ρ bs κ)) κ := by
    intro ss
    induction ss with
    | nil => intros; rfl
    | cons s ss ih =>
        intro κ hw
        simp only [List.map_cons, List.foldr_cons]
        rw [ih _ (fun t ht => hw t (by simp [ht])), schemeShiftDenote (hw s (by simp))]
  unfold Env.shift Env.interpret
  rw [hf _ _ (fun p hp => (hΓ.1 p hp).1), hb _ _ (fun s hs => (hΓ.2 s hs).1)]

theorem envExistsShift (hΓ : Env.WF S Δ Γ)
    (ρ : Assignment M) (bs vs : List M.Carrier) (ι : GroundEnv M) :
    (Γ.shift vs.length).exists_.Holds M ρ (vs ++ bs) ι ↔ Γ.exists_.Holds M ρ bs ι := by
  change ((Γ.shift vs.length).letIn (Constraint.truth.shift vs.length 0)).Holds _ _ _ _ ↔ _
  rw [← envLetInShift]
  exact constraintShiftHolds (envLetInWF (C := .truth) hΓ trivial) ρ bs vs ι

/-- Existential witnesses stay in their type/effect scope when the environment
is moved beneath the quantifier. -/
theorem envLetInExists (hΓ : Env.WF S Δ Γ) (ks : List Kind)
    (D : Constraint) (ρ : Assignment M) (bs : List M.Carrier) (ι : GroundEnv M) :
    (Γ.letIn (.exists_ ks D)).Holds M ρ bs ι ↔
      (Constraint.exists_ ks ((Γ.shift ks.length).letIn D)).Holds M ρ bs ι := by
  rw [envLetInHolds]
  change (_ ∧ ∃ vs, KindValues M ks vs ∧ _) ↔ ∃ vs, KindValues M ks vs ∧ _
  constructor
  · rintro ⟨hΓe, vs, hv, hD⟩
    refine ⟨vs, hv, (envLetInHolds _ _ _ _ _).mpr ⟨?_, ?_⟩⟩
    · simpa only [← hv.length_eq] using (envExistsShift hΓ ρ bs vs ι).mpr hΓe
    · simpa only [← hv.length_eq, envInterpretShift hΓ] using hD
  · rintro ⟨vs, hv, h⟩
    obtain ⟨hΓe, hD⟩ := (envLetInHolds _ _ _ _ _).mp h
    refine ⟨?_, vs, hv, ?_⟩
    · apply (envExistsShift hΓ ρ bs vs ι).mp
      simpa only [hv.length_eq] using hΓe
    · simpa only [← hv.length_eq, envInterpretShift hΓ] using hD

/-- Universal clauses require the outer environment to be feasible separately;
there may be no semantic values of the quantified kinds. -/
theorem envLetInForall (hΓ : Env.WF S Δ Γ) (ks : List Kind)
    (D : Constraint) (ρ : Assignment M) (bs : List M.Carrier) (ι : GroundEnv M) :
    (Γ.letIn (.forall_ ks D)).Holds M ρ bs ι ↔
      Γ.exists_.Holds M ρ bs ι ∧
      (Constraint.forall_ ks ((Γ.shift ks.length).letIn D)).Holds M ρ bs ι := by
  rw [envLetInHolds]
  apply and_congr_right
  intro hΓe
  constructor
  · intro h vs hv
    apply (envLetInHolds _ _ _ _ _).mpr
    refine ⟨?_, ?_⟩
    · simpa only [← hv.length_eq] using (envExistsShift hΓ ρ bs vs ι).mpr hΓe
    · simpa only [← hv.length_eq, envInterpretShift hΓ] using h vs hv
  · intro h vs hv
    have hD := ((envLetInHolds _ _ _ _ _).mp (h vs hv)).2
    simpa only [← hv.length_eq, envInterpretShift hΓ] using hD


/-- All constraint forms are positive in the ground environment, including
universal handler clauses and schemes nested inside definitions. -/
def GroundEnv.Included (ι κ : GroundEnv M) : Prop :=
  ∀ x, ι.lookup x ⊆ κ.lookup x

theorem groundMonotonicity (M : Model) :
    (∀ (D : Constraint) (ρ : Assignment M) bs ι κ,
      GroundEnv.Included ι κ → D.Holds M ρ bs ι → D.Holds M ρ bs κ) ∧
    (∀ (s : Scheme) (ρ : Assignment M) bs ι κ,
      GroundEnv.Included ι κ → s.denote M ρ bs ι ⊆ s.denote M ρ bs κ) := by
  have hc : ∀ (D : Constraint) (ρ : Assignment M) bs ι κ,
      GroundEnv.Included ι κ → D.Holds M ρ bs ι → D.Holds M ρ bs κ := by
    apply Constraint.rec
      (motive_1 := fun D => ∀ (ρ : Assignment M) bs ι κ,
        GroundEnv.Included ι κ → D.Holds M ρ bs ι → D.Holds M ρ bs κ)
      (motive_2 := fun s => ∀ (ρ : Assignment M) bs ι κ,
        GroundEnv.Included ι κ → s.denote M ρ bs ι ⊆ s.denote M ρ bs κ)
    · intros; trivial
    · intros; contradiction
    · intros; assumption
    · intro D E ihD ihE ρ bs ι κ hi h
      exact ⟨ihD _ _ _ _ hi h.1, ihE _ _ _ _ hi h.2⟩
    · intro ks D ih ρ bs ι κ hi h
      obtain ⟨vs, hv, hD⟩ := h
      exact ⟨vs, hv, ih _ _ _ _ hi hD⟩
    · intro ks D ih ρ bs ι κ hi h
      exact fun vs hv => ih _ _ _ _ hi (h vs hv)
    · intro s D ihs ihD ρ bs ι κ hi h
      apply ihD _ _ _ _ _ h
      intro x
      cases x with
      | free x => exact hi (.free x)
      | bound i =>
        cases i with
        | zero => exact ihs _ _ _ _ hi
        | succ i => exact hi (.bound i)
    · intro x s D ihs ihD ρ bs ι κ hi h
      apply ihD _ _ _ _ _ h
      intro y
      cases y with
      | bound i => exact hi (.bound i)
      | free y =>
          by_cases hy : y = x
          · simpa [GroundEnv.lookup, GroundEnv.bind, hy] using ihs _ _ _ _ hi
          · simpa [GroundEnv.lookup, GroundEnv.bind, hy] using hi (.free y)
    · intro x T ρ bs ι κ hi h
      exact hi x h
    · intro ks D T ih ρ bs ι κ hi v h
      obtain ⟨hk, vs, hv, hD, hTv⟩ := h
      exact ⟨hk, vs, hv, ih _ _ _ _ hi hD, hTv⟩
  refine ⟨hc, ?_⟩
  rintro ⟨ks, D, T⟩ ρ bs ι κ hi v ⟨hk, vs, hv, hD, hTv⟩
  exact ⟨hk, vs, hv, hc _ _ _ _ _ hi hD, hTv⟩

/-- This is the body obligation after comparing declared and generated schemes. -/
theorem definitionMonotone (hs : s.denote M ρ bs ι ⊆ t.denote M ρ bs ι)
    (h : (Constraint.def_ s D).Holds M ρ bs ι) :
    (Constraint.def_ t D).Holds M ρ bs ι := by
  apply (groundMonotonicity M).1 D ρ bs _ _ _ h
  intro x
  cases x with
  | free x => exact Set.Subset.refl _
  | bound i =>
      cases i with
      | zero => exact hs
      | succ i => exact Set.Subset.refl _

end EHMX
