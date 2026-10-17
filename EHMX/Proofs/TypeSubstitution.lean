import EHMX.Proofs.ConstraintLaws

/-!
束縛された型・効果変数の同時代入。
使用先は `typingTypeEffectSubstitution` の letPoly / handle / exists_ 分岐、
さらに多相値と操作節の具体化である。外側の変数の代入像を量化の下で
持ち上げ、内側の変数はそのまま残す。

構成の参照元: lean-system-f-xi, commit
9173a02d9c67eea0b0c665d3319d834e3947518f,
EffectPolyTypeLemmas / Typing.substKind_preserves。
EHMX では型と効果が同一の kind 付き構文なので、代入は一本の写像で表す。
制約とスキームの量化にも持上げを適用する点は EHMX 固有である。
-/
namespace EHMX

abbrev BoundSubst := Nat → Ty

def Ty.substBound (σ : BoundSubst) : Ty → Ty
  | .free X => .free X
  | .bound i => σ i
  | .con f ts => .con f (ts.map (Ty.substBound σ))

def BoundSubst.lift (n : Nat) (σ : BoundSubst) : BoundSubst :=
  fun i => if i < n then .bound i else (σ (i - n)).shift n 0

def BoundSubst.Valid (S : Signature) (Δ Δ' : List Kind) (σ : BoundSubst) : Prop :=
  ∀ i k, Δ[i]? = some k →
    (∃ j, σ i = .bound j ∧ Δ'[j]? = some k) ∨ (σ i).HasKind S Δ' k

/-- An unused, undeclared kind in Δ can still be renamed to the same kind in Δ'.
The final safety goals do not require all entries of Δ to be declared. -/
theorem BoundSubst.imageKind (hσ : BoundSubst.Valid S Δ Δ' σ)
    (hi : Δ[i]? = some k) (hk : k ∈ S.kinds) : (σ i).HasKind S Δ' k := by
  rcases hσ i k hi with ⟨j, hj, hlookup⟩ | h
  · rw [hj]; exact .bound hlookup hk
  · exact h

mutual
def Constraint.substBound (σ : BoundSubst) : Constraint → Constraint
  | .truth => .truth
  | .falsity => .falsity
  | .atom p ts => .atom p (ts.map (Ty.substBound σ))
  | .conj C D => .conj (C.substBound σ) (D.substBound σ)
  | .exists_ ks C => .exists_ ks (C.substBound (σ.lift ks.length))
  | .forall_ ks C => .forall_ ks (C.substBound (σ.lift ks.length))
  | .def_ s C => .def_ (s.substBound σ) (C.substBound σ)
  | .defFree x s C => .defFree x (s.substBound σ) (C.substBound σ)
  | .inst x T => .inst x (T.substBound σ)
def Scheme.substBound (σ : BoundSubst) : Scheme → Scheme
  | .all ks C T => .all ks (C.substBound (σ.lift ks.length))
      (T.substBound (σ.lift ks.length))
end

def Env.substBound (σ : BoundSubst) (Γ : Env) : Env :=
  ⟨Γ.free.map (fun p => (p.1, p.2.substBound σ)), Γ.bound.map (Scheme.substBound σ)⟩

theorem kindSubstBound (h : Ty.HasKind S Δ T k) (hσ : BoundSubst.Valid S Δ Δ' σ) :
    Ty.HasKind S Δ' (T.substBound σ) k := by
  induction T using tyInduction generalizing k with
  | hf X =>
      simp only [Ty.substBound]
      cases h; exact .free (by assumption)
  | hb i =>
      simp only [Ty.substBound]
      cases h with | bound hi hk => exact BoundSubst.imageKind hσ hi hk
  | hc f ts ih =>
      simp only [Ty.substBound]
      cases h with
      | con hf hs =>
          exact .con hf (List.forall₂_map_left_iff.mpr
            (forall₂ImplMem hs (fun T hT k hk => ih T hT hk)))

theorem BoundSubst.validLift (hσ : BoundSubst.Valid S Δ Δ' σ) (ks : List Kind) :
    BoundSubst.Valid S (ks ++ Δ) (ks ++ Δ') (σ.lift ks.length) := by
  intro i k hi
  unfold BoundSubst.lift
  by_cases h : i < ks.length
  · simp only [h, ↓reduceIte]
    exact Or.inl ⟨i, rfl, by simpa [List.getElem?_append, h] using hi⟩
  · simp only [h, ↓reduceIte]
    have ht : Δ[i - ks.length]? = some k := by
      simpa [List.getElem?_append, h] using hi
    rcases hσ _ _ ht with ⟨j, hj, hlookup⟩ | hk
    · refine Or.inl ⟨j + ks.length, ?_, ?_⟩
      · simp [hj, Ty.shift]
      · simpa [List.getElem?_append, Nat.not_lt, Nat.add_comm] using hlookup
    · exact Or.inr (kindShift hk ks)

@[simp] theorem tySubstBoundId (T : Ty) : T.substBound Ty.bound = T := by
  induction T using tyInduction with
  | hf X => simp only [Ty.substBound]
  | hb i => simp only [Ty.substBound]
  | hc f ts ih =>
      simp only [Ty.substBound]
      congr 1
      exact (List.map_congr_left (fun T hT => ih T hT)).trans (List.map_id ts)

/-- Shift is a simultaneous renaming, including a nonzero cutoff. -/
theorem tyShiftSubstBound (T : Ty) (n d : Nat) :
    T.shift n d = T.substBound (fun i => .bound (if i < d then i else i + n)) := by
  induction T using tyInduction with
  | hf X => simp only [Ty.substBound, Ty.shift]
  | hb i => simp only [Ty.substBound, Ty.shift]
  | hc f ts ih =>
      simp only [Ty.shift, Ty.substBound]
      congr 1
      exact List.map_congr_left (fun T hT => ih T hT)

/-- Opening removes a block; under d binders its replacement terms are shifted. -/
theorem tyOpenSubstBound (T : Ty) (d : Nat) (us : List Ty) :
    T.openAt d us = T.substBound (fun i => if i < d then .bound i else
      match us[i-d]? with
      | some U => U.shift d 0
      | none => .bound (i - us.length)) := by
  induction T using tyInduction with
  | hf X => simp only [Ty.substBound, Ty.openAt]
  | hb i =>
      simp only [Ty.substBound, Ty.openAt]
      split <;> rfl
  | hc f ts ih =>
      simp only [Ty.openAt, Ty.substBound]
      congr 1
      exact List.map_congr_left (fun T hT => ih T hT)

theorem tySubstBoundComp (T : Ty) (σ τ : BoundSubst) :
    (T.substBound σ).substBound τ = T.substBound (fun i => (σ i).substBound τ) := by
  induction T using tyInduction with
  | hf X => simp only [Ty.substBound]
  | hb i => simp only [Ty.substBound]
  | hc f ts ih =>
      simp only [Ty.substBound, List.map_map]
      congr 1
      exact List.map_congr_left (fun T hT => ih T hT)

theorem tyShiftLiftSubst (T : Ty) (n : Nat) (σ : BoundSubst) :
    (T.shift n 0).substBound (σ.lift n) = (T.substBound σ).shift n 0 := by
  induction T using tyInduction with
  | hf X => simp [Ty.shift, Ty.substBound]
  | hb i => simp [Ty.shift, Ty.substBound, BoundSubst.lift]
  | hc f ts ih =>
      simp only [Ty.shift, Ty.substBound, List.map_map]
      congr 1
      exact List.map_congr_left (fun T hT => ih T hT)

/-- Simultaneous preservation for constraints and schemes. In particular, both
existential and universal binders use the lifted induction hypothesis. -/
theorem substBoundWF (S : Signature) :
    (∀ (C : Constraint) Δ n, C.WF S Δ n → ∀ Δ' σ, BoundSubst.Valid S Δ Δ' σ →
      (C.substBound σ).WF S Δ' n) ∧
    (∀ (s : Scheme) Δ n, s.WF S Δ n → ∀ Δ' σ, BoundSubst.Valid S Δ Δ' σ →
      (s.substBound σ).WF S Δ' n) := by
  have hc : ∀ (C : Constraint) Δ n, C.WF S Δ n →
      ∀ Δ' σ, BoundSubst.Valid S Δ Δ' σ → (C.substBound σ).WF S Δ' n := by
    apply Constraint.rec
      (motive_1 := fun C => ∀ Δ n, C.WF S Δ n → ∀ Δ' σ,
        BoundSubst.Valid S Δ Δ' σ → (C.substBound σ).WF S Δ' n)
      (motive_2 := fun s => ∀ Δ n, s.WF S Δ n → ∀ Δ' σ,
        BoundSubst.Valid S Δ Δ' σ → (s.substBound σ).WF S Δ' n)
    · intros; trivial
    · intros; trivial
    · intro p ts Δ n h Δ' σ hσ
      exact ⟨h.1, List.forall₂_map_left_iff.mpr
        (forall₂ImplMem h.2 (fun _ _ _ h => kindSubstBound h hσ))⟩
    · intro C D ihC ihD Δ n h Δ' σ hσ
      exact ⟨ihC _ _ h.1 _ _ hσ, ihD _ _ h.2 _ _ hσ⟩
    · intro ks C ih Δ n h Δ' σ hσ
      exact ⟨h.1, ih _ _ h.2 _ _ (BoundSubst.validLift hσ ks)⟩
    · intro ks C ih Δ n h Δ' σ hσ
      exact ⟨h.1, ih _ _ h.2 _ _ (BoundSubst.validLift hσ ks)⟩
    · intro s C ihs ihC Δ n h Δ' σ hσ
      exact ⟨ihs _ _ h.1 _ _ hσ, ihC _ _ h.2 _ _ hσ⟩
    · intro x s C ihs ihC Δ n h Δ' σ hσ
      exact ⟨ihs _ _ h.1 _ _ hσ, ihC _ _ h.2 _ _ hσ⟩
    · intro x T Δ n h Δ' σ hσ
      exact ⟨kindSubstBound h.1 hσ, h.2⟩
    · intro ks C T ih Δ n h Δ' σ hσ
      exact ⟨h.1, ih _ _ h.2.1 _ _ (BoundSubst.validLift hσ ks),
        kindSubstBound h.2.2 (BoundSubst.validLift hσ ks)⟩
  refine ⟨hc, ?_⟩
  intro s Δ n h Δ' σ hσ
  cases s with
  | all ks C T =>
      exact ⟨h.1, hc C _ _ h.2.1 _ _ (BoundSubst.validLift hσ ks),
        kindSubstBound h.2.2 (BoundSubst.validLift hσ ks)⟩

/-- Substitution cannot introduce free term identifiers into constraints. -/
theorem substBoundFpi :
    (∀ (C : Constraint) σ, (C.substBound σ).fpi = C.fpi) ∧
    (∀ (s : Scheme) σ, (s.substBound σ).fpi = s.fpi) := by
  have hc : ∀ (C : Constraint) σ, (C.substBound σ).fpi = C.fpi := by
    apply Constraint.rec
      (motive_1 := fun C => ∀ σ, (C.substBound σ).fpi = C.fpi)
      (motive_2 := fun s => ∀ σ, (s.substBound σ).fpi = s.fpi)
    all_goals intros; simp_all [Constraint.substBound, Scheme.substBound,
      Constraint.fpi, Scheme.fpi]
    case inst x T σ => cases x <;> rfl
  exact ⟨hc, fun s σ => by cases s; exact hc _ _⟩

theorem envSubstBoundWF (h : Env.WF S Δ Γ) (hσ : BoundSubst.Valid S Δ Δ' σ) :
    Env.WF S Δ' (Γ.substBound σ) := by
  constructor
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨(substBoundWF S).2 _ _ _ (h.1 q hq).1 _ _ hσ,
      ((substBoundFpi.2 _ σ).trans (h.1 q hq).2)⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact ⟨(substBoundWF S).2 _ _ _ (h.2 t ht).1 _ _ hσ,
      ((substBoundFpi.2 _ σ).trans (h.2 t ht).2)⟩

/-- Relation between source and target valuations. Quantifier witnesses remain
semantic values; they need not be expressible by type syntax. -/
def BoundSubst.Realizes (M : Model) (Δ : List Kind) (ρ : Assignment M)
    (bs bs' : List M.Carrier) (σ : BoundSubst) : Prop :=
  ∀ i k, Δ[i]? = some k → (σ i).eval M ρ bs' = bs[i]?.getD M.default

theorem forall₂MemLeft (h : List.Forall₂ R xs ys) (hx : x ∈ xs) :
    ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | cons hr hs ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, by simp, hr⟩
      · obtain ⟨y, hy, hr⟩ := ih hx
        exact ⟨y, by simp [hy], hr⟩

theorem evalSubstBound (hT : Ty.HasKind S Δ T k)
    (hσ : BoundSubst.Realizes M Δ ρ bs bs' σ) :
    (T.substBound σ).eval M ρ bs' = T.eval M ρ bs := by
  induction T using tyInduction generalizing k with
  | hf X => simp [Ty.substBound, Ty.eval]
  | hb i =>
      cases hT with
      | bound hi _ => simpa [Ty.substBound, Ty.eval] using hσ i _ hi
  | hc f ts ih =>
      cases hT with
      | con hf hs =>
          simp only [Ty.substBound, Ty.eval, List.map_map]
          congr 1
          apply List.map_congr_left
          intro T hT
          obtain ⟨k, _, hk⟩ := forall₂MemLeft hs hT
          exact ih T hT hk

theorem BoundSubst.realizesLift (hσ : BoundSubst.Realizes M Δ ρ bs bs' σ)
    (hvs : KindValues M ks vs) :
    BoundSubst.Realizes M (ks ++ Δ) ρ (vs ++ bs) (vs ++ bs') (σ.lift ks.length) := by
  intro i k hi
  have hlen := hvs.length_eq
  by_cases h : i < ks.length
  · have hv : i < vs.length := by omega
    simp [BoundSubst.lift, h, Ty.eval, List.getElem?_append, hv]
  · have hv : ¬ i < vs.length := by omega
    have ht : Δ[i - ks.length]? = some k := by
      simpa [List.getElem?_append, h] using hi
    simpa [BoundSubst.lift, h, ← hlen, evalShift, List.getElem?_append, hv]
      using hσ _ _ ht

/-- Mutual semantic substitution covers existential/universal quantification
and ground-environment bindings, including schemes under def/defFree. -/
theorem substBoundSemantics (M : Model) :
    (∀ (C : Constraint) Δ n, C.WF S Δ n → ∀ ρ bs bs' σ ι,
      BoundSubst.Realizes M Δ ρ bs bs' σ →
      ((C.substBound σ).Holds M ρ bs' ι ↔ C.Holds M ρ bs ι)) ∧
    (∀ (s : Scheme) Δ n, s.WF S Δ n → ∀ ρ bs bs' σ ι,
      BoundSubst.Realizes M Δ ρ bs bs' σ →
      (s.substBound σ).denote M ρ bs' ι = s.denote M ρ bs ι) := by
  have hc : ∀ (C : Constraint) Δ n, C.WF S Δ n → ∀ ρ bs bs' σ ι,
      BoundSubst.Realizes M Δ ρ bs bs' σ →
      ((C.substBound σ).Holds M ρ bs' ι ↔ C.Holds M ρ bs ι) := by
    apply Constraint.rec
      (motive_1 := fun C => ∀ Δ n, C.WF S Δ n → ∀ ρ bs bs' σ ι,
        BoundSubst.Realizes M Δ ρ bs bs' σ →
        ((C.substBound σ).Holds M ρ bs' ι ↔ C.Holds M ρ bs ι))
      (motive_2 := fun s => ∀ Δ n, s.WF S Δ n → ∀ ρ bs bs' σ ι,
        BoundSubst.Realizes M Δ ρ bs bs' σ →
        (s.substBound σ).denote M ρ bs' ι = s.denote M ρ bs ι)
    · intros; rfl
    · intros; rfl
    · intro p ts Δ n h ρ bs bs' σ ι hσ
      simp only [Constraint.substBound, Constraint.Holds, List.map_map]
      have he : ts.map (fun T => (T.substBound σ).eval M ρ bs') =
          ts.map (fun T => T.eval M ρ bs) := by
        apply List.map_congr_left
        intro T hT
        obtain ⟨k, _, hk⟩ := forall₂MemLeft h.2 hT
        exact evalSubstBound hk hσ
      rw [show (Ty.eval M ρ bs' ∘ Ty.substBound σ) =
        (fun T => (T.substBound σ).eval M ρ bs') from rfl, he]
    · intro C D ihC ihD Δ n h ρ bs bs' σ ι hσ
      exact and_congr (ihC _ _ h.1 _ _ _ _ _ hσ) (ihD _ _ h.2 _ _ _ _ _ hσ)
    · intro ks C ih Δ n h ρ bs bs' σ ι hσ
      change (∃ vs, KindValues M ks vs ∧ _) ↔ ∃ vs, KindValues M ks vs ∧ _
      exact exists_congr (fun vs => and_congr_right (fun hv =>
        ih _ _ h.2 _ _ _ _ _ (BoundSubst.realizesLift hσ hv)))
    · intro ks C ih Δ n h ρ bs bs' σ ι hσ
      change (∀ vs, KindValues M ks vs → _) ↔ ∀ vs, KindValues M ks vs → _
      exact forall_congr' (fun vs => imp_congr_right (fun hv =>
        ih _ _ h.2 _ _ _ _ _ (BoundSubst.realizesLift hσ hv)))
    · intro s C ihs ihC Δ n h ρ bs bs' σ ι hσ
      simp only [Constraint.substBound, Constraint.Holds,
        ihs _ _ h.1 _ _ _ _ _ hσ]
      exact ihC _ _ h.2 _ _ _ _ _ hσ
    · intro x s C ihs ihC Δ n h ρ bs bs' σ ι hσ
      simp only [Constraint.substBound, Constraint.Holds,
        ihs _ _ h.1 _ _ _ _ _ hσ]
      exact ihC _ _ h.2 _ _ _ _ _ hσ
    · intro x T Δ n h ρ bs bs' σ ι hσ
      simp only [Constraint.substBound, Constraint.Holds, evalSubstBound h.1 hσ]
    · intro ks C T ih Δ n h ρ bs bs' σ ι hσ
      ext v
      change (_ ∧ ∃ vs, KindValues M ks vs ∧ _ ∧ _) ↔
        (_ ∧ ∃ vs, KindValues M ks vs ∧ _ ∧ _)
      apply and_congr_right; intro _
      apply exists_congr; intro vs
      apply and_congr_right; intro hv
      rw [ih _ _ h.2.1 _ _ _ _ _ (BoundSubst.realizesLift hσ hv),
        evalSubstBound h.2.2 (BoundSubst.realizesLift hσ hv)]
  refine ⟨hc, ?_⟩
  intro s Δ n h ρ bs bs' σ ι hσ
  cases s with
  | all ks C T =>
      ext v
      change (_ ∧ ∃ vs, KindValues M ks vs ∧ _ ∧ _) ↔
        (_ ∧ ∃ vs, KindValues M ks vs ∧ _ ∧ _)
      apply and_congr_right; intro _
      apply exists_congr; intro vs
      apply and_congr_right; intro hv
      rw [hc _ _ _ h.2.1 _ _ _ _ _ (BoundSubst.realizesLift hσ hv),
        evalSubstBound h.2.2 (BoundSubst.realizesLift hσ hv)]

/-- Every valid target valuation induces a source valuation, even if Δ contains
unused undeclared kinds. This is a semantic valuation, not a list of type terms. -/
theorem BoundSubst.realization (hF : EffectFramework S M)
    (hσ : BoundSubst.Valid S Δ Δ' σ) (hρ : Assignment.Valid S M ρ)
    (hbs' : KindValues M Δ' bs') :
    ∃ bs, KindValues M Δ bs ∧ BoundSubst.Realizes M Δ ρ bs bs' σ := by
  let bs := List.ofFn (fun i : Fin Δ.length => (σ i).eval M ρ bs')
  have hi : ∀ i k, Δ[i]? = some k → M.kind ((σ i).eval M ρ bs') = k := by
    intro i k hik
    rcases hσ i k hik with ⟨j, hj, hlookup⟩ | hk
    · obtain ⟨v, hv, hkv⟩ := forall₂Lookup hbs' hlookup
      simpa [hj, Ty.eval, hv] using hkv
    · exact evalKind hF hρ hbs' hk
  refine ⟨bs, ?_, ?_⟩
  · apply List.forall₂_iff_get.mpr
    refine ⟨by simp [bs], ?_⟩
    intro i h₁ h₂
    simpa [bs] using hi i Δ[i] (List.getElem?_eq_getElem h₂)
  · intro i k hik
    have hlt := (List.getElem?_eq_some_iff.mp hik).1
    simp [bs, hlt]

theorem entailsSubstBound (hF : EffectFramework S M)
    (hσ : BoundSubst.Valid S Δ Δ' σ)
    (hC : Constraint.WF S Δ 0 C) (hD : Constraint.WF S Δ 0 D)
    (h : Entails S M Δ C D) :
    Entails S M Δ' (C.substBound σ) (D.substBound σ) := by
  intro ρ bs' ι hρ hbs' hι hC'
  obtain ⟨bs, hbs, hr⟩ := BoundSubst.realization hF hσ hρ hbs'
  exact ((substBoundSemantics M).1 D _ _ hD _ _ _ _ _ hr).mpr
    (h _ _ _ hρ hbs hι (((substBoundSemantics M).1 C _ _ hC _ _ _ _ _ hr).mp hC'))

@[simp] theorem BoundSubst.liftZero (σ : BoundSubst) : σ.lift 0 = σ := by
  funext i; simp [BoundSubst.lift]

theorem BoundSubst.liftComp (n : Nat) (σ τ : BoundSubst) :
    (fun i => (σ.lift n i).substBound (τ.lift n)) =
      BoundSubst.lift n (fun i => (σ i).substBound τ) := by
  funext i
  by_cases h : i < n
  · simp [BoundSubst.lift, h, Ty.substBound]
  · simp only [BoundSubst.lift, h, ↓reduceIte]
    exact tyShiftLiftSubst _ _ _

theorem substBoundComp :
    (∀ (C : Constraint) σ τ, (C.substBound σ).substBound τ =
      C.substBound (fun i => (σ i).substBound τ)) ∧
    (∀ (s : Scheme) σ τ, (s.substBound σ).substBound τ =
      s.substBound (fun i => (σ i).substBound τ)) := by
  have hc : ∀ (C : Constraint) σ τ, (C.substBound σ).substBound τ =
      C.substBound (fun i => (σ i).substBound τ) := by
    apply Constraint.rec
      (motive_1 := fun C => ∀ σ τ, (C.substBound σ).substBound τ =
        C.substBound (fun i => (σ i).substBound τ))
      (motive_2 := fun s => ∀ σ τ, (s.substBound σ).substBound τ =
        s.substBound (fun i => (σ i).substBound τ))
    all_goals intros; simp_all only [Constraint.substBound, Scheme.substBound,
      List.map_map, Function.comp_def, tySubstBoundComp, BoundSubst.liftComp]
  refine ⟨hc, ?_⟩
  intro s σ τ
  cases s
  simp only [Scheme.substBound, hc, tySubstBoundComp, BoundSubst.liftComp]

theorem BoundSubst.liftShift (n m d : Nat) :
    (BoundSubst.lift n (fun i => .bound (if i < d then i else i + m))) =
      (fun i => .bound (if i < d + n then i else i + m)) := by
  funext i
  by_cases h : i < n
  · have hi : i < d + n := by omega
    simp [BoundSubst.lift, h, hi]
  · by_cases hd : i - n < d
    · have hi : i < d + n := by omega
      simp [BoundSubst.lift, h, hd, hi, Ty.shift, Nat.sub_add_cancel (by omega : n ≤ i)]
    · have hi : ¬ i < d + n := by omega
      simp only [BoundSubst.lift, h, hd, hi, ↓reduceIte, Ty.shift,
        Nat.not_lt_zero]
      congr 1; omega

theorem shiftSubstBound :
    (∀ (C : Constraint) n d, C.shift n d =
      C.substBound (fun i => .bound (if i < d then i else i + n))) ∧
    (∀ (s : Scheme) n d, s.shift n d =
      s.substBound (fun i => .bound (if i < d then i else i + n))) := by
  have hc : ∀ (C : Constraint) n d, C.shift n d =
      C.substBound (fun i => .bound (if i < d then i else i + n)) := by
    apply Constraint.rec
      (motive_1 := fun C => ∀ n d, C.shift n d =
        C.substBound (fun i => .bound (if i < d then i else i + n)))
      (motive_2 := fun s => ∀ n d, s.shift n d =
        s.substBound (fun i => .bound (if i < d then i else i + n)))
    all_goals intros; simp_all only [Constraint.shift, Scheme.shift,
      Constraint.substBound, Scheme.substBound, tyShiftSubstBound, BoundSubst.liftShift]
    case atom p ts n d =>
      congr 1
      exact List.map_congr_left (fun T _ => tyShiftSubstBound T n d)
  refine ⟨hc, ?_⟩
  intro s n d; cases s
  simp only [Scheme.shift, Scheme.substBound, hc, tyShiftSubstBound, BoundSubst.liftShift]

theorem constraintShiftLiftSubst (C : Constraint) (n : Nat) (σ : BoundSubst) :
    (C.shift n 0).substBound (σ.lift n) = (C.substBound σ).shift n 0 := by
  simp only [shiftSubstBound.1, substBoundComp.1, Nat.not_lt_zero, ↓reduceIte]
  congr 1
  funext i
  have hn : ¬ i + n < n := by omega
  simp only [Ty.substBound, BoundSubst.lift, hn, ↓reduceIte, Nat.add_sub_cancel_right]
  simpa only [Nat.not_lt_zero, ↓reduceIte] using tyShiftSubstBound (σ i) n 0

theorem schemeShiftLiftSubst (s : Scheme) (n : Nat) (σ : BoundSubst) :
    (s.shift n 0).substBound (σ.lift n) = (s.substBound σ).shift n 0 := by
  simp only [shiftSubstBound.2, substBoundComp.2, Nat.not_lt_zero, ↓reduceIte]
  congr 1
  funext i
  have hn : ¬ i + n < n := by omega
  simp only [Ty.substBound, BoundSubst.lift, hn, ↓reduceIte, Nat.add_sub_cancel_right]
  simpa only [Nat.not_lt_zero, ↓reduceIte] using tyShiftSubstBound (σ i) n 0

theorem envShiftLiftSubst (Γ : Env) (n : Nat) (σ : BoundSubst) :
    (Γ.shift n).substBound (σ.lift n) = (Γ.substBound σ).shift n := by
  cases Γ
  simp only [Env.shift, Env.substBound, List.map_map, Function.comp_def,
    schemeShiftLiftSubst]

theorem instanceSubstBound (s : Scheme) (T : Ty) (σ : BoundSubst) :
    (s.instanceConstraint T).substBound σ =
      (s.substBound σ).instanceConstraint (T.substBound σ) := by
  cases s
  simp only [Scheme.instanceConstraint, Scheme.substBound, Constraint.substBound,
    Constraint.le, List.map_cons, List.map_nil, tyShiftLiftSubst]

theorem declarationSubstBound (hT : Ty.HasKind S ks T k) (σ : BoundSubst) :
    T.substBound (σ.lift ks.length) = T := by
  induction T using tyInduction generalizing k with
  | hf X => simp [Ty.substBound]
  | hb i =>
      cases hT with
      | bound hi _ =>
          have hlt := (List.getElem?_eq_some_iff.mp hi).1
          simp [Ty.substBound, BoundSubst.lift, hlt]
  | hc f ts ih =>
      simp only [Ty.substBound]
      congr 1
      trans ts.map id
      · apply List.map_congr_left
        intro T hmem
        cases hT with
        | con _ hs =>
            obtain ⟨k, _, hk⟩ := forall₂MemLeft hs hmem
            exact ih T hmem hk
      · exact List.map_id ts

theorem declarationOpenSubstBound (hT : Ty.HasKind S ks T k)
    (hargs : List.Forall₂ (Ty.HasKind S Δ) args ks) (σ : BoundSubst) :
    (T.openAt 0 args).substBound σ = T.openAt 0 (args.map (Ty.substBound σ)) := by
  induction T using tyInduction generalizing k with
  | hf X => simp [Ty.openAt, Ty.substBound]
  | hb i =>
      cases hT with
      | bound hi _ =>
          obtain ⟨U, hU, _⟩ := forall₂Lookup hargs hi
          simp [Ty.openAt, hU, List.getElem?_map]
  | hc f ts ih =>
      simp only [Ty.openAt, Ty.substBound, List.map_map]
      congr 1
      apply List.map_congr_left
      intro T hmem
      cases hT with
      | con _ hs =>
          obtain ⟨k, _, hk⟩ := forall₂MemLeft hs hmem
          exact ih T hmem hk

@[simp] theorem BoundSubst.liftId (n : Nat) : BoundSubst.lift n Ty.bound = Ty.bound := by
  funext i
  by_cases h : i < n
  · simp [BoundSubst.lift, h]
  · simp [BoundSubst.lift, h, Ty.shift, Nat.sub_add_cancel (by omega : n ≤ i)]

theorem substBoundId :
    (∀ (C : Constraint), C.substBound Ty.bound = C) ∧
    (∀ (s : Scheme), s.substBound Ty.bound = s) := by
  have hc : ∀ (C : Constraint), C.substBound Ty.bound = C := by
    apply Constraint.rec
      (motive_1 := fun C => C.substBound Ty.bound = C)
      (motive_2 := fun s => s.substBound Ty.bound = s)
    all_goals intros; simp_all [Constraint.substBound, Scheme.substBound]
    case atom p ts => exact (List.map_congr_left (fun T _ => tySubstBoundId T)).trans (List.map_id ts)
  exact ⟨hc, fun s => by cases s; simp [Scheme.substBound, hc]⟩

/-- Remove precisely the initial block, leaving all outer variables in scope. -/
def BoundSubst.many (args : List Ty) : BoundSubst := fun i =>
  match args[i]? with
  | some U => U
  | none => .bound (i - args.length)

theorem BoundSubst.validMany (hargs : List.Forall₂ (Ty.HasKind S Δ) args ks) :
    BoundSubst.Valid S (ks ++ Δ) Δ (BoundSubst.many args) := by
  intro i k hi
  by_cases h : i < ks.length
  · have hki : ks[i]? = some k := by simpa [List.getElem?_append, h] using hi
    obtain ⟨U, hU, hk⟩ := forall₂Lookup hargs hki
    exact Or.inr (by simpa [BoundSubst.many, hU] using hk)
  · have hlen := hargs.length_eq
    have hn : args[i]? = none := List.getElem?_eq_none (by omega)
    exact Or.inl ⟨i - args.length, by simp [BoundSubst.many, hn],
      by simpa [List.getElem?_append, h, hlen] using hi⟩

theorem tyOpenMany (T : Ty) (args : List Ty) :
    T.openAt 0 args = T.substBound (BoundSubst.many args) := by
  rw [tyOpenSubstBound]
  congr 1
  funext i
  simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, BoundSubst.many]
  cases args[i]? <;> simp

theorem BoundSubst.manyShift (args : List Ty) (i : Nat) :
    BoundSubst.many args (i + args.length) = .bound i := by
  simp [BoundSubst.many]

theorem tyShiftMany (T : Ty) (args : List Ty) :
    (T.shift args.length 0).substBound (BoundSubst.many args) = T := by
  rw [tyShiftSubstBound, tySubstBoundComp]
  simpa only [Nat.not_lt_zero, ↓reduceIte, Ty.substBound,
    BoundSubst.manyShift] using tySubstBoundId T

theorem constraintShiftMany (C : Constraint) (args : List Ty) :
    (C.shift args.length 0).substBound (BoundSubst.many args) = C := by
  rw [shiftSubstBound.1, substBoundComp.1]
  simpa only [Nat.not_lt_zero, ↓reduceIte, Ty.substBound,
    BoundSubst.manyShift] using substBoundId.1 C

theorem schemeShiftMany (s : Scheme) (args : List Ty) :
    (s.shift args.length 0).substBound (BoundSubst.many args) = s := by
  rw [shiftSubstBound.2, substBoundComp.2]
  simpa only [Nat.not_lt_zero, ↓reduceIte, Ty.substBound,
    BoundSubst.manyShift] using substBoundId.2 s

theorem envShiftMany (Γ : Env) (args : List Ty) :
    (Γ.shift args.length).substBound (BoundSubst.many args) = Γ := by
  cases Γ
  simp [Env.shift, Env.substBound, List.map_map, Function.comp_def, schemeShiftMany]

theorem BoundSubst.validShift (ks : List Kind) :
    BoundSubst.Valid S Δ (ks ++ Δ) (fun i => .bound (i + ks.length)) := by
  intro i k hi
  refine Or.inl ⟨i + ks.length, rfl, ?_⟩
  simpa [List.getElem?_append, Nat.not_lt, Nat.add_comm] using hi

theorem schemeShiftWF (hs : Scheme.WF S Δ n s) (ks : List Kind) :
    (s.shift ks.length 0).WF S (ks ++ Δ) n := by
  rw [shiftSubstBound.2]
  simpa only [Nat.not_lt_zero, ↓reduceIte] using
    (substBoundWF S).2 s _ _ hs _ _ (BoundSubst.validShift ks)

theorem schemeShiftFpi (s : Scheme) (n d : Nat) : (s.shift n d).fpi = s.fpi := by
  rw [shiftSubstBound.2]
  exact substBoundFpi.2 _ _

end EHMX
