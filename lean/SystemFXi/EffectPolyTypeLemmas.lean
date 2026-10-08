import SystemFXi.EffectPolySubtyping
import SystemFXi.EffectPolyProgress

/-!
# 型・効果変数の改名と置換

両 kind の変数は一つの de Bruijn 環境を使う。各補題は型注釈だけでなく
関数矢印の潜在効果にも同じ改名・置換が作用することを示す。
-/

namespace SystemFXi.Poly

/-- 恒等改名は型を変えない: id(σ) = σ。 -/
theorem Ty.rename_id (σ : Ty) : σ.rename id = σ := by
  induction σ with
  | var _ => rfl
  | arr _ _ _ ihA ihB =>
      simp [Ty.rename, ihA, ihB, Effect.rename_id]
  | all κ _ ih =>
      have hlift : liftRen id = id := by
        funext i
        cases i <;> rfl
      simpa [Ty.rename, hlift] using congrArg (Ty.all κ) ih

/-- 型と効果の同時改名は合成できる。 -/
theorem Ty.rename_comp (σ : Ty) :
    ∀ (ρ υ : Nat → Nat),
      (σ.rename ρ).rename υ = σ.rename (fun i => υ (ρ i)) := by
  induction σ with
  | var _ => intro _ _; rfl
  | arr _ _ _ ihA ihB =>
      intro ρ υ
      simp [Ty.rename, ihA, ihB, Effect.rename_comp]
  | all κ _ ih =>
      intro ρ υ
      have hlift :
          (fun i => liftRen υ (liftRen ρ i)) =
            liftRen (fun i => υ (ρ i)) := by
        funext i
        cases i <;> rfl
      simpa [Ty.rename, hlift] using
        congrArg (Ty.all κ) (ih (liftRen ρ) (liftRen υ))

/-- 恒等置換は型・効果を変えない。 -/
def KindSubst.identity : KindSubst where
  types := Ty.var
  effects := Effect.var

/-- 恒等置換を束縛子の下へ移しても恒等置換である。 -/
theorem KindSubst.identity_lift :
    KindSubst.identity.lift = KindSubst.identity := by
  apply congrArg₂ KindSubst.mk
  · funext i
    cases i <;> rfl
  · funext i
    cases i <;> simp [KindSubst.identity,
      Effect.rename, Effect.var]

/-- σ[id] = σ。 -/
theorem Ty.subst_id (σ : Ty) :
    σ.subst KindSubst.identity = σ := by
  induction σ with
  | var _ => rfl
  | arr _ _ _ ihA ihB =>
      simp only [Ty.subst, ihA, ihB]
      congr 1
      exact Effect.subst_id _
  | all κ _ ih =>
      simpa [Ty.subst, KindSubst.identity_lift] using
        congrArg (Ty.all κ) ih

/-- σ[τ] を改名すると、τ の各型・効果像を改名した置換になる。 -/
theorem Ty.subst_rename (σ : Ty) :
    ∀ (τ : KindSubst) (ρ : Nat → Nat),
      (σ.subst τ).rename ρ =
        σ.subst
          { types := fun i => (τ.types i).rename ρ
            effects := fun i => (τ.effects i).rename ρ } := by
  induction σ with
  | var _ => intro _ _; rfl
  | arr _ _ _ ihA ihB =>
      intro τ ρ
      simp [Ty.subst, Ty.rename, ihA, ihB,
        Effect.substKind, Effect.subst_rename]
  | all κ _ ih =>
      intro τ ρ
      have hlift :
          { types := fun i => (τ.lift.types i).rename (liftRen ρ)
            effects := fun i => (τ.lift.effects i).rename (liftRen ρ) } =
          (KindSubst.mk
            (fun i => (τ.types i).rename ρ)
            (fun i => (τ.effects i).rename ρ)).lift := by
        apply congrArg₂ KindSubst.mk
        · funext i
          cases i with
          | zero => rfl
          | succ j =>
              simp only [KindSubst.lift]
              rw [Ty.rename_comp, Ty.rename_comp]
              congr 1
        · funext i
          cases i with
          | zero => rfl
          | succ j =>
              simp only [KindSubst.lift]
              rw [Effect.rename_comp, Effect.rename_comp]
              congr 1
      simpa [Ty.subst, Ty.rename, hlift] using
        congrArg (Ty.all κ) (ih τ.lift (liftRen ρ))

/-- ρ(σ) の置換は、τ を ρ で添字付けした置換になる。 -/
theorem Ty.rename_subst (σ : Ty) :
    ∀ (ρ : Nat → Nat) (τ : KindSubst),
      (σ.rename ρ).subst τ =
        σ.subst
          { types := fun i => τ.types (ρ i)
            effects := fun i => τ.effects (ρ i) } := by
  induction σ with
  | var _ => intro _ _; rfl
  | arr _ _ _ ihA ihB =>
      intro ρ τ
      simp [Ty.rename, Ty.subst, ihA, ihB,
        Effect.substKind, Effect.rename_subst]
  | all κ _ ih =>
      intro ρ τ
      have hlift :
          { types := fun i => τ.lift.types (liftRen ρ i)
            effects := fun i => τ.lift.effects (liftRen ρ i) } =
          (KindSubst.mk
            (fun i => τ.types (ρ i))
            (fun i => τ.effects (ρ i))).lift := by
        apply congrArg₂ KindSubst.mk
        · funext i
          cases i <;> rfl
        · funext i
          cases i <;> rfl
      simpa [Ty.subst, Ty.rename, hlift] using
        congrArg (Ty.all κ) (ih (liftRen ρ) τ.lift)

/-- 一つ持ち上げた型への置換は、置換後に持ち上げることと等しい。 -/
theorem Ty.shift_subst (σ : Ty) (υ : KindSubst) :
    (σ.rename Nat.succ).subst υ.lift =
      (σ.subst υ).rename Nat.succ := by
  rw [Ty.rename_subst, Ty.subst_rename]
  congr 1

/-- 一つ持ち上げた効果への置換は、置換後に持ち上げることと等しい。 -/
theorem Effect.shift_subst (ε : Effect) (υ : KindSubst) :
    (ε.rename Nat.succ).subst υ.lift.effects =
      (ε.subst υ.effects).rename Nat.succ := by
  rw [Effect.rename_subst, Effect.subst_rename]
  congr 1

/-- 型・効果の二つの同時置換は各像で合成できる。 -/
theorem Ty.subst_subst (σ : Ty) :
    ∀ (τ υ : KindSubst),
      (σ.subst τ).subst υ =
        σ.subst
          { types := fun i => (τ.types i).subst υ
            effects := fun i => (τ.effects i).subst υ.effects } := by
  induction σ with
  | var _ => intro _ _; rfl
  | arr _ _ _ ihA ihB =>
      intro τ υ
      simp [Ty.subst, ihA, ihB, Effect.substKind,
        Effect.subst_subst]
  | all κ _ ih =>
      intro τ υ
      have hlift :
          { types := fun i => (τ.lift.types i).subst υ.lift
            effects := fun i => (τ.lift.effects i).subst υ.lift.effects } =
          (KindSubst.mk
            (fun i => (τ.types i).subst υ)
            (fun i => (τ.effects i).subst υ.effects)).lift := by
        apply congrArg₂ KindSubst.mk
        · funext i
          cases i with
          | zero => rfl
          | succ j => exact Ty.shift_subst (τ.types j) υ
        · funext i
          cases i with
          | zero => rfl
          | succ j => exact Effect.shift_subst (τ.effects j) υ
      simpa [Ty.subst, hlift] using
        congrArg (Ty.all κ) (ih τ.lift υ.lift)

/-- 型・効果の改名は整形式な効果の和を保つ。 -/
theorem Effect.rename_union (ε η : Effect) (ρ : Nat → Nat) :
    (ε ∪ η).rename ρ = ε.rename ρ ∪ η.rename ρ := by
  cases ε with
  | mk labels vars =>
      cases η with
      | mk labels' vars' =>
          apply congrArg₂ Effect.mk
          · rfl
          · simp [Effect.rename, Finset.image_union]

/-- 潜在効果の包含は同時改名で保存される。 -/
theorem Effect.Subset.rename {ε η : Effect}
    (h : ε ⊆ η) (ρ : Nat → Nat) :
    ε.rename ρ ⊆ η.rename ρ := by
  constructor
  · exact h.1
  · exact Finset.image_subset_image h.2

/-- 潜在効果の包含は同時置換で保存される。 -/
theorem Effect.Subset.subst {ε η : Effect}
    (h : ε ⊆ η) (τ : Nat → Effect) :
    ε.subst τ ⊆ η.subst τ := by
  constructor
  · intro op hop
    rcases Finset.mem_union.mp hop with hl | hv
    · exact Finset.mem_union.mpr (Or.inl (h.1 hl))
    · apply Finset.mem_union.mpr
      right
      rcases Finset.mem_biUnion.mp hv with ⟨μ, hμ, hopμ⟩
      exact Finset.mem_biUnion.mpr ⟨μ, h.2 hμ, hopμ⟩
  · intro μ hμ
    rcases Finset.mem_biUnion.mp hμ with ⟨ν, hν, hμν⟩
    exact Finset.mem_biUnion.mpr ⟨ν, h.2 hν, hμν⟩

/-- ρ : Δ → Δ′ は各変数の kind を保つ改名。 -/
def RenValid (Δ Δ' : List Kind) (ρ : Nat → Nat) : Prop :=
  ∀ i κ, Δ[i]? = some κ → Δ'[ρ i]? = some κ

/-- kind を保つ改名は束縛子の下でも kind を保つ。 -/
theorem liftRen_valid {Δ Δ' : List Kind} {ρ : Nat → Nat}
    (hρ : RenValid Δ Δ' ρ) (κ : Kind) :
    RenValid (κ :: Δ) (κ :: Δ') (liftRen ρ) := by
  intro i κ' hi
  cases i with
  | zero =>
      simp at hi
      subst κ'
      rfl
  | succ j =>
      simpa [liftRen] using hρ j κ' (by simpa using hi)

/-- 効果の kind 判定は kind を保つ改名で保存される。 -/
theorem Effect.WF.rename_preserves {sig : Signature}
    {Δ Δ' : List Kind} {ε : Effect} {ρ : Nat → Nat}
    (h : Effect.WF (fun op => sig op ≠ none) Δ ε)
    (hρ : RenValid Δ Δ' ρ) :
    Effect.WF (fun op => sig op ≠ none) Δ' (ε.rename ρ) := by
  constructor
  · exact h.1
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact hρ j .effect (h.2 j hj)

/-- Δ ⊢ σ :: T は kind を保つ改名で保存される。 -/
theorem Ty.WF.rename_preserves {sig : Signature}
    {Δ : List Kind} {σ : Ty} (h : Ty.WF sig Δ σ) :
    ∀ {Δ' : List Kind} (ρ : Nat → Nat),
      RenValid Δ Δ' ρ → Ty.WF sig Δ' (σ.rename ρ) := by
  induction h with
  | var hi =>
      intro Δ' ρ hρ
      exact .var (hρ _ .type hi)
  | arr _ hε _ ihA ihB =>
      intro Δ' ρ hρ
      exact .arr (ihA ρ hρ) (hε.rename_preserves hρ) (ihB ρ hρ)
  | all _ ih =>
      intro Δ' ρ hρ
      exact .all (ih (liftRen ρ) (liftRen_valid hρ _))

/-- Δ ⊢ σ₁ <: σ₂ は kind を保つ改名で保存される。 -/
theorem Subtype.rename_preserves {sig : Signature}
    {Δ : List Kind} {a b : Ty} (h : Subtype sig Δ a b) :
    ∀ {Δ' : List Kind} (ρ : Nat → Nat),
      RenValid Δ Δ' ρ →
      Subtype sig Δ' (a.rename ρ) (b.rename ρ) := by
  induction h with
  | var =>
      intro Δ' ρ hρ
      exact .var
  | arr _ hε _ ihA ihB =>
      intro Δ' ρ hρ
      exact .arr (ihA ρ hρ) (hε.rename ρ) (ihB ρ hρ)
  | all _ ih =>
      intro Δ' ρ hρ
      exact .all (ih (liftRen ρ) (liftRen_valid hρ _))

/-- τ : Δ → Δ′ は各変数を同じ kind の整形式な引数へ送る。 -/
def SubstValid (sig : Signature) (Δ Δ' : List Kind)
    (τ : KindSubst) : Prop :=
  (∀ i, Δ[i]? = some .type → Ty.WF sig Δ' (τ.types i)) ∧
  (∀ i, Δ[i]? = some .effect →
    Effect.WF (fun op => sig op ≠ none) Δ' (τ.effects i))

/-- 置換の値を一つの束縛子の下へ改名しても整形式。 -/
theorem KindSubst.lift_valid {sig : Signature}
    {Δ Δ' : List Kind} {τ : KindSubst}
    (hτ : SubstValid sig Δ Δ' τ) (κ : Kind) :
    SubstValid sig (κ :: Δ) (κ :: Δ') τ.lift := by
  constructor
  · intro i hi
    cases i with
    | zero =>
        have hk : κ = .type := by simpa using hi
        subst κ
        exact .var rfl
    | succ j =>
        have hj : Δ[j]? = some .type := by simpa using hi
        exact (hτ.1 j hj).rename_preserves Nat.succ
          (by
            intro k κ' hk
            simpa using hk)
  · intro i hi
    cases i with
    | zero =>
        have hk : κ = .effect := by simpa using hi
        subst κ
        change Effect.WF (fun op => sig op ≠ none)
          (Kind.effect :: Δ') (Effect.var 0)
        constructor
        · simp [Effect.var]
        · intro j hj
          have hzero : j = 0 := by simpa [Effect.var] using hj
          subst j
          rfl
    | succ j =>
        have hj : Δ[j]? = some .effect := by simpa using hi
        exact (hτ.2 j hj).rename_preserves
          (by
            intro k κ' hk
            simpa using hk)

/-- 効果の kind 判定は kind を保つ置換で保存される。 -/
theorem Effect.WF.subst_preserves {sig : Signature}
    {Δ Δ' : List Kind} {ε : Effect} {τ : KindSubst}
    (h : Effect.WF (fun op => sig op ≠ none) Δ ε)
    (hτ : SubstValid sig Δ Δ' τ) :
    Effect.WF (fun op => sig op ≠ none) Δ' (ε.substKind τ) := by
  constructor
  · intro op hop
    rcases Finset.mem_union.mp hop with hl | hv
    · exact h.1 op hl
    · rcases Finset.mem_biUnion.mp hv with ⟨μ, hμ, hopμ⟩
      exact (hτ.2 μ (h.2 μ hμ)).1 op hopμ
  · intro μ hμ
    rcases Finset.mem_biUnion.mp hμ with ⟨ν, hν, hμν⟩
    exact (hτ.2 ν (h.2 ν hν)).2 μ hμν

/-- Δ ⊢ σ :: T は kind を保つ同時置換で保存される。 -/
theorem Ty.WF.subst_preserves {sig : Signature}
    {Δ : List Kind} {σ : Ty} (h : Ty.WF sig Δ σ) :
    ∀ {Δ' : List Kind} (τ : KindSubst),
      SubstValid sig Δ Δ' τ → Ty.WF sig Δ' (σ.subst τ) := by
  induction h with
  | var hi =>
      intro Δ' τ hτ
      exact hτ.1 _ hi
  | arr _ hε _ ihA ihB =>
      intro Δ' τ hτ
      exact .arr (ihA τ hτ) (hε.subst_preserves hτ) (ihB τ hτ)
  | all _ ih =>
      intro Δ' τ hτ
      exact .all (ih τ.lift (KindSubst.lift_valid hτ _))

/-- 部分型は kind を保つ同時置換で保存される。 -/
theorem Subtype.subst_preserves {sig : Signature}
    {Δ : List Kind} {a b : Ty} (h : Subtype sig Δ a b) :
    ∀ {Δ' : List Kind} (τ : KindSubst),
      SubstValid sig Δ Δ' τ →
      Subtype sig Δ' (a.subst τ) (b.subst τ) := by
  induction h with
  | var =>
      intro Δ' τ hτ
      exact Subtype.refl _ _
  | arr _ hε _ ihA ihB =>
      intro Δ' τ hτ
      exact .arr (ihA τ hτ) (hε.subst τ.effects) (ihB τ hτ)
  | all _ ih =>
      intro Δ' τ hτ
      exact .all (ih τ.lift (KindSubst.lift_valid hτ _))

/-- 二つの置換が Δ の各変数上で一致する。 -/
def SubstAgree (Δ : List Kind) (τ υ : KindSubst) : Prop :=
  (∀ i, Δ[i]? = some .type → τ.types i = υ.types i) ∧
  (∀ i, Δ[i]? = some .effect → τ.effects i = υ.effects i)

/-- 束縛子の下でも置換の一致は保存される。 -/
theorem SubstAgree.lift {Δ : List Kind} {τ υ : KindSubst}
    (h : SubstAgree Δ τ υ) (κ : Kind) :
    SubstAgree (κ :: Δ) τ.lift υ.lift := by
  constructor
  · intro i hi
    cases i with
    | zero => rfl
    | succ j =>
        have hj : Δ[j]? = some .type := by simpa using hi
        simp only [KindSubst.lift]
        rw [h.1 j hj]
  · intro i hi
    cases i with
    | zero => rfl
    | succ j =>
        have hj : Δ[j]? = some .effect := by simpa using hi
        simp only [KindSubst.lift]
        rw [h.2 j hj]

/-- Δ ⊢ ε :: E の自由変数上で一致する置換は ε 上で一致する。 -/
theorem Effect.WF.subst_congr {sig : Signature}
    {Δ : List Kind} {ε : Effect}
    (h : Effect.WF (fun op => sig op ≠ none) Δ ε)
    (τ υ : KindSubst) (hag : SubstAgree Δ τ υ) :
    ε.substKind τ = ε.substKind υ := by
  unfold Effect.substKind
  apply congrArg₂ Effect.mk
  · congr 1
    apply Finset.biUnion_congr rfl
    intro μ hμ
    rw [hag.2 μ (h.2 μ hμ)]
  · apply Finset.biUnion_congr rfl
    intro μ hμ
    rw [hag.2 μ (h.2 μ hμ)]

/-- Δ ⊢ σ :: T の自由変数上で一致する置換は σ 上で一致する。 -/
theorem Ty.WF.subst_congr {sig : Signature}
    {Δ : List Kind} {σ : Ty}
    (h : Ty.WF sig Δ σ) :
    ∀ (τ υ : KindSubst), SubstAgree Δ τ υ →
      σ.subst τ = σ.subst υ := by
  induction h with
  | var hi =>
      intro τ υ hag
      exact hag.1 _ hi
  | arr _ hε _ ihA ihB =>
      intro τ υ hag
      simp only [Ty.subst, ihA τ υ hag, ihB τ υ hag,
        hε.subst_congr τ υ hag]
  | all _ ih =>
      intro τ υ hag
      simp only [Ty.subst]
      congr 1
      exact ih τ.lift υ.lift (hag.lift _)

/-- ρ が Δ の各変数を固定する。 -/
def RenFix (Δ : List Kind) (ρ : Nat → Nat) : Prop :=
  ∀ i κ, Δ[i]? = some κ → ρ i = i

/-- 束縛子の下でも改名が恒等である。 -/
theorem RenFix.lift {Δ : List Kind} {ρ : Nat → Nat}
    (h : RenFix Δ ρ) (κ : Kind) :
    RenFix (κ :: Δ) (liftRen ρ) := by
  intro i κ' hi
  cases i with
  | zero => rfl
  | succ j =>
      simpa [liftRen] using congrArg Nat.succ
        (h j κ' (by simpa using hi))

/-- ρ が自由効果変数を固定すれば ρ(ε) = ε。 -/
theorem Effect.WF.rename_eq {sig : Signature}
    {Δ : List Kind} {ε : Effect}
    (h : Effect.WF (fun op => sig op ≠ none) Δ ε)
    (ρ : Nat → Nat) (hρ : RenFix Δ ρ) :
    ε.rename ρ = ε := by
  cases ε with
  | mk labels vars =>
      apply congrArg₂ Effect.mk
      · rfl
      · calc
          vars.image ρ = vars.image id := by
            apply Finset.image_congr
            intro μ hμ
            exact hρ μ .effect (h.2 μ hμ)
          _ = vars := Finset.image_id

/-- ρ が自由な型・効果変数を固定すれば ρ(σ) = σ。 -/
theorem Ty.WF.rename_eq {sig : Signature}
    {Δ : List Kind} {σ : Ty}
    (h : Ty.WF sig Δ σ) :
    ∀ (ρ : Nat → Nat), RenFix Δ ρ → σ.rename ρ = σ := by
  induction h with
  | var hi =>
      intro ρ hρ
      simp [Ty.rename, hρ _ .type hi]
  | arr _ hε _ ihA ihB =>
      intro ρ hρ
      simp only [Ty.rename, ihA ρ hρ, ihB ρ hρ,
        hε.rename_eq ρ hρ]
  | all _ ih =>
      intro ρ hρ
      simp only [Ty.rename]
      congr 1
      exact ih (liftRen ρ) (hρ.lift _)

/-- n 個の内側の変数は外側の改名を受けない。 -/
theorem liftRenN_fixed (n : Nat) (ρ : Nat → Nat) :
    ∀ i, i < n → liftRenN n ρ i = i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ j =>
          simp only [liftRenN, liftRen]
          exact congrArg Nat.succ (ih j (by omega))

/-- 外側の i 番目の変数は ρ(i) に改名される。 -/
theorem liftRenN_outer (n : Nat) (ρ : Nat → Nat) (i : Nat) :
    liftRenN n ρ (i + n) = ρ i + n := by
  induction n with
  | zero => simp [liftRenN]
  | succ n ih =>
      have heq : i + (n + 1) = (i + n) + 1 := by omega
      rw [heq, liftRenN, liftRen, ih]
      omega

/-- 量化列の下でも kind を保つ改名は有効。 -/
theorem liftRenN_valid {Δ Δ' : List Kind} {ρ : Nat → Nat}
    (hρ : RenValid Δ Δ' ρ) (ks : List Kind) :
    RenValid (ks ++ Δ) (ks ++ Δ') (liftRenN ks.length ρ) := by
  induction ks with
  | nil => simpa [liftRenN] using hρ
  | cons κ ks ih =>
      simpa [liftRenN] using liftRen_valid ih κ

/-- 宣言された量化列の変数は、外側の改名で固定される。 -/
theorem liftRenN_fix (ks : List Kind) (ρ : Nat → Nat) :
    RenFix ks (liftRenN ks.length ρ) := by
  intro i κ hi
  have hidx : i < ks.length :=
    (List.getElem?_eq_some_iff.mp hi).choose
  exact liftRenN_fixed ks.length ρ i hidx

/-- Γ↑ⁿ を外側で改名する順序を交換できる。 -/
theorem TermCtx.liftKind_rename (Γ : TermCtx) (n : Nat)
    (ρ : Nat → Nat) :
    (Γ.liftKind n).map (Ty.rename (liftRenN n ρ)) =
      TermCtx.liftKind (Γ.map (Ty.rename ρ)) n := by
  simp only [TermCtx.liftKind, List.map_map]
  apply List.map_congr_left
  intro σ hσ
  change ((σ.rename (fun i => i + n)).rename (liftRenN n ρ)) =
    ((σ.rename ρ).rename (fun i => i + n))
  rw [Ty.rename_comp, Ty.rename_comp]
  congr 1
  funext i
  exact liftRenN_outer n ρ i

/-- 効果変数の改名は添字だけを改名する。 -/
theorem Effect.rename_var (i : Nat) (ρ : Nat → Nat) :
    (Effect.var i).rename ρ = Effect.var (ρ i) := by
  simp [Effect.var, Effect.rename]

/-- n 個の内側の変数は外側の置換を受けない。 -/
theorem KindSubst.liftN_fixed (n : Nat) (τ : KindSubst) :
    ∀ i, i < n →
      (τ.liftN n).types i = .var i ∧
      (τ.liftN n).effects i = Effect.var i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      cases i with
      | zero => exact ⟨rfl, rfl⟩
      | succ j =>
          obtain ⟨ht, he⟩ := ih j (by omega)
          simp only [KindSubst.liftN, KindSubst.lift]
          rw [ht, he, Effect.rename_var]
          exact ⟨rfl, rfl⟩

/-- 外側の i 番目の置換像は n 個の束縛子の下に持ち上がる。 -/
theorem KindSubst.liftN_outer (n : Nat) (τ : KindSubst) (i : Nat) :
    (τ.liftN n).types (i + n) =
        (τ.types i).rename (fun j => j + n) ∧
    (τ.liftN n).effects (i + n) =
        (τ.effects i).rename (fun j => j + n) := by
  induction n with
  | zero =>
      simp only [KindSubst.liftN, Nat.add_zero]
      exact ⟨(Ty.rename_id _).symm, (Effect.rename_id _).symm⟩
  | succ n ih =>
      have heq : i + (n + 1) = (i + n) + 1 := by omega
      rw [heq]
      obtain ⟨ht, he⟩ := ih
      simp only [KindSubst.liftN, KindSubst.lift, ht, he]
      constructor
      · rw [Ty.rename_comp]
        congr 1
      · rw [Effect.rename_comp]
        congr 1

/-- 量化列の下でも kind を保つ置換は有効。 -/
theorem KindSubst.liftN_valid {sig : Signature}
    {Δ Δ' : List Kind} {τ : KindSubst}
    (hτ : SubstValid sig Δ Δ' τ) (ks : List Kind) :
    SubstValid sig (ks ++ Δ) (ks ++ Δ') (τ.liftN ks.length) := by
  induction ks with
  | nil => simpa [KindSubst.liftN] using hτ
  | cons κ ks ih =>
      simpa [KindSubst.liftN] using KindSubst.lift_valid ih κ

/-- 型を n 個持ち上げてから置換する操作は、置換後に持ち上げる操作。 -/
theorem Ty.shift_substN (σ : Ty) (n : Nat) (τ : KindSubst) :
    (σ.rename (fun i => i + n)).subst (τ.liftN n) =
      (σ.subst τ).rename (fun i => i + n) := by
  rw [Ty.rename_subst, Ty.subst_rename]
  congr 1
  apply congrArg₂ KindSubst.mk
  · funext i
    exact (τ.liftN_outer n i).1
  · funext i
    exact (τ.liftN_outer n i).2

/-- 効果を n 個持ち上げてから置換する操作も可換。 -/
theorem Effect.shift_substN (ε : Effect) (n : Nat) (τ : KindSubst) :
    (ε.rename (fun i => i + n)).subst (τ.liftN n).effects =
      (ε.subst τ.effects).rename (fun i => i + n) := by
  rw [Effect.rename_subst, Effect.subst_rename]
  congr 1
  funext i
  exact (τ.liftN_outer n i).2

/-- Γ↑ⁿ への外側の置換は、先に Γ を置換してから持ち上げる操作。 -/
theorem TermCtx.liftKind_subst (Γ : TermCtx) (n : Nat)
    (τ : KindSubst) :
    (Γ.liftKind n).map (Ty.subst (τ.liftN n)) =
      TermCtx.liftKind (Γ.map (Ty.subst τ)) n := by
  simp only [TermCtx.liftKind, List.map_map]
  apply List.map_congr_left
  intro σ hσ
  exact σ.shift_substN n τ

/-- kind の一致する混合引数列は操作宣言の同時置換として有効。 -/
theorem KindSubst.many_valid {sig : Signature}
    {Δ : List Kind} {ks : List Kind} {args : List Arg}
    (hargs : List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) ks args) :
    SubstValid sig ks Δ (KindSubst.many args) := by
  have hlen : ks.length = args.length := hargs.length_eq
  constructor
  · intro i hi
    obtain ⟨hidx, hk⟩ := List.getElem?_eq_some_iff.mp hi
    have hargIdx : i < args.length := by omega
    have harg := hargs.get hidx hargIdx
    change Arg.WF sig Δ ks[i] args[i] at harg
    rw [hk] at harg
    cases hθ : args[i] with
    | type σ =>
        have hσ : Ty.WF sig Δ σ := by
          simp [Arg.WF, hθ] at harg
          exact harg
        simpa [KindSubst.many, hargIdx, hθ] using hσ
    | effect ε =>
        have hfalse : False := by
          simp [Arg.WF, hθ] at harg
        exact hfalse.elim
  · intro i hi
    obtain ⟨hidx, hk⟩ := List.getElem?_eq_some_iff.mp hi
    have hargIdx : i < args.length := by omega
    have harg := hargs.get hidx hargIdx
    change Arg.WF sig Δ ks[i] args[i] at harg
    rw [hk] at harg
    cases hθ : args[i] with
    | type σ =>
        have hfalse : False := by
          simp [Arg.WF, hθ] at harg
        exact hfalse.elim
    | effect ε =>
        have hε : Effect.WF (fun op => sig op ≠ none) Δ ε := by
          simpa [Arg.WF, hθ] using harg
        simpa [KindSubst.many, hargIdx, hθ] using hε

/-- 混合引数列の置換は、量化列の外側の kind 環境も保つ。 -/
theorem KindSubst.many_valid_append {sig : Signature}
    {Δ : List Kind} {ks : List Kind} {args : List Arg}
    (hargs : List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) ks args) :
    SubstValid sig (ks ++ Δ) Δ (KindSubst.many args) := by
  have hbase := KindSubst.many_valid hargs
  have hlen : ks.length = args.length := hargs.length_eq
  constructor
  · intro i hi
    by_cases hsmall : i < ks.length
    · rw [List.getElem?_append_left hsmall] at hi
      exact hbase.1 i hi
    · have hlarge : ks.length ≤ i := by omega
      rw [List.getElem?_append_right hlarge] at hi
      have hargsLarge : args.length ≤ i := by omega
      have hnone : args[i]? = none :=
        List.getElem?_eq_none hargsLarge
      have hi' : Δ[i - args.length]? = some .type := by
        simpa [hlen] using hi
      simpa [KindSubst.many, hnone] using Ty.WF.var hi'
  · intro i hi
    by_cases hsmall : i < ks.length
    · rw [List.getElem?_append_left hsmall] at hi
      exact hbase.2 i hi
    · have hlarge : ks.length ≤ i := by omega
      rw [List.getElem?_append_right hlarge] at hi
      have hargsLarge : args.length ≤ i := by omega
      have hnone : args[i]? = none :=
        List.getElem?_eq_none hargsLarge
      have hi' : Δ[i - args.length]? = some .effect := by
        simpa [hlen] using hi
      have hvar : Effect.WF (fun op => sig op ≠ none) Δ
          (Effect.var (i - args.length)) := by
        constructor
        · simp [Effect.var]
        · intro μ hμ
          have heq : μ = i - args.length := by
            simpa [Effect.var] using hμ
          simpa [heq] using hi'
      simpa [KindSubst.many, hnone] using hvar

/-- 整形式な多相操作宣言の引数型は混合引数列で具体化できる。 -/
theorem Ty.WF.instantiateMany {sig : Signature}
    {ks : List Kind} {σ : Ty}
    (h : Ty.WF sig ks σ) {Δ : List Kind}
    {args : List Arg}
    (hargs : List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) ks args) :
    Ty.WF sig Δ (σ.instantiateMany args) :=
  h.subst_preserves (KindSubst.many args) (KindSubst.many_valid hargs)

/-- kind 付き引数の改名は kind を保存する。 -/
theorem Arg.WF.rename_preserves {sig : Signature}
    {Δ Δ' : List Kind} {κ : Kind} {arg : Arg}
    (h : Arg.WF sig Δ κ arg) (ρ : Nat → Nat)
    (hρ : RenValid Δ Δ' ρ) :
    Arg.WF sig Δ' κ (arg.rename ρ) := by
  cases κ <;> cases arg
  · exact Ty.WF.rename_preserves h ρ hρ
  · cases h
  · cases h
  · exact Effect.WF.rename_preserves h hρ

/-- kind 付き引数の置換は kind を保存する。 -/
theorem Arg.WF.subst_preserves {sig : Signature}
    {Δ Δ' : List Kind} {κ : Kind} {arg : Arg}
    (h : Arg.WF sig Δ κ arg) (τ : KindSubst)
    (hτ : SubstValid sig Δ Δ' τ) :
    Arg.WF sig Δ' κ (arg.subst τ) := by
  cases κ <;> cases arg
  · exact Ty.WF.subst_preserves h τ hτ
  · cases h
  · cases h
  · exact Effect.WF.subst_preserves h hτ

/-- 混合引数列の改名は各位置の kind を保存する。 -/
theorem Arg.WF.renameMany {sig : Signature}
    {Δ Δ' : List Kind} {ks : List Kind} {args : List Arg}
    (h : List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) ks args)
    (ρ : Nat → Nat) (hρ : RenValid Δ Δ' ρ) :
    List.Forall₂ (fun κ θ => Arg.WF sig Δ' κ θ)
      ks (args.map (Arg.rename ρ)) := by
  induction h with
  | nil => exact .nil
  | cons h₀ _ ih => exact .cons (h₀.rename_preserves ρ hρ) ih

/-- 混合引数列の置換は各位置の kind を保存する。 -/
theorem Arg.WF.substMany {sig : Signature}
    {Δ Δ' : List Kind} {ks : List Kind} {args : List Arg}
    (h : List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) ks args)
    (τ : KindSubst) (hτ : SubstValid sig Δ Δ' τ) :
    List.Forall₂ (fun κ θ => Arg.WF sig Δ' κ θ)
      ks (args.map (Arg.subst τ)) := by
  induction h with
  | nil => exact .nil
  | cons h₀ _ ih => exact .cons (h₀.subst_preserves τ hτ) ih

/-- 操作宣言の型の具体化と外側の改名は交換する。 -/
theorem Ty.instantiateMany_rename {sig : Signature}
    {ks : List Kind} {body : Ty}
    (hbody : Ty.WF sig ks body) {Δ : List Kind}
    {args : List Arg}
    (hargs : List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) ks args)
    (ρ : Nat → Nat) :
    (body.instantiateMany args).rename ρ =
      body.instantiateMany (args.map (Arg.rename ρ)) := by
  rw [Ty.instantiateMany, Ty.subst_rename]
  apply hbody.subst_congr
  have hlen : ks.length = args.length := hargs.length_eq
  constructor
  · intro i hi
    obtain ⟨hidx, hk⟩ := List.getElem?_eq_some_iff.mp hi
    have hargIdx : i < args.length := by omega
    have harg := hargs.get hidx hargIdx
    change Arg.WF sig Δ ks[i] args[i] at harg
    rw [hk] at harg
    cases hθ : args[i] with
    | type σ =>
        simp [KindSubst.many, List.getElem?_map, hargIdx, hθ, Arg.rename]
    | effect ε =>
        have hfalse : False := by simp [Arg.WF, hθ] at harg
        exact hfalse.elim
  · intro i hi
    obtain ⟨hidx, hk⟩ := List.getElem?_eq_some_iff.mp hi
    have hargIdx : i < args.length := by omega
    have harg := hargs.get hidx hargIdx
    change Arg.WF sig Δ ks[i] args[i] at harg
    rw [hk] at harg
    cases hθ : args[i] with
    | type σ =>
        have hfalse : False := by simp [Arg.WF, hθ] at harg
        exact hfalse.elim
    | effect ε =>
        simp [KindSubst.many, List.getElem?_map, hargIdx, hθ, Arg.rename]

/-- 操作宣言の型の具体化と外側の置換は交換する。 -/
theorem Ty.instantiateMany_subst {sig : Signature}
    {ks : List Kind} {body : Ty}
    (hbody : Ty.WF sig ks body) {Δ : List Kind}
    {args : List Arg}
    (hargs : List.Forall₂ (fun κ θ => Arg.WF sig Δ κ θ) ks args)
    (τ : KindSubst) :
    (body.instantiateMany args).subst τ =
      body.instantiateMany (args.map (Arg.subst τ)) := by
  rw [Ty.instantiateMany, Ty.subst_subst]
  apply hbody.subst_congr
  have hlen : ks.length = args.length := hargs.length_eq
  constructor
  · intro i hi
    obtain ⟨hidx, hk⟩ := List.getElem?_eq_some_iff.mp hi
    have hargIdx : i < args.length := by omega
    have harg := hargs.get hidx hargIdx
    change Arg.WF sig Δ ks[i] args[i] at harg
    rw [hk] at harg
    cases hθ : args[i] with
    | type σ =>
        simp [KindSubst.many, List.getElem?_map, hargIdx, hθ, Arg.subst]
    | effect ε =>
        have hfalse : False := by simp [Arg.WF, hθ] at harg
        exact hfalse.elim
  · intro i hi
    obtain ⟨hidx, hk⟩ := List.getElem?_eq_some_iff.mp hi
    have hargIdx : i < args.length := by omega
    have harg := hargs.get hidx hargIdx
    change Arg.WF sig Δ ks[i] args[i] at harg
    rw [hk] at harg
    cases hθ : args[i] with
    | type σ =>
        have hfalse : False := by simp [Arg.WF, hθ] at harg
        exact hfalse.elim
    | effect ε =>
        simp [KindSubst.many, List.getElem?_map, hargIdx, hθ,
          Arg.subst, Effect.substKind]

/-- n 個持ち上げた型を n 個の混合引数で具体化すると元に戻る。 -/
theorem Ty.shift_instantiateMany (σ : Ty) (args : List Arg)
    (n : Nat) (hlen : args.length = n) :
    (σ.rename (fun i => i + n)).subst
      (KindSubst.many args) = σ := by
  rw [Ty.rename_subst]
  have hmap :
      { types := fun i => (KindSubst.many args).types (i + n)
        effects := fun i => (KindSubst.many args).effects (i + n) } =
      KindSubst.identity := by
    apply congrArg₂ KindSubst.mk
    · funext i
      simp [KindSubst.many, hlen]
    · funext i
      simp [KindSubst.many, hlen]
  rw [hmap, Ty.subst_id]

/-- n 個持ち上げた効果を n 個の混合引数で具体化すると元に戻る。 -/
theorem Effect.shift_instantiateMany (ε : Effect)
    (args : List Arg) (n : Nat) (hlen : args.length = n) :
    (ε.rename (fun i => i + n)).subst
      (KindSubst.many args).effects = ε := by
  rw [Effect.rename_subst]
  have hmap :
      (fun i => (KindSubst.many args).effects (i + n)) =
      Effect.var := by
    funext i
    simp [KindSubst.many, hlen]
  rw [hmap, Effect.subst_id]

/-- Γ↑ⁿ を同じ長さの混合引数で具体化すると Γ に戻る。 -/
theorem TermCtx.liftKind_instantiateMany (Γ : TermCtx)
    (args : List Arg) (n : Nat) (hlen : args.length = n) :
    (Γ.liftKind n).map
      (Ty.subst (KindSubst.many args)) = Γ := by
  simp only [TermCtx.liftKind, List.map_map]
  have hfn :
      Ty.subst (KindSubst.many args) ∘
          Ty.rename (fun i => i + n) = id := by
    funext σ
    exact Ty.shift_instantiateMany σ args n hlen
  rw [hfn]
  simp

/-- 空効果は任意の kind 環境で整形式。 -/
theorem Effect.WF.empty {sig : Signature} {Δ : List Kind} :
    Effect.WF (fun op => sig op ≠ none) Δ ∅ := by
  constructor <;> simp

/-- 宣言された操作の単元効果は整形式。 -/
theorem Effect.WF.singleton {sig : Signature} {Δ : List Kind}
    {op : Op} (h : sig op ≠ none) :
    Effect.WF (fun op => sig op ≠ none) Δ
      (Effect.singleton op) := by
  constructor
  · intro op' hop
    have heq : op' = op := by simpa using hop
    simpa [heq] using h
  · simp

/-- 整形式な効果の和集合は整形式。 -/
theorem Effect.WF.union {sig : Signature} {Δ : List Kind}
    {ε η : Effect}
    (hε : Effect.WF (fun op => sig op ≠ none) Δ ε)
    (hη : Effect.WF (fun op => sig op ≠ none) Δ η) :
    Effect.WF (fun op => sig op ≠ none) Δ (ε ∪ η) := by
  constructor
  · intro op hop
    rcases Finset.mem_union.mp hop with hl | hr
    · exact hε.1 op hl
    · exact hη.1 op hr
  · intro μ hμ
    rcases Finset.mem_union.mp hμ with hl | hr
    · exact hε.2 μ hl
    · exact hη.2 μ hr

/-- kind の一致する単一引数は束縛子の除去として有効。 -/
theorem KindSubst.single_valid {sig : Signature}
    {Δ : List Kind} {κ : Kind} {arg : Arg}
    (harg : Arg.WF sig Δ κ arg) :
    SubstValid sig (κ :: Δ) Δ (KindSubst.single arg) := by
  constructor
  · intro i hi
    cases i with
    | zero =>
        have hk : κ = .type := by simpa using hi
        subst κ
        cases arg with
        | type σ => exact harg
        | effect ε => cases harg
    | succ j =>
        have hj : Δ[j]? = some .type := by simpa using hi
        cases arg <;> exact Ty.WF.var hj
  · intro i hi
    cases i with
    | zero =>
        have hk : κ = .effect := by simpa using hi
        subst κ
        cases arg with
        | type σ => cases harg
        | effect ε => exact harg
    | succ j =>
        have hj : Δ[j]? = some .effect := by simpa using hi
        cases arg
        all_goals
          constructor
          · simp [KindSubst.single, Effect.var]
          · intro μ hμ
            have heq : μ = j := by
              simpa [KindSubst.single, Effect.var] using hμ
            simpa [heq] using hj

/-- ∀β::κ の本体は、kind の一致する θ で具体化しても整形式。 -/
theorem Ty.WF.instantiate {sig : Signature}
    {Δ : List Kind} {κ : Kind} {body : Ty}
    (hbody : Ty.WF sig (κ :: Δ) body)
    {arg : Arg} (harg : Arg.WF sig Δ κ arg) :
    Ty.WF sig Δ (body.instantiate arg) :=
  hbody.subst_preserves (KindSubst.single arg) (KindSubst.single_valid harg)

/-- 型付けされた式の結果型と評価効果はともに well-kinded。 -/
theorem Typing.wf {sig : Signature}
    (hsigwf : Signature.WF sig)
    {Δ : List Kind} {Γ : TermCtx} {e : Expr}
    {σ : Ty} {ε : Effect}
    (ht : Typing sig Δ Γ e σ ε) :
    Ty.WF sig Δ σ ∧
      Effect.WF (fun op => sig op ≠ none) Δ ε := by
  induction ht with
  | var _ hσ =>
      exact ⟨hσ, Effect.WF.empty⟩
  | lam hA _ ih =>
      exact ⟨.arr hA ih.2 ih.1, Effect.WF.empty⟩
  | app _ _ ihF ihX =>
      obtain ⟨hFty, hFeff⟩ := ihF
      obtain ⟨_, hXeff⟩ := ihX
      cases hFty with
      | arr _ hbody hresult =>
          exact ⟨hresult, (hFeff.union hXeff).union hbody⟩
  | tlam _ ih =>
      exact ⟨.all ih.1, Effect.WF.empty⟩
  | tapp _ harg ih =>
      obtain ⟨hFty, hFeff⟩ := ih
      cases hFty with
      | all hbody =>
          exact ⟨hbody.instantiate harg, hFeff⟩
  | @perform Δ Γ op decl args arg ε hlookup hargs _ ih =>
      have hdecl := hsigwf op decl hlookup
      exact ⟨hdecl.2.instantiateMany hargs,
        (Effect.WF.singleton (by rw [hlookup]; simp)).union ih.2⟩
  | handle _ _ _ _ _ _ ihBody ihRet ihClause =>
      exact ihRet
  | sub _ _ hσ hε _ ih =>
      exact ⟨hσ, hε⟩

/-- kind 付き型適用と外側の変数改名は交換する。 -/
theorem Ty.instantiate_rename {sig : Signature}
    {Δ : List Kind} {κ : Kind} {body : Ty}
    (hbody : Ty.WF sig (κ :: Δ) body)
    {arg : Arg} (harg : Arg.WF sig Δ κ arg)
    (ρ : Nat → Nat) :
    (body.instantiate arg).rename ρ =
      (body.rename (liftRen ρ)).instantiate (arg.rename ρ) := by
  simp only [Ty.instantiate, Ty.subst_rename, Ty.rename_subst]
  apply hbody.subst_congr
  constructor
  · intro i hi
    cases i with
    | zero =>
        have hk : κ = .type := by simpa using hi
        subst κ
        cases arg with
        | type σ => rfl
        | effect ε => cases harg
    | succ j =>
        cases arg
        all_goals rfl
  · intro i hi
    cases i with
    | zero =>
        have hk : κ = .effect := by simpa using hi
        subst κ
        cases arg with
        | type σ => cases harg
        | effect ε => rfl
    | succ j =>
        cases arg
        all_goals rfl

/-- 型を一つ持ち上げてから任意の引数で具体化すると元に戻る。 -/
theorem Ty.shift_instantiate (σ : Ty) (arg : Arg) :
    (σ.rename Nat.succ).instantiate arg = σ := by
  rw [Ty.instantiate, Ty.rename_subst]
  have hmap :
      { types := fun i => (KindSubst.single arg).types (i + 1)
        effects := fun i => (KindSubst.single arg).effects (i + 1) } =
      KindSubst.identity := by
    cases arg <;>
      apply congrArg₂ KindSubst.mk <;>
      funext i <;> rfl
  rw [hmap, Ty.subst_id]

/-- 効果を一つ持ち上げてから具体化すると元に戻る。 -/
theorem Effect.shift_instantiate (ε : Effect) (arg : Arg) :
    (ε.rename Nat.succ).subst
      (KindSubst.single arg).effects = ε := by
  rw [Effect.rename_subst]
  have hmap :
      (fun i => (KindSubst.single arg).effects (i + 1)) =
      Effect.var := by
    cases arg <;> rfl
  rw [hmap, Effect.subst_id]

/-- kind 付き型適用と外側の同時置換は交換する。 -/
theorem Ty.instantiate_subst {sig : Signature}
    {Δ : List Kind} {κ : Kind} {body : Ty}
    (hbody : Ty.WF sig (κ :: Δ) body)
    {arg : Arg} (harg : Arg.WF sig Δ κ arg)
    (τ : KindSubst) :
    (body.instantiate arg).subst τ =
      (body.subst τ.lift).instantiate (arg.subst τ) := by
  simp only [Ty.instantiate, Ty.subst_subst]
  apply hbody.subst_congr
  constructor
  · intro i hi
    cases i with
    | zero =>
        have hk : κ = .type := by simpa using hi
        subst κ
        cases arg with
        | type σ => rfl
        | effect ε => cases harg
    | succ j =>
        cases arg
        all_goals
          change τ.types j =
            ((τ.types j).rename Nat.succ).instantiate _
          exact (Ty.shift_instantiate _ _).symm
  · intro i hi
    cases i with
    | zero =>
        have hk : κ = .effect := by simpa using hi
        subst κ
        cases arg with
        | type σ => cases harg
        | effect ε =>
            simp only [KindSubst.single, KindSubst.lift, Arg.subst,
              Effect.substKind, Effect.subst_var]
    | succ j =>
        cases arg with
        | type σ =>
            simpa only [KindSubst.single, KindSubst.lift, Arg.subst,
              Effect.subst_var] using
              (Effect.shift_instantiate (τ.effects j)
                (Arg.type (σ.subst τ))).symm
        | effect ε =>
            simpa only [KindSubst.single, KindSubst.lift, Arg.subst,
              Effect.substKind, Effect.subst_var] using
              (Effect.shift_instantiate (τ.effects j)
                (Arg.effect (ε.subst τ.effects))).symm

end SystemFXi.Poly
