import HMX.LocallyNameless.Proofs.GenerationSupport

namespace HMX.LN.Proofs

theorem derivationWF (h : Derivation S M C Γ t s d) : JudgmentWF S C Γ t s := by
  cases h <;> assumption

theorem alternateWF (h : AlternateTyping S M C Γ t T) : JudgmentWF S C Γ t (.mono T) := by
  cases h <;> assumption

theorem envBinderEqDpi (Γ Δ : Env) (h : Γ.BinderEq Δ) : Γ.dpi = Δ.dpi := by
  have hm : Γ.map Prod.fst = Δ.map Prod.fst := by
    induction h with
    | nil => rfl
    | cons hp ht ih => simp only [List.map_cons, hp.1, ih]
  exact congrArg List.toFinset hm

theorem exprFpiOpenSubset (t : Expr) (x : Id) (d : Nat) :
    t.fpi ⊆ (Expr.openAt d (.ident (.free x)) t).fpi := by
  induction t generalizing d with
  | ident v =>
      cases v with
      | free y => exact Finset.Subset.rfl
      | bound i => exact Finset.empty_subset _
  | lam t ih => exact ih (d+1)
  | app t u iht ihu => exact Finset.union_subset_union (iht d) (ihu d)
  | letE t u iht ihu => exact Finset.union_subset_union (iht d) (ihu (d+1))

theorem cofiniteScope (Γ : Env) (t : Expr) (s : Scheme) (L : Finset Nat)
    (h : ∀ z ∉ L, (Expr.openAt 0 (.ident (.free (.var z))) t).fpi ⊆ (Env.dpi (Γ ++ [(.var z,s)]))) :
    t.fpi ⊆ Γ.dpi := by
  intro x hx
  have hex : ∃ z, z ∉ L ∧ x ≠ Id.var z := by
    cases x with
    | var y =>
        obtain ⟨z,hz⟩ := Finset.exists_notMem (insert y L)
        simp only [Finset.mem_insert, not_or] at hz
        exact ⟨z, hz.2, by simpa using Ne.symm hz.1⟩
    | loc y => obtain ⟨z,hz⟩ := Finset.exists_notMem L; exact ⟨z,hz,by simp⟩
    | const y => obtain ⟨z,hz⟩ := Finset.exists_notMem L; exact ⟨z,hz,by simp⟩
  obtain ⟨z,hz,hxz⟩ := hex
  have hh := h z hz (exprFpiOpenSubset t (.var z) 0 hx)
  simpa [Env.dpi, hxz] using hh

theorem derivationScope (h : Derivation S M C Γ t s d) : t.fpi ⊆ Γ.dpi := by
  induction h with
  | var hw hl _ =>
      intro x hx
      simp only [Expr.fpi, Finset.mem_singleton] at hx
      subst x
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,lookupMember _ _ _ hl,rfl⟩)
  | @abs C Γ t T U d L hw hd ih => exact cofiniteScope Γ t (.mono T) L ih
  | app hw ht hu iht ihu => exact Finset.union_subset iht ihu
  | letE L hw ht hu iht ihu => exact Finset.union_subset iht (cofiniteScope _ _ _ L ihu)
  | gen hw hn hf hd ih => exact ih
  | inst hw hn hd ih => exact ih
  | sub hw hd he ih => exact ih
  | exists_ hw hn hk hf hd ih => exact ih
  | convert hw hd he hΓ hs ih => simpa only [envBinderEqDpi _ _ hΓ] using ih

theorem derivationRealizable (hM : M.Requirements S) (h : Derivation S M C Γ t s d) :
    Entails S M C s.exists_ := by
  induction h with
  | var hw hl he => exact he
  | abs L hw hd ih => exact fun ρ ι _ _ _ => monoExists S M ρ ι _
  | app hw ht hu iht ihu => exact fun ρ ι _ _ _ => monoExists S M ρ ι _
  | letE L hw ht hu iht ihu => exact fun ρ ι _ _ _ => monoExists S M ρ ι _
  | gen hw hn hf hd ih => exact fun _ _ _ _ he => he.2
  | inst hw hn hd ih => exact fun ρ ι _ _ _ => monoExists S M ρ ι _
  | sub hw hd he ih => exact fun ρ ι _ _ _ => monoExists S M ρ ι _
  | @exists_ Γ t s xs C d hw hn hk hf hd ih =>
      intro ρ ι hρ hι he
      have hc := (derivationWF hd).1
      obtain ⟨vs,hv,he⟩ := (existsNamesHolds S M ρ ι xs C hc).mp he
      have hr := ih _ ι (assignBlockValid S M ρ xs vs hρ hv) hι he
      apply (holdsAssignBlock S M hM ρ ι xs vs s.exists_ hρ hι hv (schemeExistsWF S s hw.2.2.2.1) ?_).mp hr
      exact Finset.disjoint_left.mpr (fun X hx hX => Finset.disjoint_left.mp hf hx
        (Finset.mem_union_right _ (schemeExistsFv s hX)))
  | @convert D Δ t r C Γ s d hw hd he hΓ hs ih =>
      intro ρ ι hρ hι hD
      have hC := he.2 ρ ι hρ hι hD
      have hnon := (schemeExistsNonempty S M hM ρ ι hρ s (derivationWF hd).2.2.2.1).mp (ih ρ ι hρ hι hC)
      apply (schemeExistsNonempty S M hM ρ ι hρ r hw.2.2.2.1).mpr
      have heq := schemeBinderEq S M ρ ι s r hs (fun _ => ρ (0,0)) (fun _ => ∅)
      change s.denote S M ρ ι = r.denote S M ρ ι at heq
      simpa only [heq] using hnon

theorem typingProperties (S : Signature) (M : Model) (I : Set Nat) : HMX.LN.typingProperties S M I := by
  intro hF C Γ t s ⟨d,hd⟩
  exact ⟨derivationWF hd, derivationScope hd, derivationRealizable hF.1 hd⟩

def typeRename (p : TVar ≃ TVar) : Subst := fun X => .free (p X)

theorem typeRenameClosed (p : TVar ≃ TVar) : ∀ X, (typeRename p X).LCAt 0 := by
  intro X; simp [typeRename, Ty.LCAt]

theorem idxOfMapEquiv (p : TVar ≃ TVar) (xs : List TVar) (X : TVar) :
    (xs.map p).idxOf (p X) = xs.idxOf X := by
  induction xs with
  | nil => rfl
  | cons Y xs ih => simp [List.idxOf_cons, p.injective.eq_iff, ih]

theorem tyRenameKind (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (T : Ty) (ks : List Nat) (h : T.HasKind S ks k) : (T.subst (typeRename p)).HasKind S ks k := by
  induction T using tyInduction generalizing k with
  | hf X => cases h with | free hx => simpa [Ty.subst, typeRename, hk] using (Ty.HasKind.free (S := S) (ks := ks) (X := p X) (by simpa [hk] using hx))
  | hb i => simpa [Ty.subst] using h
  | hc f ts ih =>
      cases h with
      | con hf hs =>
          simp only [Ty.subst]
          exact .con hf (List.forall₂_map_left_iff.mpr (forall₂ImplMem hs (fun U hu q hq => ih U hu hq)))

theorem typeRenameKinds (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1) (xs : List TVar) :
    (xs.map p).map Prod.fst = xs.map Prod.fst := by simp [List.map_map, Function.comp_def, hk]

theorem typeRenameCloseFree (p : TVar ≃ TVar) (xs : List TVar) (n : Nat) (X : TVar) :
    ((Ty.free X).closeAt n xs).subst (typeRename p) = (typeRename p X).closeAt n (xs.map p) := by
  by_cases hx : X ∈ xs
  · simp [Ty.closeAt, Ty.subst, typeRename, hx, idxOfMapEquiv]
  · simp [Ty.closeAt, Ty.subst, typeRename, hx]

theorem renameExistsNames (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1) (xs : List TVar) (C : Constraint) :
    (C.existsNames xs).subst (typeRename p) = (C.subst (typeRename p)).existsNames (xs.map p) :=
  substExistsRename C xs (xs.map p) _ _ (typeRenameKinds p hk xs).symm (fun n X _ => typeRenameCloseFree p xs n X)

theorem renameGeneralize (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1) (xs : List TVar) (C : Constraint) (T : Ty) :
    (Scheme.generalize xs C T).subst (typeRename p) =
      Scheme.generalize (xs.map p) (C.subst (typeRename p)) (T.subst (typeRename p)) :=
  substGeneralizeRename C T xs (xs.map p) _ _ (typeRenameKinds p hk xs).symm (fun n X _ => typeRenameCloseFree p xs n X)

theorem tyRenameFv (p : TVar ≃ TVar) (T : Ty) :
    (T.subst (typeRename p)).fv = T.fv.image p := by
  induction T using tyInduction with
  | hf X => simp [Ty.subst, typeRename, Ty.fv]
  | hb i => simp [Ty.subst, Ty.fv]
  | hc f ts ih =>
      ext X
      simp only [Ty.subst, Ty.fv, List.map_map, memUnionFold, Function.comp_apply, Finset.mem_image]
      constructor
      · rintro ⟨U,hu,hx⟩
        rw [ih U hu] at hx
        obtain ⟨Y,hy,rfl⟩ := Finset.mem_image.mp hx
        exact ⟨Y,⟨U,hu,hy⟩,rfl⟩
      · rintro ⟨Y,⟨U,hu,hy⟩,rfl⟩
        exact ⟨U,hu,by rw [ih U hu]; exact Finset.mem_image.mpr ⟨Y,hy,rfl⟩⟩

theorem constraintRenameFv (p : TVar ≃ TVar) (C : Constraint) (n : Nat) :
    (C.mapTypes (fun _ T => T.subst (typeRename p)) n).fv = C.fv.image p := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ n, (C.mapTypes (fun _ T => T.subst (typeRename p)) n).fv = C.fv.image p)
    (motive_2 := fun s => ∀ n, (s.mapTypes (fun _ T => T.subst (typeRename p)) n).fv = s.fv.image p)
    (by intros; simp [Constraint.mapTypes, Constraint.fv])
    (by intros; simp [Constraint.mapTypes, Constraint.fv])
    (by
      intro q ts n
      ext X
      simp only [Constraint.mapTypes, Constraint.fv, List.map_map, memUnionFold, Function.comp_apply, tyRenameFv, Finset.mem_image]
      constructor
      · rintro ⟨T,ht,Y,hy,hxy⟩; exact ⟨Y,⟨T,ht,hy⟩,hxy⟩
      · rintro ⟨Y,⟨T,ht,hy⟩,hxy⟩; exact ⟨T,ht,Y,hy,hxy⟩)
    (by intro C D ihC ihD n; simp [Constraint.mapTypes, Constraint.fv, ihC, ihD, Finset.image_union])
    (by intro ks C ih n; exact ih _)
    (by intro b s C ihs ihC n; simp [Constraint.mapTypes, Constraint.fv, ihs, ihC, Finset.image_union])
    (by intro x T n; exact tyRenameFv p T)
    (by intro ks C T ih n; simp [Scheme.mapTypes, Scheme.fv, ih, tyRenameFv, Finset.image_union]) C n

theorem schemeRenameFv (p : TVar ≃ TVar) (s : Scheme) :
    (s.subst (typeRename p)).fv = s.fv.image p := by
  cases s
  simp [Scheme.subst, Scheme.mapTypes, Scheme.fv, constraintRenameFv, tyRenameFv, Finset.image_union]

theorem schemeSubstFpi (θ : Subst) (s : Scheme) : (s.subst θ).fpi = s.fpi := by
  cases s; exact constraintMapTypesFpi _ _ _

theorem envSubstFpi (θ : Subst) (Γ : Env) : (Γ.subst θ).fpi = Γ.fpi := by
  induction Γ with
  | nil => rfl
  | cons q Γ ih => simpa [Env.subst, Env.fpi, schemeSubstFpi] using congrArg (fun F => q.2.fpi ∪ F) ih

theorem envRenameFv (p : TVar ≃ TVar) (Γ : Env) :
    (Γ.subst (typeRename p)).fv = Γ.fv.image p := by
  induction Γ with
  | nil => simp [Env.subst, Env.fv]
  | cons q Γ ih =>
      change (q.2.subst (typeRename p)).fv ∪ (Env.subst (typeRename p) Γ).fv = (q.2.fv ∪ Env.fv Γ).image p
      rw [schemeRenameFv, ih, Finset.image_union]

theorem tyRenameClosed (T : Ty) (q : Nat → Nat) (n : Nat) (h : T.LCAt 0) : T.renameAt n q = T := by
  induction T using tyInduction with
  | hf X => simp [Ty.renameAt]
  | hb i => simp [Ty.LCAt] at h
  | hc f ts ih =>
      simp only [Ty.renameAt]
      simp only [Ty.LCAt] at h
      congr 1
      exact (List.map_congr_left (g := id) (fun U hu => ih U hu (h U hu))).trans (List.map_id ts)

theorem tySubstRename (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0) (T : Ty) (q : Nat → Nat) (n : Nat) :
    (T.renameAt n q).subst θ = (T.subst θ).renameAt n q := by
  induction T using tyInduction with
  | hf X => simpa only [Ty.renameAt, Ty.subst] using (tyRenameClosed (θ X) q n (hθ X)).symm
  | hb i => simp [Ty.renameAt, Ty.subst]
  | hc f ts ih =>
      simp only [Ty.renameAt, Ty.subst, List.map_map]
      congr 1
      exact List.map_congr_left (fun U hu => ih U hu)

theorem constraintSubstRename (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0) (C : Constraint) (q : Nat → Nat) :
    (C.mapTypes (fun n T => T.renameAt n q) 0).subst θ =
      (C.subst θ).mapTypes (fun n T => T.renameAt n q) 0 :=
  constraintMapTypesCommute _ _ _ _ (fun n T => tySubstRename θ hθ T q n) C 0

theorem constraintBinderEqSubst (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0)
    (C D : Constraint) (h : C.BinderEq D) : (C.subst θ).BinderEq (D.subst θ) := by
  apply Constraint.BinderEq.rec
    (motive_1 := fun C D _ => (C.subst θ).BinderEq (D.subst θ))
    (motive_2 := fun s r _ => (s.subst θ).BinderEq (r.subst θ))
    (by intros; exact .refl)
    (by intro C D h ih; exact .symm ih)
    (by intro C D E h₁ h₂ ih₁ ih₂; exact .trans ih₁ ih₂)
    (by intro C C' D D' h₁ h₂ ih₁ ih₂; exact .conj ih₁ ih₂)
    (by
      intro ks ls q D C hq h ih
      simp only [Constraint.subst, Constraint.mapTypes]
      simp only [constraintSubstAt]
      apply Constraint.BinderEq.exists_ hq
      simpa only [constraintSubstRename θ hθ] using ih)
    (by intro s r C D b hs hC ihs ihC; exact .def_ ihs ihC)
    (by intros; exact .refl)
    (by intro s r h ih; exact .symm ih)
    (by intro s r u h₁ h₂ ih₁ ih₂; exact .trans ih₁ ih₂)
    (by
      intro ks ls q D U C T hq hC hT ih
      simp only [Scheme.subst, Scheme.mapTypes, constraintSubstAt]
      exact .all hq (by simpa only [constraintSubstRename θ hθ] using ih)
        (by rw [← tySubstRename θ hθ, hT])) h

theorem schemeBinderEqSubst (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0)
    (s r : Scheme) (h : s.BinderEq r) : (s.subst θ).BinderEq (r.subst θ) := by
  apply Scheme.BinderEq.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun s r _ => (s.subst θ).BinderEq (r.subst θ))
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; trivial) (by intros; trivial) (by intros; trivial)
    (by intros; exact .refl)
    (by intro s r h ih; exact .symm ih)
    (by intro s r u h₁ h₂ ih₁ ih₂; exact .trans ih₁ ih₂)
    (by
      intro ks ls q D U C T hq hC hT _
      simp only [Scheme.subst, Scheme.mapTypes, constraintSubstAt]
      exact .all hq (by simpa only [constraintSubstRename θ hθ] using constraintBinderEqSubst θ hθ _ _ hC)
        (by rw [← tySubstRename θ hθ, hT])) h

theorem schemeRenameWF (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (s : Scheme) (hs : s.WF S ks d) : (s.subst (typeRename p)).WF S ks d := by
  cases s with
  | all bs C T =>
      exact ⟨hs.1, constraintMapTypesPreservesWF S _ (fun ks _ T k ht => tyRenameKind p hk T ks ht) C _ _ _ hs.2.1,
        tyRenameKind p hk T _ hs.2.2⟩

theorem judgmentRenameWF (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (h : JudgmentWF S C Γ t s) :
    JudgmentWF S (C.subst (typeRename p)) (Γ.subst (typeRename p)) t (s.subst (typeRename p)) := by
  refine ⟨constraintMapTypesPreservesWF S _ (fun ks _ T k ht => tyRenameKind p hk T ks ht) C [] 0 0 h.1,
    ?_, h.2.2.1, schemeRenameWF p hk s h.2.2.2.1, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact schemeRenameWF p hk r.2 (h.2.1 r hr)
  · simpa only [Constraint.subst, constraintMapTypesFpi] using h.2.2.2.2.1
  · simpa only [envSubstFpi] using h.2.2.2.2.2.1
  · simpa only [schemeSubstFpi] using h.2.2.2.2.2.2

theorem renameHolds (p : TVar ≃ TVar) (C : Constraint) (hw : C.WF S [] 0)
    (ρ : Assignment M) (ι : GroundEnv M) :
    (C.subst (typeRename p)).Holds S M ρ ι ↔ C.Holds S M (fun X => ρ (p X)) ι := by
  have hh := constraintEvalSubst S M (typeRename p) (typeRenameClosed p) ρ ι C 0 (fun _ => ρ (0,0)) (fun _ => ∅)
  simp only [typeRename, Ty.eval, Ty.evalAt] at hh
  exact hh.trans (holdsClosed S M _ ι C hw _ _)

theorem entailsRename (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (C D : Constraint) (hc : C.WF S [] 0) (hd : D.WF S [] 0) (h : Entails S M C D) :
    Entails S M (C.subst (typeRename p)) (D.subst (typeRename p)) := by
  intro ρ ι hρ hι hC
  apply (renameHolds p D hd ρ ι).mpr
  exact h _ ι (fun X hx => by simpa only [hk] using hρ (p X) (by simpa only [hk] using hx)) hι
    ((renameHolds p C hc ρ ι).mp hC)

theorem envBinderEqSubst (θ : Subst) (hθ : ∀ X, (θ X).LCAt 0)
    (Γ Δ : Env) (h : Γ.BinderEq Δ) : (Γ.subst θ).BinderEq (Δ.subst θ) := by
  induction h with
  | nil => exact .nil
  | cons hp ht ih => exact .cons ⟨hp.1, schemeBinderEqSubst θ hθ _ _ hp.2⟩ ih

theorem lookupSubst (θ : Subst) (Γ : Env) (x : Id) :
    lookup (Γ.subst θ) x = (lookup Γ x).map (Scheme.subst θ) := by
  induction Γ with
  | nil => rfl
  | cons q Γ ih =>
      rcases q with ⟨y,s⟩
      change lookup ((y,s.subst θ)::Env.subst θ Γ) x = _
      rw [lookupCons, lookupCons, ih]
      cases hl : lookup Γ x with
      | some r => rfl
      | none => by_cases hxy : x = y <;> simp [hxy]

theorem renameDisjoint (p : TVar ≃ TVar) (xs : List TVar) (F : Vars) (h : Disjoint xs.toFinset F) :
    Disjoint (xs.map p).toFinset (F.image p) := by
  apply Finset.disjoint_left.mpr
  intro Z hz hF
  obtain ⟨X,hX,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hz)
  obtain ⟨Y,hY,he⟩ := Finset.mem_image.mp hF
  have he' := p.injective he
  subst Y
  exact Finset.disjoint_left.mp h (List.mem_toFinset.mpr hX) hY

theorem schemeExistsSubst (θ : Subst) (s : Scheme) :
    s.exists_.subst θ = (s.subst θ).exists_ := by cases s; rfl

theorem derivationRename (hS : S.Valid) (p : TVar ≃ TVar) (hk : ∀ X, (p X).1 = X.1)
    (h : Derivation S M C Γ t s d) :
    Derivation S M (C.subst (typeRename p)) (Γ.subst (typeRename p)) t (s.subst (typeRename p)) d := by
  induction h with
  | var hw hl he =>
      refine .var (judgmentRenameWF p hk hw) ?_ ?_
      · rw [lookupSubst, hl]; rfl
      · rw [← schemeExistsSubst]
        exact entailsRename p hk _ _ hw.1 (schemeExistsWF S _ hw.2.2.2.1) he
  | abs L hw hd ih =>
      simp only [substMono, Ty.arrow, Ty.subst, List.map_cons, List.map_nil]
      apply Derivation.abs L
      · simpa only [substMono, Ty.arrow, Ty.subst, List.map_cons, List.map_nil] using judgmentRenameWF p hk hw
      · intro z hz
        simpa only [Env.subst, List.map_append, List.map_cons, List.map_nil, substMono] using ih z hz
  | app hw ht hu iht ihu =>
      simp only [substMono] at *
      apply Derivation.app (judgmentRenameWF p hk hw) _ ihu
      simpa only [Ty.arrow, Ty.subst, List.map_cons, List.map_nil] using iht
  | letE L hw ht hu iht ihu =>
      simp only [substMono] at *
      apply Derivation.letE L (judgmentRenameWF p hk hw) iht
      intro z hz
      simpa only [Env.subst, List.map_append, List.map_cons, List.map_nil, substMono] using ihu z hz
  | @gen C Γ t xs D T d hw hn hf hd ih =>
      simp only [substConj, renameExistsNames p hk, renameGeneralize p hk]
      apply Derivation.gen
      · simpa only [substConj, renameExistsNames p hk, renameGeneralize p hk] using judgmentRenameWF p hk hw
      · exact hn.map p.injective
      · simpa only [Finset.image_union, ← constraintRenameFv p C 0, ← envRenameFv p Γ, Constraint.subst] using renameDisjoint p xs (C.fv ∪ Γ.fv) hf
      · simpa only [substConj, substMono] using ih
  | inst hw hn hd ih =>
      simp only [substConj, substMono]
      apply Derivation.inst (judgmentRenameWF p hk hw) (hn.map p.injective)
      simpa only [renameGeneralize p hk, Constraint.subst] using ih
  | sub hw hd he ih =>
      simp only [substMono] at *
      refine Derivation.sub (judgmentRenameWF p hk hw) ih ?_
      rw [← substLe]
      exact entailsRename p hk _ _ hw.1 ⟨hS.1,
        .cons (derivationWF hd).2.2.2.1.2.2 (.cons hw.2.2.2.1.2.2 .nil)⟩ he
  | @exists_ Γ t s xs C d hw hn hks hf hd ih =>
      simp only [renameExistsNames p hk]
      apply Derivation.exists_
      · simpa only [renameExistsNames p hk] using judgmentRenameWF p hk hw
      · exact hn.map p.injective
      · intro X hx; obtain ⟨Y,hY,rfl⟩ := List.mem_map.mp hx; simpa only [hk] using hks Y hY
      · simpa only [Finset.image_union, ← envRenameFv p Γ, ← schemeRenameFv p s] using renameDisjoint p xs (Γ.fv ∪ s.fv) hf
      · exact ih
  | convert hw hd he hΓ hs ih =>
      exact .convert (judgmentRenameWF p hk hw) ih
        ⟨entailsRename p hk _ _ (derivationWF hd).1 hw.1 he.1,
          entailsRename p hk _ _ hw.1 (derivationWF hd).1 he.2⟩
        (envBinderEqSubst _ (typeRenameClosed p) _ _ hΓ) (schemeBinderEqSubst _ (typeRenameClosed p) _ _ hs)

theorem freshSameKind (k : Nat) (F : Vars) : ∃ X : TVar, X.1 = k ∧ X ∉ F := by
  obtain ⟨n,hn⟩ := Finset.exists_notMem (F.image Prod.snd)
  exact ⟨(k,n),rfl,fun h => hn (Finset.mem_image.mpr ⟨(k,n),h,rfl⟩)⟩

theorem swapKind (X Y : TVar) (h : X.1 = Y.1) (Z : TVar) : (Equiv.swap X Y Z).1 = Z.1 := by
  by_cases hx : Z = X
  · subst Z; simpa using h.symm
  · by_cases hy : Z = Y
    · subst Z; simpa using h
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy]

theorem freshTypePermutation (A F G : Vars) (h : Disjoint A G) :
    ∃ p : TVar ≃ TVar, (∀ X, (p X).1 = X.1) ∧ (∀ X ∈ G, p X = X) ∧ (∀ X ∈ A, p X ∉ F) := by
  induction A using Finset.induction_on generalizing F G with
  | empty => exact ⟨Equiv.refl _, fun _ => rfl, fun _ _ => rfl, by simp⟩
  | @insert X A hx ih =>
      have hXG : X ∉ G := Finset.disjoint_left.mp h (by simp)
      have hAG : Disjoint A G := Finset.disjoint_left.mpr (fun Z hz hg => Finset.disjoint_left.mp h (by simp [hz]) hg)
      have hA : Disjoint A (insert X G) := by
        apply Finset.disjoint_left.mpr
        intro Z hz hg
        rcases Finset.mem_insert.mp hg with rfl | hg
        · exact hx hz
        · exact Finset.disjoint_left.mp hAG hz hg
      obtain ⟨p,hpk,hpg,hpf⟩ := ih (insert X F) (insert X G) hA
      obtain ⟨Y,hYk,hY⟩ := freshSameKind X.1 (insert X (F ∪ G ∪ A.image p))
      have hyX : Y ≠ X := fun he => hY (by simp [he])
      have hyF : Y ∉ F := fun he => hY (by simp [he])
      have hyG : Y ∉ G := fun he => hY (by simp [he])
      have hyA : Y ∉ A.image p := fun he => hY (by simp [he])
      refine ⟨p.trans (Equiv.swap X Y), fun Z => (swapKind X Y hYk.symm (p Z)).trans (hpk Z), ?_, ?_⟩
      · intro Z hz
        change Equiv.swap X Y (p Z) = Z
        rw [hpg Z (by simp [hz])]
        apply Equiv.swap_apply_of_ne_of_ne
        · exact fun he => hXG (he ▸ hz)
        · exact fun he => hyG (he ▸ hz)
      · intro Z hz
        change Equiv.swap X Y (p Z) ∉ F
        rcases Finset.mem_insert.mp hz with he | hz
        · subst Z
          rw [hpg X (by simp), Equiv.swap_apply_left]; exact hyF
        · have hpX : p Z ≠ X := fun he => hpf Z hz (by simp [he])
          have hpY : p Z ≠ Y := fun he => hyA (Finset.mem_image.mpr ⟨Z,hz,he⟩)
          rw [Equiv.swap_apply_of_ne_of_ne hpX hpY]
          exact fun he => hpf Z hz (by simp [he])

theorem tyRenameFixed (p : TVar ≃ TVar) (T : Ty) (h : ∀ X ∈ T.fv, p X = X) :
    T.subst (typeRename p) = T := by
  exact (tySubstCongr T (typeRename p) Ty.free
    (fun X hx => by simp only [typeRename, h X hx])).trans (tySubstIdentity T)

theorem constraintRenameFixed (p : TVar ≃ TVar) (C : Constraint) (n : Nat)
    (h : ∀ X ∈ C.fv, p X = X) : C.mapTypes (fun _ T => T.subst (typeRename p)) n = C := by
  apply Constraint.rec
    (motive_1 := fun C => ∀ n, (∀ X ∈ C.fv, p X = X) → C.mapTypes (fun _ T => T.subst (typeRename p)) n = C)
    (motive_2 := fun s => ∀ n, (∀ X ∈ s.fv, p X = X) → s.mapTypes (fun _ T => T.subst (typeRename p)) n = s)
    (by intros; rfl) (by intros; rfl)
    (by
      intro q ts n hh
      simp only [Constraint.mapTypes]
      congr 1
      exact (List.map_congr_left (g := id) (fun T ht => tyRenameFixed p T
        (fun X hx => hh X ((memUnionFold Ty.fv ts X).mpr ⟨T,ht,hx⟩)))).trans (List.map_id ts))
    (by
      intro C D ihC ihD n hh
      exact congrArg₂ Constraint.conj (ihC n (fun X hx => hh X (Finset.mem_union_left _ hx)))
        (ihD n (fun X hx => hh X (Finset.mem_union_right _ hx))))
    (by intro ks C ih n hh; exact congrArg (Constraint.exists_ ks) (ih _ hh))
    (by
      intro b s C ihs ihC n hh
      exact congrArg₂ (Constraint.def_ b) (ihs n (fun X hx => hh X (Finset.mem_union_left _ hx)))
        (ihC n (fun X hx => hh X (Finset.mem_union_right _ hx))))
    (by intro x T n hh; exact congrArg (Constraint.inst x) (tyRenameFixed p T hh))
    (by
      intro ks C T ih n hh
      exact congrArg₂ (Scheme.all ks) (ih _ (fun X hx => hh X (Finset.mem_union_left _ hx)))
        (tyRenameFixed p T (fun X hx => hh X (Finset.mem_union_right _ hx)))) C n h

theorem schemeRenameFixed (p : TVar ≃ TVar) (s : Scheme) (h : ∀ X ∈ s.fv, p X = X) :
    s.subst (typeRename p) = s := by
  cases s with
  | all ks C T =>
      exact congrArg₂ (Scheme.all ks)
        (constraintRenameFixed p C _ (fun X hx => h X (Finset.mem_union_left _ hx)))
        (tyRenameFixed p T (fun X hx => h X (Finset.mem_union_right _ hx)))

theorem envRenameFixed (p : TVar ≃ TVar) (Γ : Env) (h : ∀ X ∈ Γ.fv, p X = X) :
    Γ.subst (typeRename p) = Γ := by
  induction Γ with
  | nil => rfl
  | cons q Γ ih =>
      have hs := schemeRenameFixed p q.2 (fun X hx => h X (Finset.mem_union_left _ hx))
      have ht := ih (fun X hx => h X (Finset.mem_union_right _ hx))
      simpa only [Env.subst, List.map_cons, hs] using congrArg (List.cons q) ht

end HMX.LN.Proofs
