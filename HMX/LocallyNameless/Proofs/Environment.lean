import HMX.LocallyNameless.Proofs.ConstraintLaws

namespace HMX.LN.Proofs

def extendEnv (S : Signature) (M : Model) (ρ : Assignment M) : Env → GroundEnv M → GroundEnv M
  | [], ι => ι
  | (x,s) :: Γ, ι => extendEnv S M ρ Γ (updateEnv ι x (s.denote S M ρ ι))

def envReady (S : Signature) (M : Model) (ρ : Assignment M) : Env → GroundEnv M → Prop
  | [], _ => True
  | (x,s) :: Γ, ι => s.exists_.Holds S M ρ ι ∧ envReady S M ρ Γ (updateEnv ι x (s.denote S M ρ ι))

theorem extendEnvAppend (S : Signature) (M : Model) (ρ : Assignment M) (Γ Δ : Env) (ι : GroundEnv M) :
    extendEnv S M ρ (Γ ++ Δ) ι = extendEnv S M ρ Δ (extendEnv S M ρ Γ ι) := by
  induction Γ generalizing ι with
  | nil => rfl
  | cons p Γ ih => cases p; exact ih _

theorem defInHolds (S : Signature) (M : Model) (ρ : Assignment M) (Γ : Env) (ι : GroundEnv M) (C : Constraint) :
    (Env.defIn Γ C).Holds S M ρ ι ↔ C.Holds S M ρ (extendEnv S M ρ Γ ι) := by
  induction Γ generalizing ι with
  | nil => rfl
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      exact (defineHolds S M ρ ι x s (Env.defIn Γ C)).trans (ih _)

theorem letInReady (S : Signature) (M : Model) (ρ : Assignment M) (Γ : Env) (ι : GroundEnv M) (C : Constraint) :
    (Env.letIn Γ C).Holds S M ρ ι ↔ envReady S M ρ Γ ι ∧ C.Holds S M ρ (extendEnv S M ρ Γ ι) := by
  induction Γ generalizing ι with
  | nil => exact ⟨fun h => ⟨trivial,h⟩, fun h => h.2⟩
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      exact (letNameHolds S M ρ ι x s (Env.letIn Γ C)).trans
        ((and_congr Iff.rfl (ih _)).trans and_assoc.symm)

theorem existsFoldHolds (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M)
    (Γ Δ : Env) (C : Constraint) :
    ((Γ.foldl (fun (acc : Env × Constraint) p =>
      (acc.1 ++ [p], .conj acc.2 (Env.defIn acc.1 p.2.exists_))) (Δ,C)).2).Holds S M ρ ι ↔
      C.Holds S M ρ ι ∧ envReady S M ρ Γ (extendEnv S M ρ Δ ι) := by
  induction Γ generalizing Δ C with
  | nil => exact ⟨fun h => ⟨h,trivial⟩, fun h => h.1⟩
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      rw [List.foldl_cons, ih]
      change (C.Holds S M ρ ι ∧ (Env.defIn Δ s.exists_).Holds S M ρ ι) ∧ _ ↔ _
      rw [defInHolds, extendEnvAppend]
      exact and_assoc

theorem envExistsHolds (S : Signature) (M : Model) (ρ : Assignment M) (ι : GroundEnv M) (Γ : Env) :
    Γ.exists_.Holds S M ρ ι ↔ envReady S M ρ Γ ι := by
  have h := existsFoldHolds S M ρ ι Γ [] .truth
  exact h.trans (and_iff_right True.intro)

theorem letInHolds (S : Signature) (M : Model) (ρ : Assignment M) (Γ : Env) (ι : GroundEnv M) (C : Constraint) :
    (Env.letIn Γ C).Holds S M ρ ι ↔ Γ.exists_.Holds S M ρ ι ∧ C.Holds S M ρ (extendEnv S M ρ Γ ι) :=
  (letInReady S M ρ Γ ι C).trans (and_congr (envExistsHolds S M ρ ι Γ).symm Iff.rfl)

theorem letInWFReflect (S : Signature) (Γ : Env) (C : Constraint) (h : (Env.letIn Γ C).WF S [] 0) :
    Γ.WF S ∧ C.WF S [] 0 := by
  induction Γ with
  | nil => exact ⟨by simp [Env.WF], h⟩
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      have hw := letNameWFReflect S x s (Env.letIn Γ C) h
      have ht := ih hw.2
      refine ⟨?_, ht.2⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hw.1
      · exact ht.1 p hp

theorem extendEnvValid (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (Γ : Env) (ι : GroundEnv M) (hρ : ρ.Valid S M) (hΓ : Γ.WF S) (hι : ι.Valid M) :
    (extendEnv S M ρ Γ ι).Valid M := by
  induction Γ generalizing ι with
  | nil => exact hι
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      exact ih _ (fun p hp => hΓ p (by simp [hp]))
        (schemeDenotationValid S M hM ρ ι s x hρ hι (hΓ (x,s) (by simp)))

theorem prefixConjunction (S : Signature) (M : Model) : HMX.LN.prefixConjunction S M := by
  intro _ Γ C D _ _
  constructor <;> intro ρ ι _ _ h
  · obtain ⟨hΓ,hC,hD⟩ := (letInHolds S M ρ Γ ι (.conj C D)).mp h
    exact ⟨(letInHolds S M ρ Γ ι C).mpr ⟨hΓ,hC⟩, (letInHolds S M ρ Γ ι D).mpr ⟨hΓ,hD⟩⟩
  · obtain ⟨hΓ,hC⟩ := (letInHolds S M ρ Γ ι C).mp h.1
    have hD := (letInHolds S M ρ Γ ι D).mp h.2 |>.2
    exact (letInHolds S M ρ Γ ι (.conj C D)).mpr ⟨hΓ,hC,hD⟩

theorem envFvCons (p : Id × Scheme) (Γ : Env) : Env.fv (p :: Γ) = p.2.fv ∪ (Env.fv Γ) := rfl

theorem envFpiCons (p : Id × Scheme) (Γ : Env) : Env.fpi (p :: Γ) = p.2.fpi ∪ (Env.fpi Γ) := rfl

theorem schemeExistsWF (S : Signature) (s : Scheme) (hs : s.WF S [] 0) : s.exists_.WF S [] 0 := by
  cases s with | all ks C T => exact ⟨hs.1, hs.2.1⟩

theorem schemeExistsFv (s : Scheme) : s.exists_.fv ⊆ s.fv := by
  cases s with | all ks C T => exact Finset.subset_union_left

theorem schemeExistsFpi (s : Scheme) : s.exists_.fpi = s.fpi := by cases s; rfl

theorem envAssignmentLocality (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ ρ' : Assignment M) (Γ : Env) (ι : GroundEnv M) (hρ : ρ.Valid S M) (hρ' : ρ'.Valid S M)
    (hΓ : Γ.WF S) (hι : ι.Valid M) (hf : ∀ X ∈ (Env.fv Γ), ρ X = ρ' X) :
    extendEnv S M ρ Γ ι = extendEnv S M ρ' Γ ι ∧ (envReady S M ρ Γ ι ↔ envReady S M ρ' Γ ι) := by
  induction Γ generalizing ι with
  | nil => exact ⟨rfl, Iff.rfl⟩
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      have hs := hΓ (x,s) (by simp)
      have hsf : ∀ X ∈ s.fv, ρ X = ρ' X := fun X hx => hf X (Finset.mem_union_left _ hx)
      have hd := (semanticLocality S M hM ρ ρ' ι ι hρ hρ' hι hι).2 s hs hsf (by intros; rfl)
      have he := (semanticLocality S M hM ρ ρ' ι ι hρ hρ' hι hι).1 s.exists_ (schemeExistsWF S s hs)
        (fun X hx => hsf X (schemeExistsFv s hx)) (by intros; rfl)
      have ht := ih (updateEnv ι x (s.denote S M ρ' ι)) (fun p hp => hΓ p (by simp [hp]))
        (schemeDenotationValid S M hM ρ' ι s x hρ' hι hs) (fun X hx => hf X (Finset.mem_union_right _ hx))
      simpa only [extendEnv, envReady, hd] using And.intro ht.1 (and_congr he ht.2)

theorem prefixExists (S : Signature) (M : Model) : HMX.LN.prefixExists S M := by
  intro hM Γ xs C _ hf hL hR
  have hw := letInWFReflect S Γ (C.existsNames xs) hL
  have hc := (existsNamesWFReflect S xs C hw.2).2
  have hΓC := (existsNamesWFReflect S xs (Env.letIn Γ C) hR).2
  constructor
  · intro ρ ι hρ hι he
    obtain ⟨hready,he⟩ := (letInReady S M ρ Γ ι (C.existsNames xs)).mp he
    obtain ⟨vs,hv,hc'⟩ := (existsNamesHolds S M ρ _ xs C hc).mp he
    have hp := envAssignmentLocality S M hM (assignBlock xs vs ρ) ρ Γ ι
      (assignBlockValid S M ρ xs vs hρ hv) hρ hw.1 hι (by
        intro X hx; apply assignBlockOutside; intro hm; exact Finset.disjoint_left.mp hf (by simpa using hm) hx)
    apply (existsNamesHolds S M ρ ι xs (Env.letIn Γ C) hΓC).mpr
    refine ⟨vs,hv,(letInReady S M _ Γ ι C).mpr ⟨hp.2.mpr hready, ?_⟩⟩
    simpa only [hp.1] using hc'
  · intro ρ ι hρ hι he
    obtain ⟨vs,hv,he⟩ := (existsNamesHolds S M ρ ι xs (Env.letIn Γ C) hΓC).mp he
    obtain ⟨hready,hc'⟩ := (letInReady S M _ Γ ι C).mp he
    have hp := envAssignmentLocality S M hM (assignBlock xs vs ρ) ρ Γ ι
      (assignBlockValid S M ρ xs vs hρ hv) hρ hw.1 hι (by
        intro X hx; apply assignBlockOutside; intro hm; exact Finset.disjoint_left.mp hf (by simpa using hm) hx)
    apply (letInReady S M ρ Γ ι (C.existsNames xs)).mpr
    refine ⟨hp.2.mp hready, (existsNamesHolds S M ρ _ xs C hc).mpr ⟨vs,hv,?_⟩⟩
    simpa only [hp.1] using hc'

theorem lookupCons {α : Type} (Γ : List (Id × α)) (x y : Id) (s : α) :
    lookup ((y,s) :: Γ) x = match lookup Γ x with
      | some r => some r
      | none => if x = y then some s else none := by
  unfold lookup
  rw [List.reverse_cons, List.find?_append]
  cases h : Γ.reverse.find? (fun p => p.1 == x) with
  | none =>
      by_cases he : x = y
      · subst x; simp
      · simp [he, Ne.symm he]
  | some p => simp

theorem lookupMember (Γ : Env) (x : Id) (s : Scheme) (h : lookup Γ x = some s) : (x,s) ∈ Γ := by
  unfold lookup at h
  obtain ⟨p,hp,hs⟩ := Option.map_eq_some_iff.mp h
  have hx : p.1 = x := by simpa using List.find?_some hp
  have hm : p ∈ Γ := List.mem_reverse.mp (List.mem_of_find?_eq_some hp)
  rcases p with ⟨y,r⟩
  change y = x at hx
  change r = s at hs
  simpa only [hx,hs] using hm

theorem envFpiMember (Γ : Env) (p : Id × Scheme) (hp : p ∈ Γ) : p.2.fpi ⊆ Env.fpi Γ := by
  induction Γ with
  | nil => simp at hp
  | cons q Γ ih =>
      rcases List.mem_cons.mp hp with rfl | hp
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih hp) Finset.subset_union_right

theorem schemeGroundIndependent (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (s : Scheme) (ι ι' : GroundEnv M) (hρ : ρ.Valid S M)
    (hs : s.WF S [] 0) (hf : s.fpi = ∅) (hι : ι.Valid M) (hι' : ι'.Valid M) :
    s.denote S M ρ ι = s.denote S M ρ ι' :=
  (semanticLocality S M hM ρ ρ ι ι' hρ hρ hι hι').2 s hs (by intros; rfl) (by simp [hf])

theorem extendEnvLookup (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (Γ : Env) (ι : GroundEnv M) (hρ : ρ.Valid S M)
    (hΓ : Γ.WF S) (hf : Γ.fpi = ∅) (hι : ι.Valid M) (x : Id) :
    extendEnv S M ρ Γ ι x = match lookup Γ x with
      | some s => s.denote S M ρ ι
      | none => ι x := by
  induction Γ generalizing ι with
  | nil => rfl
  | cons p Γ ih =>
      rcases p with ⟨y,s⟩
      have hs := hΓ (y,s) (by simp)
      have htail : Env.fpi Γ = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun z hz => by
        have : z ∈ Env.fpi ((y,s)::Γ) := Finset.mem_union_right _ hz
        simp [hf] at this)
      have hi := schemeDenotationValid S M hM ρ ι s y hρ hι hs
      change extendEnv S M ρ Γ _ x = _
      rw [ih (updateEnv ι y (s.denote S M ρ ι)) (fun p hp => hΓ p (by simp [hp])) htail hi, lookupCons]
      cases hl : lookup Γ x with
      | none => by_cases hxy : x = y <;> simp [updateEnv, hxy]
      | some r =>
          have hr := lookupMember Γ x r hl
          have hrf : r.fpi = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun z hz => by
            have := envFpiMember Γ (x,r) hr hz
            simp [htail] at this)
          exact schemeGroundIndependent S M hM ρ r _ ι hρ (hΓ (x,r) (by simp [hr])) hrf hi hι

theorem instanceConstraintHolds (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (ι : GroundEnv M) (s : Scheme) (T : Ty)
    (hρ : ρ.Valid S M) (hs : s.WF S [] 0) (ht : T.HasKind S [] 0) :
    (s.instanceConstraint T).Holds S M ρ ι ↔ T.eval M ρ ∈ s.denote S M ρ ι := by
  cases s with
  | all ks C U =>
      simp only [Scheme.WF, List.append_nil] at hs
      have hT : ∀ vs, (T.shift ks.length 0).evalAt M ρ (push vs (fun _ => ρ (0,0))) = T.eval M ρ := by
        intro vs
        rw [tyShiftClosed T 0 ks.length (tyKindLC T S [] 0 ht)]
        exact tyEvalStacks M ρ _ _ T 0 (tyKindLC T S [] 0 ht) (by simp)
      simp only [Scheme.instanceConstraint, Constraint.Holds, Constraint.holdsAt, Constraint.le,
        List.map_cons, List.map_nil, Predicate.eval, Scheme.denote, Scheme.denoteAt, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨vs,hv,hc,hU,hT',hle⟩
        rw [hT] at hT' hle
        exact ⟨hT',vs,hv,hc,hle⟩
      · rintro ⟨hk,vs,hv,hc,hle⟩
        refine ⟨vs,hv,hc,?_,?_,?_⟩
        · exact evaluationKind S M hM ρ _ ks U 0 hρ (pushKinds M vs ks hv _) hs.2.2
        · simpa only [hT] using hk
        · simpa only [hT] using hle

theorem prefixLookup (S : Signature) (M : Model) : HMX.LN.prefixLookup S M := by
  intro hM Γ x s T hΓ hf hl hL _
  have hw := (letInWFReflect S Γ (.inst (.free x) T) hL).2
  have ht : T.HasKind S [] 0 := hw.1
  have hs := hΓ (x,s) (lookupMember Γ x s hl)
  constructor <;> intro ρ ι hρ hι he
  · obtain ⟨hready,hx⟩ := (letInHolds S M ρ Γ ι (.inst (.free x) T)).mp he
    have hx' : T.eval M ρ ∈ extendEnv S M ρ Γ ι x := hx
    rw [extendEnvLookup S M hM ρ Γ ι hρ hΓ hf hι x, hl] at hx'
    exact ⟨hready,(instanceConstraintHolds S M hM ρ ι s T hρ hs ht).mpr hx'⟩
  · apply (letInHolds S M ρ Γ ι (.inst (.free x) T)).mpr
    refine ⟨he.1,?_⟩
    change T.eval M ρ ∈ extendEnv S M ρ Γ ι x
    rw [extendEnvLookup S M hM ρ Γ ι hρ hΓ hf hι x, hl]
    exact (instanceConstraintHolds S M hM ρ ι s T hρ hs ht).mp he.2

theorem envReadyGroundIndependent (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (Γ : Env) (ι ι' : GroundEnv M) (hρ : ρ.Valid S M)
    (hΓ : Γ.WF S) (hf : Γ.fpi = ∅) (hι : ι.Valid M) (hι' : ι'.Valid M) :
    envReady S M ρ Γ ι ↔ envReady S M ρ Γ ι' := by
  induction Γ generalizing ι ι' with
  | nil => rfl
  | cons p Γ ih =>
      rcases p with ⟨x,s⟩
      have hs := hΓ (x,s) (by simp)
      have hf' : s.fpi = ∅ ∧ Env.fpi Γ = ∅ := by simpa only [envFpiCons, Finset.union_eq_empty] using hf
      apply and_congr
      · exact (semanticLocality S M hM ρ ρ ι ι' hρ hρ hι hι').1 s.exists_ (schemeExistsWF S s hs)
          (by intros; rfl) (by simp [schemeExistsFpi, hf'.1])
      · exact ih _ _ (fun p hp => hΓ p (by simp [hp])) hf'.2
          (schemeDenotationValid S M hM ρ ι s x hρ hι hs)
          (schemeDenotationValid S M hM ρ ι' s x hρ hι' hs)

theorem extendEnvIdempotent (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (Γ : Env) (ι : GroundEnv M) (hρ : ρ.Valid S M)
    (hΓ : Γ.WF S) (hf : Γ.fpi = ∅) (hι : ι.Valid M) :
    extendEnv S M ρ Γ (extendEnv S M ρ Γ ι) = extendEnv S M ρ Γ ι := by
  have hi := extendEnvValid S M hM ρ Γ ι hρ hΓ hι
  funext x
  rw [extendEnvLookup S M hM ρ Γ (extendEnv S M ρ Γ ι) hρ hΓ hf hi x]
  cases hl : lookup Γ x with
  | none => rfl
  | some s =>
      rw [extendEnvLookup S M hM ρ Γ ι hρ hΓ hf hι x, hl]
      have hm := lookupMember Γ x s hl
      have hs : s.fpi = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun z hz => by
        have := envFpiMember Γ (x,s) hm hz
        simp [hf] at this)
      exact schemeGroundIndependent S M hM ρ s _ ι hρ (hΓ (x,s) hm) hs hi hι

/-- A realized, identifier-closed prefix can be repeated in its own environment. -/
theorem letInRepeated (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (Γ : Env) (ι : GroundEnv M) (C : Constraint) (hρ : ρ.Valid S M)
    (hΓ : Γ.WF S) (hf : Γ.fpi = ∅) (hι : ι.Valid M) (hr : envReady S M ρ Γ ι) :
    (Γ.letIn C).Holds S M ρ (extendEnv S M ρ Γ ι) ↔ C.Holds S M ρ (extendEnv S M ρ Γ ι) := by
  rw [letInReady, extendEnvIdempotent S M hM ρ Γ ι hρ hΓ hf hι]
  exact and_iff_right ((envReadyGroundIndependent S M hM ρ Γ ι _ hρ hΓ hf hι
    (extendEnvValid S M hM ρ Γ ι hρ hΓ hι)).mp hr)

theorem letInSnoc (Γ : Env) (x : Id) (s : Scheme) (C : Constraint) :
    Env.letIn (Γ ++ [(x,s)]) C = Γ.letIn (C.letName x s) := by
  simp [Env.letIn, List.foldr_append]

theorem letNameDenoteEq (S : Signature) (M : Model) (hM : M.Requirements S)
    (ρ : Assignment M) (ι : GroundEnv M) (x : Id) (s r : Scheme) (C : Constraint)
    (hρ : ρ.Valid S M) (hs : s.WF S [] 0) (hr : r.WF S [] 0)
    (he : s.denote S M ρ ι = r.denote S M ρ ι) :
    (C.letName x s).Holds S M ρ ι ↔ (C.letName x r).Holds S M ρ ι := by
  rw [letNameHolds, letNameHolds, schemeExistsNonempty S M hM ρ ι hρ s hs,
    schemeExistsNonempty S M hM ρ ι hρ r hr, he]

theorem letDup (S : Signature) (M : Model) : HMX.LN.letDup S M := by
  intro hM Γ x xs C T D hΓ hf _ hdis hL hR
  rw [letInSnoc] at hL hR ⊢
  rw [letInSnoc]
  have hs := (letNameWFReflect S x _ D (letInWFReflect S Γ _ hL).2).1
  have hr := (letNameWFReflect S x _ D (letInWFReflect S Γ _ hR).2).1
  have hC := generalizeWFReflect S xs C T hs
  have hGC := generalizeWFReflect S xs (Γ.letIn C) T hr
  have he : ∀ ρ ι, ρ.Valid S M → ι.Valid M → envReady S M ρ Γ ι →
      ((D.letName x (Scheme.generalize xs C T)).Holds S M ρ (extendEnv S M ρ Γ ι) ↔
      (D.letName x (Scheme.generalize xs (Γ.letIn C) T)).Holds S M ρ (extendEnv S M ρ Γ ι)) := by
    intro ρ ι hρ hι hready
    apply letNameDenoteEq S M hM ρ _ x _ _ D hρ hs hr
    ext v
    rw [generalizeDenote S M ρ _ xs C T hC.2.1 hC.2.2,
      generalizeDenote S M ρ _ xs (Γ.letIn C) T hGC.2.1 hGC.2.2]
    apply and_congr Iff.rfl
    apply exists_congr
    intro vs
    apply and_congr_right
    intro hv
    have hρ' := assignBlockValid S M ρ xs vs hρ hv
    have hp := envAssignmentLocality S M hM (assignBlock xs vs ρ) ρ Γ ι hρ' hρ hΓ hι (by
      intro X hx
      apply assignBlockOutside
      intro hm
      exact Finset.disjoint_left.mp hdis (by simpa using hm) hx)
    have hc := letInRepeated S M hM (assignBlock xs vs ρ) Γ ι C hρ' hΓ hf hι (hp.2.mpr hready)
    rw [hp.1] at hc
    exact and_congr hc.symm Iff.rfl
  constructor <;> intro ρ ι hρ hι hh
  · obtain ⟨hready,hbody⟩ := (letInReady S M ρ Γ ι _).mp hh
    exact (letInReady S M ρ Γ ι _).mpr ⟨hready,(he ρ ι hρ hι hready).mp hbody⟩
  · obtain ⟨hready,hbody⟩ := (letInReady S M ρ Γ ι _).mp hh
    exact (letInReady S M ρ Γ ι _).mpr ⟨hready,(he ρ ι hρ hι hready).mpr hbody⟩

theorem letSchemeMonotonicity (S : Signature) (M : Model) : HMX.LN.letSchemeMonotonicity S M := by
  intro hM C x s r D _ hs hr _ hinc ρ ι hρ hι hh
  have hi := hinc ρ ι hρ hι hh.1
  obtain ⟨hse,hD⟩ := (letNameHolds S M ρ ι x s D).mp hh.2
  obtain ⟨v,hv⟩ := (schemeExistsNonempty S M hM ρ ι hρ s hs).mp hse
  apply (letNameHolds S M ρ ι x r D).mpr
  refine ⟨(schemeExistsNonempty S M hM ρ ι hρ r hr).mpr ⟨v,hi hv⟩, ?_⟩
  exact constraintMonotone S M ρ D _ _ _ _ _ (updateEnvMonotone ι x _ _ hi)
    (fun _ => Set.Subset.rfl) hD

end HMX.LN.Proofs
