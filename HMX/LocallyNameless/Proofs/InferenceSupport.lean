import HMX.LocallyNameless.Proofs.GeneratedSchemes

namespace HMX.LN.Proofs

/-- Count term nodes, independently of the representation of identifiers. -/
def exprNodes : Expr → Nat
  | .ident _ => 1
  | .lam t => exprNodes t + 1
  | .app t u | .letE t u => exprNodes t + exprNodes u + 1

theorem exprNodesOpen (t : Expr) (x : Id) (d : Nat) :
    exprNodes (Expr.openAt d (.ident (.free x)) t) = exprNodes t := by
  induction t generalizing d with
  | ident v => cases v <;> simp [Expr.openAt, Expr.shift, exprNodes]; split <;> rfl
  | lam t ih => simp [Expr.openAt, exprNodes, ih]
  | app t u iht ihu => simp [Expr.openAt, exprNodes, iht, ihu]
  | letE t u iht ihu => simp [Expr.openAt, exprNodes, iht, ihu]

theorem exprOpenScope (t : Expr) (x : Id) (d : Nat) :
    (Expr.openAt d (.ident (.free x)) t).fpi ⊆ insert x t.fpi := by
  induction t generalizing d with
  | ident v =>
      cases v with
      | free y => simp [Expr.openAt, Expr.fpi]
      | bound i => simp only [Expr.openAt]; split <;> simp [Expr.shift, Expr.fpi]
  | lam t ih => exact ih (d+1)
  | app t u iht ihu =>
      simpa only [Expr.openAt, Expr.fpi, Finset.insert_union, Finset.union_insert,
        Finset.insert_idem] using Finset.union_subset_union (iht d) (ihu d)
  | letE t u iht ihu =>
      simpa only [Expr.openAt, Expr.fpi, Finset.insert_union, Finset.union_insert,
        Finset.insert_idem] using Finset.union_subset_union (iht d) (ihu (d+1))

theorem envSnocWF (Γ : Env) (x : Id) (s : Scheme) (hΓ : Γ.WF S) (hs : s.WF S [] 0) :
    (Γ ++ [(x,s)]).WF S := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hΓ p hp
  · simpa using List.mem_singleton.mp hp ▸ hs

theorem envSnocFpi (Γ : Env) (x : Id) (s : Scheme) :
    (Γ ++ [(x,s)]).fpi = Γ.fpi ∪ s.fpi := by
  induction Γ with
  | nil => simp [Env.fpi]
  | cons p Γ ih => simpa only [List.cons_append, envFpiCons, Finset.union_assoc] using congrArg (p.2.fpi ∪ ·) ih

theorem openedScope (Γ : Env) (t : Expr) (x : Id) (s : Scheme) (h : t.fpi ⊆ Γ.dpi) :
    (Expr.openAt 0 (.ident (.free x)) t).fpi ⊆ (Γ ++ [(x,s)]).dpi := by
  intro y hy
  have hh := exprOpenScope t x 0 hy
  simp only [Finset.mem_insert] at hh
  rcases hh with rfl | hh
  · simp [Env.dpi]
  · simpa [Env.dpi] using Or.inr (h hh)

theorem inferWF (hS : S.Valid) (hΓ : Γ.WF S) (ht : t.LCAt 0) (hT : T.HasKind S [] 0) :
    (infer Γ t T).WF S [] 0 := letInWF S Γ _ hΓ (generationWF S hS 0 t T ht hT)

theorem inferFpi (Γ : Env) (t : Expr) (T : Ty) (hf : Γ.fpi = ∅) (h : t.fpi ⊆ Γ.dpi) :
    (infer Γ t T).fpi = ∅ := by
  rw [infer, letInFpi Γ _ hf, (generationFreeVariables t T).2]
  exact Finset.sdiff_eq_empty_iff_subset.mpr h

theorem inferenceJudgment (hC : C.WF S [] 0) (hΓ : Γ.WF S) (ht : t.LCAt 0)
    (hT : T.HasKind S [] 0) (hCf : C.fpi = ∅) (hΓf : Γ.fpi = ∅) :
    JudgmentWF S C Γ t (.mono T) := ⟨hC,hΓ,ht,monoWF S T hT,hCf,hΓf,rfl⟩

theorem lookupOfDpi (Γ : Env) (x : Id) (hx : x ∈ Γ.dpi) : ∃ s, lookup Γ x = some s := by
  induction Γ with
  | nil => simp [Env.dpi] at hx
  | cons p Γ ih =>
      rw [lookupCons]
      split
      · exact ⟨_,rfl⟩
      · split
        · exact ⟨_,rfl⟩
        · rename_i hn he
          have hx' : x ∈ Env.dpi Γ := by
            simpa [Env.dpi, he, Ne.symm he] using hx
          obtain ⟨s,hs⟩ := ih hx'
          simp_all

/-- Opening the program binder works for qualified schemes as well as monotypes. -/
theorem generateLetNameScheme (t : Expr) (z : Nat) (T : Ty) (s : Scheme)
    (hz : Id.var z ∉ t.fpi) :
    (generate t T).letBound .term s =
      (generate (Expr.openAt 0 (.ident (.free (.var z))) t) T).letName (.var z) s := by
  have hf : Id.var z ∉ (generate t T).fpi := by rw [(generationFreeVariables t T).2]; exact hz
  have he := constraintCloseOpenId (generate t T) (.var z) 0 hf
  change ((generate t T).openId (.var z)).closeId (.var z) = generate t T at he
  have ho : (generate t T).openId (.var z) = generate (Expr.openAt 0 (.ident (.free (.var z))) t) T :=
    generateOpenAt t T (.var z) 0
  rw [ho] at he
  simp only [Constraint.letBound, Constraint.letName, Constraint.define, Binder.ofId, he]

/-- Prefix distribution also exposes the WF and identifier closure needed by Exists. -/
theorem inferencePrefixExists (hM : M.Requirements S) (Γ : Env) (xs : List TVar)
    (D : Constraint) (hΓ : Γ.WF S) (hΓf : Γ.fpi = ∅) (hn : xs.Nodup) (hf : Disjoint xs.toFinset Γ.fv)
    (hW : (Γ.letIn (D.existsNames xs)).WF S [] 0)
    (hF : (Γ.letIn (D.existsNames xs)).fpi = ∅) :
    (Γ.letIn D).WF S [] 0 ∧ (Γ.letIn D).fpi = ∅ ∧
      Equivalent S M (Γ.letIn (D.existsNames xs)) ((Γ.letIn D).existsNames xs) := by
  have hd := existsNamesWFReflect S xs D (letInWFReflect S Γ _ hW).2
  have hw := letInWF S Γ D hΓ hd.2
  refine ⟨hw,?_,prefixExists S M hM Γ xs D hn hf hW (existsNamesWF S xs _ 0 hd.1 hw)⟩
  rw [letInFpi Γ _ hΓf, existsNamesFpi] at hF
  rw [letInFpi Γ _ hΓf]
  exact hF

theorem instanceConstraintWF (hS : S.Valid) (s : Scheme) (T : Ty)
    (hs : s.WF S [] 0) (hT : T.HasKind S [] 0) : (s.instanceConstraint T).WF S [] 0 := by
  cases s with
  | all ks D A =>
      refine ⟨hs.1,hs.2.1,hS.1,.cons hs.2.2 (.cons ?_ .nil)⟩
      rw [tyShiftClosed T 0 ks.length (tyKindLC T S [] 0 hT)]
      exact tyKindClosed T S (ks ++ []) 0 hT

theorem envExistsWF (Γ : Env) (hΓ : Γ.WF S) : Γ.exists_.WF S [] 0 := by
  have hd : ∀ (Δ : Env) (D : Constraint), Δ.WF S → D.WF S [] 0 → (Δ.defIn D).WF S [] 0 := by
    intro Δ D hΔ hD
    induction Δ with
    | nil => exact hD
    | cons p Δ ih =>
        exact (letNameWF S p.1 p.2 _ (hΔ p (by simp))
          (ih (fun q hq => hΔ q (by simp [hq])))).2
  have hf : ∀ (Λ Δ : Env) (D : Constraint), Λ.WF S → Δ.WF S → D.WF S [] 0 →
      (Λ.foldl (fun (acc : Env × Constraint) p =>
        (acc.1 ++ [p], .conj acc.2 (acc.1.defIn p.2.exists_))) (Δ,D)).2.WF S [] 0 := by
    intro Λ
    induction Λ with
    | nil => intro Δ D _ _ hD; exact hD
    | cons p Λ ih =>
        intro Δ D hΛ hΔ hD
        exact ih (Δ ++ [p]) _ (fun q hq => hΛ q (by simp [hq]))
          (envSnocWF Δ p.1 p.2 hΔ (hΛ p (by simp)))
          ⟨hD,hd Δ _ hΔ (schemeExistsWF S p.2 (hΛ p (by simp)))⟩
  exact hf Γ [] .truth hΓ (by simp [Env.WF]) trivial

theorem inferenceVariable (hF : Framework S M I) (C : Constraint) (Γ : Env) (x : Id) (U : Ty)
    (hw : JudgmentWF S C Γ (.ident (.free x)) (.mono U)) (hx : x ∈ Γ.dpi)
    (he : Entails S M C (infer Γ (.ident (.free x)) U)) :
    AlternateTyping S M C Γ (.ident (.free x)) U := by
  obtain ⟨s,hl⟩ := lookupOfDpi Γ x hx
  have hs := hw.2.1 (x,s) (lookupMember Γ x s hl)
  have hsf : s.fpi = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
    intro y hy
    have hh := envFpiMember Γ (x,s) (lookupMember Γ x s hl) hy
    simp [hw.2.2.2.2.2.1] at hh)
  have hU := hw.2.2.2.1.2.2
  have hp := prefixLookup S M hF.1 Γ x s U hw.2.1 hw.2.2.2.2.2.1 hl
    (inferWF hF.1.1 hw.2.1 hw.2.2.1 hU)
    ⟨envExistsWF Γ hw.2.1,instanceConstraintWF hF.1.1 s U hs hU⟩
  obtain ⟨xs,D,T,hn,hf,hk,hD,hT,hds⟩ := schemeFreshOpening s hs (C.fv ∪ Γ.fv ∪ U.fv)
  have hDf : D.fpi = ∅ := by rw [← generalizeFpi xs D T,hds,hsf]
  have hv := AlternateTyping.varInst (M := M)
    (inferenceJudgment (C := .conj C D) ⟨hw.1,hD⟩ hw.2.1 trivial hT
      (by simp [Constraint.fpi,hw.2.2.2.2.1,hDf]) hw.2.2.2.2.2.1) hn (by rw [hds]; exact hl)
  apply alternateGeneralizedInstance hF xs hn hk hv hw (fun _ _ _ _ hh => hh) hf
  intro ρ ι hρ hι hh
  rw [hds]
  exact (instanceConstraintHolds S M hF.1 ρ ι s U hρ hs hU).mp
    (hp.1 ρ ι hρ hι (he ρ ι hρ hι hh)).2

theorem prefixSnocRealizable (hM : M.Requirements S) (Γ : Env) (x : Id) (s : Scheme) (B : Constraint)
    (hΓ : Γ.WF S) (hs : s.WF S [] 0) (hsf : s.fpi = ∅) :
    Entails S M ((Γ ++ [(x,s)]).letIn B) s.exists_ := by
  intro ρ ι hρ hι hh
  rw [letInSnoc] at hh
  have he := (letNameHolds S M ρ (extendEnv S M ρ Γ ι) x s B).mp
    ((letInReady S M ρ Γ ι _).mp hh).2
  have hl := (semanticLocality S M hM ρ ρ (extendEnv S M ρ Γ ι) ι hρ hρ
    (extendEnvValid S M hM ρ Γ ι hρ hΓ hι) hι).1 s.exists_ (schemeExistsWF S s hs)
    (by intros; rfl) (by simp [schemeExistsFpi,hsf])
  exact hl.mp he.1

/-- Identifier-closed assumptions are unchanged when a well-formed environment is prefixed. -/
theorem closedHoldsExtend (hM : M.Requirements S) (Γ : Env) (C : Constraint)
    (hΓ : Γ.WF S) (hC : C.WF S [] 0) (hf : C.fpi = ∅)
    (ρ : Assignment M) (ι : GroundEnv M) (hρ : ρ.Valid S M) (hι : ι.Valid M) :
    C.Holds S M ρ (extendEnv S M ρ Γ ι) ↔ C.Holds S M ρ ι :=
  (semanticLocality S M hM ρ ρ _ ι hρ hρ
    (extendEnvValid S M hM ρ Γ ι hρ hΓ hι) hι).1 C hC (by intros; rfl) (by simp [hf])

theorem envReadyAppend (S : Signature) (M : Model) (ρ : Assignment M) (Γ Δ : Env) (ι : GroundEnv M) :
    envReady S M ρ (Γ ++ Δ) ι ↔ envReady S M ρ Γ ι ∧ envReady S M ρ Δ (extendEnv S M ρ Γ ι) := by
  induction Γ generalizing ι with
  | nil => simp [envReady,extendEnv]
  | cons p Γ ih => simp only [List.cons_append,envReady,extendEnv,ih,and_assoc]

theorem envSnocRealizable (hM : M.Requirements S) (C : Constraint) (Γ : Env) (x : Id) (s : Scheme)
    (hΓ : Γ.WF S) (hs : s.WF S [] 0) (hf : s.fpi = ∅)
    (hΓe : Entails S M C Γ.exists_) (hse : Entails S M C s.exists_) :
    Entails S M C (Γ ++ [(x,s)]).exists_ := by
  intro ρ ι hρ hι hh
  apply (envExistsHolds S M ρ ι _).mpr
  apply (envReadyAppend S M ρ Γ [(x,s)] ι).mpr
  refine ⟨(envExistsHolds S M ρ ι Γ).mp (hΓe ρ ι hρ hι hh),?_,trivial⟩
  exact (closedHoldsExtend hM Γ s.exists_ hΓ (schemeExistsWF S s hs)
    (by rw [schemeExistsFpi,hf]) ρ ι hρ hι).mpr (hse ρ ι hρ hι hh)

/-- Binder permutations preserve both environment extension and feasibility. -/
theorem envBinderSemantics (hM : M.Requirements S) (Γ Δ : Env) (h : Γ.BinderEq Δ)
    (hΓ : Γ.WF S) (hΔ : Δ.WF S) (ρ : Assignment M) (ι : GroundEnv M)
    (hρ : ρ.Valid S M) (hι : ι.Valid M) :
    extendEnv S M ρ Γ ι = extendEnv S M ρ Δ ι ∧
      (envReady S M ρ Γ ι ↔ envReady S M ρ Δ ι) := by
  induction h generalizing ι with
  | nil => exact ⟨rfl,Iff.rfl⟩
  | @cons p q Γ Δ hp ht ih =>
      have hs := hΓ p (by simp)
      have hr := hΔ q (by simp)
      have hd : p.2.denote S M ρ ι = q.2.denote S M ρ ι := schemeBinderEq S M ρ ι _ _ hp.2 _ _
      have he : p.2.exists_.Holds S M ρ ι ↔ q.2.exists_.Holds S M ρ ι := by
        rw [schemeExistsNonempty S M hM ρ ι hρ p.2 hs,
          schemeExistsNonempty S M hM ρ ι hρ q.2 hr,hd]
      have hi := ih (fun a ha => hΓ a (by simp [ha])) (fun a ha => hΔ a (by simp [ha]))
        (updateEnv ι p.1 (p.2.denote S M ρ ι)) (schemeDenotationValid S M hM ρ ι p.2 p.1 hρ hι hs)
      simp only [extendEnv,envReady]
      rw [← hp.1,← hd]
      exact ⟨hi.1,and_congr he hi.2⟩

theorem prefixBinderEquivalent (hM : M.Requirements S) (Γ Δ : Env) (h : Γ.BinderEq Δ)
    (hΓ : Γ.WF S) (hΔ : Δ.WF S) (B : Constraint) :
    Equivalent S M (Γ.letIn B) (Δ.letIn B) := by
  constructor <;> intro ρ ι hρ hι hh
  · have he := envBinderSemantics hM Γ Δ h hΓ hΔ ρ ι hρ hι
    obtain ⟨hr,hb⟩ := (letInReady S M ρ Γ ι B).mp hh
    exact (letInReady S M ρ Δ ι B).mpr ⟨he.2.mp hr,he.1 ▸ hb⟩
  · have he := envBinderSemantics hM Γ Δ h hΓ hΔ ρ ι hρ hι
    obtain ⟨hr,hb⟩ := (letInReady S M ρ Δ ι B).mp hh
    exact (letInReady S M ρ Γ ι B).mpr ⟨he.2.mpr hr,he.1.symm ▸ hb⟩

/-- Substituting a type in an expected type supplies its evaluation as a witness.
No assumption that arbitrary model elements are represented by types is used. -/
theorem generateTypeWitness (hS : S.Valid) (t : Expr) (B A : Ty) (X : TVar)
    (ht : t.LCAt 0) (hB : B.HasKind S [] 0) (hA : A.LCAt 0)
    (ρ : Assignment M) (ι : GroundEnv M) :
    (generate t (B.subst (fun Y => if Y = X then A else .free Y))).Holds S M ρ ι ↔
      (generate t B).Holds S M (assignBlock [X] [A.eval M ρ] ρ) ι := by
  let θ : Subst := fun Y => if Y = X then A else .free Y
  have hθ : ∀ Y, (θ Y).LCAt 0 := by intro Y; by_cases he : Y = X <;> simp [θ,he,hA,Ty.LCAt]
  have he : (fun Y => (θ Y).eval M ρ) = assignBlock [X] [A.eval M ρ] ρ := by
    funext Y
    by_cases hy : Y = X <;> simp [θ,hy,assignBlock,Ty.eval,Ty.evalAt]
  have hh := constraintEvalSubst S M θ hθ ρ ι (generate t B) 0 (fun _ => ρ (0,0)) (fun _ => ∅)
  change ((generate t B).subst θ).Holds S M ρ ι ↔ _ at hh
  rw [generateSubstEq t B θ hθ (tyKindLC B S [] 0 hB),he] at hh
  exact hh.trans (constraintStacks S M _ ι (generate t B) [] 0
    (generationWF S hS 0 t B ht hB) _ _ _ _ (by simp) (by simp))

theorem generateApplicationEntails (hF : Framework S M I) (t u : Expr) (A U : Ty)
    (ht : t.LCAt 0) (hu : u.LCAt 0) (hA : A.HasKind S [] 0) (hU : U.HasKind S [] 0) :
    Entails S M (.conj (generate t (.arrow A U)) (generate u A)) (generate (.app t u) U) := by
  obtain ⟨X,hX,hXF⟩ := freshSameKind 0 (A.fv ∪ U.fv)
  have hxU : X ∉ U.fv := fun hm => hXF (Finset.mem_union_right _ hm)
  have hXk : (Ty.free X).HasKind S [] 0 := by rw [← hX]; exact .free (by rw [hX]; exact hF.1.1.1)
  let θ : Subst := fun Y => if Y = X then A else .free Y
  have hUs : U.subst θ = U := by
    rw [tySubstCongr U θ Ty.free (by intro Y hy; simp [θ,show Y ≠ X from fun he => hxU (he ▸ hy)]),tySubstIdentity]
  have hB := arrowKind S hF.1.1 (.free X) U [] hXk hU
  have hAc := tyKindLC A S [] 0 hA
  intro ρ ι hρ hι hh
  rw [generateAppFresh t u U X (tyKindLC U S [] 0 hU) hX hxU]
  apply (existsNamesHolds S M ρ ι [X]
    (.conj (generate t (.arrow (.free X) U)) (generate u (.free X)))
    ⟨generationWF S hF.1.1 0 t _ ht hB,generationWF S hF.1.1 0 u _ hu hXk⟩).mpr
  refine ⟨[A.eval M ρ],.cons (by rw [hX]; exact evalKind S M hF.1 ρ hρ A 0 hA) .nil,?_,?_⟩
  · apply (generateTypeWitness hF.1.1 t (.arrow (.free X) U) A X ht hB hAc ρ ι).mp
    change (generate t ((Ty.arrow (.free X) U).subst θ)).Holds S M ρ ι
    have hBs : (Ty.arrow (.free X) U).subst θ = .arrow A U := by
      simp only [Ty.arrow,Ty.subst,List.map_cons,List.map_nil,hUs]
      simp [θ]
    rw [hBs]
    exact hh.1
  · apply (generateTypeWitness hF.1.1 u (.free X) A X hu hXk hAc ρ ι).mp
    simp only [Ty.subst,ite_true]
    exact hh.2

end HMX.LN.Proofs
